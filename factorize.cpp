#include <cassert>
#include <cstdio>
#include <cstdint>
#include <ctime>

#include <algorithm>
#include <array>
#include <atomic>
#include <bitset>
#include <condition_variable>
#include <deque>
#include <iostream>
#include <limits>
#include <map>
#include <memory>
#include <mutex>
#include <string>
#include <thread>
#include <vector>

typedef uint64_t uint_t;
typedef std::map<uint_t, uint_t> map_t;

// Keep it small, as we do round-robin work assignment 
// without work-stealing, which means the bigger the queue,
// the more hard work can be accumulated by a single thread.
static const size_t queue_size = 16;

// lock-free single-producer single-consumer queue
template<typename T, size_t Size>
class queue_t
{
   // padding gives 20% speedup on my machine
   static const size_t padding_size = 256;
   char padding0_[padding_size];
   T values_[Size];
   char padding1_[padding_size];
   std::atomic<uint_t> head_;
   char padding2_[padding_size];
   std::atomic<uint_t> tail_;

public:
   queue_t ()
      : head_ (0)
      , tail_ (0)
   {
      // should have been static_assert but my compiler does not support it yet
      assert (Size >= 2 && ((Size - 1) & Size) == 0); // power of two
   }

   bool enqueue (const T & value)
   {
      const uint_t head = head_.load (std::memory_order_relaxed);
      const uint_t tail = tail_.load (std::memory_order_acquire);

      // full?
      if ((head - tail) == Size) 
	 return false;

      values_[head & (Size - 1)] = value;
      assert (head < std::numeric_limits<uint_t>::max ());
      head_.fetch_add (1, std::memory_order_release);
      return true;
   }
   
   bool dequeue (T & value)
   {
      const uint_t head = head_.load (std::memory_order_acquire);
      const uint_t tail = tail_.load (std::memory_order_relaxed);

      // empty?
      if (head == tail) 
	 return false;

      value = values_[tail & (Size - 1)];
      tail_.fetch_add (1, std::memory_order_release);
      return true;
   }

};

// effective prime counter
class prime_counter_t
{
   struct counter_t
   {
      uint_t prime;
      uint_t count;
      counter_t () : prime (0), count (0) {}
   };

   static const size_t max_primes = 64; // even less, just an estimate
   std::array<counter_t, max_primes> counters_;
   size_t size_;

   size_t cursor () const
   {
      assert (size_);
      return size_ - 1;
   }

   bool empty () const
   {
      return !size_;
   }

public:

   prime_counter_t () : size_ (0) {}

   void count (const uint_t prime)
   {
      assert (prime > 1);
      if (empty () || counters_[cursor ()].prime != prime)
      {
	 assert (empty () || (prime > counters_[cursor ()].prime));
	 ++size_;
	 assert (size_ <= max_primes);
	 counters_[cursor ()].prime = prime;
      }
      ++counters_[cursor ()].count;
   }

   void update (map_t & map)
   {
      for (size_t i = 0; i < size_; ++i)
      {
	 const counter_t & counter = counters_[i];
	 assert (counter.prime);
	 assert (counter.count);

	 auto mi = map.find (counter.prime);
	 if (mi == map.end ())
	    map.insert (
	       std::make_pair (counter.prime, counter.count));
	 else
	    mi->second = std::max (mi->second, counter.count);
      }
   }
};

// generator to read uints from stdin
class producer_t
{
   bool eof_;
   uint_t value_;

   void read ()
   {
      char buf[256] = {};
      eof_ = fgets (buf, sizeof (buf), stdin) == 0;
      try
      {
	 value_ = std::stoull (buf);
      }
      catch (...)
      {}
   }

public:
   producer_t () 
      : eof_ (false) 
      , value_ (0)
   {
      // get the first value
      operator++ ();
   }

   producer_t & begin ()
   {
      return *this;
   }

   producer_t & end ()
   {
      return *this;
   }

   bool operator== (const producer_t & self)
   {
      return eof_;
   }

   bool operator!= (const producer_t & self)
   {
      return !(*this == self);
   }

   producer_t & operator++ ()
   {
      assert (!eof_);
      read ();
      return *this;
   }

   producer_t & operator++ (int)
   {
      assert (!eof_);
      read ();
      return *this;
   }

   uint_t operator* () const
   {
      assert (!eof_);
      return value_;
   }
};

// multi-threaded factorizer
template<typename Job, size_t QueueSize>
class factorizer_t
{
   const size_t thread_num_;
   
   struct job_t
   {
      bool end; // signals the end of jobs
      Job data;
      job_t () : data (0), end (false) {}
      job_t (const Job & data) : data (data), end (false) {}
      job_t (const bool end) : data (0), end (true) {}
   };

   // queue of jobs
   typedef queue_t<job_t, QueueSize> queue_t;

   // each thread is assigned a queue, and a map to store results
   std::vector<std::thread> threads_;
   std::unique_ptr<queue_t[]> queues_; // queues are not copyable, so I can't use a vector
   std::vector<map_t> maps_;

   // mutex and cv allow main thread to sleep if workers are busy
   std::mutex mtx_;
   std::condition_variable cv_;

   template<typename Worker>
   void start_threads (Worker & worker)
   {
      for (size_t i = 0; i < thread_num_; ++i)
	 threads_.push_back (
	    std::thread (worker, std::ref (queues_[i]), std::ref (maps_[i])));
   }

   void wait_threads ()
   {
      std::unique_lock<std::mutex> lock (mtx_);
      cv_.wait (lock);
   }

   void join_threads ()
   {
      // signal
      for (size_t i = 0; i < thread_num_; ++i)
      {
	 while (!queues_[i].enqueue (job_t (/* end= */true)))
	    // makes no sense to busy-wait here
	    wait_threads ();
      }

      // join
      std::for_each (std::begin (threads_), 
		     std::end (threads_),
		     [] (std::thread & t) { t.join (); });
   }

   void assign_job (Job & data)
   {
      const job_t job (data);
      while (1)
      {
	 size_t tries = 0;
	 const size_t max_tries = 10;
	 // try hard to find an empty slot
	 for (; tries < max_tries; ++tries)
	 {
	    // try to put to one of empty queues
	    // start with a random queue to avoid patterns in input
	    size_t j = (rand () >> 16) % thread_num_;
	    const size_t till = j + thread_num_;
	    for (; j < till && !queues_[j % thread_num_].enqueue (job); ++j);
	    if (j < till)
	       break;

	    // no need to yield on last try
	    if ((tries + 1) < max_tries)
	    {
	       // no empty queues? yield!
	       std::this_thread::yield ();
	    }
	 }

	 // done?
	 if (tries < max_tries)
	    break;

	 // busy waiting didn't work? sleep!
	 wait_threads ();
      }
   }

   void join_maps (map_t & final, const map_t & map)
   {
      auto fi = final.begin ();
      auto mi = map.begin ();

      // join
      while (fi != final.end () && mi != map.end ())
      {
	 if (fi->first < mi->first)
	 {
	    ++fi;
	 }
	 else if (fi->first > mi->first)
	 {
	    final.insert (fi, *mi);
	    ++mi;
	 }
	 else 
	 {
	    assert (fi->first == mi->first);
	    fi->second = std::max (fi->second, mi->second);
	    ++fi;
	    ++mi;
	 }
      }

      // append map tail
      for (; mi != map.end (); ++mi)
	 final.insert (final.end (), *mi);
   }

public:
   factorizer_t (const size_t thread_num) 
      : thread_num_ (thread_num)
      , queues_ (new queue_t[thread_num_])
      , maps_ (thread_num_)
   {
      srand (static_cast<unsigned int> (time (0)));
   }

   template<typename Producer, typename Func>
   void operator() (map_t & final, Producer & producer, Func & func)
   {
      auto & cv = cv_; // don't want to capture 'this'

      // worker routine
      auto worker = [&cv, &func] (queue_t & q, map_t & m) {
	 job_t job;
	 while (!job.end)
	 {
	    // busy wait if no job
	    while (!q.dequeue (job))
	    {
	       // wake him up!
	       cv.notify_one ();
	       std::this_thread::yield ();
	    }

	    // notify that queue has room
	    cv.notify_one ();

	    // do the job
	    if (!job.end)
	       func (job.data, m);
	 }

	 // release fence to make sure all data written by this thread is visible
	 std::atomic_thread_fence (std::memory_order_release);
      };

      // release fence to make sure workers see all data we've written
      std::atomic_thread_fence (std::memory_order_release);

      // start workers
      start_threads (worker);

      // push jobs
      for (auto data: producer)
	 assign_job (data);

      // join
      join_threads ();

      // acquire fence to make sure all data written by threads is visible
      std::atomic_thread_fence (std::memory_order_acquire);

      // join maps
      for (auto m: maps_)
	 join_maps (final, m);
   }
};

// sieve that takes time to build, but gives 20x speed improvement
class sieve_t
{
   typedef std::deque<uint_t> primes_t;
   primes_t primes_;

public:
   sieve_t ()
   {
      static const int uint_digits = std::numeric_limits<uint_t>::digits;
      static const uint_t prime_max = 
	 (static_cast<uint_t> (1) << ((uint_digits + 1) / 2)) + 1;
      typedef std::bitset<prime_max> sieve_t;

      std::unique_ptr<sieve_t> sieve_owner (new sieve_t ());
      sieve_t & sieve = *sieve_owner;

      uint_t last_prime = 0;
      for (uint_t i = 2; i < sieve.size (); ++i)
      {
	 if (sieve[i])
	    continue;

	 primes_.push_back (i - last_prime);
	 last_prime = i;

	 for (uint_t j = i * i; j > i && j < sieve.size (); ++j)
	    sieve[j] = true;
      }
   }

   size_t size () const
   {
      return primes_.size ();
   }

   uint_t prime (const size_t index) const
   { 
      return primes_[index]; 
   }
   
};

// simple factorization using modulo
static void
factorize (uint_t number, map_t & map)
{
   prime_counter_t counter;
   for (uint_t i = 2; i < number; ++i)
   {
      const uint_t sqr = i * i;
      if (sqr < i || sqr > number)
	 break;

      for (; (number % i) == 0; number /= i)
	 counter.count (i);
   }

   if (number > 1)
      counter.count (number);

   counter.update (map);
}

// functor that uses sieve for factorization
template<typename Sieve>
class sieve_factorize_t
{
   const Sieve & sieve_;
public:
   sieve_factorize_t (const Sieve & sieve) : sieve_ (sieve) {}

   void operator () (uint_t number, map_t & map) 
   {
      prime_counter_t counter;
      const size_t size = sieve_.size ();
      uint_t prime = 0;
      for (size_t i = 0; i < size; ++i)
      {
	 prime += sieve_.prime (i);
	 if ((prime * prime) > number)
	    break;

	 for (; (number % prime) == 0; number /= prime)
	    counter.count (prime);
      }
      if (number > 1)
	 counter.count (prime);

      counter.update (map);
   }
};

// no concurrency overhead
static void
single_threaded (map_t & map)
{
   producer_t p;
   for (auto n: p)
      factorize (n, map);
}

// multi-threaded factorization using modulo
static void
modulo (map_t & map, const size_t threads)
{
   factorizer_t<uint_t, queue_size> fact (threads);
   fact (map, producer_t (), factorize);
}

// multi-threaded factorization using sieve
static void
sieve (map_t & map, const size_t threads)
{
   const sieve_t sieve;
   sieve_factorize_t<sieve_t> factorize (sieve);
   factorizer_t<uint_t, queue_size> proc (threads);
   proc (map, producer_t (), factorize);
}

static void
help ()
{
   std::cout
      << "Factorize integers from standard input" << std::endl
      << "Usage: factorize [mode] [threads]" << std::endl
      << " modulo - default mode, uses modulo" << std::endl
      << " sieve  - uses sieve (20x speedup for 200 sec to build sieve)" << std::endl
      << " single - single threaded mode using modulo" << std::endl;
}

int
main (int argc, char *argv[])
{
   size_t threads = 0;
   if (argc > 2)
      threads = atoi (argv[2]);
   if (threads == 0)
      threads = 1;

   // default mode
   std::string mode = "modulo";
   if (argc > 1)
      mode = argv[1];

   // container for results
   map_t map;

   if (mode == "single")
   {
      single_threaded (map);
   }
   else if (mode == "modulo")
   {
      modulo (map, threads);
   }
   else if (mode == "sieve")
   {
      sieve (map, threads);
   }
   else if (mode == "help")
   {
      help ();
      return 1;
   }
   else
   {
      std::cerr << "Unknown mode" << std::endl;
      return 1;
   }

   for (auto i: map)
      for (uint_t p = 0; p < i.second; ++p)
	 std::cout << i.first << std::endl;

   return 0;
}
