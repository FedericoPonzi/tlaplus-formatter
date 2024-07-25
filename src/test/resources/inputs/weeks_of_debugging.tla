This code is from the talk SREcon20 Americas - Weeks of Debugging Can Save You Hours of TLA+ by Markus A. Kuppe.
https://www.youtube.com/watch?v=wjsI0lTSjIo


void *producer(void * arg) {
    while(1) {
        pthread_mutex_lock(&mutex); // acquire the lock
        while(count == buff_size) // check if the buffer is full
            pthread_cond_wait(&modify, &mutex);
        append(rand() % (10)); // produce!

        pthread_cond_signal(&modify); // broadcast that the buffer is full
        pthread_mutex_unlock(&mutex); // release the lock
    }
}

void *consumer(void * arg) {
    long report = 0;
    while(1) {
        pthread_mutex_lock(&mutex); // acquire the lock

        while(count == 0) // check if the buffer is empty
            pthread_cond_wait(&modify, &mutex); // wait for the buffer

        head(); // consume (we don't care about the value)
        pthread_cond_signal(&modify); // signal that the buffer is empty
        pthread_mutex_unlock(&mutex); // release the lock

        if (report++ % 10000 == 0) {
            printf("\n%ld values consumed", report);
        }
    }
}

It contains some concurrency bug, the goal of this spec is to spot it.

In order to understand the below spec, it's good to understand the semantics of pthread_cond_wait/cond_signal.

Condition variables work in this way: a condition modify, is protected by a mutex "mutex".
The thread shall acquire the mutex, then when pthread_cond_wait will unlock the mutex and put it to sleep.
When pthread_cond_signal is called over "modify", the thread will be weaken up and it will try to re-acquire
the lock on mutex. Because clearly it's a waste of energy to wake multiple threads if all of them are going to try to
take ownership of the same mutex (only one of them will win while the other will go back to sleep), pthread_cond_signal
optimizes this by sending a signal to a random thread waiting to be waken up.

So to recap, even if multiple threads are waiting on the mutex, only one of them will get the signal and actively try to
acquire the lock.

After solving the problem, the configuation matters: the program works well with one consumer and one producer, but
deadlocks with a confiugration that has two or more of either. The buffer size doesn't really matter.


---- MODULE weeks_of_debugging ----
EXTENDS TLC, Sequences, Naturals, FiniteSets
CONSTANT BufferSize, Producers, Consumers

ASSUME BufferSize > 0
ASSUME Cardinality(Producers) > 0
ASSUME Cardinality(Consumers) > 0

baitinv == TRUE
\*baitinv ==  TLCGet("level") < 11

empty == "empty"
All == Consumers \cup Producers

(* --algorithm weeks_of_debugging {
    variables mutex = empty,
              buffer = 0,
              signaled = empty,
              waitgroup = {};
    define {
        TypeOk == /\ buffer >= 0
                  /\ buffer <= BufferSize
                  /\ signaled \in All \cup {empty}
                  /\ mutex \in All \cup {empty}
                  /\ waitgroup \subseteq All

        IsBufferFull == buffer = BufferSize
        IsBufferEmpty == buffer = 0

        Inv == waitgroup # Producers \cup Consumers
    }
    fair process (prod \in Producers) {
PROD:
        while(TRUE) {
            await mutex = empty;
            mutex := self;
PROD1:
            while(IsBufferFull) {
                mutex := empty;
                waitgroup := waitgroup \cup {self};
PROD3:
                await mutex = empty /\ signaled = self;
                mutex := self;
                signaled := empty;
            };
PRODUCING:
            buffer := buffer +1;
            with (t \in waitgroup) {
                signaled := t;
                waitgroup := waitgroup \ {t};
            };
            mutex := empty;
        }
    }
\* Consumer is specular to Producer, but
\* waits until buffer is not empty and reduces buffer length
    fair process (cons \in Consumers) {
CONS:
        while(TRUE) {
            await mutex = empty;
            mutex := self;
CONS1:
            while(IsBufferEmpty) {
                mutex := empty;
                waitgroup := waitgroup \cup {self};
CONS3:
                await mutex = empty /\ signaled = self;
                mutex := self;
                signaled := empty;
            };
CONSUMING:
            buffer := buffer -1;
            with (t \in waitgroup) {
                signaled := t;
                waitgroup := waitgroup \ {t};
            };
            mutex := empty;
        }
    }
} *)
\* BEGIN TRANSLATION (chksum(pcal) = "c5ad8119" /\ chksum(tla) = "4d498a1a")
VARIABLES mutex, buffer, signaled, waitgroup, pc

(* define statement *)
TypeOk == /\ buffer >= 0
          /\ buffer <= BufferSize
          /\ signaled \in All \cup {empty}
          /\ mutex \in All \cup {empty}
          /\ waitgroup \subseteq All

IsBufferFull == buffer = BufferSize
IsBufferEmpty == buffer = 0

Inv == waitgroup # Producers \cup Consumers


vars == << mutex, buffer, signaled, waitgroup, pc >>

ProcSet == (Producers) \cup (Consumers)

Init == (* Global variables *)
        /\ mutex = empty
        /\ buffer = 0
        /\ signaled = empty
        /\ waitgroup = {}
        /\ pc = [self \in ProcSet |-> CASE self \in Producers -> "PROD"
                                        [] self \in Consumers -> "CONS"]

PROD(self) == /\ pc[self] = "PROD"
              /\ mutex = empty
              /\ mutex' = self
              /\ pc' = [pc EXCEPT ![self] = "PROD1"]
              /\ UNCHANGED << buffer, signaled, waitgroup >>

PROD1(self) == /\ pc[self] = "PROD1"
               /\ IF IsBufferFull
                     THEN /\ mutex' = empty
                          /\ waitgroup' = (waitgroup \cup {self})
                          /\ pc' = [pc EXCEPT ![self] = "PROD3"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "PRODUCING"]
                          /\ UNCHANGED << mutex, waitgroup >>
               /\ UNCHANGED << buffer, signaled >>

PROD3(self) == /\ pc[self] = "PROD3"
               /\ mutex = empty /\ signaled = self
               /\ mutex' = self
               /\ signaled' = empty
               /\ pc' = [pc EXCEPT ![self] = "PROD1"]
               /\ UNCHANGED << buffer, waitgroup >>

PRODUCING(self) == /\ pc[self] = "PRODUCING"
                   /\ buffer' = buffer +1
                   /\ \E t \in waitgroup:
                        /\ signaled' = t
                        /\ waitgroup' = waitgroup \ {t}
                   /\ mutex' = empty
                   /\ pc' = [pc EXCEPT ![self] = "PROD"]

prod(self) == PROD(self) \/ PROD1(self) \/ PROD3(self) \/ PRODUCING(self)

CONS(self) == /\ pc[self] = "CONS"
              /\ mutex = empty
              /\ mutex' = self
              /\ pc' = [pc EXCEPT ![self] = "CONS1"]
              /\ UNCHANGED << buffer, signaled, waitgroup >>

CONS1(self) == /\ pc[self] = "CONS1"
               /\ IF IsBufferEmpty
                     THEN /\ mutex' = empty
                          /\ waitgroup' = (waitgroup \cup {self})
                          /\ pc' = [pc EXCEPT ![self] = "CONS3"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "CONSUMING"]
                          /\ UNCHANGED << mutex, waitgroup >>
               /\ UNCHANGED << buffer, signaled >>

CONS3(self) == /\ pc[self] = "CONS3"
               /\ mutex = empty /\ signaled = self
               /\ mutex' = self
               /\ signaled' = empty
               /\ pc' = [pc EXCEPT ![self] = "CONS1"]
               /\ UNCHANGED << buffer, waitgroup >>

CONSUMING(self) == /\ pc[self] = "CONSUMING"
                   /\ buffer' = buffer -1
                   /\ \E t \in waitgroup:
                        /\ signaled' = t
                        /\ waitgroup' = waitgroup \ {t}
                   /\ mutex' = empty
                   /\ pc' = [pc EXCEPT ![self] = "CONS"]

cons(self) == CONS(self) \/ CONS1(self) \/ CONS3(self) \/ CONSUMING(self)

Next == (\E self \in Producers: prod(self))
           \/ (\E self \in Consumers: cons(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Producers : WF_vars(prod(self))
        /\ \A self \in Consumers : WF_vars(cons(self))

\* END TRANSLATION


====

