---------------------- MODULE Playground ----------------------
EXTENDS Naturals, TLC, Integers
CONSTANTS N
SeqSum(x) == TRUE
Weighs(seq, wt) ==
  \E coef \in [1..N -> -1..1] :
      SeqSum([i \in 1..N |-> coef[i] * seq[i]]) = wt


==============================================================
