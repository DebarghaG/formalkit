/* No ltl block: checks assertions and invalid end states (deadlock). */
chan c = [0] of { byte };
active proctype A() { c ! 1; c ! 2 }
active proctype B() { byte x; c ? x }
