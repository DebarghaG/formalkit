% Claim: 4 pigeons cannot fit in 3 holes one-per-hole. A solution would refute it; unsat proves it.
include "alldifferent.mzn";
array[1..4] of var 1..3: hole;
constraint alldifferent(hole);
solve satisfy;
