include "alldifferent.mzn";
int: n;
array[1..n] of var 1..n: q;
constraint alldifferent(q);
constraint alldifferent([q[i] + i | i in 1..n]);
constraint alldifferent([q[i] - i | i in 1..n]);
solve satisfy;
