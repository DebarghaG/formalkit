% Two numbers in 1..10 summing to 12 with maximal product.
var 1..10: x;
var 1..10: y;
constraint x + y = 12;
solve maximize x * y;
