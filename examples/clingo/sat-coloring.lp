% 3-colour a triangle with a pendant vertex
node(1..4). edge(1,2). edge(2,3). edge(1,3). edge(3,4).
color(red;green;blue).
1 { col(N,C) : color(C) } 1 :- node(N).
:- edge(X,Y), col(X,C), col(Y,C).
#show col/2.
