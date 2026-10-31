% "Some bird flies" does not entail "every bird flies".
fof(tweety, axiom, bird(tweety) & flies(tweety)).
fof(pingu, axiom, bird(pingu)).
fof(goal, conjecture, ! [X] : (bird(X) => flies(X))).
