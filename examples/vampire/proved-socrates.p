fof(socrates_man, axiom, man(socrates)).
fof(men_mortal, axiom, ! [X] : (man(X) => mortal(X))).
fof(goal, conjecture, mortal(socrates)).
