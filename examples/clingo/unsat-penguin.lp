% Default with exception: birds fly unless they are penguins.
% Claim: sam does not fly. Forbid the claim's negation; unsat proves it.
bird(tweety). bird(sam). penguin(sam).
flies(X) :- bird(X), not penguin(X).
:- not flies(sam).
