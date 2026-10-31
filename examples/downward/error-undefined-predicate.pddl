(define (domain switch)
  (:requirements :strips)
  (:predicates (on) (off))
  (:action turn-on :parameters () :precondition (off) :effect (and (lit) (not (off)))))
