; The robot needs the key to open the door, but the key is unreachable.
(define (domain rooms)
  (:requirements :strips :typing)
  (:types room)
  (:predicates (at ?r - room) (connected ?a ?b - room) (has-key))
  (:action move
    :parameters (?a ?b - room)
    :precondition (and (at ?a) (connected ?a ?b))
    :effect (and (at ?b) (not (at ?a))))
  (:action enter-vault
    :parameters (?a ?b - room)
    :precondition (and (at ?a) (has-key))
    :effect (and (at ?b) (not (at ?a)))))
