(define (problem vault) (:domain rooms)
  (:objects hall kitchen vault - room)
  (:init (at hall) (connected hall kitchen) (connected kitchen hall))
  (:goal (at vault)))
