\\ User calls remain forbidden in guards in 0.2.
(define helper-v2
  { number --> boolean }
  X -> true)

(define guard-user-call-v2
  { number --> symbol }
  X -> yes where (helper-v2 X)
  _ -> no)
