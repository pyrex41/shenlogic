\\ A guard error blocks fallback; it is not the same as a false guard.
(define guard-error
  { number --> symbol }
  X -> yes where (+ true X)
  _ -> no)
