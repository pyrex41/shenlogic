(define helper
  { number --> boolean }
  X -> true)

(define guarded-call
  { number --> symbol }
  X -> yes where (helper X)
  _ -> no)
