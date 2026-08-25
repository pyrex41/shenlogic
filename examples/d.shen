\\ README poison case: unguarded ((d N) = (+ 1 (d N))) classically yields 0 = 1.
(define d
  { number --> number }
  N -> (+ 1 (d N)))
