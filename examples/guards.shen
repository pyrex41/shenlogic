(define sign
  { number --> symbol }
  X -> negative where (< X 0)
  0 -> zero
  X -> positive)
