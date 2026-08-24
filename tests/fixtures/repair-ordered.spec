(shenlogic-repair 1
  (expect (classify -1) nonpositive)
  (expect (classify 0) nonpositive)
  (expect (classify 1) one)
  (expect (classify 2) two)
  (expect (classify 3) positive)
  (forbid (classify 0) negative))
