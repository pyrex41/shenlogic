(shenlogic-repair 1
  (expect (factorial 0) 2)
  (expect (factorial 1) 2)
  (forbid (factorial 2) 2))
