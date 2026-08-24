(shenlogic-repair 1
  (expect (factorial 0) 2)
  (law (all X : number
         ((X = 0) => ((factorial X) = 2)))))
