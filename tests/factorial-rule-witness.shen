\\ Ground instantiation witness for compiled factorial rules.
\\ Loads tests/golden/factorial.slir and checks two substitutions:
\\   factorial_c0_p0 with a0=0 derives 1
\\   factorial_c1_p1 chain 1..5 derives 120
\\ Not eval iff T(P), and not Lean Derives.
\\ certificate-instantiate only replaces a whole term (toy fact replay);
\\ compiled rules need a walk, which is local to this file.

(define rules-witness.theory
  -> (let Ir (hd (read-from-string-unprocessed
                   (read-file-as-string "tests/golden/factorial.slir")))
        (if (and (cons? Ir)
                 (= (hd Ir) shenlogic-ir)
                 (= (hd (tl Ir)) 2))
            (hd (tl (tl Ir)))
            false)))

(define rules-witness.rules
  [theory _ _ Rs | _] -> Rs
  [theory _ Rs | _] -> Rs
  _ -> [])

(define rules-witness.rule
  Id Theory -> (certificate-rule Id (rules-witness.rules Theory)))

(define rules-witness.function
  [rule _ F _ _ _ _ _ _] -> F
  [rule _ F _ _ _ _] -> F)

(define rules-witness.args
  [rule _ _ _ _ A _ _ _] -> A
  [rule _ _ A _ _ _] -> A)

(define rules-witness.lookup
  X [] -> X
  X [[A B] | S] -> (if (= X A) B (rules-witness.lookup X S)))

(define rules-witness.inst
  X S -> (let F (rules-witness.lookup X S)
           (if (not (= F X))
               F
               (if (cons? X)
                   (rules-witness.inst-list X S)
                   X))))

(define rules-witness.inst-list
  [] _ -> []
  [X | Xs] S -> [(rules-witness.inst X S) | (rules-witness.inst-list Xs S)]
  X _ -> X)

(define rules-witness.eval-int
  [i-lit N] -> (if (number? N) [ok N] [error])
  [i-sub A B] -> (let X (rules-witness.eval-int A)
                   (let Y (rules-witness.eval-int B)
                     (if (and (= (hd X) ok) (= (hd Y) ok))
                         [ok (- (hd (tl X)) (hd (tl Y)))]
                         [error])))
  [i-mul A B] -> (let X (rules-witness.eval-int A)
                   (let Y (rules-witness.eval-int B)
                     (if (and (= (hd X) ok) (= (hd Y) ok))
                         [ok (* (hd (tl X)) (hd (tl Y)))]
                         [error])))
  _ -> [error])

(define rules-witness.eval-value
  [v-int I] -> (let N (rules-witness.eval-int I)
                 (if (= (hd N) ok)
                     [ok [v-int [i-lit (hd (tl N))]]]
                     [error]))
  v-true -> [ok v-true]
  v-false -> [ok v-false]
  _ -> [error])

(define rules-witness.eval-values
  [] -> [ok []]
  [X | Xs] -> (let A (rules-witness.eval-value X)
                (let B (rules-witness.eval-values Xs)
                  (if (and (= (hd A) ok) (= (hd B) ok))
                      [ok [(hd (tl A)) | (hd (tl B))]]
                      [error]))))

(define rules-witness.premise?
  [value-eq A B] _ -> (let X (rules-witness.eval-value A)
                        (let Y (rules-witness.eval-value B)
                          (and (= (hd X) ok)
                               (= (hd Y) ok)
                               (= (hd (tl X)) (hd (tl Y))))))
  [value-neq A B] _ -> (let X (rules-witness.eval-value A)
                         (let Y (rules-witness.eval-value B)
                           (and (= (hd X) ok)
                                (= (hd Y) ok)
                                (not (= (hd (tl X)) (hd (tl Y)))))))
  [call Name Args Result] Facts ->
    (let As (rules-witness.eval-values Args)
      (let R (rules-witness.eval-value Result)
        (and (= (hd As) ok)
             (= (hd R) ok)
             (element? [Name (hd (tl As)) (hd (tl R))] Facts))))
  _ _ -> false)

(define rules-witness.premises?
  [] _ -> true
  [P | Ps] Facts -> (and (rules-witness.premise? P Facts)
                         (rules-witness.premises? Ps Facts)))

(define rules-witness.step
  Rule Sub Facts ->
    (if (= Rule false)
        false
        (let Premises (rules-witness.inst-list (certificate-rule-premises Rule) Sub)
          (if (rules-witness.premises? Premises Facts)
              (let Args (rules-witness.inst-list (rules-witness.args Rule) Sub)
                (let Result (rules-witness.inst (certificate-rule-result Rule) Sub)
                  (let As (rules-witness.eval-values Args)
                    (let R (rules-witness.eval-value Result)
                      (if (and (= (hd As) ok) (= (hd R) ok))
                          [ok [(rules-witness.function Rule)
                               (hd (tl As))
                               (hd (tl R))]]
                          false)))))
              false))))

(define rules-witness.chain
  [] Facts -> [ok Facts]
  [[Rule Sub] | Steps] Facts ->
    (let R (rules-witness.step Rule Sub Facts)
      (if (= R false)
          false
          (rules-witness.chain Steps [(hd (tl R)) | Facts]))))

(define rules-witness.sub0
  N -> [[[v-var factorial_a0] [v-int [i-lit N]]]])

(define rules-witness.r0
  -> (intern "R0"))

(define rules-witness.sub1
  N R -> [[[v-var factorial_a0] [v-int [i-lit N]]]
          [[i-var factorial_a0] [i-lit N]]
          [[v-var (rules-witness.r0)] [v-int [i-lit R]]]
          [[i-var (rules-witness.r0)] [i-lit R]]])

(define rules-witness.zero
  -> (let T (rules-witness.theory)
        (let C0 (rules-witness.rule factorial_c0_p0 T)
          (= (rules-witness.step C0 (rules-witness.sub0 0) [])
             [ok [factorial [[v-int [i-lit 0]]] [v-int [i-lit 1]]]]))))

(define rules-witness.five
  -> (let T (rules-witness.theory)
        (let C0 (rules-witness.rule factorial_c0_p0 T)
          (let C1 (rules-witness.rule factorial_c1_p1 T)
            (let R (rules-witness.chain
                      [[C0 (rules-witness.sub0 0)]
                       [C1 (rules-witness.sub1 1 1)]
                       [C1 (rules-witness.sub1 2 1)]
                       [C1 (rules-witness.sub1 3 2)]
                       [C1 (rules-witness.sub1 4 6)]
                       [C1 (rules-witness.sub1 5 24)]]
                      [])
              (and (cons? R)
                   (= (hd R) ok)
                   (element? [factorial [[v-int [i-lit 5]]] [v-int [i-lit 120]]]
                             (hd (tl R)))))))))
