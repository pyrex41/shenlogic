\\ Human-review equations in the notation of the motivating example.

(declare surface.translate [A --> string])
(declare surface.definitions [A --> string])
(declare surface.clauses [A --> [B --> [C --> string]]])
(declare surface.clause [A --> [B --> [C --> string]]])
(declare surface.call [A --> [B --> string]])
(declare surface.exclusions [A --> [B --> C]])
(declare surface.applicable [A --> [B --> string]])
(declare surface.match-many [A --> [B --> [C --> [D --> E]]]])
(declare surface.match [A --> [B --> [C --> [D --> E]]]])
(declare surface.guard-condition [A --> [B --> C]])
(declare surface.substitute [A --> [B --> C]])
(declare surface.substitute-list [A --> [B --> C]])
(declare surface.lookup [A --> [B --> C]])
(declare surface.conjunction [A --> string])
(declare surface.formulas [A --> string])
(declare surface.formula [A --> string])
(declare surface.term [A --> string])
(declare surface.terms [A --> string])
(declare surface.cons-form? [A --> boolean])
(declare surface.list-term [A --> string])
(declare surface.list-items [A --> string])
(declare surface.variables [A --> [B --> C]])
(declare surface.vars [A --> B])
(declare surface.vars-list [A --> B])
(declare surface.unique [A --> A])
(declare surface.quantify [A --> [string --> string]])

(define surface.translate
  [program Definitions] -> (surface.definitions Definitions))

(define surface.definitions
  [] -> ""
  [[definition Name _ Clauses _] | Ds] ->
    (cn (surface.clauses Name Clauses [] ) (surface.definitions Ds)))

(define surface.clauses
  _ [] _ -> ""
  Name [C | Cs] Prior ->
    (cn (surface.clause Name C Prior)
        (surface.clauses Name Cs [C | Prior])))

(define surface.clause
  Name [clause _ Patterns Guard Body] Prior ->
    (let Equation (cn "(" (cn (surface.call Name Patterns)
                       (cn " = " (cn (surface.term Body) ")"))))
      (let Conditions (append (surface.exclusions (reverse Prior) Patterns)
                              (surface.guard-condition Guard []))
        (let Proposition (if (= Conditions []) Equation
                             (cn "(" (cn (surface.conjunction Conditions)
                               (cn " => " (cn Equation ")")))))
          (cn (surface.quantify (surface.variables Patterns []) Proposition)
              (n->string 10))))))

(define surface.call
  Name [] -> (cn "(" (cn (str Name) ")"))
  Name Args -> (cn "(" (cn (str Name) (cn " "
                 (cn (surface.terms Args) ")")))))

(define surface.exclusions
  [] _ -> []
  [C | Cs] Patterns ->
    (cons (cn "(~ " (cn (surface.applicable C Patterns) ")"))
          (surface.exclusions Cs Patterns)))

(define surface.applicable
  [clause _ PriorPatterns Guard _] Patterns ->
    (let Matched (surface.match-many PriorPatterns Patterns [] [])
      (let Env (hd (tl Matched))
        (let Conditions (hd (tl (tl Matched)))
          (surface.conjunction
            (append Conditions (surface.guard-condition Guard Env)))))))

(define surface.match-many
  [] [] Env Conditions -> [matched Env (reverse Conditions)]
  [P | Ps] [A | As] Env Conditions ->
    (let R (surface.match P A Env Conditions)
      (surface.match-many Ps As (hd (tl R)) (hd (tl (tl R)))))
  _ _ Env Conditions -> [matched Env [false | Conditions]])

(define surface.match
  P A Env Conditions ->
    (if (= P _)
        [matched Env Conditions]
        (if (variable? P)
            (let Old (surface.lookup P Env)
              (if (= Old not-found)
                  [matched [[P A] | Env] Conditions]
                  [matched Env [[= (hd (tl Old)) A] | Conditions]]))
        (if (and (surface.cons-form? P) (surface.cons-form? A))
            (let H (surface.match (hd (tl P)) (hd (tl A)) Env Conditions)
              (surface.match (hd (tl (tl P))) (hd (tl (tl A)))
                (hd (tl H)) (hd (tl (tl H)))))
            [matched Env [[= A P] | Conditions]]))))

(define surface.guard-condition
  none _ -> []
  [some G] Env -> [(surface.substitute G Env)]
  G Env -> [(surface.substitute G Env)])

(define surface.substitute
  X Env ->
    (if (variable? X)
        (let Found (surface.lookup X Env)
          (if (= Found not-found) X (hd (tl Found))))
        (if (cons? X)
            (surface.substitute-list X Env)
            X)))

(define surface.substitute-list
  [] _ -> []
  [X | Xs] Env -> [(surface.substitute X Env) |
                   (surface.substitute-list Xs Env)])

(define surface.lookup
  _ [] -> not-found
  X [[X V] | _] -> [found V]
  X [_ | Rest] -> (surface.lookup X Rest))

(define surface.conjunction
  [] -> "true"
  [X] -> (surface.formula X)
  Xs -> (cn "(and " (cn (surface.formulas Xs) ")")))

(define surface.formulas
  [] -> ""
  [X] -> (surface.formula X)
  [X | Xs] -> (cn (surface.formula X) (cn " " (surface.formulas Xs))))

(define surface.formula
  true -> "true"
  false -> "false"
  X -> X where (string? X)
  [= A B] -> (cn "(" (cn (surface.term A) (cn " = "
                 (cn (surface.term B) ")"))))
  X -> (surface.term X))

(define surface.term
  X ->
    (if (cons? X)
        (if (surface.cons-form? X)
            (surface.list-term X)
            (cn "(" (cn (surface.terms X) ")")))
        (str X)))

(define surface.terms
  [] -> ""
  [X] -> (surface.term X)
  [X | Xs] -> (cn (surface.term X) (cn " " (surface.terms Xs))))

(define surface.cons-form?
  [cons _ _] -> true
  _ -> false)

(define surface.list-term
  X -> (cn "[" (cn (surface.list-items X) "]")))

(define surface.list-items
  [] -> ""
  [cons H []] -> (surface.term H)
  [cons H T] ->
    (if (surface.cons-form? T)
        (cn (surface.term H) (cn " " (surface.list-items T)))
        (cn (surface.term H) (cn " | " (surface.term T))))
  X -> (surface.term X))

(define surface.variables
  [] Acc -> (reverse (surface.unique Acc))
  [P | Ps] Acc -> (surface.variables Ps (append (surface.vars P) Acc)))

(define surface.vars
  X ->
    (if (= X _)
        []
        (if (variable? X) [X]
        (if (cons? X) (surface.vars-list X) []))))

(define surface.vars-list
  [] -> []
  [X | Xs] -> (append (surface.vars X) (surface.vars-list Xs)))

(define surface.unique
  [] -> []
  [X | Xs] -> (if (element? X Xs) (surface.unique Xs)
                  [X | (surface.unique Xs)]))

(define surface.quantify
  [] Proposition -> Proposition
  [X | Xs] Proposition ->
    (cn "(all " (cn (str X) (cn " "
      (cn (surface.quantify Xs Proposition) ")")))))
