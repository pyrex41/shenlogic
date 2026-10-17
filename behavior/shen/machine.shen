\\ State: [store resources emitted receipts]. Model values are bounded integers,
\\ strings and booleans. Effects are intents; adapters realize them separately.
(define bt.checked X -> (if (bt.integer? X) X (simple-error "integer overflow")))
(define bt.bool X -> (if (boolean? X) X (simple-error "boolean required")))
(define bt.num X -> (if (bt.integer? X) X (simple-error "integer required")))
(define bt.eval ["lit" X] _ _ -> X
  ["get" K] Store _ -> (bt.lookup K Store)
  ["input" K] _ Input -> (bt.lookup K Input)
  ["not" X] S I -> (not (bt.bool (bt.eval X S I)))
  ["and" X Y] S I -> (and (bt.bool (bt.eval X S I)) (bt.bool (bt.eval Y S I)))
  ["or" X Y] S I -> (or (bt.bool (bt.eval X S I)) (bt.bool (bt.eval Y S I)))
  ["=" X Y] S I -> (= (bt.eval X S I) (bt.eval Y S I))
  ["<" X Y] S I -> (< (bt.num (bt.eval X S I)) (bt.num (bt.eval Y S I)))
  ["<=" X Y] S I -> (<= (bt.num (bt.eval X S I)) (bt.num (bt.eval Y S I)))
  ["+" X Y] S I -> (bt.checked (+ (bt.num (bt.eval X S I)) (bt.num (bt.eval Y S I))))
  ["-" X Y] S I -> (bt.checked (- (bt.num (bt.eval X S I)) (bt.num (bt.eval Y S I))))
  ["*" X Y] S I -> (bt.checked (* (bt.num (bt.eval X S I)) (bt.num (bt.eval Y S I))))
  _ _ _ -> (simple-error "unsupported expression"))
(define bt.run P State Input Fuel ->
  (if (> Fuel 0)
    (trap-error (bt.exec P State Input Fuel) (/. Ex ["error" State (error-to-string Ex) Fuel]))
    ["inconclusive" State "fuel exhausted" 0]))
(define bt.exec P State Input Fuel -> ["inconclusive" State "fuel exhausted" 0] where (<= Fuel 0)
  ["skip"] State _ F -> ["ok" State (- F 1)]
  ["require" X] [S R E D] I F -> (if (bt.bool (bt.eval X S I)) ["ok" [S R E D] (- F 1)] ["error" [S R E D] "requirement failed" (- F 1)])
  ["put" K X] [S R E D] I F -> ["ok" [(bt.store K (bt.eval X S I) S) R E D] (- F 1)]
  ["emit" K X] [S R E D] I F -> ["ok" [S R (append E [[K (bt.eval X S I)]]) D] (- F 1)]
  ["consume" K] [S R E D] _ F -> ["ok" [S (bt.atom-out ["consume" K] R) E D] (- F 1)]
  ["produce" K] [S R E D] _ F -> ["ok" [S (bt.atom-out ["produce" K] R) E D] (- F 1)]
  ["seq" P Q] State I F -> (bt.run-next Q I (bt.run P State I (- F 1)))
  ["case" X P Q] [S R E D] I F -> (bt.run (if (bt.bool (bt.eval X S I)) P Q) [S R E D] I (- F 1))
  ["repeat" N P] State I F -> (bt.loop N P State I (- F 1))
  ["atomic" P] State I F -> (bt.rollback State (bt.run P State I (- F 1)))
  ["once" K P] [S R E D] I F -> (bt.once K P [S R E D] I (- F 1) (bt.lookup K I))
  _ State _ F -> ["error" State "unsupported program" F])
(define bt.run-next Q I ["ok" State F] -> (bt.run Q State I F) _ _ R -> R)
(define bt.loop 0 _ State _ F -> ["ok" State F]
  N P State I F -> (bt.loop-next (- N 1) P I (bt.run P State I F)))
(define bt.loop-next N P I ["ok" State F] -> (bt.loop N P State I F) _ _ _ R -> R)
(define bt.rollback _ ["ok" State F] -> ["ok" State F]
  Original ["error" _ Why F] -> ["error" Original Why F]
  Original ["inconclusive" _ Why F] -> ["inconclusive" Original Why F])
(define bt.once K P [S R E D] I F Id ->
  (if (bt.has [K Id] D)
    (if (= (bt.lookup [K Id] D) [P I]) ["ok" [S R E D] F] ["error" [S R E D] "request identity conflict" F])
    (bt.receipt [S R E D] K Id P I (bt.run P [S R E D] I F))))
(define bt.receipt _ K Id P I ["ok" [S R E D] F] -> ["ok" [S R E (bt.store [K Id] [P I] D)] F]
  Original _ _ _ _ Result -> (bt.rollback Original Result))

\\ Observation admission retains alternate worlds for unknown commit.
(define bt.observe P State Input "completed" F -> (bt.run P State Input F)
  P State Input "not-committed" F -> ["alternatives" [State]]
  P State Input "unknown-commit" F -> (bt.unknown State (bt.run P State Input F))
  _ State _ _ _ -> ["inconclusive" State "unknown observation" 0])
(define bt.unknown Old ["ok" New _] -> ["alternatives" (if (= Old New) [Old] [Old New])]
  Old ["error" New Why F] -> ["alternatives" (if (= Old New) [Old] [Old New])]
  Old ["inconclusive" _ Why F] -> ["inconclusive" Old Why F])

\\ Explicit graph is derived from program syntax. IDs are traversal paths.
(define bt.graph P -> (bt.graph-h P "root"))
(define bt.graph-h ["seq" P Q] Id ->
  (append [[Id "sequence" [(cn Id ".a") (cn Id ".b")]]]
    (append (bt.graph-h P (cn Id ".a")) (bt.graph-h Q (cn Id ".b"))))
  ["case" C P Q] Id ->
  (append [[Id "choice" [(cn Id ".yes") (cn Id ".no")]]]
    (append (bt.graph-h P (cn Id ".yes")) (bt.graph-h Q (cn Id ".no"))))
  ["repeat" N P] Id -> (append [[Id "repeat" [(cn Id ".body")]]]
    (bt.graph-h P (cn Id ".body")))
  ["atomic" P] Id -> (append [[Id "atomic" [(cn Id ".body")]]] (bt.graph-h P (cn Id ".body")))
  ["once" K P] Id -> (append [[Id "once" [(cn Id ".body")]]] (bt.graph-h P (cn Id ".body")))
  P Id -> [[Id "primitive" P]])

\\ Trace judgments compare observations to reachable worlds. Partial effect
\\ records are subsequences, never treated as complete delivery histories.
(define bt.observed-store? [] _ -> true [[K V] | Xs] S -> (and (bt.has K S) (and (= V (bt.lookup K S)) (bt.observed-store? Xs S))))
(define bt.subsequence? [] _ -> true _ [] -> false [X | Xs] [X | Ys] -> (bt.subsequence? Xs Ys) Xs [_ | Ys] -> (bt.subsequence? Xs Ys))
(define bt.matches? [S _ E _] Seen Effects Complete ->
  (and (bt.observed-store? Seen S) (if Complete (= Effects E) (bt.subsequence? Effects E))))
(define bt.filter-worlds [] _ _ _ -> [] [W | Ws] S E C ->
  (if (bt.matches? W S E C) [W | (bt.filter-worlds Ws S E C)] (bt.filter-worlds Ws S E C)))
(define bt.judge Worlds Seen Effects Complete ->
  (bt.judge-result (bt.filter-worlds Worlds Seen Effects Complete) Complete))
(define bt.judge-result [] _ -> ["violation" []]
  Worlds true -> ["compatible" Worlds]
  Worlds false -> ["inconclusive" Worlds])
