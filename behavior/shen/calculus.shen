\\ Behavioral calculus v1. Programs and proofs are inert data.
\\ Resources are affine names; no contraction rule exists.
(define bt.member X [] -> false X [X | _] -> true X [_ | Xs] -> (bt.member X Xs))
(define bt.unique [] -> true [X | Xs] -> (and (not (bt.member X Xs)) (bt.unique Xs)))
(define bt.remove X [X | Xs] -> Xs X [Y | Ys] -> [Y | (bt.remove X Ys)] _ [] -> [])
(define bt.union [] Ys -> Ys [X | Xs] Ys -> (if (bt.member X Ys) (bt.union Xs Ys) [X | (bt.union Xs Ys)]))
(define bt.subset [] _ -> true [X | Xs] Ys -> (and (bt.member X Ys) (bt.subset Xs Ys)))
(define bt.lookup K [[K V] | _] -> V K [_ | Xs] -> (bt.lookup K Xs) K [] -> (simple-error "missing binding"))
(define bt.has K [[K _] | _] -> true K [_ | Xs] -> (bt.has K Xs) _ [] -> false)
(define bt.store K V [] -> [[K V]] K V [[K _] | Xs] -> [[K V] | Xs] K V [X | Xs] -> [X | (bt.store K V Xs)])
(define bt.integer? X -> (and (number? X) (and (= X (round X)) (<= (abs X) 2147483647))))
(define bt.literal? X -> true where (or (string? X) (or (boolean? X) (bt.integer? X))) X -> false)
(define bt.expr? ["lit" X] -> (bt.literal? X)
  ["get" K] -> (string? K)
  ["input" K] -> (string? K)
  ["not" X] -> (bt.expr? X)
  [Op X Y] -> (and (bt.member Op ["+" "-" "*" "=" "<" "<=" "and" "or"]) (and (bt.expr? X) (bt.expr? Y)))
  _ -> false)
(define bt.safe-name? X -> (and (string? X) (not (= X ""))))
(define bt.atom-valid? ["skip"] -> true
  ["require" X] -> (bt.expr? X)
  ["put" K X] -> (and (bt.safe-name? K) (bt.expr? X))
  ["emit" K X] -> (and (bt.safe-name? K) (bt.expr? X))
  ["consume" K] -> (bt.safe-name? K)
  ["produce" K] -> (bt.safe-name? K)
  _ -> false)
(define bt.atom-out ["consume" K] In -> (if (bt.member K In) (bt.remove K In) (simple-error "resource absent"))
  ["produce" K] In -> (if (and (not (bt.member K In)) (bt.member (cn "mint:" K) In)) (append (bt.remove (cn "mint:" K) In) [K]) (simple-error "resource mint authority absent or duplicate"))
  _ In -> In)
(define bt.atom-effects ["put" K _] -> [["write" K]] ["emit" K _] -> [["emit" K]] _ -> [])
(define bt.atom-judgment? P In Out E ->
  (and (bt.atom-valid? P) (and (bt.unique In)
    (trap-error (and (= Out (bt.atom-out P In)) (= E (bt.atom-effects P))) (/. Ex false)))))
(define bt.repeat? N -> (and (bt.integer? N) (and (>= N 0) (<= N 1000))))

\\ Each constructor is a sequent rule, not a wrapper around inference.
(datatype bt-proof
  if (bt.atom-judgment? P In Out E)
  __________________________________________
  ["primitive"] : (bt-proof P In Out E);

  if (= E (bt.union E1 E2))
  A : (bt-proof P In Mid E1); B : (bt-proof Q Mid Out E2);
  __________________________________________
  ["sequence" Mid E1 E2 A B] : (bt-proof ("seq" P Q) In Out E);

  if (and (bt.expr? C) (= E (bt.union E1 E2)))
  A : (bt-proof P In Out E1); B : (bt-proof Q In Out E2);
  __________________________________________
  ["branches" E1 E2 A B] : (bt-proof ("case" C P Q) In Out E);

  if (bt.repeat? N)
  A : (bt-proof P In In E);
  __________________________________________
  ["invariant" A] : (bt-proof ("repeat" N P) In In E);

  A : (bt-proof P In Out E);
  __________________________________________
  ["transaction" A] : (bt-proof ("atomic" P) In Out E);

  if (bt.safe-name? K)
  A : (bt-proof P In In E);
  __________________________________________
  ["deduplicate" A] : (bt-proof ("once" K P) In In E);)

\\ Proof construction is separate from checking the resulting inhabitant.
(define bt.infer P In -> (trap-error (bt.infer-h P In) (/. Ex ["reject" (error-to-string Ex)])))
(define bt.infer-h ["seq" P Q] In -> (bt.infer-seq P Q In (bt.infer-h P In))
  ["case" C P Q] In -> (if (bt.expr? C) (bt.infer-case C P Q In (bt.infer-h P In) (bt.infer-h Q In)) (simple-error "invalid condition"))
  ["repeat" N P] In -> (if (bt.repeat? N) (bt.infer-wrap "invariant" In (bt.infer-h P In) true) (simple-error "invalid repeat bound"))
  ["atomic" P] In -> (bt.infer-wrap "transaction" In (bt.infer-h P In) false)
  ["once" K P] In -> (if (bt.safe-name? K) (bt.infer-wrap "deduplicate" In (bt.infer-h P In) true) (simple-error "invalid request key"))
  P In -> (if (and (bt.atom-valid? P) (bt.unique In))
    ["ok" (bt.atom-out P In) (bt.atom-effects P) ["primitive"]]
    (simple-error "unsupported program or duplicate resources")))
(define bt.infer-seq P Q In ["ok" Mid E1 A] ->
  (bt.finish-seq Mid E1 A (bt.infer-h Q Mid)))
(define bt.finish-seq Mid E1 A ["ok" Out E2 B] -> ["ok" Out (bt.union E1 E2) ["sequence" Mid E1 E2 A B]])
(define bt.infer-case C P Q In ["ok" Out E1 A] ["ok" Out E2 B] -> ["ok" Out (bt.union E1 E2) ["branches" E1 E2 A B]]
  _ _ _ _ _ _ -> (simple-error "branches leave different resources"))
(define bt.infer-wrap Tag In ["ok" Out E A] RequireInvariant ->
  (if (or (not RequireInvariant) (= In Out)) ["ok" Out E [Tag A]] (simple-error "resource invariant not preserved")))

\\ Semantic behavioral refinements. The proof method is part of the type.
\\ once executes its body atomically in this abstract machine, including receipt.
(datatype bt-retry-safe
  A : (bt-proof ("once" K P) In In E);
  __________________________________________
  ["by-durable-deduplication" A] : (bt-retry-safe ("once" K P) In E);)
(datatype bt-effects-within
  if (bt.subset E Allowed)
  A : (bt-proof P In Out E);
  __________________________________________
  ["by-effect-inclusion" E A] : (bt-effects-within P In Out Allowed);)

\\ Ground data proof terms are already elaborated by the bridge. Invoke System S
\\ directly: the general source typecheck entry curries arbitrary witness lists.
(define bt.check-ground Proof Type ->
  (prolog? (shen.system-S [(receive Proof) : (receive Type)] [])))

\\ A decidable semantic refinement: preservation of a sum of store fields on
\\ successful completion. Symbolic affine execution; unsupported arithmetic rejects.
(define bt.coeff K Terms -> (if (bt.has K Terms) (bt.lookup K Terms) 0))
(define bt.add-terms [] B -> B [[K V] | A] B -> (bt.add-terms A (bt.store K (bt.checked (+ V (bt.coeff K B))) B)))
(define bt.scale N [] -> [] N [[K V] | Xs] -> [[K (bt.checked (* N V))] | (bt.scale N Xs)])
(define bt.terms-equal A B -> (and (bt.terms-sub A B) (bt.terms-sub B A)))
(define bt.terms-sub [] _ -> true [[K V] | Xs] B -> (and (= V (bt.coeff K B)) (bt.terms-sub Xs B)))
(define bt.affine ["lit" N] _ -> (if (bt.integer? N) [["constant" N]] (simple-error "noninteger affine literal"))
  ["get" K] Env -> (if (bt.has K Env) (bt.lookup K Env) [[(cn "state:" K) 1]])
  ["input" K] _ -> [[(cn "input:" K) 1]]
  ["+" A B] Env -> (bt.add-terms (bt.affine A Env) (bt.affine B Env))
  ["-" A B] Env -> (bt.add-terms (bt.affine A Env) (bt.scale -1 (bt.affine B Env)))
  ["*" ["lit" N] A] Env -> (bt.scale (bt.num N) (bt.affine A Env))
  ["*" A ["lit" N]] Env -> (bt.scale (bt.num N) (bt.affine A Env))
  _ _ -> (simple-error "outside affine proof fragment"))
(define bt.affine-step ["put" K X] Env -> [(bt.store K (bt.affine X Env) Env)]
  ["seq" P Q] Env -> (bt.affine-many Q (bt.affine-step P Env))
  ["case" _ P Q] Env -> (append (bt.affine-step P Env) (bt.affine-step Q Env))
  ["atomic" P] Env -> (bt.affine-step P Env)
  ["once" _ P] Env -> [Env | (bt.affine-step P Env)]
  ["repeat" 0 _] Env -> [Env]
  ["repeat" N P] Env -> (bt.affine-many ["repeat" (- N 1) P] (bt.affine-step P Env))
  P Env -> [Env] where (bt.atom-valid? P)
  _ _ -> (simple-error "unsupported affine operation"))
(define bt.affine-many _ [] -> [] P [Env | Envs] -> (append (bt.affine-step P Env) (bt.affine-many P Envs)))
(define bt.sum-fields [] _ -> [] [K | Ks] Env -> (bt.add-terms (bt.affine ["get" K] Env) (bt.sum-fields Ks Env)))
(define bt.all-preserve _ _ [] -> true Ks Before [Env | Envs] -> (and (bt.terms-equal Before (bt.sum-fields Ks Env)) (bt.all-preserve Ks Before Envs)))
(define bt.preserves? P Ks -> (trap-error (and (not (= Ks [])) (and (bt.unique Ks) (bt.all-preserve Ks (bt.sum-fields Ks []) (bt.affine-step P [])))) (/. Ex false)))
(datatype bt-preserves
  if (bt.preserves? P Keys)
  A : (bt-proof P In Out E);
  __________________________________________
  ["by-affine-invariant" A] : (bt-preserves P In Out E Keys);)
