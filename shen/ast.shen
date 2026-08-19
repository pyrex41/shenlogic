\\ A small data-only AST. Payloads remain raw Shen values.
(define shenlogic.ast.make-program Definitions -> [program Definitions])
(define shenlogic.ast.program-definitions [program Definitions] -> Definitions)

(define shenlogic.ast.make-definition Name Signature Clauses Arity -> [definition Name Signature Clauses Arity])
(define shenlogic.ast.definition-name [definition Name _ _ _] -> Name)
(define shenlogic.ast.definition-signature [definition _ Signature _ _] -> Signature)
(define shenlogic.ast.definition-clauses [definition _ _ Clauses _] -> Clauses)
(define shenlogic.ast.definition-arity [definition _ _ _ Arity] -> Arity)

(define shenlogic.ast.make-signature Args Result -> [signature Args Result])
(define shenlogic.ast.make-no-signature -> none)
(define shenlogic.ast.signature-args [signature Args _] -> Args)
(define shenlogic.ast.signature-result [signature _ Result] -> Result)

(define shenlogic.ast.make-clause Index Patterns Guard Body -> [clause Index Patterns Guard Body])
(define shenlogic.ast.clause-index [clause I _ _ _] -> I)
(define shenlogic.ast.clause-patterns [clause _ P _ _] -> P)
(define shenlogic.ast.clause-guard [clause _ _ G _] -> G)
(define shenlogic.ast.clause-body [clause _ _ _ B] -> B)

(define shenlogic.ast.make-some-guard G -> [some G])
