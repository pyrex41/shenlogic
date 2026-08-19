\\ ShenLogic 0.2 control-flow corpus.
\\ Nested `if` and `let` expressions must evaluate only the selected path.

(define nested-if-let
  { number --> number }
  X -> (let Y (+ X 1)
         (if (< Y 0)
             (let Z (- 0 Y) (+ Z 10))
             (if (= Y 0) 99 (* Y 2)))))

\\ The recursive call is deliberately divergent.  Short-circuiting must
\\ skip it when the left operand determines the result.
(define diverge
  { number --> boolean }
  X -> (diverge X))

(define short-circuit-and
  { number --> boolean }
  X -> (and false (diverge X)))

(define short-circuit-or
  { number --> boolean }
  X -> (or true (diverge X)))

\\ Strict arguments are evaluated from left to right.  The first operand
\\ has a type error; evaluating the divergent second operand first would
\\ incorrectly report a timeout instead.
(define strict-left-error
  { number --> number }
  X -> (+ true X))

(define strict-right-diverge
  { number --> number }
  X -> (strict-right-diverge X))

(define strict-call-order
  { number --> number }
  X -> (+ (strict-left-error X) (strict-right-diverge X)))
