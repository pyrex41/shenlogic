\\ Canonical, deterministic S-expression serialization.
\\
\\ Shen strings are quoted (and escaped by code point), while symbols remain
\\ bare.  This is important for v2: a [v-string S] payload must not become
\\ indistinguishable from the symbol S.  Lists are written with parentheses;
\\ improper lists retain the dotted tail notation.

(define serialize.escape-char
  C -> (let N (string->n C)
         (if (= N 34)
             (cn (n->string 92) (n->string 34))
             (if (= N 92)
                 (cn (n->string 92) (n->string 92))
                 (if (= N 10)
                     (cn (n->string 92) "n")
                     (if (= N 13)
                         (cn (n->string 92) "r")
                         (if (= N 9)
                             (cn (n->string 92) "t") C)))))))

(define serialize.escape-chars
  [] -> ""
  [C | Cs] -> (cn (serialize.escape-char C)
                  (serialize.escape-chars Cs)))

(define serialize-string
  S -> (cn (n->string 34)
           (cn (serialize.escape-chars (explode S))
               (n->string 34))))

(define serialize-symbol
  X -> (str X))

(define serialize-term
  X -> (if (string? X)
           (serialize-string X)
           (if (cons? X)
               (serialize-list X)
               (serialize-symbol X))))

(define serialize-list
  [] -> "()"
  [X | Rest] -> (cn "(" (cn (serialize-term X)
                             (cn (serialize-list-tail Rest) ")"))))

(define serialize-list-tail
  [] -> ""
  [X | Rest] -> (cn " " (cn (serialize-term X)
                             (serialize-list-tail Rest))))

(define serialize-lines
  [] -> ""
  [X] -> (serialize-term X)
  [X | Rest] -> (cn (serialize-term X) (cn "~%" (serialize-lines Rest))))

(define serialize-canonical
  Terms -> (serialize-lines Terms))

(define serialize.canonical
  Value -> (serialize-term Value))

(define serialize-roundtrip
  Terms -> (serialize-canonical Terms))
