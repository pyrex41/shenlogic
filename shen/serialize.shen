
(define serialize-term
  X -> (if (cons? X)
           (serialize-list X)
           (str X)))

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
  [X | Rest] -> (cn (serialize-term X) (cn "\n" (serialize-lines Rest))))

(define serialize-canonical
  Terms -> (serialize-lines Terms))

(define serialize.canonical
  Value -> (serialize-term Value))

(define serialize-roundtrip
  Terms -> (serialize-canonical Terms))
