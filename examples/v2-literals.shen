\\ Symbols and strings are distinct literal values.

(define literal-kind
  { A --> symbol }
  foo -> symbol-foo
  "foo" -> string-foo
  _ -> other)

(define literal-string-probe
  { --> symbol }
  -> (literal-kind "foo"))
