\\ List functions THORN 20 takes from the Shen S42 standard library
\\ (Lib/StLib/Lists/lists.shen and Symbols/symbols2.shen, BSD, Mark Tarver) that the kernel (41.2
\\ and S42 alike) does not define.  Wrapped in package thorn so the names resolve to
\\ the thorn.-prefixed references THORN20.shen compiles to.

(package thorn []

\\ From Lib/StLib/Symbols/symbols2.shen.
(define newv
  {--> symbol}
  -> (gensym (protect X)))

(define remove-duplicates
  {(list A) --> (list A)}
   [] -> []
   [X | Y] -> (remove-duplicates Y) where (element? X Y)
   [X | Y] -> [X | (remove-duplicates Y)])

(define subset?
  {(list A) --> (list A) --> boolean}
   [] _ -> true
   [X | Y] Z -> (subset? Y Z) where (element? X Z)
   _ _ -> false)

(define every?
  {(A --> boolean) --> (list A) --> boolean}
   _ [] -> true
   P [X | Y] -> (every? P Y)  where (P X)
   _ _ -> false)

(define sort
  {(A --> A --> boolean) --> (list A) --> (list A)}
    _ [] -> []
    _ [X] -> [X]
    R [X | Y] -> (let Less (mapcan (/. Z (if (R Z X) [Z] [])) Y)
                      More (mapcan (/. Z (if (not (R Z X)) [Z] [])) Y)
                      (append (sort R Less) [X] (sort R More))))

(define filter
  {(A --> boolean) --> (list A) --> (list A)}
   _ [] -> []
   F [X | Y] -> (if (F X) [X | (filter F Y)] (filter F Y)))

(define remove-if
  {(A --> boolean) --> (list A) --> (list A)}
   _ [] -> []
   F [X | Y] -> (if (F X) (remove-if F Y) [X | (remove-if F Y)]))

(define partition
   {(A --> A --> boolean) --> (list A) --> (list (list A))}
   _ [] -> []
   R [X | Y] -> (let EQ (mapcan (/. Z (if (R X Z) [Z] [])) [X | Y])
                     Remainder (difference [X | Y] EQ)
                     [EQ | (partition R Remainder)])
   _ _ -> (simple-error "partition requires a list"))

(define mapf
  {(A --> B) --> (list A) --> (B --> (list C) --> (list C)) --> (list C)}
   _ [] _ -> []
   F [X | Y] C -> (C (F X) (mapf F Y C)))

)
