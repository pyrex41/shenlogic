\\ THORN smoke: the vendored prover loads on this host, its typed prop
\\ grammar loads, and it proves a ground append fact and Schubert's
\\ Steamroller.  Exit status is nonzero on any failure.
(tc -)
(load "third_party/thorn/prelude.shen")
(load "third_party/thorn/THORN20.shen")
(load "third_party/thorn/datatypes.shen")

(set thorn-failures 0)

(define thorn-check
  Name Got Want -> (if (= Got Want)
                       (output "ok   ~A~%" Name)
                       (do (set thorn-failures (+ 1 (value thorn-failures)))
                           (output "FAIL ~A: got ~S want ~S~%" Name Got Want))))

(thorn.defaults)
(thorn.depth 6)
(kb-> [[all w [[append [] w] = w]]
       [all w [all x [all y [[append [cons w x] y] = [cons w [append x y]]]]]]])
(thorn-check "append-ground"
             (<-kb [[append [cons a [cons b []]] []] = [cons a [cons b []]]]) true)
(thorn-check "append-false-unproved"
             (<-kb [[append [cons a []] []] = [cons b []]]) false)

\\ Schubert's Steamroller, axioms as in third_party/thorn/problems/schubert.shen.
\\ shen-go needs roughly 5 million inferences, about 15 seconds here.
(thorn.defaults)
(thorn.timeout 120)
(kb-> [ [all x [[wolf x] => [animal x]]]
        [all x [[fox x] => [animal x]]]
        [all x [[bird x] => [animal x]]]
        [all x [[caterpillar x] => [animal x]]]
        [all x [[snail x] => [animal x]]]
        [all x [[grain x] => [plant x]]]
        
        [exists x [wolf x]]
        [exists x [fox x]]
        [exists x [bird x]]
        [exists x [caterpillar x]]
        [exists x [snail x]]
        [exists x [grain x]]
        
        [all x [[animal x] => [[all y [[plant y] => [eats x y]]]
                    v 
                    [all z [[[[animal z] &
                             [smaller z x]] &
                             [exists u [[plant u] & [eats z u]]]]
                             => 
                             [eats x z]]]]]]

        [all x [all y [[[caterpillar x] & [bird y]] => [smaller x y]]]]
        [all x [all y [[[snail x] & [bird y]]  =>  [smaller x y]]]]
        [all x [all y [[[bird x] & [fox y]]  =>  [smaller x y]]]]
        [all x [all y [[[fox x] & [wolf y]]  =>  [smaller x y]]]]
        [all x [all y [[[bird x] & [caterpillar y]]  =>  [eats x y]]]]
        
        [all x [[caterpillar x]  
                 =>  [exists y [[plant y] & [eats x y]]]]]
        [all x [[snail x]        
                 =>  [exists y [[plant y] & [eats x y]]]]]

        [all x [all y [[[wolf x] & [fox y]]  =>  [~ [eats x y]]]]]
        [all x [all y [[[wolf x] & [grain y]]  =>  [~ [eats x y]]]]]
        [all x [all y [[[bird x] & [snail y]]  =>  [~ [eats x y]]]]] ])
(thorn-check "steamroller"
             (<-kb [exists x [exists y [[[animal x] &
                               [animal y]] &
                                 [[eats x y] &
                              [all z [[grain z] => [eats y z]]]]]]])
             true)

(if (= (value thorn-failures) 0)
    (output "thorn smoke: all checks passed~%")
    (do (output "thorn smoke: ~A failure(s)~%" (value thorn-failures))
        (error "THORN smoke failure")))
