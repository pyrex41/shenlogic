(define istype?
  {term --> boolean}
  A -> true    where (element? A [type symbol boolean string nat t t1 t2 t3])
  [list A] -> (istype? A)
  [A --> B] -> (and (istype? A) (istype? B))
  _ -> false) 
  
(datatype kludge 
   
   [X : A] : prop; Hyps : (list prop);
   _________________________________________________
   (prolog? (shen.system-S [(shen.curry (receive X)) : (receive A)] (receive Hyps))) : boolean;
   
   [X : type] : prop; Hyps : (list prop);
   ________________________________________________________________________________
   (prolog? (shen.system-S [(shen.rcons_form (receive X)) : type] (receive Hyps))) : boolean;)  
  
(define call-system-S 
  {(list prop) --> prop --> boolean}
  Hyps [X : type] -> (prolog? (shen.system-S [(shen.rcons_form (receive X)) : type] (receive Hyps)))  
  Hyps [X : A] -> (prolog? (shen.system-S [(shen.curry (receive X)) : (receive A)] (receive Hyps))))   
  
(datatype prop
  
  P : prop; Q : prop;
  ====================== 
  [P <=> Q] : prop;
  
  P : prop; Q : prop;
  ====================== 
  [P & Q] : prop;
  
  P : prop; Q : prop;
  ====================== 
  [P v Q] : prop;
  
  P : prop; Q : prop;
  ====================== 
  [P => Q] : prop;
  
  P : prop;
  ============ 
  [~ P] : prop;
  
  T : term; A : type;
  ===================
  [T : A] : prop;
  
  !;
  A : variable; 
  A : type >> P : prop;
  _________________________________
  [all A : type P] : prop;
  
  !;
  A : variable; 
  A : type >> P : prop;
  _______________________
  [exists A : type P] : prop;
  
  !;
  X : variable, P : prop >> Q;
  _________________________________
  [all X : type P] : prop >> Q;
  
  X : variable; A : type; P : prop;
  =================================
  [exists X : A P] : prop;
  
  X : variable; A : type; P : prop;
  =================================
  [all X : A P] : prop;
  
  X : term; Y : term;
  ===================
  [X = Y] : prop;
  
  ______________
  falsum : prop;
  
  ______________
  verum : prop;
  
  if (atom? X)
  ____________
  X : term;
  
  [X | Y] : (list term);
  ======================
  [X | Y] : (- term);
  
  X : variable;
  _____________
  X : term;
     
  if (variable? X)
  _______________ 
  X : variable;
  
  __________________
  (newv) : variable;
  
  if (atomic-type? A)
  ____________________
  A : type;
  
  ________________________________________
  (istype? A) : verified >> A : type;
  
  A : type;
  =================
  [list A] : type;
  
  A : type; B : type;
  ===================
  [A --> B] : type;)
  
(define subst-free
  {term --> term --> prop --> prop}
  T X [P <=> Q] -> [(subst-free T X P) <=> (subst-free T X Q)]
  T X [P & Q]   -> [(subst-free T X P) & (subst-free T X Q)]
  T X [P v Q]   -> [(subst-free T X P) v (subst-free T X Q)]
  T X [P => Q]  -> [(subst-free T X P) => (subst-free T X Q)]
  T X [~ P]     -> [~ (subst-free T X P)]
  T X [all X : A P]    -> [all X : A P]
  T X [exists X : A P] -> [exists X : A P]
  T X [all Y : A P]    -> [all Y : (subst-type T X A) (subst-free T X P)]
  T X [exists Y : A P] -> [exists Y : (subst-type T X A) (subst-free T X P)]
  T X [Y = Z] -> [(subst-term T X Y) = (subst-term T X Z)]
  T X falsum -> falsum
  T X verum  -> verum) 
  
(define subst-type
  {term --> term --> type --> type}
   T X A -> (subst-type-h T X A)  where (istype? T)
   _ _ A -> A)
   
(define subst-type-h
  {type --> term --> type --> type}
   T X A -> T    where (== X A)
   T X [list A] -> [list (subst-type-h T X A)]
   T X [A --> B] -> [(subst-type-h T X A) --> (subst-type-h T X B)]
   _ _ A -> A)    

(define subst-term
  {term --> term --> term --> term}
  T X X -> T
  T X [Y | Z] -> [(subst-term T X Y) | (map (/. W (subst-term T X W)) Z)]
  T X Y -> Y)
  
(include [step])

(d-rule hyp ()
   
     _______
     P >> P;)
   
   (d-rule vr1 ()

     P;
     ________
     [P v Q];)
   
   (d-rule vr2 ()

     Q;
     ________
     [P v Q];)
   
   (d-rule vl ()

     Q >> P;
     R >> P;
     ______________
     [Q v R] >> P;)
   
   (d-rule &r ()
   
      P; Q;
      _____
      [P & Q];)
    
    (d-rule &l ()
    
      P, Q >> R;
      __________
      [P & Q] >> R;)
      
    (d-rule =>r ()
    
      P >> Q;
      _______
      [P => Q];)
      
     (d-rule =>l ()
     
       [P => Q] >> P;
       ______________
       [P => Q] >> Q;)
       
     (d-rule <=>r ()
     
       [[P => Q] & [Q => P]];
       ______________________
       [P <=> Q];)
       
     (d-rule <=>l ()
     
       [[P => Q] & [Q => P]] >> R;
       ______________________
       [P <=> Q] >> R;) 
    
     (d-rule ~r ()
     
       [P => falsum];
       ______________
       [~ P];)     
           
     (d-rule ~l ()
     
       [P => falsum] >> Q;
       ______________
       [~ P] >> Q;)                
   
     (d-rule lemma (Q : prop)
   
       Q;
       Q >> P;
       _______
       P;)

(d-rule lem (P : prop)

      [P v [~ P]] >> Q;
       ______________
       Q;)
       
(d-rule exp ()
      
   falsum;
   _______
   P;)
   
(d-rule obvious ()

   _______
   verum;)          
     
(d-rule thin (N : number)
     
 let Hypotheses (let P (nth N Hypotheses) (remove P Hypotheses))
  P;
 ________
  P;)
            
 (d-rule promote (N : number)
      
   let Q (nth N Hypotheses)
   let Hypotheses [Q | (remove Q Hypotheses)]
   P;
   ____________
   P;)
   
 (d-rule alll (T : term)

   [T : A];
   (subst-free T X P), [all X : A P] >> Q;
   _______________________________________
   [all X : A P] >> Q;)
   
 (d-rule allr (T : term)

   if (symbol? T)
   if (= (occurrences T [all X : A P]) 0)
   if (= (occurrences T Hypotheses) 0)
   if (= (occurrences T Sequents) 0)
   
   [T : A] >> (subst-free T X P);
   __________________
   [all X : A P];)
   
(d-rule existsl (T : term)

   if (= (occurrences T [exists X : A P]) 0)
   if (= (occurrences T Hypotheses) 0)
   if (= (occurrences T Sequents) 0)
   
   [T : A], (subst-free T X P) >> Q;
   __________________
   [exists X : A P] >> Q;)
   
(d-rule existsr (T : term)

   [T : A];
   (subst-free T X P);
   __________________
   [exists X : A P];)   
   
(d-rule =r ()

  ________
  [X = X];)
  
(d-rule =l ()

  [X = Y] >> (subst-free Y X P);
  ______________________________
  [X = Y] >> P;)
  
(d-rule intro (S : symbol)

  let Hypotheses (append (axioms S) Hypotheses)
  P;
  _____
  P;)    
  
(d-rule system-S ()

  if (call-system-S Hypotheses [X : A])
  ________
  [X : A];)  
  
(d-rule mathl-ind ()

  (subst-free 0 X P);
  [all X : nat [P => (subst-free [succ X] X P)]];
  __________________________________________________  
  [all X : nat P];) 
  
(d-rule list-ind ()

  let Y (type (newv) variable)
  let Z (type (newv) variable)
  (subst-free [] X P);
  [all Y : A
    [all Z : [list A]
      [(subst-free Z X P) => (subst-free [cons Y Z] X P)]]];
  __________________________________________
  [all X : [list A] P];) 
  
(d-rule nil ()

  ____________________________________________________________________ 
  [all A : type [all X : A [all Y : [list A] [~ [[cons X Y] = []]]]]];) 
  
(d-rule list-identity ()

_______________________________________________________________________
[all A : type [all X : A [all Y : [list A] [all W : A [all Z : [list A] 
              [[[cons X Y] = [cons W Z]] => [[X = W] & [Y = Z]]]]]]]];)
              
(d-rule list-acyclic ()
    
____________________________________________________________________
[all A : type [all X : A [all Y : [list A] [~ [[cons X Y] = Y]]]]];)            
      