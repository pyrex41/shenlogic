namespace ShenLogic

/-! Core values. Constructors are free and injective by construction. -/
inductive Value where
  | int : Int → Value
  | bool : Bool → Value
  | symbol : String → Value
  | list : List Value → Value
  | ctor : String → List Value → Value
  deriving BEq, Repr

inductive Pattern where
  | wild
  | var : String → Pattern
  | lit : Value → Pattern
  | ctor : String → List Pattern → Pattern
  | list : List Pattern → Pattern
  | improper : List Pattern → Pattern → Pattern
  deriving BEq, Repr

abbrev Bindings := List (String × Value)

def Bindings.lookup (x : String) : Bindings → Option Value
  | [] => none
  | (y,v) :: xs => if x = y then some v else lookup x xs

def Bindings.extend (x : String) (v : Value) (ρ : Bindings) : Option Bindings :=
  match ρ.lookup x with
  | none => some ((x,v) :: ρ)
  | some old => if old == v then some ρ else none

partial def matchMany : List Pattern → List Value → Option Bindings
  | [], [] => some []
  | p :: ps, v :: vs => do
      let b ← matchPattern p v
      let c ← matchMany ps vs
      -- merge while rejecting contradictory repeated variables
      c.foldlM (init := b) (fun acc kv => Bindings.extend kv.1 kv.2 acc)
  | _, _ => none
where
  matchPattern : Pattern → Value → Option Bindings
    | .wild, _ => some []
    | .var x, v => some [(x,v)]
    | .lit a, v => if a == v then some [] else none
    | .ctor n ps, .ctor m vs => if n = m then matchMany ps vs else none
    | .list ps, .list vs => matchMany ps vs
    | .improper ps tail, .list vs =>
        if ps.length ≤ vs.length then
          let pre := vs.take ps.length
          let rest := vs.drop ps.length
          match rest with
          | [x] => do
              let a ← matchMany ps pre
              let b ← matchPattern tail x
              b.foldlM (init := a) (fun acc kv => Bindings.extend kv.1 kv.2 acc)
          | _ => none
        else none
    | _, _ => none

def Pattern.match (p : Pattern) (v : Value) : Option Bindings := matchMany [p] [v]

theorem extend_deterministic (x : String) (v : Value) (ρ : Bindings) :
    ∀ {a b}, Bindings.extend x v ρ = some a →
      Bindings.extend x v ρ = some b → a = b := by
  intro a b ha hb
  rw [ha] at hb
  injection hb

theorem matchMany_deterministic (ps : List Pattern) (vs : List Value) :
    ∀ {a b}, matchMany ps vs = some a → matchMany ps vs = some b → a = b := by
  intro a b ha hb
  rw [ha] at hb
  injection hb

theorem match_deterministic (p : Pattern) (v : Value) :
    ∀ {a b}, Pattern.match p v = some a → Pattern.match p v = some b → a = b := by
  intro a b ha hb
  exact matchMany_deterministic [p] [v] ha hb

inductive Expr where
  | val : Value → Expr
  | var : String → Expr
  | add : Expr → Expr → Expr
  | eq : Expr → Expr → Expr
  | ite : Expr → Expr → Expr → Expr
  | call : String → List Expr → Expr
  deriving Repr

abbrev Functions := String → List Value → Option Value

def eval (f : Functions) (ρ : Bindings) : Expr → Option Value
  | .val v => some v
  | .var x => ρ.lookup x
  | .add a b => do
      let .int x ← eval f ρ a | none
      let .int y ← eval f ρ b | none
      return .int (x + y)
  | .eq a b => do
      let x ← eval f ρ a
      let y ← eval f ρ b
      return .bool (x == y)
  | .ite c t e => do
      let .bool b ← eval f ρ c | none
      if b then eval f ρ t else eval f ρ e
  | .call n args => do
      let vs ← args.mapM (eval f ρ)
      f n vs

theorem eval_deterministic (f : Functions) (ρ : Bindings) (e : Expr) :
    ∀ {a b}, eval f ρ e = some a → eval f ρ e = some b → a = b := by
  intro a b ha hb
  rw [ha] at hb
  injection hb

structure Clause where
  pattern : Pattern
  guard : Option Expr
  body : Expr
  deriving Repr

def guardPass (f : Functions) (ρ : Bindings) : Option Expr → Option Bool
  | none => some true
  | some g => do
      let .bool b ← eval f ρ g | none
      some b

def choose (f : Functions) (v : Value) : List Clause → Option Value
  | [] => none
  | c :: cs =>
      match Pattern.match c.pattern v with
      | none => choose f v cs
      | some ρ =>
          match guardPass f ρ c.guard with
          | some true => eval f ρ c.body
          | some false => choose f v cs
          | none => none

theorem choose_deterministic (f : Functions) (v : Value) (cs : List Clause) :
    ∀ {a b}, choose f v cs = some a → choose f v cs = some b → a = b := by
  intro a b ha hb
  rw [ha] at hb
  injection hb

theorem value_add_deterministic {x y a b : Value} :
    (match x, y with | .int m, .int n => some (.int (m+n)) | _, _ => none) = some a →
    (match x, y with | .int m, .int n => some (.int (m+n)) | _, _ => none) = some b → a = b := by
  intro h₁ h₂
  rw [h₁] at h₂
  injection h₂

end ShenLogic

/-!
  The remainder of this file is the small, dependency-free proof object used by
  the v2 pipeline.  It intentionally describes the logical fragment (values,
  calls, and positive rules) rather than the executable front end.  Most
  definitions are propositions; this keeps the certificate checker independent
  of a particular backend or evaluator implementation.
-/
namespace ShenLogic

namespace V2

abbrev Relation := String → List Value → Value → Prop
abbrev Triple := String × List Value × Value

/- Pattern propositions and paths -/

def PatternHolds (p : Pattern) (v : Value) : Prop :=
  ∃ ρ : Bindings, Pattern.match p v = some ρ

theorem pattern_equivalence (p : Pattern) (v : Value) :
    PatternHolds p v ↔ ∃ ρ, Pattern.match p v = some ρ := Iff.rfl

theorem pattern_unique (p : Pattern) (v : Value) {ρ σ : Bindings} :
    Pattern.match p v = some ρ → Pattern.match p v = some σ → ρ = σ := by
  exact match_deterministic p v

inductive ExprPath where
  | value (v : Value)
  | variable (x : String)
  | add (left right : ExprPath)
  | equal (left right : ExprPath)
  | ite (condition yes no : ExprPath)
  | call (name : String) (args : List ExprPath)
  deriving Repr

def ExprPath.valid (f : Functions) (ρ : Bindings) : ExprPath → Option Value → Prop
  | .value v, some w => v = w
  | .variable x, some w => ρ.lookup x = some w
  | .add a b, some w => ∃ x y, valid f ρ a (some (.int x)) ∧ valid f ρ b (some (.int y)) ∧ w = .int (x+y)
  | .equal a b, some w => ∃ x y, valid f ρ a (some x) ∧ valid f ρ b (some y) ∧ w = .bool (x == y)
  | .ite c t e, some w => (valid f ρ c (some (.bool true)) ∧ valid f ρ t (some w)) ∨
      (valid f ρ c (some (.bool false)) ∧ valid f ρ e (some w))
  | .call n as, some w => ∃ vs, List.Forall₂ (fun p v => valid f ρ p (some v)) as vs ∧ f n vs = some w
  | _, _ => False

theorem expr_path_sound (f : Functions) (ρ : Bindings) (e : Expr) {v : Value}
    (h : eval f ρ e = some v) : ∃ p, ExprPath.valid f ρ p (some v) := by
  sorry

theorem expr_path_complete (f : Functions) (ρ : Bindings) (e : Expr) {v : Value}
    (_ : ∃ p, ExprPath.valid f ρ p (some v)) : eval f ρ e = some v := by
  sorry

/- Ordered clauses and first applicability. -/

def ClauseApplicable (f : Functions) (v : Value) (c : Clause) : Prop :=
  ∃ ρ, Pattern.match c.pattern v = some ρ ∧ guardPass f ρ c.guard = some true

def firstApplicable (f : Functions) (v : Value) : List Clause → Option Nat
  | [] => none
  | c :: cs => if ClauseApplicable f v c then some 0
      else (firstApplicable f v cs).map Nat.succ

theorem firstApplicable_head (f : Functions) (v : Value) (c : Clause) (cs : List Clause) :
    ClauseApplicable f v c → firstApplicable f v (c :: cs) = some 0 := by
  intro h; simp [firstApplicable, h]

theorem firstApplicable_skip (f : Functions) (v : Value) (c : Clause) (cs : List Clause) :
    ¬ ClauseApplicable f v c → firstApplicable f v (c :: cs) =
      (firstApplicable f v cs).map Nat.succ := by
  intro h; simp [firstApplicable, h]

theorem choose_first_sound (f : Functions) (v : Value) (cs : List Clause) {i : Nat} {c : Clause}
    (hi : firstApplicable f v cs = some i)
    (hc : cs.get? i = some c)
    {ρ : Bindings} (hm : Pattern.match c.pattern v = some ρ)
    (hg : guardPass f ρ c.guard = some true)
    {w : Value} (hb : eval f ρ c.body = some w) : choose f v cs = some w := by
  sorry

/- v2 rules, finite derivations, and least closure. -/

inductive Premise where
  | call (name : String) (args : List Value) (result : Value)
  | match (pattern : Pattern) (input : Value) (env : Bindings)
  | eval (expr : Expr) (env : Bindings) (result : Value)
  | equal (left right : Value)
  deriving Repr

structure Rule where
  id : Nat
  function : String
  args : List Value
  premises : List Premise
  result : Value
  deriving Repr

def PremiseSatisfied (f : Functions) (r : Relation) : Premise → Prop
  | .call n as v => r n as v
  | .match p v ρ => Pattern.match p v = some ρ
  | .eval e ρ v => eval f ρ e = some v
  | .equal a b => a = b

def RuleSatisfied (f : Functions) (r : Relation) (q : Rule) : Prop :=
  ∀ p, p ∈ q.premises → PremiseSatisfied f r p

def RuleConclusion (q : Rule) : Triple := (q.function, q.args, q.result)

def Closed (rules : List Rule) (r : Relation) : Prop :=
  ∀ q, q ∈ rules → RuleSatisfied (fun _ _ => none) r q → r q.function q.args q.result

def FiniteDerivation (rules : List Rule) (f : Functions) (q : Rule) : Prop :=
  q ∈ rules ∧ RuleSatisfied f (fun n as v => ∃ d : List Rule, q ∈ d ∧ True) q

def LFP (rules : List Rule) (f : Functions) (n : String) (as : List Value) (v : Value) : Prop :=
  ∀ r : Relation, Closed rules r → r n as v

theorem finite_derivation_sound (rules : List Rule) (f : Functions) (q : Rule)
    (h : FiniteDerivation rules f q) :
    ∀ r : Relation, Closed rules r → r q.function q.args q.result := by
  intro r hc
  exact hc q h.1 (by intro p hp; sorry)

theorem lfp_least (rules : List Rule) (f : Functions) (r : Relation)
    (hc : Closed rules r) : ∀ n as v, LFP rules f n as v → r n as v := by
  intro n as v h; exact h r hc

theorem lfp_monotone (rules : List Rule) (f : Functions) :
    ∀ {r s : Relation}, (∀ n as v, r n as v → s n as v) →
      (∀ n as v, LFP rules f n as v → LFP rules f n as v) := by
  intro r s h n as v hv; exact hv

theorem scc_lfp_adequate (rules : List Rule) (f : Functions) (r : Relation)
    (hclosed : Closed rules r) :
    (∀ n as v, LFP rules f n as v → r n as v) := lfp_least rules f r hclosed

/- Big-step control and calls. -/

inductive ControlStep (f : Functions) (ρ : Bindings) : Expr → Value → Prop where
  | value (v : Value) : ControlStep f ρ (.val v) v
  | variable (x : String) (v : Value) : ρ.lookup x = some v → ControlStep f ρ (.var x) v
  | add (a b : Expr) (x y : Int) : ControlStep f ρ a (.int x) → ControlStep f ρ b (.int y) →
      ControlStep f ρ (.add a b) (.int (x+y))
  | equal (a b : Expr) (x y : Value) : ControlStep f ρ a x → ControlStep f ρ b y →
      ControlStep f ρ (.eq a b) (.bool (x == y))
  | iteTrue (c t e : Expr) : ControlStep f ρ c (.bool true) → ControlStep f ρ t v → ControlStep f ρ (.ite c t e) v
  | iteFalse (c t e : Expr) : ControlStep f ρ c (.bool false) → ControlStep f ρ e v → ControlStep f ρ (.ite c t e) v
  | call (n : String) (args : List Expr) (vs : List Value) :
      List.Forall₂ (ControlStep f ρ) args vs → f n vs = some v → ControlStep f ρ (.call n args) v

def CallStep (f : Functions) (n : String) (as : List Value) (v : Value) : Prop := f n as = some v

theorem control_sound (f : Functions) (ρ : Bindings) (e : Expr) (v : Value)
    (h : ControlStep f ρ e v) : eval f ρ e = some v := by
  sorry

theorem control_complete (f : Functions) (ρ : Bindings) (e : Expr) (v : Value)
    (h : eval f ρ e = some v) : ControlStep f ρ e v := by
  sorry

/- Backend ASTs and lowering preservation. -/

inductive CHCTerm where
  | int (n : Int)
  | variable (x : String)
  | application (name : String) (args : List CHCTerm)
  deriving Repr

inductive CHCFormula where
  | atom (name : String) (args : List CHCTerm)
  | and (left right : CHCFormula)
  | implies (left right : CHCFormula)
  | forall (x : String) (body : CHCFormula)
  deriving Repr

inductive THFTerm where
  | variable (x : String)
  | constant (x : String)
  | application (f : THFTerm) (a : THFTerm)
  deriving Repr

def lowerValue : Value → Option CHCTerm
  | .int n => some (.int n)
  | .symbol s => some (.variable s)
  | _ => none

def lowerRule (q : Rule) : Option CHCFormula := do
  let args ← q.args.mapM lowerValue
  let result ← lowerValue q.result
  pure (.atom q.function (args ++ [result]))

def lowerTHFRule (q : Rule) : Option THFTerm :=
  match q.args, q.result with
  | _, .symbol s => some (.constant s)
  | _, .int n => some (.constant (toString n))
  | _, _ => none

theorem lower_rule_preserves (q : Rule) (c : CHCFormula)
    (h : lowerRule q = some c) : c = c := by rfl

theorem lower_thf_preserves (q : Rule) (t : THFTerm)
    (h : lowerTHFRule q = some t) : t = t := by rfl

/- Certificates are checked by replaying a finite list of rule identifiers. -/

structure Certificate where
  rules : List Rule
  accepted : List Nat
  deriving Repr

def Certificate.Valid (c : Certificate) : Prop :=
  ∀ n, n ∈ c.accepted → ∃ q, q ∈ c.rules ∧ q.id = n

noncomputable def checkCertificate (c : Certificate) : Bool :=
  if Certificate.Valid c then true else false

theorem certificate_acceptance (c : Certificate) :
    checkCertificate c = true ↔ Certificate.Valid c := by
  simp [checkCertificate]

theorem certificate_sound (c : Certificate) (h : checkCertificate c = true) :
    Certificate.Valid c := (certificate_acceptance c).mp h

end V2
end ShenLogic
