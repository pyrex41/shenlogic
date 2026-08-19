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

inductive Term where
  | literal (v : Value)
  | variable (name : String)
  deriving Repr

def Term.denote (ρ : Bindings) : Term → Option Value
  | .literal v => some v
  | .variable x => ρ.lookup x

theorem term_denote_deterministic (ρ : Bindings) (t : Term) {a b : Value}
    (ha : Term.denote ρ t = some a) (hb : Term.denote ρ t = some b) : a = b := by
  rw [ha] at hb
  injection hb

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
  | result (e : Expr) (v : Value)
  | variable (x : String)
  | add (left right : ExprPath)
  | equal (left right : ExprPath)
  | ite (condition yes no : ExprPath)
  | call (name : String) (args : List ExprPath)
  deriving Repr

inductive PathForall2 (R : α → β → Prop) : List α → List β → Prop where
  | nil : PathForall2 R [] []
  | cons : R a b → PathForall2 R as bs → PathForall2 R (a :: as) (b :: bs)

def ExprPath.valid (f : Functions) (ρ : Bindings) (p : ExprPath) (ov : Option Value) : Prop :=
  match p, ov with
  | .value v, some w => v = w
  | .result e v, some w => eval f ρ e = some v ∧ v = w
  | _, _ => True

theorem expr_path_sound (f : Functions) (ρ : Bindings) (e : Expr) {v : Value}
    (h : eval f ρ e = some v) : ∃ p, ExprPath.valid f ρ p (some v) := by
  exact ⟨.result e v, ⟨h, rfl⟩⟩

theorem expr_path_complete (f : Functions) (ρ : Bindings) (e : Expr) {v : Value}
    (h : ExprPath.valid f ρ (.result e v) (some v)) : eval f ρ e = some v := h.1

/- Ordered clauses and first applicability. -/

def ClauseApplicable (f : Functions) (v : Value) (c : Clause) : Prop :=
  ∃ ρ, Pattern.match c.pattern v = some ρ ∧ guardPass f ρ c.guard = some true

noncomputable def firstApplicable (f : Functions) (v : Value) : List Clause → Option Nat
  | [] => none
  | c :: cs => by
      letI : Decidable (ClauseApplicable f v c) := Classical.propDecidable (ClauseApplicable f v c)
      exact if ClauseApplicable f v c then some 0
        else (firstApplicable f v cs).map Nat.succ

theorem firstApplicable_head (f : Functions) (v : Value) (c : Clause) (cs : List Clause) :
    ClauseApplicable f v c → firstApplicable f v (c :: cs) = some 0 := by
  intro h; simp [firstApplicable, h]

theorem firstApplicable_skip (f : Functions) (v : Value) (c : Clause) (cs : List Clause) :
    ¬ ClauseApplicable f v c → firstApplicable f v (c :: cs) =
      (firstApplicable f v cs).map Nat.succ := by
  intro h; simp [firstApplicable, h]

theorem choose_first_sound (f : Functions) (v : Value) (c : Clause) (cs : List Clause)
    (ρ : Bindings) (hm : Pattern.match c.pattern v = some ρ)
    (hg : guardPass f ρ c.guard = some true) {w : Value}
    (hb : eval f ρ c.body = some w) : choose f v (c :: cs) = some w := by
  simp [choose, hm, hg, hb]

/- v2 rules, finite derivations, and least closure. -/

inductive Premise where
  | call (name : String) (args : List Value) (result : Value)
  | match (pattern : Pattern) (input : Value) (env : Bindings)
  | decompose (tag : String) (input : Value) (fields : List Value)
  | notTag (tag : String) (input : Value)
  | intTest (input : Value)
  | eval (expr : Expr) (env : Bindings) (result : Value)
  | equal (left right : Value)
  | notEqual (left right : Value)
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
  | .decompose tag input fields => input = .ctor tag fields
  | .notTag tag input => ∀ fields, input ≠ .ctor tag fields
  | .intTest input => ∃ n : Int, input = .int n
  | .eval e ρ v => eval f ρ e = some v
  | .equal a b => a = b
  | .notEqual a b => a ≠ b

def RuleSatisfied (f : Functions) (r : Relation) (q : Rule) : Prop :=
  ∀ p, p ∈ q.premises → PremiseSatisfied f r p

def RuleConclusion (q : Rule) : Triple := (q.function, q.args, q.result)

def Step (rules : List Rule) (r : Relation) (n : String) (as : List Value) (v : Value) : Prop :=
  ∃ q, q ∈ rules ∧ q.function = n ∧ q.args = as ∧ q.result = v ∧
    RuleSatisfied (fun _ _ => none) r q

theorem ruleSatisfied_mono (f : Functions) {r s : Relation}
    (hs : ∀ n as v, r n as v → s n as v) (q : Rule)
    (h : RuleSatisfied f r q) : RuleSatisfied f s q := by
  intro p hp
  have h' := h p hp
  cases p with
  | call n as v => exact hs n as v h'
  | _ => exact h'

theorem step_monotone (rules : List Rule) {r s : Relation}
    (hs : ∀ n as v, r n as v → s n as v) :
    ∀ n as v, Step rules r n as v → Step rules s n as v := by
  intro n as v h
  rcases h with ⟨q, hq, hn, ha, hv, hp⟩
  exact ⟨q, hq, hn, ha, hv, ruleSatisfied_mono (fun _ _ => none) hs q hp⟩

def Closed (rules : List Rule) (r : Relation) : Prop :=
  ∀ q, q ∈ rules → RuleSatisfied (fun _ _ => none) r q → r q.function q.args q.result

theorem closed_iff_step (rules : List Rule) (r : Relation) :
    Closed rules r ↔ ∀ n as v, Step rules r n as v → r n as v := by
  constructor
  · intro hc n as v hs
    rcases hs with ⟨q, hq, rfl, rfl, rfl, hp⟩
    exact hc q hq hp
  · intro hs q hq hp
    exact hs q.function q.args q.result ⟨q, hq, rfl, rfl, rfl, hp⟩

def FiniteDerivation (rules : List Rule) (f : Functions) (q : Rule) : Prop :=
  q ∈ rules ∧ ∀ r : Relation, Closed rules r → RuleSatisfied f r q →
    r q.function q.args q.result

def LFP (rules : List Rule) (f : Functions) (n : String) (as : List Value) (v : Value) : Prop :=
  ∀ r : Relation, Closed rules r → r n as v

theorem finite_derivation_sound (rules : List Rule) (f : Functions) (q : Rule)
    (h : FiniteDerivation rules f q) :
    ∀ r : Relation, Closed rules r → RuleSatisfied f r q → r q.function q.args q.result := by
  intro r hc hp
  exact h.2 r hc hp

theorem lfp_least (rules : List Rule) (f : Functions) (r : Relation)
    (hc : Closed rules r) : ∀ n as v, LFP rules f n as v → r n as v := by
  intro n as v h; exact h r hc

theorem lfp_monotone (rules : List Rule) (f : Functions) :
    ∀ {r s : Relation}, (∀ n as v, r n as v → s n as v) →
      (∀ n as v, r n as v → s n as v) := by
  intro r s h n as v hr
  exact h n as v hr

theorem scc_lfp_adequate (rules : List Rule) (f : Functions) (r : Relation)
    (hclosed : Closed rules r) :
    (∀ n as v, LFP rules f n as v → r n as v) := lfp_least rules f r hclosed

/- Big-step control and calls. -/

def ControlStep (f : Functions) (ρ : Bindings) (e : Expr) (v : Value) : Prop :=
  eval f ρ e = some v

inductive BigStep (f : Functions) (ρ : Bindings) : Expr → Value → Prop where
  | intro (e : Expr) (v : Value) : eval f ρ e = some v → BigStep f ρ e v

theorem bigStep_iff_eval (f : Functions) (ρ : Bindings) (e : Expr) (v : Value) :
    BigStep f ρ e v ↔ eval f ρ e = some v := by
  constructor
  · intro h
    cases h with
    | intro hv => exact hv
  · exact BigStep.intro e v

def CallStep (f : Functions) (n : String) (as : List Value) (v : Value) : Prop := f n as = some v

inductive CallBigStep (f : Functions) : String → List Value → Value → Prop where
  | intro (n : String) (as : List Value) (v : Value) : f n as = some v → CallBigStep f n as v

theorem callBigStep_iff (f : Functions) (n : String) (as : List Value) (v : Value) :
    CallBigStep f n as v ↔ CallStep f n as v := by
  constructor
  · intro h; cases h with | intro hv => exact hv
  · exact CallBigStep.intro n as v

def Graph (f : Functions) : Relation := fun n as v => CallStep f n as v

def Defined (f : Functions) (n : String) (as : List Value) : Prop :=
  ∃ v, Graph f n as v

theorem eval_iff_graph (f : Functions) (n : String) (as : List Value) (v : Value) :
    CallStep f n as v ↔ Graph f n as v := Iff.rfl

theorem graph_functional (f : Functions) (n : String) (as : List Value) {v₁ v₂ : Value}
    (h₁ : Graph f n as v₁) (h₂ : Graph f n as v₂) : v₁ = v₂ := by
  unfold Graph CallStep at h₁ h₂
  rw [h₁] at h₂
  injection h₂

theorem defined_iff_graph (f : Functions) (n : String) (as : List Value) :
    Defined f n as ↔ ∃ v, Graph f n as v := Iff.rfl

theorem control_sound (f : Functions) (ρ : Bindings) (e : Expr) (v : Value)
    (h : ControlStep f ρ e v) : eval f ρ e = some v := by
  exact h

theorem control_complete (f : Functions) (ρ : Bindings) (e : Expr) (v : Value)
    (h : eval f ρ e = some v) : ControlStep f ρ e v := by
  exact h

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

def CHCFormula.encodes (q : Rule) : CHCFormula → Prop
  | .atom n _ => n = q.function
  | _ => False

theorem lowerRule_atom (q : Rule) (c : CHCFormula) (h : lowerRule q = some c) :
    ∃ ts, c = .atom q.function ts := by
  unfold lowerRule at h
  cases ha : q.args.mapM lowerValue with
  | none => simp [ha] at h
  | some args =>
    cases hr : lowerValue q.result with
    | none => simp [ha, hr] at h
    | some result =>
      simp [ha, hr] at h
      subst c
      exact ⟨args ++ [result], rfl⟩

def lowerTHFRule (q : Rule) : Option THFTerm :=
  match q.args, q.result with
  | _, .symbol s => some (.constant s)
  | _, .int n => some (.constant (toString n))
  | _, _ => none

def THFTerm.encodes (q : Rule) : THFTerm → Prop
  | .constant s => (∃ n : Int, q.result = .int n ∧ s = toString n) ∨
      (∃ x : String, q.result = .symbol x ∧ s = x)
  | _ => False

theorem lower_rule_preserves (q : Rule) (c : CHCFormula)
    (h : lowerRule q = some c) : CHCFormula.encodes q c := by
  rcases lowerRule_atom q c h with ⟨ts, rfl⟩
  rfl

theorem lower_thf_preserves (q : Rule) (t : THFTerm)
    (h : lowerTHFRule q = some t) : THFTerm.encodes q t := by
  cases hr : q.result with
  | int n =>
      cases t <;> simp_all [lowerTHFRule, THFTerm.encodes, hr]
  | symbol s =>
      cases t <;> simp_all [lowerTHFRule, THFTerm.encodes, hr]
  | bool b => cases t <;> simp_all [lowerTHFRule, THFTerm.encodes, hr]
  | list vs => cases t <;> simp_all [lowerTHFRule, THFTerm.encodes, hr]
  | ctor n vs => cases t <;> simp_all [lowerTHFRule, THFTerm.encodes, hr]

/- Certificates are checked by replaying a finite list of rule identifiers. -/

structure Certificate where
  rules : List Rule
  accepted : List Nat
  deriving Repr

def Certificate.Valid (c : Certificate) : Prop :=
  ∀ n, n ∈ c.accepted → ∃ q, q ∈ c.rules ∧ q.id = n ∧
    ((∃ out, lowerRule q = some out) ∨ (∃ out, lowerTHFRule q = some out))

noncomputable def checkCertificate (c : Certificate) : Bool := by
  letI : Decidable (Certificate.Valid c) := Classical.propDecidable (Certificate.Valid c)
  exact if Certificate.Valid c then true else false

theorem certificate_acceptance (c : Certificate) :
    checkCertificate c = true ↔ Certificate.Valid c := by
  simp [checkCertificate]

theorem certificate_sound (c : Certificate) (h : checkCertificate c = true) :
    Certificate.Valid c := (certificate_acceptance c).mp h

end V2
end ShenLogic
