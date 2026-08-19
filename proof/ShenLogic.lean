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
