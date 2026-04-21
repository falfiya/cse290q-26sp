import Mathlib.Tactic

/-
# The Calculus of Constructions

Coquand and Huet, 1988

Q/A
- Consistency, what does that mean?
  It means that ¬(⊢ False)
  Inconsistent, ⊢ False
    Then, since False -> p for all p, then ⊢ p for all p
- *, why isn't `⊢ * : *` ?  Girard's paradox.  (Jean-Yves)
  (* : Δ : □ : ...)
  (Pure Type Systems go in this direction.  Have things like `* -> *`)
  Universes
  Type : Type 1 : Type 2 : Type 3 : ...
- * is both propositions and types?
  p : Prop
  α : Type
  p : τ
  α : τ, where τ encompasses both Prop and Type
- A little about untyping:
  When you compile CoC to a program, the types have no computational content.
  So, erase them, in a systematic way.
- What's going on with 101 (*)?

  Γ ⊢ M : Δ
  e.g.
  [k:Nat]* ⊢ (λn:Int)(λp:Int→* )(p (n+k)) : [n:Int][p:Int→*]*

  It's a typo. Second rule should be

  Γ ⊢ M : Δ
  ---------     (*)
  Γ ⊢ M ≅ M
-/

/-
Notions

Lambda abstractions
  (λx : N) M
for
  fun x : N => M

  (other sources: λ x . N)

Products
  [x : A] M
for
  (x : A) → M
  Π x : A, M  in other type theory sources

Why is it a "product"?
How many functions from {1,2} → {a,b,c} are there?
Given f : {1,2} → {a,b,c},  what's the data?
  f(1) is something  (3 options)
  f(2) is something  (3 options)
  so there are 3*3 options

|Π x : A, M| = Π x : A, |M|
-/

/-
De Bruijn indexing,
referencing depth of occurrence with respect to number of
the (λx : N) or [x : A] quantifiers.

e.g.
  (λx : M)(λy : N)((x y) x)
  (λM)(λN)((1 0) 1)

  (λx : M)(x [y : N]((x y) x))
  (λM)(0 [N]((1 0) 1))

-/

/-
The * constant, the "universe of all types".
Both propositions and types have * as their type

"Type of all types"?

-/

/-
Contexts
  [x₁:A₁][x₂:A₂]⋯[xₙ:Aₙ]*

Types of logical propositions and proposition schemas

schemas are families.
-/

inductive Term where
  | star                           -- *
  | lam (M : Term) (N : Term)      -- (λx:M)N
  | forallE (M : Term) (N : Term)  -- [x:M]N
  | bvar (idx : Nat)               -- De Bruijn variables
  | app (M N : Term)               -- M N
  deriving Inhabited

mutual

/-- Predicate for contexts legal of depth n -/
inductive Term.IsContextAt : Nat → Term → Prop where
  | univ {n : Nat} :
    ------------------
    star.IsContextAt n
  | quant_obj {n : Nat} {M N : Term} :
    M.IsObjectAt n → N.IsContextAt (n + 1) →
    ----------------------------------------
    (forallE M N).IsContextAt n
  | quant_ctx {n : Nat} {M N : Term} :
    M.IsContextAt n → N.IsContextAt (n + 1) →
    -----------------------------------------
    (forallE M N).IsContextAt n

/-- Predicate for objects legal of depth n -/
inductive Term.IsObjectAt : Nat → Term → Prop where
  | var {n k : Nat} : k < n → IsObjectAt n (bvar k)
  | prod_obj {n : Nat} {M N : Term} :
    M.IsObjectAt n → N.IsObjectAt (n + 1) →
    ---------------------------------------
    (forallE M N).IsObjectAt n
  | prod_ctx {n : Nat} {M N : Term} :
    M.IsContextAt n → N.IsObjectAt (n + 1) →
    ----------------------------------------
    (forallE M N).IsObjectAt n
  | lam_obj {n : Nat} {M N : Term} :
    M.IsObjectAt n → N.IsObjectAt (n + 1) →
    ---------------------------------------
    (lam M N).IsObjectAt n
  | lam_ctx {n : Nat} {M N : Term} :
    M.IsContextAt n → N.IsObjectAt (n + 1) →
    ----------------------------------------
    (lam M N).IsObjectAt n
  | appl {n : Nat} {M N : Term} :
    M.IsObjectAt n → N.IsObjectAt n →
    ---------------------------------
    (app M N).IsObjectAt n

end

def Term.IsTermAt (M : Term) (n : Nat) : Prop :=
  M.IsContextAt n ∨ M.IsObjectAt n

def Term.IsContext (M : Term) : Prop :=
  ∃ n : Nat, M.IsContextAt n

def Term.IsObject (M : Term) : Prop :=
  ∃ n : Nat, M.IsObjectAt n

def Term.IsClosed (M : Term) : Prop :=
  M.IsTermAt 0

#print Term.IsObjectAt

syntax "lets_solve_it" : tactic
macro_rules
  | `(tactic| lets_solve_it) =>
    `(tactic|
      first
      | (try constructor) <;> done
      -- | (first | left | right) <;> lets_solve_it
      | apply Term.IsObjectAt.var <;> lets_solve_it
      | apply Term.IsObjectAt.prod_obj <;> lets_solve_it
      | apply Term.IsObjectAt.prod_ctx <;> lets_solve_it
      | apply Term.IsObjectAt.lam_obj <;> lets_solve_it
      | apply Term.IsObjectAt.lam_ctx <;> lets_solve_it
      | apply Term.IsObjectAt.appl <;> lets_solve_it
      | apply Term.IsContextAt.univ <;> lets_solve_it
      | apply Term.IsContextAt.quant_obj <;> lets_solve_it
      | apply Term.IsContextAt.quant_ctx <;> lets_solve_it
      | grind )

open Term in
example :
    -- [x:[y:*]y](x x)
    (forallE (forallE star (bvar 0)) (app (bvar 0) (bvar 0))).IsClosed := by
  unfold Term.IsClosed Term.IsTermAt
  right
  show_term lets_solve_it

/-
Free variables?

These are bvars that don't refer to quantifiers in the expression.
-/

-- ...[3][2][1][0] | (λM)(λN)(3 4 1)


def Term.hasFreeBVar (p : Nat → Bool) (M : Term) (depth : Nat := 0) : Bool :=
  match M with
  | star => false
  | forallE M N => M.hasFreeBVar p depth || N.hasFreeBVar p (depth + 1)
  | lam M N => M.hasFreeBVar p depth || N.hasFreeBVar p (depth + 1)
  | app M N => M.hasFreeBVar p depth || N.hasFreeBVar p depth
  | bvar idx =>
    if idx < depth then
      false
    else
      p (idx - depth)

open Term in
#eval let M := (lam star (lam star (app (app (bvar 3) (bvar 4)) (bvar 1))))
      M.hasFreeBVar (· == 1)

theorem Term.closed_iff_not_hasFreeBVar (M : Term) :
    M.IsClosed ↔ ¬ M.hasFreeBVar (fun _ => true) := by
  sorry -- exercise!

def Term.contextLength (Γ : Term) : Nat :=
  match Γ with
  | star => 0
  | forallE _ Δ => Δ.contextLength + 1
  | _ => panic! "not a context"

def Term.contextConcat (Γ Δ : Term) : Term :=
  match Γ with
  | star => Δ
  | forallE M Γ' => forallE M (Γ'.contextConcat Δ)
  | _ => panic! "not a context"

def Term.contextExtend (Γ M : Term) : Term :=
  Γ.contextConcat (forallE M star)

/-
Curry-Howard isomorphism

Objects represent logical propositions as well as
individual elements and functions.

Uniform notation

CoC      Propositions        Types
[x:M]P   (∀x:M)N             (Πx:M)N   (x:M)→N
(λx:M)N  →I rule             functions
M N      →E (modus ponens)   application
-/



/-
"Relocation operation" ξᵢ
-/

/-- Take all free bvars with idx ≥ i, and increment them -/
def Term.liftVars (M : Term) (i : Nat) (depth : Nat := 0) : Term :=
  match M with
  | star => star
  | forallE M N => forallE (M.liftVars i depth) (N.liftVars i (depth+1))
  | lam M N => lam (M.liftVars i depth) (N.liftVars i (depth+1))
  | app M N => forallE (M.liftVars i depth) (N.liftVars i depth)
  | bvar idx =>
    if idx < depth then
      bvar idx
    else if idx - depth ≥ i then
      bvar (idx + 1)
    else
      bvar idx

-- Exercise: use the liftVars version that increments i instead, and prove
-- it's the same. (If it's true.)

def Term.lift (M : Term) : Term :=
  M.liftVars 0

/--
Given [xₙ₋₁:Γₙ₋₁][x₀:Γ₀]*,
Γ.contextAt k is Γₖ with vars lifted
-/
def Term.contextAt (Γ : Term) (k : Nat) : Term :=
  sorry











/-
Cut elimination

Γ, p ⊢ q   Γ ⊢ p
----------------
     Γ ⊢ q

-/
