import Batteries


namespace Lecture
/-!
# Recursion and induction

We've seen propositional and first-order logic.
We've seen some calculus of constructions.

What about data? Where are our natural numbers?
Where are our linked lists? I thought we were functional programming.
-/

-- Aside: let's remember our Church numerals:
-- def church_zero  := fun f x => x
-- def church_one   := fun f x => f x
-- def church_two   := fun f x => f (f x)
-- def church_three := fun f x => f (f (f x))

/-!
## What are the natural numbers anyway?

"Obviously," ℕ = {0, 1, 2, ...}
It starts with 0, and you can increment (take the *successor*) forever,
getting new natural numbers.
But, that's not obvious enough to put into type theory.



Imagine for some reason we believe in the real numbers `ℝ` (or some other
system that has enough arithmetic structure, if you wish); our goal is
to figure out what characterizes `ℕ` from this set.

Let's say a set `S ⊆ ℝ` is *`ℕ`-constructing* if
  1. `0 ∈ S`
  2. for all `n ∈ S`, then `n + 1 ∈ S`.

This is meant to capture what it means to construct natural numbers.
The set contains `0 + 1 + 1 + ⋯ + 1`, so `S` is big enough to construct
every natural number.

`ℕ`-constructing sets don't have to be `ℕ` itself.
The set `ℝ` itself is `ℕ`-constructing, which has too much stuff.

We say that `ℕ` is the *smallest* `ℕ`-constructing set.
Smallest means:
  for all `S ⊆ ℝ`, if `S` is `ℕ`-constructing, then `ℕ ⊆ S`



Set theory gives us a way to construct such a set. Define
  ℕ := ⋂{S ⊆ ℝ : S is `ℕ`-constructing}

The existence of this set depends on the fact that there's at
least one `ℕ`-constructing set.


(We will now dispense with `ℝ`.)


Recall that each predicate `p : ℕ → Prop` defines a set
  { x : ℕ | p x }

Let's see what the ramifications are if `{x : ℕ | p x}` is
an `ℕ`-constructing set.

  1. `0 ∈ {x : ℕ | p x}`
     means
     `p 0`

  2. for all `n ∈ {x : ℕ | p x}`, then `n + 1 ∈ {x : ℕ | p x}`
     means
     `∀ n : ℕ, p n → p (n + 1)`

Then, since `ℕ` is smallest, we get
  ℕ ⊆ {x : ℕ | p x}
which means
  ∀ n : ℕ, p n


So, assembling these, we get

  p 0      ∀ n : ℕ, p n → p (n + 1)
  --------------------------------- [ℕ-ind]
          ∀ n : ℕ, p n

That's the principle of induction!

-/

/-!
Summary so far:
1. We start with thinking about *constructing* natural numbers
   from `0` and taking successors.
2. From the collection of all such sets that support such constructions,
   we take the *least* one.
3. The least set has the principle of induction that we know and love.
-/

/-!
  n : ℕ   p 0   ∀ n : ℕ, p n → p (n + 1)
  -------------------------------------- [ℕ-elim]
          p n
-/

/-!
That was sets though.

What does this look like in type theory and lambda calculus?

Let's say a type `S` is `ℕ`-constructing if we give the additional data:
  1. `S.zero : S`
  2. `S.succ : S → S`
So, for example, 3 can be constructed as
  `S.succ (S.succ (S.succ S.zero)) : S`

-/
structure NatConst (S : Type) where
  zero : S
  succ : S → S

def Int.nat : NatConst Int where
  zero := 0
  succ := fun n => n + 1

def Int.nat' : NatConst Int where
  zero := 22
  succ := fun n => n - 2

/-!

We don't expect anything about `S.succ`. It might not be injective. For example,
we could have `Bool` with
  `zero := false`
  `succ := fun _ => true`
-/

def Bool.nat : NatConst Bool where
  zero := false
  succ := fun _ => true
-- false -> true -\
--           ^    |
--           \---/

def Bool.nat' : NatConst Bool where
  zero := false
  succ := not
-- false -> true -\
--    ^           |
--     \---------/

def Bool.nat'' : NatConst Bool where
  zero := false
  succ := fun _ => false
-- true -> false -\
--           ^    |
--           \---/

/-!

A key ingredient is to know what "smallest" means.

Something that works out is the following:
  if there's a function `α → β`, then we think of this as `α ≤ β`

  if `α` has the property that for all `β`, there exists a _unique_ function `α → β`,
  then `α` is called an *initial* type.

We'll use "initial" for "smallest". Similarly, there's a notion of "terminal"
for "largest".


We don't want to work with mere functions though. We want to consider only those
functions that somehow respect these `NatConst` structures.


-/
/-!
Q: What's the initial type in `Type`?
-/
example (β : Type) : Empty → β := nofun  -- and this function is unique

/-!
Q: What's the terminal type in `Type`?
-/
example (α : Type) : α → Unit := fun _ => () -- and this function is unique

/--
A predicate saying that the function preserves `Nat` constructions.
-/
structure NatConst.IsFunction {S S' : Type}
    (nat : NatConst S) (nat' : NatConst S')
    (f : S → S') : Prop where
  map_zero : f nat.zero = nat'.zero
  map_succ : ∀ n : S, f (nat.succ n) = nat'.succ (f n)

-- (it's a homomorphism)

-- Example:
example : NatConst.IsFunction Int.nat Bool.nat' (fun n => n % 2 == 1) where
  map_zero := rfl
  map_succ n := by
    simp [Int.nat, Bool.nat']
    grind


/-!
Given this, now we can express what it means to find the "smallest"
`ℕ`-constructing type.
-/
def NatConst.IsInitial {S : Type} (nat : NatConst S) : Prop :=
  ∀ (S' : Type) (nat' : NatConst S'),
  ∃ (f : S → S'),
    NatConst.IsFunction nat nat' f
    ∧ ∀ (f' : S → S'), NatConst.IsFunction nat nat' f' → f = f'

namespace Axiomatically
noncomputable section

axiom Nat : Type
axiom Nat.nat : NatConst Nat
axiom Nat.uniqueFun {S' : Type} (nat' : NatConst S') : Nat → S'
axiom Nat.uniqueFun_is_function {S' : Type} (nat' : NatConst S') :
    NatConst.IsFunction Nat.nat nat' (Nat.uniqueFun nat')
axiom Nat.uniqueFun_is_unique {S' : Type} (nat' : NatConst S')
    (f : Nat → S') (hf : NatConst.IsFunction Nat.nat nat' f) :
    Nat.uniqueFun nat' = f

theorem Nat.isInitial : Nat.nat.IsInitial := by
  intro S' nat'
  exists Nat.uniqueFun nat'
  constructor
  · apply Nat.uniqueFun_is_function
  · apply Nat.uniqueFun_is_unique

/-!
Let's unpack all this.
-/

def Nat.zero : Nat := Nat.nat.zero
def Nat.succ (n : Nat) : Nat := Nat.nat.succ n

#check (@Nat.uniqueFun)
/-
{S' : Type} → NatConst S' → Nat → S'
≈ {S' : Type} → (S' × (S' → S')) → Nat → S'
≈ {S' : Type} → (S' × (S' → S')) → Nat → S'
≈ {S' : Type} → S' → (S' → S') → Nat → S'
-/
def Nat.fold {S : Type} (zero : S) (succ : S → S) (n : Nat) : S :=
  Nat.uniqueFun { zero, succ } n

theorem Nat.fold_zero {S : Type} (zero : S) (succ : S → S) :
    Nat.fold zero succ Nat.zero = zero := by
  unfold Nat.fold
  exact (Nat.uniqueFun_is_function { zero, succ }).map_zero

theorem Nat.fold_succ {S : Type} (zero : S) (succ : S → S) (n : Nat) :
    Nat.fold zero succ (Nat.succ n) = succ (Nat.fold zero succ n) := by
  unfold Nat.fold
  apply (Nat.uniqueFun_is_function { zero, succ }).map_succ

/-
That's to say, we "could" have defined it as

def Nat.fold {S : Type} (zero : S) (succ : S → S) (n : Nat) : S :=
  match n with
  | Nat.zero => zero
  | Nat.succ n' => succ (Nat.fold zero succ n')
-/

/-
def Nat.add (m n : Nat) : Nat :=
  match n with
  | Nat.zero => m
  | Nat.succ n' => Nat.succ (Nat.add m n')

What if

def Nat.add (m n : Nat) : Nat :=
  Nat.fold ?z ?s n

Nat.add m 0 = m
  = Nat.fold ?z ?s 0
  = ?z
Nat.add m (Nat.succ n') = Nat.succ (Nat.add m n')
  = Nat.fold ?z ?s (Nat.succ n')
  = ?s (Nat.fold ?z ?s n')
  = ?s (Nat.add m n')

So ?z := m
And we have the equation
  Nat.succ (Nat.add m n') = ?s (Nat.add m n')
So, replacing `Nat.add m n'` by a fresh variable `x`, we have
  Nat.succ x = ?s x
This suggests
  ?s := fun x => Nat.succ x

Hence,
def Nat.add (m n : Nat) : Nat :=
  Nat.fold m (fun x => Nat.succ x) n

Or, after eta reduction,

def Nat.add (m n : Nat) : Nat :=
  Nat.fold m Nat.succ n
-/

theorem NatConst.IsFunction.trans {S S' S'' : Type}
    (nat : NatConst S) (nat' : NatConst S') (nat'' : NatConst S'')
    (f : S → S') (f' : S' → S'')
    (hf : NatConst.IsFunction nat nat' f)
    (hf' : NatConst.IsFunction nat' nat'' f') :
    NatConst.IsFunction nat nat'' (f' ∘ f) where
  map_zero := by simp [hf.map_zero, hf'.map_zero]
  map_succ := by simp [hf.map_succ, hf'.map_succ]

@[elab_as_elim]
def Nat.rec {S : Nat → Type}
    (zero : S Nat.zero) (succ : (n : Nat) → S n → S (Nat.succ n))
    (n : Nat) : S n := by
  let S : Type := (n : Nat) × S n
  let Snat : NatConst S :=
    { zero := ⟨Nat.zero, zero⟩,
      succ := fun n => ⟨Nat.succ n.1, succ n.1 n.2⟩ }
  let f := Nat.uniqueFun Snat
  let f' : S → Nat := fun n => n.1
  have f'isfun : NatConst.IsFunction Snat Nat.nat f' :=
    { map_zero := rfl,
      map_succ := fun _ => rfl }
  have h1 : NatConst.IsFunction Nat.nat Nat.nat (f' ∘ f) := by
    apply NatConst.IsFunction.trans Nat.nat Snat Nat.nat
    apply Nat.uniqueFun_is_function
    assumption
  have h2 : NatConst.IsFunction Nat.nat Nat.nat id := by
    constructor
    rfl
    intro
    rfl
  have h3 := Nat.uniqueFun_is_unique _ _ h1
  have h4 := Nat.uniqueFun_is_unique _ _ h2
  rw [h4] at h3
  have := congrFun h3 n
  simp [f'] at this
  have h := (f n).2
  exact this ▸ h

@[induction_eliminator]
theorem Nat.ind {p : Nat → Prop}
    (zero : p Nat.zero) (succ : (n : Nat) → p n → p (Nat.succ n))
    (n : Nat) : p n := by
  let S : Nat → Type := fun n => PLift (p n)
  let zero' : S Nat.zero := PLift.up zero
  let succ' (n : Nat) (h : S n) : S (Nat.succ n) := PLift.up (succ n h.down)
  let v : S n := Nat.rec zero' succ' n
  exact v.down

def Nat.pred (n : Nat) : Nat :=
  Nat.rec zero (fun n' _ => n') n

end
end Axiomatically

namespace Lambdas
/-!
Via Boehm-Berarducci encodings
-/

#check @Axiomatically.Nat.fold
-- {S : Type} → S → (S → S) → Nat → S
-- ≈ Nat → ({S : Type} → S → (S → S) → S)

def Nat := (S : Type) → S → (S → S) → S

#check Nat
-- Huh, that's in Type 1

-- We'd want "intersection types"
--   ∩(S : Type), S → (S → S) → S
-- (functions that are parametric in S)
-- (note to kmill: investigate the end construction in category theory)

end Lambdas


end Lecture

/-!
## Logic with the Calculus of Constructions
-/
namespace CoC

def True := ∀ (p : Prop), p → p
def False := ∀ (p : Prop), p
def Not (p : Prop) := p → False
def And (p q : Prop) := ∀ (r : Prop), (p → q → r) → r
def Or (p q : Prop) := ∀ (r : Prop), (p → r) → (q → r) → r
def Exists {α : Type} (p : α → Prop) := ∀ (r : Prop), ((x : α) → p x → r) → r

variable {p q r : Prop}

theorem imp_not_not (hp : p) : Not (Not p) :=
  sorry

theorem and_symm (hpq : And p q) : And q p :=
  sorry

theorem or_symm (hpq : Or p q) : Or q p :=
  sorry

theorem not_not_or_not : Not (Not (Or p (Not p))) :=
  sorry

def Nat := ∀ (β : Type), (β → β) → β → β

def Nat.zero : Nat := fun _β _f x => x
def Nat.succ (n : Nat) : Nat := fun β f x => f (n β f x)

def Nat.toLeanNat (n : CoC.Nat) : _root_.Nat :=
  n _root_.Nat _root_.Nat.succ _root_.Nat.zero

def _root_.Nat.toCoCNat : _root_.Nat → CoC.Nat
  | 0 => sorry
  | n+1 => sorry

-- def Nat.pred : Nat → Nat := sorry
def Nat.add : Nat → Nat → Nat := sorry
def Nat.mul : Nat → Nat → Nat := sorry

end CoC
