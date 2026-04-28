import Mathlib.Tactic
/-!
# Creating data axiomatically

In this exercise, we will work through creating data types axiomatically,
to understand theory underlying the `inductive` command. You should *never* do
this in practice since axioms can lead to inconsistency! However, we want to
understand what data really is and where it comes from.
-/

/-!
What are natural numbers?

Like for propositions, we can describe the introduction and elimination rules:
-/

-- Introduction rules (a.k.a. constructors)
#check Nat.zero
#check Nat.succ
-- Elimination rule (a.k.a. recursor)
#check Nat.rec

/-!
Hmm, that's a complicated rule. It encodes a number of things simultaneously,
and its some cleverness that we only need a single elimination rule.

In another system, we might have separate elimination rules for induction
and recursion, which have been combined here.
-/
-- We can use it to define an induction principle:
theorem Nat.induction {P : Nat → Prop} (zero : P Nat.zero)
    (succ : ∀ n, P n → P (Nat.succ n)) (n : Nat) : P n :=
  Nat.rec zero succ n

-- And we can use it to define a recursion principle:
def Nat.fold' {α : Type} (zero : α)
    (succ : α → α) (n : Nat) : α :=
  Nat.rec zero (fun _ => succ) n

-- The recursion principle satisfies two equations:
theorem Nat.fold'_zero {α : Type} (zero : α) (succ : α → α) :
    Nat.fold' zero succ Nat.zero = zero :=
  rfl
theorem Nat.fold'_succ {α : Type} (zero : α) (succ : α → α) (n : Nat) :
    Nat.fold' zero succ (Nat.succ n) = succ (Nat.fold' zero succ n) :=
  rfl

/-!
Exercise: define the addition function on natural numbers using `Nat.fold'`.
See the two theorems following it for its specification.
-/
def Nat.add' (m n : Nat) : Nat :=
  sorry

theorem Nat.add'_zero (n : Nat) :
    Nat.add' Nat.zero n = n :=
  sorry -- should be `rfl`

theorem Nat.add'_succ (m n : Nat) :
    Nat.add' (Nat.succ m) n = Nat.succ (Nat.add' m n) :=
  sorry -- should be `rfl`

/-!
Now let's try to understand what `Nat` "is", and where the recursor comes from.

Let's go back to the key fact that `Nat` has two constructors. Let's build
a type that represents a choice of constructors for a given type `τ`.
This is called a *signature* for the data type. The idea is that having
a `NatSig τ` provides a way to denote/evaluate a `Nat` in the type `τ`.
-/
structure NatSig (τ : Type) where
  zero : τ
  succ : τ → τ

-- The `Nat` as a `Nat`.
def NatSig.nat : NatSig Nat where
  zero := Nat.zero
  succ := Nat.succ

-- Write a reasonable signature for `Int`, interpreting `Nat` inside `Int`.
def NatSig.toInt : NatSig Int :=
  sorry

-- Write another signature for `Int`. This time, the interpretation
-- of `n : Nat` should be `-n-1 : Int`.
def NatSig.toNegSucc : NatSig Int :=
  sorry

-- Write a signature that computes whether or not the given `Nat` is even.
def NatSig.isEven : NatSig Bool :=
  sorry

/-!
A key part of the theory is what it means for a function to map one signature
to another.
-/
structure NatSig.IsMap {τ τ' : Type}
    (s : NatSig τ) (s' : NatSig τ')
    (f : τ → τ') : Prop where
  map_zero : f s.zero = s'.zero
  map_succ : ∀ n : τ, f (s.succ n) = s'.succ (f n)

theorem NatSig.IsMap.id {τ : Type} (s : NatSig τ) :
    NatSig.IsMap s s id :=
  sorry

theorem NatSig.IsMap.trans {τ τ' τ'' : Type}
    (s : NatSig τ) (s' : NatSig τ') (s'' : NatSig τ'')
    (f : τ → τ') (f' : τ' → τ'')
    (hf : NatSig.IsMap s s' f)
    (hf' : NatSig.IsMap s' s'' f') :
    NatSig.IsMap s s'' (f' ∘ f) :=
  sorry


/-!
(To be continued)
-/
