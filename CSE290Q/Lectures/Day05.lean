import Mathlib.Tactic

/-!
Agenda:
- Talk about history of ITPs
- Look at Automath
- Continue talking about natural deduction
-/

/-
intensionality:   convertibility
extensionality:   Eq   (=)
-/

namespace NS

-- * bool := PN : TYPE
axiom bool : Type
-- * b := --- : bool
variable (b : bool)
-- b * TRUE := PN : TYPE
axiom TRUE (b : bool) : Type
-- b * c := --- : bool
variable (c : bool)
-- c * impl := PN : bool
axiom impl (b c : bool) : bool
-- c * asp1 := --- : TRUE(b)
variable (asp1 : TRUE b)
-- asp1 * asp2 := --- : TRUE(impl)
variable (asp2 : TRUE (impl b c))
-- asp2 * modpon := PN : TRUE(c)
axiom modpon (b c : bool) (asp1 : TRUE b) (asp2 : TRUE (impl b c)) : TRUE c
-- c * asp4 := --- : [x,TRUE(b)]TRUE(c)
variable (asp4 : (x : TRUE b) → TRUE c)
-- asp4 * axiom' := PN : TRUE(impl)
axiom axiom' (b c : bool) (asp4 : TRUE b → TRUE c) : TRUE (impl b c)
/-
        Γ, hp : TRUE p ⊢ hq : TRUE q
  ----------------------------------- →I
    Γ ⊢ (fun (hp : p) => hq) : TRUE (p → q)
-/

/-

x : Nat, y : Nat ⊢ ...
in CoC paper:
((x : Nat) → (y : Nat) → *) ⊢ ...

-/

end NS

/-!
# Natural deduction (cont'd)

First-order logic consists of

- propositional logic (with ¬, ∧, ∨, →, ↔, True, and False),
- quantifiers (∀, ∃), and
- propositional and predicate variables

---

Notation and basic concepts:

  `p`, `q`, `r`, etc. are propositional (meta)variables

  `h`, `hp`, `hq`, etc. are proof (meta)variables

  `α`, `β`, `γ`, etc. are types

  `p : Prop` is pronounced "p is a proposition"
  `h : p`    is pronounced "h is a proof of p"
  `α : Type` is pronounced "α is a type"
  `x : α`    is pronounced "x has type α"

  A *context* is a list of these `:` pairs, e.g.
    p : Prop, q : Prop, hp : p, hq : q

  `Γ`, etc. are context metavariables

  `Γ ⊢ p : Prop` is the judgment "`p` is a proposition in context `Γ`"

  `Γ ⊢ h : p`    is the judgment "`h` is a proof of `p` in context `Γ`"

  `Γ ⊢ p`        is the judgment "there exists a proof `h` such that `Γ ⊢ h : p`"
                 (we say that `p` is *true* with respect to `Γ` in such a case)

-/

/-!
# Quantifiers
-/

/-!
## Universal introduction

Let `p` denote a predicate with domain `α`.
We encode predicates as functions `p : α → Prop`,
and we write `p x` instead of `p(x)`.

           Γ, x : α ⊢ hp : p x
  ----------------------------------------- ∀I
    Γ ⊢ (fun (x : α) => hp) : ∀ x : α, p x

-/

example {α : Type} (p : α → Prop) : ∀ x : α, p x :=
  fun (x : α) => sorry
/-
At `sorry`, we see that the local context is
  x : α  ⊢ p x
which matches what's above the line for →I
-/



/-
What? We use `fun` both for `→` introduction and `∀` introduction?
-/

/-!
## Existential introduction

Let `p` denote a predicate with domain `α`.

     Γ ⊢ t : α      Γ ⊢ hp : p t
  --------------------------------------- ∃I
    Γ ⊢ Exists.intro t hp : ∃ x : α, p x

This is like a conjunction.
-/

variable {α : Type} (p : α → Prop) in
variable (t : α) (hp : p t) in
#check (Exists.intro t hp : ∃ x : α, p x)



/-!
## Universal elimination

    Γ ⊢ h : ∀ x : α, p x    Γ ⊢ t : α
  ------------------------------------ ∀E
            Γ ⊢ h t : p t
-/

variable {α : Type} (p : α → Prop) in
variable (h : ∀ x : α, p x) (t : α) in
#check (h t : p t)

/-!
## Existential elimination

  Γ ⊢ h : ∃ x, p x   Γ, x : α, hp : p x ⊢ hq : q
--------------------------------------------------- ∃E
  Γ ⊢ (match h with | Exists.intro x hp => hq) : q

More complicated to state than conjunction elimination (∧I₁ and ∧I₂).
-/

example {α : Type} (p : α → Prop) (q : Prop) (h : ∃ x, p x) : q :=
  let ⟨x, hp⟩ := h
  sorry

/-
Compare to

      Γ ⊢ h : p ∧ q   Γ, hp : p, hq : q ⊢ hr : r
  ------------------------------------------------- ∧E
     Γ ⊢ And.casesOn h (fun hp hq => hpqr) : r
-/
