import Mathlib

--open Classical

/-
We use S to denote a mixed stratage
-/

variable (α : Type*) [Fintype α] [DecidableEq α]

namespace stdSimplex
variable (k : Type*)  [OrderedSemiring k] (α : Type*) [Fintype α]

instance funlike : FunLike (stdSimplex k α) α k where
  coe := Subtype.val
  coe_injective' := Subtype.val_injective

variable {k α} in
abbrev pure [DecidableEq α] (i : α) : stdSimplex k α  := ⟨fun j => if i=j then 1 else 0,
 by {
  constructor
  . {
    intro j
    by_cases H: i=j
    repeat simp [H]
  }
  . simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  }⟩

noncomputable instance SInhabited_of_Inhabited [DecidableEq α] [Inhabited α]: Inhabited (stdSimplex k α) where
  default := pure (default : α)


noncomputable instance SNonempty_of_Inhabited {α : Type*} [DecidableEq α] [Fintype α] [Inhabited α]: Nonempty (stdSimplex k α) := Nonempty.intro (default : stdSimplex k α)

variable {k α} in
lemma wsum_magic_ineq {σ : stdSimplex k α} {f : α → k} {c : k} :
  ∑ i : α, (σ i) *  f i = c → ∃ i, 0 < σ i ∧ f i ≤ c := by
    intro H1
    by_contra H2
    replace H2 :∀ i, σ i = 0 ∨ c < f i := by sorry
    -- use Finset.sum_lt_sum
    sorry

end stdSimplex


abbrev S:= stdSimplex ℝ α

namespace S

variable {α : Type*} [Fintype α] [DecidableEq α]

/-
@[simp]
noncomputable def pure (i : α) : S α  := ⟨fun j => if i=j then 1 else 0,
 by {
  constructor
  . {
    intro j
    by_cases H: i=j
    repeat simp [H]
  }
  . simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  }⟩

noncomputable instance SInhabited_of_Inhabited {α : Type*} [Fintype α] [Inhabited α]: Inhabited (S α) where
  default := pure (default : α)


noncomputable instance SNonempty_of_Inhabited {α : Type*} [Fintype α] [Inhabited α]: Nonempty (S α) := Nonempty.intro (default : S α)

-/
