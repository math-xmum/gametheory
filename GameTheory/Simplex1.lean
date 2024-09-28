import Mathlib

open Classical

/-
We use S to denote a mixed stratage
-/

variable (α : Type*) [Fintype α]

namespace stdSimplex
variable (k : Type*)  [OrderedSemiring k] (α : Type*) [Fintype α]

instance funlike : FunLike (stdSimplex k α) α k where
  coe := Subtype.val
  coe_injective' := Subtype.val_injective

variable {k α} in
noncomputable abbrev pure (i : α) : stdSimplex k α  := ⟨fun j => if i=j then 1 else 0,
 by {
  constructor
  . {
    intro j
    by_cases H: i=j
    repeat simp [H]
  }
  . simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  }⟩

noncomputable instance SInhabited_of_Inhabited [Inhabited α]: Inhabited (stdSimplex k α) where
  default := pure (default : α)


noncomputable instance SNonempty_of_Inhabited {α : Type*} [Fintype α] [Inhabited α]: Nonempty (stdSimplex k α) := Nonempty.intro (default : stdSimplex k α)


end stdSimplex


abbrev S:= stdSimplex ℝ α

namespace S

variable {α : Type*} [Fintype α]

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
