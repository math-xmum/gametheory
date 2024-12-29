import Mathlib
import GameTheory.Scarf
import LLMlean

noncomputable section

variable (n l : ℕ) (i : Fin n)

abbrev TT := {x : Πₗ (i : Fin n), ℕ | ∑ i, x i  = l}

instance TT.funlike : FunLike (TT n l) (Fin n) ℕ where
  coe := fun a => a.1
  coe_injective' := by simp

variable {n l} in
abbrev TT.Ilt ( x y : TT n l) :=
  toLex (x i, x)  < toLex (y i, y)

instance TT.IST : IsStrictTotalOrder (TT n l) (TT.Ilt i) where
  trichotomous := by
    intro a b
    repeat rw [TT.Ilt]
    have h1 : toLex (a i, a) <  toLex (b i, b) ∨ toLex (a i, a) = toLex (b i, b) ∨ toLex (b i, b) < toLex (a i, a) :=
      by apply IsTrichotomous.trichotomous
    convert h1
    suffices hh : a = b → a i = b i from
      by simp;exact hh
    intro h;rw [h]
  irrefl := by simp
  trans := by
    intro a b c
    rw [TT.Ilt]
    apply lt_trans


variable {n l} in
instance TT.ILO : IndexedLOrder (Fin n) (TT n l) where
  IST := fun i => linearOrderOfSTO (TT.Ilt i)

set_option quotPrecheck false
local notation  lhs "<[" i "]" rhs => (IndexedLOrder.IST i).lt lhs rhs
local notation  lhs "≤[" i "]" rhs => (IndexedLOrder.IST i).le lhs rhs

lemma TT.Ilt_def (a b : TT n l) :
  (a <[i] b) ↔ TT.Ilt i a b := by
  rfl

lemma TT.Ilt_keyprop (a b : TT n l) :
  a i < b i → a <[i] b := by
  intro h
  rw [TT.Ilt_def,Ilt,Prod.Lex.lt_iff]
  simp [h]



end
