import Mathlib
import GameTheory.Scarf
import LLMlean

noncomputable section

variable (n l : ℕ) (i : Fin n) [Fact (1 < n )]

abbrev TT := {x : Πₗ (i : Fin n), ℕ | ∑ i, x i  = l}

instance TT.inhabited : Inhabited (TT n l) where
  default :=
    ⟨ fun i => if i = 0 then l else 0,  by simp⟩

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

/- Theorem 10-/


lemma size_bound_key (σ : Finset (TT n l)) (C : Finset (Fin n)) (h : TT.ILO.isDominant σ C): l < ∑ k ∈ C,   := by sorry

theorem size_bound_in (σ : Finset (TT n l)) (C : Finset (Fin n)) (h : TT.ILO.isDominant σ C): ∀ x ∈ σ , ∀ y ∈ σ , ∀ i ∈ C, (x i:ℤ ) - (y i : ℤ) < 2 * n +1 := by sorry

/- Theorem 10-/
theorem size_bound_out (σ : Finset (TT n l)) (C : Finset (Fin n)) : ∀ x ∈ σ , ∀ y ∈ σ , ∀ i ∉ C, (x i:ℤ )  <  n +1 := by sorry


end
