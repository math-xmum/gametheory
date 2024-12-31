import Mathlib
import GameTheory.Scarf
import LLMlean

open Classical

section
/-- A dependent product of finite, indexed by finite, is a finite. -/
instance Pi.Lex.finite {α : Type*} {β : α → Type*} [DecidableEq α] [Finite α]
    [∀ a, Finite (β a)] : Finite (Πₗ a, β a) :=
        (Equiv.finite_iff toLex).1 Pi.finite

end

noncomputable section
open IndexedLOrder


variable (n l : ℕ+) (i : Fin n)

abbrev TT := {x : Πₗ (_ : Fin n), Fin (l+1) | ∑ i, x i  = l}

instance TT.finite : Finite (TT n l) := by
  rw [Set.coe_eq_subtype]
  exact Subtype.finite

instance TT.inhabited : Inhabited (TT n l) where
  default :=
    ⟨ fun i => if i = 0 then l else 0,  by simp⟩

instance TT.funlike : FunLike (TT n l) (Fin n) (Fin (l+1)) where
  coe := fun a => a.1
  coe_injective' := by simp

variable {n l} in
def TTtostdSimplex (x : TT n l) : stdSimplex ℝ (Fin n) := ⟨fun i => x i / l, by
  rw [stdSimplex]
  constructor
  · intro;simp only[Set.coe_setOf]
    apply div_nonneg <;> simp
  · simp only [Set.coe_setOf];
    rw [<-Finset.sum_div]
    sorry
  ⟩

instance TT.CoestdSimplex : CoeOut (TT n l) (stdSimplex ℝ (Fin n)) where
  coe := TTtostdSimplex


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


lemma size_bound_key (σ : Finset (TT n l)) (C : Finset (Fin n)) (h : TT.ILO.isDominant σ C)
(h2 : σ.Nonempty):
  l < ∑ k ∈ C, σ.inf' h2 f + C.card  := by sorry

theorem size_bound_in (σ : Finset (TT n l)) (C : Finset (Fin n)) (h : TT.ILO.isDominant σ C): ∀ x ∈ σ , ∀ y ∈ σ , ∀ i ∈ C, (x i:ℤ ) - (y i : ℤ) < 2 * n +1 := by sorry

/- Theorem 10-/
theorem size_bound_out (σ : Finset (TT n l)) (C : Finset (Fin n)) : ∀ x ∈ σ , ∀ y ∈ σ , ∀ i ∉ C, (x i:ℤ )  <  n +1 := by sorry


section Brouwer


--instance stdSimplex.cpt : CompactSpace ↑(stdSimplex ℝ (Fin n)) := inferInstance

variable (f : stdSimplex ℝ (Fin n) → stdSimplex ℝ (Fin n))

variable {n l}

instance stdSimplex.upidx (x y : stdSimplex ℝ (Fin n)) : Nonempty { i | x.1 i ≤ y.1 i} := by sorry

noncomputable def stdSimplex.pick (x  y : stdSimplex ℝ (Fin n)) := Classical.choice $ stdSimplex.upidx x y



def Fcolor (x : TT n l) : Fin n := stdSimplex.pick x (f x)

def room_seq (l' : ℕ) :=
  let l : PNat := ⟨l'+1,Nat.zero_lt_succ _⟩
  Classical.choice (TT.ILO.Scarf (@Fcolor n l f)).to_subtype

def room_point_seq (l' : ℕ) := pick_colorful_point
(Finset.mem_filter.1 (room_seq f l').2).2 |>.1



section finiteness
theorem exists_subseq_constant_of_finite_image {s : Finset α} (e : ℕ → α) (he : ∀ n, e n ∈ s ) :
  ∃ a ∈ s, ∃ g : ℕ ↪o ℕ,  (∀ n, e (g n) = a) := by
  sorry

end finiteness

lemma constant_index_set_nonempty : Nonempty {(a, g) :(Finset (Fin n)) × (ℕ ↪o ℕ) | ∀ l', (room_seq f (g l')).1.2 = a } := by
  obtain ⟨a, ha,g,hg⟩ := exists_subseq_constant_of_finite_image (s := Finset.univ)
    (fun x => (room_seq f x).1.2) (by simp)
  use ⟨a,g⟩; simp [hg]


/- room_seq ∘ gpkg.1.2 has constant value equal to gpkg.1.1-/
def gpkg :=  Classical.choice $ constant_index_set_nonempty f

abbrev g1 := gpkg f |>.1.2


open Topology

/- room_seq ∘ g1 ∘ hpkg.1.2 converge to a point in stdSimplex-/
def hpkg_aux:
  Nonempty {(w , h) : (stdSimplex ℝ  (Fin n)) × (ℕ → ℕ) | StrictMono h ∧ Filter.Tendsto
    (fun l => (room_point_seq f (g1 f l): stdSimplex ℝ (Fin n)))
    Filter.atTop (𝓝 w) } := sorry

def hpkg := Classical.choice $ hpkg_aux f



theorem Brouwer (hf : Continuous f): ∃ x , f x = x := by
  use (hpkg f).1.1
  sorry


end Brouwer
end
