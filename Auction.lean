import Mathlib.Data.Real.EReal 
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Lattice

open Classical

section 

variable  {I : Type*} [Fintype I] [Inhabited I] (H : ∃ i j : I, i≠j) (v : I→ ℝ)

section
 
variable {I : Type*} [Fintype I] [hI: Inhabited I] {hP : ∃ i j : I , i ≠ j } 
variable (b :I →  ℝ  )


lemma hP': ∀ i : I , ∃ j, i ≠  j := by 
{
   obtain  ⟨ ii, jj , hh⟩  := hP
   intro i
   by_cases (i=ii)
   . use jj ; rw [h] ; exact hh
   --use jj as j
   . use ii
}
--这有点像if/else，case by case讨论？

/-
example (P Q : Prop ) : P ∧  Q → Q ∧ P :=  by {
  intro H
  exact ⟨H.2, H.1⟩ 
} 

def one : {x:ℕ // x>0} := {
   val :=1
   property := by norm_num
}

def one' : {x:ℕ // x>0} := ⟨ 1, by norm_num⟩ 


#check one
-/

def maxb : ℝ  := Finset.sup' Finset.univ (⟨ hI.default ,  Finset.mem_univ _⟩ ) b
/-
Given nonempty finset s then s.sup' H f is the supremum of its image under b in
-/

/-后面跟个b是什么作用
b: I → ℝ
-/

/- Finset.univ is the universal finite set of type Finset α implied from the assumption Fintype α.
全集

-/



--⟨ ⟩ 什么时候用

lemma exists_max : ∃ i: I, b i = maxb b := by
{
   obtain ⟨  i , _ ,h2⟩ := Finset.exists_mem_eq_sup' (⟨ hI.default, Finset.mem_univ _⟩ ) b
   exact ⟨ i, symm h2⟩
}
--theorem Finset.exists_mem_eq_sup'{α : Type u_2} {ι : Type u_5} [LinearOrder α] {s : Finset ι} (H : Finset.Nonempty s) (f : ι → α) :
--   ∃ i, i ∈ s ∧ Finset.sup' s H f = f i


noncomputable def winner : I := Classical.choose (exists_max b)

lemma winner_take_max : b (winner b) = maxb b:= Classical.choose_spec (exists_max b)

lemma second_nonempty :Finset.Nonempty (Finset.erase  Finset.univ (winner b) ) := by 
{
  obtain ⟨ i , hi ⟩  := @hP' I hP (winner b) 
  use i
  simp only [Finset.mem_univ, not_true, Finset.mem_erase, and_true]
  rw [ne_comm]
  exact hi
}

noncomputable def secondprice : ℝ  := Finset.sup' (Finset.erase Finset.univ (winner b))
(@second_nonempty _ _ _ hP b) b

variable (v: I → ℝ)

noncomputable def utility  (i : I) : ℝ := max (v i - (@secondprice _ _ _ hP b)) 0 


-- bi is the dominant bidding for i-th player
def dominant (i : I) (bi : ℝ) : Prop :=
   ∀ b b': I → ℝ , (b i =bi) → (∀ j:I, j≠ i→ b j = b' j) 
   →  @utility _ _ _ hP b v i ≥ @utility _ _ _ hP b' v i 

end

theorem valuation_is_dominant (i : I ) : @dominant _ _ _ hP v i (v i) := by {
   sorry
   
}

end

