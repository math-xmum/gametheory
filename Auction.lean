import Mathlib.Data.Real.EReal
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Lattice



open Classical

structure Auction where
   I : Type*
   hF : Fintype I
   hI: Inhabited I
   hP : ∃ i j : I , i ≠ j
   hP' :  ∀ i : I , ∃ j, i ≠  j
   v : I → ℝ -- The value of each clients


namespace Auction

variable {a : Auction} (b : a.I → ℝ  )

instance : Fintype a.I := a.hF

@[simp]
def maxb : ℝ  := Finset.sup' Finset.univ (⟨ a.hI.default ,  (Finset.mem_univ _)⟩ ) b


lemma exists_max : ∃ i: a.I, b i = a.maxb b := by
{
   obtain ⟨  i , _ ,h2⟩ := Finset.exists_mem_eq_sup' (⟨ a.hI.default, (Finset.mem_univ _)⟩ ) b
   exact ⟨ i, symm h2⟩
}


noncomputable def winner : a.I := Classical.choose (exists_max b)

lemma winner_take_max : b (winner b) = maxb b:= Classical.choose_spec (exists_max b)

lemma delete_i_nonempty (i:a.I) :Finset.Nonempty (Finset.erase  Finset.univ i ) := by
{
  obtain ⟨ i , hi ⟩  := a.hP' i
  use i
  simp only [Finset.mem_univ, not_true, Finset.mem_erase, and_true]
  rw [ne_comm]
  exact hi
}

--B is the maxial bid of all but i
noncomputable def B (i: a.I) : ℝ  := Finset.sup' (Finset.erase Finset.univ i) (delete_i_nonempty i) b


noncomputable def secondprice : ℝ  := B b (winner b)


noncomputable def utility  (i : a.I) : ℝ := if i = winner b then a.v i - secondprice b else 0

lemma utility_winner (H: i = winner b) : utility b i = a.v i - secondprice b
:= by rw [utility]; simp only [ite_true, H]

lemma utility_loser (i: a.I) (H : i≠ winner b) : utility b i = 0
:= by rw [utility]; simp only [ite_false, H]

def dominant (i : a.I) (bi : ℝ) : Prop :=
   ∀ b b': a.I → ℝ , (b i = bi) → (∀ j: a.I, j≠ i→ b j = b' j)
   →  utility  b i ≥ utility b' i


lemma gt_wins (i : a.I) (H: ∀ j , i ≠j →  b i > b j) : i = winner b
:= by {
   have HH : ∀ j, i = j ↔  b j = maxb b:= by {
      have imax : b i = maxb b := by {
         have H1 : b i ≤  maxb b := by
         {
            apply Finset.le_sup'
            simp only [Finset.mem_univ]
         }
         have H2 : maxb b ≤ b i := by
         {
            apply Finset.sup'_le
            intro j _
            by_cases hji : i=j
            . rw [hji]
            . {
               have hji' := H j ( by rw [ne_eq] ; exact hji)
               linarith
            }
         }
         linarith
      }
      intro j
      constructor
      . {
         intro hji
         rw [<-hji]
         exact imax
      }
      . {
         intro hbj
         by_contra hji
         have hji' := H j (by rw [ne_eq];exact hji)
         rw [hbj] at hji'
         linarith
      }
   }
   rw [HH]
   rw [<-winner_take_max]
}






lemma b_winner_max (H: i = winner b) : ∀ j: a.I, b i ≥ b j
:= by{
          intro j

          have H_max: b (winner b) = maxb b := winner_take_max b
          rw [<-H] at H_max
          --怎么将 winner_take_max 重写为关于 i 的形式:直接rw反过来
          have H_sup: b j ≤ maxb b
          {
          apply Finset.le_sup'
          simp only [Finset.mem_univ]
          }
          rw [<-H_max] at H_sup
          exact H_sup
           --怎么用这个linarith：不用linarith就行
     }

lemma b_winner' (H: i = winner b) : b i ≥ B b i := by
{
   have Hmax := winner_take_max b
   rw [<-H] at Hmax
   rw [Hmax]
   apply Finset.sup'_le
   intro j
   intro hj
   apply Finset.le_sup'
   simp only [Finset.mem_erase,Finset.mem_univ]
}

lemma b_winner (H: i = winner b) : b i ≥ secondprice b := by
   {
    have Hmax := winner_take_max b
    rw [<-H] at Hmax
    rw [Hmax]
    apply Finset.sup'_le
    apply delete_i_nonempty
    intro j _
    apply Finset.le_sup'
    simp only [Finset.mem_erase,Finset.mem_univ]

   }

lemma b_loser_max (H: i ≠  winner b) : B b i = maxb b := by
   {
      have H1 : B b i ≤ maxb b := by
      {
         apply Finset.sup'_le
         intro i _
         apply Finset.le_sup'
         simp only [Finset.mem_univ]
      }
      have H2 : maxb b ≤ B b i := by
      {
       rw [<-winner_take_max]
       intro j _
       by_cases hji : i=j
       apply Finset.sup'_le
      }
      linarith
   }
--bbi<=maxb b
--maxb b<=bbi
lemma b_loser' (H: i ≠  winner b) : b i ≤ B b i := by
   {
      have Hmax := winner_take_max b
      rw [Hmax]
      apply Finset.sup'_le
      intro j
      intro hj
      apply Finset.le_sup'
      simp only [Finset.mem_erase,Finset.mem_univ]

   }

lemma b_loser (H: i ≠  winner b) : b i ≤ secondprice b := by sorry

lemma utility_pos (i: a.I) : (b i = a.v i) → utility b i≥0   := by sorry

theorem valuation_is_dominant (i : a.I ) : dominant i (a.v i) := by {
   intro b b' hb hb'
   by_cases H : i = winner b'
   . {
      by_cases H2 : a.v i >  B b' i
      . {
         -- Show that i is also the winner for bidding b
         -- Show that secondprice b  = secondprice b'
         -- Show that utility b i = utility b' i
         sorry
      }
      . {
         -- Show that 0 ≥  utility b' i
         -- Combine with utility b i ≥ 0 finish the proof
         sorry
      }
   }
   . {
      have u' := utility_loser b' i  H
      simp only [u',utility_pos b i hb]
   }
}


end Auction
