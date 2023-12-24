import Mathlib.Data.Real.EReal
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.MetricSpace.Basic


-- ℝ is not a complete lattice,
--iSup may not exits le_iSup' (lam.aux A B)  (linear_comb t xx xx')
-- use theorems starts with ciSup etc.

import GameTheory.Simplex

open Classical

/-
We use S to denote a mixed stratage
-/


variable (I J : Type*)

@[ext]
structure zerosumGame where
  g : I → J → ℝ
  HI : Inhabited I
  HJ : Inhabited J

instance : CoeFun (zerosumGame I J) (fun _ => I →  J → ℝ ) where
  coe := zerosumGame.g

attribute [coe] zerosumGame.g


namespace zerosumGame
variable {I J : Type*}
variable (A : zerosumGame I J)

noncomputable def maxmin : EReal := @iSup EReal _ I (fun i => @iInf EReal _ J (fun  j: J => ((A i j ):EReal)))


noncomputable def minmax : EReal := @iInf EReal _ J (fun j => @iSup EReal _ I (fun  i: I => ((A i j):EReal)))


lemma maxmin_le_minmax : maxmin A ≤ minmax A := by {
have H1 : ∀ j i,  @iInf EReal _ J (fun j => A i j) ≤ A i j:= by {
 intro j i
 apply iInf_le
}
rw [minmax,maxmin]
have H2 : ∀ j, @iSup EReal _ I (fun i => @iInf EReal _ J (fun j => A i j)
) ≤ @iSup EReal _ I (fun i => A i j) := by {
  intro j
  apply iSup_mono
  exact H1 j
}
exact le_iInf H2
}


def guarantees1 (w : ℝ) := ∃ i: I, ∀ j : J , (A i j) ≥ w

def guarantees2 (w : ℝ) := ∃ j: J, ∀ i : I , (A i j) ≤ w


end zerosumGame



namespace zerosumFGame

open S

variable {I J : Type*}  [Inhabited I] [Inhabited J] [Fintype I] [Fintype J]
variable (A : I → J → ℝ )



def sumxC (j:J) (x : S I) (C : I →J → ℝ ) := Finset.sum Finset.univ (fun i : I => (x i) *( C i j))

def sumyC (i:I) (y : S J) (C : I →J → ℝ ) := Finset.sum  Finset.univ (fun j : J=> (y j) * ( C i j))




noncomputable def E (A : I → J → ℝ) (x : S I) (y : S J) : ℝ := wsum x (fun i => wsum y (A i))

end zerosumFGame

section Loomis
open S
open zerosumFGame

variable (n : ℕ) {I J: Type*} [Inhabited I] [Inhabited J] [Fintype I] [Fintype J]


noncomputable def lam.aux (A: I →J → ℝ ) (x : S I) :=
  Finset.inf' Finset.univ (Inhabited.toFinsetNonempty J) (fun j =>
   wsum x (fun i => A i j ))



noncomputable def lam0 (A : I →J → ℝ ):=  iSup (lam.aux A )


lemma lam.aux.continouse (A : I →J → ℝ ) : Continuous (lam.aux A) := by {
  sorry
}

instance Real.instClosedIciTopology : ClosedIicTopology ℝ := ⟨by {
  intro a
  rw [<-isSeqClosed_iff_isClosed,IsSeqClosed]
  intro x p hx hp
  simp only [Set.mem_setOf_eq] at hx
  simp only [Set.mem_setOf_eq]
  apply le_of_tendsto_of_tendsto' hp (tendsto_const_nhds) hx
} ⟩

lemma lam.aux.bddAbove (A : I →J → ℝ ) : ∃ C, ∀ x , lam.aux A x ≤ C := by {
  sorry
}

lemma lam.aux.le_lam0 (A : I →J → ℝ ) : ∀ x, lam.aux A x ≤ lam0 A :=
  le_ciSup (bddAbove_def.2 (by simp [lam.aux.bddAbove A]))


lemma exits_xx_lam0 (A : I →J → ℝ ) :
   ∃ (xx : S I), ∀ j, (wsum xx (fun i => A i j)) ≥  lam0 A := by {
    have hs : IsCompact (Set.univ : Set (S I)) := isCompact_univ
    have clam.aux : ContinuousOn (lam.aux A) (Set.univ)
      := continuous_iff_continuousOn_univ.1 (lam.aux.continouse A)
    obtain ⟨xx,_,Hxx⟩ := IsCompact.exists_isMaxOn (hs) (by simp [SNonempty_of_Inhabited]) (clam.aux)
    rw [isMaxOn_iff] at Hxx
    use xx
    intro j
    calc
      lam0 A ≤ lam.aux A xx:= by {
        simp only [Set.mem_univ, forall_true_left] at Hxx
        simp [lam0, ciSup_le Hxx]
      }
      _ ≤ _ :=by  rw [lam.aux]; apply Finset.inf'_le _ (by simp)
   }



noncomputable def mu.aux (A : I →J → ℝ ) (y : S J) :=
  Finset.sup' Finset.univ (Inhabited.toFinsetNonempty I) (fun i =>
    wsum y (fun j => A i j ))

noncomputable def mu0 (A : I →J → ℝ ):=  iInf (mu.aux A )

lemma mu.aux.continouse (A : I →J → ℝ ) : Continuous (mu.aux A) := by {
  -- the proof is the same as that of lam
  sorry
}

-- use IsCompact.exists_isMaxOn


lemma exits_yy_mu0 (A : I →J → ℝ )  : ∃ (yy : S J), ∀ i, (wsum yy (A i)) ≤  mu0 A := by sorry
-- the proof is the same as that of xx_lam0


lemma wsum_wsum_comm {A : I→J→ ℝ }: wsum xx (fun i => wsum yy (A i)) = wsum yy (fun j => wsum xx (fun i => A i j)) := by {
  repeat simp_rw [wsum,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
}


lemma lam0_le_mu0 (A : I →J → ℝ ) :
  lam0 A ≤ mu0 A := by {
    obtain ⟨xx,Hxx⟩ := exits_xx_lam0 A
    obtain ⟨yy,Hyy⟩ := exits_yy_mu0 A
    calc
      lam0 A ≤ E A xx yy := by {
        rw [E,wsum_wsum_comm]; exact ge_iff_simplex_ge.1 Hxx yy
      }
      _ ≤ mu0 A := by rw [E]; exact le_iff_simplex_le.1 Hyy xx
  }

lemma singleton_of_card_one {I: Type*} [Fintype I] (H: Fintype.card I = 1) : ∃ i: I, (Finset.univ) = {i} ∧ (Set.univ) = {S.pure i} := by {
    obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.1 H
    use i
    constructor
    . {ext; simp [hi]}
    . { ext x
        constructor
        . {
          intro _
          simp only [S.pure, Set.mem_singleton_iff]
          have := Subtype.coe_eta x x.2
          rw [<-this]
          rw [Subtype.mk_eq_mk]
          ext j
          simp only [hi,ite_true]
          have := x.2.2
          simp only [univ_eq_singleton_of_card_one i H, Finset.sum_singleton] at this
          exact this
        }
        . simp
    }
}

lemma minmax'_IJ_2 (Hn: 2 = Fintype.card I + Fintype.card J) (A : I →J→ ℝ): lam0 A = mu0 A := by {
        have  ⟨HSI,HSJ⟩  : Fintype.card I =1 ∧ Fintype.card J =1:= by {
          have p1 := @Fintype.card_pos I _ _
          have p2 := @Fintype.card_pos J _ _
          constructor; repeat linarith
        }
        obtain ⟨i0,hi1,hi2⟩ := singleton_of_card_one HSI
        obtain ⟨j0,hj1,hj2⟩ := singleton_of_card_one HSJ
        have H1 : lam0 A = A i0 j0 := by {
          have :∀ x, lam.aux A x = A i0 j0 := by {
            intro x
            simp only [lam.aux,hj1,Finset.inf'_singleton]
            have : x = S.pure i0 := Set.mem_singleton_iff.1 (by
              simp_rw [<-hi2,Set.mem_univ])
            rw [this,wsum_pure]
          }
          rw [lam0,iSup_congr this,ciSup_const]
        }
        have H2 : mu0 A = A i0 j0 := by {
          -- The proof is the same as that of H1
          sorry
        }
        linarith
}

theorem minmax' (Hgt : 2 ≤ n) (Hn: n = Fintype.card I + Fintype.card J) (A : I →J→ ℝ): lam0 A = mu0 A := by {
      induction' n, Hgt using Nat.le_induction with n hn IH generalizing I J  A
      .  apply minmax'_IJ_2 Hn
      . {
        have := le_iff_eq_or_lt.1  (lam0_le_mu0 A)
        apply Or.elim this
        . simp
        . {
          intro lam0_lt_mu0
          exfalso
          obtain ⟨xx, Hxx⟩ :=  exits_xx_lam0 A
          obtain ⟨yy, Hyy⟩ :=  exits_yy_mu0 A
          have exits_ij : (∃ j:J, (wsum xx (fun i => A i j)) > lam0 A )
             ∨  (∃ i:I, (wsum yy (fun j => A i j)) < mu0 A)
            := by {
              by_contra HP
              simp only [not_or,not_exists,gt_iff_lt,not_lt] at HP
              have Hxx:∀ (j : J), (wsum xx fun i => A i j) = lam0 A := fun j => le_antisymm  (HP.1 j) (Hxx j)
              have Hyy:∀ (i : I), (wsum yy (A i))  = mu0 A := fun i => le_antisymm  (Hyy i) (HP.2 i)
              have  :lam0 A = mu0 A:= by {calc
                lam0 A = E A xx yy := by {
                  rw [E,wsum_wsum_comm]
                  simp only [wsum_const' Hxx]
                }
                _ = mu0 A := by simp only [E,wsum_const' Hyy]
              }
              linarith
            }
          apply Or.elim exits_ij
          .  {
            intro HJ
            obtain ⟨j0,HJ⟩:= HJ
            let J' := {j : J // j≠j0}
            have inhabited_J' : Inhabited J':= by sorry
            have cardn : n = Fintype.card I + Fintype.card J' := by {
              have : Fintype.card J'  = Fintype.card J -1 := by simp only [ne_eq, Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, ge_iff_le]
              have cardposJ: 1≤ Fintype.card J := @Fintype.card_pos J _ _
              rw [this,<-Nat.add_sub_assoc cardposJ _,<-Hn]
              simp only [ge_iff_le, add_le_iff_nonpos_left, nonpos_iff_eq_zero, add_tsub_cancel_right]
            }
            let A' := fun i: I => fun j : J' => A i j
            have HIJ' := IH cardn A'
            have lam0_lt_lam0' : lam0 A  < lam0 A' := by {sorry}
            obtain ⟨xx', Hxx'⟩ :=  exits_xx_lam0 A'
            obtain ⟨yy', Hyy'⟩ :=  exits_yy_mu0 A'
            have prop_st : ∃ t : {t: ℝ // 0≤ t ∧ t≤1},  lam.aux A (linear_comb t xx xx') > lam0 A := by {
              -- This is the most difficult part
              sorry
            }
            obtain ⟨t, Hst⟩ := prop_st
            have prop_iSup : ∀ x: S I, lam.aux A x ≤ lam0 A := lam.aux.le_lam0 A
            have := prop_iSup (linear_comb t xx xx')
            linarith
          }
          . {
            -- The proof is almost similar to the above
            sorry
          }
        }
      }
}

theorem minmax_theorem' (A : I →J→ ℝ): lam0 A = mu0 A
 := by {
      let n := Fintype.card I + Fintype.card J
      have ngetwo: 2 ≤ n :=by
         {
          have p1 := @Fintype.card_pos I _ _
          have p2 := @Fintype.card_pos J _ _
          linarith
        }
      exact minmax' n  ngetwo (rfl) A
  }

end Loomis




namespace zerosumFGame
open S
variable {I J : Type*} [Inhabited I] [Inhabited J] [Fintype I] [Fintype J]

def one_matrix (_ : I )  (_ : J):  ℝ := 1


def one_xx_eq_one {j: J } {xx : S I}: wsum xx (fun i => one_matrix i j) = 1 := by {
  simp only [wsum,one_matrix,mul_one]
  norm_cast
  simp only [S.sum_one]
}

def one_yy_eq_one {i: I } {yy : S J}: S.wsum yy (one_matrix i) = 1 := by {
  simp only [wsum,one_matrix,mul_one]
  norm_cast
  simp only [S.sum_one]
}



theorem minmax_theorem : ∃ (xx : S I) (yy : S J) (v : ℝ),
  (∀ (y : S J), (E A xx y) ≥ v ) ∧ ( ∀ (x : S I), E A x yy ≤ v)  := by {
    have  MM':= minmax_theorem' A
    obtain ⟨xx, Hxx⟩ :=  exits_xx_lam0 A
    obtain ⟨yy, Hyy⟩ :=  exits_yy_mu0 A
    use xx,yy,(lam0 A)
    constructor
    . {
      intro y
      rw [E,wsum_wsum_comm]
      apply (ge_iff_simplex_ge).1 Hxx
    }
    . {
      intro x
      rw [E,MM']
      apply (le_iff_simplex_le).1 Hyy
    }
}

end zerosumFGame
