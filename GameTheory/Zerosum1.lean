import Mathlib.Data.Real.EReal
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.MetricSpace.Basic



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
 sorry
} ⟩


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
  sorry
}

-- use IsCompact.exists_isMaxOn


lemma exits_yy_mu0 (A : I →J → ℝ )  : ∃ (yy : S J), ∀ i, (wsum yy (A i)) ≤  mu0 A := by sorry



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

lemma singleton_of_card_one {I:Type*} [Fintype I] (H: Fintype.card I = 1) : ∃ i: I, (Finset.univ) = {i} ∧ (Set.univ) = {S.pure i} := by {
    obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.1 H
    use i
    constructor
    . {ext; simp [hi]}
    . { ext x
        constructor
        . {
          intro _
          simp only [S.pure, Set.mem_singleton_iff]
          --apply  Subtype.ext_val
          --rw [S] at x
          have := Subtype.coe_eta x x.2
          rw [<-this]
          rw [Subtype.mk_eq_mk]
          sorry
        }
        . simp
    }
}

theorem minmax' (Hgt : 2 ≤ n) (Hn: n = Fintype.card I + Fintype.card J) (A : I →J→ ℝ): lam0 A = mu0 A := by {
      induction' n, Hgt using Nat.le_induction with n hn IH generalizing I J  A
      . {
        have  ⟨HSI,HSJ⟩  : Fintype.card I =1 ∧ Fintype.card J =1:= by {
          have p1 := @Fintype.card_pos I _ _
          have p2 := @Fintype.card_pos J _ _
          constructor; repeat linarith
        }
        obtain ⟨i0, hi0⟩ := Fintype.card_eq_one_iff.1 HSI
        obtain ⟨j0, hj0⟩ := Fintype.card_eq_one_iff.1 HSJ
        have UI : @Finset.univ I _ = {i0} := by {
          ext
          simp only [Finset.mem_univ, Finset.mem_singleton, true_iff,hi0]
        }
        have UJ : @Finset.univ J _ = {j0} := by {
          ext
          simp only [Finset.mem_univ, Finset.mem_singleton, true_iff,hj0]
        }
        rw [lam0,mu0]
      }
      . {
        sorry
      }
}

 theorem Loomis' (Hgt : 2 ≤ n) (Hn: n=Fintype.card I + Fintype.card J) (A : I →J→ ℝ) (B : I→ J→ ℝ) (PB : ∀ i:I, ∀ j:J,  B i j > 0 ):
  ∃ (v : ℝ),
    (∃  (xx : S I) , ∀ j , wsum xx (fun i => A i j) ≥  v * wsum xx (fun i=> B i j)) ∧
    (∃ (yy : S J), ∀ i ,  wsum yy (A i) ≤  v * wsum yy (B i)) := by {
      induction' n, Hgt using Nat.le_induction with n hn IH generalizing I J  A B
      . {
        have HSI : Fintype.card I =1 := by {
          have p1 := @Fintype.card_pos I _ _
          have p2 := @Fintype.card_pos J _ _
          linarith
        }
        have HSJ : Fintype.card J =1 := by {
          have p1 := @Fintype.card_pos I _ _
          have p2 := @Fintype.card_pos J _ _
          linarith
        }
        obtain ⟨i0, hi0⟩ := Fintype.card_eq_one_iff.1 HSI
        obtain ⟨j0, hj0⟩ := Fintype.card_eq_one_iff.1 HSJ
        have UI : @Finset.univ I _ = {i0} := by {
          ext
          simp only [Finset.mem_univ, Finset.mem_singleton, true_iff,hi0]
        }
        have UJ : @Finset.univ J _ = {j0} := by {
          ext
          simp only [Finset.mem_univ, Finset.mem_singleton, true_iff,hj0]
        }
        -- v = A i j /B i j where i j is the default value
        let v := A i0 j0/ B i0 j0
        use v
        constructor
        . {
          use S.pure i0
          intro j
          have HJ := hj0 j
          simp_rw [wsum, HJ, UI,Finset.sum_singleton,S.pure_eq_one,one_mul, ge_iff_le]
          have :=PB i0 j0
          calc
           A i0 j0 / B i0 j0 * B i0 j0 = A i0 j0 := by {
            exact div_mul_cancel (A i0 j0) (ne_of_gt this)
           }
           _ ≤ A i0 j0 := le_refl _
        }
        . {
            sorry
        }
      }
      . {
        by_cases  HH : lam0 A  = mu0 A
        . {
          use (lam0 A )
          exact ⟨exits_xx_lam0' A , by {rw [HH]; exact exits_yy_mu0' A }⟩
        }
        . {
          have H0:= lam0_le_mu0 A B PB
          have H0: lam0 A B < mu0 A B := by {
            rw [le_iff_lt_or_eq] at H0
            exact Or.elim H0 (id) (by intro H; exfalso;exact HH H)
          }
          obtain ⟨xx, Hxx⟩ :=  exits_xx_lam0' A B PB
          obtain ⟨yy, Hyy⟩ :=  exits_yy_mu0' A B PB
          have exits_ij : (∃ j:J, (wsum xx (fun i => A i j)) > lam0 A B * wsum xx (fun i => B i j))
             ∨  (∃ i:I, (wsum yy (fun j => A i j)) < mu0 A B * wsum yy (fun j => B i j))
            := by sorry
          apply Or.elim exits_ij
          . {
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
            let B' := fun i: I => fun j : J' => B i j
            have posB' : ∀ i j, B' i j >0 :=  fun i => fun j =>  PB i j
            obtain ⟨v',⟨xx',hxx'⟩, ⟨ yy',hyy'⟩ ⟩ := @IH I J' _ (inhabited_J') _ _ cardn A' B' posB'
            have lam0_lt_v' : lam0 A B < v' := by {sorry}
            exfalso
            have prop_st :∃ t : {t:ℝ // 0≤ t ∧ t≤1},  lam.aux A B (linear_comb t xx xx') > lam0 A B := by sorry
            obtain ⟨t, Hst⟩ := prop_st
            -- ℝ is not a complete lattice,
            --iSup may not exits le_iSup' (lam.aux A B)  (linear_comb t xx xx')
            have prop_iSup : ∀ x: S I, lam.aux A B x ≤ lam0 A B := by sorry
            have := prop_iSup (linear_comb t xx xx')
            linarith
          }
          . {
            sorry
          }
        }
      }
    }


theorem Loomis (A : I →J→ ℝ) (B : I→ J→ ℝ) (PB : ∀ i:I, ∀ j:J,  B i j > 0 ):
  ∃ (v : ℝ) ,
  (∃  (xx : S I) , ∀ j , wsum xx (fun i => A i j) ≥  v * wsum xx (fun i=> B i j))
  ∧ (∃ (yy : S J), ∀ i ,  wsum yy (A i) ≤  v * wsum yy (B i))
 := by {
      let n := Fintype.card I + Fintype.card J
      exact @Loomis' n I J _ _ _ _ ( by
         {
          have p1 := @Fintype.card_pos I _ _
          have p2 := @Fintype.card_pos J _ _
          linarith
        }
      ) (rfl) A B PB
  }


end Loomis




namespace zerosumFGame
open S
variable {I J : Type*} [Inhabited I] [Inhabited J] [Fintype I] [Fintype J]



#check E
#check Loomis

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
    let B := @one_matrix I J
    obtain ⟨v, ⟨xx, H1⟩ ,⟨yy, H2⟩⟩   := Loomis A B (by {
        intro _ _; simp only [one_matrix,gt_iff_lt, zero_lt_one]})
    use xx, yy, v
    constructor
    . {
      simp_rw [one_xx_eq_one,mul_one] at H1
      intro y
      rw [E,wsum_wsum_comm]
      apply (ge_iff_simplex_ge).1 H1
    }
    . {
      simp_rw [one_yy_eq_one,mul_one] at H2
      intro xx
      rw [E]
      apply (le_iff_simplex_le).1 H2
    }
}

end zerosumFGame
