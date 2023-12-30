/-
Our reference is
[LRS] Rida Laraki, Jérôme Renault, Sylvain Sorin, Mathematical Foundations of Game Theory (Universitext), 2019
-/

import Mathlib.Data.Real.EReal
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic
-- This libary proves ℝ has the the orderedtopology
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.MetricSpace.PseudoMetric


-- ℝ is not a complete lattice,
-- iSup may not exits
-- use theorems starts with ciSup etc.

import GameTheory.Simplex

open Classical

/-
We use S to denote a mixed stratage
-/
@[simp]
def Interval := { t: ℝ // 0 ≤ t ∧ t ≤ 1 }

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

lemma lam.aux_gt_iff_gt (A : I→ J →  ℝ ) (c:ℝ) (x: S I):
 lam.aux A x > c ↔ (∀ j,    wsum x (fun i => A i j ) > c)
:= by simp [lam.aux,Finset.lt_inf_iff]


lemma lam.aux.continouse (A : I →J → ℝ ) : Continuous (lam.aux A) := by {
  let fj := fun j x => wsum x (fun i => A i j)
  --have H1: ∀ j∈ Finset.univ , Continuous ((fun j x => wsum x (fun i => A i j))fj j) := by sorry
  have H1: ∀ j∈ Finset.univ , Continuous (fj j) := by simp [wsum_isContinous]
  exact Continuous.finset_inf'_apply (Inhabited.toFinsetNonempty J) H1
}

#check Continuous.finset_inf'_apply
#check Continuous.finset_inf'

lemma lam.aux.bddAbove (A : I →J → ℝ ) : ∃ C, ∀ x , lam.aux A x ≤ C := by {
  have NEI : Finset.Nonempty (Finset.univ : Finset I) := Inhabited.toFinsetNonempty I
  have NEJ : Finset.Nonempty (Finset.univ : Finset J) := Inhabited.toFinsetNonempty J
  let fi := fun i => Finset.sup'  Finset.univ NEJ (A i)
  let C0 := Finset.sup' Finset.univ NEI fi
  have Aij : ∀ i j,  A i j ≤ C0 := by {
    intro i j
    calc
    _ ≤ Finset.sup'  Finset.univ NEJ (A i) :=  Finset.le_sup' _ (Finset.mem_univ _)
    _ ≤ C0 := Finset.le_sup' fi (Finset.mem_univ _)
  }
  use C0 --* Fintype.card J
  intro x
  simp only [aux, ge_iff_le, Finset.mem_univ, Finset.inf'_le_iff,true_and]
  use default
  calc
    _ ≤ wsum x fun _ => C0 := by apply wsum_le_of_le (fun a => Aij a default)
    _ = C0 := wsum_const _ _
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


lemma wsum_comb_eq_comb_wsum (f : I → ℝ) (x y: S I) : ∀ t : Interval, wsum (linear_comb t x y) f = t.val * (wsum x f) + (1-t.val)*(wsum y f) := by {
  intro a
  simp [wsum,linear_comb,add_mul,Finset.sum_add_distrib,Finset.mul_sum,mul_assoc]
}

--lemma


lemma linear_comb_gt_left {x y: ℝ}  (H : x < y ) {t : Interval} : t.val <1 → t.val * x + (1-t.val) *y > x:= by {
  intro Ht
  have P1:(1-t.val)>0 := by linarith
  calc
    _ =  x + (1-t.val)*(y-x) := by ring
    _ > x :=by {
      have : (1-t.val) * (y-x) >0 :=by {
        have P2: (y-x) >0 := by linarith
        calc
          _ > _ :=  mul_lt_mul_of_pos_left P2 P1
          _ = 0 := by simp
      }
      linarith
    }
}

lemma linear_comb_gt_right {x y: ℝ} (H : x > y ) {t: Interval} : t.val > 0 → t.val * x + (1-t.val) *y > y:= by {
  intro Ht
  have := @linear_comb_gt_left y x (gt_iff_lt.1 H) ⟨1-t.val,by {
   constructor; repeat simp [t.prop] }⟩ (by { dsimp; linarith })
  calc
  _ = (1-t.val) * y + (1-(1-t.val)) * x := by ring
  _ > _ := this
}

lemma linear_comb_gt_of_ge_gt (x y: ℝ ) (c:ℝ) (H1 : x ≥ c ) (H2 : y >c)  (t : Interval) : t.val <1 → t.val * x + (1-t.val) *y > c:= by {
  intro Ht
  have V1: 0 ≤ x - c := by linarith
  calc
  _ ≥ t.val * c + (1-t.val) * y := by {
    rw [ge_iff_le,<-le_neg_add_iff_le]
    calc
    _ ≤ t.val * (x-c) := by {exact mul_nonneg_iff.2 (Or.inl ⟨t.prop.1,V1⟩)
    }
    _ = _ := by ring }
  _ > c := linear_comb_gt_left H2 Ht
}


lemma ContinuousAt_gt_of_gt_nbh {f : ℝ → ℝ} {c:ℝ} (H1: f x > c) (H2: ContinuousAt f x) {l :ℝ} (H3 : l < x): ∃ t, l < t ∧ t < x ∧ f t >c :=
by {
  let A := Set.Ioi c
  have nbhA: A ∈ nhds (f x):= Ioi_mem_nhds (by linarith)
  have Cfx:= (continuousAt_def.1 H2) A nbhA
  have N1 := exists_Ioc_subset_of_mem_nhds' Cfx (H3)
  obtain ⟨a,hl1,hl2⟩ := N1
  rw [Set.mem_Ico] at hl1
  let t := (a+x)/2
  use t
  exact ⟨by simp only [lt_div_iff]; linarith, by {
    simp only [gt_iff_lt, zero_lt_two, div_lt_iff]
    linarith
  },
    by {
       have Ht1: t ∈ Set.Ioc a x:= by {
          simp only [Set.mem_Ioc]
          exact ⟨by linarith,by linarith ⟩
       }
       have Ht2: t ∈ f ⁻¹' A :=  Set.mem_of_subset_of_mem hl2 Ht1
       simp only [Set.mem_preimage, Set.mem_Ioi] at Ht2
       exact gt_iff_lt.2 Ht2
    }
  ⟩
}

lemma linear_comb_gt_of_gt_nbh' (x y: ℝ ) (c:ℝ) (H : x > c ) : ∃ (t : Interval),  0 < t.val ∧ t.val <1 ∧  t.val * x + (1-t.val) *y > c:= by {
  let f := fun s => s*x +(1-s)*y
  have Hfx : f 1 = x := by ring
  have Hfx' : f 1 > c := by linarith
  have Cf : Continuous f := by continuity
  have Cfx : ContinuousAt f 1 := Continuous.continuousAt Cf
  obtain ⟨a,ha1,ha2,ha3⟩ := ContinuousAt_gt_of_gt_nbh Hfx' Cfx (by linarith : (0:ℝ)<1)
  use ⟨a,by linarith,by linarith⟩
}


lemma wsum_linear_comb_gt_of_ge_gt (f : I → ℝ) (x y: S I) (c : ℝ) (H1 : wsum x f ≥ c ) (H2 : wsum y f > c) (t : Interval) : t.val <1 → wsum (linear_comb t x y) f > c := by {
  intro Ht; rw [wsum_comb_eq_comb_wsum]
  exact linear_comb_gt_of_ge_gt _ _ c H1 H2 _ Ht
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
              -- use continuous_iff_continuousAt
              -- use ContinuousAt.tendsto
              have HJ0:∃ (t : { t:ℝ // 0 ≤ t ∧ t ≤ 1 }), 0< t.val ∧  t.val < 1 ∧ wsum (linear_comb t xx xx') (fun i => A i j0 ) > lam0 A
                := by {
                  simp only [wsum_comb_eq_comb_wsum _ xx xx']
                  apply linear_comb_gt_of_gt_nbh' _ _ _ HJ
                }
              have HJ2: ∀  j:J , j≠ j0 → ∀ (t : { t:ℝ // 0 ≤ t ∧ t ≤ 1}), t.val < 1 →  wsum (linear_comb t xx xx') (fun i => A i j ) > lam0 A
                := by {
                   intro j Hj t Ht
                   apply wsum_linear_comb_gt_of_ge_gt
                   . exact (Hxx j)
                   . {
                    calc
                    _ ≥ lam0 A' := Hxx' ⟨j, Hj⟩
                    _ > lam0 A := by linarith
                   }
                   . exact Ht
                }
              obtain ⟨t0, HtJ0⟩ := HJ0
              use t0
              rw [lam.aux_gt_iff_gt]
              intro j
              by_cases Hj : j=j0
              .  simp [Hj,HtJ0]
              .  exact HJ2 j Hj t0 (HtJ0.2.1)
            }
            obtain ⟨t, Hst⟩ := prop_st
            have prop_iSup : ∀ x: S I, lam.aux A x ≤ lam0 A := lam.aux.le_lam0 A
            have := prop_iSup (linear_comb t xx xx')
            linarith
          }
          . {
            -- The proof is similar to the above
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


-- The following is a version of von Neumann's minimax theorem
-- stated as Theorem 2.3.1 in [LRS]
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
