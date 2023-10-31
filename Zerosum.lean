import Mathlib.Data.Real.EReal
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.MetricSpace.Basic

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

section S
variable (α : Type*) [Fintype α]

def S := { x : α→ NNReal // Finset.sum Finset.univ x = 1}

instance coe_fun : CoeFun (S α) fun _ => α → NNReal :=
  ⟨fun x => (x.val : α → NNReal)⟩

lemma sum_one (x : S α) : Finset.sum Finset.univ x = 1
:= x.prop

lemma exists_nonzero {α : Type* } [Fintype α]  (x: S α) : ∃ i, x i > 0 := by {
  by_contra h
  simp only [gt_iff_lt, not_exists, not_lt, nonpos_iff_eq_zero] at h
  have : Finset.sum Finset.univ x = 0 := by {
    apply Finset.sum_eq_zero
    intros i _
    exact h i
  }
  rw  [sum_one α x] at this
  exact one_ne_zero this
}

@[simp]
noncomputable def pure (i : α) : S α  := ⟨ fun j => if i=j then 1 else 0,
 by {simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]}⟩

--weighted sum
noncomputable def wsum {α : Type*} [Fintype α] (x : S α) (f : α → ℝ ) := Finset.sum Finset.univ (fun i:α => (x i) * (f i))

lemma sum_pos {α : Type*} [Fintype α] {x : S α} {f : α → ℝ } (H : ∀ i, f i >0) : wsum x f > 0:= by {
  -- q: what is sum_pos
  have h' : ∀ i, (x i : ℝ) * (f i : ℝ) ≥  0 := by
    { intro i; exact mul_pos (H i) ((x i).2) };
    rw [NNReal.coe_pos] at h';
    exact NNReal.sum_pos (by simp [h'])
}

def linear_comb {α : outParam Type*} [Fintype α] (t: {t : NNReal // t≤ 1}) (a : S α) (b : S α) : S α :=
  ⟨ fun i => ⟨t * a i + (1-t) * (b i), (by
  {apply add_nonneg; apply mul_nonneg; simp[NNReal.coe_nat_cast]; simp[NNReal.coe_nat_cast]; apply mul_nonneg; exact nnreal.sub_le_iff_le_add.mp; simp[NNReal.coe_nat_cast] })⟩,
    by {
      apply add_nonneg;
    }
  ⟩


instance metricS {α : Type*} [Fintype α] : MetricSpace (S α) := MetricSpace.induced (fun x => x.val)
   (by {rw [Function.Injective]; exact fun a1 a2 h1 => Subtype.ext_iff.2 h1})
   (metricSpacePi)

instance Simplex_compact {α : Type*} [Fintype α] [Inhabited α]: CompactSpace (S α) := by sorry
-- Use Metric.compactSpace_iff_isBounded_univ

#check Metric.compactSpace_iff_isBounded_univ


-- Use IsCompact.exists_sSup_image_eq_and_ge

end S

namespace zerosumFGame

variable {I J : Type*}  [Inhabited I] [Inhabited J] [Fintype I] [Fintype J]
variable (A : I → J → ℝ )



def sumxC (j:J) (x : S I) (C : I →J → ℝ ) := Finset.sum Finset.univ (fun i : I => (x i) *( C i j))

def sumyC (i:I) (y : S J) (C : I →J → ℝ ) := Finset.sum  Finset.univ (fun j : J=> (y j) * ( C i j))



lemma sum_pure [Fintype I] {f: I→ℝ} {a:I} :
  Finset.sum Finset.univ (fun i => (pure I a i) * f i) = f a :=
  by {
    have : f a= (pure I a a).toReal * f a := by simp [_root_.pure,ite_true, ENNReal.one_toReal, one_mul]
    rw [this]
    apply Finset.sum_eq_single --_ I _ Finset.univ _ a (sorry) (sorry)
    . {
      intro b _ h3
      simp only [_root_.pure, mul_eq_zero, NNReal.coe_eq_zero, ite_eq_right_iff, one_ne_zero]
      exact Or.inl (fun x => h3 (symm x))
    }
    . {
    intro h1
    exfalso; simp only [Finset.mem_univ, not_true] at h1
    }
  }


lemma simplex_ge_iff_vertex_ge [Fintype I] {f : I → ℝ } {v : ℝ} :
   (∀ x : S I,   Finset.sum Finset.univ (fun i : I => (x i).toReal * f i)≥ v)
    ↔ (∀ i : I, f i ≥ v):= by {
  constructor
  . {
    intro H i
    have := H (pure I i)
    rw [sum_pure] at this
    exact this
  }
  . {
    intro H x
    simp only [ge_iff_le]
    calc
      v = Finset.sum Finset.univ (fun i : I => (x i).toReal * v) := by {
        rw [<-Finset.sum_mul]
        norm_cast; rw [sum_one]
        norm_cast; rw [one_mul]
      }
      _ ≤ Finset.sum Finset.univ (fun i : I => (x i).toReal * f i) :=
      Finset.sum_le_sum (by {
        intro i
        simp only [Finset.mem_univ, gt_iff_lt, forall_true_left]
        rw [<-sub_nonneg,<-mul_sub]
        exact mul_nonneg (NNReal.zero_le_coe) (sub_nonneg.2 (H i))
      })
  }
 }



-- expactation of the payoff of a mixed stratage
noncomputable def E (A : I →J →ℝ) (x : S I) (y : S J) : ℝ := wsum x (fun i => wsum y (A i))

-- One may need Finset.sum_comm' Finset.sum_mul

-- lemma E_eq1

/-
lemma E_eq1 {x : PMF I} {y : PMF J} : Finset.sum (@Finset.univ _ A.FI)
( fun (i : I ) => Finset.sum (@Finset.univ _ A.FJ) (fun (j : J) => (x i).toReal * (A i j) * ((y j).toReal) )) = Finset.sum (@Finset.univ _ A.FI)
( fun (i : I ) =>(x i).toReal * Finset.sum (@Finset.univ _ A.FJ) (fun (j : J) => (A i j) * ((y j).toReal) )) := by {
  sorry
}
-/

-- invoke exterem value theorem is_compact.exists_forall_le


-- def lam0

end zerosumFGame

section Loomis

variable (n : ℕ) {I J: Type*} [Inhabited I] [Inhabited J] [Fintype I] [Fintype J]

lemma nonempty (α : Type*) [Inhabited α] [Fintype α ]: Finset.Nonempty (@Finset.univ α  _)  := by {
  use Inhabited.default
  simp only [Finset.mem_univ]
}


noncomputable def lam.aux (A B : I →J → ℝ ) (x : S I) :=
  Finset.inf' Finset.univ (nonempty J) (fun j =>
   wsum x (fun i => A i j ) / wsum x (fun i => B i j))

noncomputable def lam0 (A B : I →J → ℝ ):=  iSup (lam.aux A B)


noncomputable def mu.aux (A B : I →J → ℝ ) (y : S J) :=  Finset.sup' Finset.univ (nonempty  I) (fun i => wsum y (fun j => A i j ) / wsum y (fun j => B i j) )

noncomputable def mu0 (A B : I →J → ℝ ):=  iInf (mu.aux A B)

lemma exits_xx_lam0 (A B : I →J → ℝ ) (PB : ∀ i:I, ∀ j:J,  B i j > 0 ) : ∃ (xx : S I), ∀ j, (wsum xx (fun i => A i j)) / (wsum xx (fun i => B i j))≥  lam0 A B  := by sorry


lemma exits_xx_lam0' (A B : I →J → ℝ ) (PB : ∀ i:I, ∀ j:J,  B i j > 0 ) : ∃ (xx : S I), ∀ j, (wsum xx (fun i => A i j))≥  lam0 A B *  (wsum xx (fun i => B i j)) := by sorry

lemma exits_yy_mu0 (A B : I →J → ℝ ) (PB : ∀ i:I, ∀ j:J,  B i j > 0 ) : ∃ (yy : S J), ∀ i, (wsum yy (A i)) / (wsum yy (B i))≤  mu0 A B  := by sorry

lemma exits_yy_mu0' (A B : I →J → ℝ ) (PB : ∀ i:I, ∀ j:J,  B i j > 0 ) : ∃ (yy : S J), ∀ i, (wsum yy (A i)) ≤  mu0 A B * (wsum yy (B i)) := by sorry


lemma lam0_le_mu0 (A B : I →J → ℝ ) (PB : ∀ i:I, ∀ j:J,  B i j > 0 ) :
  lam0 A B ≤ mu0 A B := by sorry


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
          use pure I i0
          intro j
          have HJ := hj0 j
          simp_rw [wsum, HJ, UI,Finset.sum_singleton, _root_.pure, ite_true, NNReal.coe_one, one_mul, ge_iff_le]
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
        by_cases  HH : lam0 A B = mu0 A B
        . {
          use (lam0 A B)
          exact ⟨exits_xx_lam0' A B PB, by {rw [HH]; exact exits_yy_mu0' A B PB}⟩
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
            have prop_st :∃ t : {t: NNReal // t≤1},  lam.aux A B (linear_comb t xx xx') > lam0 A B := by sorry
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



/-

section minmax
theorem minmax_theorem : ∃ (xx : S I) (yy : S J) (v : ℝ), (∀ (y : S J), E A xx y ≥ v ) ∧ (∀ (x : S I), E A x yy ≤ v)  := by {
  let B : I → J → ℝ  := fun i => fun j => 1
  obtain ⟨xx, yy, v, H1, H2⟩ := Loomis A B (by {intro i j; simp only [gt_iff_lt, zero_lt_one]})
  use xx,  yy, v
  constructor
  . {
    -- rw [E_eq1]
    -- rw [simplex_ge_iff_vertex_ge]
    sorry
  }
  . {
    --rw [E_eq1]
  sorry
  }

}

end minmax

-/
