import Mathlib.Data.Real.EReal
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Topology.Separation

open Classical

/-
We use S to denote a mixed stratage
-/

section S
variable (α : Type*) [Fintype α]

def S := { x : α→ NNReal // Finset.sum Finset.univ x = 1}

instance S.coe_fun : CoeFun (S α) fun _ => α → NNReal :=
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
  have h' : ∀ i, (x i : ℝ) * (f i : ℝ) ≥  0 := by{
    intro i ; exact mul_nonneg (NNReal.zero_le_coe) (le_of_lt (H i))
  }
  simp only [wsum];
  let ⟨j, Hjj⟩ := exists_nonzero x;
  have h'' : (x j : ℝ) * (f j : ℝ) > 0 := by {exact mul_pos (Hjj) (H j)}
  have H'' : (Finset.sum (Finset.univ \ {j}) fun i => (x i) * f i) + (Finset.sum {j} fun i => (x i) * f i)
      = (Finset.sum Finset.univ fun i => (x i) * f i) := by {
    apply Finset.sum_sdiff
    simp only [Finset.subset_univ]
  }
  rw [<-H'',add_comm]
  apply add_pos_of_pos_of_nonneg
  rw [Finset.sum_singleton]
  exact h''
  apply Finset.sum_nonneg
  simp only [Finset.mem_univ, not_true, Finset.mem_sdiff, Finset.mem_singleton, true_and, gt_iff_lt,
    NNReal.coe_pos]
  intro i _
  exact h' i
}

def linear_comb {α : outParam Type*} [Fintype α] (t: {t : NNReal // t≤ 1}) (a : S α) (b : S α) : S α :=
  ⟨ fun i => ⟨t * a i + (1-t) * (b i), (by
  { apply add_nonneg; apply mul_nonneg
    simp[NNReal.coe_nat_cast]
    simp[NNReal.coe_nat_cast]
    apply mul_nonneg
    simp only [sub_nonneg]
    exact t.prop
    simp
    })⟩,
    by {
      let f : α → Real  := fun i => (t :ℝ) * (a i :ℝ)
      have sumf : Finset.sum Finset.univ f = t := by {
        rw [<-Finset.mul_sum]
        norm_cast
        simp [sum_one]
      }
      let g : α → Real  := fun i => (1 -(t: ℝ)) * (b i :ℝ)
      have sumg : Finset.sum Finset.univ g = 1-t := by {
        rw [<-Finset.mul_sum]
        norm_cast
        simp [sum_one]
      }
      ext
      rw [NNReal.coe_sum]
      simp only [NNReal.coe_mk, NNReal.coe_one]
      have fg_eq :  (fun i : α  =>(f i + g i) )= fun i => t * a i + (1 -(t: ℝ)) * (b i :ℝ) := by {
        ext
        dsimp
      }
      rw [<-fg_eq]
      rw [Finset.sum_add_distrib]
      rw [sumf,sumg]
      simp only [add_sub_cancel'_right]
    }
  ⟩


instance metricS {α : Type*} [Fintype α] : MetricSpace (S α) := MetricSpace.induced (fun x => x.val)
   (by {rw [Function.Injective]; exact fun a1 a2 h1 => Subtype.ext_iff.2 h1})
   (metricSpacePi)

-- Use Metric.compactSpace_iff_isBounded_univ

--#check Metric.compactSpace_iff_isBounded_univ


-- Use IsCompact.exists_sSup_image_eq_and_ge

end S


variable (α : Type*) [Fintype α]

def S' := { x : α→ ℝ // (∀ i:α, 0 ≤ x i)  ∧  Finset.sum Finset.univ x = 1}
def S'' := {x :α → ℝ  | (∀ i:α, 0 ≤ x i)  ∧  (Finset.sum (Finset.univ) x = 1)}

namespace S'

variable {α : Type*} [Fintype α]

lemma subset_subtype: S' α =  ↑(S'' α):= rfl

instance coe_fun : CoeFun (S' α) fun _ => α → ℝ :=
  ⟨fun x => (x.val : α → ℝ )⟩

lemma non_neg {i : α } {x : S' α} : 0 ≤  x i := x.prop.1 i

lemma sum_one (x : S' α) : Finset.sum Finset.univ x = 1
:= x.prop.2

lemma exists_nonzero {α : Type* } [Fintype α]  (x: S' α) : ∃ i, x i > 0 := by {
  by_contra h
  simp only [gt_iff_lt, not_exists, not_lt, nonpos_iff_eq_zero] at h
  have : Finset.sum Finset.univ x = 0 := by {
    apply Finset.sum_eq_zero
    intros i _
    have : 0 ≤ x i  := non_neg
    have : x i ≤ 0 := h i
    linarith
  }
  rw  [sum_one x] at this
  exact one_ne_zero this
}


--weighted sum
noncomputable def wsum {α : Type*} [Fintype α] (x : S' α) (f : α → ℝ ) := Finset.sum Finset.univ (fun i:α => (x i) * (f i))

lemma sum_pos {α : Type*} [Fintype α] {x : S' α} {f : α → ℝ } (H : ∀ i, f i >0) : wsum x f > 0:= by {
  -- q: what is sum_pos
  have h' : ∀ i, (x i : ℝ) * (f i : ℝ) ≥  0 := by{
    intro i ; exact mul_nonneg (non_neg) (le_of_lt (H i))
  }
  simp only [wsum];
  let ⟨j, Hjj⟩ := exists_nonzero x;
  have h'' : (x j : ℝ) * (f j : ℝ) > 0 := by {exact mul_pos (Hjj) (H j)}
  have H'' : (Finset.sum (Finset.univ \ {j}) fun i => (x i) * f i) + (Finset.sum {j} fun i => (x i) * f i)
      = (Finset.sum Finset.univ fun i => (x i) * f i) := by {
    apply Finset.sum_sdiff
    simp only [Finset.subset_univ]
  }
  rw [<-H'',add_comm]
  apply add_pos_of_pos_of_nonneg
  rw [Finset.sum_singleton]
  exact h''
  apply Finset.sum_nonneg
  simp only [Finset.mem_univ, not_true, Finset.mem_sdiff, Finset.mem_singleton, true_and, gt_iff_lt,
    NNReal.coe_pos]
  intro i _
  exact h' i
}

def linear_comb {α : outParam Type*} [Fintype α] (t: {t : NNReal // t≤ 1}) (a : S' α) (b : S' α) : S α :=
  ⟨ fun i => ⟨t * a i + (1-t) * (b i), (by
  { apply add_nonneg; apply mul_nonneg
    simp[non_neg]
    simp[non_neg]
    apply mul_nonneg
    simp only [sub_nonneg]
    exact t.prop
    simp [non_neg]
    })⟩,
    by {
      let f : α → Real  := fun i => (t :ℝ) * (a i :ℝ)
      have sumf : Finset.sum Finset.univ f = t := by {
        rw [<-Finset.mul_sum]
        norm_cast
        simp [sum_one]
      }
      let g : α → Real  := fun i => (1 -(t: ℝ)) * (b i :ℝ)
      have sumg : Finset.sum Finset.univ g = 1-t := by {
        rw [<-Finset.mul_sum]
        norm_cast
        simp [sum_one]
      }
      ext
      rw [NNReal.coe_sum]
      simp only [NNReal.coe_mk, NNReal.coe_one]
      have fg_eq :  (fun i : α  =>(f i + g i) )= fun i => t * a i + (1 -(t: ℝ)) * (b i :ℝ) := by {
        ext
        dsimp
      }
      rw [<-fg_eq]
      rw [Finset.sum_add_distrib]
      rw [sumf,sumg]
      simp only [add_sub_cancel'_right]
    }
  ⟩


instance metricS : MetricSpace (S' α) := MetricSpace.induced (fun x => x.val)
   (by {rw [Function.Injective]; exact fun a1 a2 h1 => Subtype.ext_iff.2 h1})
   (metricSpacePi)


instance proper_real : ProperSpace ℝ := by {
  simp [properSpace_of_locallyCompactSpace ℝ]
}

instance proper_pi : ProperSpace (α→ ℝ ) := by {
  apply pi_properSpace
}

lemma x_ge_zero {x : α → ℝ} {b : α} (h : x ∈ S'' α ) :  0 ≤  x b := by {
  rw [S'',Set.mem_setOf] at h
  exact h.1 b
}
lemma x_le_one {x : α → ℝ} {b:α} (h : x ∈ S'' α ): x b ≤ 1 := by {
  rw [S'', Set.mem_setOf] at h
  rw [<-h.2]
  apply Finset.single_le_sum (by {
    simp only [Finset.mem_univ, forall_true_left]
    exact h.1
  }) (by {
    simp only [Finset.mem_univ]
  }
  )
}

lemma Simplex.isBounded [Inhabited α] : Bornology.IsBounded (S'' α) := by {
  rw [Metric.isBounded_iff_subset_ball (fun _ => 0)]
  use (2:ℝ)
  intro x hx
  simp only [Metric.mem_ball]
  rw [dist_pi_def]
  norm_cast
  simp only [bot_eq_zero', zero_lt_two, Finset.sup_lt_iff, Finset.mem_univ, forall_true_left]
  intro b
  rw [nndist_dist, Real.dist_eq,<-NNReal.coe_lt_coe,NNReal.coe_two,Real.coe_toNNReal _ (by simp)]
  simp only [sub_zero]
  rw [abs_of_nonneg]
  have hb:= @x_le_one _ _ _ b hx
  apply lt_of_le_of_lt hb
  norm_cast
  apply x_ge_zero hx
}

lemma Simplex.isClosed :IsClosed (S'' α):= by {
  rw [<-isSeqClosed_iff_isClosed]
  rw [isSeqClosed_iff]
  apply superset_antisymm
  exact subset_seqClosure
  rw [seqClosure_eq_closure]
  intro x hx
  rw [mem_closure_iff_seq_limit] at hx
  let ⟨y,hy1,hy2⟩ := hx
  simp only [S'',Set.mem_setOf_eq]
  rw [tendsto_pi_nhds] at hy2
  constructor
  . {
    intro a
    have hy22 := hy2 a
    rw [Filter.Tendsto] at hy22
    apply ge_of_tendsto hy22
    apply Filter.eventually_of_forall
    intro i
    let ⟨h1,_⟩ := hy1 i
    exact h1 a
  }
  . {
    have h1:= tendsto_finset_sum (Finset.univ: Finset α) (fun i _ => hy2 i)
    have hy1:= fun b => (hy1 b).2
    simp only [hy1, gt_iff_lt, not_lt] at h1
    rw [tendsto_const_nhds_iff] at h1
    rw [h1]
  }
}

instance Simplex.CompactSpace' [Inhabited α]: CompactSpace (S' α) := by {
  simp only [subset_subtype]
  rw [<-isCompact_iff_compactSpace]
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨Simplex.isClosed, Simplex.isBounded⟩
}


lemma SS'_iso : S α ≃ᵢ  S' α where
  toFun := fun x => ⟨fun i => x i, ⟨fun i => (x i).prop ,(by {
    have :=x.2
    norm_cast
   })⟩⟩
  invFun := fun x => ⟨fun i => ⟨x i,x.prop.1 i⟩, (by {
    ext
    simp only [NNReal.coe_one,NNReal.coe_sum,NNReal.coe_mk,x.2.2]
    })⟩
  left_inv := by {
    intro x
    apply Subtype.coe_eta
  }
  right_inv := by {
    rw [Function.RightInverse,Function.LeftInverse]
    simp
  }
  isometry_toFun := by {
    rw [Isometry]
    simp only
    intro x1 x2
    norm_cast
  }


instance Simplex.CompactSpace [Inhabited α]: CompactSpace (S α) := by {
  have h:= Homeomorph.symm (IsometryEquiv.toHomeomorph (@SS'_iso α _))
  exact Homeomorph.compactSpace h
}

end S'
