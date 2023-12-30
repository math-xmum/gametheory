import Mathlib.Data.Real.EReal
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Topology.Separation
import Mathlib.Data.Finset.Lattice
import Mathlib.Topology.Algebra.Order.Compact

open Classical

/-
We use S to denote a mixed stratage
-/

variable (α : Type*) [Fintype α]

def S := { x : α→ ℝ // (∀ i:α, 0 ≤ x i)  ∧  Finset.sum Finset.univ x = 1}
def S'' := {x :α → ℝ  | (∀ i:α, 0 ≤ x i)  ∧  (Finset.sum (Finset.univ) x = 1)}

namespace S

variable {α : Type*} [Fintype α]

lemma subset_subtype: S α =  ↑(S'' α):= rfl

instance coe_fun : CoeFun (S α) fun _ => α → ℝ :=
  ⟨fun x => (x.val : α → ℝ )⟩

lemma non_neg {i : α } {x : S α} : 0 ≤  x i := x.prop.1 i

lemma sum_one (x : S α) : Finset.sum Finset.univ x = 1
:= x.prop.2

lemma exists_nonzero {α : Type* } [Fintype α]  (x: S α) : ∃ i, x i > 0 := by {
  by_contra h
  simp only [gt_iff_lt, not_exists, not_lt, nonpos_iff_eq_zero] at h
  have : Finset.sum Finset.univ x = 0 := by {
    apply Finset.sum_eq_zero
    intros i _
    have : 0 ≤ x i  := by apply non_neg
    have : x i ≤ 0 := h i
    linarith
  }
  simp only  [sum_one,one_ne_zero] at this
}


@[simp]
noncomputable def pure (i : α) : S α  := ⟨fun j => if i=j then 1 else 0,
 by {
  constructor
  . {
    intro j
    by_cases H: i=j
    repeat simp [H]
  }
  . simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  }⟩

noncomputable instance SInhabited_of_Inhabited {α : Type*} [Fintype α] [Inhabited α]: Inhabited (S α) where
  default := pure (default : α)


noncomputable instance SNonempty_of_Inhabited {α : Type*} [Fintype α] [Inhabited α]: Nonempty (S α) := Nonempty.intro (default : S α)

lemma pure_eq_one {a b : α}: a = b → pure a b = 1 := by {
  intro h
  simp [pure, ite_eq_left_iff, zero_ne_one,h]
}

lemma pure_eq_zero {a b : α}: a ≠ b → pure a b = 0 := by {
  intro h
  simp [pure, ite_eq_right_iff,h]
}

noncomputable def wsum {α : Type*} [Fintype α] (x : S α) (f : α → ℝ ) := Finset.sum Finset.univ (fun i:α => (x i) * (f i))

lemma wsum_pos {α : Type*} [Fintype α] {x : S α} {f : α → ℝ } (H : ∀ i, f i >0) : wsum x f > 0:= by {
  have h' : ∀ i, (x i : ℝ) * (f i : ℝ) ≥  0 := by{
    intro i ; exact mul_nonneg (by simp [S.non_neg]) (le_of_lt (H i))
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

def linear_comb {α : outParam Type*} [Fintype α] (t: {t :ℝ // 0≤ t ∧  t≤ 1}) (a : S α) (b : S α) : S α := ⟨fun i => (t * (a i) + (1-t) * (b i)), by {
  constructor
  . {
    intro i
    apply add_nonneg; apply mul_nonneg
    simp [t.prop.1]
    simp [S.non_neg]
    apply mul_nonneg
    simp [t.prop.2]
    simp [S.non_neg]
  }
  . {
      let f : α → ℝ := fun i => (t :ℝ) * (a i :ℝ)
      have sumf : Finset.sum Finset.univ f = t := by {
        rw [<-Finset.mul_sum]
        simp [S.sum_one]
      }
      let g : α → Real  := fun i => (1 -(t: ℝ)) * (b i :ℝ)
      have sumg : Finset.sum Finset.univ g = 1-t := by {
        rw [<-Finset.mul_sum]
        simp [S.sum_one]
      }
      have fg_eq :  (fun i : α  =>(f i + g i) )= fun i => t * a i + (1 -(t: ℝ)) * (b i :ℝ) := by dsimp
      rw [<-fg_eq]
      rw [Finset.sum_add_distrib]
      rw [sumf,sumg]
      simp only [add_sub_cancel'_right]
    }}⟩


instance metricS : MetricSpace (S α) := MetricSpace.induced (fun x => x.val)
   (by {rw [Function.Injective]; exact fun a1 a2 h1 => Subtype.ext_iff.2 h1})
   (metricSpacePi)

lemma projection_isContinuous {i: α} : Continuous (fun (x: S α ) => (x i :ℝ)) := by {
  let proj := fun y : α → ℝ => y i
  have Cproj : Continuous proj := by continuity
  let inc := fun x : S α => x.val
  have Cinc : Continuous inc := by continuity
  have : (fun (x: S α ) => (x i :ℝ))  = proj ∘ inc := by ext; simp
  exact Continuous.comp Cproj Cinc
}

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
  apply x_ge_zero
  exact hx
}


lemma SisClosed :IsClosed (S'' α):= by {
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

instance SisCompactSpace [Inhabited α]: CompactSpace (S α) := by {
  simp only [subset_subtype]
  rw [<-isCompact_iff_compactSpace]
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨SisClosed, Simplex.isBounded⟩
}



end S


lemma Inhabited.toFinsetNonempty (α : Type*) [Inhabited α] [Fintype α ]: Finset.Nonempty (@Finset.univ α  _)  := by {
  use Inhabited.default
  simp only [Finset.mem_univ]
}

namespace S
variable {I: Type*} [Fintype I]


lemma sum_pure [Fintype I] {f: I→ℝ} {a:I} :
  Finset.sum Finset.univ (fun i => (S.pure a i) * f i) = f a :=
  by {
    have : f a= (S.pure a a) * f a := by simp [ite_true, ENNReal.one_toReal, one_mul]
    rw [this]
    apply Finset.sum_eq_single
    . {
      intro b _ h3
      simp only [S.pure, ite_mul, one_mul, zero_mul, ite_eq_right_iff,S.pure_eq_zero (Ne.symm h3)]
      simp only [Ne.symm h3, IsEmpty.forall_iff]
    }
    . {
    intro h1
    exfalso; simp only [Finset.mem_univ, not_true] at h1
    }
  }

--lemma wsum_pure [Fintype I] {f: I→ℝ} {a:I} :
--  wsum (S.pure a) f = f a := by rw [wsum,sum_pure]


lemma wsum_pure [Fintype I] (f: I→ℝ) (a:I) :
  wsum (S.pure a) f = f a := by rw [wsum,sum_pure]


lemma wsum_const [Fintype I] (b:ℝ) :
  ∀ x: S I, wsum x (fun _ => b) = b :=
    by intro x; simp [wsum,<-Finset.sum_mul,sum_one]

lemma wsum_congr (h : ∀ (i : I), f i = g i) : ∀ x, wsum x f = wsum x g := by intro x ;simp [wsum,h]

lemma wsum_const' [Fintype I] {b:ℝ}  {f: I→ℝ} (H: ∀ a:I, f a = b) :
  ∀ x: S I, wsum x f = b :=
    by intro x; simp [wsum,H,<-Finset.sum_mul,sum_one]


lemma wsum_le_of_le [Fintype I]  {f g: I→ℝ} (H: ∀ (a:I), (f a) ≤ g a) : ∀ x: S I, (wsum x f) ≤ (wsum x g)  := by {
  intro x
  have : ∀ i∈ Finset.univ, x i * f i ≤ x i * g i := fun i _ =>
    mul_le_mul_of_nonneg_left (H i) (non_neg)
  simp [wsum,Finset.sum_le_sum this]
}

lemma wsum_isContinous [Fintype I] {f: I→ℝ} : Continuous (fun x : S I => wsum x f) :=
 continuous_finset_sum _ (fun _ _ => (Continuous.mul (projection_isContinuous) (continuous_const)))


lemma ge_iff_simplex_ge {f : I → ℝ} {v : ℝ}: (∀ i:I , f i ≥ v) ↔ ∀ x : S I, (wsum x f) ≥ v := by {
  constructor
  . {
    intro hi x
    rw [wsum,ge_iff_le]
    calc
      v = Finset.sum Finset.univ fun i => x i * v := by {
        simp only [<-Finset.sum_mul]
        norm_cast
        simp only [S.sum_one, NNReal.coe_one, one_mul]
      }
      _ ≤ _ := by {
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left (ge_iff_le.1 (hi i)) (non_neg)
      }
  }
  . {
    intro HI i
    have := HI (pure i)
    rw [wsum_pure] at this
    exact this
  }
}


lemma le_iff_simplex_le {f : I → ℝ} {v : ℝ}: (∀ i:I , f i ≤  v) ↔ ∀ x : S I, (wsum x f) ≤  v := by {
  constructor
  . {
    intro hi x
    rw [wsum,<-ge_iff_le]
    calc
      v = Finset.sum Finset.univ fun i => x i * v := by {
        simp only [<-Finset.sum_mul]
        norm_cast
        simp only [S.sum_one, NNReal.coe_one, one_mul]
      }
      _ ≥   _ := by {
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left (ge_iff_le.1 (hi i)) (non_neg)
      }
  }
  . {
    intro HI i
    have := HI (pure i)
    rw [wsum_pure] at this
    exact this
  }
}


variable [Inhabited I]


lemma fintypenonempty (α : Type*) [Inhabited α] [Fintype α ]: Finset.Nonempty (@Finset.univ α  _)  := by {
  use Inhabited.default
  simp only [Finset.mem_univ]
}


-- The following lemmas compare sup on i and weighted sum sup

lemma Finset.exists_sup'_image' (f : I → ℝ) (H: Finset.Nonempty s) : ∃ i∈ s,
(Finset.sup' s H f = f i ∧ ∀ j ∈ s, f j ≤ f i)  := by {
  obtain ⟨i,Hi⟩ := Finset.exists_max_image s f H
  use i
  exact  ⟨Hi.1,
  ⟨by {
      apply le_antisymm
      . apply Finset.sup'_le H f Hi.2
      . apply Finset.le_sup' f Hi.1 },
    Hi.2 ⟩ ⟩
}

lemma Finset.exists_sup'_image (f : I → ℝ) (H: Finset.Nonempty s) : ∃ i∈ s,
Finset.sup' s H f = f i   := by {
  obtain ⟨i,Hi⟩ := Finset.exists_sup'_image' f H
  use i
  exact ⟨Hi.1,Hi.2.1⟩
}

lemma sup_eq_wsum_sup {f : I → ℝ} {v : ℝ}: Finset.sup' Finset.univ (Inhabited.toFinsetNonempty I) f = iSup (fun (x: S I) => wsum x f) := by {
  have non_empty:=Inhabited.toFinsetNonempty I
  obtain ⟨i,⟨_,Hi2,Hi3⟩⟩ := Finset.exists_sup'_image' f non_empty
  rw [Hi2]
  have Hi3 : ∀ j:I, f j≤ f i := by simp [Hi3]
  have Hi3' := le_iff_simplex_le.1 Hi3
  apply le_antisymm
  . {
    have wsum_fi := wsum_pure f i
    rw [<-wsum_fi]
    have H : BddAbove (Set.range (fun x => wsum x f)):= by {
      rw [<-wsum_fi] at Hi3'
      apply bddAbove_def.2 ⟨wsum (pure i) f, by {
        intro y hy
        obtain ⟨j, hj⟩ := Set.mem_range.1 hy
        simp only [<-hj,Hi3']
      }⟩
    }
    apply le_ciSup H
  }
  . exact ciSup_le Hi3'
}


-- lemma inf_eq_wsum_inf {f : I → ℝ} {v : ℝ}: Finset.inf' Finset.univ (Inhabited.toFinsetNonempty I) f = iInf (fun (x: S I) => wsum x f) := by {
--   sorry
-- }


end S
