/-
Our reference is
[LRS] Rida Laraki, Jérôme Renault, Sylvain Sorin, Mathematical Foundations of Game Theory (Universitext), 2019
-/


import Mathlib

-- ℝ is not a complete lattice,
-- iSup may not exits
-- use theorems starts with ciSup etc.

open BigOperators
open Classical
open Finset

section Simplex


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
      simp only [add_sub_cancel]
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

omit [Fintype I] in
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

omit [Fintype I] in
lemma wsum_pure [Fintype I] (f: I→ℝ) (a:I) :
  wsum (S.pure a) f = f a := by rw [wsum,sum_pure]

omit [Fintype I] in
lemma wsum_const [Fintype I] (b:ℝ) :
  ∀ x: S I, wsum x (fun _ => b) = b :=
    by intro x; simp [wsum,<-Finset.sum_mul,sum_one]

lemma wsum_congr (h : ∀ (i : I), f i = g i) : ∀ x, wsum x f = wsum x g := by intro x ;simp [wsum,h]

omit [Fintype I] in
lemma wsum_const' [Fintype I] {b:ℝ}  {f: I→ℝ} (H: ∀ a:I, f a = b) :
  ∀ x: S I, wsum x f = b :=
    by intro x; simp [wsum,H,<-Finset.sum_mul,sum_one]

omit [Fintype I] in
lemma wsum_le_of_le [Fintype I]  {f g: I→ℝ} (H: ∀ (a:I), (f a) ≤ g a) : ∀ x: S I, (wsum x f) ≤ (wsum x g)  := by {
  intro x
  have : ∀ i∈ Finset.univ, x i * f i ≤ x i * g i := fun i _ =>
    mul_le_mul_of_nonneg_left (H i) (non_neg)
  simp [wsum,Finset.sum_le_sum this]
}

omit [Fintype I] in
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

omit [Fintype I] [Inhabited I] in
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


end Simplex


namespace zerosum
/-
We use S to denote a mixed stratage
-/
@[simp]
def Interval := { t: ℝ // 0 ≤ t ∧ t ≤ 1 }

variable {I J : Type*}

@[ext]
structure zerosumGame (I J : Type*) where
  g : I → J → ℝ
  HI : Inhabited I
  HJ : Inhabited J

instance : CoeFun (zerosumGame I J) (fun _ => I →  J → ℝ ) where
  coe := zerosumGame.g

attribute [coe] zerosumGame.g


namespace zerosumGame
variable (A : zerosumGame I J)

noncomputable def maxmin : EReal := iSup (fun (i:I) => iInf (fun  (j: J) => ((A i j ):EReal)))

noncomputable def minmax : EReal := iInf (fun (j:J) => iSup (fun  (i: I) => ((A i j):EReal)))


lemma maxmin_le_minmax : maxmin A ≤ minmax A := by
  have H1 : ∀ j i,  iInf (fun (j :J) => (A i j:EReal)) ≤ (A i j:EReal):= by
    intro j i
    simp [iInf_le]
  rw [minmax,maxmin]
  have H2 : ∀ j, iSup (fun (i:I) => iInf (fun (j:J) => (A i j:EReal)) )
    ≤ iSup (fun (i:I) => (A i j:EReal)) := by
    intro j
    apply iSup_mono
    exact H1 j
  exact le_iInf H2


def guarantees1 (w : ℝ) := ∃ i: I, ∀ j : J , (A i j) ≥ w

def guarantees2 (w : ℝ) := ∃ j: J, ∀ i : I , (A i j) ≤ w


end zerosumGame



namespace zerosumFGame

open S

variable [Inhabited I] [Inhabited J] [Fintype I] [Fintype J]
variable (A : I → J → ℝ )



def sumxC (j:J) (x : S I) (C : I →J → ℝ ) := Finset.sum Finset.univ (fun i : I => (x i) *( C i j))

def sumyC (i:I) (y : S J) (C : I →J → ℝ ) := Finset.sum  Finset.univ (fun j : J=> (y j) * ( C i j))




noncomputable def E (A : I → J → ℝ) (x : S I) (y : S J) : ℝ := wsum x (fun i => wsum y (A i))

end zerosumFGame

section Loomis
open S
open zerosumFGame

variable  [Inhabited I] [Inhabited J] [Fintype I] [Fintype J]


noncomputable def lam.aux (A: I →J → ℝ ) (x : S I) :=
  Finset.inf' Finset.univ (Inhabited.toFinsetNonempty J) (fun j =>
   wsum x (fun i => A i j ))

noncomputable def mu.aux (A : I →J → ℝ ) (y : S J) :=
  Finset.sup' Finset.univ (Inhabited.toFinsetNonempty I) (fun i =>
    wsum y (fun j => A i j ))


noncomputable def lam0 (A : I →J → ℝ ):=  iSup (lam.aux A )

omit [Inhabited I] in
lemma lam.aux_gt_iff_gt (A : I→ J →  ℝ ) (c:ℝ) (x: S I):
 lam.aux A x > c ↔ (∀ j,    wsum x (fun i => A i j ) > c)
:= by simp [lam.aux,Finset.lt_inf_iff]

omit [Inhabited J] in
lemma mu.aux_lt_iff_lt (A : I→ J →  ℝ ) (c:ℝ) (y: S J):
 mu.aux A y < c ↔ (∀ i,    wsum y (fun j => A i j ) < c)
:= by simp [mu.aux, Finset.inf'_lt_iff]

omit [Inhabited I] in
lemma lam.aux.continouse (A : I →J → ℝ ) : Continuous (lam.aux A) := by {
  let fj := fun j x => wsum x (fun i => A i j)
  have H1: ∀ j∈ Finset.univ , Continuous (fj j) := by simp [fj,wsum_isContinous]
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
   ∃ (xx : S I), ∀ j, (wsum xx (fun i => A i j)) ≥  lam0 A := by
    have hs : IsCompact (Set.univ : Set (S I)) := isCompact_univ
    have clam.aux : ContinuousOn (lam.aux A) (Set.univ)
      := continuous_iff_continuousOn_univ.1 (lam.aux.continouse A)
    obtain ⟨xx,_,Hxx⟩ := IsCompact.exists_isMaxOn (hs) (by simp [SNonempty_of_Inhabited]) (clam.aux)
    rw [isMaxOn_iff] at Hxx
    use xx
    intro j
    calc
      lam0 A ≤ lam.aux A xx:= by
        simp only [Set.mem_univ, forall_true_left] at Hxx
        simp [lam0, ciSup_le Hxx]
      _ ≤ _ :=by  rw [lam.aux]; apply Finset.inf'_le _ (by simp)




noncomputable def mu0 (A : I →J → ℝ ):=  iInf (mu.aux A )

lemma mu.aux.continouse (A : I →J → ℝ ) : Continuous (mu.aux A) := by {
  -- the proof is the same as that of lam
  let fi := fun i x => wsum x (fun j => A i j)
  have H1: ∀ i∈ Finset.univ , Continuous (fi i) := by simp [fi,wsum_isContinous]
  exact Continuous.finset_sup'_apply (Inhabited.toFinsetNonempty I) H1
}

-- use IsCompact.exists_isMaxOn

--
lemma wsum_le_of_le [Fintype I]  {f g: I→ℝ} (H: ∀ (a:I), (f a) ≤ g a) : ∀ x: S I, (wsum x f) ≤ (wsum x g)  := by
  intro x
  have : ∀ i∈ Finset.univ, x i * f i ≤ x i * g i := fun i _ =>
    mul_le_mul_of_nonneg_left (H i) (non_neg)
  simp [wsum,Finset.sum_le_sum this]

lemma wsum_ge_of_ge [Fintype I]  {f g: I→ℝ} (H: ∀ (a:I), (f a) ≥ g a) : ∀ x: S I, (wsum x f) ≥ (wsum x g)  := by
  intro x
  have : ∀ i∈ Finset.univ, x i * f i ≥ x i * g i := fun i _ =>
    mul_le_mul_of_nonneg_left (H i) (non_neg)
  simp [wsum,Finset.sum_le_sum this]

lemma mu.aux.bddBelow (A : I →J → ℝ ) : ∃ C, ∀ y , mu.aux A y ≥ C := by
  have NEI : Finset.Nonempty (Finset.univ : Finset I) := Inhabited.toFinsetNonempty I
  have NEJ : Finset.Nonempty (Finset.univ : Finset J) := Inhabited.toFinsetNonempty J
  let fj := fun j => Finset.inf' Finset.univ NEI (fun i =>A i j)
  let C0 := Finset.inf' Finset.univ NEJ fj
  have Aij : ∀ i j,  A i j ≥ C0 := by
    intro i j
    calc
    _ ≥ Finset.inf'  Finset.univ NEI (fun i =>A i j) :=  Finset.inf'_le _ (Finset.mem_univ _)
    _ ≥ C0 := Finset.inf'_le fj (Finset.mem_univ _)
  use C0 --* Fintype.card J
  intro y
  simp only [mu.aux, ge_iff_le, Finset.mem_univ, Finset.le_sup'_iff,true_and]
  use default
  calc
    _ ≥ wsum y fun _ => C0 := by apply wsum_ge_of_ge (fun a => Aij default a)
    _ = C0 := wsum_const _ _


lemma mu.aux.ge_mu0 (A : I →J → ℝ ) : ∀ y, mu.aux A y ≥ mu0 A :=
  ciInf_le (bddBelow_def.2 (by simp [mu.aux.bddBelow A]))

--

lemma exits_yy_mu0 (A : I →J → ℝ )  :
∃ (yy : S J), ∀ i, (wsum yy (fun j => A i j)) ≤  mu0 A := by
    have hs : IsCompact (Set.univ : Set (S J)) := isCompact_univ
    have cmu.aux : ContinuousOn (mu.aux A) (Set.univ)
      := continuous_iff_continuousOn_univ.1 (mu.aux.continouse A)
    obtain ⟨yy,_,Hyy⟩ := IsCompact.exists_isMinOn (hs) (by simp [SNonempty_of_Inhabited]) (cmu.aux)
    rw [isMinOn_iff] at Hyy
    use yy
    intro i
    calc
      mu0 A ≥ mu.aux A yy:= by
        simp only [Set.mem_univ, forall_true_left] at Hyy
        simp [mu0, le_ciInf Hyy]
      _ ≥ _ :=by
        rw [mu.aux]
        apply Finset.le_sup' (fun i:I => wsum yy (fun j => A i j)) (Finset.mem_univ i)

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

lemma linear_comb_gt_right {x y: ℝ} (H : x > y ) {t: Interval} : 0< t.val → t.val * x + (1-t.val) *y > y:= by {
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

--
lemma linear_comb_lt_of_ge_gt (x y: ℝ ) (c:ℝ) (H1 : x ≤ c ) (H2 : y < c)  (t : Interval) : t.val <1 → t.val * x + (1-t.val) *y < c:= by
  intro Ht
  have V1 : x - c ≤ 0 := by linarith
  calc
  _ ≤ t.val * c + (1-t.val) * y := by
    have hh : x = c + (x-c) := by simp
    rw [hh,mul_add]
    have : t.val * (x-c) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos t.prop.1 V1
    linarith
  _ < c := by
    have : (1-t.val) * y < (1-t.val) *c := by
      have : 0 < (1-t.val) := by linarith
      aesop
    linarith

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
  exact ⟨by simp only [t,lt_div_iff]; linarith, by {
    simp only [t,gt_iff_lt, zero_lt_two, div_lt_iff]
    linarith
  },
    by {
       have Ht1: t ∈ Set.Ioc a x:= by {
          simp only [t,Set.mem_Ioc]
          exact ⟨by linarith,by linarith ⟩
       }
       have Ht2: t ∈ f ⁻¹' A :=  Set.mem_of_subset_of_mem hl2 Ht1
       simp only [Set.mem_preimage, Set.mem_Ioi] at Ht2
       exact gt_iff_lt.2 Ht2
    }
  ⟩
}

--
lemma ContinuousAt_lt_of_lt_nbh {f : ℝ → ℝ} {c:ℝ} (H1: f x < c) (H2: ContinuousAt f x) {l :ℝ} (H3 :  l < x ): ∃ t, l < t ∧ t < x ∧ f t <c :=
by {
  let A := Set.Iio c
  have nbhA: A ∈ nhds (f x):= Iio_mem_nhds (by linarith)
  have Cfx:= (continuousAt_def.1 H2) A nbhA
  have N1 := exists_Ioc_subset_of_mem_nhds' Cfx (H3)
  obtain ⟨a,hl1,hl2⟩ := N1
  rw [Set.mem_Ico] at hl1
  let t := (a+x)/2
  use t
  exact ⟨by simp only [t,lt_div_iff]; linarith, by {
    simp only [t,gt_iff_lt, zero_lt_two, div_lt_iff]
    linarith
  },
    by {
       have Ht1: t ∈ Set.Ioc a x:= by {
          simp only [t,Set.mem_Ico]
          exact ⟨by linarith,by linarith ⟩
       }
       have Ht2: t ∈ f ⁻¹' A :=  Set.mem_of_subset_of_mem hl2 Ht1
       simp only [Set.mem_preimage, Set.mem_Ioi] at Ht2
       exact gt_iff_lt.2 Ht2
    }
  ⟩
}
--

lemma linear_comb_gt_of_gt_nbh' (x y: ℝ ) (c:ℝ) (H : x > c ) : ∃ (t : Interval),  0 < t.val ∧ t.val <1 ∧  t.val * x + (1-t.val) *y > c:= by {
  let f := fun s => s*x +(1-s)*y
  have Hfx : f 1 = x := by ring
  have Hfx' : f 1 > c := by linarith
  have Cf : Continuous f := by continuity
  have Cfx : ContinuousAt f 1 := Continuous.continuousAt Cf
  obtain ⟨a,ha1,ha2,ha3⟩ := ContinuousAt_gt_of_gt_nbh Hfx' Cfx (by linarith : (0:ℝ)<1)
  use ⟨a,by linarith,by linarith⟩
}

--
lemma linear_comb_lt_of_lt_nbh' (x y: ℝ ) (c:ℝ) (H : x < c ) : ∃ (t : Interval),  0 < t.val ∧ t.val <1 ∧  t.val * x + (1-t.val) *y < c:= by
  let f := fun s => s*x +(1-s)*y
  have Hfx : f 1 = x := by ring
  have Hfx' : f 1 < c := by linarith
  have Cf : Continuous f := by continuity
  have Cfx : ContinuousAt f 1 := Continuous.continuousAt Cf
  obtain ⟨a,ha1,ha2,ha3⟩ := ContinuousAt_lt_of_lt_nbh Hfx' Cfx (by linarith : (0:ℝ)<1 )
  use ⟨a,by linarith,by linarith⟩
--

lemma wsum_linear_comb_gt_of_ge_gt (f : I → ℝ) (x y: S I) (c : ℝ) (H1 : wsum x f ≥ c ) (H2 : wsum y f > c) (t : Interval) : t.val <1 → wsum (linear_comb t x y) f > c := by {
  intro Ht; rw [wsum_comb_eq_comb_wsum]
  exact linear_comb_gt_of_ge_gt _ _ c H1 H2 _ Ht
}

--
lemma wsum_linear_comb_gt_of_ge_lt (f : I → ℝ) (x y: S I) (c : ℝ) (H1 : wsum x f ≤ c ) (H2 : wsum y f < c) (t : Interval) : t.val <1 → wsum (linear_comb t x y) f < c := by {
  intro Ht; rw [wsum_comb_eq_comb_wsum]
  exact linear_comb_lt_of_ge_gt _ _ c H1 H2 _ Ht
}
--

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
        have H2 : mu0 A = A i0 j0 := by
          -- The proof is the same as that of H1
          have :∀ y, mu.aux A y = A i0 j0 := by
            intro y
            simp only [mu.aux,hi1,Finset.sup'_singleton]
            have : y = S.pure j0 := Set.mem_singleton_iff.1 (by
              simp_rw [<-hj2,Set.mem_univ])
            rw [this,wsum_pure]
          rw [mu0,iInf_congr this,ciInf_const]
        linarith
}

@[simp]
def subtypecongr {α : Type*} {p : α → Prop} {q : α → Prop} (h : ∀ x, p x ↔ q x) : {x // p x} ≃ {x // q x} := {
  toFun := fun x => ⟨x.1, (h x.1).1 x.2⟩,
  invFun := fun x => ⟨x.1, (h x.1).2 x.2⟩,
  left_inv := by {rintro ⟨x, hx⟩; simp},
  right_inv := by {rintro ⟨x, hx⟩; simp}
}


theorem Finset.prod_extend_by_one' {α : Type*} {β : Type*} [Fintype α] [CommMonoid β] [DecidableEq α] (s : Finset α) (f : s → β) : ∏ i, (fun i  => if  h: i∈s then f ⟨i, h⟩ else 1) i =  ∏ j , f j:= by
  simp only [prod_dite, Subtype.forall,implies_true, prod_eq_one, mul_one,attach_eq_univ]
  let e : {x // x ∈ filter (· ∈ s) univ } ≃ {x // x ∈ s}:= subtypecongr (by simp)
  apply Finset.prod_equiv e (by simp)
  intro i _ ; congr

theorem Finset.sum_extend_by_zero' {α : Type*} {β : Type*} [Fintype α] [AddCommMonoid β] [DecidableEq α] (s : Finset α) (f : s → β) : ∑ i, (fun i  => if  h: i∈s then f ⟨i, h⟩ else 0) i =  ∑  j , f j:= by
  simp only [sum_dite, Subtype.forall,implies_true, sum_eq_zero, add_zero,attach_eq_univ]
  let e : {x // x ∈ filter (· ∈ s) univ } ≃ {x // x ∈ s}:= subtypecongr (by simp)
  apply Finset.sum_equiv e (by simp)
  intro i _ ; congr

theorem dite_mul {β : Type*} [Mul β] (p : Prop) [Decidable p] (a : β ) (b : p → β) (c : ¬p → β) :
(if h : p then b h else c h) * a = if h : p then (b h) * a else (c h) * a :=
  by split_ifs <;> rfl


theorem minmax' (n :ℕ) (Hgt : 2 ≤ n) (Hn: n = Fintype.card I + Fintype.card J) (A : I →J→ ℝ): lam0 A = mu0 A := by {
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
          . {
            intro HJ
            obtain ⟨j0,HJ⟩:= HJ
            let J' := {j : J // j≠j0}
            have cardJ_ne_one: Fintype.card J ≠ 1 := by
              intro H
              obtain ⟨j, hj⟩ := Finset.card_eq_one.1 H
              have HJ0 : j0 ∈ (Finset.univ : Finset J) := by simp
              have j0j : j0 = j := by
                rw [hj] at HJ0
                exact Finset.mem_singleton.1 HJ0
              have this: lam0 A ≥  (wsum xx fun i => A i j0) := by
                calc
                _ ≥ lam.aux A xx := by apply lam.aux.le_lam0
                _ = wsum xx fun i => A i j0 := by
                  simp [lam.aux,j0j,hj]
              linarith
            have inhabited_J' : Inhabited J':= by
              have HJ0 : ∃ j, (j ≠ j0) := by
                by_contra H1
                push_neg at H1
                have Jj0 : (Finset.univ : Finset J) = {j0} := by
                  ext;simp [H1]
                have : Fintype.card J = 1 := by
                  simp [<-Finset.card_univ,Jj0]
                exact cardJ_ne_one this
              have jj : J' := ⟨choose HJ0, choose_spec HJ0⟩
              exact {default:=jj}
            have cardn : n = Fintype.card I + Fintype.card J' := by
              have : Fintype.card J'  = Fintype.card J -1 := by simp only [J',ne_eq, Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, ge_iff_le]
              have cardposJ: 1≤ Fintype.card J := @Fintype.card_pos J _ _
              rw [this,<-Nat.add_sub_assoc cardposJ _,<-Hn]
              simp only [ge_iff_le, add_le_iff_nonpos_left, nonpos_iff_eq_zero, add_tsub_cancel_right]
            let A' := fun i: I => fun j : J' => A i j
            have HIJ' := IH cardn A'
            have lam0_lt_lam0' : lam0 A  < lam0 A' := by
              have h1 : lam0 A < mu0 A := lam0_lt_mu0
              have h2 : mu0 A = iInf (mu.aux A) := rfl
              have h3 : mu0 A' = iInf (mu.aux A') := rfl
              have h4 : iInf (mu.aux A') ≥ iInf (mu.aux A) := by
                rw [ge_iff_le]
                let tau : S J' → S J := fun y' : S J' =>
                   ⟨fun j:J => if h: j≠ j0 then (y' ⟨j,h⟩) else 0 ,(by
                    constructor
                    . intro j
                      by_cases hj : j = j0
                      . simp [hj]
                      . simp [hj,y'.prop]
                    . simp only [dite_not, Finset.sum_dite, Finset.sum_const_zero, zero_add,Finset.attach_eq_univ]
                      let e : { x // x ∈ Finset.filter (¬ ·=j0) Finset.univ} ≃ J' := subtypecongr (by simp)
                      apply Eq.symm
                      calc
                        _ = _ := Eq.symm y'.2.2
                        _ = _ := by
                          apply Eq.symm
                          apply Finset.sum_equiv e (by simp)
                          intro i _;congr)⟩
                have SJ' := {y : S J | y j0 =0 }
                nth_rw 2 [iInf]
                apply le_csInf
                . apply Set.range_nonempty
                . rintro b ⟨y',Hy'⟩
                  have h6 : mu.aux A' y' = mu.aux A (tau y') := by
                    simp_rw [mu.aux,wsum,dite_mul]
                    congr;ext i
                    simp only [ne_eq, zero_mul, dite_not, Finset.sum_dite, Finset.sum_const_zero,
                      zero_add]
                    --unfold J'
                    let e : { x // x ∈ Finset.filter (¬ ·=j0) Finset.univ} ≃ J' := subtypecongr (by simp)
                    apply Eq.symm
                    apply Finset.sum_equiv e (by simp)
                    intro i hi; aesop
                  rw [h6] at Hy'
                  rw [<-Hy']
                  apply ciInf_le
                  rw [bddBelow_def]
                  obtain ⟨C, HC⟩ := mu.aux.bddBelow A
                  use C
                  intro D ⟨y, hy⟩
                  rw [<-hy]
                  exact HC y
              rw [<-h2, <-h3, <-HIJ'] at h4
              apply gt_of_ge_of_gt h4 h1
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
            intro HI
            obtain ⟨i0,HI⟩:= HI
            let I' := {i : I // i≠i0}
            have cardI_ne_one: Fintype.card I ≠ 1 := by
              intro H
              obtain ⟨i, hi⟩ := Finset.card_eq_one.1 H
              have HI0 : i0 ∈ (Finset.univ : Finset I) := by simp
              have i0i : i0 = i := by
                rw [hi] at HI0
                exact Finset.mem_singleton.1 HI0
              have this: mu0 A ≤  (wsum yy fun j => A i0 j) := by
                calc
                _ ≤ mu.aux A yy := by apply mu.aux.ge_mu0
                _ = wsum yy fun j => A i0 j := by
                  simp [mu.aux,i0i,hi]
              linarith
            have inhabited_I' : Inhabited I':= by
              have HI0 : ∃ i, (i ≠ i0) := by
                by_contra H1
                push_neg at H1
                have Ii0 : (Finset.univ : Finset I) = {i0} := by
                  ext;simp [H1]
                have : Fintype.card I = 1 := by
                  simp [<-Finset.card_univ,Ii0]
                exact cardI_ne_one this
              have ii : I' := ⟨choose HI0, choose_spec HI0⟩
              exact {default:=ii}
            have cardn : n = Fintype.card I' + Fintype.card J := by
              have : Fintype.card I'  = Fintype.card I -1 := by simp only [I',ne_eq, Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, ge_iff_le]
              have cardposI: 1≤ Fintype.card I:= @Fintype.card_pos I _ _
              rw [this,add_comm,<-Nat.add_sub_assoc cardposI _]
              nth_rewrite 2 [add_comm] at Hn
              rw [<-Hn]
              simp only [ge_iff_le, add_le_iff_nonpos_left, nonpos_iff_eq_zero, add_tsub_cancel_right]
            let A' := fun i: I' => fun j : J => A i j
            have HIJ' := IH cardn A'
            have mu0_lt_mu0' : mu0 A'  < mu0 A := by
              have h1 : lam0 A < mu0 A := lam0_lt_mu0
              have h2 : lam0 A = iSup (lam.aux A) := rfl
              have h3 : lam0 A' = iSup (lam.aux A') := rfl
              have h4 : iSup (lam.aux A') ≤ iSup (lam.aux A) := by
                let tau : S I' → S I := fun x' =>
                   ⟨fun i:I => if h: i≠ i0 then (x' ⟨i,h⟩) else 0 ,(by
                    constructor
                    . intro i
                      by_cases hi : i = i0
                      . simp [hi]
                      . simp [hi,x'.prop]
                    . simp only [dite_not, Finset.sum_dite, Finset.sum_const_zero, zero_add,Finset.attach_eq_univ]
                      let e : { y // y ∈ Finset.filter (¬ ·=i0) Finset.univ} ≃ I' := subtypecongr (by simp)
                      apply Eq.symm
                      calc
                        _ = _ := Eq.symm x'.2.2
                        _ = _ := by
                          apply Eq.symm
                          apply Finset.sum_equiv e (by simp)
                          intro j _;congr)⟩
                have SI' := {x : S I | x i0 =0 }
                nth_rw 2 [iSup]
                apply csSup_le
                . apply Set.range_nonempty
                . rintro b ⟨x',Hx'⟩
                  have h6 : lam.aux A' x' = lam.aux A (tau x') := by
                    simp_rw [lam.aux,wsum,dite_mul]
                    congr;ext j
                    simp only [ne_eq, zero_mul, dite_not, Finset.sum_dite, Finset.sum_const_zero,
                      zero_add]
                    let e : { y // y ∈ Finset.filter (¬ ·=i0) Finset.univ} ≃ I' := subtypecongr (by simp)
                    apply Eq.symm
                    apply Finset.sum_equiv e (by simp)
                    intro j hj; aesop
                  rw [h6] at Hx'
                  rw [<-Hx']
                  apply le_ciSup
                  rw [bddAbove_def]
                  obtain ⟨C, HC⟩ := lam.aux.bddAbove A
                  use C
                  intro D ⟨x, hx⟩
                  rw [<-hx]
                  exact HC x
              rw [<-h2, <-h3, HIJ'] at h4
              apply lt_of_le_of_lt h4 h1
            obtain ⟨_, _⟩ :=  exits_xx_lam0 A'
            obtain ⟨yy', Hyy'⟩ :=  exits_yy_mu0 A'
            have prop_st : ∃ t : {t: ℝ // 0≤ t ∧ t≤1},  mu.aux A (linear_comb t yy yy') < mu0 A := by {
              have HI0:∃ (t : { t:ℝ // 0 ≤ t ∧ t ≤ 1 }), 0< t.val ∧  t.val < 1 ∧ wsum (linear_comb t yy yy') (fun j => A i0 j ) < mu0 A
                := by {
                  simp only [wsum_comb_eq_comb_wsum _ yy yy']
                  apply linear_comb_lt_of_lt_nbh' _ _ _ HI
                }
              have HI2: ∀  i:I , i≠i0 → ∀ (t : { t:ℝ // 0 ≤ t ∧ t ≤ 1}), t.val < 1 →  wsum (linear_comb t yy yy') (fun j => A i j ) < mu0 A
                := by {
                   intro i Hi t Ht
                   apply wsum_linear_comb_gt_of_ge_lt
                   . exact (Hyy i)
                   . {
                    calc
                    _ ≤ mu0 A' := Hyy' ⟨i, Hi⟩
                    _ < mu0 A := by linarith
                   }
                   . exact Ht
                }
              obtain ⟨t0, HtI0⟩ := HI0
              use t0
              rw [mu.aux_lt_iff_lt]
              intro i
              by_cases Hi : i=i0
              .  simp [Hi,HtI0]
              .  exact HI2 i Hi t0 (HtI0.2.1)
            }
            obtain ⟨t, Hst⟩ := prop_st
            have prop_iInf : ∀ y: S J, mu.aux A y ≥ mu0 A := mu.aux.ge_mu0 A
            have := prop_iInf (linear_comb t yy yy')
            linarith
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
          --unfold n
          simp [n];linarith
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
end zerosum
