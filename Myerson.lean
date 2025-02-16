import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.Topology.MetricSpace.Basic

open Classical
open BigOperators Finset

/-- A single parameter environment has
- a set of agents I (which is finite and nonempty),
- a feasible set X, in which each element is a nonnegative vector
  `(x1, x2, . . . , xn)`,
  where xi denotes the "amount of stuff" given. -/
structure SingleParameterEnvironment (I : Type u) [Fintype I] [Nonempty I] where
  -- The feasible set
  feasibleSet : Set (I → ℝ)
  -- We require the feasible set to be nonempty
  feasibleSetNonempty : Nonempty feasibleSet

-- Throughout let E denote a single-parameter environment.
namespace SingleParameterEnvironment

variable {I : Type u} [Fintype I] [Nonempty I]
variable (E : SingleParameterEnvironment I)

/-- A direct-revelation mechanism for a single-parameter environment
is formalized by an allocation rule and a payment rule. -/
structure DirectRevelationMechanism (E : SingleParameterEnvironment I) where
  allocationRule : (I → ℝ) → (I → ℝ)
  paymentRule : (I → ℝ) → I → ℝ
  allocationRuleValid : ∀ b, allocationRule b ∈ E.feasibleSet

section definitions

variable {E : SingleParameterEnvironment I}
variable (D : DirectRevelationMechanism E)
-- instance (E : SingleParameterEnvironment) : Nonempty I := INonempty
-- instance (E : SingleParameterEnvironment) : Fintype I := IFintype
-- instance (E : SingleParameterEnvironment) : Nonempty (E.feasibleSet) :=
--   E.feasibleSetNonempty
-- instance (E : SingleParameterEnvironment) :
--   CoeFun E.feasibleSet (fun _ => I → ℝ) where coe f := f


/-- Quasi-linear utility -/
@[simp]

def utility (v : I → ℝ) (b : I → ℝ) (i : I) : ℝ :=
  v i * (D.allocationRule b i) - D.paymentRule b i

/-- A dominant strategy for `i` is a strategy (i.e., a bid `bi`)
that is guaranteed to maximize `i`'s utility, no matter what the other
bidders do; in other words, for any bids `b` and `b'` such that `b i = bi`,
the utility from `b` should be not less than that of `b'` -/
def dominant (v : I → ℝ) (bid_amount : ℝ) (i : I) : Prop :=
  ∀ b b': I → ℝ,
  b i = bid_amount →
  (∀ j : I, j ≠ i → b j = b' j) → utility D v b i ≥ utility D v b' i

/-- A system is dominant-strategy incentive compatible (DSIC) if
truthful bidding is always a dominant strategy for every bidder and if
truthful bidders always obtain nonnegative utility. -/
def dsic := ∀ (i : I), ∀ (v : I → ℝ), dominant D v (v i) i


--这个是不是mathlib里面有，貌似还真没有
-- Goal here: Define a monotone allocation rule
def nondecreasing (f : ℝ → ℝ) := ∀ (x1 x2 : ℝ), x1 ≤ x2 → f x1 ≤ f x2

/-
@[simp]
noncomputable def with_hole (f : I → ℝ) (i : I) (bi : ℝ) (j : I) : ℝ :=
  if j = i then bi else f j

lemma filled_hole_retrieve {f : I → ℝ} {i : I} {bi : ℝ} :
  with_hole f i bi i = bi := by
  rw [with_hole]; simp

lemma filled_hole_retrieve_other
  {f : I → ℝ} {i j : I} {hyp : i ≠ j} {bi : ℝ} :
  with_hole f i bi j = f j := by
  rw [with_hole, ite_eq_right_iff]
  intro H
  exfalso
  exact hyp (symm H)

lemma filled_hole_almost_equal :
  ∀ (j : I), j ≠ i → with_hole b i x1 j = with_hole b i x2 j := by
  intro j hyp
  rw [filled_hole_retrieve_other]
  rw [filled_hole_retrieve_other]
  { symm; exact hyp }
  { symm; exact hyp }

lemma almost_equal_fill_hole (b b' : I → ℝ) (i : I) :
  (∀ (j : I), ¬j = i → b j = b' j) → with_hole b i = with_hole b' i := by
  intro hyp
  funext x j
  by_cases eq : j = i
  { simp; split; rfl; rfl; }
  { simp; split; rfl; exact hyp j eq }

lemma filled_hole_replace
  {f : I → ℝ} {i : I} {bi : ℝ} :
  with_hole (with_hole f i bi) i = with_hole f i := by
  funext bi' j
  by_cases j = i
  { simp; split; rfl; rfl }
  { simp; split; rfl; rfl; }

lemma unfill_fill_hole {f : I → ℝ} {i : I} : f = with_hole f i (f i) := by
  funext x; simp; split; rename_i p; rw [p]; rfl
-/
/-尝试修一些with hole
@[simp]
noncomputable def with_hole (f : I → ℝ) (i : I) (bi : ℝ) (j : I) : ℝ :=
  if j = i then bi else f j

lemma filled_hole_retrieve {f : I → ℝ} {i : I} {bi : ℝ} :
  with_hole f i bi i = bi := by
  rw [with_hole]
  simp

lemma filled_hole_retrieve_other
  {f : I → ℝ} {i j : I} {bi : ℝ} (hyp : i ≠ j) :
  with_hole f i bi j = f j := by
  rw [with_hole]
  simp
  intro h
  exfalso
  exact hyp h.symm

lemma filled_hole_almost_equal {b : I → ℝ} {i : I} {x1 x2 : ℝ} :
  ∀ (j : I), j ≠ i → with_hole b i x1 j = with_hole b i x2 j := by
  intro j hyp
  sorry

lemma almost_equal_fill_hole {b b' : I → ℝ} {i : I} :
  (∀ (j : I), j ≠ i → b j = b' j) → with_hole b i = with_hole b' i := by
  intro hyp
  funext x j
  by_cases eq : j = i
  · simp [with_hole, eq]
  · simp [with_hole, eq]
    exact hyp j eq

lemma filled_hole_replace
  {f : I → ℝ} {i : I} {bi : ℝ} :
  with_hole (with_hole f i bi) i = with_hole f i := by
  funext bi' j
  by_cases h : j = i
  · simp [with_hole, h]
  · simp [with_hole, h]

lemma unfill_fill_hole {f : I → ℝ} {i : I} : f = with_hole f i (f i) := by
  funext x
  simp [with_hole]
  sorry
-/

/-- An allocation rule is monotone if replacing for every i, replacing the
bid of i with something higher does not cause her to lose allocation. -/
def monotone (ar : (I → ℝ) → (I → ℝ)) :=
  ∀ i : I,
  ∀ b : I → ℝ,
  nondecreasing (λ (bi : ℝ) => ar (Function.update b i bi) i)

/-- Construct a DirectRevelationMechanism from an allocation rule and a payment rule,
    when the allocation rule is feasible. -/
def constructMechanism (E : SingleParameterEnvironment I)
    (ar : (I → ℝ) → (I → ℝ))
    (pr : (I → ℝ) → I → ℝ)
    (h : ∀ b, ar b ∈ E.feasibleSet) : DirectRevelationMechanism E where
  allocationRule := ar
  paymentRule := pr
  allocationRuleValid := h

/-- An allocation rule is implementable if
there is a payment rule such that the resulting direct-revelation mechanism
is DSIC and the allocation rule always produces feasible allocations. -/
def implementable (ar : (I → ℝ) → (I → ℝ)) (E : SingleParameterEnvironment I) :=
  ∃ (h : ∀ b, ar b ∈ E.feasibleSet),
  ∃ pr : (I → ℝ) → I → ℝ,
    dsic (constructMechanism E ar pr h)


end definitions









/- The remaining part of the file is used to prove Myersons' lemma,
we will show that
- An allocation rule is implementable iff it is monotone,
- if x is monotone, then there exists a unique payment rule (given by an
explicit formula) for which the direct revelation system is DSIC and bidders
that bid 0 pay 0. -/

section myerson

variable {E : SingleParameterEnvironment}

theorem payment_sandwich
  (ar : (I → ℝ) → E.feasibleSet)
  (p : (I → ℝ) → I → ℝ) (y z : ℝ):
  @dsic E {allocationRule := ar, paymentRule := p}
  → ∀ i : I,
  z * (ar (with_hole b i y) i - ar (with_hole b i z) i)
  ≤ p (with_hole b i y) i - p (with_hole b i z) i
  ∧ p (with_hole b i y) i - p (with_hole b i z) i
  ≤ y * (ar (with_hole b i y) i - ar (with_hole b i z) i) := by
  intro d i
  have h1 :
    y * (ar (with_hole b i z)) i ≤ y * (ar (with_hole b i y)) i
    - p (with_hole b i y) i + p (with_hole b i z) i
    := by
    have h : (with_hole b i y i = if i = i then y else 0) := by simp
    specialize d i (fun j => if j = i then y else 0)
      (with_hole b i y) (with_hole b i z) h filled_hole_almost_equal
    rw [utility] at d
    simp at d
    exact d
  -- Set z to be the valuation of i here
  have h2 :
    z * (ar (with_hole b i y)) i ≤ z * (ar (with_hole b i z)) i
    - p (with_hole b i z) i + p (with_hole b i y) i
    := by
    have h : (with_hole b i z i = if i = i then z else 0) := by simp
    specialize d i (fun j => if j = i then z else 0)
      (with_hole b i z) (with_hole b i y) h filled_hole_almost_equal
    rw [utility] at d
    simp at d
    exact d
  constructor; { linarith }; { linarith }

-- Goal here: Implementable → Monotone
theorem implementable_impl_monotone (ar : (I → ℝ) → E.feasibleSet) :
  implementable ar → monotone ar := by
  rintro ⟨p, impl⟩ i b x1 x2 xhyp
  have := @payment_sandwich E b ar p x1 x2 impl i
  have y : (x2 - x1) * (ar (with_hole b i x1) i - ar (with_hole b i x2) i) ≤ 0
  := by linarith
  by_cases l : x2 - x1 > 0
  { have := nonpos_of_mul_nonpos_right y l
    linarith }
  { have : x1 = x2 := by linarith
    rw [this] }

-- Will start wrangling with integrals here
open Monotone intervalIntegral

-- Goal here: "Explicit formula" works
-- TODO: Clean this proof up thoroughly
-- I don't have a better name for this, sorry
@[simp]
noncomputable def magic_payment_rule
  (ar : (I → ℝ) → E.feasibleSet) (b : I → ℝ) (i : I) : ℝ :=
  (b i) * ar b i - ∫ t in (0)..(b i), (fun t' => ar (with_hole b i t') i) t

@[simp]
noncomputable def with_magic (ar : (I → ℝ) → E.feasibleSet)
  : DirectRevelationMechanism E :=
  { allocationRule := ar, paymentRule := magic_payment_rule ar }

def utility_exp {v : I → ℝ} (b : I → ℝ) :
  @utility E (with_magic ar) v b i
    = (v i - b i) * ar b i
    + ∫ x in (0)..(b i), (fun t' => ar (with_hole b i t') i) x := by
      rw [utility]; simp; ring_nf

theorem magic_payment_rule_works (ar : (I → ℝ) → E.feasibleSet)
  : (monotone ar) → @dsic E (with_magic ar) := by
  -- Suppose `ar` is monotone and let `i` be the bidder in consideration.
  -- Let `v` be the valuation of the bidders.
  -- Let `b` and `b'` be bids such that `b j = b' j` for all `j ≠ i`,
  -- and `b i = v i`.
  intro mon i v b b' b_i_eq_v_i almost_eq
  --push_neg at almost_eq
  -- The goal now is to show that `utility v b i ≥ utility v b' i`.

  -- We establish a bunch of integrability statements here, no content here
  have func_is_monotone : Monotone (fun x => ar (with_hole b' i x) i):= by
    rw [Monotone]; intro x y h; exact mon i b' x y h
  have b_i_to_b'_i : IntervalIntegrable
    (fun x => ar (with_hole b' i x) i) MeasureTheory.volume (b i) (b' i) := by
    exact intervalIntegrable func_is_monotone
  have zero_to_b_i : IntervalIntegrable
    (fun x => ar (with_hole b' i x) i) MeasureTheory.volume 0 (b i) := by
    exact intervalIntegrable func_is_monotone
  have zero_to_b'_i : IntervalIntegrable
    (fun x => ar (with_hole b' i x) i) MeasureTheory.volume 0 (b' i) := by
    exact intervalIntegrable func_is_monotone
  have const_to_int :
    ∫ x in (b' i)..(b i), (fun _ => ar b' i) x = (b i - b' i) * ar b' i := by
    rw [integral_const]; simp

  -- We will compute `utility v b' i - utility v b i` by cases.
  suffices h : utility v b' i - utility v b i ≤ 0 by linarith
  repeat rw [utility_exp]
  rw [← b_i_eq_v_i]
  ring_nf
  rw [almost_equal_fill_hole b b' i almost_eq, ← sub_mul]
  rw [integral_interval_sub_left zero_to_b'_i zero_to_b_i]
  rw [← const_to_int]
  rw [integral_symm]
  rw [← integral_neg, ← integral_add (by simp) b_i_to_b'_i]

  -- It remains to show that
  -- ∫ (x : ℝ) in b i..b' i,
  -- -(fun x ↦ ↑(ar b') i) x + ↑(ar (with_hole b' i x)) i ≤ 0
  -- We proceed by cases.
  by_cases limit_ineq : b' i ≤ b i
  { rw [integral_symm, ← integral_neg]
    simp
    have : ∀ u ∈ Set.Icc (b' i) (b i),
    0 ≤ (fun x => (ar (with_hole b' i x)) i - (ar b') i) u := by
      intro x; simp
      intro le _
      rw [@unfill_fill_hole E b' i, filled_hole_replace]
      exact mon i b' (b' i) x le
    have := @integral_nonneg
      (fun x => (ar (with_hole b' i x)) i - (ar b') i)
      (b' i) (b i) MeasureTheory.volume limit_ineq this

    have : (-∫ u in (b' i)..(b i),
      (fun x => (ar (with_hole b' i x)) i - (ar b') i) u) ≤ 0
      := by linarith
    rw [← integral_neg] at this
    simp at this
    have t :
      (fun x => (ar b') i - (ar (with_hole b' i x)) i)
      = (fun x => (-(ar (with_hole b' i x)) i) + (ar (b') i))
      := by funext x; linarith
    rw [t] at this
    exact this }
  { --simp
    have : ∀ u ∈ Set.Icc (b i) (b' i),
    0 ≤ (fun x => - (ar (with_hole b' i x)) i + (ar b') i) u := by
      intro x; simp
      intro _ ge
      rw [@unfill_fill_hole E b' i, filled_hole_replace]
      exact mon i b' x (b' i) ge
    have := @integral_nonneg
      (fun x => - (ar (with_hole b' i x)) i + (ar b') i)
      (b i) (b' i) MeasureTheory.volume (by linarith) this

    have : (- ∫ u in (b i)..(b' i),
      (fun x => - (ar (with_hole b' i x)) i + (ar b') i) u) ≤ 0
      := by linarith
    rw [← integral_neg] at this
    simp at this
    exact this }

theorem magic_payment_bid_zero_implies_payment_zero
  (ar : (I → ℝ) → E.feasibleSet) :
  ∀ b : I → ℝ, ∀ i : I, b i = 0 → magic_payment_rule ar b i = 0 := by
  intro b i hyp; rw [magic_payment_rule, hyp]; simp

-- Goal here: Works → "Explicit formula"
-- TODO: figure out a proof and then finish this
theorem magic_payment_rule_unique (ar : (I → ℝ) → E.feasibleSet)
  : ∀ p q : ((I → ℝ) → I → ℝ),
  (monotone ar)
  → @dsic E {allocationRule := ar, paymentRule := p}
  → @dsic E {allocationRule := ar, paymentRule := q}
  → (∀ b : I → ℝ, ∀ i : I, b i = 0 → p b i = 0)
  → (∀ b : I → ℝ, ∀ i : I, b i = 0 → q b i = 0)
  → p = q := by
  intro p q _ dp dq hyp hyq
  funext b i

  -- Set d = p - q.
  set d := p - q
  -- It suffices to show that d b i ≤ ε for all ε ≥ 0.
  suffices : ∀ ε > 0, |d b i| ≤ ε
  { exact eq_of_forall_dist_le this }

  -- Therefore let ε ≥ 0.
  intro ε hε
  -- For notational simplicity let c _ := d (with_hole b i _) i
  set c := fun (y : ℝ) => d (with_hole b i y) i
  -- For notational simplicity let c' _ := ar (with_hole b i _) i
  set c' := fun (y : ℝ) => ar (with_hole b i y) i

  have : d b i = c (b i) := by simp; conv => lhs; rw [@unfill_fill_hole E b i]
  rw [this]

  have useful : ∀ y z : ℝ, y ≥ z → |c y - c z| ≤ (y - z) * (c' y - c' z) := by
    intro y z _; rw [abs_le]
    obtain ⟨h1, h2⟩ := @payment_sandwich E b ar p y z dp i
    obtain ⟨h3, h4⟩ := @payment_sandwich E b ar q y z dq i
    simp; constructor <;> linarith

  have c_zero_is_zero : c 0 = 0 := by
    specialize hyp (with_hole b i 0) i (by simp)
    specialize hyq (with_hole b i 0) i (by simp)
    simp; rw [hyp, hyq]; simp

  -- deal first with the situation where the allocation is equal.
  by_cases r : c' (b i) - c' 0 = 0
  { by_cases b i ≥ 0
    { specialize useful (b i) 0 (by assumption)
      rw [c_zero_is_zero, r] at useful; simp at useful
      simp; rw [useful]; simp; linarith }
    { specialize useful  0 (b i) (by linarith)
      have : c' 0 - c' (b i) = 0 := by linarith
      rw [c_zero_is_zero, this] at useful; simp at useful
      simp; rw [abs_sub_comm, useful]; simp; linarith }}

  -- Let N be large so that the bottom holds. This makes sense since we can
  -- assume the denominator is not 0.
  obtain ⟨N, Nhyp⟩ := exists_nat_ge (|b i| * |c' (b i) - c' 0| / ε)

  have c'_diff_gt_zero : 0 < |c' (b i) - c' 0| := by
    rw [lt_abs]; push_neg at r; rw [ne_iff_lt_or_gt, or_comm] at r
    conv => rhs; rw [lt_neg, neg_zero]
    conv => lhs; rw [← GT.gt]
    exact r

  have N_gt_zero : N > 0 := by
    rw [div_le_iff hε] at Nhyp
    have : b i ≠ 0 := by by_contra r'; rw [r'] at r; simp at r
    have : 0 < |b i| * |c' (b i) - c' 0| := by
      apply mul_pos
      { rw [lt_abs, or_comm]
        conv => left; rw [lt_neg]; simp
        have := ne_iff_lt_or_gt.mp this
        exact this }
      { exact c'_diff_gt_zero }
    have : 0 < N * ε := by linarith
    have := (mul_pos_iff_of_pos_right hε).mp this
    simp at this
    exact this

  have sane : N * (b i / N) = b i := by
    rw [← mul_div_assoc, mul_comm]
    apply mul_div_cancel
    simp
    linarith


  have : c (b i) = c (N * (b i / N)) - c (0 * (b i / N)) := by
    rw [sane]
    have : 0 * (b i / N) = 0 := by ring_nf
    rw [this, c_zero_is_zero]
    simp
  rw [this]

  have := sum_range_sub (fun l => c (l * (b i / N))) N
  simp at this; simp
  rw [← this]

  have := Finset.abs_sum_le_sum_abs
    (fun (l : ℕ) => c ((l + 1) * (b i / N)) - c (l * (b i / N))) (range N)
  simp at this; apply le_trans this

  have : ∀ x ∈ range N, |c ((x + 1) * (b i / N)) - c (x * (b i / N))|
    ≤ (b i / N) * (c' ((x + 1) * (b i / N)) - c' (x * (b i / N))) := by
    intro x _
    by_cases r : b i ≥ 0
    { have : (x + 1) * (b i / N) ≥ x * (b i / N) := by
        ring_nf; simp; rw [← div_eq_mul_inv]; exact div_nonneg r (by linarith)
      specialize useful ((x + 1) * (b i / N)) (x * (b i / N)) this
      apply le_trans useful; ring_nf; simp }
    { push_neg at r
      have : x * (b i / N) ≥ (x + 1) * (b i / N) := by
        ring_nf; simp; rw [← div_eq_mul_inv]
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      specialize useful (x * (b i / N)) ((x + 1) * (b i / N)) this
      rw [abs_sub_comm]
      apply le_trans useful; ring_nf; simp }
  have := Finset.sum_le_sum this
  apply le_trans this
  rw [← Finset.mul_sum]
  have := sum_range_sub (fun x => c' (x * (b i / N))) N
  simp
  simp at this
  rw [this, sane, div_mul_eq_mul_div]
  apply (div_le_iff _).mpr
  apply (div_le_iff hε).mp at Nhyp
  conv => right; rw [mul_comm]
  apply le_trans' Nhyp
  rw [← abs_mul]
  simp
  apply le_trans' (le_abs_self _)
  rfl
  simp
  assumption
