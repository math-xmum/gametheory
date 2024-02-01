import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue

open Classical
open BigOperators

/-- A single parameter environment has
- some number n of agents, and
- a feasible set X, in which each element is a nonnegative vector
  `(x1, x2, . . . , xn)`,
  where xi denotes the “amount of stuff” given. -/
structure SingleParameterEnvironment where
  -- The set of bidders
  I : Type*
  -- We require I to be nonempty
  INonempty : Nonempty I
  -- We require I to be finite
  IFintype : Fintype I
  -- The feasible set
  feasibleSet : Set (I → ℝ)
  -- We require the feasible set to be nonempty
  feasibleSetNonempty : Nonempty feasibleSet

instance (E : SingleParameterEnvironment) : Nonempty E.I := E.INonempty
instance (E : SingleParameterEnvironment) : Fintype E.I := E.IFintype
instance (E : SingleParameterEnvironment) : Nonempty (E.feasibleSet) :=
  E.feasibleSetNonempty
instance (E : SingleParameterEnvironment) :
  CoeFun E.feasibleSet (fun _ => E.I → ℝ) where coe f := f

-- Throughout let E denote a single-parameter environment.
namespace SingleParameterEnvironment

/-- A direct-revelation mechanism for a single-parameter environment
is formalized by an allocation rule and a payment rule. -/
structure DirectRevelationMechanism (E : SingleParameterEnvironment) where
  allocationRule : (E.I → ℝ) → E.feasibleSet
  paymentRule : (E.I → ℝ) → E.I → ℝ

section definitions
/- Henceforth let E be a single parameter environment and D be a direct
revelation mechanism on E. -/
variable {E : SingleParameterEnvironment} {D : DirectRevelationMechanism E}

/-- Quasi-linear utility -/
@[simp]
def utility (v : E.I → ℝ) (b : E.I → ℝ) (i : E.I) : ℝ :=
  v i * D.allocationRule b i - D.paymentRule b i

/-- A dominant strategy for `i` is a strategy (i.e., a bid `bi`)
that is guaranteed to maximize `i`’s utility, no matter what the other
bidders do; in other words, for any bids `b` and `b'` such that `b i = bi`,
the utility from `b` should be not less than that of `b'` -/
def dominant (v : E.I → ℝ) (bid_amount : ℝ) (i : E.I) : Prop :=
  ∀ b b': E.I → ℝ,
  b i = bid_amount →
  (∀ j : E.I, j ≠ i → b j = b' j) → @utility E D v b i ≥ @utility E D v b' i

/-- A system is dominant-strategy incentive compatible (DSIC) if
truthful bidding is always a dominant strategy for every bidder and if
truthful bidders always obtain nonnegative utility. -/
def dsic := ∀ (i : E.I), ∀ (v : E.I → ℝ), @dominant E D v (v i) i

-- Goal here: Define a monotone allocation rule
def nondecreasing (f : ℝ → ℝ) := ∀ (x1 x2 : ℝ), x1 ≤ x2 → f x1 ≤ f x2

@[simp]
noncomputable def with_hole (f : E.I → ℝ) (i : E.I) (bi : ℝ) (j : E.I) : ℝ :=
  if j = i then bi else f j

lemma filled_hole_retrieve {f : E.I → ℝ} {i : E.I} {bi : ℝ} :
  with_hole f i bi i = bi := by
  rw [with_hole]; simp

lemma filled_hole_retrieve_other
  {f : E.I → ℝ} {i j : E.I} {hyp : i ≠ j} {bi : ℝ} :
  with_hole f i bi j = f j := by
  rw [with_hole, ite_eq_right_iff]
  intro H
  exfalso
  exact hyp (symm H)

lemma filled_hole_almost_equal :
  ∀ (j : E.I), j ≠ i → with_hole b i x1 j = with_hole b i x2 j := by
  intro j hyp
  rw [filled_hole_retrieve_other]
  rw [filled_hole_retrieve_other]
  { symm; exact hyp }
  { symm; exact hyp }

lemma almost_equal_fill_hole (b b' : E.I → ℝ) (i : E.I) :
  (∀ (j : E.I), ¬j = i → b j = b' j) → with_hole b i = with_hole b' i := by
  intro hyp
  funext x j
  by_cases eq : j = i
  { simp; split; rfl; rfl; }
  { simp; split; rfl; exact hyp j eq }

lemma filled_hole_replace
  {f : E.I → ℝ} {i : E.I} {bi : ℝ} :
  with_hole (with_hole f i bi) i = with_hole f i := by
  funext bi' j
  by_cases j = i
  { simp; split; rfl; rfl }
  { simp; split; rfl; rfl; }

lemma unfill_fill_hole {f : E.I → ℝ} {i : E.I} : f = with_hole f i (f i) := by
  funext x; simp; split; rename_i p; rw [p]; rfl

/-- An allocation rule is monotone if replacing for every i, replacing the
bid of i with something higher does not cause her to lose allocation. -/
def monotone (ar : (E.I → ℝ) → E.feasibleSet) :=
  ∀ i : E.I,
  ∀ b : E.I → ℝ,
  nondecreasing (λ (bi : ℝ) => ar (with_hole b i bi) i)

/-- An allocation rule is implementable if
there is a payment rule such that the resulting direct-revelation mechanism
is DSIC. -/
def implementable (ar : (E.I → ℝ) → E.feasibleSet) :=
  ∃ pr : (E.I → ℝ) → E.I → ℝ,
  @dsic E {allocationRule := ar, paymentRule := pr}

end definitions

/- The remaining part of the file is used to prove Myersons' lemma,
we will show that
- An allocation rule is implementable iff it is monotone,
- if x is monotone, then there exists a unique payment rule (given by an
explicit formula) for which the direct revelation system is DSIC and bidders
that bid 0 pay 0. -/

section myerson

variable {E : SingleParameterEnvironment}

-- Goal here: Implementable → Monotone
theorem implementable_impl_monotone (ar : (E.I → ℝ) → E.feasibleSet) :
  implementable ar → monotone ar := by
  rintro ⟨p, impl⟩ i b x1 x2 xhyp
  -- Set x1 to be the valuation of i here
  have h1 :
    x1 * (ar (with_hole b i x2)) i ≤ x1 * (ar (with_hole b i x1)) i
    - p (with_hole b i x1) i + p (with_hole b i x2) i
    := by
    have h : (with_hole b i x1 i = if i = i then x1 else 0) := by simp
    specialize impl i (fun j => if j = i then x1 else 0)
      (with_hole b i x1) (with_hole b i x2) h filled_hole_almost_equal
    rw [utility] at impl
    simp at impl
    exact impl
  -- Set x2 to be the valuation of i here
  have h2 :
    x2 * (ar (with_hole b i x1)) i ≤ x2 * (ar (with_hole b i x2)) i
    - p (with_hole b i x2) i + p (with_hole b i x1) i
    := by
    have h : (with_hole b i x2 i = if i = i then x2 else 0) := by simp
    specialize impl i (fun j => if j = i then x2 else 0)
      (with_hole b i x2) (with_hole b i x1) h filled_hole_almost_equal
    rw [utility] at impl
    simp at impl
    exact impl
  -- combine the two obtained inequalities
  have y :
  (x2 - x1) * (ar (with_hole b i x1) i - ar (with_hole b i x2) i) ≤ 0
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
  (ar : (E.I → ℝ) → E.feasibleSet) (b : E.I → ℝ) (i : E.I) : ℝ :=
  (b i) * ar b i - ∫ t in (0)..(b i), (fun t' => ar (with_hole b i t') i) t

@[simp]
noncomputable def with_magic (ar : (E.I → ℝ) → E.feasibleSet)
  : DirectRevelationMechanism E :=
  { allocationRule := ar, paymentRule := magic_payment_rule ar }

theorem magic_payment_rule_works (ar : (E.I → ℝ) → E.feasibleSet)
  : (monotone ar) → @dsic E (with_magic ar) := by
  -- Suppose `ar` is monotone and let `i` be the bidder in consideration.
  -- Let `v` be the valuation of the bidders.
  -- Let `b` and `b'` be bids such that `b j = b' j` for all `j ≠ i`,
  -- and `b i = v i`.
  intro mon i v b b' b_i_eq_v_i almost_eq
  push_neg at almost_eq
  -- The goal now is to show that `utility v b i ≥ utility v b' i`.
  -- First we show that we have the following result:
  have utility_exp b :
    @utility E (@with_magic E ar) v b i
    = (v i - b i) * ar b i
    + ∫ x in (0)..(b i), (fun t' => ar (with_hole b i t') i) x := by
      rw [utility]; simp; ring_nf

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
  { simp
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
  (ar : (E.I → ℝ) → E.feasibleSet) :
  ∀ b : E.I → ℝ, ∀ i : E.I, b i = 0 → magic_payment_rule ar b i = 0 := by
  intro b i hyp; rw [magic_payment_rule, hyp]; simp

-- Goal here: Works → "Explicit formula"
-- TODO: figure out a proof and then finish this
theorem magic_payment_rule_unique (ar : (E.I → ℝ) → E.feasibleSet)
  : ∀ p : ((E.I → ℝ) → E.I → ℝ),
  @dsic E (@with_magic E ar) → p = magic_payment_rule ar := by

  sorry
