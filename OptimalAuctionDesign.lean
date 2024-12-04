import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses
import Mathlib.Data.ENNReal.Basic

open Classical MeasureTheory ProbabilityTheory

/-- Structure representing an auction environment with revision effects -/
structure AuctionEnv where
  n : ℕ
  a : Fin n → ℝ
  b : Fin n → ℝ
  μ : Fin n → Measure ℝ

  bounds_valid : ∀ i, a i < b i
  μ_probability : ∀ i, IsProbabilityMeasure (μ i)
  f : Fin n → ℝ → ℝ
  density_eq : ∀ i t, ∫ x in Set.Iic t, f i x = (μ i (Set.Iic t)).toReal
  e : Fin n → ℝ → ℝ
  density_positive : ∀ i t, t ∈ Set.Icc (a i) (b i) → f i t > 0
  revision_zero_expectation : ∀ j, ∫ t in (a j)..(b j), e j t * f j t = 0
  μ_finite : IsFiniteMeasure (μ i)

attribute [instance] AuctionEnv.μ_probability

instance AuctionEnv.mu_finite {env : AuctionEnv} {i : Fin env.n}: IsFiniteMeasure (env.μ i )
  := inferInstance

namespace Auction

variable (env : AuctionEnv)

/-- Given an auction environment, defines its value space -/
abbrev ValueSpace := Fin env.n → ℝ

/-- Cumulative distribution functions -/
noncomputable def F (i : Fin env.n) : ℝ → ℝ :=
  fun t ↦ (env.μ i (Set.Iic t)).toReal

#check MeasureTheory.ProbabilityMeasure.apply_mono
#check MeasureTheory.measure_lt_top
#check ENNReal.toReal_mono

/-- F is monotone -/
theorem F_monotone (i : Fin env.n) :
  Monotone (F env i) := by
  intro x y hxy
  unfold F
  have h1 : Set.Iic x ⊆ Set.Iic y := by exact Set.Iic_subset_Iic.2 hxy
  have h2 : (env.μ i (Set.Iic x)) ≤ (env.μ i (Set.Iic y)) := by
    exact OuterMeasureClass.measure_mono (env.μ i) h1

  -- have I : IsFiniteMeasure (env.μ i) := by
  --   exact (env.μ_probability i).toIsFiniteMeasure
  apply ENNReal.toReal_mono
  · exact ne_of_lt (measure_lt_top (env.μ i) (Set.Iic y))
  · exact h2

/-- F is bounded by 0 and 1 -/
theorem F_bounds (i : Fin env.n) (t : ℝ) :
 0 ≤ F env i t ∧ F env i t ≤ 1 := by
 unfold F
 constructor
 · exact ENNReal.toReal_nonneg
 · have h := (env.μ_probability i).measure_univ
   have h2 : env.μ i (Set.Iic t) ≤ env.μ i Set.univ := by
     apply OuterMeasureClass.measure_mono
     intro x setx
     trivial
   simp [h] at h2
   have h3 : ENNReal.ofReal ((env.μ i (Set.Iic t)).toReal) = env.μ i (Set.Iic t) := by
     apply ENNReal.ofReal_toReal
     apply measure_ne_top
   have h4 : ENNReal.ofReal ((env.μ i (Set.Iic t)).toReal) ≤ 1 := by
     rw [h3]
     exact h2
   exact ENNReal.ofReal_le_one.1 h4

/-- F tends to 0 at -∞ -/
theorem F_tendsto_atBot (i : Fin env.n) :
 Filter.Tendsto (F env i) Filter.atBot (nhds 0) := by
 unfold F
 apply squeeze_zero
 · intro t
   exact ENNReal.toReal_nonneg
 · intro t
   exact (F_bounds env i t).2
 · intro s h
   rcases Metric.mem_nhds_iff.1 h with ⟨ε, εpos, hε⟩
   refine Filter.mem_atBot_sets.2 ⟨-ε, fun y hy => ?_⟩
   have h2 := OuterMeasureClass.measure_mono (env.μ i) (Set.subset_univ (Set.Iic y))
   have h3 : (env.μ i (Set.Iic y)).toReal ≤ 1 := by
     have h4 := le_trans h2 (by rw [(env.μ_probability i).measure_univ])
     apply ENNReal.toReal_le_of_le_ofReal
     · norm_num
     · simp only [ENNReal.ofReal_one, h4]
   apply hε
   simp only [Metric.mem_ball, dist_zero_right]
   have h_lower : -1 ≤ ((env.μ i) (Set.Iic y)).toReal := by sorry
   sorry

/-- F tends to 1 at +∞ -/
theorem F_tendsto_atTop (i : Fin env.n) :
  Filter.Tendsto (F env i) Filter.atTop (nhds 1) := by
  sorry

/-- F agrees with the integral of f -/
theorem F_eq_integral (i : Fin env.n) (t : ℝ) :
  F env i t = ∫ x in Set.Iic t, env.f i x := by
  unfold F
  exact Eq.symm (env.density_eq i t)

/-- F is the cdf of μ -/
theorem F_eq_cdf (i : Fin env.n) (t : ℝ) :
  F env i t = (cdf (env.μ i)) t := by
  unfold F cdf
  sorry
  -- simp only [condCDF_eq_toReal_iic]

theorem cdf_value_le_one (i : Fin env.n) (t : ℝ) :
  (env.μ i (Set.Iic t)) ≤ 1 := prob_le_one

section Valuations

/-- Final valuation function for bidder i -/
noncomputable def bidder_valuation {env : AuctionEnv} (i : Fin env.n) (t : ValueSpace env) : ℝ :=
  t i + ∑ j in (Finset.univ.erase i), env.e j (t j)

/-- Final valuation function for seller -/
noncomputable def seller_valuation {env : AuctionEnv} (t₀ : ℝ) (t : ValueSpace env) : ℝ :=
  t₀ + ∑ j in Finset.univ, env.e j (t j)

/-! ### Main Theorems -/

/-- Structure of valuations in auction with revision effects -/
theorem auction_valuation_structure
  {env : AuctionEnv}
  (i : Fin env.n)
  (t : ValueSpace env):
  bidder_valuation i t = t i + ∑ j in (Finset.univ.erase i), env.e j (t j) := by
  rfl

/-- Relationship between bidder and seller valuations -/
theorem bidder_seller_valuation_relation
  {env : AuctionEnv}
  (t₀ : ℝ)
  (t : ValueSpace env)
  (i : Fin env.n):
  seller_valuation t₀ t - bidder_valuation i t = t₀ - t i + env.e i (t i) := by
  simp only [seller_valuation, bidder_valuation, Finset.mem_univ, Finset.sum_erase_eq_sub]
  ring

end Valuations


namespace DirectRevelationMechanisms

variable {env : AuctionEnv}

-- The space of bidding strategies for a general mechanism -/
variable {Θ : Fin env.n → Type}

/-- Values must lie in their valid intervals -/
structure ValidValue (env : AuctionEnv) where
  value : ValueSpace env
  valid : ∀ i, value i ∈ Set.Icc (env.a i) (env.b i)

/-- A general auction mechanism -/
structure GeneralMechanism where
  /-- Probability assignment in general mechanism -/
  p : (Π i, Θ i) → Fin env.n → ℝ
  /-- Payment function in general mechanism -/
  x : (Π i, Θ i) → Fin env.n → ℝ
  /-- Strategic plans -/
  θ : Π i, Set.Icc (env.a i) (env.b i) → Θ i
  /-- Probability conditions for general mechanism -/
  p_nonneg : ∀ s i, p s i ≥ 0
  p_sum_le_one : ∀ s, ∑ i, p s i ≤ 1

variable (mech : @GeneralMechanism env Θ)

/-- Apply strategic plans to convert value profiles to strategy profiles -/
def apply_strategies (t : ValidValue env) : Π i, Θ i :=
  fun i ↦ mech.θ i ⟨t.value i, t.valid i⟩

/-- Expected utility in a general mechanism -/
noncomputable def general_mechanism_utility
    (i : Fin env.n)
    (t : ValidValue env) : ℝ :=
  let s := apply_strategies mech t
  bidder_valuation i t.value * mech.p s i - mech.x s i

/-- Type for outcome functions: a direct revelation mechanism (p,x) -/
structure DirectMechanism (env : AuctionEnv) where
  /-- Probability assignment function: p_i(t) is probability that i gets the object -/
  p : ValidValue env → Fin env.n → ℝ
  /-- Payment function: x_i(t) is the payment from bidder i to seller -/
  x : ValidValue env → Fin env.n → ℝ
  /-- Probability conditions (3.3) -/
  p_nonneg : ∀ t i, p t i ≥ 0
  p_sum_le_one : ∀ t, ∑ i, p t i ≤ 1

/-- Function to update a value profile while preserving validity -/
noncomputable def update_value
    (t : ValidValue env)
    (i : Fin env.n)
    (s_i : ℝ)
    (h_s_i : s_i ∈ Set.Icc (env.a i) (env.b i)) : ValidValue env where
  value := Function.update t.value i s_i
  valid := by
    intro j
    by_cases h : j = i
    · rw [h, Function.update_same]
      exact h_s_i
    · rw [Function.update_noteq h]
      exact t.valid j

/-- Expected utility of bidder i in a direct revelation mechanism (3.1) -/
noncomputable def bidder_utility
    (direct_mech : DirectMechanism env)
    (i : Fin env.n)
    (t : ValidValue env) : ℝ :=
  bidder_valuation i t.value * direct_mech.p t i - direct_mech.x t i

/-- Expected utility of the seller in a direct revelation mechanism (3.2) -/
noncomputable def seller_utility
    (direct_mech : DirectMechanism env)
    (t₀ : ℝ)
    (t : ValidValue env) : ℝ :=
  seller_valuation t₀ t.value * (1 - ∑ i, direct_mech.p t i) + ∑ i, direct_mech.x t i

/-- Individual rationality condition (3.4) -/
def individual_rational (direct_mech : DirectMechanism env) : Prop :=
  ∀ i t, bidder_utility direct_mech i t ≥ 0

/-- Incentive compatibility condition (3.5) -/
def incentive_compatible (direct_mech : DirectMechanism env) : Prop :=
  ∀ i s_i
    (h_s_i : s_i ∈ Set.Icc (env.a i) (env.b i)) t,
    bidder_utility direct_mech i t ≥
    bidder_utility direct_mech i (update_value t i s_i h_s_i)

/-- A feasible mechanism satisfies both IR and IC constraints -/
structure FeasibleMechanism (env : AuctionEnv) extends DirectMechanism env where
  ir : individual_rational toDirectMechanism
  ic : incentive_compatible toDirectMechanism

/-- Feasibility conditions for general mechanisms -/
structure IsFeasibleGeneralMechanism : Prop where
  /-- Individual rationality for general mechanism -/
  ir : ∀ i t,
    general_mechanism_utility mech i t ≥ 0
  /-- Nash equilibrium condition -/
  nash_equilibrium : ∀ i  s_i
    (h_s_i : s_i ∈ Set.Icc (env.a i) (env.b i)) t,
    general_mechanism_utility mech i t ≥
    general_mechanism_utility mech i (update_value t i s_i h_s_i)

/-- The Revelation Principle (Lemma 3.1) -/
theorem revelation_principle (h_feas : IsFeasibleGeneralMechanism mech) :
    ∃ (m : FeasibleMechanism env),
      ∀ i t,
        bidder_utility m.toDirectMechanism i t = general_mechanism_utility mech i t := by
  -- Construct the direct revelation mechanism
  let direct_p : ValidValue env → Fin env.n → ℝ := fun t i ↦
    mech.p (apply_strategies mech t) i
  let direct_x : ValidValue env → Fin env.n → ℝ := fun t i ↦
    mech.x (apply_strategies mech t) i

  have p_nonneg : ∀ t i, direct_p t i ≥ 0 := by
    intro t i
    exact mech.p_nonneg (apply_strategies mech t) i

  have p_sum_le_one : ∀ t, ∑ i, direct_p t i ≤ 1 := by
    intro t
    exact mech.p_sum_le_one (apply_strategies mech t)

  let direct_mech : DirectMechanism env := {
    p := direct_p
    x := direct_x
    p_nonneg := p_nonneg
    p_sum_le_one := p_sum_le_one
  }

  -- Prove utilities are equal under truthful reporting
  have utility_eq : ∀ i t,
      bidder_utility direct_mech i t = general_mechanism_utility mech i t := by
    intro i t
    unfold bidder_utility general_mechanism_utility
    simp only [direct_p, direct_x]


  -- Prove individual rationality
  have ir : individual_rational direct_mech := by
    intro i t
    rw [utility_eq]
    exact h_feas.ir i t

  -- Prove incentive compatibility
  have ic : incentive_compatible direct_mech := by
    intro i s_i h_s_i t
    rw [utility_eq]
    have h := h_feas.nash_equilibrium i s_i h_s_i t
    exact h

  -- Construct the feasible mechanism
  let m : FeasibleMechanism env := {
    toDirectMechanism := direct_mech
    ir := ir
    ic := ic
  }

  -- Show existence with utility equivalence
  use m


end DirectRevelationMechanisms

end Auction
