import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses


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
  have h1 : Set.Iic x ⊆ Set.Iic y := by exact Set.Iic_subset_Iic.mpr hxy
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
      exact OuterMeasureClass.measure_mono (env.μ i) fun ⦃a⦄ a => trivial
    -- rw [h] at h2
    simp [h] at h2 --这个类型转换怎么搞
    exact h2
    have h3 : env.μ i (Set.Iic t) ≠ ⊤ := by
      exact ne_of_lt (measure_lt_top (env.μ i) (Set.Iic t))
    apply ENNReal.toReal_mono h3 h2

/-- F tends to 0 at -∞ -/
theorem F_tendsto_atBot (i : Fin env.n) :
  Filter.Tendsto (F env i) Filter.atBot (nhds 0) := by
  unfold F
  apply squeeze_zero
  · intro t
    exact ENNReal.toReal_nonneg
  · intro t
    apply Preorder.le_refl
  · intro t innhd
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
  (env.μ i (Set.Iic t)) ≤ 1 := by sorry
  -- exact MeasureTheory.IsProbabilityMeasure.le_one (env.μ_probability i)

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
  (t : ValueSpace env)
  (h_bounds : ∀ j, t j ∈ Set.Icc (env.a j) (env.b j)) :
  bidder_valuation i t = t i + ∑ j in (Finset.univ.erase i), env.e j (t j) := by
  rfl

/-- Relationship between bidder and seller valuations -/
theorem bidder_seller_valuation_relation
  {env : AuctionEnv}
  (t₀ : ℝ)
  (t : ValueSpace env)
  (i : Fin env.n)
  (h_bounds : ∀ j, t j ∈ Set.Icc (env.a j) (env.b j)) :
  seller_valuation t₀ t - bidder_valuation i t = t₀ - t i + env.e i (t i) := by
  simp [seller_valuation, bidder_valuation]
  sorry

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
theorem revelation_principle
    (h_feas : IsFeasibleGeneralMechanism mech) :
    ∃ (m : FeasibleMechanism env),
      ∀ i t_i (h_t_i : t_i ∈ Set.Icc (env.a i) (env.b i)) t,
        bidder_utility m.toDirectMechanism i t = general_mechanism_utility mech i t_i h_t_i t := by
  -- Construct the direct revelation mechanism
  let direct_p : ValidValue env → Fin env.n → ℝ := fun t i ↦
    mech.p (apply_strategies mech t) i
  let direct_x : ValidValue env → Fin env.n → ℝ := fun t i ↦
    mech.x (apply_strategies mech t) i
  -- We need to show this construction yields a feasible mechanism
  sorry

end DirectRevelationMechanisms

end Auction
