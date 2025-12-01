import Mathlib

/- If A bids lower then, A wins the contract  -/
abbrev utilityA(cA cB : ℚ)(bA bB : ℚ) :ℚ :=
  if bA < bB then bB - cA else 0

theorem truthful_bidding_dominates (bA bB : ℚ) :
  ∀ bA bB, utilityA cA cB cA bB ≥  utilityA cA cB bA bB := by
  sorry
