import Mathlib

/-!
  Define the utility function for bidder A:
  If A bids lower than B, A wins the contract and gains (bB - cA).
  Otherwise, A gets 0 utility.
-/
abbrev utilityA (cA cB : ℚ) (bA bB : ℚ) : ℚ :=
  if bA < bB then bB - cA else 0

/-!
  Prove that truthful bidding (bidding one's cost) is a weakly dominant strategy:
  That is, bidding one's true cost `cA` always yields at least as much utility as any other bid `bA`.
-/
theorem truthful_bidding_dominates (cA cB bA bB : ℚ) :
  utilityA cA cB cA bB ≥ utilityA cA cB bA bB := by
  dsimp [utilityA]  -- Unfold the definition of utilityA
  split_ifs <;> linarith
