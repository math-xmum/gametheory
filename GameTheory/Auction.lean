import Mathlib.Data.Real.EReal
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Lattice

open Classical

/-- An auction consists of a finite nonempty set of bidders I, together with
their valuations. -/
structure Auction where
  -- I is the set of agents
  I : Type*
  -- We require I to be finite
  hF : Fintype I
  -- We require I to be non-empty
  hN : Nonempty I
  -- v is the valuation of each client
  v : I → ℝ

namespace Auction

/- Throughout this document let `a` denote an auction,
and `b` denote the bids by each agent -/
variable {a : Auction} (b : a.I → ℝ)

instance : Fintype a.I := a.hF
instance : Nonempty a.I := a.hN

--Helper Functions and Definitions

/-- a.max returns the highest bid given a bidding function b. -/
@[simp]
def max : ℝ := Finset.sup' (Finset.univ) (Finset.univ_nonempty) b

/-- There exists a participant i whose bid equals the highest bid. -/
lemma exists_max : ∃ i : a.I, b i = a.max b := by
  obtain ⟨i, _, h2⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty b
  exact ⟨i, symm h2⟩

/-- The winner of the auction is the participant with the highest bid. -/
noncomputable def winner : a.I := choose (exists_max b)

/-- The bid of the winner equals the highest bid. -/
lemma winner_take_max : b (winner b) = max b := choose_spec (exists_max b)

section second_price_strategy
/-- If there are at least two agents,
removing one still leaves a non-empty set. -/
lemma delete_i_nonempty (i : a.I) (htwo : Nontrivial a.I)
  : Finset.Nonempty (Finset.erase Finset.univ i) := by
  let ⟨x, y, diff⟩ := htwo
  have hx : x ∈ Finset.univ := Finset.mem_univ x
  have hy : y ∈ Finset.univ := Finset.mem_univ y
  simp; use x, hx, y, hy;

-- Henceforth assume that `a.I` has at least two elements
variable [htwo : Nontrivial a.I]

/-- returns the maximal bid of all but i. -/
noncomputable def max_without_i (i: a.I) : ℝ :=
  Finset.sup' (Finset.erase Finset.univ i) (delete_i_nonempty i htwo) b

/-- The second highest bid, i.e. the highest bid excluding the winner’s bid. -/
noncomputable def second_price: ℝ := max_without_i b (winner b)

/-- The utility of participant i, which is their valuation minus the second
highest bid if i is the winner, or 0 otherwise. -/
noncomputable def utility (i : a.I) : ℝ :=
   if i = winner b then a.v i - second_price b else 0


--Proofs and Lemmas

/-- If i is the winner then their utility is their valuation minus
the second highest bid. -/
lemma utility_winner (i : a.I) (H : i = winner b)
  : utility b i = a.v i - second_price b :=
  by rw [utility]; simp only [ite_true, H]

/-- If i is not the winner, then their utility is 0. -/
lemma utility_loser (i : a.I) (H : i ≠ winner b) : utility b i = 0 :=
  by rw [utility]; simp only [ite_false, H]

/-- A dominant strategy for `i` is a strategy (i.e., a bid `bi`)
that is guaranteed to maximize `i`’s utility, no matter what the other
bidders do; in other words, for any bids `b` and `b'` such that `b i = bi`,
the utility from `b` should be not less than that of `b'` -/
@[simp]
def dominant (i : a.I) (bi : ℝ) : Prop :=
  ∀ b b': a.I → ℝ, b i = bi → (∀ j: a.I, j ≠ i → b j = b' j) →
  utility b i ≥ utility b' i

/-- Suppose that `i` bids strictly higher than anyone else, then
`i` wins the bid. -/
lemma gt_wins (i : a.I) (H: ∀ j, i ≠ j → b i > b j) : i = winner b := by
  -- check that b i ≤ max b by definition of max
  have hgt : b i ≤ max b := by apply Finset.le_sup'; exact Finset.mem_univ i
  -- check that b i ≥ max b by definition of b
  have hlt : b i ≥ max b := by
    apply Finset.sup'_le
    intro j _
    by_cases hh : i = j
    { rw [hh] } -- if i = j
    { push_neg at hh; specialize H j hh; linarith } -- if i ≠ j
  have heq : b i = max b := by linarith
  have HH (j : a.I): i = j ↔ b j = max b := by
   constructor
   { intro z; rw [z] at heq; assumption }
   { contrapose; push_neg; intro hj; specialize H j hj; linarith }
  rw [HH, ← winner_take_max]

/-- The bid of the winner is always greater than or equal to the bids
of all other participants. -/
lemma b_winner_max (H: i = winner b) : ∀ j : a.I, b i ≥ b j := by
  intro j
  have H_max : b (winner b) = max b := winner_take_max b
  rw [← H] at H_max
  have H_sup : b j ≤ max b
  { apply Finset.le_sup'; simp only [Finset.mem_univ] }
  rwa [H_max]

/-- The bid of the winner is always greater than or equal to
the second highest bid. -/
lemma b_winner_ge_next (H: i = winner b) : b i ≥ max_without_i b i := by
  have Hmax := winner_take_max b
  rw [← H] at Hmax
  rw [Hmax]
  apply Finset.sup'_le
  intro j
  intro _
  apply Finset.le_sup'
  simp only [Finset.mem_erase,Finset.mem_univ]


/-- The bid of the winner is always greater than or equal to the
second highest bid. -/
lemma b_winner (H: i = winner b) : b i ≥ second_price b := by
  rw [H, second_price, max_without_i]
  apply Finset.sup'_le
  intro j _
  rw [winner_take_max b]
  apply Finset.le_sup'
  simp only [Finset.mem_erase, Finset.mem_univ]

/-- If i is not the winner, then the highest bid excluding i
is equal to the overall highest bid. -/
lemma b_loser_max (H: i ≠  winner b) : max_without_i b i = max b := by
  have H1 : max_without_i b i ≤ max b := by
    apply Finset.sup'_le
    intro i _
    apply Finset.le_sup'
    simp only [Finset.mem_univ]
  have H2 : max b ≤ max_without_i b i := by
    rw [<-winner_take_max b]
    apply Finset.le_sup'
    simp only [Finset.mem_univ, Finset.mem_erase, and_true]
    exact (Ne.symm H)
  linarith


-- TODO: lemma b_loser' (H: i ≠  winner b) : b i ≤ max_without_i b i
-- TODO: lemma b_loser (H: i ≠  winner b) : b i ≤ second_price b

/-- In a second-price auction,
every truthful bidder is guaranteed nonnegative utility. -/
lemma utility_nneg (i: a.I) : (b i = a.v i) → utility b i ≥ 0 := by
  intro H
  by_cases H2 : i = winner b
  { rw [utility]
    simp only [H2, if_true]
    rw[← H2, ← H, H2, winner_take_max b]
    apply sub_nonneg.mpr
    rw [second_price]
    apply Finset.sup'_le
    simp only [Finset.mem_univ, Finset.mem_erase, and_true]
    intro j _
    rw [max]
    simp only [Finset.le_sup'_iff, Finset.mem_univ, true_and]
    use j }
  { rw [utility, if_neg H2] }

/-- A dominant strategy is bidding your whole valuation -/
theorem valuation_is_dominant (i : a.I) : dominant i (a.v i) := by
  intro b b' hb hb'
  by_cases H : i = winner b'
  { by_cases H1 : a.v i > max_without_i b' i
    { -- Show that i is also the winner for bidding b
      -- Show that secondprice b  = secondprice b'
      -- Show that utility b i = utility b' i
      have h_winner_b : i = winner b := gt_wins b i (λ j hj => by {
      rw[hb]
      rw[hb']
      --对于所有 j ≠ i，b i = a.v i > b' j = b j
      have HBi: max_without_i b' i ≥  b' j := by
        rw [max_without_i]
        simp only [Finset.mem_univ, not_true, ge_iff_le, Finset.le_sup'_iff,
         Finset.mem_erase, ne_eq, and_true]
        use j
        simp only [le_refl, and_true]
        rw [<-ne_eq,ne_comm]
        exact hj

      exact gt_of_gt_of_ge H1 HBi
      exact id (Ne.symm hj) } )
      rw [utility_winner b _ h_winner_b]
      rw [utility_winner b' _ H]
      -- Show that secondprice b  = secondprice b'
      have h_secondprice_eq : second_price b = second_price b' := by {
        repeat rw [second_price]
        rw[← h_winner_b, ← H]
        repeat rw [B]
        apply Finset.sup'_congr (delete_i_nonempty i htwo) (rfl)
        intro j hj
        rw [Finset.mem_erase] at hj
        exact hb' j hj.1
      }
      rw [h_secondprice_eq] }
    { rw [ge_iff_le,utility,<-H]
      simp only [ite_true, ge_iff_le, tsub_le_iff_right]
      simp only [gt_iff_lt, not_lt] at H1
      rw [second_price,<-H]
      have := utility_nneg b i hb
      linarith } }
  { have := utility_nneg b i hb
    convert this
    simp [utility,H] }

#check valuation_is_dominant

end second_price_strategy


section first_price_strategy
/-- Under the first price strategy, the utility is 0
if an agent loses the bid, and `a.v i - b i` otherwise. -/
noncomputable def utility_first_price (i : a.I) : ℝ :=
  if i = winner b then a.v i - b i else 0

/-- The winner has utility  `a.v i - b i` -/
lemma utility_first_price_winner (i : a.I) (H : i = winner b) :
  utility_first_price b i = a.v i - b i := by
  rw[H]
  simp only [utility_first_price, if_true]

/-- Losers have utility 0. -/
lemma utility_first_price_loser (i : a.I) (H : i ≠ winner b) :
  utility_first_price b i = 0 := by
  rw [utility_first_price]
  simp only [H, if_false]

/-- Definition of dominant strategy, in a first pric strategy setting. -/
def dominant_first_price (i : a.I) (bi : ℝ) : Prop :=
  ∀ b b': a.I → ℝ, (b i = bi) → (∀ j : a.I, j ≠ i → b j = b' j)
  → utility_first_price b i ≥ utility_first_price b' i

/-- There are no dominant strategies in first price strategy settings. -/
theorem first_price_no_dominant_strategy (i : a.I) (bi :  ℝ) :
  ¬ (dominant_first_price i bi) := by
  simp only [dominant_first_price, not_forall]

  let b := fun j => if j = i then (bi : ℝ) else bi - 2
  let b' := fun j => if j = i then (bi - 1 : ℝ) else bi - 2
  use b, b'
  simp only [ne_eq, exists_prop, ite_true, exists_const]
  simp only [true_and]
  constructor
  intro j hj
  simp only [if_false, hj]
  have winner_b : i = winner b := by
    apply gt_wins b i
    intro j hj
    simp [Ne.symm hj]
  have winner_b' : i = winner b' := by
    apply gt_wins b' i
    intro j hj
    simp only [ite_true, Ne.symm hj, ite_false, gt_iff_lt, sub_lt_sub_iff_left]
    linarith

  have h1 := utility_first_price_winner b i winner_b
  have h2 := utility_first_price_winner b' i winner_b'
  simp [h1, h2]

end first_price_strategy

end Auction
