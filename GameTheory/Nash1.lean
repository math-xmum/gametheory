import Mathlib
import GameTheory.Simplex1

open Classical
open BigOperators

/-
A game is a set of maps g^i : Πᵢ S i → ℝ
-/
structure Game where
    I : Type*           -- The set of player
    HI : Inhabited I     -- at least one player
    SS : I → Type*       -- S is the set of strategies
    HSS (i :I): Inhabited (SS i) -- The set of strategies is nonempty
    g : I → (Π i, SS i) →  ℝ
    -- an elements in Π i, SS is a move of all players.
    -- g i is the payoff of the i-th player

attribute [instance] Game.HI Game.HSS

namespace Game

variable {G : Game}

def NashEquilibrium (x : (Π i, G.SS i)) :=
  ∀ (i : G.I)
    (y : Π i, G.SS i ),
    (∀ j : G.I, i ≠ j → (x j = y j) ) →
     G.g i x ≥ G.g i y

instance {G: Game} {i : G.I}: Inhabited (G.SS i) := G.HSS i

end Game

open Game

structure FinGame extends Game where
  FinI : Fintype I
  FinSS : ∀ i : I , Fintype (SS i)

attribute [instance] FinGame.FinI FinGame.FinSS


namespace FinGame


instance {G : FinGame} : Fintype G.I := G.FinI
instance {G : FinGame} {i : G.I}: Fintype (G.SS i) := G.FinSS i
noncomputable instance mixed_SS_i_Inhabited {G: FinGame} {i : G.I}: Inhabited (S (G.SS i)) := inferInstance

@[simp]
abbrev mixedSSi (G : FinGame) (i : G.I) := S (G.SS i)

@[simp]
abbrev mixedS (G : FinGame) := (i:G.I) → S (G.SS i)

/-
@[simp]
noncomputable def with_hole {G: FinGame} (s : G.mixedS) (i : G.I) (x : S (G.SS i)) := Function.update G.I (fun i =>S (G.SS i)) s i x

-- comma_notation for mixed game
noncomputable instance comma.mixed {G : FinGame} {i : G.I} : CoeOut  ((S (G.SS i))×(@IFun' G.I (fun i => S (G.SS i )) i)) (IFun (fun i => S (G.SS i))) where
  coe := @combinePair G.I (fun i=> S (G.SS i)) i
-/

noncomputable def mixed_g {G: FinGame} (i : G.I) (x : Π i, S (G.SS i) ) : ℝ := ∑ s : (Π j, G.SS j) , ∏ j,  x j (s j) * (G.g i s)


def mixedNashEquilibrium {G: FinGame} (x : G.mixedS) :=
  ∀ (i:G.I)
    (y : G.mixedS ),
    (∀ j: G.I, i ≠ j → (x j = y j) ) →
     G.mixed_g i x ≥ G.mixed_g i y

end FinGame

section Brouwer.mixedGame
variable {G : FinGame}


theorem Brouwer.mixedGame (f : G.mixedS → G.mixedS) (hf : Continuous f) : ∃ x : G.mixedS, f x = x := sorry

end Brouwer.mixedGame

section mixedNashEquilibrium
variable (G : FinGame)
open FinGame

/-noncomputable def evaluate_at_mixed (i : G.I) (σ : G.mixedS) : ℝ :=
  ∑ pureS : (Π i, G.SS i), (∏ i : G.I, σ i (pureS i)) * G.g i pureS

lemma mixed_g_eq_evaluate (i : G.I) (σ : G.mixedS) : evaluate_at_mixed G i σ = mixed_g i σ := by
  simp [evaluate_at_mixed, mixed_g]

  sorry-/


noncomputable def mixed_strategy_of_pure (i : G.I) (a : G.SS i) : S (G.SS i) := by
  let f := fun t ↦ if t = a then (1 : ℝ) else 0
  use f
  refine And.intro ?_ ?_
  aesop
  simp

noncomputable def g_function (i : G.I) (σ : G.mixedS) (a : G.SS i) : ℝ :=
  σ i a + max 0 (mixed_g i (Function.update σ i (mixed_strategy_of_pure G i a)) - mixed_g i σ)

variable (sigma : G.mixedS ) (i : G.I) (a : G.SS i)
--#check evaluate_at_mixed G i sigma
--#check (sigma i a) --G.g i (sigma i) (a)

noncomputable def mixed_strategy (σ : G.mixedS) (i : G.I) (a : G.SS i) : ℝ :=
  g_function G i σ a / ∑ b : G.SS i, g_function G i σ b
   --G.g i / Fintype.sum

--variable (σ : G.mixedS) (i : G.I)
--#check mixed_strategy G σ i
-- certificate: nonneg, sum to 1

--lemma g_function_nonneg (σ : G.mixedS)

#check map_sum
#check Finset.mul_sum
#check div_eq_mul_inv
#check ENNReal.ofReal
#check ENNReal.toReal
#check ENNReal.ofReal_toReal

lemma mixed_strategy_simplex_cert (σ : G.mixedS) (i : G.I) : (mixed_strategy G σ i) ∈ S'' (G.SS i) := by
  simp [S'', mixed_strategy] -- g_function, mixed_g
  constructor
  · intro h
    sorry
  · --rw [Real.inv]
    let g : ℝ →+ ℝ := by
      have hom : ZeroHom ℝ ℝ := by
        refine ⟨fun x ↦ x / ∑ b : G.SS i, g_function G i σ b, ?_⟩
        simp
      refine ⟨hom, fun x y ↦ ?_⟩
      have (t : ℝ) : hom.toFun t = t / ∑ b : G.SS i, g_function G i σ b := by
        sorry
      simp_rw [this]
      field_simp
    calc
      _ = ∑ b : G.toGame.SS i, g (g_function G i σ b) := by
        rfl
      _ = _ := by
        have := @map_sum _ (G.SS i) _ _ _ _ _ _ g (fun a ↦ g_function G i σ a) Finset.univ
        rw [← this]
        field_simp
        apply Real.

  -- // (∀ i:α, 0 ≤ x i)  ∧  Finset.sum Finset.univ x = 1}

noncomputable def f_function (σ: G.mixedS) : G.mixedS :=
  fun (i : G.I) ↦ ⟨mixed_strategy G σ i, mixed_strategy_simplex_cert G σ i⟩

theorem ExistsNashEq : ∃ x : G.mixedS , mixedNashEquilibrium x := by {


  sorry
}

end mixedNashEquilibrium
