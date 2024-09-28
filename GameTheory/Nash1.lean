import Mathlib
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Strict
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Algebra.Affine
import Mathlib.Topology.Algebra.Module.Basic


import GameTheory.Simplex1

open Classical
open BigOperators


noncomputable section


/-
A game is a set of maps g^i : Πᵢ S i → ℝ
-/
structure Game where
    I : Type*           -- The set of player
    --deEqI : DecidableEq I := inferInstance -- Decidable Eq
    HI : Inhabited I     -- at least one player
    SS : I → Type*       -- S is the set of strategies
    HSS (i :I): Inhabited (SS i) -- The set of strategies is nonempty
    --deEqSS (i : I) : DecidableEq (SS i)
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
variable {G : FinGame}

instance {G : FinGame} : Fintype G.I := G.FinI
instance {G : FinGame} {i : G.I}: Fintype (G.SS i) := G.FinSS i
--instance mixed_SS_i_Inhabited {G: FinGame} {i : G.I}: Inhabited (S (G.SS i)) := inferInstance

variable (G) in
abbrev mixedS  := Π i, stdSimplex ℝ (G.SS i)

def mixed_g (i : G.I) (m : Π i, S (G.SS i) ) : ℝ := ∑ s : (Π j, G.SS j) , ∏ j,  m j (s j) * (G.g i s)


def FinGame2MixedGame (G : FinGame) : Game := {
  I := G.I
  HI := G.HI
  SS := fun i => S (G.SS i)
  HSS := inferInstance
  /-
  Let m be the mixed strategy, then m j (s j) is the probabilty
  of j-th player take the strategy (s j), the actural probability for taking the strategy s is the product probability
  -/
  g := mixed_g
}

-- Let μ denote the mixed Game
notation:999 "μ" rhs:60 => (FinGame2MixedGame rhs)

variable (G : FinGame)


theorem ExistsNashEq : ∃ m :  (i:(μ G).I )→ (μ G).SS i, (μ G).NashEquilibrium m := by sorry



/-
@[simp]
noncomputable def with_hole {G: FinGame} (s : G.mixedS) (i : G.I) (x : S (G.SS i)) := Function.update G.I (fun i =>S (G.SS i)) s i x

-- comma_notation for mixed game
noncomputable instance comma.mixed {G : FinGame} {i : G.I} : CoeOut  ((S (G.SS i))×(@IFun' G.I (fun i => S (G.SS i )) i)) (IFun (fun i => S (G.SS i))) where
  coe := @combinePair G.I (fun i=> S (G.SS i)) i
-/


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

variable {G} in
noncomputable abbrev g_function (i : G.I) (σ : G.mixedS) (a : G.SS i) : ℝ :=
  σ i a + max 0 (mixed_g i (Function.update σ i (stdSimplex.pure a)) - mixed_g i σ)

lemma g_function_noneg (i : G.I) (σ : G.mixedS) (a : G.SS i) : 0 ≤ g_function i σ a := by
  rw [g_function]
  calc
    _ ≤ σ i a :=(σ i).2.1 a
    _ = σ i a + 0 := by simp
    _ ≤ _ := by apply add_le_add_left; simp

--variable (sigma : G.mixedS ) (i : G.I) (a : G.SS i)

variable {G} in
noncomputable def nash_map_aux (σ : G.mixedS) (i : G.I) (a : G.SS i) : ℝ :=
  g_function i σ a / ∑ b : G.SS i, g_function i σ b

variable {G} in
lemma nash_map_cert (σ : G.mixedS) (i : G.I) : (nash_map_aux σ i) ∈ S (G.SS i) := by
  sorry


noncomputable def nash_map (σ: G.mixedS) : G.mixedS :=
  fun (i : G.I) ↦ ⟨nash_map_aux σ i, nash_map_cert σ i⟩

theorem ExistsNashEq : ∃ x : G.mixedS , mixedNashEquilibrium x := by {


  sorry
}

end mixedNashEquilibrium
