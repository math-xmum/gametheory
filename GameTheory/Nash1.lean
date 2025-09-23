import Mathlib
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Strict
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Algebra.Affine
import Mathlib.Topology.Algebra.Module.Basic


import GameTheory.Simplex1

open Classical
open BigOperators
open Function

noncomputable section


/-
A game is a set of maps g^i : Πᵢ S i → ℝ
-/
structure Game where
    I : Type*           -- The set of player
    --deEqI : DecidableEq I := inferInstance -- Decidable Eq
    HI : Inhabited I     -- at least one player
    SS : I → Type*       -- S is the set of strategies
    HSS (i :I) : Inhabited (SS i) -- The set of strategies is nonempty
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
abbrev mixedS  := (i : G.I) → stdSimplex ℝ (G.SS i)

def mixed_g (i : G.I) (m : Π i, S (G.SS i) ) : ℝ := ∑ s : (Π j, G.SS j) , (∏ j,  m j (s j)) * (G.g i s)

#print mixed_g


lemma mixed_g_linear : G.mixed_g i (update  x i y) = ∑ s : G.SS i, y s * G.mixed_g i (update x i (stdSimplex.pure s)) := by sorry




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
  ∀ (i:G.I), ∀ (y : S (G.SS  i)),
     G.mixed_g i x ≥ G.mixed_g i (update  x i y)



end FinGame

section Brouwer.mixedGame
variable {G : FinGame}


theorem Brouwer.mixedGame (f : G.mixedS → G.mixedS) (hf : Continuous f) : ∃ x : G.mixedS, f x = x := by sorry

end Brouwer.mixedGame

section mixedNashEquilibrium
variable (G : FinGame)
open FinGame

/-noncomputable def evaluate_at_mixed (i : G.I) (σ : G.mixedS) : ℝ :=
  ∑ pureS : (Π i, G.SS i), (∏ i : G.I, σ i (pureS i)) * G.g i pureS

lemma mixed_g_eq_evaluate (i : G.I) (σ : G.mixedS) : evaluate_at_mixed G i σ = mixed_g i σ := by
  simp [evaluate_at_mixed, mixed_g]

  sorry-/



variable {G}

noncomputable abbrev g_function (i : G.I) (σ : G.mixedS) (a : G.SS i) : ℝ :=
  σ i a + max 0 (mixed_g i (Function.update σ i (stdSimplex.pure a)) - mixed_g i σ)


lemma sigma_le_g_function (i : G.I) (σ : G.mixedS) (a : G.SS i) : σ i a ≤ g_function i σ a := by
  rw [g_function]; norm_num

lemma g_function_noneg (i : G.I) (σ : G.mixedS) (a : G.SS i) : 0 ≤ g_function i σ a := by
  have h1: 0 ≤ σ i a:= (σ i).2.1 a
  linarith [sigma_le_g_function i σ a]

--variable (sigma : G.mixedS ) (i : G.I) (a : G.SS i)

lemma one_le_sum_g (i : G.I) (σ : G.mixedS) : 1 ≤ ∑ b : G.SS i, g_function i σ b := by
  calc
  _ = ∑ b : G.SS i, σ i b := Eq.symm (σ i).2.2
  _ ≤ _ := Finset.sum_le_sum (by norm_num [sigma_le_g_function i σ])


noncomputable abbrev nash_map_aux (σ : G.mixedS) (i : G.I) (a : G.SS i) : ℝ :=
  g_function i σ a / ∑ b : G.SS i, g_function i σ b

lemma nash_map_cert (σ : G.mixedS) (i : G.I) :
  (nash_map_aux σ i) ∈ S (G.SS i) := by
  unfold nash_map_aux
  constructor
  · intro x;
    apply div_nonneg <| g_function_noneg i σ x
    linarith [one_le_sum_g i σ]
  · rw [<-Finset.sum_div]
    apply div_self
    linarith [one_le_sum_g i σ]


variable (G)

noncomputable def nash_map (σ: G.mixedS) : G.mixedS :=
  fun (i : G.I) ↦ ⟨nash_map_aux σ i, nash_map_cert σ i⟩

lemma cg : Continuous fun a => g_function (G:=G) i a s := by
  unfold g_function
  apply Continuous.add
  · let f : G.mixedS → stdSimplex ℝ (G.SS i) := fun σ => σ i
    let g : stdSimplex ℝ (G.SS i) → ℝ := fun a => a s
    have hfg: g ∘ f = fun σ => σ i s := by
      ext σ; rfl
    rw [<-hfg]
    apply Continuous.comp
    · have hgg : g =  (fun a => a s) ∘ (fun a => a.1)  := rfl
      rw [hgg]
      apply Continuous.comp
      · apply continuous_apply
      · continuity
    · continuity

  · apply Continuous.max
    · continuity
    · unfold mixed_g
      apply Continuous.sub
      · apply continuous_finset_sum
        intro i' _
        apply Continuous.mul
        · apply continuous_finset_prod
          intro i'' _
          by_cases h : i'' = i
          · rw [h]
            continuity
          · simp only [ne_eq, h, not_false_eq_true, update_noteq]
            have : (fun (a : G.mixedS) => (a i'') (i' i'')) = (fun f => f (i' i'')) ∘ Subtype.val ∘ fun a => a i'' := by
              rfl
            rw [this]
            apply Continuous.comp
            continuity
            apply Continuous.comp <;> continuity
        · continuity
      · apply continuous_finset_sum
        intro i' _
        apply Continuous.mul
        · apply continuous_finset_prod
          intro i'' _
          by_cases h : i'' = i
          · have : (fun (a : G.mixedS) => (a i) (i' i)) = (fun f => f (i' i)) ∘ Subtype.val ∘ fun a => a i := by
              rfl
            rw [h]
            rw [this]
            apply Continuous.comp
            continuity
            apply Continuous.comp <;> continuity
          · have : (fun (a : G.mixedS) => (a i'') (i' i'')) = (fun f => f (i' i'')) ∘ Subtype.val ∘ fun a => a i'' := by
              rfl
            rw [this]
            apply Continuous.comp
            continuity
            apply Continuous.comp <;> continuity
        · continuity


lemma nash_map_cont : Continuous $ nash_map G :=
  by
  unfold nash_map
  unfold nash_map_aux
  apply continuous_pi
  intro i
  apply Continuous.subtype_mk
  apply continuous_pi
  intro s
  apply Continuous.div
  · apply cg
  · apply continuous_finset_sum
    intro i _; apply cg
  · intro σ
    apply ne_of_gt
    nlinarith [show 1 ≤ ∑ b : G.SS i, g_function i σ b by apply one_le_sum_g i σ]


theorem ExistsNashEq : ∃ σ : G.mixedS , mixedNashEquilibrium σ := by {
  obtain ⟨σ, hs⟩ := Brouwer.mixedGame (nash_map G)  (nash_map_cont G)
  use σ
  intro i y
  by_cases H : ∀ t, G.mixed_g i σ  ≥ G.mixed_g i (update σ i (stdSimplex.pure t))
  · have h1 : ∃ t : G.SS i, mixed_g i (update σ i (stdSimplex.pure t)) ≥  mixed_g i (update σ i y) := by
      have h1 : G.mixed_g i (update  σ i y) = ∑ s : G.SS i, y s * G.mixed_g i (update σ i (stdSimplex.pure s)) := by apply mixed_g_linear
      rw [h1]
      obtain ⟨t,ht⟩ := Finite.exists_max (fun s => G.mixed_g i (update σ i (stdSimplex.pure s)))
      use t
      simp
      have : ∑ s : G.SS i, y s * G.mixed_g i (update σ i (stdSimplex.pure s))
             ≤ ∑ s : G.SS i, y s * G.mixed_g i (update σ i (stdSimplex.pure t)) := by
        apply Finset.sum_le_sum
        intro s _
        apply mul_le_mul_of_nonneg_left (ht s)
        have : 0 ≤ y s := (y).2.1 s
        exact this

      have h2 : ∑ s : G.SS i, y s  = 1 := by
        exact (y).2.2

      rw [← Finset.sum_mul, h2] at this
      simp at this
      exact this
    obtain ⟨t, ht⟩ := h1
    specialize H t
    nlinarith

  · exfalso -- This case cannot happen
    push_neg at H
    obtain ⟨t,ht⟩ := H
    have H1 :  1 < ∑ b, g_function i σ b := by
      have h1 : 1 ≤ ∑ b : G.SS i, g_function i σ b := by
        apply one_le_sum_g i σ
      have h2 : 1 ≠ ∑ b : G.SS i, g_function i σ b := by
        intro h2
        replace h2 : ∑ b : G.SS i, σ i b  = ∑ b : G.SS i,   g_function  i σ b := by
          have h3 : 1 = ∑ b : G.SS i, σ i b := Eq.symm (σ i).2.2
          rw [h3] at h2
          exact h2
        unfold g_function at h2
        replace h2 : ∑ s : G.SS i, max 0 (mixed_g i (update σ i (stdSimplex.pure s)) - mixed_g i σ) = 0 := by
          rw [Finset.sum_add_distrib] at h2
          linarith
        replace h2 : mixed_g i (update σ i (stdSimplex.pure t)) - mixed_g i σ ≤ 0 := by
          by_cases h :  ∀ s : G.SS i, mixed_g i (update σ i (stdSimplex.pure s)) - mixed_g i σ ≤ 0
          · specialize h t
            simp at h
            simp
            exact h
          · exfalso
            simp at h
            obtain ⟨s, hs⟩:= h
            have h3 : max 0 (mixed_g i (update σ i (stdSimplex.pure s)) - mixed_g i σ) = mixed_g i (update σ i (stdSimplex.pure s)) - mixed_g i σ := by simp; nlinarith
            have h4: ∀ s : G.SS i , 0 ≤ max 0 (mixed_g i (update σ i (stdSimplex.pure s)) - mixed_g i σ) := by
                intro s
                simp
            have h5 : ∑ s : G.SS i, max 0 (mixed_g i (update σ i (stdSimplex.pure s)) - mixed_g i σ) > 0 := by
              have f : mixed_g i (update σ i (stdSimplex.pure s)) - mixed_g i σ ≤ ∑ s : G.SS i, max 0 (mixed_g i (update σ i (stdSimplex.pure s)) - mixed_g i σ) := by
                rw [← h3]
                set g :G.SS i → ℝ := fun s => max 0 (mixed_g i (update σ i (stdSimplex.pure s)) - mixed_g i σ)
                have h6 : g s = max 0 (mixed_g i (update σ i (stdSimplex.pure s)) - mixed_g i σ) := by rfl
                rw [←h6]
                apply Finset.single_le_sum
                replace h4 : ∀  s : G.SS i, 0 ≤ g s := by
                  simp [g]
                norm_num
                · apply h4
                · simp
              nlinarith
            nlinarith
        nlinarith
      rw [lt_iff_le_and_ne]
      exact ⟨h1, h2⟩
    have H2 : ∑ s, σ i s * G.mixed_g i (update σ i (stdSimplex.pure s)) =
      G.mixed_g i σ := by
      rw [← mixed_g_linear]
      simp
      -- have H2: G.mixed_g i (update σ i (σ i)) = G.mixed_g i σ  := by sorry\
    obtain ⟨s,hs1,hs2⟩:= stdSimplex.wsum_magic_ineq H2
    have : σ i s = σ i s / (∑ b : G.SS i, g_function i σ b) := by
      nth_rw 1 [<-hs]
      calc
      _ = nash_map_aux σ i s := by rw [nash_map];rfl
      _ = _ := by
        rw [nash_map_aux,g_function]
        have : max 0 (mixed_g i (update σ i (stdSimplex.pure s)) - mixed_g i σ)  = 0 := by
          simp
          apply hs2
        rw [this];norm_num
    have self_div_lemma {x y : ℝ} : x ≠ 0 → x = x/y →  y = 1 := by
      intro h1 h2
      rw [eq_div_iff_mul_eq ] at h2
      replace h2 : y = x / x := by
        rw [mul_comm, ← eq_div_iff] at h2
        linarith
        apply h1
      rw [div_self (show x ≠ 0 by apply h1)] at h2
      exact h2
      intro H'
      replace h2 : x=0 := by rw [h2,H'];simp
      exact h1 h2
    have := self_div_lemma (by linarith) this
    linarith
}

end mixedNashEquilibrium
