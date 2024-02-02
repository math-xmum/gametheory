import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.EReal
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Finprod
import GameTheory.Simplex

open Classical
open BigOperators

/-
A game is a set of maps g^i : Πᵢ S i → ℝ
-/
structure Game.{u,v} where
    I : Type u           -- The set of player
    HI : Inhabited I     -- at least one player
    SS : I → Type v       -- S is the set of strategies
    HSS : ∀ (i: I), Inhabited (SS i) -- The set of strategies is nonempty
    g : I → (Π i, SS i) →  ℝ
    -- an elements in Π i, SS is a move of all players.
    -- g i is the payoff of the i-th player
#align game Game


namespace Game

variable {G: Game}

def NashEquilibrium (x : (Π i,  G.SS i)) :=
  ∀ (i:G.I)
    (y : Π i, G.SS i ),
    (∀ j: G.I, i≠j → (x j = y j) ) →
     G.g i x ≥ G.g i y

instance {G: Game} {i : G.I}: Inhabited (G.SS i) := G.HSS i

end Game

open Game

namespace aux
universe u v

variable {I:Type u}
variable {f: I → Type v}



/-
@[simp]
noncomputable abbrev lifti {i j:I}  (h : j=i) (x : f i): f j :=  by rw [h]; exact x

variable {i j:I} (h : j=i)

noncomputable example : lifti f (Eq.symm h) (lifti f  h (x : f i)) = x  :=  by simp

-/
@[simp]
abbrev I' (i:I) := {j // j≠ i}

@[simp]
abbrev IFun (f : I → Sort*) :=  (i:I) → f i

@[simp]
abbrev IFun' (f : I → Sort*) (i:I) := (j : I' i) → f j

@[simp]
noncomputable def with_hole (x : IFun f) (i : I) (y: f i) : IFun f :=
fun j =>  if h : j = i then (by rw [h];exact y) else x j


@[simp]
noncomputable def combineSubtypeFun (x : f i) (y : IFun' f i ) : IFun f := fun j =>  (if h : j=i then (by rw [h];exact x) else  y ⟨j, h⟩)

@[simp]
noncomputable def combinePair(b : (f i) × (IFun' f i)) : IFun f := combineSubtypeFun b.1 b.2



attribute [coe] combinePair

noncomputable instance combinePair.general {i : I}: CoeOut ((f i) × (IFun' f i)) (IFun f) where
  coe := combinePair

@[simp]
lemma comma_eval  {x : f i} {y : IFun' f i } : ((x,y): IFun f) i = x := by simp

@[simp]
lemma comma_eval' {i j:I} {x : f i} {y : IFun' f i } :
(h : j≠i) →  ((x,y): IFun f) j = y ⟨j,h⟩  := by intro h; simp [h]



variable (i : I) (b' : I' i → ℝ ) (x : ℝ)

variable {α : Type*}
#check IFun' (fun _ => α) i
#check IFun (fun _ => α)

noncomputable instance combinePair.mono  {i :I}: CoeOut ((α) × (I' i→ α )) (I → α ) where
  coe := @combinePair I (fun _=> α) i

#check ((x,b'): I→ ℝ)


noncomputable instance {G:Game} {i : G.I} : CoeOut  ((G.SS i)×(@IFun' G.I G.SS i)) (IFun G.SS) where
  coe := @combinePair G.I G.SS i


end aux


structure FinGame extends Game where
  FinI : Fintype I
  FinSS : ∀ i:I , Fintype (SS i)


namespace FinGame

open aux


instance {G: FinGame} : Fintype G.I := G.FinI
instance {G: FinGame} {i : G.I}: Fintype (G.SS i) := G.FinSS i
noncomputable instance mixed_SS_i_Inhabited {G: FinGame} {i : G.I}: Inhabited (S (G.SS i)) := S.SInhabited_of_Inhabited

@[simp]
abbrev mixedSSi (G : FinGame) (i : G.I) := S (G.SS i)

@[simp]
abbrev mixedS (G : FinGame) := (i:G.I) → S (G.SS i)

@[simp]
noncomputable def with_hole {G: FinGame} (s : G.mixedS) (i : G.I) (x : S (G.SS i)) := @aux.with_hole G.I (fun i =>S (G.SS i)) s i x

-- comma_notation for mixed game
noncomputable instance comma.mixed {G:FinGame} {i : G.I} : CoeOut  ((S (G.SS i))×(@IFun' G.I (fun i => S (G.SS i )) i)) (IFun (fun i => S (G.SS i))) where
  coe := @combinePair G.I (fun i=> S (G.SS i)) i


noncomputable def mixed_g {G: FinGame} (i : G.I) (x : Π i, S (G.SS i) ) : ℝ := ∑ s : (Π j, G.SS j) , ∏ j,  x j (s j) * (G.g i s)




def mixedNashEquilibrium {G: FinGame} (x : G.mixedS) :=
  ∀ (i:G.I)
    (y : G.mixedS ),
    (∀ j: G.I, i≠j → (x j = y j) ) →
     G.mixed_g i x ≥ G.mixed_g i y

end FinGame

section Brouwer.mixedGame
variable {G: FinGame}


theorem Brouwer.mixedGame (f : G.mixedS → G.mixedS) (hf : Continuous f) : ∃ x : G.mixedS, f x = x := sorry

end Brouwer.mixedGame

section mixedNashEquilibrium
variable (G : FinGame)
open FinGame

theorem ExistsNashEq : ∃ x : G.mixedS , mixedNashEquilibrium x := by {
  sorry
}

end mixedNashEquilibrium
