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

section comma_notation

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

noncomputable def combineSubtypeFun (x : f i) (y : IFun' f i ) : IFun f := fun j =>  (if h : j=i then (by rw [h];exact x) else  y ⟨j, h⟩)

noncomputable def combinePair(b : (f i) × (IFun' f i)) : IFun f := combineSubtypeFun b.1 b.2

attribute [coe] combinePair

noncomputable instance  {i : I}: CoeOut ((f i) × (IFun' f i)) (IFun f) where
  coe := combinePair

variable (i : I) (b' : I' i → ℝ ) (x : ℝ)

--#check ((x,b'): I→ ℝ)

end comma_notation


structure FinGame extends Game where
  FinI : Fintype I
  FinSS : ∀ i:I , Fintype (SS i)

 --def mixed_g  := fun i => fun m => ∑ᶠ (s : (j:G.I)→ G.SS j), (∏ᶠ (j:G.I), m j (s j)) * (G.g i s)



--noncomputable def mixed_g {G: FinGame} := fun (i : G.I) => (fun (x : Π i, S (G.SS i) ) =>  Finset.sum Finset.univ fun (s : (Π j, G.SS j)) => (finprod (fun j => x j (s j)) * (G.g i s)))




namespace FinGame



instance {G: FinGame} : Fintype G.I := G.FinI
instance {G: FinGame} {i : G.I}: Fintype (G.SS i) := G.FinSS i

noncomputable instance mixed_SS_i_Inhabited {G: FinGame} {i : G.I}: Inhabited (S (G.SS i)) := S.SInhabited_of_Inhabited


noncomputable def mixed_g {G: FinGame} (i : G.I) (x : Π i, S (G.SS i) ) : ℝ := ∑ s : (Π j, G.SS j) , ∏ j,  x j (s j) * (G.g i s)

@[simp]
abbrev mixedSSi (G : FinGame) (i : G.I) := S (G.SS i)

@[simp]
abbrev mixedS (G : FinGame) := (i:G.I) → S (G.SS i)



def mixedNashEquilibrium {G: FinGame} (x : G.mixedS) :=
  ∀ (i:G.I)
    (y : Π i, G.SS i ),
    (∀ j: G.I, i≠j → (x j = y j) ) →
     G.g i x ≥ G.g i y



noncomputable def FinGame2MixedGame (G : FinGame) : Game where
  I := G.I
  HI := G.HI
  SS := fun (i:G.I) => S (G.SS i)
  HSS := fun _ => mixed_SS_i_Inhabited
  g := mixed_g
  --g := fun i => fun m => ∑ᶠ (s : (j:G.I)→ G.SS j), (∏ᶠ (j:G.I), m j (s j)) * (G.g i s)

end FinGame

notation:999 "μ" rhs:100 => (FinGame2MixedGame rhs)

variable (G : FinGame)


variable (f : (μ G).SS  →(μ G).SS)

theorem ExistsNashEq : ∃ x :  Π i, (μ G).SS i, NashEquilibrium x := by {
  sorry
}
