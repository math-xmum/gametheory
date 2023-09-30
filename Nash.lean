import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.EReal
import Mathlib.Data.Set.Basic



/-
A game is a set of maps g^i : Πᵢ S i → ℝ
-/
structure Game.{u,v} where 
    I : Type u 
    HI : Inhabited I
    S : I → Type v 
    HS : ∀ (i: I), Inhabited (S i) 
    g : I → (∀ i:I, S i) →  ℝ
#align game Game 


namespace Game

def NashEquilibrium (s : (∀ i:I self, self.S i )) :=  
  ∀ (i:self.I)  
    (t : (i:self.I)→(self.S i)),
    (∀ j: self.I, i≠j → (s j = t j) ) →  
     self.g i s ≥ self.g i t 

end Game

structure FinGame extends Game where 
  FinI : Fintype I 
  FinS : ∀ i:I , Fintype (S i)  


--def Simplex (α : Type*) :=  
open BigOperators 

def Simplex.{u} (α : Type u) [Fintype α]: Type u :=
  { f : α → ℝ // 0≤ f ∧  ∑ i: α in Finset.univ, f i =1 }
#align simplex Simplex 
