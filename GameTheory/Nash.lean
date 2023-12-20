import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.EReal
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Finprod

open Classical 

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

variable (self : Game)

def NashEquilibrium (s : (∀ i:self.I, self.S i )) :=  
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
  { f : α → ℝ // 0 ≤ f ∧  ∑ i: α in Finset.univ, f i =1}
#align simplex Simplex 

instance funLike [Fintype α] : FunLike (Simplex α) α fun _ => ℝ where
  coe p a := p.1 a
  coe_injective' _ _ h := Subtype.eq h
--#align Simplex.fun_like Simplex.funLike

@[ext]
theorem Simplex.ext [Fintype α ] {p q : Simplex α} (h : ∀ x, p x = q x) : p = q :=
  FunLike.ext p q h
--#align pmf.ext Pmf.ext


noncomputable instance Simplex.inHabited (α : Type u) [Fintype α] [Inhabited α] : 
 Inhabited (Simplex α) where  
  default := ⟨fun i  => if i=default then (1:ℝ)   else (0:ℝ), 
   by {
    constructor
    . {
      rw [Pi.le_def];intro i;apply ite_nonneg;simp only [zero_le_one];
      simp only [le_refl]
    }
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    } 
  ⟩ 
  

--noncomputable def FinGame.mixedgi (G : FinGame) (gi : ((i :G.I)→ G.S i) → ℝ) (m : ((i:G.I)→ @Simplex (G.S i ) (G.FinS i))) : ℝ := 


noncomputable def FinGame2MixedGame (G : FinGame) : Game := {
  I := G.I
  HI := G.HI
  S := fun i => @Simplex (G.S i) (G.FinS i)
  HS := fun i => @Simplex.inHabited (G.S i) (G.FinS i) (G.HS i) 
  g := fun i => fun m => ∑ᶠ (s : (j:G.I)→ G.S j), (∏ᶠ (j:G.I), m j (s j)) * (G.g i s)
} 

notation:999 "μ" rhs:60 => (FinGame2MixedGame rhs) 

variable (G : FinGame)


theorem ExistsNashEq : ∃ m :  (i:(μ G).I )→ (μ G).S i, (μ G).NashEquilibrium m := by sorry  
