import Mathlib.Data.Real.EReal 
import Mathlib.Probability.ProbabilityMassFunction.Integrals


section 

variable {I J : Type*} (g : I → J → ℝ) 

--def gg : I -> J -> EReal := fun i => fun j => ( (g i j):EReal )







/-
We use Probability mass function to denote a mixed stratage
-/



end

variable (I J : Type*)


@[ext]
structure zerosumGame where
  g : I → J → ℝ  
  HI : Inhabited I
  HJ : Inhabited J

instance : CoeFun (zerosumGame I J) (fun _ => I →  J → ℝ ) where  
  coe := zerosumGame.g

attribute [coe] zerosumGame.g 


--finite game
structure zerosumFGame extends zerosumGame I J where
  FI : Fintype I 
  FJ : Fintype J 
  


namespace zerosumGame 
variable {I J : Type*}
variable (A : zerosumGame I J) 

noncomputable def maxmin : EReal := @iSup EReal _ I (fun i => @iInf EReal _ J (fun  j: J => ((A i j ):EReal))) 


noncomputable def minmax : EReal := @iInf EReal _ J (fun j => @iSup EReal _ I (fun  i: I => ((A i j):EReal))) 


lemma maxmin_le_minmax : maxmin A ≤ minmax A := by {
have H1 : ∀ j i,  @iInf EReal _ J (fun j => A i j) ≤ A i j:= by {
 intro j i
 apply iInf_le
}
rw [minmax,maxmin]
have H2 : ∀ j, @iSup EReal _ I (fun i => @iInf EReal _ J (fun j => A i j)
) ≤ @iSup EReal _ I (fun i => A i j) := by {
  intro j 
  apply iSup_mono
  exact H1 j
} 
exact le_iInf H2
}


def guarantees1 (w : ℝ) := ∃ i: I, ∀ j : J , (A i j) ≥ w  

def guarantees2 (w : ℝ) := ∃ j: J, ∀ i : I , (A i j) ≤ w 


-- expactation of the payoff of a mixed stratage
noncomputable def E (x : PMF I) (y : PMF J) : ℝ := ∑' (i : I ),  ∑' (j : J), ((x i).toReal : ℝ) * (A i j) * ((y j).toReal : ℝ) 

end zerosumGame





section zerosumFGame  

variable {I J : Type*}
variable (A : zerosumGame I J) 


theorem Loomis (B : I →J → ℝ   ) (PB : ∀ i:I, ∀ j:J,  B i j > 0 )  : 
  ∃ (xx : PMF I) (yy : PMF J) (v : ℝ),  
    (∀ j , ∑ᶠ i:I, (xx i).toReal * A i j ≥  v * ∑ᶠ i:I, (xx i).toReal * B i j ) ∧
    (∀ i ,  ∑ᶠ j:J, (yy j).toReal * A i j ≤  v * ∑ᶠ j:J, (yy j).toReal * B i j ) := by sorry  

theorem minmax_theorem : ∃ (xx : PMF I) (yy : PMF J) (v : ℝ), ∀ (x : PMF I) (y : PMF J) , A.E xx y ≥ v ∧ A.E x yy ≤ v  := by sorry   



end zerosumFGame


