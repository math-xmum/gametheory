import Mathlib.Data.Real.EReal 

section 

variable {I J : Type*} (g : I → J → ℝ) 

def guarantees1 (w : ℝ) := ∃ i: I, ∀ j : J , (g i j) ≥ w  

def guarantees2 (w : ℝ) := ∃ j: J, ∀ i : I , (g i j) ≤ w 

--def gg : I -> J -> EReal := fun i => fun j => ( (g i j):EReal )




noncomputable def maxmin : EReal := @iSup EReal _ I (fun i => @iInf EReal _ J (fun  j: J => ((g i j):EReal))) 


noncomputable def minmax : EReal := @iInf EReal _ J (fun j => @iSup EReal _ I (fun  i: I => ((g i j):EReal))) 


lemma maxmin_le_minmax : maxmin g ≤ minmax g := by {
  sorry 
}  

end



