import Mathlib.Data.Real.EReal 
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad 

open Classical

/-
We use Probability mass function to denote a mixed stratage
-/


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



def zerosumFGame.toFun (A : zerosumFGame I J) := A.g 
instance : CoeFun (zerosumFGame I J) (fun _ => I →  J → ℝ ) where  
  coe := zerosumFGame.toFun I J 

attribute [coe] zerosumFGame.toFun   

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


/-
section
variable {I : Type*}

lemma sum_pure {f: I→ℝ} {a:I}: ∑' i: I, ((PMF.pure a i).toReal * f i) = f a := by {
  have Hsummand : (fun i => (PMF.pure a i).toReal * f i) 
              = fun i:I  => (if i = a then f a else 0) := by {
                ext i
                simp only [PMF.pure_apply]
                by_cases hh: i = a
                . simp only [hh,ite_true, ENNReal.one_toReal, one_mul]
                . simp only [hh, ite_false, ENNReal.zero_toReal, zero_mul]
              } 
  rw [Hsummand]
  exact tsum_ite_eq a (f a)  
} 


lemma simplex_ge_iff_vertex_ge {f : I → ℝ } {v : ℝ} : 
 (∀ x : PMF I,   ∑' i : I, (x i).toReal * f i ≥ v) ↔ (∀ i : I, f i ≥ v):= by {
  constructor 
  . {
    intro H i
    have := H (PMF.pure i)
    rw [sum_pure] at this
    exact this
  } 
  . {
    intro H x

  }
 } 

end
-/


namespace zerosumFGame  

variable {I J : Type*}
variable (A : zerosumFGame I J) 

instance : Fintype I := A.FI
instance : Fintype J := A.FJ


def sumxC (j:J) (x : PMF I) (C : I →J → ℝ ) := Finset.sum  (@Finset.univ _ A.FI) (fun i : I=> (x i).toReal *( C i j))

def sumyC (i:I) (y : PMF J) (C : I →J → ℝ ) := Finset.sum  (@Finset.univ _ A.FJ) (fun j : J=> (y j).toReal *( C i j))



lemma sum_pure [Fintype I] {f: I→ℝ} {a:I} : 
  Finset.sum Finset.univ (fun i => (PMF.pure a i).toReal * f i) = f a :=
  by {
    have : f a= (PMF.pure a a).toReal * f a := by simp only [PMF.pure_apply, ite_true, ENNReal.one_toReal, one_mul]
    rw [this]
    apply Finset.sum_eq_single --_ I _ Finset.univ _ a (sorry) (sorry) 
    intro h1 _ h3; simp only [PMF.pure_apply, h3, ite_false, ENNReal.zero_toReal, zero_mul]
    intro h1; exfalso; simp only [Finset.mem_univ, not_true] at h1  
  }


lemma simplex_ge_iff_vertex_ge [Fintype I] {f : I → ℝ } {v : ℝ} : 
   (∀ x : PMF I,   Finset.sum Finset.univ (fun i : I => (x i).toReal * f i)≥ v) 
    ↔ (∀ i : I, f i ≥ v):= by {
  constructor 
  . {
    intro H i
    have := H (PMF.pure i)
    rw [sum_pure] at this
    exact this
  } 
  . {
    intro H x
    sorry
  }
 } 



theorem Loomis (B : I →J → ℝ   ) (PB : ∀ i:I, ∀ j:J,  B i j > 0 )  : 
  ∃ (xx : PMF I) (yy : PMF J) (v : ℝ),  
    (∀ j , A.sumxC j xx A ≥  v * A.sumxC j xx B) ∧
    (∀ i ,  A.sumyC i yy A≤  v * A.sumyC i yy B ) := by sorry  

theorem minmax_theorem : ∃ (xx : PMF I) (yy : PMF J) (v : ℝ), ∀ (x : PMF I) (y : PMF J) , A.E xx y ≥ v ∧ A.E x yy ≤ v  := by sorry   



end zerosumFGame


