import Mathlib.Data.Real.EReal 
import Mathlib.Data.Real.NNReal 
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Basic
--import Mathlib.Probability.ProbabilityMassFunction.Integrals
--import Mathlib.Probability.ProbabilityMassFunction.Monad 

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


end zerosumGame


/-
sectionm
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

section S 
variable (α : Type*) [Fintype α] 

def S := { x : α→ NNReal // Finset.sum Finset.univ x = 1}  

instance coe_fun : CoeFun (S α) fun _ => α → NNReal :=
  ⟨fun x => (x.val : α → NNReal)⟩ 

@[simp]
noncomputable def pure (i : α) : S α  := ⟨ fun j => if i=j then 1 else 0,
 by {simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]}⟩ 


end S

namespace zerosumFGame  

variable {I J : Type*}  [Inhabited I] [Inhabited J] [Fintype I] [Fintype J]
variable (A : I → J → ℝ ) 



def sumxC (j:J) (x : S I) (C : I →J → ℝ ) := Finset.sum Finset.univ (fun i : I => (x i) *( C i j))

def sumyC (i:I) (y : S J) (C : I →J → ℝ ) := Finset.sum  Finset.univ (fun j : J=> (y j) * ( C i j))



lemma sum_pure [Fintype I] {f: I→ℝ} {a:I} : 
  Finset.sum Finset.univ (fun i => (pure I a i) * f i) = f a :=
  by {
    have : f a= (pure I a a).toReal * f a := by simp [_root_.pure,ite_true, ENNReal.one_toReal, one_mul]
    rw [this]
    apply Finset.sum_eq_single --_ I _ Finset.univ _ a (sorry) (sorry) 
    . {
      intro b _ h3
      simp only [_root_.pure, mul_eq_zero, NNReal.coe_eq_zero, ite_eq_right_iff, one_ne_zero]
      exact Or.inl (fun x => h3 (symm x))   
    }
    . {
    intro h1
    exfalso; simp only [Finset.mem_univ, not_true] at h1  
    }
  }


lemma simplex_ge_iff_vertex_ge [Fintype I] {f : I → ℝ } {v : ℝ} : 
   (∀ x : S I,   Finset.sum Finset.univ (fun i : I => (x i).toReal * f i)≥ v) 
    ↔ (∀ i : I, f i ≥ v):= by {
  constructor 
  . {
    intro H i
    have := H (pure I i)
    rw [sum_pure] at this
    exact this
  } 
  . {
    intro H x
    simp only [ge_iff_le]
    calc 
      v = Finset.sum Finset.univ (fun i : I => (x i).toReal * v) := by {
        sorry
      } 
      _ ≤ Finset.sum Finset.univ (fun i : I => (x i).toReal * f i) :=
      Finset.sum_le_sum (by {
        intro i
        simp only [Finset.mem_univ, gt_iff_lt, forall_true_left]
        rw [<-sub_nonneg,<-mul_sub]
        exact mul_nonneg (NNReal.zero_le_coe) (sub_nonneg.2 (H i))
      })
  }
 } 



-- expactation of the payoff of a mixed stratage
noncomputable def E (x : S I) (y : S J) : ℝ := Finset.sum Finset.univ  
( fun (i : I ) => Finset.sum Finset.univ  (fun (j : J) => (x i) * (A i j) * (y j)))

-- One may need Finset.sum_comm' Finset.sum_mul

-- lemma E_eq1 

/-
lemma E_eq1 {x : PMF I} {y : PMF J} : Finset.sum (@Finset.univ _ A.FI) 
( fun (i : I ) => Finset.sum (@Finset.univ _ A.FJ) (fun (j : J) => (x i).toReal * (A i j) * ((y j).toReal) )) = Finset.sum (@Finset.univ _ A.FI) 
( fun (i : I ) =>(x i).toReal * Finset.sum (@Finset.univ _ A.FJ) (fun (j : J) => (A i j) * ((y j).toReal) )) := by { 
  sorry
}
-/

-- invoke exterem value theorem is_compact.exists_forall_le


theorem Loomis (B : I →J → ℝ   ) (PB : ∀ i:I, ∀ j:J,  B i j > 0 )  : 
  ∃ (xx : S I) (yy : S J) (v : ℝ),  
    (∀ j , sumxC j xx A ≥  v * sumxC j xx B) ∧
    (∀ i ,  sumyC i yy A ≤  v * sumyC i yy B) := by sorry  



theorem minmax_theorem : ∃ (xx : S I) (yy : S J) (v : ℝ), (∀ (y : S J), E A xx y ≥ v ) ∧ (∀ (x : S I), E A x yy ≤ v)  := by {  
  let B : I → J → ℝ  := fun i => fun j => 1 
  obtain ⟨xx, yy, v, H1, H2⟩ := Loomis A B (by {intro i j; simp only [gt_iff_lt, zero_lt_one]})
  use xx,  yy, v
  constructor 
  . {
    -- rw [E_eq1]
    -- rw [simplex_ge_iff_vertex_ge]
    sorry  
  }
  . {
    --rw [E_eq1]
  sorry
  } 

} 



end zerosumFGame


