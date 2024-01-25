import Mathlib.Data.Real.EReal
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Lattice

open Classical
open BigOperators

-- Single-parameter environments
structure SingleParameterEnvironment where
   I : Type* -- The set of bidders 智能体
   IInhabited : Inhabited I--At least one element exist
   IFintype : Fintype I
   feasibleSet: I → Set ℝ -- feasibleSet可行解集
   feasibleSetInhabited: ∀ i, Inhabited (feasibleSet i)
   --val: I → ℝ  -- valuation of the item for each bidder

namespace SingleParameterEnvironment
variable (E: SingleParameterEnvironment)
variable {F: SingleParameterEnvironment}

instance : Inhabited E.I := E.IInhabited
instance : Fintype E.I := E.IFintype
instance : Inhabited (E.feasibleSet i) := E.feasibleSetInhabited _


--new valuation
--abbrev Valuation := E.I → ℝ
def Valuation := E.I → ℝ

-- The type of bids
abbrev Bids := E.I → ℝ

-- The subtype of all bidders delete i-th bidder
abbrev I' i:= {j : F.I // j ≠ i}

abbrev Bids' (i : F.I) := I' i → ℝ

noncomputable def combineBids {i : F.I} (x : ℝ) (b' : Bids' i) : F.Bids
:= fun j => if h:j=i then x else b' ⟨j, h⟩

noncomputable def combineBidsPair {i : F.I} (b : ℝ × Bids' i) : F.Bids
:= combineBids b.1 b.2
attribute [coe] combineBidsPair

noncomputable instance  {i : F.I}: CoeOut (ℝ × (Bids' i)) F.Bids where
  coe := combineBidsPair

variable (i : F.I) (b' : Bids' i) (x : ℝ)

#check ((x,b'): F.Bids)

@[simp]
def Allocation := Π i, E.feasibleSet i

-- The type of allocation rule
@[simp]
def AllocationRule := E.Bids → E.Allocation

def Monotone (ar : F.AllocationRule) := ∀ i (x1 x2: ℝ) (b': Bids' i), x1 < x2 →  (ar (x1,b') i) ≤  (ar (x2,b') i)

-- Payments
abbrev Payment:= E.I → ℝ

abbrev PaymentRule := E.Bids → E.Payment

-- Quasi_Linear utility
def utility (ar : F.AllocationRule) (pr : F.PaymentRule) (v : F.Valuation) (b : F.Bids) :
  F.I → ℝ := fun i => v i * (ar b i) - (pr b i)

--错的domnant定义
--def dominant (ar : F.AllocationRule) (pr : F.PaymentRule) (v : F.Valuation) (i : F.I) (bi : ℝ) :=
 -- ∀ (b' :Bids' i), utility ar pr v (bi,b') i ≥ utility ar pr v  (bi', b') i
--正确的dominant定义
def dominant (ar : F.AllocationRule) (pr : F.PaymentRule) (v : F.Valuation) (i : F.I) (bi : ℝ) :=
  ∀ (bi' : ℝ) (b' :Bids' i), utility ar pr v (bi, b') i ≥ utility ar pr v (bi', b') i

def DSIC ar pr v := ∀ i:F.I,
  (dominant ar pr v i (v i))
  ∧ (∀ b' : Bids' i, utility ar pr v ((v i),b') i ≥ 0)

def Implementable (ar : F.AllocationRule) := ∃ pr : F.PaymentRule, ∀ v, DSIC ar pr v


lemma relation_h12(x1:ℝ )(x2:ℝ )(x3:ℝ )(x4:ℝ ):
   x1 ≤ x2 - x3 + x4 ↔ x1 -x2 ≤ x4 - x3:= by {
constructor
.intro h1
 linarith
.intro h2
 linarith
}
lemma relation_h13(x1:ℝ )(x2:ℝ )(x3:ℝ )(x4:ℝ )(a:ℝ ): a*x1 - a*x2 ≤ x4 - x3 ↔ a*(x1 -x2) ≤ x4 - x3:= by {
constructor
.intro h1
 linarith
.intro h2
 linarith
}
lemma relation_h14(x1:ℝ )(x2:ℝ )(x3:ℝ )(x4:ℝ )(a:ℝ ):
 a*(x1 -x2) ≤ x4 - x3 ↔ a*(x2 -x1) ≥  x3 - x4 := by {
constructor
.intro h1
 linarith
.intro h2
 linarith
}
lemma subnonneg_of_le (a b : ℝ) (h : a ≤ b) : a - b ≤ 0 := by {
  linarith
}

--dsic
lemma implementable_imp_monotone (ar :F.AllocationRule) (v : F.Valuation):
Implementable ar → Monotone ar := by {
  rw [Implementable, Monotone]
  intro H i z y b' Hx
  obtain ⟨pr,Hpr⟩:= H
  let x := fun (z:ℝ) => ar (z,b') i
  let p := fun (z:ℝ) => pr (z,b') i
  let zz : F.Valuation := fun _ => z
  let yy : F.Valuation := fun _ => y
  have H1 := (Hpr zz i).1  y b'
  simp only [utility, ge_iff_le, tsub_le_iff_right] at H1
  have H1: z * (x y - x z) ≤ p y - p z := by linarith
  have H2 := (Hpr yy i).1  z b'
  simp only [utility, ge_iff_le, tsub_le_iff_right] at H2
  have H2 : p y - p z ≤ y * (x y - x z) := by linarith
  have H3: (z - y)  * (x y - x z) ≤ 0 := by linarith
  have H4 : z - y < 0 := by linarith

  have H5 := ((@mul_nonpos_iff_neg_imp_nonneg _ _ (z-y) (x y - x z)).1 H3).1 H4

  simp [x] at H5
  simp [H5]
}


theorem MyersonLemma (ar :F.AllocationRule) :
Implementable ar ↔ Monotone ar := by {
  constructor
  · intro h
    exact implementable_imp_monotone ar hj


  · rintro hmon
    use λ b i => b i
    rintro v i b'
    constructor
}

  --函数延展性 三元组相等 => 函数unique
lemma function_extensionality {α β : Type} {f g : α → β} (h : ∀ x, f x = g x) : f = g :=by {
  funext x
  exact h x
}

example (α β : Type) (f g : α → β) (h : ∀ x, f x = g x) : f = g := by{
  apply function_extensionality
  exact h
}

lemma funext₃_extensionality(H : ∀ (a : ) (b : β), f a b = g a b) : f = g :=by{
  apply funext₃
  exact h
}

--lemma eq_zero  (pr : F.PaymentRule)(i : F.I) (bi : ℝ):
  --∀pr: F.PaymentRule, pr( 0, bi )= 0 := by {

--}

--If X is monotone, then there is a unique payment rule such that the sealed-bid mechanism (X; P)
--is DSIC [assuming the normalization that bi = 0 implies Pi(b) = 0].
--theorem Myerson's_Lemma2(ar :F.AllocationRule)(pr : F.PaymentRule) :Implementable ar → (ar,pr) is unique  := by{


--感觉跟凸优化又有点关系，
--feasible set X. Each element of X is a nonnegative nvector (x1, x2, . . . , xn),
--where xi denotes the “amount of stuff” given to agent i.
