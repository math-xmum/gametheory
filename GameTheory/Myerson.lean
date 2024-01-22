import Mathlib.Data.Real.EReal
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Lattice

open Classical
open BigOperators

-- Single-parameter environments
structure SingleParameterEnvironment where
   I : Type* -- The set of bidders
   IInhabited : Inhabited I
   IFintype : Fintype I
   feasibleSet: I → Set ℝ -- feasibleSet
   feasibleSetInhabited: ∀ i, Inhabited (feasibleSet i)
   --val: I → ℝ  -- valuation of the item for each bidder

namespace SingleParameterEnvironment
variable (E: SingleParameterEnvironment)
variable {F: SingleParameterEnvironment}

instance : Inhabited E.I := E.IInhabited
instance : Fintype E.I := E.IFintype
instance : Inhabited (E.feasibleSet i) := E.feasibleSetInhabited _


--new valuation
abbrev Valuation := E.I → ℝ

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


def Monotone (ar : F.AllocationRule) := ∀ i (x1 x2: ℝ) (b': Bids' i), x1 ≤ x2 →  (ar (x1,b') i) ≤  (ar (x2,b') i)

-- Payments
abbrev Payment:= E.I → ℝ

abbrev PaymentRule := E.Bids → E.Payment

-- Quasi_Linear utility
def utility (ar : F.AllocationRule) (pr : F.PaymentRule) (v : F.Valuation) (b : F.Bids) :
  F.I → ℝ := fun i => v i * (ar b i) - (pr b i)


def dominant (ar : F.AllocationRule) (pr : F.PaymentRule) (v : F.Valuation) (i : F.I) (bi : ℝ) :=
  ∀ (b' :Bids' i), utility ar pr v (bi,b') i ≥ utility ar pr v (bi, b') i

def DSIC ar pr v := ∀ i:F.I,
  (dominant ar pr v i (v i))
  ∧ (∀ b' : Bids' i, utility ar pr v ((v i),b') i ≥ 0)

def Implementable (ar : F.AllocationRule) := ∀ v, ∃ pr : F.PaymentRule, DSIC ar pr v

--lemma eq_zero  (pr : F.PaymentRule)(i : F.I) (bi : ℝ):
  --∀pr: F.PaymentRule, pr( 0, bi )= 0 := by {

--}

--An allocation rule X is implementable if and only if it is monotone
theorem Myerson's_Lemma1 (ar :F.AllocationRule) :
Implementable ar ↔ Monotone ar := by {
  constructor
  intro h hj

}
  --函数延展性 三元组相等 => 函数unique
lemma function_extensionality {α β: Type} {f g : α → β} (h : ∀ x, f x = g x) : f = g :=by {
  funext x
  exact h x
}

example (α β : Type) (f g : α → β) (h : ∀ x, f x = g x) : f = g := by{
  apply function_extensionality
  exact h
}


--If X is monotone, then there is a unique payment rule such that the sealed-bid mechanism (X; P)
--is DSIC [assuming the normalization that bi = 0 implies Pi(b) = 0].
--theorem Myerson's_Lemma2(ar :F.AllocationRule)(pr : F.PaymentRule) :Implementable ar → (ar,pr) is unique  := by{


--感觉跟凸优化又有点关系，
--feasible set X. Each element of X is a nonnegative nvector (x1, x2, . . . , xn),
--where xi denotes the “amount of stuff” given to agent i.
