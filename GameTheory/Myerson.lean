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
   val: I → ℝ  -- valuation of the item for each bidder



namespace SingleParameterEnvironment
variable (E: SingleParameterEnvironment)
variable {F: SingleParameterEnvironment}

instance : Inhabited E.I := E.IInhabited
instance : Fintype E.I := E.IFintype
instance : Inhabited (E.feasibleSet i) := E.feasibleSetInhabited _

-- The type of bids
@[simp]
def Bids := E.I → ℝ


-- The subtype delete i-th bidder
@[simp]
def I' i:= {j : F.I // j ≠ i}


@[simp]
def Bids' (i : F.I) := I' i → ℝ

noncomputable def combineBids {i : F.I} (x : ℝ) (b' : I' i →ℝ) : F.Bids
:= fun j => if h:j=i then x else b' ⟨j, h⟩

noncomputable instance  {i : F.I}: CoeOut (ℝ × (Bids' i)) F.Bids where
  coe  b := combineBids b.1 b.2


@[simp]
def Allocation := Π i, E.feasibleSet i

-- The type of allocation rule
@[simp]
def AllocationRule := E.Bids → E.Allocation


def Monotone (ar : F.AllocationRule) := ∀ i (x1 x2: ℝ) (b': Bids' i), x1 ≤ x2 →  (ar (x1,b') i) ≤  (ar (x2,b') i)


-- Payments

@[simp]
def Payment:= E.I → ℝ

@[simp]
def PaymentRule := E.Bids → E.Payment

-- Quasi_Linear utility
def utility (ar : F.AllocationRule) (pr : F.PaymentRule) (b : F.Bids) :
  F.I → ℝ := fun i => F.val i * (ar b i) - (pr b i)

def dominant (ar : F.AllocationRule) (pr : F.PaymentRule) (i : F.I) (bi : ℝ) := ∀ (b' :Bids' i), utility ar pr (bi,b') i ≥ utility ar pr (bi, b') i

def DSIC ar pr := ∀ i:F.I,
  (dominant ar pr i (F.val i))
  ∧ (∀ b' : Bids' i, utility ar pr ((F.val i),b') i ≥ 0)

def Implementable (ar : F.AllocationRule) := ∃ pr : F.PaymentRule, DSIC ar pr

theorem MyersonLemma (ar :F.AllocationRule) :
Implementable ar ↔ Monotone ar := sorry


end SingleParameterEnvironment
