import Mathlib
--import LLMlean

variable {T : Type*} [Fintype T] [DecidableEq T]   -- The finite set T
variable {I : Type*} [Fintype I] [DecidableEq I] [Nontrivial I] -- The index set I

/- A family of linear orders indexed by I -/
/-
structure IndexedSTOrder (T : Type*) (I : Type*) where
  ilt : I → T → T → Prop -- lt i represents <ᵢ
  isStrictOrder : IsStrictTotalOrder T (ilt i)
  isDecidableRel : DecidableRel (ilt i)
attribute [instance] IndexedSTOrder.isStrictOrder IndexedSTOrder.isDecidableRel

variable (IST : IndexedSTOrder T I)


set_option quotPrecheck false

local notation  lhs "<[" i "]" rhs => (linearOrderOfSTO (IST.ilt i)).lt lhs rhs
local notation  lhs "≤[" i "]" rhs => (linearOrderOfSTO (IST.ilt i)).le lhs rhs

local notation  "min[" i "]" rhs => @Finset.min T (linearOrderOfSTO (IST.ilt i)) rhs
-/


class IndexedLOrder (I T :Type*) where
  IST : I → LinearOrder T

instance : FunLike (IndexedLOrder I T) I (LinearOrder T) where
  coe := fun a => a.IST
  coe_injective' := fun f g h => by cases f; cases g; congr


variable [IST : IndexedLOrder I T]

set_option quotPrecheck false

local notation  lhs "<[" i "]" rhs => (IST i).lt lhs rhs
local notation  lhs "≤[" i "]" rhs => (IST i).le lhs rhs



namespace IndexedLOrder
/- Definition of Dominant -/
def isDominant (σ : Finset T) (C : Finset I) :=
  ∀ y, ∃ i ∈ C, ∀ x ∈ σ,  y ≤[i] x


/- Lemma 1 -/
omit [Fintype T] [DecidableEq T] [Fintype I] [DecidableEq I] [Nontrivial I] in
lemma Dominant_of_subset (σ τ : Finset T) (C : Finset I) :
  τ ⊆ σ → isDominant σ C  → isDominant τ C := by
    intro h1 h2
    intro y
    obtain ⟨j,hj⟩:= h2 y
    use j,hj.1
    intro x hx
    exact hj.2 x (h1 hx)

omit [Fintype T] [DecidableEq T] [Fintype I] [DecidableEq I] [Nontrivial I] in
lemma Dominant_of_supset (σ : Finset T) (C D: Finset I) :
  C ⊆ D → isDominant σ C  → isDominant σ D := by
    intro h1 h2
    intro y
    obtain ⟨j,hj⟩:= h2 y
    use j,(h1 hj.1)
    intro x hx
    exact hj.2 x hx

omit [Fintype T] [DecidableEq T] [Fintype I] [DecidableEq I] [Nontrivial I] in
lemma empty_Dominant (h : D.Nonempty) : IST.isDominant Finset.empty D := by
  intro y
  obtain ⟨j,hj⟩ := h
  use j
  constructor
  · exact hj
  · intro x hx
    contradiction


abbrev isCell (σ : Finset T) (C : Finset I) := C.Nonempty ∧ isDominant σ C


abbrev isRoom (σ : Finset T) (C : Finset I) :=  isCell σ C ∧ C.card = σ.card

abbrev isDoor (σ : Finset T) (C : Finset I) :=  isCell σ C ∧ C.card = σ.card + 1

inductive isDoorof (τ : Finset T) (D : Finset I) (σ : Finset T) (C : Finset I) : Prop
  | idoor (x :T) (h1 : x ∉ τ) (h2 : insert x τ = σ) (h3 : D = C)
  | odoor (j :I) (h1 : j ∉ C) (h2 : τ = σ) (h3 : D = insert j C)

lemma isCell_of_Door (h1 : isDoorof τ D σ C) (h2 : IST.isCell σ C): IST.isCell τ D := by
  cases h1
  · rename_i j h1 h3 h4
    rw [h4]
    constructor
    · exact h2.1
    · exact Dominant_of_subset _ _ C (by simp [<-h3]) h2.2
  · sorry


lemma isRoom_of_Door (h1 : isDoorof τ D σ C) (h2 : IST.isDoor τ D): IST.isRoom τ D := by sorry


/- TODO formula that every room has |I| doors -/

lemma room_is_not_door (h1 : IST.isRoom σ C) : ∀ τ D,  ¬ (isDoorof τ D σ C) := sorry

variable (τ D) in
def isOutsideDoor := IST.isDoor τ D ∧ τ = Finset.empty

variable (τ D) in
def isInternalDoor := IST.isDoor τ D ∧ τ.Nonempty

/- Lemma 2-/
lemma outsidedoor_singleton (i : I) : IST.isOutsideDoor Finset.empty {i} := sorry


variable (τ D) in
lemma outsidedoor_is_singleton (h : IST.isOutsideDoor τ  D) :  τ = Finset.empty ∧  ∃ i, D = {i} := sorry


section KeyLemma

/- Lemma 3-/
theorem internal_door_two_rooms (τ : Finset T) (D : Finset I)
    (h : IST.isInternalDoor τ D) :
    ∃ (σ₁ σ₂ : Finset T) (C₁ C₂ : Finset I),
      σ₁ ≠ σ₂ ∧
      IST.isRoom σ₁ C₁ ∧
      IST.isRoom σ₂ C₂ ∧
      isDoorof τ D σ₁ C₁ ∧
      isDoorof τ D σ₂ C₂ ∧
      (∀ σ C, IST.isRoom σ C → isDoorof τ D σ C →
       (σ = σ₁ ∧ C = C₁) ∨ (σ = σ₂ ∧ C = C₂)) := by
       sorry
end KeyLemma


end IndexedLOrder
