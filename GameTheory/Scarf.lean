import Mathlib


variable {T : Type*} [Fintype T] [DecidableEq T] [Inhabited T]  -- The finite set T
variable {I : Type*} [Fintype I] [DecidableEq I]
-- The index set I

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
variable (σ : Finset T) (C : Finset I)

/- Definition of Dominant -/
def isDominant  :=
  ∀ y, ∃ i ∈ C, ∀ x ∈ σ,  y ≤[i] x

omit [Fintype T] [DecidableEq T] [Fintype I] [DecidableEq I] in
variable {σ C} in
lemma Nonempty_of_Dominant (h : IST.isDominant σ C) : C.Nonempty := by
  obtain ⟨j,hj⟩ := h default
  exact ⟨j, hj.1⟩




/- Lemma 1 -/
omit [Fintype T] [DecidableEq T] [Inhabited T]  [Fintype I] [DecidableEq I]  in
lemma Dominant_of_subset (σ τ : Finset T) (C : Finset I) :
  τ ⊆ σ → isDominant σ C  → isDominant τ C := by
    intro h1 h2
    intro y
    obtain ⟨j,hj⟩:= h2 y
    use j,hj.1
    intro x hx
    exact hj.2 x (h1 hx)

omit [Fintype T] [DecidableEq T] [Inhabited T]  [Fintype I] [DecidableEq I]  in
lemma Dominant_of_supset (σ : Finset T) (C D: Finset I) :
  C ⊆ D → isDominant σ C  → isDominant σ D := by
    intro h1 h2
    intro y
    obtain ⟨j,hj⟩:= h2 y
    use j,(h1 hj.1)
    intro x hx
    exact hj.2 x hx

omit [Fintype T] [DecidableEq T] [Inhabited T]  [Fintype I] [DecidableEq I]  in
lemma empty_Dominant (h : D.Nonempty) : IST.isDominant Finset.empty D := by
  intro y
  obtain ⟨j,hj⟩ := h
  use j
  constructor
  · exact hj
  · intro x hx
    contradiction


abbrev isCell  := isDominant σ C


abbrev isRoom :=  isCell σ C ∧ C.card = σ.card

omit [Fintype T] [DecidableEq T] [Fintype I] [DecidableEq I] in
lemma sigma_nonempty_of_room {σ : Finset T} {C : Finset I} (h : isRoom σ C) : σ.Nonempty  := by
  have hC : C.Nonempty := Nonempty_of_Dominant h.1
  have hCpos : 0 < C.card := Finset.card_pos.2 hC
  have h_card : σ.card = C.card := h.2.symm
  have hpos : 0 < σ.card := by rwa [h_card]
  exact Finset.card_pos.1 hpos

/- use |σ| = |C| and C nonempty-/

abbrev isDoor  :=  isCell σ C ∧ C.card = σ.card + 1

inductive isDoorof (τ : Finset T) (D : Finset I) (σ : Finset T) (C : Finset I) : Prop
  | idoor (h0 : isCell σ C) (x :T) (h1 : x ∉ τ) (h2 : insert x τ = σ) (h3 : D = C)
  | odoor (h0 : isCell σ C) (j :I) (h1 : j ∉ C) (h2 : τ = σ) (h3 : D = insert j C)

omit [Fintype T] [Inhabited T] [Fintype I] in
lemma isCell_of_door (h1 : isDoorof τ D σ C) : IST.isCell τ D := by
  cases h1
  · rename_i h0 j h1 h3 h4
    rw [h4]
    exact IST.Dominant_of_subset _ _ C (by simp [<-h3]) h0
  · rename_i h0 j h1 h2' h3
    rw [h2', h3]
    exact IST.Dominant_of_supset _ _ _ (Finset.subset_insert j C) h0

omit [Fintype T] [Inhabited T] [Fintype I] in
lemma isRoom_of_Door (h1 : isDoorof τ D σ C) (h2 : IST.isDoor τ D): IST.isRoom σ C := by
  cases h1
  · rename_i h0 x h3 h4 h5
    constructor
    · exact h0
    · simp only [<-h5, h2.2, <-h4, h3, not_false_eq_true, Finset.card_insert_of_not_mem]
  · rename_i h0 x h3 h4 h5
    constructor
    · exact h0
    · have h6 := Finset.card_insert_of_not_mem h3
      subst h4
      replace h5 : D.card = (insert x C).card := by rw [h5]
      rw [h6] at h5
      rw [h2.2] at h5
      exact Eq.symm $ (add_left_inj _).1 h5



/- TODO formula that every room has |I| doors -/
def door_para : Sum (σ) (C) ≃ {(τ,D): (Finset T)× (Finset I) | IST.isDoorof τ D σ C} where
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry


lemma room_is_not_door (h1 : IST.isRoom σ C) : ∀ τ D,  ¬ (isDoorof σ C τ D) := sorry



variable (τ D) in
abbrev isOutsideDoor := IST.isDoor τ D ∧ τ = Finset.empty

variable (τ D) in
abbrev isInternalDoor := IST.isDoor τ D ∧ τ.Nonempty

/- Lemma 2-/
omit [Fintype T] [DecidableEq T] [Inhabited T] [Fintype I] [DecidableEq I] in
lemma outsidedoor_singleton (i : I) : IST.isOutsideDoor Finset.empty {i} := by
  constructor
  · rw [isDoor,isCell,isDominant]
    constructor
    · intro y; use i
      constructor
      · exact Finset.mem_singleton.2 (rfl)
      · intro x hx
        contradiction
    · simp only [Finset.card_singleton, self_eq_add_left, Finset.card_eq_zero]
      rfl
  · rfl


--variable (τ D) in
omit [Fintype T] [DecidableEq T] [Inhabited T] [Fintype I] [DecidableEq I] in
lemma outsidedoor_is_singleton (h : IST.isOutsideDoor τ  D) :  τ = Finset.empty ∧  ∃ i, D = {i} := by
  obtain ⟨h1, h2⟩ := h
  subst h2
  obtain ⟨h2,h3⟩ := h1
  replace h4 : D.card = 1 := by
    simp_all only [add_left_eq_self, Finset.card_eq_zero]
    rfl
  exact ⟨rfl, Finset.card_eq_one.1 h4⟩


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


noncomputable section Scarf

open Classical


variable [IST : IndexedLOrder I T]

variable (c : T → I) (σ : Finset T) (C : Finset I)

def isColorful : Prop := IST.isCell σ C ∧ σ.image c   = C

variable {c σ C} in
lemma room_of_colorful (h : IST.isColorful c σ C) : IST.isRoom σ C := by sorry

variable {c σ C} in
def pick_colorful_point (h : IST.isColorful c σ C): σ := Classical.choice (sigma_nonempty_of_room (room_of_colorful h)).to_subtype




abbrev colorful := Finset.filter (fun (x : Finset T× Finset I) =>  IST.isColorful c x.1 x.2) Finset.univ



theorem Scarf : (IST.colorful c).Nonempty := sorry

end Scarf


end IndexedLOrder
