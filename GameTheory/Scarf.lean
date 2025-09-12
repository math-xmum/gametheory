import Mathlib

import LLM

open Finset

variable {T : Type*} [Inhabited T] -- The finite set T
variable {I : Type*}
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

variable {σ C} in
lemma Nonempty_of_Dominant (h : IST.isDominant σ C) : C.Nonempty := by
  obtain ⟨j,hj⟩ := h default
  exact ⟨j, hj.1⟩




/- Lemma 1 -/
omit [Inhabited T] in
lemma Dominant_of_subset (σ τ : Finset T) (C : Finset I) :
  τ ⊆ σ → isDominant σ C  → isDominant τ C := by
    intro h1 h2
    intro y
    obtain ⟨j,hj⟩:= h2 y
    use j,hj.1
    intro x hx
    exact hj.2 x (h1 hx)

omit [Inhabited T] in
lemma Dominant_of_supset (σ : Finset T) (C D: Finset I) :
  C ⊆ D → isDominant σ C  → isDominant σ D := by
    intro h1 h2
    intro y
    obtain ⟨j,hj⟩:= h2 y
    use j,(h1 hj.1)
    intro x hx
    exact hj.2 x hx

omit [Inhabited T] in
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

lemma sigma_nonempty_of_room {σ : Finset T} {C : Finset I} (h : isRoom σ C) : σ.Nonempty  := by
  have hC : C.Nonempty := Nonempty_of_Dominant h.1
  have hCpos : 0 < C.card := Finset.card_pos.2 hC
  have h_card : σ.card = C.card := h.2.symm
  have hpos : 0 < σ.card := by rwa [h_card]
  exact Finset.card_pos.1 hpos

/- use |σ| = |C| and C nonempty-/

abbrev isDoor  :=  isCell σ C ∧ C.card = σ.card + 1


variable [DecidableEq T] [DecidableEq I]

inductive isDoorof (τ : Finset T) (D : Finset I) (σ : Finset T) (C : Finset I) : Prop
  | idoor (h0 : isCell σ C) (x :T) (h1 : x ∉ τ) (h2 : insert x τ = σ) (h3 : D = C)
  | odoor (h0 : isCell σ C) (j :I) (h1 : j ∉ C) (h2 : τ = σ) (h3 : D = insert j C)

omit [Inhabited T] in
lemma isCell_of_door (h1 : isDoorof τ D σ C) : IST.isCell τ D := by
  cases h1
  · rename_i h0 j h1 h3 h4
    rw [h4]
    exact IST.Dominant_of_subset _ _ C (by simp [<-h3]) h0
  · rename_i h0 j h1 h2' h3
    rw [h2', h3]
    exact IST.Dominant_of_supset _ _ _ (Finset.subset_insert j C) h0

omit [Inhabited T] in
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

def door_para : Sum σ C.toSet.compl ≃ {(τ,D): (Finset T)× (Finset I) | IST.isDoorof τ D σ C} where
  toFun := fun x => match x with
    | .inl y => ⟨(Finset.erase σ y.1, C), by
     sorry
      ⟩
    | .inr y => ⟨(σ, insert y.1 C), by
     sorry
      ⟩
  invFun := sorry
  left_inv := by
    intro x
    cases x <;> simp_all [Finset.mem_erase, Finset.mem_compl]
    sorry
  right_inv := by
    intro ⟨(τ, D), h⟩
    cases h <;> simp_all [Finset.mem_erase, Finset.mem_compl]
    sorry


lemma room_is_not_door (h1 : IST.isRoom σ C) : ∀ τ D,  ¬ (isDoorof σ C τ D) := sorry



variable (τ D) in
abbrev isOutsideDoor := IST.isDoor τ D ∧ τ = Finset.empty

variable (τ D) in
abbrev isInternalDoor := IST.isDoor τ D ∧ τ.Nonempty

/- Lemma 2-/
omit [Inhabited T] [DecidableEq T] [DecidableEq I] in
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
omit [Inhabited T] [DecidableEq T] [DecidableEq I] in
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

def isNearlyColorful : Prop := IST.isCell σ C ∧ (C \ σ.image c).card = 1


variable {c σ C} in
lemma type_aux (h : isNearlyColorful c σ C) : ∃! i : I, i ∉ σ.image c ∧ C = insert i (σ.image c) := sorry



variable {c σ C} in
def NCtype (h : isNearlyColorful c σ C) : I :=
  Classical.choose (type_aux h).exists


structure TypedNC (i : I) (σ : Finset T) (C : Finset I): Prop where
  nc : isNearlyColorful c σ C
  t : NCtype nc = i


variable {c σ C} in
lemma room_of_colorful (h : IST.isColorful c σ C) : IST.isRoom σ C := by sorry

variable {c σ C} in
def pick_colorful_point (h : IST.isColorful c σ C): σ := Classical.choice (sigma_nonempty_of_room (room_of_colorful h)).to_subtype



/-
Lemma 4 -/
variable {c σ C} in
lemma NC_of_outsidedoor (h : isOutsideDoor σ C) : isNearlyColorful c σ C  := by
  rcases h with ⟨hσ, hC⟩
  rw [isNearlyColorful]
  have : Finset.image c σ = ∅ := by
    rw [hC]
    simp
  rw [this]
  simp [hC]
  constructor
  · rw [isCell, isDominant]
    intro y
    obtain ⟨j, hj⟩ := Nonempty_of_Dominant hσ.1
    use j, hj
    intro x hx
    contradiction
  · rw [hC] at hσ
    exact hσ.2
  <;> simp_all
  sorry


variable {c σ C} in
lemma type_unique_of_outsidedoor (h : isOutsideDoor σ C) : ∃! i,  i = NCtype (NC_of_outsidedoor (c:=c) h)  := by
  obtain ⟨i, rfl⟩ := h.2
  unfold NCtype
  sorry




/-
Lemma 5
-/
lemma NC_or_C_of_door (h1 : isNearlyColorful c τ D) (h2 : isDoorof τ D σ C) : isNearlyColorful c σ C ∨ isColorful c σ C := by
  rcases h2 with ⟨h2_cell, x, hx_notin, hx_insert, hD⟩ | ⟨h2_cell, j, hj_notin, hD, hj_insert⟩
  · left
    rw [isNearlyColorful]
    simp_all [Finset.card_sdiff, Finset.card_insert_of_not_mem, Finset.card_singleton]
    sorry
  · right
    simp_all [Finset.image_insert, Finset.insert_eq_self]
    sorry

lemma NCtype_of_door (h1 : isNearlyColorful c τ D) (h2 : isDoorof τ D σ C) (h3 : isNearlyColorful c σ C) :
    NCtype h1 = NCtype h3 := by sorry


/-Lemma 6 : The version in paper is not correct-/
lemma card_of_NCcell (h : isNearlyColorful c σ D) : #σ = #(image c σ) ∨  #σ + 1 = #(image c σ):= sorry

/- Finset.card_eq_two -/

/-Lemma 7-/
abbrev doors_NCroom  := {(τ,D) | isNearlyColorful c τ D ∧ isDoorof τ D σ C }


lemma card_two_of_doors_NCroom (h0 : isRoom σ C) (h1 : isNearlyColorful c σ C) : (doors_NCroom c σ C).ncard = 2:= sorry



variable [Fintype T] [Fintype I]

abbrev colorful := Finset.filter (fun (x : Finset T× Finset I) =>  IST.isColorful c x.1 x.2) univ


abbrev dbcountingset (i : I):= Finset.filter (fun x : (Finset T× Finset I) × (Finset T× Finset I) => TypedNC c i x.1.1 x.1.2 ∧ isDoorof x.1.1 x.1.2 x.2.1 x.2.2) univ


-- Finset.disjoint_filter_filter_neg
--
lemma dbcount_outside_door' (i : I): ∃! x, x ∈ filter (fun x => isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)  :=  sorry
-- Use Lemme 2


lemma dbcount_outside_door_odd (i : I): Odd (filter (fun x => isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)).card  :=  sorry

lemma dbcount_internal_door_even (i : I) : Even (filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)).card := sorry

lemma dbcount_NCroom (i : I) : Even (filter (fun x => ¬ isColorful c x.2.1 x.2.2) (dbcountingset c i)).card := by
  let s := filter (fun x => ¬isColorful c x.2.1 x.2.2) (dbcountingset c i)
  let t := filter (fun (x : Finset T × Finset I) => IST.isRoom x.1 x.2 ∧ TypedNC c i x.1 x.2 ) univ
  let f := fun (x : (Finset T × Finset I)× Finset T × Finset I) => x.2
  have fs_in_t : ∀ x ∈ s, f x ∈ t := sorry
  have counteq := Finset.card_eq_sum_card_fiberwise fs_in_t
  have fiber_sizetwo :∀ y ∈ t, #(filter (fun a=> f a = y) s) = 2  := sorry
  have sumeq := Finset.sum_const_nat fiber_sizetwo
  rw [sumeq] at counteq
  simp only [counteq, even_two, Even.mul_left]






def dbount_croom (i: I) : (filter (fun x => isColorful c x.2.1 x.2.2) (dbcountingset c i)).card = (filter (fun (x : Finset T × Finset I) => isColorful c x.1 x.2 ∧ i ∈ x.2) univ).card := by
  rw [Finset.filter_filter]
  apply Finset.card_nbij (fun x => x.2)
  · intro x hx; sorry
  · sorry
  · sorry



lemma parity_lemma {a b c d : ℕ }(h1 : Odd a) (h2 : Even b) (h3 : Even d) (h4 : a + b = c + d ): Odd c := by
  by_contra h0
  replace h0 := Nat.not_odd_iff_even.1 h0
  have oddab := Even.odd_add h2 h1
  rw [h4] at oddab
  have evencd := Even.add h0 h3
  exact Nat.not_odd_iff_even.2 evencd oddab


theorem _root_.Finset.card_filter_filter_neg {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p]
 : s.card  = (Finset.filter p s).card + (Finset.filter (fun (a : α) => ¬p a) s).card :=
  by
    nth_rw 1 [<-Finset.filter_union_filter_neg_eq p s]
    apply Finset.card_union_eq_card_add_card.2 (Finset.disjoint_filter_filter_neg _ _ _)


lemma typed_colorful_room_odd (i : I): Odd (Finset.filter (fun (x: Finset T × Finset I) => isColorful c x.1 x.2 ∧ i ∈ x.2) univ).card := by
  let s := dbcountingset c i
  have cardeq' := Finset.card_filter_filter_neg s (fun x => isOutsideDoor x.1.1 x.1.2)
  have cardeq := Finset.card_filter_filter_neg s (fun x => isColorful c x.2.1 x.2.2)
  rw [cardeq'] at cardeq
  apply parity_lemma (dbcount_outside_door_odd c i) (dbcount_internal_door_even c i)  (dbcount_NCroom c i)




variable [Inhabited I]

theorem Scarf : (IST.colorful c).Nonempty := by
  have cardpos := Odd.pos $ typed_colorful_room_odd c default
  replace nonempty:= Finset.card_pos.1 cardpos
  obtain ⟨x,hx⟩ := nonempty
  replace hx := (Finset.mem_filter.1 hx).2
  use x
  simp only [mem_filter, mem_univ, hx, and_self]


end Scarf


end IndexedLOrder
