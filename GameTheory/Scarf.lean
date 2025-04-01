import Mathlib
--import LLMlean

section fiberlemma

open Finset

variable {α β : Type} [DecidableEq α] [DecidableEq β]

lemma injOn_sdiff (s : Finset α) (f : α → β) (h : s.card = (Finset.image f s).card + 1) : ∃ a b, a ∈ s ∧ b ∈ s ∧ f a = f b ∧ a ≠ b ∧ Set.InjOn f (s \ ({a, b} : Finset α)) := by
  have of_card_domain_eq_card_image_succ  (s : Finset α) (f : α → β) (h : s.card = (Finset.image f s).card + 1) :
  ∃ a b, a ∈ s ∧ b ∈ s ∧ f a = f b ∧ a ≠ b := by
    suffices ¬ Set.InjOn f s by
      contrapose! this
      tauto
    by_contra h1
    linarith [Finset.card_image_of_injOn h1]
  obtain ⟨a, b, as, bs, h1, h2⟩ := of_card_domain_eq_card_image_succ s f h
  have absub : {a, b} ⊆ s :=  Finset.insert_subset as (Finset.singleton_subset_iff.mpr bs)
  use a, b
  repeat apply And.intro;assumption
  rw [←Finset.coe_sdiff]
  apply Finset.injOn_of_card_image_eq
  rw [Finset.card_sdiff]
  · have : (Finset.image f (s \ {a, b})).card = (Finset.image f s).card - 1 := by
      have aux1 : ∀ c, c ∈ s → c ≠ a → c ≠ b → f c ≠ f a := by
        intro c cs ca cb fcfa
        have cardabc : ({a, b, c} : Finset α).card = 3 := by
          rw [Finset.card_eq_three]
          use a, b, c
          tauto
        have abcss : {a, b, c} ⊆ s := by
          apply Finset.insert_subset as
          apply Finset.insert_subset bs (by simp [cs])
        have : (image f s).card < s.card - 1 :=
          calc
            _ = (image f ((s \ {a, b, c}) ∪ {a, b, c})).card :=
              congrArg _ (congrArg _ (Eq.symm (sdiff_union_of_subset abcss)))
            _ = (image f (s \ {a, b, c}) ∪ image f {a, b, c}).card :=
              congrArg _ (Finset.image_union _ _)
            _ ≤ (image f (s \ {a, b, c})).card + (image f {a, b, c}).card :=
              Finset.card_union_le _ _
            _ = (image f (s \ {a, b, c})).card + 1 := by
              simp [Finset.card_eq_one]
              exact ⟨f a, by simp [←h1, fcfa]⟩
            _ ≤ (s \ {a, b, c}).card + 1 := by
              simp [Finset.card_image_le]
            _ = s.card - 3 + 1 := by
              rw [Finset.card_sdiff abcss, cardabc]
            _ < _ := by
              have : 2 < s.card := by
                have := Finset.card_le_card abcss
                omega
              omega
        omega
      have aux2 : Finset.image f (s \ {a, b}) = Finset.image f s \ {f a} := by
        ext x
        constructor <;> intro h1'
        · obtain ⟨c, csdiff, fcx⟩ := Finset.mem_image.1 h1'
          obtain ⟨cs, cneab⟩ := Finset.mem_sdiff.1 csdiff
          simp at cneab
          simp
          exact ⟨⟨c, cs, fcx⟩, by simp [← fcx]; exact aux1 c cs cneab.1 cneab.2⟩
        · simp at h1'
          obtain ⟨c, cs, fcx⟩ := h1'.1
          simp [←fcx]
          use c
          simp [cs]
          by_contra! hf
          by_cases ceqa : c = a
          · rw [ceqa] at fcx; rw [fcx] at h1'; tauto
          · rw [hf ceqa, ←h1] at fcx; rw [fcx] at h1; tauto
      rw [aux2, Finset.card_sdiff (by simp; exact ⟨a, as, rfl⟩), card_singleton]
    rw [this,Finset.card_pair h2, h]
    simp
  · exact absub

end fiberlemma


open Classical
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

abbrev mini {σ : Finset T} (h2 : σ.Nonempty) (i : I) : T := @Finset.min' _ (IST i) _ h2

omit [Inhabited T] in
lemma keylemma_of_domiant {σ : Finset T} {C: Finset I} (h1 : IST.isDominant σ C) (h2: σ.Nonempty): σ  = C.image (mini h2)  :=
  by
    ext a
    constructor
    · intro ha
      rw [mem_image]
      by_contra  hm
      push_neg at hm
      obtain ⟨i,hi1,hi2⟩ := h1 a
      replace hm := hm i hi1
      rw [mini] at hm
      have ha1 := @Finset.le_min' _ (IST i) _ h2 a hi2
      have ha2 := @Finset.min'_le _ (IST i) _ _ ha
      apply hm
      refine @eq_of_le_of_le _ (IST i).toPartialOrder _ _ ha2 ha1
    · suffices h: ∀ x ∈ C, mini h2 x = a → a ∈ σ from
      by simp;exact h
      intro _ _ ha
      simp [mini,<-ha,Finset.min'_mem]

omit [Inhabited T] in
lemma card_le_of_domiant {σ : Finset T} {C: Finset I} (h1 : IST.isDominant σ C) : σ.card  ≤  C.card  := by
  by_cases h2 : σ.Nonempty
  · rw [keylemma_of_domiant h1 h2]
    apply Finset.card_image_le
  · rw [not_nonempty_iff_eq_empty] at h2
    simp only [h2, card_empty, zero_le]


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
  | idoor (h0 : isCell σ C) (h1 : isDoor τ D) (x :T) (h1 : x ∉ τ) (h2 : insert x τ = σ) (h3 : D = C)
  | odoor (h0 : isCell σ C) (h1 : isDoor τ D) (j :I) (h1 : j ∉ C) (h2 : τ = σ) (h3 : D = insert j C)

omit [Inhabited T] in
lemma isCell_of_door (h1 : isDoorof τ D σ C) : IST.isCell τ D := by
  cases h1
  · rename_i h0 _ j h1 h3 h4
    rw [h4]
    exact IST.Dominant_of_subset _ _ C (by simp [<-h3]) h0
  · rename_i h0 _ j h1 h2' h3
    rw [h2', h3]
    exact IST.Dominant_of_supset _ _ _ (Finset.subset_insert j C) h0

variable {σ C} in
omit [Inhabited T] in
lemma isRoom_of_Door (h1 : isDoorof τ D σ C) : IST.isRoom σ C := by
  cases h1
  · rename_i h0 h2 x h3 h4 h5
    constructor
    · exact h0
    · simp only [<-h5, h2.2, <-h4, h3, not_false_eq_true, Finset.card_insert_of_not_mem]
  · rename_i h0 h2 x h3 h4 h5
    constructor
    · exact h0
    · have h6 := Finset.card_insert_of_not_mem h3
      subst h4
      replace h5 : D.card = (insert x C).card := by rw [h5]
      rw [h6] at h5
      rw [h2.2] at h5
      exact Eq.symm $ (add_left_inj _).1 h5



/- TODO formula that every room has |I| doors -/
/- This can be skipped first-/

def door_para : Sum σ C.toSet.compl ≃ {(τ,D): (Finset T)× (Finset I) | IST.isDoorof τ D σ C} where
  toFun := fun x => match x with
    | .inl y => ⟨(Finset.erase σ y.1, C), by sorry⟩
    | .inr y => ⟨(σ, insert y.1 C), by sorry⟩
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

omit [Inhabited T] in
lemma room_is_not_door (h1 : IST.isRoom σ C) : ∀ τ D,  ¬ (isDoorof σ C τ D) := by
  intro τ D hd
  unfold isRoom at h1
  cases hd with
  | idoor h0 hd  x h2 h3 h4 =>
    unfold isDoor at hd
    obtain ⟨_,hd⟩ := hd
    have cond : #σ = #σ +1 := by rw [h1.2] at hd; assumption
    simp at cond
  | odoor h0 hd j h2 h3 h4 =>
    unfold isDoor at hd
    obtain ⟨_,hd⟩ := hd
    have cond : #σ = #σ +1 := by rw [h1.2] at hd; assumption
    simp at cond

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
  obtain ⟨_,h3⟩ := h1
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
       (σ = σ₁ ∧ C = C₁) ∨ (σ = σ₂ ∧ C = C₂)) := sorry

end KeyLemma


noncomputable section Scarf

open Classical


--variable [IST : IndexedLOrder I T]

variable (c : T → I) (σ : Finset T) (C : Finset I)

def isColorful : Prop := IST.isCell σ C ∧ σ.image c   = C

def isNearlyColorful : Prop := IST.isCell σ C ∧ (C \ σ.image c).card = 1

def isTypedNC (i : I) (σ : Finset T) (C : Finset I): Prop := IST.isCell σ C ∧ i ∉ (σ.image c) ∧ C = insert i (σ.image c)


variable {c σ C}


/- Easy -/
omit [Inhabited T] [DecidableEq T] in
lemma not_colorful_of_TypedNC (h1 : isTypedNC c i σ C) : ¬ IST.isColorful c σ C := by
  intro h
  unfold isTypedNC at h1
  unfold isColorful at h

  obtain ⟨_, h2, h3⟩ := h1
  obtain ⟨_, h4⟩ := h

  have i_not_in_C : i ∉ C := by
    rw [←h4]
    exact h2
  have i_in_C : i ∈ C := by
    rw [h3]
    exact Finset.mem_insert_self i (σ.image c)
  contradiction

/- Not useful -/
/-
lemma NC_of_TNC (h1 : isTypedNC c i σ C) : isNearlyColorful c σ C := sorry
-/

/-
variable {c σ C} in
lemma type_aux (h : isNearlyColorful c σ C) : ∃! i : I, i ∉ σ.image c ∧ C = insert i (σ.image c) := sorry



variable {c σ C} in
def NCtype (h : isNearlyColorful c σ C) : I :=
  Classical.choose (type_aux h).exists


structure TypedNC (i : I) (σ : Finset T) (C : Finset I): Prop where
  nc : isNearlyColorful c σ C
  t : NCtype nc = i
-/

omit [Inhabited T] [DecidableEq T] in
lemma room_of_colorful (h : IST.isColorful c σ C) : IST.isRoom σ C := by
  unfold isRoom
  unfold isColorful at h
  constructor
  · exact h.1
  · have h1 : C.card = (σ.image c).card := by rw [h.2]
    have h2 : (σ.image c).card ≤ σ.card := Finset.card_image_le
    have h3 : σ.card ≤ C.card := card_le_of_domiant h.1
    linarith



def pick_colorful_point (h : IST.isColorful c σ C): σ := Classical.choice (sigma_nonempty_of_room (room_of_colorful h)).to_subtype


-- Easy
/- Lemma 4 -/
omit [Inhabited T] [DecidableEq T] in
lemma NC_of_outsidedoor (h : isOutsideDoor σ C) : isNearlyColorful c σ C  := by
  cases h with
  | intro hd he =>
    unfold isNearlyColorful
    unfold isCell
    constructor
    · exact hd.1
    · rw [he]
      have h_img : Finset.image c Finset.empty = Finset.empty := Finset.image_empty c
      rw [h_img]
      have h_disj : Disjoint C Finset.empty := Finset.disjoint_empty_right C
      have h_sdiff : C \ Finset.empty = C := Finset.sdiff_eq_self_of_disjoint h_disj
      rw [h_sdiff]
      unfold isDoor at hd
      have h1 := hd.2
      rw [he] at h1
      exact h1



/-
variable {c σ C} in
lemma type_unique_of_outsidedoor (h : isOutsideDoor σ C) : ∃! i,  i = isNCtype (NC_of_outsidedoor (c:=c) h)  := sorry
-/

section useless_lemma
lemma door_of_Croom (h1 : isColorful c σ C) (h2 : isDoorof τ D σ C) : isNearlyColorful c τ D := by sorry

lemma unique_type_door_of_Croom (h1 : isColorful c σ C) (i :I) :
∃! x : Finset T × Finset I , isDoorof x.1 x.2 σ C ∧ isTypedNC c i σ C:= by sorry
end useless_lemma

/-
Lemma 5
-/
lemma NC_or_C_of_door (h1 : isTypedNC c i τ D) (h2 : isDoorof τ D σ C) : isTypedNC c i σ C ∨ isColorful c σ C := sorry


lemma NCtype_of_door (h1 : isTypedNC c i τ D) (h2 : isDoorof τ D σ C) (h3 : isTypedNC c i σ C) : isTypedNC c i τ D := sorry

/-Lemma 6 : The version in paper is not correct-/
lemma card_of_NCcell (h : isNearlyColorful c σ C) : #σ = #(image c σ) ∨  #σ + 1 = #(image c σ):= sorry

/- Finset.card_eq_two -/

/-Lemma 7-/
variable (c σ C) in
abbrev doors_NCroom (i : I):= {(τ,D) | isTypedNC c i τ D ∧ isDoorof τ D σ C }

lemma doors_of_NCroom (h0 : isRoom σ C) (h1 : isTypedNC c i σ C) : ∃ x y, x ≠ y ∧  doors_NCroom c σ C i = {x,y} := by
  sorry


lemma card_two_of_doors_NCroom (h0 : isRoom σ C) (h1 : isTypedNC c i σ C) : (doors_NCroom c σ C i).ncard = 2:=
  by
    obtain ⟨x,y,hx1,hx2⟩ := doors_of_NCroom h0 h1
    simp [hx1,hx2]

variable [Fintype T] [Fintype I]

variable (c) in
abbrev colorful := Finset.filter (fun (x : Finset T× Finset I) =>  IST.isColorful c x.1 x.2) univ

variable (c) in
abbrev dbcountingset (i : I):= Finset.filter (fun x : (Finset T× Finset I) × (Finset T× Finset I) => isTypedNC c i x.1.1 x.1.2 ∧ isDoorof x.1.1 x.1.2 x.2.1 x.2.2) univ


-- Finset.disjoint_filter_filter_neg
--
variable (c) in
lemma dbcount_outside_door' (i : I): ∃ x,  filter (fun x => isOutsideDoor x.1.1 x.1.2) (dbcountingset c i) = {x}  :=  sorry

variable (c)

-- Use Lemme 2
lemma dbcount_outside_door_odd (i : I): Odd (filter (fun x => isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)).card  := by
  have cardone: (filter (fun x => isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)).card = 1 := by
    obtain ⟨x,hx⟩ := dbcount_outside_door' c i
    simp [hx]
  convert odd_one

lemma dbcount_internal_door_even (i : I) : Even (filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)).card := sorry

/- Easy -/
variable {c} in
lemma NC_of_NCdoor (h1 : isTypedNC c i τ D)
(h2 : isDoorof τ D σ C) :
  ¬ isColorful c σ C → isTypedNC c i σ C := by
  -- use  lemma NC_or_C_of_door

  sorry

variable {c} in
lemma firber2_doors_NCroom (h0 : isRoom σ C) (h1 : isTypedNC c i σ C) :
  (filter (fun (x : (Finset T× Finset I)× Finset T × Finset I) => x.2 = (σ,C)) (dbcountingset c i)).card = 2 := by
    sorry

lemma dbcount_NCroom (i : I) : Even (filter (fun x => ¬ isColorful c x.2.1 x.2.2) (dbcountingset c i)).card := by
  let s := filter (fun x => ¬isColorful c x.2.1 x.2.2) (dbcountingset c i)
  let t := filter (fun (x : Finset T × Finset I) => IST.isRoom x.1 x.2 ∧ isTypedNC c i x.1 x.2 ) univ
  let f := fun (x : (Finset T × Finset I)× Finset T × Finset I) => x.2
  have fs_in_t : ∀ x ∈ s, f x ∈ t := by
    intro x hx;
    show x.2 ∈ t
    rw [mem_filter] at hx
    obtain ⟨hx1,hx2⟩ := hx
    rw [mem_filter] at hx1
    rw [mem_filter]
    refine ⟨by simp, isRoom_of_Door hx1.2.2,?_⟩
    apply NC_of_NCdoor hx1.2.1 hx1.2.2 hx2
  have counteq := Finset.card_eq_sum_card_fiberwise fs_in_t
  have fiber_sizetwo :∀ y ∈ t, #(filter (fun a=> f a = y) s) = 2  :=
    by
      intro y hy
      rw [Finset.mem_filter] at hy
      obtain ⟨_,hy1,hy2⟩ := hy
      unfold s
      rw [filter_filter]
      have f2 := firber2_doors_NCroom hy1 hy2
      rw [<-f2]
      congr 1
      apply filter_congr
      intro x hx
      rw [mem_filter] at hx
      obtain ⟨hx1,hx2,hx3⟩ := hx
      unfold f
      constructor
      · simp
      · intro h
        simp_rw [h,and_true]
        exact not_colorful_of_TypedNC hy2
  have sumeq := Finset.sum_const_nat fiber_sizetwo
  rw [sumeq] at counteq
  rw [counteq]
  simp only [even_two, Even.mul_left]

lemma parity_lemma {a b c d : ℕ } (h1 : Odd a) (h2 : Even b) (h3 : Even d) (h4 : a + b = c + d ): Odd c := by
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

lemma typed_colorful_room_odd (i : I): Odd (Finset.filter (fun (x: (Finset T× Finset I) × Finset T × Finset I) =>  isColorful c x.2.1 x.2.2) (dbcountingset c i)).card
:= by
  let s:= dbcountingset c i
  have cardeq' := Finset.card_filter_filter_neg s (fun x => isOutsideDoor x.1.1 x.1.2)
  have cardeq := Finset.card_filter_filter_neg s (fun x => isColorful c x.2.1 x.2.2)
  apply parity_lemma (dbcount_outside_door_odd c i) (dbcount_internal_door_even c i) (dbcount_NCroom c i)
  rw [<-cardeq',<-cardeq]

variable [Inhabited I]

theorem Scarf : (IST.colorful c).Nonempty := by
  have cardpos := Odd.pos $ typed_colorful_room_odd c default
  replace nonempty:= Finset.card_pos.1 cardpos
  obtain ⟨x,hx⟩ := nonempty
  replace hx := (Finset.mem_filter.1 hx).2
  use x.2
  simp only [mem_filter, mem_univ, hx, and_self]

end Scarf


end IndexedLOrder
