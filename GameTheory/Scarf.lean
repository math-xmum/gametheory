import Mathlib
--import LLMlean

section fiberlemma

open Finset

universe u v
variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

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
    · simp only [Finset.card_singleton, Finset.card_eq_zero]
      rfl
  · rfl


--variable (τ D) in
omit [Inhabited T] [DecidableEq T] [DecidableEq I] in
lemma outsidedoor_is_singleton (h : IST.isOutsideDoor τ  D) :  τ = Finset.empty ∧  ∃ i, D = {i} := by
  obtain ⟨h1, h2⟩ := h
  subst h2
  obtain ⟨_,h3⟩ := h1
  replace h4 : D.card = 1 := by
    simp_all only [Finset.card_eq_zero, Nat.zero_add]
    rfl
  exact ⟨rfl, Finset.card_eq_one.1 h4⟩


section KeyLemma

-- Helper lemma: existence of elements greater than all minimums except one
lemma exists_greater_than_all_mins_except_one {τ : Finset T} {D : Finset I} (h_τ_nonempty : τ.Nonempty)
    (h_D_card_ge_2 : 2 ≤ D.card) (i : I) (hi_in_D : i ∈ D) :
    ∃ y, ∀ k ∈ D \ {i}, mini h_τ_nonempty k <[k] y := by
  have h_D_diff_nonempty : (D \ {i}).Nonempty := by
    have h_exists_other : ∃ j ∈ D, j ≠ i := by
      by_contra h_all_eq_i
      push_neg at h_all_eq_i
      have h_D_eq_singleton : D = {i} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hi_in_D, h_all_eq_i⟩
      have h_card_eq_1 : D.card = 1 := by rw [h_D_eq_singleton, Finset.card_singleton]
      linarith [h_D_card_ge_2, h_card_eq_1]
    obtain ⟨j, hj_in_D, hj_ne_i⟩ := h_exists_other
    use j
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨hj_in_D, hj_ne_i⟩
  have exists_larger_for_each_k : ∀ k' ∈ (D \ {i}), ∃ y_k', mini h_τ_nonempty k' <[k'] y_k' := by
    intro k' hk'_mem
    classical
    sorry
  choose y_map hy_map_spec using exists_larger_for_each_k

  sorry

-- Helper lemma: if m₁ is in M i₁ and x is in τ, then m₁ ≤[i₁] x
lemma m1_le_tau_elements {τ : Finset T} {D : Finset I} {i₁ : I} {m₁ : T}
    (h_τ_nonempty : τ.Nonempty)
    (M : I → Set T)
    (hm₁_in_Mi1 : m₁ ∈ M i₁) (hi₁_in_D : i₁ ∈ D) (x : T) (hx_in_τ : x ∈ τ) :
    m₁ ≤[i₁] x := by
  sorry

-- Helper lemma: if y is dominated in τ and m₁ has special property, then y ≤[j] m₁
lemma dominated_element_le_special {τ : Finset T} {D : Finset I} {i₁ j : I} {m₁ y : T}
    (h_cell_τD : IST.isCell τ D)
    (h_τ_nonempty : τ.Nonempty) (hm₁_special : ∀ k ∈ D \ {i₁}, mini h_τ_nonempty k <[k] m₁)
    (hi₁_in_D : i₁ ∈ D) (hj_in_D : j ∈ D)
    (hj_dominates : ∀ x ∈ τ, y ≤[j] x) : y ≤[j] m₁ := by
  sorry

-- Helper lemma: special element dominates minimum in its own order
omit [Inhabited T] [DecidableEq T] in
lemma special_element_dominates_own_mini {τ : Finset T} {D : Finset I} {i : I} {m : T}
    (_ : IST.isCell τ D) (h_τ_nonempty : τ.Nonempty)
    (_ : ∀ k ∈ D \ {i}, mini h_τ_nonempty k <[k] m) (_ : i ∈ D)
    (hm_dominates_own_mini : mini h_τ_nonempty i ≤[i] m) :
    mini h_τ_nonempty i ≤[i] m := by
  exact hm_dominates_own_mini

-- Helper lemma: transitivity through minimum in indexed order
omit [Inhabited T] [DecidableEq T] [DecidableEq I] in
lemma le_trans_through_mini {k : I} {y x : T} {τ : Finset T} (h_τ_nonempty : τ.Nonempty)
    (hy_le_mini : y ≤[k] mini h_τ_nonempty k) (hmini_lt_x : mini h_τ_nonempty k <[k] x) :
    y ≤[k] x := by
  have h_le_of_lt_k : mini h_τ_nonempty k ≤[k] x := @le_of_lt T (IST k).toPartialOrder.toPreorder (mini h_τ_nonempty k) x hmini_lt_x
  exact @le_trans T (IST k).toPartialOrder.toPreorder y (mini h_τ_nonempty k) x hy_le_mini h_le_of_lt_k

-- Helper lemma: if y is dominated by τ under order j, then y ≤[j] mini
omit [Inhabited T] [DecidableEq T] [DecidableEq I] in
lemma dominated_le_mini {j : I} {y : T} {τ : Finset T} (h_τ_nonempty : τ.Nonempty)
    (hj_dominates : ∀ x ∈ τ, y ≤[j] x) : y ≤[j] mini h_τ_nonempty j := by
  apply hj_dominates
  exact @Finset.min'_mem _ (IST j) _ h_τ_nonempty

-- Helper lemma: adding a special element preserves cell property
omit [Inhabited T] in
lemma cell_preserved_by_adding_special_element {τ : Finset T} {D : Finset I} {i : I} {m : T}
    (h_cell_τD : IST.isCell τ D)
    (h_τ_nonempty : τ.Nonempty) (_ : m ∉ τ)
    (hm_special : ∀ k ∈ D \ {i}, mini h_τ_nonempty k <[k] m) (_ : i ∈ D)
    (hm_dominates_mini_i : mini h_τ_nonempty i ≤[i] m) :
    IST.isCell (insert m τ) D := by
  intro y
  obtain ⟨j, hj_in_D, hj_dominates_τ⟩ := h_cell_τD y
  use j, hj_in_D

  intro x hx_in_insert
  cases' Finset.mem_insert.mp hx_in_insert with hx_eq_m hx_in_τ

  case inl =>
    rw [hx_eq_m]
    cases' Classical.em (j = i) with hj_eq_i hj_ne_i
    case inl =>
      rw [hj_eq_i] at hj_dominates_τ
      have hy_le_mini : y ≤[i] mini h_τ_nonempty i :=
        dominated_le_mini h_τ_nonempty hj_dominates_τ
      rw [hj_eq_i]
      exact @le_trans T (IST i).toPartialOrder.toPreorder y (mini h_τ_nonempty i) m hy_le_mini hm_dominates_mini_i

    case inr =>
      have hj_in_diff : j ∈ D \ {i} := by
        simp [Finset.mem_sdiff, Finset.mem_singleton]
        exact ⟨hj_in_D, hj_ne_i⟩

      have hmini_lt_m : mini h_τ_nonempty j <[j] m := hm_special j hj_in_diff
      have hy_le_mini : y ≤[j] mini h_τ_nonempty j :=
        dominated_le_mini h_τ_nonempty hj_dominates_τ
      exact le_trans_through_mini h_τ_nonempty hy_le_mini hmini_lt_m

  case inr =>
    exact hj_dominates_τ x hx_in_τ

-- Helper lemma: construction of special sets M
lemma construct_special_sets {τ : Finset T} {D : Finset I} (h_cell_τD : IST.isCell τ D) (h_τ_nonempty : τ.Nonempty)
    (h_D_card_ge_2 : 2 ≤ D.card) (i₁ i₂ : I) (hi₁_in_D : i₁ ∈ D) (hi₂_in_D : i₂ ∈ D)
    (hi₁_ne_i₂ : i₁ ≠ i₂) (h_f_i1_eq_f_i2 : mini h_τ_nonempty i₁ = mini h_τ_nonempty i₂) :
    let M (idx : I) : Set T := if idx ∈ D then {y | (∀ k ∈ D \ {idx}, mini h_τ_nonempty k <[k] y) ∧ mini h_τ_nonempty idx ≤[idx] y} else ∅
    ∃ (m₁ m₂ : T), m₁ ∈ M i₁ ∧ m₂ ∈ M i₂ ∧ m₁ ∉ τ ∧ m₂ ∉ τ ∧ m₁ ≠ m₂ := by
  -- The construction ensures that:
  -- 1. For k ≠ idx: mini k <[k] y (y is above other minimums)
  -- 2. mini idx ≤[idx] y (y is above its own minimum)
  -- This guarantees the properties needed for room extension
  sorry

-- Helper lemma: uniqueness of room extensions
lemma unique_room_extensions {τ : Finset T} {D : Finset I} (h_cell_τD : IST.isCell τ D) (h_door : IST.isDoor τ D)
    (m₁ m₂ : T) (hm₁_notin_τ : m₁ ∉ τ) (hm₂_notin_τ : m₂ ∉ τ) (hm₁_ne_m₂ : m₁ ≠ m₂)
    (h_room₁ : IST.isRoom (insert m₁ τ) D) (h_room₂ : IST.isRoom (insert m₂ τ) D) :
    ∀ σ C, IST.isRoom σ C → isDoorof τ D σ C →
      (σ = insert m₁ τ ∧ C = D) ∨ (σ = insert m₂ τ ∧ C = D) := by
  sorry

/- Lemma 3-/
theorem internal_door_two_rooms (τ : Finset T) (D : Finset I)
    (h_int_door : IST.isInternalDoor τ D) :
    ∃ (σ₁ σ₂ : Finset T) (C₁ C₂ : Finset I),
      σ₁ ≠ σ₂ ∧
      IST.isRoom σ₁ C₁ ∧
      IST.isRoom σ₂ C₂ ∧
      isDoorof τ D σ₁ C₁ ∧
      isDoorof τ D σ₂ C₂ ∧
      (∀ σ C, IST.isRoom σ C → isDoorof τ D σ C →
       (σ = σ₁ ∧ C = C₁) ∨ (σ = σ₂ ∧ C = C₂)) := by

  obtain ⟨h_door, h_τ_nonempty⟩ := h_int_door
  obtain ⟨h_cell_τD, h_card_D_eq_τ_plus_1⟩ := h_door
  have h_τ_card_pos : 0 < τ.card := Finset.card_pos.mpr h_τ_nonempty
  have h_τ_card_ge_1 : 1 ≤ τ.card := Nat.one_le_of_lt h_τ_card_pos
  have h_D_card_ge_2 : 2 ≤ D.card := by linarith [h_card_D_eq_τ_plus_1, h_τ_card_ge_1]
  have h_D_gt_zero : 0 < D.card := by linarith [h_D_card_ge_2]
  have h_D_nonempty : D.Nonempty := (Finset.card_pos (s:=D)).mp h_D_gt_zero

  let f : I → T := fun i_idx => mini h_τ_nonempty i_idx
  have h_mini_def_eq_f : mini h_τ_nonempty = f := by { funext i_ex; simp [f, mini] }
  have h_τ_eq_img_f_D : τ = D.image f := by
    rw [←h_mini_def_eq_f]
    convert keylemma_of_domiant h_cell_τD h_τ_nonempty
  have h_τ_card_eq_img_f_D_card : τ.card = (D.image f).card := by rw [h_τ_eq_img_f_D]
  have h_D_card_eq_img_f_D_card_plus_1 : D.card = (D.image f).card + 1 := by
    rw [h_card_D_eq_τ_plus_1, h_τ_card_eq_img_f_D_card]

  obtain ⟨i₁, i₂, hi₁D, hi₂D, h_f_i1_eq_f_i2, hi₁_ne_i₂, h_inj_on_rest⟩ :=
    injOn_sdiff (α := I) (β := T) D f h_D_card_eq_img_f_D_card_plus_1

  -- Use the helper lemma to construct m₁ and m₂
  obtain ⟨m₁, m₂, hm₁_in_Mi1, hm₂_in_Mi2, hm₁_notin_τ, hm₂_notin_τ, hm₁_ne_m₂⟩ :=
    construct_special_sets h_cell_τD h_τ_nonempty h_D_card_ge_2 i₁ i₂ hi₁D hi₂D hi₁_ne_i₂ h_f_i1_eq_f_i2

  let σ₁_cand := insert m₁ τ
  let C₁_cand := D
  let σ₂_cand := insert m₂ τ
  let C₂_cand := D

  -- Prove that σ₁_cand and σ₂_cand are rooms
  have h_room₁ : IST.isRoom σ₁_cand C₁_cand := by
    constructor
    · -- Prove isCell σ₁_cand C₁_cand
      have hm₁_special : ∀ k ∈ D \ {i₁}, mini h_τ_nonempty k <[k] m₁ := by
        -- Extract the property from hm₁_in_Mi1
        have M_def : let M (idx : I) : Set T := if idx ∈ D then {y | (∀ k ∈ D \ {idx}, mini h_τ_nonempty k <[k] y) ∧ mini h_τ_nonempty idx ≤[idx] y} else ∅
                     m₁ ∈ M i₁ := hm₁_in_Mi1
        simp only [Set.mem_setOf_eq] at M_def
        have hi₁_in_D_check : i₁ ∈ D := hi₁D
        rw [if_pos hi₁_in_D_check] at M_def
        exact M_def.1
      exact cell_preserved_by_adding_special_element h_cell_τD h_τ_nonempty hm₁_notin_τ hm₁_special hi₁D
        (special_element_dominates_own_mini h_cell_τD h_τ_nonempty hm₁_special hi₁D
          (by -- Extract the second property from hm₁_in_Mi1
             have M_def : let M (idx : I) : Set T := if idx ∈ D then {y | (∀ k ∈ D \ {idx}, mini h_τ_nonempty k <[k] y) ∧ mini h_τ_nonempty idx ≤[idx] y} else ∅
                          m₁ ∈ M i₁ := hm₁_in_Mi1
             simp only [Set.mem_setOf_eq] at M_def
             have hi₁_in_D_check : i₁ ∈ D := hi₁D
             rw [if_pos hi₁_in_D_check] at M_def
             exact M_def.2))
    · -- Prove C₁_cand.card = σ₁_cand.card
      simp [σ₁_cand, C₁_cand]
      rw [Finset.card_insert_of_not_mem hm₁_notin_τ, h_card_D_eq_τ_plus_1]

  have h_room₂ : IST.isRoom σ₂_cand C₂_cand := by
    constructor
    · -- Prove isCell σ₂_cand C₂_cand
      have hm₂_special : ∀ k ∈ D \ {i₂}, mini h_τ_nonempty k <[k] m₂ := by
        -- Extract the property from hm₂_in_Mi2
        have M_def : let M (idx : I) : Set T := if idx ∈ D then {y | (∀ k ∈ D \ {idx}, mini h_τ_nonempty k <[k] y) ∧ mini h_τ_nonempty idx ≤[idx] y} else ∅
                     m₂ ∈ M i₂ := hm₂_in_Mi2
        simp only [Set.mem_setOf_eq] at M_def
        have hi₂_in_D_check : i₂ ∈ D := hi₂D
        rw [if_pos hi₂_in_D_check] at M_def
        exact M_def.1
      exact cell_preserved_by_adding_special_element h_cell_τD h_τ_nonempty hm₂_notin_τ hm₂_special hi₂D
        (special_element_dominates_own_mini h_cell_τD h_τ_nonempty hm₂_special hi₂D
          (by -- Extract the second property from hm₂_in_Mi2
             have M_def : let M (idx : I) : Set T := if idx ∈ D then {y | (∀ k ∈ D \ {idx}, mini h_τ_nonempty k <[k] y) ∧ mini h_τ_nonempty idx ≤[idx] y} else ∅
                          m₂ ∈ M i₂ := hm₂_in_Mi2
             simp only [Set.mem_setOf_eq] at M_def
             have hi₂_in_D_check : i₂ ∈ D := hi₂D
             rw [if_pos hi₂_in_D_check] at M_def
             exact M_def.2))
    · -- Prove C₂_cand.card = σ₂_cand.card
      simp [σ₂_cand, C₂_cand]
      rw [Finset.card_insert_of_not_mem hm₂_notin_τ, h_card_D_eq_τ_plus_1]

  -- Prove that they are doors of τ D
  have h_doorof₁ : isDoorof τ D σ₁_cand C₁_cand :=
    isDoorof.idoor (h_room₁.1) ⟨h_cell_τD, h_card_D_eq_τ_plus_1⟩ m₁ hm₁_notin_τ rfl rfl

  have h_doorof₂ : isDoorof τ D σ₂_cand C₂_cand :=
    isDoorof.idoor (h_room₂.1) ⟨h_cell_τD, h_card_D_eq_τ_plus_1⟩ m₂ hm₂_notin_τ rfl rfl

  -- Prove that σ₁_cand ≠ σ₂_cand
  have h_σ₁_ne_σ₂ : σ₁_cand ≠ σ₂_cand := by
    intro h_eq_contra
    have : m₁ ∈ σ₂_cand := by
      rw [←h_eq_contra]
      exact Finset.mem_insert_self m₁ τ
    simp [σ₂_cand] at this
    cases this with
    | inl hm₁eqm₂ => exact hm₁_ne_m₂ hm₁eqm₂
    | inr hm₁inτ => exact hm₁_notin_τ hm₁inτ

  -- Use the uniqueness helper lemma
  have h_uniqueness := unique_room_extensions h_cell_τD ⟨h_cell_τD, h_card_D_eq_τ_plus_1⟩
    m₁ m₂ hm₁_notin_τ hm₂_notin_τ hm₁_ne_m₂ h_room₁ h_room₂

  use σ₁_cand, σ₂_cand, C₁_cand, C₂_cand

end KeyLemma


noncomputable section Scarf

open Classical


--variable [IST : IndexedLOrder I T]

variable (c : T → I) (σ : Finset T) (C : Finset I)

def isColorful : Prop := IST.isCell σ C ∧ σ.image c   = C

def isNearlyColorful : Prop := IST.isCell σ C ∧ (C \ σ.image c).card = 1

def isTypedNC (i : I) (σ : Finset T) (C : Finset I): Prop := IST.isCell σ C ∧ i ∉ (σ.image c) ∧ C = insert i (σ.image c)


variable {c σ C}


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

omit [Inhabited T] [DecidableEq T] in
lemma NC_of_TNC (h1 : isTypedNC c i σ C) : isNearlyColorful c σ C := by
  obtain ⟨hcell, hnotin, heq⟩ := h1
  constructor
  · exact hcell
  · rw [heq]
    have h_eq : C \ image c σ = {i} := by
      rw [heq]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro h
        exact h.1.resolve_right h.2
      · intro h_xi
        rw [h_xi]
        exact ⟨Or.inl rfl, hnotin⟩
    rw [←heq, h_eq]
    exact Finset.card_singleton i



lemma type_aux (h : isNearlyColorful c σ C) : ∃! i : I, i ∉ σ.image c ∧ C = insert i (σ.image c) := by
  obtain ⟨_, h_card_sdiff_eq_1⟩ := h
  rw [Finset.card_eq_one] at h_card_sdiff_eq_1
  obtain ⟨i, hi_eq⟩ := h_card_sdiff_eq_1 -- hi_eq : C \ image c σ = {i}
  use i
  dsimp only
  constructor
  · -- Prove P(i): i ∉ σ.image c ∧ C = insert i (σ.image c)
    have hi_in_C_and_notin_image : i ∈ C ∧ i ∉ image c σ := by
      rw [← Finset.mem_sdiff, hi_eq]
      exact Finset.mem_singleton_self i
    constructor
    · exact hi_in_C_and_notin_image.2
    · sorry
  sorry

def NCtype (h : isNearlyColorful c σ C) : I :=
  Classical.choose (type_aux h).exists


structure TypedNC (i : I) (σ : Finset T) (C : Finset I): Prop where
  nc : isNearlyColorful c σ C
  t : NCtype nc = i


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


omit [Inhabited T] in
lemma NCtype_of_door (h1 : isTypedNC c i τ D) (_ : isDoorof τ D σ C) (_ : isTypedNC c i σ C) : isTypedNC c i τ D := h1

/-Lemma 6 : The version in paper is incorrect-/
lemma card_of_NCcell (h : isNearlyColorful c σ C) : #σ = #(image c σ) ∨  #σ + 1 = #(image c σ):= sorry

/- Finset.card_eq_two -/

/-Lemma 7-/
variable (c σ C) in
abbrev doors_NCroom (i : I):= {(τ,D) | isTypedNC c i τ D ∧ isDoorof τ D σ C }

omit [DecidableEq T] in
lemma doors_of_NCroom [DecidableEq T] (h0 : isRoom σ C) (h1 : isTypedNC c i σ C) : ∃ x y, x ≠ y ∧ doors_NCroom c σ C i = {x, y} := by

  have h_nc : isNearlyColorful c σ C := by
    obtain ⟨hcell, hnotin, heq⟩ := h1
    constructor
    · exact hcell
    · rw [heq]
      have h_eq : C \ image c σ = {i} := by
        rw [heq]
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro h
          exact h.1.resolve_right h.2
        · intro h_xi
          rw [h_xi]
          exact ⟨Or.inl rfl, hnotin⟩
      rw [←heq, h_eq]
      exact Finset.card_singleton i

  obtain h_card_case | h_card_case := card_of_NCcell h_nc
  · exfalso

    have h_card_C_eq_card_image_plus_1 : #C = #(image c σ) + 1 := by
      rw [h1.2.2]
      exact Finset.card_insert_of_not_mem h1.2.1
    linarith [h_card_C_eq_card_image_plus_1, h0.2, h_card_case]

  · exfalso
    have h_image_le_sigma : #(image c σ) ≤ #σ := Finset.card_image_le
    linarith [h_image_le_sigma, h_card_case]

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
lemma dbcount_outside_door' (i : I): ∃ x,  filter (fun x => isOutsideDoor x.1.1 x.1.2) (dbcountingset c i) = {x}  :=  by
  classical

  have h_T_nonempty : Nonempty T := ⟨(default : T)⟩
  have h_T_univ_nonempty : (Finset.univ : Finset T).Nonempty := Finset.univ_nonempty_iff.mpr h_T_nonempty
  let x_max_i : T := @Finset.max' T (IST i) Finset.univ h_T_univ_nonempty
  let σ_u : Finset T := {x_max_i}
  let C_u : Finset I := {i}
  let τ_u : Finset T := Finset.empty
  let D_u : Finset I := {i}
  let x_unique : (Finset T × Finset I) × (Finset T × Finset I) := ((τ_u, D_u), (σ_u, C_u))

  use x_unique
  ext x_gen
  simp only [mem_filter, mem_univ, mem_singleton]

  constructor
  · -- If x_gen is in the filter, then x_gen = x_unique
    intro h_in_filter
    -- h_in_filter tells us x_gen is in the filtered dbcountingset and satisfies isOutsideDoor
    simp only [mem_filter] at h_in_filter
    obtain ⟨h_in_db, h_outside⟩ := h_in_filter
    simp only [dbcountingset, mem_filter, mem_univ, true_and] at h_in_db
    obtain ⟨h_typed, h_door⟩ := h_in_db

    -- From isOutsideDoor
    obtain ⟨h_is_door, h_empty⟩ := h_outside

    -- Derive the key facts directly
    have h_empty_image : (x_gen.1.1).image c = ∅ := by
      rw [h_empty]
      exact Finset.image_empty c
    have h_x_gen_1_2_eq : x_gen.1.2 = {i} := by
      -- From h_typed: isTypedNC c i x_gen.1.1 x_gen.1.2
      obtain ⟨_, h_i_notin, h_eq⟩ := h_typed
      rw [h_eq, h_empty_image]
      simp

    -- Use outsidedoor_is_singleton to get the structure
    obtain ⟨_, h_D_singleton⟩ := outsidedoor_is_singleton ⟨h_is_door, h_empty⟩
    obtain ⟨j, h_D_eq⟩ := h_D_singleton

    -- Show j = i
    have h_j_eq_i : j = i := by
      -- We know x_gen.1.2 = {i} from h_x_gen_1_2_eq
      -- We also know from outsidedoor_is_singleton that x_gen.1.2 = {j}
      have h_eq_j : x_gen.1.2 = {j} := h_D_eq
      rw [h_x_gen_1_2_eq] at h_eq_j
      have : j ∈ {j} := Finset.mem_singleton_self j
      rw [←h_eq_j] at this
      exact Finset.eq_of_mem_singleton this

    -- Now we need to determine the room structure
    -- From isDoorof, we know either it's an idoor or odoor
    cases h_door with
    | idoor h_cell_σC h_door_τD x h_x_notin h_insert_eq h_D_eq_C =>
      -- In this case, σ = insert x τ and C = D
      -- Since τ = ∅ (from h_empty), we have σ = {x}
      have h_σ_eq : x_gen.2.1 = {x} := by
        rw [←h_insert_eq, h_empty]
        rfl

      -- We need to show x = x_max_i
      have h_x_eq_max : x = x_max_i := by
        -- From h_cell_σC, we know {x} is dominated by {i}
        -- This means for all y, y ≤[i] x
        -- Since x_max_i is the maximum element under order i, we must have x = x_max_i
        have h_dom : ∀ y, y ≤[i] x := by
          intro y
          obtain ⟨j_dom, hj_in, hj_dom⟩ := h_cell_σC y
          rw [←h_D_eq_C, h_x_gen_1_2_eq] at hj_in
          simp at hj_in
          subst hj_in
          apply hj_dom
          rw [h_σ_eq]
          simp
        -- x_max_i is the maximum, so x ≤[i] x_max_i
        have h1 : x ≤[i] x_max_i := @Finset.le_max' T (IST i) Finset.univ x (Finset.mem_univ x)
        -- But also x_max_i ≤[i] x by h_dom
        have h2 : x_max_i ≤[i] x := h_dom x_max_i
        -- Therefore x = x_max_i
        exact @le_antisymm T (IST i).toPartialOrder x x_max_i h1 h2

      -- Conclude by showing the components are equal
      apply Prod.ext
      · -- First component pair
        apply Prod.ext
        · exact h_empty
        · rw [h_x_gen_1_2_eq]
      · -- Second component pair
        apply Prod.ext
        · rw [h_σ_eq, h_x_eq_max]
        · rw [←h_D_eq_C, h_x_gen_1_2_eq]

    | odoor h_cell_σC h_door_τD j h_j_notin h_τ_eq h_D_insert =>
      -- In this case, τ = σ and D = insert j C
      -- But τ = ∅, so σ = ∅, which contradicts that we need a room
      -- This case is impossible for an outside door
      exfalso
      have h_σ_empty : x_gen.2.1 = ∅ := by
        rw [←h_τ_eq, h_empty]
        rfl
      -- Construct the isDoorof for this case
      let h_door_constructed : isDoorof x_gen.1.1 x_gen.1.2 x_gen.2.1 x_gen.2.2 :=
        isDoorof.odoor h_cell_σC ⟨h_is_door.1, h_is_door.2⟩ j h_j_notin h_τ_eq h_D_insert
      have h_room : IST.isRoom x_gen.2.1 x_gen.2.2 := isRoom_of_Door h_door_constructed
      have h_σ_nonempty : x_gen.2.1.Nonempty := sigma_nonempty_of_room h_room
      rw [h_σ_empty] at h_σ_nonempty
      exact Finset.not_nonempty_empty h_σ_nonempty

  · -- If x_gen = x_unique, then it's in the filter
    intro h_eq
    rw [h_eq]
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · sorry-- Prove isOutsideDoor x_unique.1.1 x_unique.1.2
      -- x_unique.1.1 is τ_u (Finset.empty), x_unique.1.2 is D_u ({i})
    · sorry

variable (c)

-- Use Lemme 2
lemma dbcount_outside_door_odd (i : I): Odd (filter (fun x => isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)).card  := by
  have cardone: (filter (fun x => isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)).card = 1 := by
    obtain ⟨x,hx⟩ := dbcount_outside_door' c i
    simp [hx]
  convert odd_one

lemma fiber_size_internal_door (c : T → I) (i : I) (y : Finset T × Finset I)
    (hy_internal : IST.isInternalDoor y.1 y.2) (hy_typed : isTypedNC c i y.1 y.2) :
    let s := filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)
    let f := fun (x : (Finset T × Finset I) × Finset T × Finset I) => x.1
    (filter (fun a => f a = y) s).card = 2 := by
  -- Apply internal_door_two_rooms to get exactly 2 rooms
  obtain ⟨σ₁, σ₂, C₁, C₂, h_ne, h_room₁, h_room₂, h_door₁, h_door₂, h_unique⟩ :=
    internal_door_two_rooms y.1 y.2 hy_internal

  let s := filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)
  let f := fun (x : (Finset T × Finset I) × Finset T × Finset I) => x.1

  -- The fiber consists of exactly (y, (σ₁, C₁)) and (y, (σ₂, C₂))
  let elem1 : (Finset T × Finset I) × Finset T × Finset I := (y, (σ₁, C₁))
  let elem2 : (Finset T × Finset I) × Finset T × Finset I := (y, (σ₂, C₂))

  -- Both elements are in s
  have elem1_in_s : elem1 ∈ s := by
    simp only [elem1, s, mem_filter]
    constructor
    · simp only [dbcountingset, mem_filter, mem_univ, true_and]
      exact ⟨hy_typed, h_door₁⟩
    · -- Show not outside door
      intro h_outside -- h_outside : isOutsideDoor y.1 y.2
      -- hy_internal.2 : y.1.Nonempty
      -- h_outside.2 : y.1 = Finset.empty
      exact (Finset.nonempty_iff_ne_empty.mp hy_internal.2) h_outside.2

  have elem2_in_s : elem2 ∈ s := by
    simp only [elem2, s, mem_filter]
    constructor
    · simp only [dbcountingset, mem_filter, mem_univ, true_and]
      exact ⟨hy_typed, h_door₂⟩
    · -- Show not outside door
      intro h_outside -- h_outside : isOutsideDoor y.1 y.2
      exact (Finset.nonempty_iff_ne_empty.mp hy_internal.2) h_outside.2

  -- The elements are distinct
  have elems_distinct : elem1 ≠ elem2 := by
    simp only [elem1, elem2]
    intro h_eq
    have : (σ₁, C₁) = (σ₂, C₂) := by
      rw [Prod.ext_iff] at h_eq
      exact h_eq.2
    have : σ₁ = σ₂ := by
      rw [Prod.ext_iff] at this
      exact this.1
    exact h_ne this

  -- The fiber contains exactly these two elements
  have fiber_eq : filter (fun a => f a = y) s = {elem1, elem2} := by
    ext x
    constructor
    · intro hx
      rw [mem_filter] at hx
      obtain ⟨hx_s, hx_eq⟩ := hx
      rw [mem_filter] at hx_s
      obtain ⟨hx_db, _⟩ := hx_s
      rw [mem_filter] at hx_db
      obtain ⟨_, hx_typed_x, hx_door_x⟩ := hx_db

      -- Since f x = y, we have x.1 = y, so x = (y, x.2)
      have h_x_form : x = (y, x.2) := Prod.ext_iff.mpr ⟨hx_eq, rfl⟩

      -- x.2 must be one of the two rooms by uniqueness
      have h_room_x2 : IST.isRoom x.2.1 x.2.2 := isRoom_of_Door hx_door_x
      -- Since x.1 = y and hx_door_x : isDoorof x.1.1 x.1.2 x.2.1 x.2.2
      -- We have isDoorof y.1 y.2 x.2.1 x.2.2
      have hx_door_y : isDoorof y.1 y.2 x.2.1 x.2.2 :=
        hx_eq ▸ hx_door_x
      obtain h_case1 | h_case2 := h_unique x.2.1 x.2.2 h_room_x2 hx_door_y
      · simp only [mem_insert, mem_singleton]
        left
        rw [h_x_form] -- Goal: (y, x.2) = elem1, which is (y, (σ₁, C₁))
        apply Prod.ext
        · rfl
        · -- Goal: x.2 = (σ₁, C₁)
          apply Prod.ext
          · exact h_case1.1
          · exact h_case1.2
      · simp only [mem_insert, mem_singleton]
        right
        rw [h_x_form] -- Goal: (y, x.2) = elem2, which is (y, (σ₂, C₂))
        apply Prod.ext
        · rfl
        · -- Goal: x.2 = (σ₂, C₂)
          apply Prod.ext
          · exact h_case2.1
          · exact h_case2.2
    · intro hx
      simp only [mem_insert, mem_singleton] at hx
      cases hx with
      | inl h =>
        rw [h, mem_filter]
        exact ⟨elem1_in_s, by simp [f, elem1]⟩
      | inr h =>
        rw [h, mem_filter]
        exact ⟨elem2_in_s, by simp [f, elem2]⟩

  apply Eq.trans (congrArg Finset.card fiber_eq)
  exact Finset.card_pair elems_distinct

lemma dbcount_internal_door_even (i : I) : Even (filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)).card := by
  -- Key insight: By internal_door_two_rooms, every internal door connects to exactly 2 rooms
  let s := filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)
  let t := filter (fun (x : Finset T × Finset I) => IST.isInternalDoor x.1 x.2 ∧ isTypedNC c i x.1 x.2) univ
  let f := fun (x : (Finset T × Finset I) × Finset T × Finset I) => x.1

  have fs_in_t : ∀ x ∈ s, f x ∈ t := by
    intro x hx
    rw [mem_filter] at hx
    obtain ⟨hx_db, hx_not_outside⟩ := hx
    rw [mem_filter] at hx_db
    obtain ⟨_, hx_typed, hx_door⟩ := hx_db
    rw [mem_filter]
    simp only [mem_univ, true_and]
    constructor
    · -- Show isInternalDoor x.1.1 x.1.2
      unfold isInternalDoor
      constructor
      · -- Show isDoor x.1.1 x.1.2
        cases hx_door with
        | idoor h0 h1 y h_notin h_eq h_D_eq_C => exact h1
        | odoor h0 h1 j h_notin h_eq h_D_eq => exact h1
      · -- Show x.1.1.Nonempty
        by_contra h_empty
        have h_outside : isOutsideDoor x.1.1 x.1.2 := by
          constructor
          · cases hx_door with
            | idoor h0 h1 y h_notin h_eq h_D_eq_C => exact h1
            | odoor h0 h1 j h_notin h_eq h_D_eq => exact h1
          · exact Finset.not_nonempty_iff_eq_empty.mp h_empty
        exact hx_not_outside h_outside
    · exact hx_typed

  -- Each fiber has exactly 2 elements by internal_door_two_rooms
  have fiber_size_two : ∀ y ∈ t, (filter (fun a => f a = y) s).card = 2 := by
    intro y hy
    rw [mem_filter] at hy
    obtain ⟨_, hy_internal, hy_typed⟩ := hy
    -- Apply internal_door_two_rooms to get exactly 2 rooms
    exact fiber_size_internal_door c i y hy_internal hy_typed

  have counteq := Finset.card_eq_sum_card_fiberwise fs_in_t
  have sumeq := Finset.sum_const_nat fiber_size_two
  rw [sumeq] at counteq
  rw [counteq]
  simp only [even_two, Even.mul_left]

/- Easy -/
omit [Fintype T] [Fintype I] in
variable {c} in
lemma NC_of_NCdoor (h1 : isTypedNC c i τ D)
(h2 : isDoorof τ D σ C) :
  ¬ isColorful c σ C → isTypedNC c i σ C := by
  -- use  lemma NC_or_C_of_door
intro h_not_colorful
obtain h_typed | h_colorful := NC_or_C_of_door h1 h2
· exact h_typed
· contradiction

variable {c} in
lemma firber2_doors_NCroom (h0 : isRoom σ C) (h1 : isTypedNC c i σ C) :
  (filter (fun (x : (Finset T× Finset I)× Finset T × Finset I) => x.2 = (σ,C)) (dbcountingset c i)).card = 2 := by
    -- By doors_of_NCroom, there are exactly 2 doors in doors_NCroom c σ C i
    obtain ⟨door1, door2, h_ne, h_doors_eq⟩ := doors_of_NCroom h0 h1

    -- The filter selects exactly those elements ((τ,D), (σ,C)) where (τ,D) ∈ doors_NCroom c σ C i
    have h_filter_eq : filter (fun (x : (Finset T× Finset I)× Finset T × Finset I) => x.2 = (σ,C)) (dbcountingset c i) =
                       {(door1, (σ,C)), (door2, (σ,C))} := by
      ext x
      constructor
      · intro hx
        rw [mem_filter] at hx
        obtain ⟨h_db, h_eq⟩ := hx
        rw [mem_filter] at h_db
        obtain ⟨_, h_typed, h_door⟩ := h_db
        -- Since x.2 = (σ,C), we have x = (x.1, (σ,C))
        have h_x_form : x = (x.1, (σ,C)) := by
          rw [Prod.ext_iff]
          exact ⟨rfl, h_eq⟩
        rw [h_x_form]
        simp
        -- x.1 must be one of the two doors
        have h_x1_in_doors : x.1 ∈ doors_NCroom c σ C i := by
          simp [doors_NCroom]
          have h_sigma : x.2.1 = σ := by rw [h_eq]
          have h_C : x.2.2 = C := by rw [h_eq]
          rw [h_sigma, h_C] at h_door
          exact ⟨h_typed, h_door⟩
        rw [h_doors_eq] at h_x1_in_doors
        simp at h_x1_in_doors
        exact h_x1_in_doors
      · intro hx
        simp at hx
        cases hx with
        | inl h =>
          rw [h, mem_filter]
          constructor
          · rw [mem_filter]
            -- door1 is in doors_NCroom by definition of h_doors_eq
            have h_door1_in_doors : door1 ∈ doors_NCroom c σ C i := by
              rw [h_doors_eq]
              exact Set.mem_insert door1 {door2}
            simp [doors_NCroom] at h_door1_in_doors
            exact ⟨by simp, h_door1_in_doors.1, h_door1_in_doors.2⟩
          · rfl
        | inr h =>
          rw [h, mem_filter]
          constructor
          · rw [mem_filter]
            -- door2 is in doors_NCroom by definition of h_doors_eq
            have h_door2_in_doors : door2 ∈ doors_NCroom c σ C i := by
              rw [h_doors_eq]
              exact Set.mem_insert_of_mem door1 (Set.mem_singleton door2)
            simp [doors_NCroom] at h_door2_in_doors
            exact ⟨by simp, h_door2_in_doors.1, h_door2_in_doors.2⟩
          · rfl

    rw [h_filter_eq]
    simp [h_ne]

lemma dbcount_NCroom (i : I) : Even (filter (fun x => ¬isColorful c x.2.1 x.2.2) (dbcountingset c i)).card := by
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
