import Mathlib
--import LLMlean

section fiberlemma

open Finset


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

variable {T : Type*} [Inhabited T]
variable {I : Type*}

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

-- Definition of the sets M_i used in the proof
def M_set (τ : Finset T) (D : Finset I) (i : I) (h_nonempty : τ.Nonempty) : Set T :=
  {y : T | ∀ k ∈ D, k ≠ i → mini h_nonempty k <[k] y}

-- Predicate for being the maximal element of M_i with respect to <_i
def is_maximal_in_M_set (τ : Finset T) (D : Finset I) (i : I) (h_nonempty : τ.Nonempty) (x : T) : Prop :=
  x ∈ M_set τ D i h_nonempty ∧ ∀ y ∈ M_set τ D i h_nonempty, y ≤[i] x

-- The maximal element m_i when M_i is nonempty
noncomputable def m_element [Fintype T] (τ : Finset T) (D : Finset I) (i : I) (h_nonempty : τ.Nonempty)
    (h : (M_set τ D i h_nonempty).Nonempty) : T :=
  @Finset.max' _ (IST i) (M_set τ D i h_nonempty).toFinset (Set.toFinset_nonempty.mpr h)

-- Theorem: m_element is indeed the maximal element
omit[Inhabited T][DecidableEq T][DecidableEq I] in
theorem m_element_is_maximal [Fintype T] (τ : Finset T) (D : Finset I) (i : I) (h_nonempty : τ.Nonempty)
    (h : (M_set τ D i h_nonempty).Nonempty) :
    is_maximal_in_M_set τ D i h_nonempty (m_element τ D i h_nonempty h) := by
  unfold is_maximal_in_M_set m_element
  let s_finset := (M_set τ D i h_nonempty).toFinset
  have h_nonempty_finset: s_finset.Nonempty := Set.toFinset_nonempty.mpr h
  constructor
  · rw [←Set.mem_toFinset]
    exact @Finset.max'_mem _ (IST i) s_finset h_nonempty_finset
  · intros y hy
    rw [←Set.mem_toFinset] at hy
    apply @Finset.le_max' _ (IST i)
    exact hy

-- Sublemma 3.1: τ is dominant with respect to D - i iff i ∈ {a,b} and M_i = ∅
omit [Inhabited T] in
lemma sublemma_3_1 [Fintype T] (τ : Finset T) (D : Finset I)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty) :
    ∀ i ∈ D, (IST.isDominant τ (D.erase i) ↔
      (∃ a b, a ∈ D ∧ b ∈ D ∧ a ≠ b ∧
       mini h_nonempty a = mini h_nonempty b ∧
       (i = a ∨ i = b) ∧
       M_set τ D i h_nonempty = ∅)) := by
  intro i hi
  constructor
  · intro h_dom
    have h_card : D.card = τ.card + 1 := h_door.2
    have h_image_card : D.card = (D.image (mini h_nonempty)).card + 1 := by
      have h_dominant : IST.isDominant τ D := h_door.1
      have h_image_sub : D.image (mini h_nonempty) ⊆ τ := by
        intro x hx
        simp at hx
        obtain ⟨j, _, hj_eq⟩ := hx
        rw [←hj_eq, mini]
        exact @Finset.min'_mem _ (IST j) τ h_nonempty
      have h_image_eq : D.image (mini h_nonempty) = τ := by
        convert (keylemma_of_domiant h_dominant h_nonempty).symm
      rw [h_card, h_image_eq]
    obtain ⟨a, b, ha_mem, hb_mem, h_eq_mini, h_ne, _⟩ := injOn_sdiff D (mini h_nonempty) h_image_card
    use a, b, ha_mem, hb_mem, h_ne, h_eq_mini
    by_cases h_case : i = a ∨ i = b
    · constructor
      · exact h_case
      · ext y
        simp [M_set]
        obtain ⟨k, hk_in_erase, hk_dom⟩ := h_dom y
        have hk_in_D : k ∈ D := (Finset.mem_erase.mp hk_in_erase).2
        have hk_ne_i : k ≠ i := (Finset.mem_erase.mp hk_in_erase).1
        use k, hk_in_D, hk_ne_i
    · push_neg at h_case
      obtain ⟨h_i_ne_a, h_i_ne_b⟩ := h_case

      have h_a_in_erase : a ∈ D.erase i := Finset.mem_erase.mpr ⟨h_i_ne_a.symm, ha_mem⟩
      have h_b_in_erase : b ∈ D.erase i := Finset.mem_erase.mpr ⟨h_i_ne_b.symm, hb_mem⟩

      have h_not_inj : ¬Set.InjOn (mini h_nonempty) (D.erase i : Set I) := by
        intro h_inj
        exact h_ne (h_inj h_a_in_erase h_b_in_erase h_eq_mini)

      have h_image_lt : ((D.erase i).image (mini h_nonempty)).card < (D.erase i).card := by
        by_contra h_not_lt
        push_neg at h_not_lt
        have h_eq : ((D.erase i).image (mini h_nonempty)).card = (D.erase i).card :=
          le_antisymm Finset.card_image_le h_not_lt
        have h_inj : Set.InjOn (mini h_nonempty) (D.erase i : Set I) :=
          Finset.injOn_of_card_image_eq h_eq
        exact h_not_inj h_inj
      exfalso
      have h_dom_image := keylemma_of_domiant h_dom h_nonempty
      have h_tau_eq_image : τ.card = ((D.erase i).image (mini h_nonempty)).card := by
        congr; ext; simp [h_dom_image]
      have h_tau_eq_erase : τ.card = (D.erase i).card := by
        rw [Finset.card_erase_of_mem hi, h_door.2]; simp
      rw [h_tau_eq_erase] at h_tau_eq_image
      rw [h_tau_eq_image] at h_image_lt
      exact not_lt.mpr (le_refl _) h_image_lt
  · rintro ⟨a, b, ha_mem, hb_mem, h_ne, h_eq_mini, h_i_case, h_Mi_empty⟩
    intro y
    unfold M_set at h_Mi_empty
    simp only [Set.mem_setOf_eq, Set.eq_empty_iff_forall_not_mem] at h_Mi_empty
    specialize h_Mi_empty y
    push_neg at h_Mi_empty
    obtain ⟨k, hk_mem, hk_ne_i, hk_not_lt⟩ := h_Mi_empty
    use k
    constructor
    · exact Finset.mem_erase.mpr ⟨hk_ne_i, hk_mem⟩
    · intro x hx
      letI : LinearOrder T := IST k
      have h_y_le_mini : y ≤[k] mini h_nonempty k := le_of_not_lt hk_not_lt
      have h_mini_le_x : mini h_nonempty k ≤[k] x := Finset.min'_le τ x hx
      exact @le_trans _ (IST k).toPreorder _ _ _ h_y_le_mini h_mini_le_x

/-Sublemma 3.2-/
omit [Inhabited T] in
lemma sublemma_3_2 [Fintype T] (τ : Finset T) (D : Finset I) (x : T)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty) (h_not_mem : x ∉ τ)
    (a b : I) (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (h_eq : mini h_nonempty a = mini h_nonempty b) :
    IST.isDominant (insert x τ) D ↔
    (∃ i ∈ ({a, b} : Finset I), (M_set τ D i h_nonempty).Nonempty ∧
     is_maximal_in_M_set τ D i h_nonempty x) := by
  constructor
  · intro h_dominant
    have h_insert_nonempty : (insert x τ).Nonempty := Finset.insert_nonempty x τ
    have h_min_eq_image : D.image (mini h_insert_nonempty) = insert x τ := by
      convert (keylemma_of_domiant h_dominant h_insert_nonempty).symm
    have h_x_is_min : ∃ i ∈ D, mini h_insert_nonempty i = x := by
      have h_x_in_image : x ∈ D.image (mini h_insert_nonempty) := by
        rw [h_min_eq_image]
        exact Finset.mem_insert_self x τ
      exact Finset.mem_image.mp h_x_in_image
    obtain ⟨i, hi_mem, hi_eq⟩ := h_x_is_min
    have h_is_room : isRoom (insert x τ) D := by
      unfold isRoom
      constructor
      · exact h_dominant
      · rw [Finset.card_insert_of_not_mem h_not_mem, h_door.2]
    have h_inj_insert : Set.InjOn (mini h_insert_nonempty) (D : Set I) := by
      apply Finset.injOn_of_card_image_eq
      rw [h_min_eq_image, h_is_room.2]
    have h_mini_lt_x : ∀ k ∈ D, k ≠ i → mini h_nonempty k <[k] x := by
      intros k hk_mem hk_ne_i
      have h_mini_cases : mini h_insert_nonempty k = mini h_nonempty k ∨ mini h_insert_nonempty k = x := by
        letI := IST k
        unfold mini
        by_cases h : τ.min' h_nonempty ≤[k] x
        · left
          apply le_antisymm
          · apply Finset.min'_le
            exact Finset.mem_insert_of_mem (Finset.min'_mem _ h_nonempty)
          · apply Finset.le_min'
            intro y hy
            cases Finset.mem_insert.mp hy with
            | inl h_eq => rw [h_eq]; exact h
            | inr h_mem => exact Finset.min'_le _ _ h_mem
        · right
          apply le_antisymm
          · apply Finset.min'_le
            exact Finset.mem_insert_self _ _
          · apply Finset.le_min'
            intro y hy
            cases Finset.mem_insert.mp hy with
            | inl h_eq => rw [h_eq]
            | inr h_mem => exact le_of_not_le (fun h_le => h (le_trans (Finset.min'_le _ _ h_mem) h_le))
      have h_mini_neq_x : mini h_insert_nonempty k ≠ x := by
        intro h_eq
        -- If mini h_insert_nonempty k = x for k ≠ i, we'd have two indices mapping to x
        have h_inj : Set.InjOn (mini h_insert_nonempty) (D : Set I) := h_inj_insert
        have hi_mem_D : i ∈ D := hi_mem
        have hk_mem_D : k ∈ D := hk_mem
        have h_mini_i_eq_x : mini h_insert_nonempty i = x := hi_eq
        exact hk_ne_i (h_inj hi_mem_D hk_mem_D (h_mini_i_eq_x.trans h_eq.symm)).symm
      letI := IST k
      have h_mini_eq_k : mini h_insert_nonempty k = mini h_nonempty k := by
        cases h_mini_cases with
        | inl h => exact h
        | inr h => exact absurd h h_mini_neq_x
      apply lt_of_le_of_ne
      · have h_le : mini h_insert_nonempty k ≤[k] x := by
          apply @Finset.min'_le _ (IST k)
          exact Finset.mem_insert_self x τ
        rw [h_mini_eq_k] at h_le
        exact h_le
      · exact fun h_eq_x => h_not_mem (h_eq_x ▸ Finset.min'_mem τ h_nonempty)
    have h_x_le_mini_i : x ≤[i] mini h_nonempty i := by
      letI := IST i
      rw [← hi_eq]
      unfold mini
      apply Finset.min'_le
      · exact Finset.mem_insert_of_mem (Finset.min'_mem _ h_nonempty)
    have h_i_in_ab : i ∈ ({a, b} : Finset I) := by
      by_cases hik : i = a ∨ i = b
      · simp [hik]
      · push_neg at hik
        obtain ⟨hia, hib⟩ := hik
        have h_mini_eq_for_ne_i : ∀ k ∈ D, k ≠ i → mini h_insert_nonempty k = mini h_nonempty k := by
          intros k hk_mem hk_ne_i
          have h_cases : mini h_insert_nonempty k = mini h_nonempty k ∨ mini h_insert_nonempty k = x := by
            letI := IST k
            by_cases h : τ.min' h_nonempty ≤[k] x
            · left
              apply le_antisymm
              · apply Finset.min'_le
                exact Finset.mem_insert_of_mem (Finset.min'_mem _ h_nonempty)
              · apply Finset.le_min'
                intro y hy
                cases Finset.mem_insert.mp hy with
                | inl h_eq_x => rw [h_eq_x]; exact h
                | inr h_mem => exact Finset.min'_le _ _ h_mem
            · right
              apply le_antisymm
              · apply Finset.min'_le
                exact Finset.mem_insert_self _ _
              · apply Finset.le_min'
                intro y hy
                cases Finset.mem_insert.mp hy with
                | inl h_eq_x => rw [h_eq_x]
                | inr h_mem => exact le_of_not_le (fun h_le => h (le_trans (Finset.min'_le _ _ h_mem) h_le))
          have h_mini_neq_x : mini h_insert_nonempty k ≠ x := by
            intro h_eq_k_x
            exact hk_ne_i (h_inj_insert hk_mem hi_mem (h_eq_k_x.trans hi_eq.symm))
          cases h_cases with
          | inl h => exact h
          | inr h => exact absurd h h_mini_neq_x
        have h_mini_a_eq : mini h_insert_nonempty a = mini h_nonempty a := h_mini_eq_for_ne_i a ha (Ne.symm hia)
        have h_mini_b_eq : mini h_insert_nonempty b = mini h_nonempty b := h_mini_eq_for_ne_i b hb (Ne.symm hib)
        have h_contr : mini h_insert_nonempty a = mini h_insert_nonempty b := by
          rw [h_mini_a_eq, h_mini_b_eq, h_eq]
        exact (hab (h_inj_insert ha hb h_contr)).elim
    use i, h_i_in_ab
    constructor
    · have h_nonempty_M : (M_set τ D i h_nonempty).Nonempty := by
        use x
        unfold M_set
        apply Set.mem_setOf.mpr
        intro k hk_mem hk_ne_i
        exact h_mini_lt_x k hk_mem hk_ne_i
      exact h_nonempty_M
    · unfold is_maximal_in_M_set
      constructor
      · unfold M_set
        apply Set.mem_setOf.mpr
        intro k hk_mem hk_ne_i
        exact h_mini_lt_x k hk_mem hk_ne_i
      · intros y hy
        letI := IST i
        unfold M_set at hy
        simp at hy
        obtain ⟨k, hk_in_D, h_y_le_all⟩ := h_dominant y
        by_cases hik : k = i
        · subst hik
          exact h_y_le_all x (Finset.mem_insert_self x τ)
        · have h_lt_y : mini h_nonempty k <[k] y := hy k hk_in_D hik
          have h_mini_mem : mini h_nonempty k ∈ τ := by
            unfold mini
            exact @Finset.min'_mem _ (IST k) _ h_nonempty
          have h_mini_mem_insert : mini h_nonempty k ∈ insert x τ := Finset.mem_insert_of_mem h_mini_mem
          have h_le_m : y ≤[k] mini h_nonempty k := h_y_le_all (mini h_nonempty k) h_mini_mem_insert
          letI := IST k
          exact absurd (lt_of_lt_of_le h_lt_y h_le_m) (lt_irrefl _)

  · rintro ⟨i, hi_mem_ab, h_M_nonempty, h_x_is_max⟩
    have h_x_in_M : x ∈ M_set τ D i h_nonempty := h_x_is_max.1
    unfold isDominant
    intro y
    have h_dom_tau := h_door.1
    obtain ⟨k, hk_in_D, hk_dom⟩ := h_dom_tau y
    by_cases h_k_eq_i : k = i
    · subst h_k_eq_i
      have hk_in_D : k ∈ D := by
        cases Finset.mem_insert.mp hi_mem_ab with
        | inl hk_eq_a => rwa [hk_eq_a]
        | inr hk_eq_b => have : k = b := Finset.mem_singleton.mp hk_eq_b; rw [this]; exact hb
      letI := IST k
      by_cases h_y_le_x : y ≤[k] x
      · use k, hk_in_D
        intro z hz
        cases Finset.mem_insert.mp hz with
        | inl h_z_eq_x => rw [h_z_eq_x]; exact h_y_le_x
        | inr h_z_in_tau => exact hk_dom z h_z_in_tau
      · have h_x_lt_y : x <[k] y := lt_of_not_le h_y_le_x
        have h_y_not_in_M : y ∉ M_set τ D k h_nonempty := by
          intro h_y_in_M
          have h_y_le_x : y ≤[k] x := h_x_is_max.2 y h_y_in_M
          exact not_le.mpr h_x_lt_y h_y_le_x
        simp [M_set] at h_y_not_in_M
        push_neg at h_y_not_in_M
        obtain ⟨j, hj_in_D, hj_ne_k, hj_not_lt⟩ := h_y_not_in_M
        use j, hj_in_D
        intro z hz
        cases Finset.mem_insert.mp hz with
        | inl h_z_eq_x =>
          rw [h_z_eq_x]
          letI := IST j
          have h_mini_lt_x : mini h_nonempty j <[j] x := h_x_in_M j hj_in_D hj_ne_k
          have h_y_le_mini : y ≤[j] mini h_nonempty j := le_of_not_lt hj_not_lt
          exact le_of_lt (lt_of_le_of_lt h_y_le_mini h_mini_lt_x)
        | inr h_z_in_tau =>
          letI := IST j
          have h_y_le_mini : y ≤[j] mini h_nonempty j := le_of_not_lt hj_not_lt
          have h_mini_le_z : mini h_nonempty j ≤[j] z := Finset.min'_le τ z h_z_in_tau
          exact le_trans h_y_le_mini h_mini_le_z
    · use k, hk_in_D
      intro z hz
      cases Finset.mem_insert.mp hz with
      | inl h_z_eq_x =>
        rw [h_z_eq_x]
        letI := IST k
        have h_y_le_mini : y ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) (Finset.min'_mem τ h_nonempty)
        have h_mini_lt_x : mini h_nonempty k <[k] x := h_x_in_M k hk_in_D h_k_eq_i
        exact le_of_lt (lt_of_le_of_lt h_y_le_mini h_mini_lt_x)
      | inr h_z_in_tau =>
        exact hk_dom z h_z_in_tau


-- Key lemma: M_a and M_b are disjoint
omit [Inhabited T][DecidableEq T] in
lemma M_sets_disjoint [Fintype T] (τ : Finset T) (D : Finset I) (a b : I)
    (h_nonempty : τ.Nonempty) (h_door : IST.isDoor τ D)
    (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (h_eq : mini h_nonempty a = mini h_nonempty b) :
    M_set τ D a h_nonempty ∩ M_set τ D b h_nonempty = ∅ := by
  ext y
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false]
  constructor
  · intro ⟨h_in_a, h_in_b⟩
    unfold M_set at h_in_a h_in_b
    have h_b_ne_a : b ≠ a := hab.symm
    have h_mini_b_lt_y : mini h_nonempty b <[b] y := h_in_a b hb h_b_ne_a
    have h_mini_a_lt_y : mini h_nonempty a <[a] y := h_in_b a ha hab
    rw [h_eq] at h_mini_a_lt_y
    obtain ⟨k, hk_in_D, hk_dom⟩ := h_door.1 y
    have h_mini_b_mem : mini h_nonempty b ∈ τ := by
      unfold mini
      exact @Finset.min'_mem _ (IST b) _ h_nonempty
    have h_y_le_mini_b : y ≤[k] mini h_nonempty b := hk_dom (mini h_nonempty b) h_mini_b_mem
    by_cases hk_eq_a : k = a
    · subst hk_eq_a
      letI := IST k
      exact not_le.mpr h_mini_a_lt_y h_y_le_mini_b
    · by_cases hk_eq_b : k = b
      · subst hk_eq_b
        letI := IST k
        exact not_le.mpr h_mini_b_lt_y h_y_le_mini_b
      · have h_mini_k_lt_y : mini h_nonempty k <[k] y := h_in_a k hk_in_D hk_eq_a
        have h_mini_k_mem : mini h_nonempty k ∈ τ := by
          unfold mini
          exact @Finset.min'_mem _ (IST k) _ h_nonempty
        have h_y_le_mini_k : y ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) h_mini_k_mem
        letI := IST k
        exact not_le.mpr h_mini_k_lt_y h_y_le_mini_k
  · intro h
    exact False.elim h

/- Lemma 3-/
omit [Inhabited T] in
theorem internal_door_two_rooms [Fintype T] (τ : Finset T) (D : Finset I)
    (h_int_door : IST.isInternalDoor τ D) :
    ∃ (σ₁ σ₂ : Finset T) (C₁ C₂ : Finset I),
      (σ₁, C₁) ≠ (σ₂, C₂) ∧
      IST.isRoom σ₁ C₁ ∧
      IST.isRoom σ₂ C₂ ∧
      isDoorof τ D σ₁ C₁ ∧
      isDoorof τ D σ₂ C₂ ∧
      (∀ σ C, IST.isRoom σ C → isDoorof τ D σ C →
       (σ = σ₁ ∧ C = C₁) ∨ (σ = σ₂ ∧ C = C₂)) := by
  -- Step 1: Extract the door property and get the unique pair {a,b}
  obtain ⟨h_door, h_nonempty⟩ := h_int_door
  have h_card : D.card = τ.card + 1 := h_door.2
  have h_image_card : D.card = (D.image (mini h_nonempty)).card + 1 := by
    have h_dominant : IST.isDominant τ D := h_door.1
    have h_image_eq : D.image (mini h_nonempty) = τ := by
      convert (keylemma_of_domiant h_dominant h_nonempty).symm
    rw [h_card, h_image_eq]
  obtain ⟨a, b, ha_mem, hb_mem, h_eq_mini, hab, _⟩ := injOn_sdiff D (mini h_nonempty) h_image_card
  have h_disjoint : M_set τ D a h_nonempty ∩ M_set τ D b h_nonempty = ∅ :=
    M_sets_disjoint τ D a b h_nonempty h_door ha_mem hb_mem hab h_eq_mini
  by_cases h_Ma_nonempty : (M_set τ D a h_nonempty).Nonempty
  · by_cases h_Mb_nonempty : (M_set τ D b h_nonempty).Nonempty
    · let m_a := m_element τ D a h_nonempty h_Ma_nonempty
      let m_b := m_element τ D b h_nonempty h_Mb_nonempty
      have h_ma_max : is_maximal_in_M_set τ D a h_nonempty m_a :=
        m_element_is_maximal τ D a h_nonempty h_Ma_nonempty
      have h_mb_max : is_maximal_in_M_set τ D b h_nonempty m_b :=
        m_element_is_maximal τ D b h_nonempty h_Mb_nonempty
      have h_ma_ne_mb : m_a ≠ m_b := by
        intro h_eq
        have h_ma_in_Ma : m_a ∈ M_set τ D a h_nonempty := h_ma_max.1
        have h_mb_in_Mb : m_b ∈ M_set τ D b h_nonempty := h_mb_max.1
        rw [h_eq] at h_ma_in_Ma
        have h_in_inter : m_b ∈ M_set τ D a h_nonempty ∩ M_set τ D b h_nonempty :=
          ⟨h_ma_in_Ma, h_mb_in_Mb⟩
        rw [h_disjoint] at h_in_inter
        exact Set.not_mem_empty m_b h_in_inter
      have h_ma_not_mem : m_a ∉ τ := by
        intro h_ma_in_tau
        obtain ⟨k, hk_mem, hk_dom⟩ := h_door.1 m_a
        by_cases hk_eq_a : k = a
        · subst hk_eq_a
          have h_ma_le_mini_k : m_a ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) (by
            unfold mini
            exact @Finset.min'_mem _ (IST k) _ h_nonempty)
          have h_ma_le_all : ∀ x ∈ τ, m_a ≤[k] x := hk_dom
          have h_ma_eq_mini : m_a = mini h_nonempty k := by
            letI := IST k
            have h_mini_le_ma : mini h_nonempty k ≤[k] m_a := Finset.min'_le τ m_a h_ma_in_tau
            exact le_antisymm h_ma_le_mini_k h_mini_le_ma
          have h_ma_in_M : m_a ∈ M_set τ D k h_nonempty := by
            convert h_ma_max.1
          unfold M_set at h_ma_in_M
          have h_mini_b_lt_ma : mini h_nonempty b <[b] m_a := h_ma_in_M b hb_mem hab.symm
          rw [h_ma_eq_mini, h_eq_mini] at h_mini_b_lt_ma
          letI := IST b
          exact lt_irrefl (mini h_nonempty b) h_mini_b_lt_ma
        · have h_ma_in_M : m_a ∈ M_set τ D a h_nonempty := h_ma_max.1
          unfold M_set at h_ma_in_M
          have h_mini_k_lt_ma : mini h_nonempty k <[k] m_a := h_ma_in_M k hk_mem hk_eq_a
          have h_ma_le_mini_k : m_a ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) (by
            unfold mini
            exact @Finset.min'_mem _ (IST k) _ h_nonempty)
          letI := IST k
          exact not_le.mpr h_mini_k_lt_ma h_ma_le_mini_k
      have h_mb_not_mem : m_b ∉ τ := by
        intro h_mb_in_tau
        obtain ⟨k, hk_mem, hk_dom⟩ := h_door.1 m_b
        by_cases hk_eq_b : k = b
        · subst hk_eq_b
          have h_mb_le_mini_k : m_b ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) (by
            unfold mini
            exact @Finset.min'_mem _ (IST k) _ h_nonempty)
          have h_mb_le_all : ∀ x ∈ τ, m_b ≤[k] x := hk_dom
          have h_mb_eq_mini : m_b = mini h_nonempty k := by
            letI := IST k
            have h_mini_le_mb : mini h_nonempty k ≤[k] m_b := Finset.min'_le τ m_b h_mb_in_tau
            exact le_antisymm h_mb_le_mini_k h_mini_le_mb
          have h_mb_in_M : m_b ∈ M_set τ D k h_nonempty := by
            convert h_mb_max.1
          unfold M_set at h_mb_in_M
          have h_mini_a_lt_mb : mini h_nonempty a <[a] m_b := h_mb_in_M a ha_mem hab
          rw [h_mb_eq_mini, ← h_eq_mini] at h_mini_a_lt_mb
          letI := IST a
          exact lt_irrefl (mini h_nonempty a) h_mini_a_lt_mb
        · -- Case k ≠ b: we have mini h_nonempty k <[k] m_b from M_set definition
          have h_mb_in_M : m_b ∈ M_set τ D b h_nonempty := h_mb_max.1
          unfold M_set at h_mb_in_M
          have h_mini_k_lt_mb : mini h_nonempty k <[k] m_b := h_mb_in_M k hk_mem hk_eq_b
          -- But from dominance, m_b ≤[k] mini h_nonempty k
          have h_mb_le_mini_k : m_b ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) (by
            unfold mini
            exact @Finset.min'_mem _ (IST k) _ h_nonempty)
          letI := IST k
          exact not_le.mpr h_mini_k_lt_mb h_mb_le_mini_k
      use insert m_a τ, insert m_b τ, D, D
      constructor
      · intro h_pair_eq
        have h_eq : insert m_a τ = insert m_b τ := congr_arg Prod.fst h_pair_eq
        have : m_a = m_b := by
          have h_ma_in : m_a ∈ insert m_a τ := Finset.mem_insert_self m_a τ
          rw [h_eq] at h_ma_in
          cases Finset.mem_insert.mp h_ma_in with
          | inl h => exact h
          | inr h => exact absurd h h_ma_not_mem
        exact h_ma_ne_mb this
      constructor
      · constructor
        · apply (sublemma_3_2 τ D m_a h_door h_nonempty h_ma_not_mem a b ha_mem hb_mem hab h_eq_mini).mpr
          use a, by simp
        · rw [Finset.card_insert_of_not_mem h_ma_not_mem, h_card]
      constructor
      · constructor
        · apply (sublemma_3_2 τ D m_b h_door h_nonempty h_mb_not_mem a b ha_mem hb_mem hab h_eq_mini).mpr
          use b, by simp
        · rw [Finset.card_insert_of_not_mem h_mb_not_mem, h_card]
      constructor
      · apply isDoorof.idoor
        · apply (sublemma_3_2 τ D m_a h_door h_nonempty h_ma_not_mem a b ha_mem hb_mem hab h_eq_mini).mpr
          use a, by simp
        · exact h_door
        · exact h_ma_not_mem
        · rfl
        · rfl
      constructor
      · apply isDoorof.idoor
        · apply (sublemma_3_2 τ D m_b h_door h_nonempty h_mb_not_mem a b ha_mem hb_mem hab h_eq_mini).mpr
          use b, by simp
        · exact h_door
        · exact h_mb_not_mem
        · rfl
        · rfl
      · intros σ C h_room h_door_rel
        cases h_door_rel with
        | idoor h0 _ x hx_not_mem hx_eq hc_eq =>
          subst hx_eq hc_eq
          have h_dom : IST.isDominant (insert x τ) D := h0
          have h_x_not_mem : x ∉ τ := hx_not_mem
          have h_exists_max : ∃ i ∈ ({a, b} : Finset I), (M_set τ D i h_nonempty).Nonempty ∧ is_maximal_in_M_set τ D i h_nonempty x := by
            apply (sublemma_3_2 τ D x h_door h_nonempty h_x_not_mem a b ha_mem hb_mem hab h_eq_mini).mp
            exact h_dom
          obtain ⟨i, hi_mem, hi_nonempty, hi_max⟩ := h_exists_max
          cases Finset.mem_insert.mp hi_mem with
          | inl hi_eq_a =>
            subst hi_eq_a
            have h_x_eq_ma : x = m_a := by
              letI := IST i
              have h_x_in_Ma : x ∈ M_set τ D i h_nonempty := hi_max.1
              have h_ma_in_Ma : m_a ∈ M_set τ D i h_nonempty := h_ma_max.1
              have h_x_le_ma : x ≤[i] m_a := h_ma_max.2 x h_x_in_Ma
              have h_ma_le_x : m_a ≤[i] x := hi_max.2 m_a h_ma_in_Ma
              exact le_antisymm h_x_le_ma h_ma_le_x
            left
            exact ⟨h_x_eq_ma ▸ rfl, rfl⟩
          | inr hi_eq_b =>
            have hi_eq_b : i = b := Finset.mem_singleton.mp hi_eq_b
            subst hi_eq_b
            have h_x_eq_mb : x = m_b := by
              letI := IST i
              have h_x_in_Mb : x ∈ M_set τ D i h_nonempty := hi_max.1
              have h_mb_in_Mb : m_b ∈ M_set τ D i h_nonempty := h_mb_max.1
              have h_x_le_mb : x ≤[i] m_b := h_mb_max.2 x h_x_in_Mb
              have h_mb_le_x : m_b ≤[i] x := hi_max.2 m_b h_mb_in_Mb
              exact le_antisymm h_x_le_mb h_mb_le_x
            right
            exact ⟨h_x_eq_mb ▸ rfl, rfl⟩
        | odoor h0 _ j hj_not_mem hj_eq hc_eq =>
          subst hj_eq
          have h_card_eq : C.card = τ.card := h_room.2
          have h_card_D : D.card = τ.card + 1 := h_door.2
          have h_card_insert : (insert j C).card = C.card + 1 := Finset.card_insert_of_not_mem hj_not_mem
          rw [hc_eq] at h_card_D
          rw [h_card_insert] at h_card_D
          rw [h_card_eq] at h_card_D
          have hj_in_ab : j = a ∨ j = b := by
            by_contra h_not_in
            push_neg at h_not_in
            obtain ⟨hj_ne_a, hj_ne_b⟩ := h_not_in
            have ha_in_C : a ∈ C := by
              have ha_in_D : a ∈ D := ha_mem
              rw [hc_eq] at ha_in_D
              cases Finset.mem_insert.mp ha_in_D with
              | inl h_eq => exact False.elim (hj_ne_a h_eq.symm)
              | inr h_mem => exact h_mem
            have hb_in_C : b ∈ C := by
              have hb_in_D : b ∈ D := hb_mem
              rw [hc_eq] at hb_in_D
              cases Finset.mem_insert.mp hb_in_D with
              | inl h_eq => exact False.elim (hj_ne_b h_eq.symm)
              | inr h_mem => exact h_mem
            have h_inj_C : Set.InjOn (mini h_nonempty) (C : Set I) := by
              apply Finset.injOn_of_card_image_eq
              have h_tau_eq_C_image : τ = C.image (mini h_nonempty) := by
                convert keylemma_of_domiant h0 h_nonempty
              rw [←h_tau_eq_C_image]
              exact h_card_eq.symm
            have h_a_ne_b : a ≠ b := hab
            have h_mini_eq : mini h_nonempty a = mini h_nonempty b := h_eq_mini
            exact h_a_ne_b (h_inj_C ha_in_C hb_in_C h_mini_eq)
          cases hj_in_ab with
          | inl hj_eq_a =>
            have h_dom_C : IST.isDominant τ C := h0
            rw [show C = D.erase j by rw [hc_eq]; exact (Finset.erase_insert hj_not_mem).symm] at h_dom_C
            have hj_eq_a_mem : j ∈ D := by rw [hj_eq_a]; exact ha_mem
            have h_contra := (sublemma_3_1 τ D h_door h_nonempty j hj_eq_a_mem).mp h_dom_C
            obtain ⟨a', b', ha'_mem, hb'_mem, ha'b'_ne, h_eq_mini', h_j_in_pair, h_M_empty⟩ := h_contra
            have h_Mj_nonempty : (M_set τ D j h_nonempty).Nonempty := by
              rw [hj_eq_a]; exact h_Ma_nonempty
            rw [h_M_empty] at h_Mj_nonempty
            exact False.elim (Set.not_nonempty_empty h_Mj_nonempty)
          | inr hj_eq_b =>
            have h_dom_C : IST.isDominant τ C := h0
            rw [show C = D.erase j by rw [hc_eq]; exact (Finset.erase_insert hj_not_mem).symm] at h_dom_C
            have hj_eq_b_mem : j ∈ D := by rw [hj_eq_b]; exact hb_mem
            have h_contra := (sublemma_3_1 τ D h_door h_nonempty j hj_eq_b_mem).mp h_dom_C
            obtain ⟨a', b', ha'_mem, hb'_mem, ha'b'_ne, h_eq_mini', h_j_in_pair, h_M_empty⟩ := h_contra
            have h_Mj_nonempty : (M_set τ D j h_nonempty).Nonempty := by
              rw [hj_eq_b]; exact h_Mb_nonempty
            rw [h_M_empty] at h_Mj_nonempty
            exact False.elim (Set.not_nonempty_empty h_Mj_nonempty)
    · let m_a := m_element τ D a h_nonempty h_Ma_nonempty
      have h_ma_max : is_maximal_in_M_set τ D a h_nonempty m_a :=
        m_element_is_maximal τ D a h_nonempty h_Ma_nonempty
      have h_ma_not_mem : m_a ∉ τ := by
        intro h_ma_in_tau
        obtain ⟨k, hk_mem, hk_dom⟩ := h_door.1 m_a
        by_cases hk_eq_a : k = a
        · subst hk_eq_a
          have h_ma_le_mini_k : m_a ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) (by
            unfold mini
            exact @Finset.min'_mem _ (IST k) _ h_nonempty)
          have h_ma_eq_mini : m_a = mini h_nonempty k := by
            letI := IST k
            have h_mini_le_ma : mini h_nonempty k ≤[k] m_a := Finset.min'_le τ m_a h_ma_in_tau
            exact le_antisymm h_ma_le_mini_k h_mini_le_ma
          have h_ma_in_M : m_a ∈ M_set τ D k h_nonempty := by
            convert h_ma_max.1
          unfold M_set at h_ma_in_M
          have h_mini_b_lt_ma : mini h_nonempty b <[b] m_a := h_ma_in_M b hb_mem hab.symm
          rw [h_ma_eq_mini, h_eq_mini] at h_mini_b_lt_ma
          letI := IST b
          exact lt_irrefl (mini h_nonempty b) h_mini_b_lt_ma
        · have h_ma_in_M : m_a ∈ M_set τ D a h_nonempty := h_ma_max.1
          unfold M_set at h_ma_in_M
          have h_mini_k_lt_ma : mini h_nonempty k <[k] m_a := h_ma_in_M k hk_mem hk_eq_a
          have h_ma_le_mini_k : m_a ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) (by
            unfold mini
            exact @Finset.min'_mem _ (IST k) _ h_nonempty)
          letI := IST k
          exact not_le.mpr h_mini_k_lt_ma h_ma_le_mini_k
      have h_Mb_empty : M_set τ D b h_nonempty = ∅ := Set.not_nonempty_iff_eq_empty.mp h_Mb_nonempty
      use insert m_a τ, τ, D, D.erase b
      constructor
      · intro h_pair_eq
        have h_eq : insert m_a τ = τ := congr_arg Prod.fst h_pair_eq
        have h_ma_in : m_a ∈ insert m_a τ := Finset.mem_insert_self m_a τ
        rw [h_eq] at h_ma_in
        exact h_ma_not_mem h_ma_in
      constructor
      · constructor
        · apply (sublemma_3_2 τ D m_a h_door h_nonempty h_ma_not_mem a b ha_mem hb_mem hab h_eq_mini).mpr
          use a, by simp
        · rw [Finset.card_insert_of_not_mem h_ma_not_mem, h_card]
      constructor
      · constructor
        · apply (sublemma_3_1 τ D h_door h_nonempty b hb_mem).mpr
          use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inr rfl), h_Mb_empty
        · rw [Finset.card_erase_of_mem hb_mem, h_card]
          simp
      constructor
      · apply isDoorof.idoor
        · apply (sublemma_3_2 τ D m_a h_door h_nonempty h_ma_not_mem a b ha_mem hb_mem hab h_eq_mini).mpr
          use a, by simp
        · exact h_door
        · exact h_ma_not_mem
        · rfl
        · rfl
      constructor
      · apply isDoorof.odoor
        · apply (sublemma_3_1 τ D h_door h_nonempty b hb_mem).mpr
          use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inr rfl), h_Mb_empty
        · exact h_door
        · exact Finset.not_mem_erase b D
        · rfl
        · exact (Finset.insert_erase hb_mem).symm
      · intros σ C h_room h_door_rel
        cases h_door_rel with
        | idoor h0 _ x hx_not_mem hx_eq hc_eq =>
          subst hx_eq hc_eq
          have h_dom : IST.isDominant (insert x τ) D := h0
          have h_x_not_mem : x ∉ τ := hx_not_mem
          have h_sigma_room : IST.isRoom (insert x τ) D := h_room
          have h_exists_max : ∃ i ∈ ({a, b} : Finset I), (M_set τ D i h_nonempty).Nonempty ∧ is_maximal_in_M_set τ D i h_nonempty x := by
            apply (sublemma_3_2 τ D x h_door h_nonempty h_x_not_mem a b ha_mem hb_mem hab h_eq_mini).mp
            exact h_dom
          obtain ⟨i, hi_mem, hi_nonempty, hi_max⟩ := h_exists_max
          cases Finset.mem_insert.mp hi_mem with
          | inl hi_eq_a =>
            subst hi_eq_a
            have h_x_eq_ma : x = m_a := by
              letI := IST i
              have h_x_in_Ma : x ∈ M_set τ D i h_nonempty := hi_max.1
              have h_ma_in_Ma : m_a ∈ M_set τ D i h_nonempty := h_ma_max.1
              have h_x_le_ma : x ≤[i] m_a := h_ma_max.2 x h_x_in_Ma
              have h_ma_le_x : m_a ≤[i] x := hi_max.2 m_a h_ma_in_Ma
              exact le_antisymm h_x_le_ma h_ma_le_x
            left
            exact ⟨h_x_eq_ma ▸ rfl, rfl⟩
          | inr hi_eq_b =>
             have hi_eq_b : i = b := Finset.mem_singleton.mp hi_eq_b
             subst hi_eq_b
             rw [h_Mb_empty] at hi_nonempty
             exact False.elim (Set.not_nonempty_empty hi_nonempty)
         | odoor h0 _ j hj_not_mem hj_eq hc_eq =>
           subst hj_eq
           have h_card_eq : C.card = τ.card := h_room.2
           have h_card_D : D.card = τ.card + 1 := h_door.2
           have h_card_insert : (insert j C).card = C.card + 1 := Finset.card_insert_of_not_mem hj_not_mem
           rw [hc_eq] at h_card_D
           rw [h_card_insert] at h_card_D
           rw [h_card_eq] at h_card_D
           have hj_in_ab : j ∈ ({a, b} : Finset I) := by
             by_contra h_not_in
             simp only [Finset.mem_insert, Finset.mem_singleton] at h_not_in
             push_neg at h_not_in
             obtain ⟨hj_ne_a, hj_ne_b⟩ := h_not_in
             have hj_in_D : j ∈ D := by rw [hc_eq]; exact Finset.mem_insert_self j C
             have ha_in_C : a ∈ C := by
               have ha_in_D : a ∈ D := ha_mem
               rw [hc_eq] at ha_in_D
               cases Finset.mem_insert.mp ha_in_D with
               | inl h_eq => exact absurd h_eq (Ne.symm hj_ne_a)
               | inr h_mem => exact h_mem
             have hb_in_C : b ∈ C := by
               have hb_in_D : b ∈ D := hb_mem
               rw [hc_eq] at hb_in_D
               cases Finset.mem_insert.mp hb_in_D with
               | inl h_eq => exact absurd h_eq (Ne.symm hj_ne_b)
               | inr h_mem => exact h_mem
             have h_inj_C : Set.InjOn (mini h_nonempty) (C : Set I) := by
               apply Finset.injOn_of_card_image_eq
               have h_tau_eq_C_image : τ = C.image (mini h_nonempty) := by
                convert keylemma_of_domiant h0 h_nonempty
               rw [←h_tau_eq_C_image]
               exact h_card_eq.symm
             exact hab (h_inj_C ha_in_C hb_in_C h_eq_mini)
           cases Finset.mem_insert.mp hj_in_ab with
           | inl hj_eq_a =>
             subst hj_eq_a
             exfalso
             have h_dom_C : IST.isDominant τ C := h_room.1
             rw [show C = D.erase j by rw[hc_eq]; exact (Finset.erase_insert hj_not_mem).symm] at h_dom_C
             have h_contra := (sublemma_3_1 τ D h_door h_nonempty j ha_mem).mp h_dom_C
             obtain ⟨_, _, _, _, _, _, _, h_M_empty⟩ := h_contra
             exact (Set.not_nonempty_iff_eq_empty.mpr h_M_empty) h_Ma_nonempty
           | inr hj_eq_b =>
             have hj_eq_b : j = b := Finset.mem_singleton.mp hj_eq_b
             subst hj_eq_b
             right
             exact ⟨rfl, (hc_eq ▸ (Finset.erase_insert hj_not_mem).symm)⟩
  · have h_Ma_empty : M_set τ D a h_nonempty = ∅ := Set.not_nonempty_iff_eq_empty.mp h_Ma_nonempty
    by_cases h_Mb_nonempty : (M_set τ D b h_nonempty).Nonempty
    · let m_b := m_element τ D b h_nonempty h_Mb_nonempty
      have h_mb_max : is_maximal_in_M_set τ D b h_nonempty m_b :=
        m_element_is_maximal τ D b h_nonempty h_Mb_nonempty
      have h_mb_not_mem : m_b ∉ τ := by
        intro h_mb_in_tau
        obtain ⟨k, hk_mem, hk_dom⟩ := h_door.1 m_b
        by_cases hk_eq_b : k = b
        · subst hk_eq_b
          have h_mb_le_mini_k : m_b ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) (by
            unfold mini
            exact @Finset.min'_mem _ (IST k) _ h_nonempty)
          have h_mb_eq_mini : m_b = mini h_nonempty k := by
            letI := IST k
            have h_mini_le_mb : mini h_nonempty k ≤[k] m_b := Finset.min'_le τ m_b h_mb_in_tau
            exact le_antisymm h_mb_le_mini_k h_mini_le_mb
          have h_mb_in_M : m_b ∈ M_set τ D k h_nonempty := by
            convert h_mb_max.1
          unfold M_set at h_mb_in_M
          have h_mini_a_lt_mb : mini h_nonempty a <[a] m_b := h_mb_in_M a ha_mem hab
          rw [h_mb_eq_mini, ←h_eq_mini] at h_mini_a_lt_mb
          letI := IST a
          exact lt_irrefl (mini h_nonempty a) h_mini_a_lt_mb
        · have h_mb_in_M : m_b ∈ M_set τ D b h_nonempty := h_mb_max.1
          unfold M_set at h_mb_in_M
          have h_mini_k_lt_mb : mini h_nonempty k <[k] m_b := h_mb_in_M k hk_mem hk_eq_b
          have h_mb_le_mini_k : m_b ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) (by
            unfold mini
            exact @Finset.min'_mem _ (IST k) _ h_nonempty)
          letI := IST k
          exact not_le.mpr h_mini_k_lt_mb h_mb_le_mini_k
      use insert m_b τ, τ, D, D.erase a
      constructor
      · intro h_pair_eq
        have h_eq : insert m_b τ = τ := congr_arg Prod.fst h_pair_eq
        have h_mb_in : m_b ∈ insert m_b τ := Finset.mem_insert_self m_b τ
        rw [h_eq] at h_mb_in
        exact h_mb_not_mem h_mb_in
      constructor
      · constructor
        · apply (sublemma_3_2 τ D m_b h_door h_nonempty h_mb_not_mem a b ha_mem hb_mem hab h_eq_mini).mpr
          use b, by simp
        · rw [Finset.card_insert_of_not_mem h_mb_not_mem, h_card]
      constructor
      · constructor
        · apply (sublemma_3_1 τ D h_door h_nonempty a ha_mem).mpr
          use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inl rfl), h_Ma_empty
        · rw [Finset.card_erase_of_mem ha_mem, h_card]
          simp
      constructor
      · apply isDoorof.idoor
        · apply (sublemma_3_2 τ D m_b h_door h_nonempty h_mb_not_mem a b ha_mem hb_mem hab h_eq_mini).mpr
          use b, by simp
        · exact h_door
        · exact h_mb_not_mem
        · rfl
        · rfl
      constructor
      · apply isDoorof.odoor
        · apply (sublemma_3_1 τ D h_door h_nonempty a ha_mem).mpr
          use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inl rfl), h_Ma_empty
        · exact h_door
        · exact Finset.not_mem_erase a D
        · rfl
        · exact (Finset.insert_erase ha_mem).symm
      · intros σ C h_room h_door_rel
        cases h_door_rel with
        | idoor h0 _ x hx_not_mem hx_eq hc_eq =>
          subst hx_eq hc_eq
          have h_dom : IST.isDominant (insert x τ) D := h0
          have h_x_not_mem : x ∉ τ := hx_not_mem
          have h_sigma_room : IST.isRoom (insert x τ) D := h_room
          have h_exists_max : ∃ i ∈ ({a, b} : Finset I), (M_set τ D i h_nonempty).Nonempty ∧ is_maximal_in_M_set τ D i h_nonempty x := by
            apply (sublemma_3_2 τ D x h_door h_nonempty h_x_not_mem a b ha_mem hb_mem hab h_eq_mini).mp
            exact h_dom
          obtain ⟨i, hi_mem, hi_nonempty, hi_max⟩ := h_exists_max
          cases Finset.mem_insert.mp hi_mem with
          | inl hi_eq_a =>
            subst hi_eq_a
            rw [h_Ma_empty] at hi_nonempty
            exact False.elim (Set.not_nonempty_empty hi_nonempty)
          | inr hi_eq_b =>
            have hi_eq_b : i = b := Finset.mem_singleton.mp hi_eq_b
            subst hi_eq_b
            have h_x_eq_mb : x = m_b := by
              letI := IST i
              have h_x_in_Mb : x ∈ M_set τ D i h_nonempty := hi_max.1
              have h_mb_in_Mb : m_b ∈ M_set τ D i h_nonempty := h_mb_max.1
              have h_x_le_mb : x ≤[i] m_b := h_mb_max.2 x h_x_in_Mb
              have h_mb_le_x : m_b ≤[i] x := hi_max.2 m_b h_mb_in_Mb
              exact le_antisymm h_x_le_mb h_mb_le_x
            left
            exact ⟨h_x_eq_mb ▸ rfl, rfl⟩
         | odoor h0 _ j hj_not_mem hj_eq hc_eq =>
           subst hj_eq
           have h_card_eq : C.card = τ.card := h_room.2
           have h_card_D : D.card = τ.card + 1 := h_door.2
           have h_card_insert : (insert j C).card = C.card + 1 := Finset.card_insert_of_not_mem hj_not_mem
           rw [hc_eq] at h_card_D
           rw [h_card_insert] at h_card_D
           rw [h_card_eq] at h_card_D
           have hj_in_ab : j ∈ ({a, b} : Finset I) := by
             by_contra h_not_in
             simp only [Finset.mem_insert, Finset.mem_singleton] at h_not_in
             push_neg at h_not_in
             obtain ⟨hj_ne_a, hj_ne_b⟩ := h_not_in
             have hj_in_D : j ∈ D := by rw [hc_eq]; exact Finset.mem_insert_self j C
             have ha_in_C : a ∈ C := by
               have ha_in_D : a ∈ D := ha_mem
               rw [hc_eq] at ha_in_D
               cases Finset.mem_insert.mp ha_in_D with
               | inl h_eq => exact absurd h_eq (Ne.symm hj_ne_a)
               | inr h_mem => exact h_mem
             have hb_in_C : b ∈ C := by
               have hb_in_D : b ∈ D := hb_mem
               rw [hc_eq] at hb_in_D
               cases Finset.mem_insert.mp hb_in_D with
               | inl h_eq => exact absurd h_eq (Ne.symm hj_ne_b)
               | inr h_mem => exact h_mem
             have h_inj_C : Set.InjOn (mini h_nonempty) (C : Set I) := by
               apply Finset.injOn_of_card_image_eq
               have h_tau_eq_C_image : τ = C.image (mini h_nonempty) := by
                convert keylemma_of_domiant h0 h_nonempty
               rw [←h_tau_eq_C_image]
               exact h_card_eq.symm
             exact hab (h_inj_C ha_in_C hb_in_C h_eq_mini)

           cases Finset.mem_insert.mp hj_in_ab with
           | inl hj_eq_a =>
             have hj_eq_a : j = a := hj_eq_a
             subst hj_eq_a
             right
             exact ⟨rfl, (hc_eq ▸ (Finset.erase_insert hj_not_mem).symm)⟩
           | inr hj_eq_b =>
             exfalso
             have h_dom_C : IST.isDominant τ C := h_room.1
             rw [show C = D.erase j by rw[hc_eq]; exact (Finset.erase_insert hj_not_mem).symm] at h_dom_C
             have hj_eq_b : j = b := Finset.mem_singleton.mp hj_eq_b
             subst hj_eq_b
             have h_contra := (sublemma_3_1 τ D h_door h_nonempty j hb_mem).mp h_dom_C
             obtain ⟨_, _, _, _, _, _, _, h_M_empty⟩ := h_contra
             exact (Set.not_nonempty_iff_eq_empty.mpr h_M_empty) h_Mb_nonempty
    · have h_Mb_empty : M_set τ D b h_nonempty = ∅ := Set.not_nonempty_iff_eq_empty.mp h_Mb_nonempty
      use τ, τ, D.erase b, D.erase a
      constructor
      · intro h_pair_eq
        have h_erasure_eq : D.erase b = D.erase a := congr_arg Prod.snd h_pair_eq
        have h_a_in_erase_b : a ∈ D.erase b := Finset.mem_erase.mpr ⟨hab, ha_mem⟩
        rw [h_erasure_eq] at h_a_in_erase_b
        exact (Finset.not_mem_erase a D) h_a_in_erase_b
      constructor
      · constructor
        · apply (sublemma_3_1 τ D h_door h_nonempty b hb_mem).mpr
          use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inr rfl), h_Mb_empty
        · rw [Finset.card_erase_of_mem hb_mem, h_door.2]
          simp
      constructor
      · constructor
        · apply (sublemma_3_1 τ D h_door h_nonempty a ha_mem).mpr
          use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inl rfl), h_Ma_empty
        · rw [Finset.card_erase_of_mem ha_mem, h_door.2]
          simp
      constructor
      · apply isDoorof.odoor
        · apply (sublemma_3_1 τ D h_door h_nonempty b hb_mem).mpr
          use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inr rfl), h_Mb_empty
        · exact h_door
        · exact Finset.not_mem_erase b D
        · rfl
        · exact (Finset.insert_erase hb_mem).symm
      constructor
      · apply isDoorof.odoor
        · apply (sublemma_3_1 τ D h_door h_nonempty a ha_mem).mpr
          use a, b, ha_mem, hb_mem, hab, h_eq_mini, (Or.inl rfl), h_Ma_empty
        · exact h_door
        · exact Finset.not_mem_erase a D
        · rfl
        · exact (Finset.insert_erase ha_mem).symm
      · intros σ C h_room h_door_rel
        cases h_door_rel with
        | idoor h0 _ x hx_not_mem hx_eq hc_eq =>
          subst hx_eq hc_eq
          have h_dom : IST.isDominant (insert x τ) D := h0
          have h_x_not_mem : x ∉ τ := hx_not_mem
          have h_exists_max : ∃ i ∈ ({a, b} : Finset I), (M_set τ D i h_nonempty).Nonempty ∧ is_maximal_in_M_set τ D i h_nonempty x := by
            apply (sublemma_3_2 τ D x h_door h_nonempty h_x_not_mem a b ha_mem hb_mem hab h_eq_mini).mp
            exact h_dom
          obtain ⟨i, hi_mem, hi_nonempty, _⟩ := h_exists_max
          cases Finset.mem_insert.mp hi_mem with
          | inl hi_eq_a =>
            subst hi_eq_a
            rw [h_Ma_empty] at hi_nonempty
            exact absurd hi_nonempty Set.not_nonempty_empty
          | inr hi_eq_b =>
            have hi_eq_b : i = b := Finset.mem_singleton.mp hi_eq_b
            subst hi_eq_b
            rw [h_Mb_empty] at hi_nonempty
            exact absurd hi_nonempty Set.not_nonempty_empty
        | odoor h0 _ j hj_not_mem hj_eq hc_eq =>
          subst hj_eq
          have h_dom_C : IST.isDominant τ C := h0
          have h_card_eq : C.card = τ.card := h_room.2
          have h_card_D : D.card = τ.card + 1 := h_door.2
          have h_card_insert : (insert j C).card = C.card + 1 := Finset.card_insert_of_not_mem hj_not_mem
          rw [hc_eq] at h_card_D
          rw [h_card_insert] at h_card_D
          rw [h_card_eq] at h_card_D
          have hj_in_ab : j ∈ ({a, b} : Finset I) := by
            by_contra h_not_in
            simp only [Finset.mem_insert, Finset.mem_singleton] at h_not_in
            push_neg at h_not_in
            obtain ⟨hj_ne_a, hj_ne_b⟩ := h_not_in
            have hj_in_D : j ∈ D := by rw [hc_eq]; exact Finset.mem_insert_self j C
            have ha_in_C : a ∈ C := by
              have ha_in_D : a ∈ D := ha_mem
              rw [hc_eq] at ha_in_D
              cases Finset.mem_insert.mp ha_in_D with
              | inl h_eq => exact absurd h_eq (Ne.symm hj_ne_a)
              | inr h_mem => exact h_mem
            have hb_in_C : b ∈ C := by
              have hb_in_D : b ∈ D := hb_mem
              rw [hc_eq] at hb_in_D
              cases Finset.mem_insert.mp hb_in_D with
              | inl h_eq => exact absurd h_eq (Ne.symm hj_ne_b)
              | inr h_mem => exact h_mem
            have h_inj_C : Set.InjOn (mini h_nonempty) (C : Set I) := by
              apply Finset.injOn_of_card_image_eq
              have h_tau_eq_C_image : τ = C.image (mini h_nonempty) := by
                convert keylemma_of_domiant h0 h_nonempty
              rw [←h_tau_eq_C_image]
              exact h_card_eq.symm
            exact hab (h_inj_C ha_in_C hb_in_C h_eq_mini)
          cases Finset.mem_insert.mp hj_in_ab with
          | inl hj_eq_a =>
            have hj_eq_a : j = a := hj_eq_a
            subst hj_eq_a
            have h_C_eq_erase : C = D.erase j := by
              rw [hc_eq]
              exact (Finset.erase_insert hj_not_mem).symm
            right
            exact ⟨rfl, h_C_eq_erase⟩
          | inr hj_eq_b =>
            have hj_eq_b : j = b := Finset.mem_singleton.mp hj_eq_b
            subst hj_eq_b
            have h_C_eq_erase : C = D.erase j := by
              rw [hc_eq]
              exact (Finset.erase_insert hj_not_mem).symm
            left
            exact ⟨rfl, h_C_eq_erase⟩

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


--Useless lemma, remain sorry first.
/-section useless_lemma
lemma door_of_Croom (h1 : isColorful c σ C) (h2 : isDoorof τ D σ C) : isNearlyColorful c τ D := by sorry

lemma unique_type_door_of_Croom (h1 : isColorful c σ C) (i :I) :
∃! x : Finset T × Finset I , isDoorof x.1 x.2 σ C ∧ isTypedNC c i σ C:= by sorry

lemma type_aux (h : isNearlyColorful c σ C) : ∃! i : I, i ∉ σ.image c ∧ C = insert i (σ.image c) := by
  sorry

def NCtype (h : isNearlyColorful c σ C) : I :=
  Classical.choose (type_aux h).exists

structure TypedNC (i : I) (σ : Finset T) (C : Finset I): Prop where
  nc : isNearlyColorful c σ C
  t : NCtype nc = i
end useless_lemma-/

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

/-variable {c σ C} in
lemma type_unique_of_outsidedoor (h : isOutsideDoor σ C) : ∃! i,  i = isNCtype (NC_of_outsidedoor (c:=c) h)  := sorry-/

/-Lemma 5-/
omit [Inhabited T] in
lemma NC_or_C_of_door (h1 : isTypedNC c i τ D) (h2 : isDoorof τ D σ C) :
  isTypedNC c i σ C ∨ isColorful c σ C := by

  unfold isTypedNC at h1 ⊢
  unfold isColorful
  obtain ⟨h1_cell, h1_notin, h1_eq⟩ := h1

  have h_sigma_cell : isCell σ C := by
    cases h2 with
    | idoor h0 _ _ _ _ _ => exact h0
    | odoor h0 _ _ _ _ _ => exact h0

  have step1_subset : C \ (σ.image c) ⊆ D \ (τ.image c) := by
    intro y hy
    simp only [Finset.mem_sdiff] at hy ⊢
    obtain ⟨y_in_C, y_notin_img_sigma⟩ := hy
    constructor
    · cases h2
      · rename_i h_D_eq; rw [h_D_eq]; exact y_in_C
      · rename_i h_D_eq; rw [h_D_eq]; exact Finset.mem_insert_of_mem y_in_C
    · cases h2 with
      | idoor h0 hdoor x h_x_notin h_sigma_eq h_D_eq =>
        rw [← h_sigma_eq, Finset.image_insert] at y_notin_img_sigma
        simp only [Finset.mem_insert, not_or] at y_notin_img_sigma
        exact y_notin_img_sigma.2
      | odoor h0 hdoor j h_j_notin h_sigma_eq h_D_eq =>
        rw [← h_sigma_eq] at y_notin_img_sigma
        exact y_notin_img_sigma

  have step2_D_card : (D \ (τ.image c)).card = 1 := by
    have D_sdiff_eq_i : D \ (τ.image c) = {i} := by
      rw [h1_eq]
      ext x
      simp only [mem_sdiff, mem_insert, mem_singleton, h1_notin]
      constructor
      · intro h; exact h.1.resolve_right h.2
      · intro h_xi; rw [h_xi]; exact ⟨Or.inl rfl, h1_notin⟩
    rw [D_sdiff_eq_i, Finset.card_singleton]

  have step3_C_card_le : (C \ σ.image c).card ≤ 1 := by
    rw [← step2_D_card]
    exact Finset.card_le_card step1_subset

  by_cases h : (C \ σ.image c).card = 0
  · -- Case: colorful
    right
    constructor
    · exact h_sigma_cell
    · have h_C_subset_img : C ⊆ σ.image c := by
        rw [Finset.subset_iff]
        intro x hx
        by_contra hxn
        have : x ∈ C \ σ.image c := by simp [hx, hxn]
        have : (C \ σ.image c).Nonempty := ⟨x, this⟩
        have : 0 < (C \ σ.image c).card := Finset.card_pos.2 this
        linarith [h]

      have h_room: isRoom σ C := isRoom_of_Door h2
      have h_card_eq : C.card = σ.card := h_room.2
      have h_img_le_C_card : (σ.image c).card ≤ C.card := by
        calc (σ.image c).card
          ≤ σ.card := Finset.card_image_le
          _ = C.card := h_card_eq.symm
      exact (Finset.eq_of_subset_of_card_le h_C_subset_img h_img_le_C_card).symm

  · -- Case: nearly colorful of same type
    left
    constructor
    · exact h_sigma_cell
    · have h_card_one : (C \ σ.image c).card = 1 := by omega

      have h_subset_singleton : C \ σ.image c ⊆ {i} := by
        have D_sdiff_eq_i : D \ (τ.image c) = {i} := by
          rw [h1_eq]
          ext x
          simp only [mem_sdiff, mem_insert, mem_singleton, h1_notin]
          constructor
          · intro h; exact h.1.resolve_right h.2
          · intro h_xi; rw [h_xi]; exact ⟨Or.inl rfl, h1_notin⟩
        rw [← D_sdiff_eq_i]
        exact step1_subset

      have C_sdiff_eq_i : C \ σ.image c = {i} :=
        Finset.eq_of_subset_of_card_le h_subset_singleton (by rw [h_card_one, Finset.card_singleton])

      have h_i_notin_img : i ∉ σ.image c := by
        have h_i_in_sdiff : i ∈ C \ σ.image c := by rw [C_sdiff_eq_i]; simp
        exact (Finset.mem_sdiff.mp h_i_in_sdiff).2

      constructor
      · exact h_i_notin_img
      · ext x
        constructor
        · intro hx
          rw [Finset.mem_insert]
          by_cases h_img : x ∈ σ.image c
          · right; exact h_img
          · left
            have h_in_sdiff : x ∈ C \ σ.image c := Finset.mem_sdiff.mpr ⟨hx, h_img⟩
            rw [C_sdiff_eq_i] at h_in_sdiff
            exact Finset.mem_singleton.mp h_in_sdiff
        · intro hx
          rw [Finset.mem_insert] at hx
          cases hx with
          | inl h_xi =>
            rw [h_xi]
            have : i ∈ C \ σ.image c := by rw [C_sdiff_eq_i]; simp
            exact (Finset.mem_sdiff.mp this).1
          | inr h => sorry

omit [Inhabited T] in
lemma NCtype_of_door (h1 : isTypedNC c i τ D) (_ : isDoorof τ D σ C) (_ : isTypedNC c i σ C) : isTypedNC c i τ D := h1

/-
Lemma 6 : The version in paper is incorrect-/
omit [Inhabited T] [DecidableEq T] in
lemma card_of_NCcell (h : isNearlyColorful c σ D) : #σ = #(image c σ)  ∨  #σ = #(image c σ) + 1 := by
  unfold isNearlyColorful at h
  rcases h with ⟨h_cell, h_nc_card⟩
  let img := image c σ
  have h_card_le_D : σ.card ≤ D.card := card_le_of_domiant h_cell
  have h_D_card_eq := (Finset.card_sdiff_add_card_inter D img).symm
  rw [h_nc_card] at h_D_card_eq
  have h_inter_le_img : (D ∩ img).card ≤ img.card := card_le_card (Finset.inter_subset_right)
  have h_D_le : D.card ≤ 1 + img.card := by
    linarith [h_D_card_eq, h_inter_le_img]
  have h_img_le_sigma : img.card ≤ σ.card := card_image_le
  have h_sigma_le_plus_one : σ.card ≤ img.card + 1 := by
    linarith [h_card_le_D, h_D_le]
  have h_or : σ.card ≤ img.card ∨ σ.card = img.card + 1 := by
    apply Nat.le_or_eq_of_le_succ
    exact h_sigma_le_plus_one
  cases h_or with
  | inl h_le =>
    left
    exact le_antisymm h_le h_img_le_sigma
  | inr h_eq =>
    right
    exact h_eq

/- Lemma 7-/
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
  · have h_card_eq : σ.card = (image c σ).card + 1 := by
      have h_pos : 0 < σ.card := by
        have h_nonempty := sigma_nonempty_of_room h0
        exact Finset.card_pos.2 h_nonempty
      rw [←h_card_case]

    obtain ⟨x, y, hx_mem, hy_mem, hxy_eq, hxy_ne, h_inj_remove⟩ := injOn_sdiff σ c h_card_eq

    obtain ⟨_, h_i_notin, h_C_eq⟩ := h1

    have h_inj_x : Set.InjOn c (σ \ {x}) := by
      have h_remove_x : (σ \ {x}).card = (image c (σ \ {x})).card := by
        have h1 : image c (σ \ {x}) = image c σ := by
          ext z
          constructor
          · intro hz
            obtain ⟨w, hw_mem, hw_eq⟩ := Finset.mem_image.mp hz
            exact Finset.mem_image.mpr ⟨w, (Finset.mem_sdiff.mp hw_mem).1, hw_eq⟩
          · intro hz
            obtain ⟨w, hw_mem, hw_eq⟩ := Finset.mem_image.mp hz
            by_cases h : w = x
            · subst h
              rw [←hw_eq, hxy_eq]
              exact Finset.mem_image.mpr ⟨y, Finset.mem_sdiff.mpr ⟨hy_mem, by simp [hxy_ne.symm]⟩, rfl⟩
            · exact Finset.mem_image.mpr ⟨w, Finset.mem_sdiff.mpr ⟨hw_mem, by simp [h]⟩, hw_eq⟩
        rw [h1, Finset.card_sdiff (by simp [hx_mem]), Finset.card_singleton]
        rw [h_card_eq]
        omega
      convert Finset.injOn_of_card_image_eq h_remove_x.symm
      simp only [Finset.coe_sdiff, Finset.coe_singleton]

    have h_inj_y : Set.InjOn c (σ \ {y}) := by
      have h_remove_y : (σ \ {y}).card = (image c (σ \ {y})).card := by
        have h1 : image c (σ \ {y}) = image c σ := by
          ext z
          constructor
          · intro hz
            obtain ⟨w, hw_mem, hw_eq⟩ := Finset.mem_image.mp hz
            exact Finset.mem_image.mpr ⟨w, (Finset.mem_sdiff.mp hw_mem).1, hw_eq⟩
          · intro hz
            obtain ⟨w, hw_mem, hw_eq⟩ := Finset.mem_image.mp hz
            by_cases h : w = y
            · subst h
              rw [←hw_eq, ←hxy_eq]
              exact Finset.mem_image.mpr ⟨x, Finset.mem_sdiff.mpr ⟨hx_mem, by simp [hxy_ne]⟩, rfl⟩
            · exact Finset.mem_image.mpr ⟨w, Finset.mem_sdiff.mpr ⟨hw_mem, by simp [h]⟩, hw_eq⟩
        rw [h1, Finset.card_sdiff (by simp [hy_mem]), Finset.card_singleton]
        rw [h_card_eq]
        omega
      convert Finset.injOn_of_card_image_eq h_remove_y.symm
      simp only [Finset.coe_sdiff, Finset.coe_singleton]

    have h_door_x : isDoor (σ \ {x}) C := by
      constructor
      · exact Dominant_of_subset _ _ _ (Finset.sdiff_subset) h0.1
      · rw [Finset.card_sdiff (by simp [hx_mem]), Finset.card_singleton, h0.2]
        omega

    have h_door_y : isDoor (σ \ {y}) C := by
      constructor
      · exact Dominant_of_subset _ _ _ (Finset.sdiff_subset) h0.1
      · rw [Finset.card_sdiff (by simp [hy_mem]), Finset.card_singleton, h0.2]
        omega
    have h_img_eq_x : image c (σ \ {x}) = image c σ := by
          ext z
          constructor
          · intro hz
            obtain ⟨w, hw_mem, hw_eq⟩ := Finset.mem_image.mp hz
            exact Finset.mem_image.mpr ⟨w, (Finset.mem_sdiff.mp hw_mem).1, hw_eq⟩
          · intro hz
            obtain ⟨w, hw_mem, hw_eq⟩ := Finset.mem_image.mp hz
            by_cases h : w = x
            · subst h
              rw [←hw_eq, hxy_eq]
              exact Finset.mem_image.mpr ⟨y, Finset.mem_sdiff.mpr ⟨hy_mem, by simp [hxy_ne.symm]⟩, rfl⟩
            · exact Finset.mem_image.mpr ⟨w, Finset.mem_sdiff.mpr ⟨hw_mem, by simp [h]⟩, hw_eq⟩
    have h_typed_x : isTypedNC c i (σ \ {x}) C := by
      constructor
      · exact h_door_x.1
      · constructor
        · rw [h_img_eq_x]
          exact h_i_notin
        · rw [h_C_eq]
          congr 1
          rw [h_img_eq_x]
    have h_img_eq_y : image c (σ \ {y}) = image c σ := by
            ext z
            constructor
            · intro hz
              obtain ⟨w, hw_mem, hw_eq⟩ := Finset.mem_image.mp hz
              exact Finset.mem_image.mpr ⟨w, (Finset.mem_sdiff.mp hw_mem).1, hw_eq⟩
            · intro hz
              obtain ⟨w, hw_mem, hw_eq⟩ := Finset.mem_image.mp hz
              by_cases h : w = y
              · subst h
                rw [←hw_eq, ←hxy_eq]
                exact Finset.mem_image.mpr ⟨x, Finset.mem_sdiff.mpr ⟨hx_mem, by simp [hxy_ne]⟩, rfl⟩
              · exact Finset.mem_image.mpr ⟨w, Finset.mem_sdiff.mpr ⟨hw_mem, by simp [h]⟩, hw_eq⟩
    have h_typed_y : isTypedNC c i (σ \ {y}) C := by
      constructor
      · exact h_door_y.1
      · constructor
        · rw [h_img_eq_y]
          exact h_i_notin
        · rw [h_C_eq]
          congr 1
          rw [h_img_eq_y]

    have h_doorof_x : isDoorof (σ \ {x}) C σ C := by
      apply isDoorof.idoor h0.1 h_door_x x
      · simp [hx_mem]
      · rw [Finset.sdiff_singleton_eq_erase]; exact Finset.insert_erase hx_mem
      · rfl

    have h_doorof_y : isDoorof (σ \ {y}) C σ C := by
      apply isDoorof.idoor h0.1 h_door_y y
      · simp [hy_mem]
      · rw [Finset.sdiff_singleton_eq_erase]; exact Finset.insert_erase hy_mem
      · rfl

    use (σ \ {x}, C), (σ \ {y}, C)
    constructor
    · intro h_eq
      have : x = y := by
        have h1 : σ \ {x} = σ \ {y} := by
          have ⟨h1, h2⟩ := Prod.mk.inj h_eq
          exact h1
        by_contra hne
        have hy_in_left : y ∈ σ \ {x} := by simp [hy_mem, Ne.symm hne]
        rw [h1] at hy_in_left
        have hy_notin : y ∉ σ \ {y} := by simp
        exact hy_notin hy_in_left
      exact hxy_ne this
    · ext ⟨τ, D⟩
      constructor
      · intro h_mem
        simp [doors_NCroom] at h_mem
        obtain ⟨h_typed, h_doorof⟩ := h_mem
        cases h_doorof with
        | idoor h_cell_σC h_door_τC z hz hτ_eq hD_eq =>
          have hτ_eq_sdiff : τ = σ \ {z} := by
            have h_insert : insert z τ = σ := hτ_eq
            have h_subset : τ ⊆ σ := by
              rw [←h_insert]
              exact Finset.subset_insert z τ
            have h_z_in_σ : z ∈ σ := by
              rw [←h_insert]
              exact Finset.mem_insert_self z τ
            ext w
            constructor
            · intro hw_τ
              simp
              constructor
              · exact h_subset hw_τ
              · intro h_eq
                subst h_eq
                exact hz hw_τ
            · intro hw_sdiff
              simp at hw_sdiff
              obtain ⟨hw_σ, hw_ne⟩ := hw_sdiff
              by_contra hw_not_τ
              have h_w_in_insert : w ∈ insert z τ := by
                rw [h_insert]
                exact hw_σ
              simp at h_w_in_insert
              cases h_w_in_insert with
              | inl h_eq => exact hw_ne h_eq
              | inr h_in => exact hw_not_τ h_in

          rw [hτ_eq_sdiff, hD_eq]
          simp
          have h_img_eq : (σ \ {z}).image c = σ.image c := by
            have h_D_eq_insert : D = insert i (τ.image c) := h_typed.2.2
            rw [hτ_eq_sdiff] at h_D_eq_insert
            rw [hD_eq] at h_D_eq_insert
            have h_eq : insert i ((σ \ {z}).image c) = insert i (σ.image c) := by
              rw [←h_D_eq_insert, h_C_eq]
            have h_i_notin_sdiff : i ∉ (σ \ {z}).image c := by
              rw [hτ_eq_sdiff] at h_typed
              exact h_typed.2.1
            have h_insert_eq : (σ \ {z}).image c = σ.image c := by
              ext y
              constructor
              · intro hy
                have h_y_in_insert : y ∈ insert i ((σ \ {z}).image c) := Finset.mem_insert_of_mem hy
                rw [h_eq] at h_y_in_insert
                simp only [Finset.mem_insert] at h_y_in_insert
                cases h_y_in_insert with
                | inl h_eq_i =>
                  subst h_eq_i
                  exfalso
                  have h_subset : image c (σ \ {z}) ⊆ image c σ := by
                    intro y hy
                    obtain ⟨x, hx, rfl⟩ := by simpa using hy
                    exact Finset.mem_image_of_mem c hx.1
                  exact h_i_notin (h_subset hy)
                | inr h_mem => exact h_mem
              · intro hy
                have y_ne_i : y ≠ i := fun h => h_i_notin (h ▸ hy)
                have hy' : y ∈ insert i (image c σ) := Finset.mem_insert.2 (Or.inr hy)
                rw [←h_eq] at hy'
                simpa [y_ne_i] using hy'
            exact h_insert_eq
          have hz_mem : z ∈ σ := by
            rw [←hτ_eq]
            exact Finset.mem_insert_self z τ

          have h_exists_eq : ∃ w ∈ σ \ {z}, c z = c w := by
            by_contra h_not_exists
            push_neg at h_not_exists
            have h_z_unique : ∀ w ∈ σ \ {z}, c z ≠ c w := h_not_exists
            have h_cz_in_image : c z ∈ (σ.image c) := by
              exact Finset.mem_image.mpr ⟨z, hz_mem, rfl⟩
            have h_cz_notin_sdiff_image : c z ∉ ((σ \ {z}).image c) := by
              intro h_in
              obtain ⟨w, hw_mem, hw_eq⟩ := Finset.mem_image.mp h_in
              have hw_in_sdiff : w ∈ σ \ {z} := hw_mem
              have h_eq_cz : c z = c w := hw_eq.symm
              exact h_z_unique w hw_in_sdiff h_eq_cz
            have h_subset : (σ \ {z}).image c ⊆ σ.image c := by
              intro y hy
              obtain ⟨w, hw_mem, hw_eq⟩ := Finset.mem_image.mp hy
              exact Finset.mem_image.mpr ⟨w, (Finset.mem_sdiff.mp hw_mem).1, hw_eq⟩
            have h_strict_subset : (σ \ {z}).image c ⊂ σ.image c := by
              rw [Finset.ssubset_iff_subset_ne]
              constructor
              · exact h_subset
              · intro h_eq
                rw [h_eq] at h_cz_notin_sdiff_image
                exact h_cz_notin_sdiff_image h_cz_in_image
            rw [Finset.ssubset_iff_subset_ne] at h_strict_subset
            exact h_strict_subset.2 h_img_eq

          obtain ⟨w, hw_mem, hzw_eq⟩ := h_exists_eq
          have hw_in_σ : w ∈ σ := (Finset.mem_sdiff.mp hw_mem).1
          have hw_ne_z : w ≠ z := by
            intro h_eq
            subst h_eq
            simp at hw_mem

          have h_pair_eq : ({z, w} : Finset T) = {x, y} := by
            have not_both_in_sdiff : ¬(z ∈ σ \ {x, y} ∧ w ∈ σ \ {x, y}) :=
              fun ⟨hz_in, hw_in⟩ => hw_ne_z.symm (h_inj_remove (by rw [←Finset.coe_sdiff, Finset.mem_coe]; exact hz_in) (by rw [←Finset.coe_sdiff, Finset.mem_coe]; exact hw_in) hzw_eq)

            have at_least_one_in_xy : z ∈ ({x, y} : Finset T) ∨ w ∈ ({x, y} : Finset T) := by
              by_contra h
              push_neg at h
              exact not_both_in_sdiff ⟨Finset.mem_sdiff.mpr ⟨hz_mem, h.1⟩, Finset.mem_sdiff.mpr ⟨hw_in_σ, h.2⟩⟩

            by_cases hz_in_xy : z ∈ ({x, y} : Finset T)
            · by_cases hw_in_xy : w ∈ ({x, y} : Finset T)
              · apply Finset.eq_of_subset_of_card_le
                · intro t ht; simp at ht; cases' ht with h h <;> subst t <;> assumption
                · rw [Finset.card_pair hw_ne_z.symm, Finset.card_pair hxy_ne]
              · have hw_in_sdiff : w ∈ σ \ {x, y} := Finset.mem_sdiff.mpr ⟨hw_in_σ, hw_in_xy⟩
                simp at hz_in_xy
                cases hz_in_xy with
                | inl h =>
                  subst h
                  have h_cx_cw : c z = c w := hzw_eq
                  have h_cy_cw : c y = c w := by rw [←hxy_eq, h_cx_cw]

                  have h_y_ne_w : y ≠ w := by
                    intro h_eq
                    subst h_eq
                    have h_y_notin : y ∉ σ \ {z, y} := by
                      simp [hxy_ne]
                    exact h_y_notin hw_in_sdiff

                  have h_contradiction : False := by
                    have h_inj : ∀ {a b : T}, a ∈ (σ \ {z} : Set T) → b ∈ (σ \ {z} : Set T) → c a = c b → a = b := by
                      intros a b ha hb h_eq
                      exact h_inj_x ha hb h_eq

                    have h_y_mem_set : y ∈ (σ \ {z} : Set T) := by
                      rw [Set.mem_diff]
                      constructor
                      · rw [Finset.mem_coe]; exact hy_mem
                      · intro h_in
                        rw [Set.mem_singleton_iff] at h_in
                        exact hxy_ne.symm h_in

                    have h_w_mem_set : w ∈ (σ \ {z} : Set T) := by
                      rw [Set.mem_diff]
                      constructor
                      · rw [Finset.mem_coe]; exact hw_in_σ
                      · intro h_in
                        rw [Set.mem_singleton_iff] at h_in
                        exact hw_ne_z h_in
                    have h_y_eq_w : y = w := h_inj h_y_mem_set h_w_mem_set h_cy_cw
                    exact h_y_ne_w h_y_eq_w
                  exact False.elim h_contradiction
                | inr h =>
                  subst h
                  have h_cz_cw : c z = c w := hzw_eq
                  have h_cx_cw : c x = c w := by rw [hxy_eq, h_cz_cw]

                  have h_x_ne_w : x ≠ w := by
                    intro h_eq
                    subst h_eq
                    have h_x_notin : x ∉ σ \ {x, z} := by
                      simp [hxy_ne.symm]
                    exact h_x_notin hw_in_sdiff

                  have h_contradiction : False := by
                    have h_inj : ∀ {a b : T}, a ∈ (σ \ {z} : Set T) → b ∈ (σ \ {z} : Set T) → c a = c b → a = b := by
                      intros a b ha hb h_eq
                      exact h_inj_y ha hb h_eq

                    have h_x_mem_set : x ∈ (σ \ {z} : Set T) := by
                      rw [Set.mem_diff]
                      constructor
                      · rw [Finset.mem_coe]; exact hx_mem
                      · intro h_in
                        rw [Set.mem_singleton_iff] at h_in
                        exact hxy_ne.symm h_in.symm

                    have h_w_mem_set : w ∈ (σ \ {z} : Set T) := by
                      rw [Set.mem_diff]
                      constructor
                      · rw [Finset.mem_coe]; exact hw_in_σ
                      · intro h_in
                        rw [Set.mem_singleton_iff] at h_in
                        exact hw_ne_z h_in

                    have h_x_eq_w : x = w := h_inj h_x_mem_set h_w_mem_set h_cx_cw
                    exact h_x_ne_w h_x_eq_w

                  exact False.elim h_contradiction
            · have hw_in_xy : w ∈ {x, y} := at_least_one_in_xy.resolve_left hz_in_xy
              have hz_in_sdiff : z ∈ σ \ {x, y} := Finset.mem_sdiff.mpr ⟨hz_mem, hz_in_xy⟩
              simp at hw_in_xy
              cases hw_in_xy with
              | inl h =>
                  subst h
                  have h_cz_cx : c z = c w := hzw_eq
                  have h_cz_cy : c z = c y := by rw [←hxy_eq, h_cz_cx]

                  have h_z_ne_y : z ≠ y := by
                    intro h_eq
                    subst h_eq
                    have h_y_notin : z ∉ σ \ {w, z} := by simp
                    exact h_y_notin hz_in_sdiff

                  have h_contradiction : False := by
                    have h_inj : ∀ {a b : T}, a ∈ (σ \ {w} : Set T) → b ∈ (σ \ {w} : Set T) → c a = c b → a = b := by
                      intros a b ha hb h_eq
                      exact h_inj_x ha hb h_eq

                    have h_z_mem_set : z ∈ (σ \ {w} : Set T) := by
                      rw [Set.mem_diff]
                      constructor
                      · rw [Finset.mem_coe]; exact hz_mem
                      · intro h_in
                        rw [Set.mem_singleton_iff] at h_in
                        have hz_notin_wy : z ∉ {w, y} := (Finset.mem_sdiff.mp hz_in_sdiff).2
                        simp at hz_notin_wy
                        exact hz_notin_wy.1 h_in

                    have h_y_mem_set : y ∈ (σ \ {w} : Set T) := by
                      rw [Set.mem_diff]
                      constructor
                      · rw [Finset.mem_coe]; exact hy_mem
                      · intro h_in
                        rw [Set.mem_singleton_iff] at h_in
                        exact hxy_ne.symm h_in

                    have h_z_eq_y : z = y := h_inj h_z_mem_set h_y_mem_set h_cz_cy
                    exact h_z_ne_y h_z_eq_y

                  exact False.elim h_contradiction
              | inr h =>
                subst h
                have h_cz_cy : c z = c w := hzw_eq
                have h_cz_cx : c z = c x := by rw [hxy_eq, h_cz_cy]

                have h_z_ne_x : z ≠ x := by
                  intro h_eq
                  subst h_eq
                  have h_x_notin : z ∉ σ \ {z, w} := by simp
                  exact h_x_notin hz_in_sdiff

                have h_contradiction : False := by
                  have h_inj : ∀ {a b : T}, a ∈ (σ \ {w} : Set T) → b ∈ (σ \ {w} : Set T) → c a = c b → a = b := by
                    intros a b ha hb h_eq
                    exact h_inj_y ha hb h_eq

                  have h_z_mem_set : z ∈ (σ \ {w} : Set T) := by
                    rw [Set.mem_diff]
                    constructor
                    · rw [Finset.mem_coe]; exact hz_mem
                    · intro h_in
                      rw [Set.mem_singleton_iff] at h_in
                      have hz_notin_xw : z ∉ {x, w} := (Finset.mem_sdiff.mp hz_in_sdiff).2
                      simp at hz_notin_xw
                      exact hz_notin_xw.2 h_in

                  have h_x_mem_set : x ∈ (σ \ {w} : Set T) := by
                    rw [Set.mem_diff]
                    constructor
                    · rw [Finset.mem_coe]; exact hx_mem
                    · intro h_in
                      rw [Set.mem_singleton_iff] at h_in
                      simp [hxy_ne] at h_in

                  have h_z_eq_x : z = x := h_inj h_z_mem_set h_x_mem_set h_cz_cx
                  exact h_z_ne_x h_z_eq_x

                exact False.elim h_contradiction
          have hz_in_xy : z ∈ ({x, y} : Finset T) := by
            rw [←h_pair_eq]
            simp
          simp at hz_in_xy
          cases hz_in_xy with
          | inl h => left; rw [h]
          | inr h => right; rw [h]

        | odoor h_cell_σC h_door_σD z hz hτ_eq hD_eq =>
          exfalso
          rw [hτ_eq, hD_eq] at h_typed
          obtain ⟨h_cell_typed, h_i_notin, h_D_eq_typed⟩ := h_typed
          have h_C_diff : C \ (σ.image c) = {i} := by
            rw [h_C_eq]
            ext x
            simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · intro h
              exact h.1.resolve_right h.2
            · intro h_xi
              rw [h_xi]
              exact ⟨Or.inl rfl, h_i_notin⟩

          have h_z_notin_img : z ∉ σ.image c := by
            intro h_z_in_img
            have h_z_in_C : z ∈ C := by
              rw [h_C_eq]
              exact Finset.mem_insert_of_mem h_z_in_img
            exact hz h_z_in_C

          have h_z_ne_i : z ≠ i := by
            intro h_eq
            subst h_eq
            exact hz (by rw [h_C_eq]; exact Finset.mem_insert_self z (σ.image c))

          have h_typed_diff : (insert z C) \ (σ.image c) = {i} := by
            rw [h_D_eq_typed]
            ext x
            simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · intro h
              exact h.1.resolve_right h.2
            · intro h_xi
              rw [h_xi]
              exact ⟨Or.inl rfl, h_i_notin⟩

          have h_direct_diff : (insert z C) \ (σ.image c) = insert z (C \ (σ.image c)) := by
            ext x
            simp only [Finset.mem_sdiff, Finset.mem_insert]
            constructor
            · intro h
              cases h.1 with
              | inl h_eq =>
                left
                exact h_eq
              | inr h_in_C =>
                right
                exact ⟨h_in_C, h.2⟩
            · intro h
              cases h with
              | inl h_eq =>
                subst h_eq
                exact ⟨Or.inl rfl, h_z_notin_img⟩
              | inr h_in_diff =>
                exact ⟨Or.inr h_in_diff.1, h_in_diff.2⟩

          rw [h_C_diff] at h_direct_diff
          rw [h_direct_diff] at h_typed_diff
          have h_contradiction : {i} = insert z {i} := h_typed_diff.symm

          have h_z_notin_singleton : z ∉ ({i} : Finset I) := by
            simp [h_z_ne_i]
          have h_z_in_insert : z ∈ insert z {i} := Finset.mem_insert_self z {i}
          rw [←h_contradiction] at h_z_in_insert
          exact h_z_notin_singleton h_z_in_insert
      · intro h_mem
        simp [doors_NCroom]
        simp at h_mem
        cases h_mem with
        | inl h =>
          obtain ⟨h_τ, h_D⟩ := h
          rw [h_τ, h_D]
          exact ⟨h_typed_x, h_doorof_x⟩
        | inr h =>
          obtain ⟨h_τ, h_D⟩ := h
          rw [h_τ, h_D]
          exact ⟨h_typed_y, h_doorof_y⟩


lemma card_two_of_doors_NCroom (h0 : isRoom σ C) (h1 : isTypedNC c i σ C) : (doors_NCroom c σ C i).ncard = 2:=
  by
    obtain ⟨x,y,hx1,hx2⟩ := doors_of_NCroom h0 h1
    simp [hx1,hx2]

variable [Fintype T] [Fintype I]

variable (c) in
abbrev colorful := Finset.filter (fun (x : Finset T× Finset I) =>  IST.isColorful c x.1 x.2) univ

variable (c) in
abbrev dbcountingset (i : I):= Finset.filter (fun x : (Finset T× Finset I) × (Finset T× Finset I) => isTypedNC c i x.1.1 x.1.2 ∧ isDoorof x.1.1 x.1.2 x.2.1 x.2.2) univ


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

  have h_outside_door_τu_Du : isOutsideDoor τ_u D_u := outsidedoor_singleton i
  have h_typed_nc : isTypedNC c i τ_u D_u := by
    constructor
    · exact (NC_of_outsidedoor (c := c) h_outside_door_τu_Du).1
    constructor
    · simp only [τ_u, Finset.image_empty, Finset.not_mem_empty]
      exact Finset.not_mem_empty i
    · simp only [D_u, τ_u, Finset.image_empty, Finset.insert_empty]
      rfl

  have h_door_relation : isDoorof τ_u D_u σ_u C_u := by
    apply isDoorof.idoor
    · intro y
      use i
      constructor
      · simp only [C_u, Finset.mem_singleton]
      · intro x hx
        simp only [σ_u] at hx
        simp only [Finset.mem_singleton] at hx
        rw [hx]
        exact @Finset.le_max' T (IST i) Finset.univ y (Finset.mem_univ y)
    · exact h_outside_door_τu_Du.1
    · simp only [τ_u, Finset.not_mem_empty]
      exact Finset.not_mem_empty x_max_i
    · simp only [τ_u, σ_u, Finset.insert_empty]
      rfl
    · rfl

  use x_unique
  ext x_gen
  simp only [mem_filter, mem_univ, mem_singleton]

  constructor
  · intro h_in_filter
    simp only [mem_filter] at h_in_filter
    obtain ⟨h_in_db, h_outside⟩ := h_in_filter
    simp only [dbcountingset, mem_filter, mem_univ, true_and] at h_in_db
    obtain ⟨h_typed, h_door⟩ := h_in_db
    obtain ⟨h_is_door, h_empty⟩ := h_outside
    have h_empty_image : (x_gen.1.1).image c = ∅ := by
      rw [h_empty]
      exact Finset.image_empty c
    have h_x_gen_1_2_eq : x_gen.1.2 = {i} := by
      obtain ⟨_, h_i_notin, h_eq⟩ := h_typed
      rw [h_eq, h_empty_image]
      simp
    obtain ⟨_, h_D_singleton⟩ := outsidedoor_is_singleton ⟨h_is_door, h_empty⟩
    obtain ⟨j, h_D_eq⟩ := h_D_singleton

    have h_j_eq_i : j = i := by
      have h_eq_j : x_gen.1.2 = {j} := h_D_eq
      rw [h_x_gen_1_2_eq] at h_eq_j
      have : j ∈ {j} := Finset.mem_singleton_self j
      rw [←h_eq_j] at this
      exact Finset.eq_of_mem_singleton this

    cases h_door with
    | idoor h_cell_σC h_door_τD x h_x_notin h_insert_eq h_D_eq_C =>
      have h_σ_eq : x_gen.2.1 = {x} := by
        rw [←h_insert_eq, h_empty]
        rfl

      have h_x_eq_max : x = x_max_i := by
        have h_dom : ∀ y, y ≤[i] x := by
          intro y
          obtain ⟨j_dom, hj_in, hj_dom⟩ := h_cell_σC y
          rw [←h_D_eq_C, h_x_gen_1_2_eq] at hj_in
          simp at hj_in
          subst hj_in
          apply hj_dom
          rw [h_σ_eq]
          simp
        have h1 : x ≤[i] x_max_i := @Finset.le_max' T (IST i) Finset.univ x (Finset.mem_univ x)
        have h2 : x_max_i ≤[i] x := h_dom x_max_i
        exact @le_antisymm T (IST i).toPartialOrder x x_max_i h1 h2

      apply Prod.ext
      · apply Prod.ext
        · exact h_empty
        · rw [h_x_gen_1_2_eq]
      · apply Prod.ext
        · rw [h_σ_eq, h_x_eq_max]
        · rw [←h_D_eq_C, h_x_gen_1_2_eq]

    | odoor h_cell_σC h_door_τD j h_j_notin h_τ_eq h_D_insert =>

      exfalso
      have h_σ_empty : x_gen.2.1 = ∅ := by
        rw [←h_τ_eq, h_empty]
        rfl
      let h_door_constructed : isDoorof x_gen.1.1 x_gen.1.2 x_gen.2.1 x_gen.2.2 :=
        isDoorof.odoor h_cell_σC ⟨h_is_door.1, h_is_door.2⟩ j h_j_notin h_τ_eq h_D_insert
      have h_room : IST.isRoom x_gen.2.1 x_gen.2.2 := isRoom_of_Door h_door_constructed
      have h_σ_nonempty : x_gen.2.1.Nonempty := sigma_nonempty_of_room h_room
      rw [h_σ_empty] at h_σ_nonempty
      exact Finset.not_nonempty_empty h_σ_nonempty

  · intro h_eq
    rw [h_eq]
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · constructor
      · exact h_typed_nc
      · exact h_door_relation
    · exact h_outside_door_τu_Du

variable (c)

-- Use Lemme 2
lemma dbcount_outside_door_odd (i : I): Odd (filter (fun x => isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)).card  := by
  have cardone: (filter (fun x => isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)).card = 1 := by
    obtain ⟨x,hx⟩ := dbcount_outside_door' c i
    simp [hx]
  convert odd_one
omit [Inhabited T] in
lemma fiber_size_internal_door (c : T → I) (i : I) (y : Finset T × Finset I)
    (hy_internal : IST.isInternalDoor y.1 y.2) (hy_typed : isTypedNC c i y.1 y.2) :
    let s := filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)
    let f := fun (x : (Finset T × Finset I) × Finset T × Finset I) => x.1
    (filter (fun a => f a = y) s).card = 2 := by
  obtain ⟨σ₁, σ₂, C₁, C₂, h_ne, h_room₁, h_room₂, h_door₁, h_door₂, h_unique⟩ :=
    internal_door_two_rooms y.1 y.2 hy_internal
  let s := filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)
  let f := fun (x : (Finset T × Finset I) × Finset T × Finset I) => x.1
  let elem1 : (Finset T × Finset I) × Finset T × Finset I := (y, (σ₁, C₁))
  let elem2 : (Finset T × Finset I) × Finset T × Finset I := (y, (σ₂, C₂))
  have elem1_in_s : elem1 ∈ s := by
    simp only [elem1, s, mem_filter]
    constructor
    · simp only [dbcountingset, mem_filter, mem_univ, true_and]
      exact ⟨hy_typed, h_door₁⟩
    · intro h_outside
      exact (Finset.nonempty_iff_ne_empty.mp hy_internal.2) h_outside.2
  have elem2_in_s : elem2 ∈ s := by
    simp only [elem2, s, mem_filter]
    constructor
    · simp only [dbcountingset, mem_filter, mem_univ, true_and]
      exact ⟨hy_typed, h_door₂⟩
    · intro h_outside
      exact (Finset.nonempty_iff_ne_empty.mp hy_internal.2) h_outside.2
  have elems_distinct : elem1 ≠ elem2 := by
    intro h_eq
    injection h_eq with _ h_pair_eq
    exact h_ne h_pair_eq
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
      have h_x_form : x = (y, x.2) := Prod.ext_iff.mpr ⟨hx_eq, rfl⟩
      have h_room_x2 : IST.isRoom x.2.1 x.2.2 := isRoom_of_Door hx_door_x
      have hx_door_y : isDoorof y.1 y.2 x.2.1 x.2.2 :=
        hx_eq ▸ hx_door_x
      obtain h_case1 | h_case2 := h_unique x.2.1 x.2.2 h_room_x2 hx_door_y
      · simp only [mem_insert, mem_singleton]
        left
        rw [h_x_form]
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · exact h_case1.1
          · exact h_case1.2
      · simp only [mem_insert, mem_singleton]
        right
        rw [h_x_form]
        apply Prod.ext
        · rfl
        · apply Prod.ext
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

omit [Inhabited T] in
lemma dbcount_internal_door_even (i : I) : Even (filter (fun x => ¬ isOutsideDoor x.1.1 x.1.2) (dbcountingset c i)).card := by
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
    · unfold isInternalDoor
      constructor
      · cases hx_door with
        | idoor h0 h1 y h_notin h_eq h_D_eq_C => exact h1
        | odoor h0 h1 j h_notin h_eq h_D_eq => exact h1
      · by_contra h_empty
        have h_outside : isOutsideDoor x.1.1 x.1.2 := by
          constructor
          · cases hx_door with
            | idoor h0 h1 y h_notin h_eq h_D_eq_C => exact h1
            | odoor h0 h1 j h_notin h_eq h_D_eq => exact h1
          · exact Finset.not_nonempty_iff_eq_empty.mp h_empty
        exact hx_not_outside h_outside
    · exact hx_typed

  have fiber_size_two : ∀ y ∈ t, (filter (fun a=> f a = y) s).card = 2 := by
    intro y hy
    rw [mem_filter] at hy
    obtain ⟨_, hy_internal, hy_typed⟩ := hy
    exact fiber_size_internal_door c i y hy_internal hy_typed

  have counteq := Finset.card_eq_sum_card_fiberwise fs_in_t
  have sumeq := Finset.sum_const_nat fiber_size_two
  rw [sumeq] at counteq
  rw [counteq]
  simp only [even_two, Even.mul_left]

/- Easy -/
omit [Fintype T] [Fintype I] [Inhabited T] in
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
    obtain ⟨door1, door2, h_ne, h_doors_eq⟩ := doors_of_NCroom h0 h1
    have h_filter_eq : filter (fun (x : (Finset T× Finset I)× Finset T × Finset I) => x.2 = (σ,C)) (dbcountingset c i) =
                       {(door1, (σ,C)), (door2, (σ,C))} := by
      ext x
      constructor
      · intro hx
        rw [mem_filter] at hx
        obtain ⟨h_db, h_eq⟩ := hx
        rw [mem_filter] at h_db
        obtain ⟨_, h_typed, h_door⟩ := h_db
        have h_x_form : x = (x.1, (σ,C)) := by
          rw [Prod.ext_iff]
          exact ⟨rfl, h_eq⟩
        rw [h_x_form]
        simp
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

lemma typed_colorful_room_odd  (i : I): Odd (Finset.filter (fun (x: (Finset T× Finset I) × Finset T × Finset I) =>  isColorful c x.2.1 x.2.2) (dbcountingset c i)).card
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
