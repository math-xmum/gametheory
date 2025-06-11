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

-- Key lemma: elements in M_set are not in τ
lemma M_set_disjoint_from_tau [Fintype T] (τ : Finset T) (D : Finset I) (i : I) (h_nonempty : τ.Nonempty)
    (h_door : IST.isDoor τ D) (x : T) (hx : x ∈ M_set τ D i h_nonempty) : x ∉ τ := by
  sorry

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

-- Sublemma 3.2: τ + x is dominant with respect to D iff x = m_i for some i ∈ {a,b} with M_i ≠ ∅
lemma sublemma_3_2 [Fintype T] (τ : Finset T) (D : Finset I) (x : T)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty) (h_not_mem : x ∉ τ)
    (a b : I) (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (h_eq : mini h_nonempty a = mini h_nonempty b) :
    IST.isDominant (insert x τ) D ↔
    (∃ i ∈ ({a, b} : Finset I), (M_set τ D i h_nonempty).Nonempty ∧
     is_maximal_in_M_set τ D i h_nonempty x) := by
      sorry

/- Lemma 3-/
theorem internal_door_two_rooms [Fintype T] (τ : Finset T) (D : Finset I)
    (h_int_door : IST.isInternalDoor τ D) :
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
section useless_lemma
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
end useless_lemma

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
/-
Lemma 5
-/


omit [Inhabited T] in
-- Helper lemma: if two finite sets with equal inserts have different insert elements not in the original sets, then they are equal
lemma finset_insert_eq_insert_of_disjoint {α : Type*} [DecidableEq α] (s t : Finset α) (a b : α)
    (h_eq : insert a s = insert b t) (h_a_notin : a ∉ s) (h_b_notin : b ∉ t) (h_a_ne_b : a ≠ b) :
    a ∈ t ∧ b ∈ s ∧ s = insert b (t \ {a}) ∧ t = insert a (s \ {b}) := by
  have h_a_in_t : a ∈ t := by
    have : a ∈ insert b t := by rw [←h_eq]; exact Finset.mem_insert_self a s
    cases Finset.mem_insert.mp this with
    | inl h => exact absurd h h_a_ne_b
    | inr h => exact h
  have h_b_in_s : b ∈ s := by
    have : b ∈ insert a s := by rw [h_eq]; exact Finset.mem_insert_self b t
    cases Finset.mem_insert.mp this with
    | inl h => exact absurd h.symm h_a_ne_b
    | inr h => exact h
  constructor; exact h_a_in_t
  constructor; exact h_b_in_s
  constructor
  · ext x
    constructor
    · intro hx_in_s
      by_cases h_x_eq_b : x = b
      · rw [h_x_eq_b]; exact Finset.mem_insert_self b (t \ {a})
      · have hx_in_insert_a_s : x ∈ insert a s := Finset.mem_insert_of_mem hx_in_s
        rw [h_eq] at hx_in_insert_a_s
        cases Finset.mem_insert.mp hx_in_insert_a_s with
        | inl h_x_eq_b => rw [h_x_eq_b]; exact Finset.mem_insert_self b (t \ {a})
        | inr hx_in_t =>
          apply Finset.mem_insert_of_mem
          rw [Finset.mem_sdiff]
          constructor; exact hx_in_t
          rw [Finset.mem_singleton]
          intro h_x_eq_a
          rw [h_x_eq_a] at hx_in_s
          exact h_a_notin hx_in_s
    · intro hx_in_insert
      cases Finset.mem_insert.mp hx_in_insert with
      | inl h_x_eq_b => rw [h_x_eq_b]; exact h_b_in_s
      | inr hx_in_diff =>
        rw [Finset.mem_sdiff] at hx_in_diff
        have hx_in_t := hx_in_diff.1
        have hx_ne_a := by rw [Finset.mem_singleton] at hx_in_diff; exact hx_in_diff.2
        have hx_in_insert_b_t : x ∈ insert b t := Finset.mem_insert_of_mem hx_in_t
        rw [←h_eq] at hx_in_insert_b_t
        cases Finset.mem_insert.mp hx_in_insert_b_t with
        | inl h_x_eq_a => exact absurd h_x_eq_a hx_ne_a
        | inr hx_in_s => exact hx_in_s
  · ext x
    constructor
    · intro hx_in_t
      by_cases h_x_eq_a : x = a
      · rw [h_x_eq_a]; exact Finset.mem_insert_self a (s \ {b})
      · have hx_in_insert_b_t : x ∈ insert b t := Finset.mem_insert_of_mem hx_in_t
        rw [←h_eq] at hx_in_insert_b_t
        cases Finset.mem_insert.mp hx_in_insert_b_t with
        | inl h_x_eq_a => rw [h_x_eq_a]; exact Finset.mem_insert_self a (s \ {b})
        | inr hx_in_s =>
          apply Finset.mem_insert_of_mem
          rw [Finset.mem_sdiff]
          constructor; exact hx_in_s
          rw [Finset.mem_singleton]
          intro h_x_eq_b
          rw [h_x_eq_b] at hx_in_t
          exact h_b_notin hx_in_t
    · intro hx_in_insert
      cases Finset.mem_insert.mp hx_in_insert with
      | inl h_x_eq_a => rw [h_x_eq_a]; exact h_a_in_t
      | inr hx_in_diff =>
        rw [Finset.mem_sdiff] at hx_in_diff
        have hx_in_s := hx_in_diff.1
        have hx_ne_b := by rw [Finset.mem_singleton] at hx_in_diff; exact hx_in_diff.2
        have hx_in_insert_a_s : x ∈ insert a s := Finset.mem_insert_of_mem hx_in_s
        rw [h_eq] at hx_in_insert_a_s
        cases Finset.mem_insert.mp hx_in_insert_a_s with
        | inl h_x_eq_b => exact absurd h_x_eq_b hx_ne_b
        | inr hx_in_t => exact hx_in_t

-- Helper lemma for the specific case in NC_or_C_of_door

omit [Inhabited T] IST [DecidableEq T] in
lemma helper_for_insert_eq {σ : Finset T} {C : Finset I} {i j : I}
    (h_eq : insert j C = insert i (σ.image c))
    (h_i_notin : i ∉ σ.image c)
    (h_j_notin : j ∉ C)
    (h_i_ne_j : i ≠ j) :
    i ∈ C ∧ j ∈ σ.image c ∧ σ.image c = insert j (C \ {i}) ∧ C = insert i (σ.image c \ {j}) :=
  finset_insert_eq_insert_of_disjoint (σ.image c) C i j h_eq.symm h_i_notin h_j_notin h_i_ne_j


omit [Inhabited T] in
lemma NC_or_C_of_door (h1 : isTypedNC c i τ D) (h2 : isDoorof τ D σ C) : isTypedNC c i σ C ∨ isColorful c σ C := by
     sorry





omit [Inhabited T] in
lemma NCtype_of_door (h1 : isTypedNC c i τ D) (_ : isDoorof τ D σ C) (_ : isTypedNC c i σ C) : isTypedNC c i τ D := h1

/-
Lemma 6 : The version in paper is incorrect-/
lemma card_of_NCcell (h : isNearlyColorful c σ D) : #σ = #(image c σ) ∨  #σ + 1 = #(image c σ) := by
  have h_image_le : (σ.image c).card ≤ σ.card := Finset.card_image_le
  have h_contra : σ.card + 1 ≠ (σ.image c).card := by --为啥这里能推出不等来
    intro h_eq
    linarith [h_image_le, h_eq]

  by_cases h : σ.card = (σ.image c).card
  · left
    exact h
  · right
    sorry


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

  -- Establish that the constructed elements satisfy the required properties
  have h_outside_door_τu_Du : isOutsideDoor τ_u D_u := outsidedoor_singleton i
  have h_typed_nc : isTypedNC c i τ_u D_u := by
    -- Need to prove isTypedNC c i τ_u D_u
    constructor
    · -- Prove isCell τ_u D_u
      exact (NC_of_outsidedoor (c := c) h_outside_door_τu_Du).1
    constructor
    · -- Prove i ∉ τ_u.image c = i ∉ ∅
      simp only [τ_u, Finset.image_empty, Finset.not_mem_empty]
      exact Finset.not_mem_empty i
    · -- Prove D_u = insert i (τ_u.image c) = {i} = insert i ∅
      simp only [D_u, τ_u, Finset.image_empty, Finset.insert_empty]
      rfl

  have h_door_relation : isDoorof τ_u D_u σ_u C_u := by
    -- Need to prove the door relationship
    apply isDoorof.idoor
    · -- Prove isCell σ_u C_u (already proven above, can reuse)
      intro y
      use i
      constructor
      · simp only [C_u, Finset.mem_singleton]
      · intro x hx
        simp only [σ_u] at hx
        simp only [Finset.mem_singleton] at hx
        rw [hx]
        exact @Finset.le_max' T (IST i) Finset.univ y (Finset.mem_univ y)
    · -- Prove isDoor τ_u D_u
      exact h_outside_door_τu_Du.1
    · -- Prove x_max_i ∉ τ_u
      simp only [τ_u, Finset.not_mem_empty]
      exact Finset.not_mem_empty x_max_i
    · -- Prove insert x_max_i τ_u = σ_u
      simp only [τ_u, σ_u, Finset.insert_empty]
      rfl
    · -- Prove D_u = C_u
      rfl

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

      -- We need to show x = x_max_i
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
    simp only [elem1, elem2]
    intro h_eq
    have : (σ₁, C₁) = (σ₂, C₂) := by
      rw [Prod.ext_iff] at h_eq
      exact h_eq.2
    have : σ₁ = σ₂ := by
      rw [Prod.ext_iff] at this
      exact this.1
    exact h_ne this
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

