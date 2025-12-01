import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

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
