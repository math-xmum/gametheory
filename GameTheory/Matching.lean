import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

open List
set_option linter.deprecated false
set_option linter.unusedVariables false

section

variable {n : ℕ} [NeZero n]

-- Define the type for preferences
/-
 k ≻ l by i-th person if and only if the index of k is smaller than l
-/

structure Preferences (n : Nat) where
  prefs : Fin n → List (Fin n)
  valid : ∀ h,
    List.Nodup (prefs h) ∧
    (prefs h).length = n ∧
    (∀ x : Fin n, x ∈ prefs h)  -- new property


-- A matching is a bijection between Fin n
def Matching (n : ℕ) := Equiv (Fin n)  (Fin n)

-- w m stands for the Preferences of Women and Men.
variable {w m : Preferences n}

-- FW stands for free women
-- FM stands for free men
variable (FW FM : List (Fin n))

-- propos of Men to Free Womens.
def proposeMen (i : Fin n) : Fin n :=
  (m.prefs i).filter (· ∈ FW) |>.headI

-- the list of women have been proposed
-- It could be duplicated
def proposedWomen :=
  --(FM.map $ proposeMen (m:=m) FW ).dedup
  FM.map $ proposeMen (m:=m) FW

-- All proposals received by women i
def proposalsWomen (i : Fin n):=
  FM.filter (fun j => (proposeMen (m:=m) FW j) = i)

def rank (prefs : List (Fin n)) (x : Fin n) : ℕ :=
  indexOf x prefs

-- accept the prefered mem for women i
-- Chat GPT 4o suggest to use argmin
def acceptWomen (i : Fin n) :=
  let props := proposalsWomen (m:=m) FW FM i
  -- husband
  let H := props.argmin (rank (w.prefs i))
  match H with
  | none => (default: Fin n)
  | some h => h

lemma ne_non_poposals (h: i ∈ proposedWomen (m:=m) FW FM) : proposalsWomen (m:=m) FW FM i ≠ [] := by
  unfold proposalsWomen
  unfold proposedWomen at h
  simp only [ne_eq, filter_eq_nil, decide_eq_true_eq, not_forall, Classical.not_imp,
    Decidable.not_not]
  simp only [mem_map] at h
  simp [h]

variable {FW FM} in
lemma prop_in_FM : x ∈ proposalsWomen (m:=m) FW FM i → x ∈ FM := by
unfold proposalsWomen
simp only [mem_filter, decide_eq_true_eq, and_imp]
intro h1 _
exact h1

lemma not_some_none {α : Type*} (a : Option α) : (¬ ∃ x, a = some x) → a = none := by aesop

lemma exists_mem_argmin {α β : Type*}  [LinearOrder β] [DecidableRel fun (x1 x2 : β) => x1 < x2] (f : α → β) {l : List α} (hl : l ≠ []) : ∃ x, argmin f l = some x := by
  by_contra h
  replace h := not_some_none _ h
  replace h := List.argmin_eq_none.1 h
  exact hl h


-- if i is a free women, then it will pick a men in free mem
lemma mem_FM (h: i ∈ proposedWomen (m:=m) FW FM) : acceptWomen (w:=w) (m:=m) FW FM i ∈ FM := by
  unfold acceptWomen
  -- Break down the proposalsWomen into cases
  let props := proposalsWomen (m:=m) FW FM i
  have hne : props ≠ [] := ne_non_poposals (m:=m) FW FM h
  obtain ⟨m, hm⟩ := exists_mem_argmin (rank (w.prefs i)) hne
  simp [hm,prop_in_FM]
  exact prop_in_FM (List.argmin_mem hm)

-- newly married men
def marriedMen : List (Fin n) :=
  -- pW is the list of all free women who have been proposed
  let pW := proposedWomen (m:=m) FW FM
  pW.map $ acceptWomen (w:=w) (m:=m) FW FM


def restWomen :=
  let pw := proposedWomen (m:=m) FW FM
  FW.filter (¬ · ∈  pw)


def restMen :=
  let mm := marriedMen (w:=w) (m:=m) FW FM
  FM.filter (¬ · ∈  mm)

/- Helper lemmas for list properties -/
lemma list_length_pos_iff_ne_nil {α : Type*} (l : List α) :
  l.length > 0 ↔ l ≠ [] := by
  constructor
  · intro h
    intro h_nil
    subst h_nil
    simp at h
  · intro h
    cases l
    · contradiction
    · simp

lemma list_headI_mem {α : Type*} [Inhabited α] (l : List α) (h : l ≠ []) :
  l.headI ∈ l := by
  cases l
  · contradiction
  · simp [List.headI_cons]

omit [NeZero n] in
lemma prefs_valid_filter (h2 : Fin n) (x : Fin n) : x ∈ filter (fun x => x ∈ FW) (m.prefs h2) → x ∈ FW := by aesop

lemma headI_in_filtered_list {α : Type*} [Inhabited α] (l : List α) (h : l ≠ []) : l.headI ∈ l := by
  cases l with
  | nil => contradiction
  | cons hd tl => simp [List.headI, List.mem_cons_self]


/- If a woman is in the proposed list, she must be in FW -/
lemma proposedWomen_in_FW (FW_nonempty : FW ≠ []) :
  ∀ w ∈ proposedWomen (m:=m) FW FM, w ∈ FW := by
  unfold proposedWomen
  simp only [mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intros h2 h2_in_FM
  unfold proposeMen
  apply prefs_valid_filter
  apply headI_in_filtered_list
  -- Use FW_nonempty to get first element
  have first_elem := List.exists_mem_of_ne_nil FW FW_nonempty
  rcases first_elem with ⟨w, w_in_FW⟩
  -- Show filtered list contains w
  have valid_props := m.valid h2
  have w_in_prefs : w ∈ m.prefs h2 := valid_props.2.2 w
  have w_in_filtered : w ∈ filter (fun x => decide (x ∈ FW)) (m.prefs h2) := by
    apply mem_filter.mpr
    constructor
    · exact w_in_prefs
    · rw [decide_eq_true_iff]
      exact w_in_FW
  exact List.ne_nil_of_mem w_in_filtered

/- Length of filtered list property -/
lemma List.length_filter_lt_of_mem {α : Type*} [DecidableEq α] {l : List α}
    (p : α → Prop) [DecidablePred p] {x : α} (h_mem : x ∈ l) (h_p : p x) :
    (l.filter (fun y => ¬p y)).length < l.length := by
  induction l with
  | nil =>
    contradiction  -- x ∈ [] is false
  | cons hd tl ih =>
    simp at h_mem
    cases h_mem with
    | inl h_eq =>
      -- x = hd case
      subst h_eq  -- x is now hd
      simp [h_p]  -- simplify using the fact that p x (now p hd) is true
      -- Now we need to show: (filter (fun y => ¬p y) tl).length < tl.length + 1
      apply Nat.lt_succ_of_le
      -- (filter (fun y => ¬p y) tl).length ≤ tl.length
      exact List.length_filter_le _ tl
    | inr h_in_tl =>
      -- x ∈ tl case
      by_cases h_p_hd : p hd
      · -- p hd is true, so hd is filtered out
        simp [h_p_hd]
        apply Nat.lt_succ_of_le
        exact List.length_filter_le _ tl
      · -- p hd is false, so hd remains after filtering
        simp [h_p_hd]
        simp_all only [decide_not, length_filter_lt_length_iff_exists, Bool.not_eq_eq_eq_not, Bool.not_true,
          decide_eq_false_iff_not, Decidable.not_not, forall_const]

/- Instance to ensure Fin n has decidable equality -/
instance {n : ℕ} : DecidableEq (Fin n) := inferInstance

/- Key lemma: The number of remaining women decreases in each iteration -/
lemma FM_dec (h_FW : FW ≠ []) (h_FM : FM ≠ []) :
    (restWomen (m:=m) FW FM).length < FW.length := by
  -- Unfold the definition of restWomen
  unfold restWomen

  -- Since FM is non-empty, there exists at least one free man
  have ⟨man, h_man⟩ := List.exists_mem_of_ne_nil FM h_FM

  -- This man will propose to a woman
  let proposed_woman := proposeMen (m := m) FW man

  -- Show that this proposed_woman is in proposedWomen list
  have h_in_proposed : proposed_woman ∈ proposedWomen (m := m) FW FM := by
    unfold proposedWomen
    apply mem_map.mpr
    exact ⟨man, h_man, rfl⟩

  -- Show that proposed_woman is in FW
  have h_woman_in_FW : proposed_woman ∈ FW := by
    apply prefs_valid_filter
    apply headI_in_filtered_list
    -- Get properties from valid
    have valid_props := m.valid man
    -- Every Fin n is in preferences
    have all_fins_in_prefs := valid_props.2.2
    -- Get a woman from FW
    have ⟨first_woman, first_woman_in_FW⟩ := List.exists_mem_of_ne_nil FW h_FW
    -- This woman is in the preferences
    have first_in_prefs : first_woman ∈ m.prefs man := all_fins_in_prefs first_woman
    -- So she's in the filtered list
    have first_in_filtered : first_woman ∈ filter (fun x => decide (x ∈ FW)) (m.prefs man) := by
      apply mem_filter.mpr
      constructor
      · exact first_in_prefs
      · simp only [decide_eq_true_eq]
        exact first_woman_in_FW
    -- Therefore the filtered list is non-empty
    exact List.ne_nil_of_mem first_in_filtered

  -- Now we can use the length_filter_lt_of_mem lemma
  exact List.length_filter_lt_of_mem (fun x => x ∈ proposedWomen (m:=m) FW FM) h_woman_in_FW h_in_proposed


/- The full Gale-Shapley algorithm -/
-- The map from FW to FM
-- if i ∉ FW then return the default value
variable (w m) in
def gs_aux (FW FM : List (Fin n))
  : Fin n → Fin n := fun i =>
  if i ∉ FW then
    default
  else if FM = [] then
    -- Early termination condition: No more free men
    default
  else
    let pw := proposedWomen (m:=m) FW FM
    -- the set of proposed women
    if i ∈ pw then
      acceptWomen (w:=w) (m:=m) FW FM i
    else
      let FW' := restWomen (m:=m) FW FM
      let FM' := restMen (w:=w) (m:=m) FW FM
      gs_aux FW' FM' i
termination_by FW.length
decreasing_by
  have hFW_ne : FW ≠ [] := by
    -- build the non-emptiness from mem
    apply List.ne_nil_of_mem
    rename_i h h_1 h_2
    simp_all only [Decidable.not_not, pw]
    exact h

  -- now apply the lemma
  apply FM_dec
  exact hFW_ne
  simp_all only [Decidable.not_not, ne_eq, not_false_eq_true, pw]

-- (i, j) is a blocking pair if:
-- - i is a woman
-- - j is a man
-- - i prefers j over her current match
-- - j prefers i over his current match

def isBlockingPair (σ : Matching n) (w m : Preferences n) (i j : Fin n) : Prop :=
  let womanPartner := σ.toFun i
  let manPartner := σ.invFun j
  let womanPrefs := w.prefs i
  let manPrefs := m.prefs j
  -- both prefer each other over their assigned partner
  rank womanPrefs j < rank womanPrefs womanPartner ∧
  rank manPrefs i < rank manPrefs manPartner

def isStable (σ : Matching n) (w m : Preferences n) : Prop :=
  ∀ i j : Fin n, ¬ isBlockingPair σ w m i j

variable (w m) in
def gs : Fin n → Fin n:= gs_aux w m  (List.finRange n) (List.finRange n)

-- Auxiliary lemmas needed for the main theorem

-- Definition: j proposed to i during the algorithm
def proposed_to (w m : Preferences n) (j i : Fin n) : Prop :=
  ∃ (FW FM : List (Fin n)), i ∈ FW ∧ j ∈ FM ∧ proposeMen (m:=m) FW j = i


lemma filter_eq_singleton_or_nil {α : Type*} [DecidableEq α] (l : List α) (p : α → Prop) [DecidablePred p] (a : α) :
  (∀ x, p x ↔ x = a) → filter p l = if a ∈ l then [a] else [] := by
  intro h_p_iff
  induction l with
  | nil =>
    simp [filter_nil]

  | cons hd tl ih =>
    -- Case for (hd :: tl)
    simp [filter_cons]
    -- Split into cases based on whether p hd is true
    by_cases h_p_hd : p hd
    · -- Case: p hd is true
      -- From h_p_iff we know p hd ↔ hd = a, so hd = a
      have h_eq : hd = a := (h_p_iff hd).mp h_p_hd

      -- Use the equality to rewrite
      rw [h_eq] at *

      -- Now we need to simplify further
      have h_p_a : p a := by
        rw [h_p_iff a]

      -- Also, a ∈ (a :: tl) is clearly true
      have h_a_in : a ∈ (a :: tl) := by
        apply List.mem_cons_self
      rw [ih]
      -- Simplify the right side using a = a is true
      simp only [eq_self_iff_true, true_or, if_true]

      -- Handle the two cases separately
      by_cases h_a_in_tl : a ∈ tl
      ·sorry


    rw [ih]
    simp_all only [↓reduceIte]
    split
    next h => simp_all only [↓reduceIte, or_true]
    next
      h =>
      simp_all only [↓reduceIte, filter_eq_nil_iff, decide_eq_true_eq, or_false, nil_eq, ite_eq_right_iff,
        cons_ne_self, imp_false]
      apply Aesop.BuiltinRules.not_intro
      intro a_1
      subst a_1
      simp_all only [not_true_eq_false]



-- This captures the idea that men propose to women in preference order
lemma man_proposes_in_preference_order (m : Preferences n) (j i : Fin n) :
  i ∈ m.prefs j → proposed_to w m j i := by
  intro h_i_in_prefs
  -- Define the lists FW and FM
  let FW := [i]  -- We only need woman i to be free
  let FM := [j]  -- We only need man j to be free

  -- Show that this satisfies the proposed_to definition
  unfold proposed_to
  use FW, FM
  constructor
  · -- Show i ∈ FW
    simp [FW]

  constructor
  · -- Show j ∈ FM
    simp [FM]

  · -- Show proposeMen (m:=m) FW j = i
    unfold proposeMen

    -- The key insight: we need to show that i will be the head of the filtered list
    -- First, show that i is in the filtered list
    have h_i_in_filtered : i ∈ filter (fun x => x ∈ FW) (m.prefs j) := by
      apply mem_filter.mpr
      constructor
      · exact h_i_in_prefs
      · simp [FW]

    -- Now we need to show that i is the first element in the filtered list
    -- This requires showing that the filtered list is exactly [i]
    have h_filter_eq_singleton : filter (fun x => x ∈ FW) (m.prefs j) = [i] := by
     -- Use filter_eq_of_mem_unique lemma
     apply List.filter_eq_of_mem_unique
  -- First show that i is in the filtered list (we already have this)
  use h_i_in_filtered
  -- Then show that any element in the filtered list must be i
  intros x hx
  -- If x is in the filtered list, then x ∈ FW
  have x_in_FW : x ∈ FW := by
    obtain ⟨x_in_prefs, x_decide⟩ := mem_filter.mp hx
    simp only [decide_eq_true_iff] at x_decide
    exact x_decide
  -- But FW = [i], so x = i
  simp [FW] at x_in_FW
  exact x_in_FW

-- Finally, show that headI of [i] is i
rw [h_filter_eq_singleton]
simp [List.headI]
    -- Finally, show that headI of [i] is i
    rw [h_filter_eq_singleton]
    simp [List.headI]


-- Now we can use this more general lemma to prove our original lemma
lemma proposed_to_if_prefers (w m : Preferences n) (j i wj : Fin n)
    (h : rank (m.prefs j) i < rank (m.prefs j) wj) : proposed_to w m j i := by
  -- First, we need to know that i is in j's preference list
  have i_in_prefs : i ∈ m.prefs j := by
    -- This follows from the definition of rank
    -- If i has a rank in j's preferences, it must be in the list
    have valid_prefs := m.valid j
    exact valid_prefs.2.2 i

  -- Now we can apply our auxiliary lemma
  apply man_proposes_in_preference_order
  exact i_in_prefs


-- Definition: i rejected j during the algorithm
def rejected (w m : Preferences n) (i j : Fin n) : Prop :=
  ∃ (FW FM : List (Fin n)), i ∈ FW ∧ j ∈ FM ∧ proposeMen (m:=m) FW j = i ∧ acceptWomen (w:=w) (m:=m) FW FM i ≠ j

-- Lemma: If j proposed to i but they're not matched, i rejected j
lemma proposed_but_not_matched (w m : Preferences n) (i j : Fin n)
    (h_proposed : proposed_to w m j i) (h_not_matched : gs w m i ≠ j) :
    rejected w m i j := by
 unfold rejected
 sorry

-- Lemma: If i rejected j for mi, then i prefers mi to j
lemma rejection_implies_better_match (w m : Preferences n) (i j mi : Fin n)
    (h_rejected : rejected w m i j) (h_matched_mi : gs w m i = mi) :
    rank (w.prefs i) mi < rank (w.prefs i) j := by
    sorry


-- Lemma: If woman i is matched with man mi, then i prefers mi to any man j who proposed to i
-- but was rejected
lemma final_matching_preference (w m : Preferences n) (i mi j : Fin n)
    (h_matched : gs w m i = mi)
    (h_proposed_rejected : proposed_to w m j i ∧ gs w m i ≠ j) :
    rank (w.prefs i) mi < rank (w.prefs i) j :=
by
  -- Extract the fact that j proposed to i but was rejected
  have h_j_proposed := h_proposed_rejected.1
  have h_j_rejected := h_proposed_rejected.2

  -- If j proposed to i but i is not matched with j, then i must have rejected j
  have h_rejected : rejected w m i j := by
    apply proposed_but_not_matched w m i j
    · exact h_j_proposed
    · exact h_j_rejected

  -- If i rejected j, then i prefers her final match mi to j
  -- This follows from how the algorithm works - women always accept the best proposal so far
  apply rejection_implies_better_match w m i j mi
  · exact h_rejected
  · exact h_matched

-- We need to define the inverse function for the matching
variable (w m) in
def gs_inv (j : Fin n) : Fin n :=
  -- Find a woman i such that gs w m i = j
  match List.find? (fun i => gs w m i = j) (List.finRange n) with
  | some i => i  -- Found a woman i that maps to j
  | none => default  -- Fallback in case no woman maps to j

-- We need to prove that gs and gs_inv form a bijection
lemma gs_left_inv (w m : Preferences n) :
  ∀ i : Fin n, gs_inv w m (gs w m i) = i :=
by
  intro i
  unfold gs_inv
  -- Need to show that List.find? finds i
  sorry

lemma gs_right_inv (w m : Preferences n) :
  ∀ i : Fin n, gs w m (gs_inv w m i) = i :=
by
  intro i
  unfold gs_inv
  -- Split into cases based on whether i is in the range of gs
  sorry



-- Main theorem: The Gale-Shapley algorithm produces a stable matching
lemma no_blocking_pairs (w m : Preferences n) (i j : Fin n) :
  ¬ isBlockingPair (Equiv.mk (gs w m) (gs_inv w m) (gs_left_inv w m) (gs_right_inv w m)) w m i j := by
  -- Let's name some important variables for clarity
  let σ := Equiv.mk (gs w m) (gs_inv w m) (gs_left_inv w m) (gs_right_inv w m)
  let mi := σ.toFun i  -- man matched with woman i
  let wj := σ.invFun j -- woman matched with man j

  -- Assume for contradiction that (i, j) is a blocking pair
  intro h_blocking

  -- Extract the conditions from the blocking pair definition
  have h_i_prefers_j : rank (w.prefs i) j < rank (w.prefs i) mi := h_blocking.1
  have h_j_prefers_i : rank (m.prefs j) i < rank (m.prefs j) wj := h_blocking.2

  -- First, we establish that if j prefers i to his current match,
  -- then j must have proposed to i during the algorithm
  have h_j_proposed_to_i : proposed_to w m j i := by
    apply proposed_to_if_prefers w m j i wj
    exact h_j_prefers_i

  -- Now, if j proposed to i, but i is not matched with j,
  -- then i must have rejected j at some point
  have h_i_not_matched_with_j : gs w m i ≠ j := by
    intro h_matched
    -- If i is matched with j, then mi = j
    have h_mi_eq_j : mi = j := h_matched
    -- But this contradicts that i prefers j over mi
    rw [h_mi_eq_j] at h_i_prefers_j
    -- This creates a contradiction - i cannot prefer j over j
    exact lt_irrefl (rank (w.prefs i) j) h_i_prefers_j

  -- If j proposed to i but they're not matched, i must have rejected j
  have h_i_rejected_j : rejected w m i j := by
    apply proposed_but_not_matched w m i j
    · exact h_j_proposed_to_i
    · exact h_i_not_matched_with_j

  -- If i rejected j, i must prefer her current match mi over j
  have h_i_prefers_mi : rank (w.prefs i) mi < rank (w.prefs i) j := by
    apply rejection_implies_better_match w m i j mi
    · exact h_i_rejected_j
    · rfl  -- gs w m i = mi by definition

  -- But this directly contradicts our assumption that i prefers j over mi
  exact not_lt_of_gt h_i_prefers_mi h_i_prefers_j



end

section EX

abbrev n : ℕ := 4

abbrev w : Preferences n :=
{
  prefs := ![
    [1,2,0,3],
    [0,3,2,1],
    [0,2,3,1],
    [0,2,3,1]]
  valid := by decide
}

abbrev m : Preferences n :=
{
  prefs := ![
    [3,0,1,2],
    [0,1,3,2],
    [0,2,3,1],
    [1,2,3,0]]
  valid := by decide
}

#print w
#print m


#eval! proposeMen (m:=m) (finRange n)
#eval! proposedWomen (m:=m) (finRange n) (finRange n)
#eval! proposalsWomen (m:=m) (finRange n) (finRange n)


#eval! proposeMen (m:=m) [1,2]
#eval! acceptWomen (w:=w) (m:=m) (finRange n) (finRange n)


#eval! (finRange n).map $ gs w m



end EX
