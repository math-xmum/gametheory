import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

open List

section

variable {n : ℕ} [NeZero n]

-- Define the type for preferences
/-
 k ≻ l by i-th person if and only if the index of k is smaller than l
-/
structure Preferences (n : ℕ) :=
  prefs : Fin n → List (Fin n)
  -- the pref is a
  valid : ∀ i, (prefs i).Nodup ∧ (prefs i).length = n
  --valid : ∀ i, (prefs i) ∈ (List.finRange n).permutations'

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

lemma mem_FM_aux : ∀ k ∈ proposalsWomen (m:=m) FW FM i, k ∈ FM := by
  unfold proposalsWomen
  simp only [mem_filter, decide_eq_true_eq, and_imp]
  intro k hk _
  exact hk

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

lemma FM_dec (h : FW ≠ []): (restWomen (m:=m) FW FM).length < FW.length := by sorry

-- The map from FW to FM
-- if i ∉ FW then return the default value
variable (w m) in
def gs_aux (FW FM : List (Fin n))
  : Fin n → Fin n := fun i =>
  if i ∉ FW then
    default
  else
    let pw := proposedWomen (m:=m) FW FM
    -- the set of proposed women
    if i ∈ pw then
      acceptWomen (w:=w) (m:=m) FW FM i
    else
      let FW' := restWomen (m:=m) FW FM
      let FM' := restMen (w:=w) (m:=m) FW FM
      --gs_aux _ _ w m FW' FM' i
      gs_aux FW' FM' i
termination_by FW.length
decreasing_by
  sorry

variable (w m) in
def gs : Fin n → Fin n:= gs_aux w m  (List.finRange n) (List.finRange n)

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
