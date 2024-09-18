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
  valid : ∀ i, (prefs i) ∈ (List.finRange n).permutations

-- A matching is a bijection between Fin n
def Matching (n : ℕ) := Equiv (Fin n)  (Fin n)

-- w m stands for the Preferences of Women and Men.
variable {w m : Preferences n}

-- FW stands for free women
-- FM stands for free men
variable (FW FM : List (Fin n))

-- propos of Men to Free Womens.
def proposeMen (i : Fin n) : Fin n :=
  m.prefs i |>.filter (· ∈ FW) |>.headI

-- the list of women have been proposed
def proposedWomen :=
  FM.map $ proposeMen (m:=m) FW

-- All proposals recived by women i
def proposalsWomen (i : Fin n):=
  FM.filter (proposeMen (m:=m) FW · = i)

def rank (prefs : List (Fin n)) (x : Fin n) : ℕ :=
  indexOf x prefs
  
-- accept the prefered mem for women i
-- Chat GPT 4o sugguest to use argmin
def acceptWomen (i : Fin n) :=
  let props := proposalsWomen (m:=m) FW FM i
  -- husbund
  let H := props.argmin $ rank (w.prefs i)
  match H with
  | none => (default: Fin n)
  | some h => h

-- if i is a free women, then it will pick a men in free mem
lemma mem_FM (h: i ∈ FW) : acceptWomen (w:=w) (m:=m) FW FM i ∈ FM := by sorry

-- newly married men
def marriedMen : List (Fin n) := FW.map $ acceptWomen (w:=w) (m:=m) FW FM


def restWomen :=
  let pw := proposedWomen (m:=m) FW FM
  FW.filter (¬ · ∈  pw)


def restMen :=
  let mm := marriedMen (w:=w) (m:=m) FW FM
  FW.filter (¬ · ∈  mm)

lemma FM_dec (h : 0<FW.length ): (restWomen (m:=m) FW FM).length < FW.length := by sorry

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
  simp_wf
  sorry

variable (w m) in
def gs : Fin n → Fin n:= gs_aux w m  (List.finRange n) (List.finRange n)

end

section EX

abbrev n : ℕ := 3

abbrev w : Preferences n :=
{
  prefs := fun i => match i with
    | 0 => [1,2,0]
    | 1 => [0,2,1]
    | 2 => [0,2,1]
  valid := by decide
}

abbrev m : Preferences n :=
{
  prefs := fun i => match i with
    | 0 => [0,1,2]
    | 1 => [0,2,1]
    | 2 => [1,2,0]
  valid := by decide
}

#eval (finRange n).map $ gs w m


end EX