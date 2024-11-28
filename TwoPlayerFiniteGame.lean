import Mathlib

--open Classical

/-
We only have two players.
We attempt to make everything computable

-/

section

class Doubleton (α : Type*) [DecidableEq α]:=
  x : α
  y : α
  x_ne_y : x ≠ y
  x_or_y : ∀ a : α, a=x ∨ a=y



namespace Doubleton
variable {α : Type*} [DecidableEq α] [Doubleton α]

lemma x_or_y_def : ∀ a : α, a= Doubleton.x ∨ a = Doubleton.y := Doubleton.x_or_y

lemma x_ne_y_def : (Doubleton.x :α) ≠  Doubleton.y := Doubleton.x_ne_y

def other (a : α) : α := if a = (Doubleton.x : α) then Doubleton.y else Doubleton.x

#print other
instance fin2.doubleton : Doubleton (Fin 2) where
  x := 0
  y := 1
  x_ne_y := by decide
  x_or_y := by sorry

#eval! Doubleton.other (0 : Fin 2)
#eval! Doubleton.other (1: Fin 2)

end Doubleton

end

section

/- α will be the set of all status
A game will be defined on a subset of α
There will be a master node called default
which represents the begining of the game.
-/

variable {players : Type*} [DecidableEq players] {α: Type*} [DecidableEq α] [ihb : Inhabited α] [Fintype α]

/- Let p denote a directed graph where each node have a uniqe arrow pointed out -/
variable (p : α → α)

/-Except the default element, no elements are in loops -/
class GameSpace where
  default_self : p default = default
  no_loop : ∀ (x :α), ∀ (n:ℕ), x ≠ (default :α) → p^[n+1] x ≠ x

variable [GameSpace p]

/- A subgame assocated to a node x is a status space consists of
all nodes connected to a given node -/

/- children of a given node -/
def children (x : α) : Finset α := Finset.filter (p · = x) Finset.univ


def children_list [LinearOrder α] (x : α) : List α := Finset.sort (· ≤ · ) (children p x)

/- Internodes are images of p -/
def internodes: Finset α:= Finset.image p Finset.univ

/- Leaves are non-inner nodes -/
def leaves : Finset α := Finset.filter (· ∉ internodes p) Finset.univ

lemma mem_leaves_iff_no_children {x :α} : x ∈ leaves p ↔ children p x  = {} := sorry

def subgame_aux (C : Finset α) :=
  let Y := C ∪ Finset.filter (p · ∈ C) Finset.univ
  if h : Y = C then
    Y
  else
    subgame_aux Y
termination_by Cᶜ.card
decreasing_by
  sorry

def subgame [GameSpace p] (x : α) := subgame_aux p ({x}: Finset α)

lemma subgame_def  (x : α) : y ∈ subgame p x ↔ ∃ n, p^[n] y = x := sorry

lemma subgame_mem_self (x :α) : x ∈ subgame p x := by sorry

lemma subgame_sub[igs : GameSpace p] {x y : α} (hy : p y = x) : subgame p y ⊆ subgame p x:= by sorry


lemma subgame_neq [igs : GameSpace p] {x y : α} (hy : p y = x) : subgame p y ≠  subgame p x:= by sorry

lemma subgame_decrease [igs : GameSpace p] {x y : α} (hy : p y = x) : (subgame p y).card < (subgame p x).card := by sorry


lemma internode_of_not_leaf :  x ∉ leaves p  → x ∈ internodes p := sorry

lemma subgame_leaf (hx : x ∈ leaves p) : subgame p x = {x} := sorry

variable (σ : α → α)

class Strategy where
  prop : ∀ x ∈ internodes p,  p (σ x) = x

/- Sub strategy -/
structure SStrategy [GameSpace p] (x : α) where
  s : (subgame p x) → α
  prop : ∀ x :(subgame p x), ↑x ∈ internodes p →  p (s x) = x

/-
instance SStrategy.funlike : FunLike (SStrategy p x) (subgame p x) α := {
  coe := fun σ =>
    fun n =>  σ.s n
  coe_injective' := sorry
}
-/

instance SStrategy.funlike' : FunLike (SStrategy p x) α α := {
  coe := fun σ =>
    fun n =>  if h : n ∈ (subgame p x) then σ.s ⟨n,h⟩
      else default
  coe_injective' := sorry
}


/-  R assign player of the node,
    if the node "x" is a leaf, it means the player R x win otherwise it is R x 's turn to pick the next step. -/

variable  (R : α → players)


namespace SStrategy

variable [GameSpace p] {x : α} (σ γ : SStrategy p x)


-- Make p as an implicite variable
variable {p}

def piecewise (R : α → players) (a : players): SStrategy p x where
  s := {n: subgame p x | R n = a}.piecewise σ.s γ.s
  prop := sorry

-- restriction of a SStrategy to subgame
def res (σ : SStrategy p x) (hxy : p y = x) :  SStrategy p y where
  s := fun n => σ.s ⟨n.1,subgame_sub _ hxy n.2 ⟩
  prop := sorry


-- extend of a SStrategy to subgame by move x to y
def extend (σ : SStrategy p y) (hxy : p y = x) :  SStrategy p x where
  s := fun n => if hh : n.1 ∈ subgame p y then σ n else ↑y
  prop := sorry

def singleton  (hx : x ∈ leaves p) : SStrategy p x where
  s := fun n => n.1
  prop := sorry

end SStrategy



namespace GameSpace

--variable {α: Type*} [DecidableEq α] [hia : Inhabited α] [Fintype α] {p : α → α} (σ : α → α)


/- The outcome starts from x -/
variable {p} in
def outcome  [igs: GameSpace p] (x : α) (σ : SStrategy p x)  : α :=
  if h: x ∈ leaves p then
    x
  else
    have hx : x ∈ internodes p := sorry
    have hxy : p (σ x) = x := sorry -- use  σ.prop
    have σ' : SStrategy p (σ x):= σ.res hxy
    outcome (σ x) σ'
termination_by (subgame p x).card
decreasing_by
  exact subgame_decrease p hxy

variable [Doubleton players] [LinearOrder α] (a : players) (R : α → players)

def gen_sstrategy_aux  [Doubleton players] [LinearOrder α]  (x : α) (c : List α) : Option (SStrategy p x) :=
  if h : x ∈ leaves p then
    if h1 : a = R x then
      SStrategy.singleton h
    else none
  else
    /-
      If a is the player of the current node x then
        the there is a dominant strategy for a if and only if
        there is a dominant strategy for its children
      else
        the there is a dominant strategy for a if and only if
        there is a dominant strategy for all its children
    -/
    if h1 : a = R x then
      match c with
      | [] => none
      | y :: tail =>
        /-
        the following condition always holds, but we need it for
        the completeness of the program
        -/
        if h: p y = x then
          /-
            If for the child y of x, there is no dominate strategy then consider the tail
            if there is, then extend the dominate strategy to
            subgame p x by let the strategy chose to move from x to y.
          -/
          match gen_sstrategy_aux y (children_list p y)with
          | none => gen_sstrategy_aux x tail
          | some γ => some (γ.extend h)
        else none
    else
      match c with
      | [] => none
      | y :: tail =>
        if h: p y = x then
          match gen_sstrategy_aux y (children_list p y)with
          | none => none
          | some γ => match tail with
            | [] => some (γ.extend h)
            | z :: ttail =>
              match gen_sstrategy_aux x (z :: ttail) with
              | none => none
              | some _ => some (γ.extend h)
        else
          none
termination_by ((subgame p x).card, c.length)
decreasing_by
  · left
    exact subgame_decrease p h
  · right; simp
  · left ; exact subgame_decrease p h
  · right; simp


def gen_sstrategy [Doubleton players] [LinearOrder α]  (x : α) : Option (SStrategy p x) :=
  gen_sstrategy_aux p a R x (children_list p x)

/-
A strategy σ is dominant stragegy of "a" if for any valid move of other players, "a" is always the winner
of the game
-/
variable {p} in
def dominant_strategy (σ : SStrategy p x) := ∀ (γ: SStrategy p x), R (outcome x (σ.piecewise γ R a )) = a


lemma gen_strategy_is_dominant  {σ : SStrategy p x} (h : gen_sstrategy p a R x = some σ) : dominant_strategy a R σ := sorry



theorem determined [Doubleton players] :
  ∃ a : players,
  ∃ (σ : SStrategy p x), dominant_strategy a R σ := sorry


end GameSpace

end
