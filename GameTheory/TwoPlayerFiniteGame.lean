import Mathlib

--open Classical

/-
We only have two players
-/

section

class Doubleton (α : Type*) [DecidableEq α]:=
  x : α
  y : α
  x_ne_y : x ≠ y
  x_or_y : ∀ a : α, a=x ∨ a=y

namespace Doubleton
variable {α : Type*} [DecidableEq α] [Doubleton α ]

lemma x_or_y_def : ∀ a : α, a= Doubleton.x ∨ a = Doubleton.y := Doubleton.x_or_y

lemma x_ne_y_def : (Doubleton.x :α) ≠  Doubleton.y := Doubleton.x_ne_y

end Doubleton

end

noncomputable section

/- α will be the set of all status
A game will be defined on a subset of α
There will be a master node called default
which represents the begining of the game.
-/

variable {players : Type*} {α: Type*} [DecidableEq α] [Inhabited α]

/- Let p denote a directed graph where each node have a uniqe arrow pointed out -/
variable (p : α → α)

/-Except the default element, no elements are in loops -/
structure Noloop where
  no_loop : ∀ (x :α), ∀ (n:ℕ), x ≠ (default :α) → p^[n+1] x ≠ x

/-  R assign player of the node,
    if the node "x" is a leaf, it means the player R x win otherwise it is R x 's turn to pick the next step. -/
variable  (R : α → players)

/- A subgame assocated to a node x is a status space consists of
all nodes connected to a given node -/
def subgame (x : α) := {y : α | ∃ n, p^[n] y = x}


variable (players : Type*) (α: Type*)
structure PerfectInformationGame :=
  /- Here p is a directed graph
    here p representat the parent of a node
    R assign player of the node,
    if the node "x" is a leaf, it means the player R x win otherwise it is R x 's turn to pick the next step. -/
  p : α → α
  R : α → players
  /- The root of the Game -/
  root : α
  /- This is the set of all relevent nodes -/
  nodes : Finset α
  root_mem_nodes : root ∈ nodes
  /- no loop form the child nodes, here f^n denote the iteration of f ntimes -/
  no_loop : ∀ x ∈ nodes, ∀ n:ℕ, x ≠ root → p^[n+1] x ≠ x
  /- connected to root -/
  connect_root : ∀ x∈ nodes, ∃ n:ℕ, p^[n] x = root


/-
A map  σ : α → α is a strategy of (g : PerfectInformationGame)
such that
for each x ∈ internodes,
  σ x ∈ nodes ∧ p (σ x) = x
  i.e. σ x is in the relevent nodes having x as its parent.
-/
/-
variable {α} {players} in
class Strategy' (g : PerfectInformationGame players α)
(σ : α → α) where
  prop : ∀ x ∈ g.nodes, σ x ∈ g.nodes ∧ g.p (σ x) = x
-/


variable {α} {players} in
def Strategy (g : PerfectInformationGame players α)
(σ : α → α) :=  ∀ (x), x ∈ g.nodes →  σ x ∈ g.nodes ∧ g.p (σ x) = x


namespace PerfectInformationGame
variable {α : Type*} [DecidableEq α] {players : Type*}
variable (g: PerfectInformationGame players α)

def internodes : Finset α:= Finset.image g.p g.nodes
def leaves : Finset α := Finset.filter (· ∉ g.internodes) g.nodes

variable {g} in
def propersubgame {x : α} (hx : x ∈ g.nodes) (neroot: x ≠ g.root): PerfectInformationGame players α where
  p := g.p
  R := g.R
  root := x
  /- The definition below is not correct -/
  nodes := g.nodes.erase g.root
  root_mem_nodes := Finset.mem_erase.2 ⟨neroot,hx⟩
  no_loop := by
    intro y hy n _
    obtain ⟨yneroot,ymemnodes⟩ := Finset.mem_erase.1 hy
    exact g.no_loop y ymemnodes n yneroot
  connect_root := by sorry

lemma nodes_size_decrease (hx : x∈ g.nodes) (neroot:x ≠ g.root) : (propersubgame hx neroot).nodes.card < g.nodes.card := by
  dsimp [propersubgame]
  have : g.nodes.Nonempty := Set.nonempty_of_mem g.root_mem_nodes
  simp [Finset.card_erase_of_mem g.root_mem_nodes,this]


variable (σ : α → α)

/- instance subgame_strategy' {σ : α → α} [Strategy g σ] (hx : x∈ g.nodes) (neroot:x ≠ g.root)
: Strategy (propersubgame hx neroot) σ := by sorry -/


lemma subgame_nodes_mem_nodes {players : Type*} {α : Type*}
{g : PerfectInformationGame players α} {x : α } (hx : x∈ g.nodes) (neroot:x ≠ g.root) : (propersubgame hx neroot).nodes ⊆ g.nodes := by simp only [propersubgame]; intro y hy; apply (Finset.mem_erase (a:=y)).1 hy |>.2

section strategy

def strategy_ne_root {g : PerfectInformationGame players α}
{σ : α → α} (hs : Strategy g σ) {x : α }: x ∈ g.nodes → σ x ≠ g.root:= by
  unfold Strategy at hs
  intro hx h
  have h': x =  g.p (g.root) := by rw [<-(hs _ hx).2,h]
  sorry




end strategy

lemma subgame_strategy
{σ : α → α} {g : PerfectInformationGame players α} (hs : Strategy g σ) {x : α } (hx : x∈ g.nodes) (neroot:x ≠ g.root)
: Strategy (propersubgame hx neroot) σ := by
  unfold Strategy
  intro y hy
  have hy' : y ∈ g.nodes := subgame_nodes_mem_nodes hx neroot hy
  simp only [propersubgame] at *
  constructor
  · rw [Finset.mem_erase]
    constructor
    · exact (strategy_ne_root hs hy')
    · exact (hs _ hy').1
  · exact (hs _ hy').2



def outcome {players : Type*} {α : Type*}
{σ : α → α} (g : PerfectInformationGame players α) (hs : Strategy g σ) : players :=
  if g.root ∈ g.leaves then
    g.R g.root
  else
    /- subgame -/
    let x := σ g.root
    have hx : x∈ g.nodes:= sorry
    have neroot : x≠ g.root := sorry
    let sg : PerfectInformationGame players α := g.propersubgame hx neroot
    have hs := subgame_strategy hs hx neroot
    outcome sg hs
termination_by g.nodes.card
decreasing_by
  apply nodes_size_decrease

end PerfectInformationGame


namespace PerfectInformationGame
variable (players : Type*) [Doubleton players]

variable {nodes: Type*} (g: PerfectInformationGame players nodes)



end PerfectInformationGame

end
