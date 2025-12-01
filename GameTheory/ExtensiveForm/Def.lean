import Mathlib

section

variable (Player : Type*) (Outcome : Type*) [Nonempty Player] [Nonempty Outcome]

/--
We understand a Game Space as a status machine
-/
structure preGameSpace Outcome where
    node : Type*
    nodetype : node -> Player ⊕ Outcome


namespace preGameSpace
variable {Player : Type*} {Outcome : Type*} {G : preGameSpace Player Outcome}

abbrev node.nodetype (x : G.node) := G.nodetype x

abbrev node.isOutcome (x : G.node) := x.nodetype.isRight
abbrev node.isInter (x : G.node) := x.nodetype.isLeft
abbrev node.isPlayer (x : G.node) (i : Player):= x.nodetype = Sum.inl i


lemma not_isOutcome_iff_isInter {x : G.node} : ¬ x.isOutcome ↔ x.isInter :=
  by
  unfold node.isOutcome
  unfold node.isInter
  grind

lemma not_isInter_iff_isOutcome {x : G.node} : ¬ x.isInter ↔ x.isOutcome :=
  by
  unfold node.isOutcome
  unfold node.isInter
  grind

lemma isInter_of_isPlayer {x : G.node} {i : Player} (h : x.isPlayer i) : x.isInter :=
  by
  unfold node.isPlayer at h
  unfold node.isInter
  simp [h]


abbrev Node (i : Player) := {x : G.node // x.isPlayer i}

def interNode := {x : G.node // x.isInter}
def outerNode := {x : G.node // x.isOutcome}


def node.split (x : G.node) : (G.interNode) ⊕ (G.outerNode) :=
  if h : x.isInter then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, not_isInter_iff_isOutcome.1 h⟩

def interNode.player (x : G.interNode) : Player := by
  have x_prop : x.val.nodetype.isLeft:= x.prop
  set nt := x.val.nodetype with ← h
  match nt with
  | Sum.inl i => exact i
  | Sum.inr _ => contradiction

def outerNode.outcome (x : G.outerNode) : Outcome := by
  have x_prop : x.val.nodetype.isRight:= x.prop
  set nt := x.val.nodetype with ← h
  match nt with
  | Sum.inr o => exact o
  | Sum.inl _ => contradiction


instance {x : G.node}: CoeOut (x.isInter) (G.interNode) where
  coe := fun h => ⟨x,h⟩


variable {i : Player}

lemma mem_interNode_of_memNode {x : G.Node i} : x.val.isInter :=
  by
  grind



lemma player_player'  {n : G.interNode} : n.player = i ↔ n.val.isPlayer i := by
  unfold node.isPlayer
  unfold interNode.player
  grind


instance : CoeOut (G.Node i) G.interNode where
  coe := fun x => ⟨x, isInter_of_isPlayer x.prop⟩


instance {x : G.interNode}: CoeOut (x.player =  i) (G.Node i) where
  coe := fun h => ⟨x.val, player_player'.1 h⟩


end preGameSpace

structure GameSpace Player Outcome extends preGameSpace Player Outcome where
    action : (x: preGameSpace.interNode) -> Type*
    /- We require that actions attached to x are nonempty, this is to ensure that the space of strategies is nonempty. -/
    action_intabited: ∀ x, Nonempty (action x)
    move : (x : preGameSpace.interNode) -> action x → node

namespace GameSpace
open preGameSpace

variable {Player : Type*} {Outcome : Type*} {G : GameSpace Player Outcome}

/-
lemma node.isPlayer_def (x : G.node) (i : Player) : x.isPlayer i ↔ x  G.Node i :=
  by
  constructor
  · intro h; exact h
  · intro h; exact h
-/




/-
lemma interNode_def (x : G.node) : x.isInter ↔ x ∈ G.interNode :=
  by
  constructor
  · intro h; exact h
  · intro h; exact h
-/



def Strategy := (i : Player) → (x : G.Node i) → G.action x

def Strategy' := (x : G.interNode) → G.action x

instance strategy_strategy'_coe : CoeOut G.Strategy' G.Strategy where
  coe := fun s _ n=> s n


abbrev action.next {x} (a : G.action x): G.node := G.move x a


partial def SubgameFinite (x : G.node) : Prop :=
    -- Either it is an outcome node
    (h : x.isInter) →
    -- Or all nodes obtained from the next action are fintie
    ∀ (a : G.action h), SubgameFinite a.next

def Finite := ∀ (x : G.interNode), G.SubgameFinite x.val

/-- We identify a node `x` with the subgame space with intial node `x` -/
def Subgame (G : GameSpace Player Outcome) := G.node


variable [Nonempty Outcome]

/-- Play the game from a given node with a given strategy to get an outcome -/
partial def Strategy'.play [Nonempty Outcome] (s : G.Strategy') (x : G.node) :  Outcome := match x.split with
    | Sum.inr o => o.outcome -- If we're at an outcome node, return it
    | Sum.inl x => s.play (G.move x (s x))  -- Otherwise, apply strategy and continue

/-- The outcome of a subgame starting from node x with strategy s -/
partial def subgameOutcome (x : G.Subgame) (s : G.Strategy') : Outcome :=
  s.play x

/-- Alternative definition using fuel for computational purposes -/
def Strategy'.playWithFuel (fuel : ℕ) (s : G.Strategy') : (x : G.node) → Option Outcome
  | x => match fuel with
    | 0 => none  -- Out of fuel
    | fuel' + 1 =>
      match x.split with
      | Sum.inr o => some o.outcome
      | Sum.inl x => s.playWithFuel fuel' (G.move x (s x))


section Equilibrium

variable [DecidableEq Player]


def Strategy_i (i : Player) := (x : G.Node i) → G.action x

def Strategy'.update {i : Player} (s : G.Strategy') (si : G.Strategy_i i) : G.Strategy' :=
  fun x =>
    if hx : x.player = i then si hx else s x


variable {R : Type*} [Preorder R]

def Subgame.NashEquilibrium (x : G.Subgame) (s : G.Strategy') (utility : Player → Outcome → R):= ∀ i, ∀ (si : G.Strategy_i i), utility i (s.play x) ≥ utility i ((s.update si).play x)


end Equilibrium


end GameSpace




structure Game extends GameSpace Player Outcome where
    -- The information is an partition of nodes. We use equivalence relation
    -- to represent the partition .
    info : Setoid preGameSpace.interNode
    -- The actionsets are the same for all  equivalent nodes
    actionequiv : ∀ {x y : preGameSpace.interNode}, x ≈ y → x.player = y.player → action x = action y

attribute [instance] Game.info




end

namespace Game

variable {Player : Type*} {Outcome : Type*} {G : Game Player Outcome}


structure Strategy where
  s : (x : G.interNode) -> G.action x
  s_constant : ∀ {x y : G.interNode}, x ≈ y → x.player= y.player → s x ≍ s y



end Game


variable {Player Outcome} in
def GameSpace.toPerfectInformationGame (G : GameSpace Player Outcome) : Game Player Outcome:=
{
    G with
    info := ⊥
    actionequiv := by
        intros x y H _;
        replace H : x = y := H
        rw [H]
}
