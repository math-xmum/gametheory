import Mathlib

section

variable (Player : Type*) (Outcome : Type*) [Nonempty Player] [Nonempty Outcome]

/--
We understand a Game Space as a status machine
-/
structure GameSpace Player Outcome where
    node : Type*
    action : node -> Type*
    /- We require that actions attached to x are nonempty, this is to ensure that the space of strategies is nonempty. -/
    action_intabited: ∀ x, Nonempty (action x)
    move : (x : node) -> action x → node
    nodetype : node -> Player ⊕ Outcome

namespace GameSpace

variable {Player : Type*} {Outcome : Type*} {G : GameSpace Player Outcome}


abbrev node.nodetype (x : G.node) := G.nodetype x

abbrev node.isOutcome (x : G.node) := x.nodetype.isRight
abbrev node.isInter (x : G.node) := x.nodetype.isLeft


abbrev action.next {x} (a : G.action x): G.node := G.move x a

variable (G) in
def Strategy  := (x : G.node) -> G.action x

partial def node.Finite (x : G.node) : Prop :=
    -- Either it is an outcome node
    x.isOutcome ∨
    -- Or all nodes obtained from the next action are fintie
    ∀ (a : G.action x), node.Finite a.next

def Finite := ∀ (x : G.node), x.Finite

/-- We identify a node `x` with the subgame space with intial node `x` -/
def Subgame (G : GameSpace Player Outcome) := G.node


variable [Nonempty Outcome]

/-- Play the game from a given node with a given strategy to get an outcome -/
partial def Strategy.playWithStrategy [Nonempty Outcome] (s : G.Strategy) (x : G.node) :  Outcome := match G.nodetype x with
    | Sum.inr outcome => outcome  -- If we're at an outcome node, return it
    | Sum.inl _ => s.playWithStrategy (G.move x (s x))  -- Otherwise, apply strategy and continue

/-- The outcome of a subgame starting from node x with strategy s -/
partial def subgameOutcome (x : G.Subgame) (s : G.Strategy) : Outcome :=
  s.playWithStrategy x

/-- Alternative definition using fuel for computational purposes -/
def playWithStrategyFuel (fuel : ℕ) (s : G.Strategy) : (x : G.node) → Option Outcome
  | x => match fuel with
    | 0 => none  -- Out of fuel
    | fuel' + 1 => match G.nodetype x with
      | Sum.inr outcome => some outcome
      | Sum.inl _ => playWithStrategyFuel fuel' s (G.move x (s x))

/-- For finite nodes, playing with a strategy eventually reaches an outcome -/
theorem finite_reaches_outcome (x : G.node) (hx : x.Finite) (s : G.Strategy) :
  ∃ (o : Outcome), ∃ (fuel : ℕ), playWithStrategyFuel fuel s x = some o := by
  sorry  -- This would require induction on the finiteness proof

end GameSpace


structure Game extends GameSpace Player Outcome where
    -- The information is an partition of nodes. We use equivalence relation
    -- to represent the partition .
    info : Setoid node
    -- The actionsets are the same for all  equivalent nodes
    actionequiv : ∀ {x y : node}, x ≈ y → nodetype x = nodetype y → action x = action y

attribute [instance] Game.info

end

namespace Game

variable {Player : Type*} {Outcome : Type*} {G : Game Player Outcome}



structure Strategy where
  s : (x : G.node) -> G.action x
  s_constant : ∀ {x y : G.node}, x ≈ y → x.isInter → y.isInter →  x.nodetype = y.nodetype → s x ≍ s y


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
