import Mathlib

section

variable (Players : Type*) (Outcome : Type*)

/--
We understand a Game Space as a state machine
-/
structure GameSpace Players Outcome where
    node : Type*
    action : node -> Type*
    action_intabited: ∀ x, Nonempty (action x)
    move : (x : node) -> action x → node
    nodetype : node -> Players ⊕ Outcome

namespace GameSpace

variable {Players : Type*} {Outcome : Type*} {G : GameSpace Players Outcome}


abbrev node.nodetype (x : G.node) := G.nodetype x

abbrev node.isOutcome (x : G.node) := x.nodetype.isRight


abbrev action.next {x} (a : G.action x): G.node := G.move x a

variable (G) in
def Strategy  := (x : G.node) -> G.action x

partial def node.Finite (x : G.node) : Prop :=
    -- Either it is an outcome node
    x.isOutcome ∨
    -- Or all nodes obtained from the next action are fintie
    ∀ (a : G.action x), node.Finite a.next

def Finite := ∀ (x : G.node), x.Finite

end GameSpace


structure Game extends GameSpace Players Outcome where
    -- The information is an partition of nodes. We use equivalence relation
    -- to represent the partition .
    info : Setoid node
    -- The actionsets are the same for all  equivalent nodes
    actionequiv : ∀ {x y : node}, x ≈ y → nodetype x = nodetype y → action x ≈ action y



end

section Example

/-
Now formulate the prizoner dilemma game using above definitions
-/



end Example
