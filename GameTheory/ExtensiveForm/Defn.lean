import Mathlib

section

variable (Player : Type*) (Outcome : Type*) [Nonempty Player] [Nonempty Outcome]

/--
We understand a Game Space as a status machine
-/
structure GameSpace Player Outcome where
    /-- internal node-/
    int_node : Type*
    /-- external node -/
    ext_node : Type*
    action : int_node -> Type*
    /- We require that actions attached to x are nonempty, this is to ensure that the space of strategies is nonempty. -/
    action_intabited: ∀ x, Nonempty (action x)
    move : (x : int_node) -> action x → int_node ⊕ out_node
    player: int_node -> Player
    outcome : out_node -> Outcome


namespace GameSpace

variable {Player : Type*} {Outcome : Type*} {G : GameSpace Player Outcome}

abbrev node := G.int_node ⊕ G.ext_node

abbrev int_node.player (x : G.int_node) := G.player x

abbrev Node (i : Player) := {x : G.int_node | x.player = i}


abbrev node.isOutcome (x : G.node) := x.isRight
abbrev node.isInter (x : G.node) := x.isLeft
abbrev node.player (x : G.node) : Option Player := match x with
  | Sum.inr _ => none
  | Sum.inl x => some (G.player x)

abbrev node.isPlayer (x : G.node) (i : Player) :=
  x.player = i

variable {i : Player}
@[simp]
lemma node.isPlayer_def (x : G.int_node) : x.player = i ↔ x ∈ G.Node i :=
  by
  constructor
  · intro h; exact h
  · intro h; exact h


variable {i : Player}

@[simp]
lemma node_player (x : G.Node i) : x.val.player = i :=
  x.property




variable (G) in
abbrev Strategy' (i : Player) := (x : G.Node i) → G.action x

variable (G) in
abbrev Strategy := (x : G.int_node) → G.action x

instance funlike : DFunLike G.Strategy (Player) (G.Strategy') where
  coe s := fun _ n => s n
  coe_injective' := by
    intro s t h
    ext n
    replace h:= congr_fun₂ h
    specialize h n.player ⟨n,rfl⟩
    grind

variable [DecidableEq Player]
def Strategy.update (s : G.Strategy) (si : G.Strategy' i) : G.Strategy :=
  fun x =>
    if h : x.player = i then si ⟨x, h⟩ else s x


abbrev action.next {x} (a : G.action x): G.node := G.move x a

partial def nodeFinite (x : G.node) : Prop :=
  match x with
  | Sum.inr _ => True
  | Sum.inl x => ∀ (a : G.action x), nodeFinite a.next

def Finite := ∀ (x : G.node), G.nodeFinite x

/-- We identify a node `x` with the subgame space with intial node `x` -/
abbrev Subgame (G : GameSpace Player Outcome) := G.int_node

variable [Nonempty Outcome]

/-- Play the game from a given node with a given strategy to get an outcome -/
partial def playWithStrategy [Nonempty Outcome] (s : G.Strategy) (x : G.node) :  Outcome := match x with
    | Sum.inr o => G.outcome o  -- If we're at an outcome node, return it
    | Sum.inl i => playWithStrategy s (G.move i (s i))  -- Otherwise, apply strategy and continue

partial def Subgame.play  (x : G.Subgame) (s : G.Strategy) : Outcome := playWithStrategy s (Sum.inl x)

-- #check fun s : G.Strategy => fun x : G.int_node => x.play s

variable {R : Type*} [Preorder R]

def Subgame.NashEquilibrium (x : G.Subgame) (s : G.Strategy) (utility : Player → Outcome → R):= ∀ i, ∀ (si : G.Strategy' i), utility i (x.play s) ≥ utility i (x.play (s.update si))


end GameSpace


structure Game extends GameSpace Player Outcome where
    -- The information is an partition of nodes. We use equivalence relation
    -- to represent the partition .
    info : Setoid int_node
    -- The actionsets are the same for all  equivalent nodes
    actionequiv : ∀ {x y : int_node}, x ≈ y → player x = player y → action x = action y

attribute [instance] Game.info

end

namespace Game

variable {Player : Type*} {Outcome : Type*} {G : Game Player Outcome}


variable (G) in
structure Strategy where
  s : (x : G.int_node) -> G.action x
  s_constant : ∀ {x y : G.int_node}, x ≈ y → x.player= y.player → s x ≍ s y



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
