import GameTheory.ExtensiveForm.Def

section PrisonerDilemma


-- Player and Action types
inductive Player | A | B
  deriving DecidableEq, Repr

inductive Act | C | D
  deriving DecidableEq, Repr


/--
The outcome of the game is a pair (A's payoff, B's payoff) where the payoffs are integers representing how much years the player stays in jail.
-/
def Outcome := ℕ × ℕ

-- The nodes of the game
inductive PDNode
| root        -- Player A acts
| bC          -- B acts after A chooses C
| bD          -- B acts after A chooses D
| outCC       -- both C
| outCD       -- A C, B D
| outDC       -- A D, B C
| outDD       -- both D
deriving DecidableEq, Repr

open PDNode

-- Single action type for all nodes (as requested)
def PDAction (_ : PDNode) := Act

-- Every node's action type is always inhabited (by Act.C)
instance {n} : Inhabited (PDAction n) := ⟨Act.C⟩


-- Transition function
def PD_move : (x : PDNode) → PDAction x → PDNode
| root,  Act.C => bC
| root,  Act.D => bD
| bC,    Act.C => outCC
| bC,    Act.D => outCD
| bD,    Act.C => outDC
| bD,    Act.D => outDD
| n,     _     => n  -- stay in terminal (should not matter)

-- At each node, who acts or what outcome is reached
def PD_nodetype : PDNode → Player ⊕ Outcome
| root    => Sum.inl Player.A
| bC      => Sum.inl Player.B
| bD      => Sum.inl Player.B
| outCC   => Sum.inr (3, 3)
| outCD   => Sum.inr (0, 5)
| outDC   => Sum.inr (5, 0)
| outDD   => Sum.inr (1, 1)


-- Now, the Game itself
def PrisonersDilemmaSpace : GameSpace Player Outcome :=
{ node             := PDNode,
  action           := PDAction,
  action_intabited := by intro x; apply inferInstance,
  move             := PD_move,
  nodetype         := PD_nodetype,
}



-- Now, the Game with Perfect information
def PrisonersDilemma : Game Player Outcome := PrisonersDilemmaSpace.toPerfectInformationGame


end PrisonerDilemma
