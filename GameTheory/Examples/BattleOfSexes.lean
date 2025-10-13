import GameTheory.ExtensiveForm.Def

namespace BattleOfSexes

-- Players
inductive Player | Man | Woman
deriving DecidableEq, Repr

-- Activities / Actions
inductive Action | F | C    -- Football, Concert
deriving DecidableEq, Repr

-- Outcomes (payoff for Man, Woman)
def Outcome := ℕ × ℕ

-- Node type for extensive form:
inductive BoSNode
| root         -- Man chooses
| womanF       -- Woman chooses, Man picked F
| womanC       -- Woman chooses, Man picked C
| outFF        -- both F
| outFC        -- Man F, Woman C
| outCF        -- Man C, Woman F
| outCC        -- both C
deriving DecidableEq, Repr

open BoSNode Player

-- Node's possible actions
def BoSAction (_ : BoSNode) : Type := Action

instance {n} : Inhabited (BoSAction n) := ⟨Action.F⟩

-- Game step/move (deterministic transitions)
def BoS_move : (x : BoSNode) → BoSAction x → BoSNode
| root,      Action.F   => womanF
| root,      Action.C   => womanC
| womanF,    Action.F   => outFF
| womanF,    Action.C   => outFC
| womanC,    Action.F   => outCF
| womanC,    Action.C   => outCC
| n,         _          => n   -- stays (dummy for terminals)

-- Who moves or what payoff?
def BoS_nodetype : BoSNode → Player ⊕ Outcome
| root      => Sum.inl Man
| womanF    => Sum.inl Woman
| womanC    => Sum.inl Woman
| outFF     => Sum.inr (2,1)
| outFC     => Sum.inr (0,0)
| outCF     => Sum.inr (0,0)
| outCC     => Sum.inr (1,2)

-- Define GameSpace instance
def BoS_Space : GameSpace Player Outcome :=
{ node := BoSNode,
  action := BoSAction,
  action_intabited := by intros; apply inferInstance,
  move := BoS_move,
  nodetype := BoS_nodetype
}

instance : Fintype BoSNode  where
   elems := {root, womanF, womanC, outFF, outFC, outCF, outCC}
   complete := by
    intro x
    match x with
     | root      => simp
     | womanF    => simp
     | womanC    => simp
     | outFF     => simp
     | outFC     => simp
     | outCF     => simp
     | outCC     => simp

-- Information set: Woman cannot tell whether at womanF or womanC.
instance BoS_info : Setoid BoSNode where
  r := λ x y => x = y ∨ (x = womanF ∨ x = womanC) ∧ (y  =  womanF ∨ y = womanC)
  iseqv := by
    apply Equivalence.mk <;> decide

-- Action equivalence: all nodes have the same (Action) at decision points.
theorem BoS_actionequiv {x y : BoSNode} (h : x ≈ y) (ht : BoS_nodetype x = BoS_nodetype y) :
  BoSAction x = BoSAction y :=
by
  cases x <;> cases y <;> try rfl -- all player decision nodes action type = Action

-- The full game structure:
def BattleOfSexes : Game Player Outcome :=
{ toGameSpace := BoS_Space,
  info := BoS_info,
  actionequiv := BoS_actionequiv
}

end BattleOfSexes
