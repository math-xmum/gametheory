import GameTheory.ExtensiveForm.Def

namespace BattleOfSexes

-- Players
inductive Player | Man | Woman
deriving DecidableEq, Repr

-- Activities / Actions
inductive Action | F | C    -- Football, Concert
deriving DecidableEq, Repr

instance : Inhabited Action := ⟨Action.F⟩
instance : Nonempty Action := inferInstance

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


-- Who moves or what payoff?
def BoS_nodetype : BoSNode → Player ⊕ Outcome
| root      => Sum.inl Man
| womanF    => Sum.inl Woman
| womanC    => Sum.inl Woman
| outFF     => Sum.inr (2,1)
| outFC     => Sum.inr (0,0)
| outCF     => Sum.inr (0,0)
| outCC     => Sum.inr (1,2)

def BoS_preSpace : preGameSpace Player Outcome :=
{ node := BoSNode,
  nodetype := BoS_nodetype
}

def BoSAction (_ : BoS_preSpace.interNode) : Type := Action

-- Game step/move (deterministic transitions)
def BoS_move : (x : BoS_preSpace.interNode) → BoSAction x → BoSNode
:= fun x y => match x.val, y with
| root,      Action.F   => womanF
| root,      Action.C   => womanC
| womanF,    Action.F   => outFF
| womanF,    Action.C   => outFC
| womanC,    Action.F   => outCF
| womanC,    Action.C   => outCC
| n,         _          => n   -- stays (dummy for terminals)

def BoS_Space : GameSpace Player Outcome :=
{ node := BoSNode,
  action := BoSAction,
  action_intabited := fun _ => ⟨Action.F⟩
  move := BoS_move,
  nodetype := BoS_nodetype
}

-- Define GameSpace instance

instance : Fintype BoSNode  where
   elems := {root, womanF, womanC, outFF, outFC, outCF, outCC}
   complete := by
    intro x
    match x with
     | root      | womanF    | womanC    | outFF     | outFC     | outCF     | outCC     => grind

-- Information set: Woman cannot tell whether at womanF or womanC.
instance BoS_info : Setoid BoS_preSpace.interNode where
  r := λ x y => x = y ∨ (x.val = womanF ∨ x.val = womanC) ∧ (y.val  =  womanF ∨ y.val = womanC)
  iseqv := by
    apply Equivalence.mk <;> grind

-- Action equivalence: all nodes have the same (Action) at decision points.
theorem BoS_actionequiv {x y : BoS_Space.interNode} (h : x ≈ y) (ht : x.player = y.player) :
  BoSAction x = BoSAction y :=
by
  cases x <;> cases y <;> try rfl -- all player decision nodes action type = Action

-- The full game structure:
def BattleOfSexes : Game Player Outcome :=
{ toGameSpace := BoS_Space,
  info := BoS_info,
  actionequiv := BoS_actionequiv
}


instance : Inhabited Outcome := ⟨(0,0)⟩

def utility : Player → Outcome → ℕ := fun x o =>  match x with
  | Man => o.1
  | Woman => o.2

open Action
instance : Finite Action := by
  refine @Finite.intro _ 2 ?_
  refine ⟨fun x => match x with
  | F => 0
  | C => 1,
  fun i => match i with
  | 0 => F
  | 1 => C,?_,?_
  ⟩
  grind
  grind

instance : Finite BoSNode := by
  refine @Finite.intro _ 7 ?_
  refine ⟨fun x => match x with
  | root => 0
  | womanF => 1
  | womanC => 2
  | outFF => 3
  | outFC => 4
  | outCF => 5
  | outCC => 6,
  fun i => match i with
  | 0 => root
  | 1 => womanF
  | 2 => womanC
  | 3 => outFF
  | 4 => outFC
  | 5 => outCF
  | 6 => outCC
  , by grind, by grind
  ⟩

instance : Finite $ BoS_preSpace.interNode:= by
  refine @Finite.intro _ 3 ?_
  unfold BoS_preSpace
  unfold preGameSpace.interNode
  dsimp
  refine ⟨?_,
  fun i => match i with
  | 0 => ?_
  | 1 => ?_
  | 2 => ?_
  , ?_,?_
  ⟩
  use fun x => match x.val with
  | root => 0
  | womanF => 1
  | womanC => 2
  | outFF => 2
  | outFC => 2
  | outCF => 2
  | outCC => 2
  use womanC <;> decide
  use womanF <;> decide
  use root <;> decide
  sorry
  sorry



lemma isInter (x : BoS_preSpace.node) : x.isInter ↔ x=root ∨ x=womanF ∨ x=womanC := by
  unfold BoS_preSpace at *
  fin_cases x <;> decide

instance : Finite BoS_Space.Strategy' := by
  unfold GameSpace.Strategy'
  sorry




theorem no_equilibrium : ∀ s : BoS_Space.Strategy', ¬ s.NashEquilibrium BoSNode.root utility:= by
  sorry

end BattleOfSexes
