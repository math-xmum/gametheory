import GameTheory.ExtensiveForm.Def

section CandidateChoice

-- Define players
inductive Player | Eric | Larry | Sergey
  deriving DecidableEq, Repr, Fintype

-- Define actions (candidates)
inductive Candidate | Lee | Rebecca | John
  deriving DecidableEq, Repr, Fintype

-- Define game outcomes: which candidate is accepted, or none
inductive Outcome | Accepted (c : Candidate) | Rejected
  deriving DecidableEq, Repr

open Player Candidate Outcome

/-- Game node definition -/
inductive Node
| root        -- Eric's choice
| l_Lee       -- Larry's action after Eric chooses Lee
| l_Rebecca   -- Larry's action after Eric chooses Rebecca
| l_John      -- Larry's action after Eric chooses John
| s_LL        -- Sergey's action after Eric=Lee, Larry=Lee
| s_LR        -- Sergey's action after Eric=Lee, Larry=Rebecca
| s_LJ        -- Sergey's action after Eric=Lee, Larry=John
| s_RL
| s_RR
| s_RJ
| s_JL
| s_JR
| s_JJ
| out_Accepted (c : Candidate)
| out_Rejected
deriving DecidableEq, Repr

open Node

/-- Available action type at each node (all players choose Candidate) -/
def Act (_ : Node) := Candidate

instance {n} : Inhabited (Act n) := ⟨Candidate.Lee⟩

/-- Transition function: moves to next node based on current node and action -/
def move : (x : Node) → Act x → Node
| root, Lee      => l_Lee
| root, Rebecca  => l_Rebecca
| root, John     => l_John

| l_Lee, Lee      => s_LL
| l_Lee, Rebecca  => s_LR
| l_Lee, John     => s_LJ

| l_Rebecca, Lee      => s_RL
| l_Rebecca, Rebecca  => s_RR
| l_Rebecca, John     => s_RJ

| l_John, Lee      => s_JL
| l_John, Rebecca  => s_JR
| l_John, John     => s_JJ

-- After Sergey's final vote, move to outcome node
| s_LL, _ => out_Accepted Lee
| s_LR, Lee => out_Accepted Lee
| s_LR, Rebecca => out_Accepted Rebecca
| s_LR, John => out_Rejected
| s_LJ, Lee => out_Accepted Lee
| s_LJ, John => out_Accepted John
| s_LJ, Rebecca => out_Rejected

| s_RL, Lee => out_Accepted Lee
| s_RL, Rebecca => out_Accepted Rebecca
| s_RL, John => out_Rejected
| s_RR, _ => out_Accepted Rebecca
| s_RJ, Rebecca => out_Accepted Rebecca
| s_RJ, John => out_Accepted John
| s_RJ, Lee => out_Rejected

| s_JL, John => out_Accepted John
| s_JL, Lee => out_Accepted Lee
| s_JL, Rebecca => out_Rejected
| s_JR, John => out_Accepted John
| s_JR, Rebecca => out_Accepted Rebecca
| s_JR, Lee => out_Rejected
| s_JJ, _ => out_Accepted John

-- Terminal states remain unchanged
| out_Accepted _, _ => out_Rejected
| out_Rejected, _   => out_Rejected


/-- Node type: which player acts, or outcome -/
def nodetype : Node → Player ⊕ Outcome
| root => Sum.inl Eric
| l_Lee | l_Rebecca | l_John => Sum.inl Larry
| s_LL | s_LR | s_LJ
| s_RL | s_RR | s_RJ
| s_JL | s_JR | s_JJ => Sum.inl Sergey
| out_Accepted c => Sum.inr (Accepted c)
| out_Rejected   => Sum.inr Rejected


/-- Define game space -/
def CandidateChoiceSpace : GameSpace Player Outcome :=
{ node := Node,
  action := Act,
  action_intabited := by intro x; apply inferInstance,
  move := move,
  nodetype := nodetype
}


/-- Perfect information version -/
def CandidateChoicePerfectInfo : Game Player Outcome :=
CandidateChoiceSpace.toPerfectInformationGame

end CandidateChoice



#eval move Node.s_LR Candidate.Lee -- Should be out_Accepted Lee
#eval move Node.s_RJ Candidate.Lee -- Should be out_Rejected
#eval nodetype Node.root -- Should be Sum.inl Eric
#eval nodetype (Node.out_Accepted Candidate.Rebecca) -- Should be Sum.inr (Accepted Rebecca)
#eval nodetype (move Node.l_Lee Candidate.Rebecca) -- Should be Sum.inl Sergey
#eval move Node.l_John Candidate.Rebecca -- Should be s_JR
#eval nodetype (move Node.s_JJ Candidate.John) -- Should be Sum.inr (Accepted John)
#eval nodetype (move (move Node.root Candidate.Rebecca) Candidate.John) -- Should be Sum.inl Sergey
