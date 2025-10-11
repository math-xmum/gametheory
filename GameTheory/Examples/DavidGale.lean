import Mathlib.Combinatorics.Young.YoungDiagram
import GameTheory.ExtensiveForm.Def


namespace DavidGale


/-- Players A and B. -/
inductive Player where
  | A
  | B
deriving DecidableEq, Repr

/-- In our Outcome we store the winner. -/
inductive Outcome where
  | winner : Player → Outcome

/-- helper: the other player -/
def other : Player → Player
  | Player.A => Player.B
  | Player.B => Player.A

/-
  We will represent decision nodes only for diagrams with at least one cell.
  For that we use a small helper type PosNode that packages a YoungDiagram
  together with a proof of nonemptiness of its finset of cells.
-/
abbrev DGNode := YoungDiagram × Player


abbrev DGNode.DGAction (n : DGNode) : Type :=
  let cc := n.1.cells.erase (0,0)
  if cc.Nonempty then {x // x ∈ cc} else {x : ℕ × ℕ // x = (0,0)}

abbrev DGNode.DGAction.toprod {n : DGNode} (a : n.DGAction) : (ℕ × ℕ)  := by
  unfold DGNode.DGAction at a
  by_cases h: (n.1.cells.erase (0,0)).Nonempty
  simp only [h, reduceIte] at a
  exact a.1
  simp only [h, reduceIte] at a
  exact a.1


/-- Instance to show actions are inhabited -/
instance (n : DGNode) : Nonempty (n.DGAction) := by
  unfold DGNode.DGAction
  by_cases h:(n.1.cells.erase (0,0)).Nonempty
  simp only [h, reduceIte,Finset.nonempty_coe_sort]
  simp only [h, ↓reduceIte, nonempty_subtype, exists_eq]



def nodetype (n : DGNode) : Player ⊕ Outcome :=
  if n.1.cells.card < 2 then
    Sum.inr (Outcome.winner n.2)
  else
    Sum.inl n.2


/-- Remove the north-east rectangle determined by chosen cell c = (i,j).
    We keep those cells (x,y) with x < i or y < j. -/
abbrev remove_ne (d : YoungDiagram) (c : ℕ × ℕ) : YoungDiagram := ⟨d.cells.filter fun (i,j) => c.1 < i ∨ c.2 < j,sorry⟩


def DGMove (n : DGNode) (a : n.DGAction) : DGNode :=
  if n.1.cells.card < 2 then
    (remove_ne n.1 a.toprod, other n.2)
  else
    (n.1, n.2)

/-- The David-Gale game as a GameSpace -/
def davidGaleGame : GameSpace Player Outcome where
  node := DGNode
  action := DGNode.DGAction
  action_intabited := inferInstance
  move := DGMove
  nodetype := nodetype


end DavidGale
