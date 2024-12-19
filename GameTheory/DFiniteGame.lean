import Mathlib
--open Classical


/-
We show that finite zerosum game with two player and natural has a value.
We attempt to make everything computable

The game tree is a binary tree
The value is the value of first player
-/

section

inductive Player
| A : Player -- Alice
| B : Player -- Bob
deriving Repr, DecidableEq, Inhabited



instance Player.repr : Repr Player where
  reprPrec p _ := match p with
    | Player.A => "A"
    | Player.B => "B"

inductive Select
| l -- Select the left branch
| r -- Select the right branch
deriving Repr,DecidableEq, Inhabited


#eval Player.A

inductive DGameTree
-- The winner of the game
| Leaf (w : Player) : DGameTree
-- Player's node
| Node (p : Player) (L : DGameTree) (R: DGameTree) :  DGameTree
deriving Repr, DecidableEq, Inhabited

namespace DGameTree

def size(t : DGameTree) : ℕ  := match t with
  | Leaf _ => 1
  | Node _ L R => L.size + R.size

lemma sizepos (t : DGameTree) : 1 ≤ t.size := by
  induction t
  all_goals simp [size]; try linarith

/- A Strategy of player I is a function
  sends each (Pnode I L R : GameTree) to L or R.
-/
abbrev Strategy := DGameTree → DGameTree → Select


/- Given a strategy of a player and strategy of the other player and a game
  (t : GameTree)
  the following function compute the expected outcome
  for player p
 -/
variable (S S' : Strategy) (p : Player)

/-
The outcome of the game for a given strategy
-/
def outcome (t : DGameTree) : Player :=
  match t with
  | Leaf r => r
  | Node d L R =>
    if p = d then
     match (S L R) with
      | .l => outcome L
      | .r => outcome R
    else
     match (S' L R) with
      | .l => outcome L
      | .r => outcome R

--  compute whether player P has a dominant strategy for a game of the form (Node P L R : DGameTree)
def existsDStrategy (p : Player) (t : DGameTree) : Bool :=
  match t with
  | Leaf w => w = p
  | Node w L R => if w = p
    then L.existsDStrategy p ∨ R.existsDStrategy p
    else L.existsDStrategy p ∧ R.existsDStrategy p

/- compute whether player P has a dominant strategy for a game of the form (Node P L R : DGameTree)
If there is dominant strategy, the DStrategy is the
dominant one
-/
def DStrategy (p : Player) (L R : DGameTree): Select :=
  match L.existsDStrategy p with
  | true => Select.l
  | _ =>  Select.r

variable {t : GameTree}

/- If t.existsDStrategy p, then  DStrategy is
the dominant strategy
i.e. no mater how the other part choose
 -/
theorem existsDStrategy_def {p : Player} {t : DGameTree} (h : t.existsDStrategy p) : ∀ S' : Strategy, outcome S S' p t = p := by sorry



notation:200 "LA" => (Leaf Player.A)
notation:200 "LB" => (Leaf Player.B)
notation:100 "[A " L:100 ", " R:100 "]" => DGameTree.Node Player.A L R
notation:100 "[B " L:100 ", " R:100 "]" => DGameTree.Node Player.B L R

def T := [B [A LA, LB] , LB]

#eval T.existsDStrategy Player.A

#eval T

end DGameTree


end
