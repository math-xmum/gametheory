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
| Node (p : Player) (F : List DGameTree) :  DGameTree
deriving Repr, Inhabited





namespace DGameTree

mutual
  def size: DGameTree → Nat
    | .Leaf _ => 1
    | .Node _ cs => 2+ sizeList cs
  def sizeList: List DGameTree → Nat
    | [] => 0
    | c :: cs => size c + sizeList cs
end

lemma sizeList_cons : size (Node p (h::t)) = size h + size (Node p t) := by
  simp [size,sizeList];ring

lemma sizedec {i : ℕ} (F : List DGameTree) : (F.get! i).size < (Node p F).size := by
  by_cases h : i < F.length
  · induction' F with hl t HT generalizing i
    · simp at h
    · match i with
      | 0 =>  simp [size,sizeList];linarith
      | i+1 =>
        replace h : i < t.length := by
          rw [List.length] at h
          exact Nat.lt_of_succ_lt_succ h
        replace h:= HT h
        rw [List.get!_eq_getElem!, List.getElem!_cons_succ, sizeList_cons];
        have : t[i]!.size = (t.get! i).size := by simp only [List.get!_eq_getElem!]
        rw [<-this] at h
        apply lt_of_lt_of_le h
        simp only [le_add_iff_nonneg_left, zero_le]
  · push_neg at h
    simp only [List.get!_eq_getD,List.getD_eq_default, h]
    simp only [size];linarith




/- A Strategy of player I is a function
  sends each (Pnode I L R : GameTree) to L or R.
-/
abbrev Strategy := (t : DGameTree) → ℕ


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
  | Node d F =>
    if p = d then
     outcome $ F.get! (S t)
    else
     outcome $ F.get! (S' t)
termination_by t.size
decreasing_by
  all_goals apply sizedec



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
