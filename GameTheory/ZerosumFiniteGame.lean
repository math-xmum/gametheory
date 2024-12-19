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
deriving Repr, DecidableEq

instance Player.repr : Repr Player where
  reprPrec p _ := match p with
    | Player.A => "A"
    | Player.B => "B"

inductive Select
| l -- Select the left branch
| r -- Select the right branch
deriving Repr,DecidableEq


#eval Player.A

inductive GameTree
| Leaf (val : ℚ) : GameTree
-- Player's node
| Pnode (p : Player) (L : GameTree) (R: GameTree) :  GameTree
-- Natural's node, p represent the probability to choose the left tree
| Nnode (p : Set.Icc (0:ℚ) 1) (L : GameTree) (R : GameTree) : GameTree
deriving Repr, DecidableEq



instance : Inhabited GameTree :=
  ⟨.Leaf 0⟩

#eval (default : GameTree)

namespace GameTree

def size(t : GameTree) : ℕ  := match t with
  | Leaf _ => 1
  | Pnode _ L R => L.size + R.size
  | Nnode _ L R => L.size + R.size

lemma sizepos (t : GameTree) : 1 ≤ t.size := by
  induction t
  all_goals simp [size]; try linarith

/- A Strategy of player I is a function
  sends each (Pnode I L R : GameTree) to L or R.
-/
abbrev Strategy := GameTree → GameTree → Select


/-
The following function calculate the value of the game
-/
def value (t : GameTree) : ℚ  := match t with
  | Leaf r => r
  | Pnode p L R => match p with
    -- If A is the player, the choose the maximal value
    | .A => max L.value R.value
    | .B => min L.value R.value
  | Nnode p L R => p * L.value + (1 - p) * R.value



-- The dominant Strategy for player A is to select the highest value branch
def DStrategy : Strategy :=
  fun L R =>
    if L.value < R.value then  Select.r else Select.l


/- Given a strategy of A and strategy of B and a game
  (t : GameTree)
  the following function compute the expected outcome
 -/
variable (SA SB : Strategy)

def outcome (t : GameTree) : ℚ :=
  match t with
  | Leaf r => r
  | Pnode p L R =>
    match p with
    | Player.A => match (SA L R) with
      | .l => outcome L
      | .r => outcome R
    | Player.B => match (SB L R) with
      | .l => outcome L
      | .r => outcome R
  | Nnode p L R => p * outcome L + (1-p) * outcome R

variable {t : GameTree}

/- The value is guaranteed  by DStrategy -/
theorem value_prop : t.value ≤ t.outcome DStrategy SB := by
  induction t with
  | Leaf r =>  simp [outcome,value]
  | Pnode p L R HL HR =>
    match p with
    | Player.A =>
      rw [value,outcome,DStrategy]
      split_ifs with H
      all_goals simp [HL,HR];linarith
    | Player.B =>
      rw [value,outcome]
      cases SB L R
      all_goals simp [min_le_iff,HL,HR]
  | Nnode p L R HL HR =>
    rw [outcome,value]
    have I1: p * L.value ≤ p * outcome DStrategy SB L := mul_le_mul_of_nonneg_left HL p.2.1
    have I2: (1-p) * R.value ≤ (1-p) * outcome DStrategy SB R := mul_le_mul_of_nonneg_left HR (by simp [p.2.2])
    exact add_le_add I1 I2


def PUInterval (a : ℚ) : Set.Icc (0:ℚ) 1:= if h: 0 ≤ a ∧ a ≤ 1 then ⟨a,h⟩ else 0


notation:100 "[L " v:101 "]" => Leaf v
notation:100 "[N " p:100 ", " L:100 ", " R:100 "]" => GameTree.Nnode (PUInterval p)  L R
notation:100 "[A " L:100 ", " R:100 "]" => GameTree.Pnode Player.A L R
notation:100 "[B " L:100 ", " R:100 "]" => GameTree.Pnode Player.B L R

def T := [B [A [L 10], [L (-10)]] , [L 3]]
def T' := [N 0.5 , T , T]

#eval T'.value


end GameTree


end
