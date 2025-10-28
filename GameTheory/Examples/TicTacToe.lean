-- Import necessary tactics and definitions from mathlib.
import Mathlib.Tactic
import GameTheory.ExtensiveForm.Def

namespace TicTacToe

/-- Defines a position on the 3x3 board. -/
inductive Pos : Type
| mk : Fin 3 → Fin 3 → Pos
deriving DecidableEq, Repr

/-- Defines the two players, X and O. -/
inductive Player
| X
| O
deriving DecidableEq, Repr

/-- Defines the board as a function from a position to an optional player. -/
def Board := Pos → Option Player

-- Provides a pretty-printing instance for the board.
instance : Repr Board where
  reprPrec b _ :=
    let rows := (List.finRange 3).map fun i =>
      let row := (List.finRange 3).map fun j =>
        match b (Pos.mk i j) with
        | some Player.X => "X"
        | some Player.O => "O"
        | none => "."
      String.intercalate " " row
    String.intercalate "\n" rows

/-- The initial empty board where all positions are `none`. -/
def emptyBoard : Board := fun _ => none

/-- Checks if a square is empty. Returns `true` if it is. -/
def isEmpty (b : Board) (p : Pos) : Bool :=
  b p == none

/-- Places a player's mark on the board if the position is empty. -/
def place (b : Board) (p : Pos) (pl : Player) : Board :=
  if b p = none then
    fun q => if q = p then some pl else b q
  else
    b

/-- A list of all 9 positions on the board. -/
def allPositions : List Pos :=
  (List.finRange 3).flatMap fun i =>
  (List.finRange 3).map fun j => Pos.mk i j

/-- A list of all 8 winning lines (3 rows, 3 columns, 2 diagonals). -/
def winningLines : List (List Pos) :=
  let rows := (List.finRange 3).map fun i =>
    (List.finRange 3).map fun j => Pos.mk i j
  let cols := (List.finRange 3).map fun j =>
    (List.finRange 3).map fun i => Pos.mk i j
  -- The two main diagonals are constructed directly.
  let diag1 := [
      Pos.mk ⟨0, by decide⟩ ⟨0, by decide⟩,
      Pos.mk ⟨1, by decide⟩ ⟨1, by decide⟩,
      Pos.mk ⟨2, by decide⟩ ⟨2, by decide⟩
    ]
  let diag2 := [
      Pos.mk ⟨0, by decide⟩ ⟨2, by decide⟩,
      Pos.mk ⟨1, by decide⟩ ⟨1, by decide⟩,
      Pos.mk ⟨2, by decide⟩ ⟨0, by decide⟩
    ]
  rows ++ cols ++ [diag1, diag2]

/-- Checks if a given player has won the game. -/
def isWinner (b : Board) (pl : Player) : Bool :=
  winningLines.any fun line =>
    line.all fun pos => b pos = some pl

/-- Represents the state of the game at any point (the board and the current turn). -/
structure GameState where
  board : Board
  turn  : Player
deriving Repr

/-- Switches to the next player. -/
def nextPlayer : Player → Player
| Player.X => Player.O
| Player.O => Player.X -- 【LOGIC CORRECTION】Fixed the turn logic for Player O.

/-- Performs a move for the current player at a given position. -/
def move (s : GameState) (p : Pos) : GameState :=
  let b' := place s.board p s.turn
  { board := b', turn := nextPlayer s.turn }

/-- Checks if the game has reached a terminal state (a player has won or the board is full). -/
def isTerminal (s : GameState) : Bool :=
  isWinner s.board Player.X || isWinner s.board Player.O
  || allPositions.all (fun p => s.board p ≠ none)

/-- The starting state of the game. -/
def start : GameState := { board := emptyBoard, turn := Player.X }

-- Demonstrations and tests:
#eval allPositions.length
#eval isTerminal start
#eval start -- This will now pretty-print the initial empty board.

end TicTacToe
