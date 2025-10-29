import Mathlib.Tactic
import Mathlib.Data.List.Range
import GameTheory.ExtensiveForm.Def

-- The entire model is defined within a `section` environment, parameterized by the board dimensions `m`, `n`, and the winning condition `k`.
section MnkGame

-- We declare m, n, k, and the assumption that they must be positive integers, as variables for this section.
variable {m n k : Nat}
variable (hm_pos : m > 0) (hn_pos : n > 0) (hk_pos : k > 0)

/-- Defines a position on an m x n board as an alias for a tuple of finite numbers. -/
abbrev Pos (m n : Nat) := Fin m × Fin n

/-- Provides a printing instance for the position type that depends on m and n. -/
instance : Repr (@Pos m n) where
  reprPrec p _ :=
    let (i, j) := p
    s!"({i.val}, {j.val})"

/-- The Player type remains unchanged as it is independent of the board size. -/
inductive Player
| X | O
deriving DecidableEq, Repr

/-- The Board is defined as a function from a position to an optional player. -/
def Board : Type := (@Pos m n) → Option Player

/-- The 'pretty-printing' instance for the board now uses the variables m and n. -/
instance : Repr (@Board m n) where
  reprPrec b _ :=
    let rows := (List.finRange m).map fun i =>
      let row := (List.finRange n).map fun j =>
        match b (i, j) with
        | some Player.X => "X"
        | some Player.O => "O"
        | none => "."
      String.intercalate " " row
    String.intercalate "\n" rows

/-- The initial empty board. Its type depends on m and n. -/
def emptyBoard : @Board m n := fun _ => none

/-- Checks if a square is empty. -/
def isEmpty (b : @Board m n) (p : @Pos m n) : Bool :=
  b p == none

/-- Places a player's piece on the board. -/
def place (b : @Board m n) (p : @Pos m n) (pl : Player) : @Board m n :=
  if b p == none then
    fun q => if q = p then some pl else b q
  else
    b

/-- A list containing all m*n positions on the board. -/
def allPositions : List (@Pos m n) :=
  (List.finRange m).flatMap fun i =>
  (List.finRange n).map fun j => (i, j)

/-- Generates all winning lines of length `k` for a generic `m x n` board. -/
def winningLines : List (List (@Pos m n)) :=
  let h_lines :=
    (List.finRange m).flatMap fun (i : Fin m) =>
    (List.finRange n).flatMap fun (j : Fin n) =>
      if h_j_bound : j.val + k ≤ n then
        [ (List.finRange k).map fun (ki : Fin k) =>
            let new_j := j.val + ki.val
            have h_new_j_lt_n : new_j < n :=
              Nat.lt_of_lt_of_le (Nat.add_lt_add_left ki.isLt j.val) h_j_bound
            (i, ⟨new_j, h_new_j_lt_n⟩)
        ]
      else []

  let v_lines :=
    (List.finRange m).flatMap fun (i : Fin m) =>
    (List.finRange n).flatMap fun (j : Fin n) =>
      if h_i_bound : i.val + k ≤ m then
        [ (List.finRange k).map fun (ki : Fin k) =>
            let new_i := i.val + ki.val
            have h_new_i_lt_m : new_i < m :=
              Nat.lt_of_lt_of_le (Nat.add_lt_add_left ki.isLt i.val) h_i_bound
            (⟨new_i, h_new_i_lt_m⟩, j)
        ]
      else []

  let d1_lines :=
    (List.finRange m).flatMap fun (i : Fin m) =>
    (List.finRange n).flatMap fun (j : Fin n) =>
      if h_bounds : i.val + k ≤ m ∧ j.val + k ≤ n then
        [ (List.finRange k).map fun (ki : Fin k) =>
            let new_i := i.val + ki.val
            let new_j := j.val + ki.val
            have h_new_i_lt_m : new_i < m :=
              Nat.lt_of_lt_of_le (Nat.add_lt_add_left ki.isLt i.val) h_bounds.1
            have h_new_j_lt_n : new_j < n :=
              Nat.lt_of_lt_of_le (Nat.add_lt_add_left ki.isLt j.val) h_bounds.2
            (⟨new_i, h_new_i_lt_m⟩, ⟨new_j, h_new_j_lt_n⟩)
        ]
      else []

  let d2_lines :=
    (List.finRange m).flatMap fun (i : Fin m) =>
    (List.finRange n).flatMap fun (j : Fin n) =>
      if h_bounds : i.val + k ≤ m ∧ j.val + 1 ≥ k then
        [ (List.finRange k).map fun (ki : Fin k) =>
            let new_i := i.val + ki.val
            have : j.val ≥ ki.val :=
              Nat.le_of_lt_succ (Nat.lt_of_lt_of_le ki.isLt h_bounds.2)
            let new_j := j.val - ki.val
            have h_new_i_lt_m : new_i < m :=
              Nat.lt_of_lt_of_le (Nat.add_lt_add_left ki.isLt i.val) h_bounds.1
            have h_new_j_lt_n : new_j < n :=
              Nat.lt_of_le_of_lt (Nat.sub_le j.val ki.val) j.isLt
            (⟨new_i, h_new_i_lt_m⟩, ⟨new_j, h_new_j_lt_n⟩)
        ]
      else []

  h_lines ++ v_lines ++ d1_lines ++ d2_lines

/-- The game state, which automatically depends on m and n from the section. -/
structure GameState where
  board : @Board m n
  turn  : Player
deriving Repr

/-- Checks if a player has won. -/
def isWinner (b : @Board m n) (pl : Player) : Bool :=
  List.any (@winningLines m n k) fun line =>
    let marksOnLine := line.map fun pos => b pos
    (marksOnLine.takeWhile (· = some pl)).length = k

/-- Switches the player, an operation independent of the board size. -/
def nextPlayer : Player → Player
| Player.X => Player.O
| Player.O => Player.X

/-- Executes a move. -/
def move (s : @GameState m n) (p : @Pos m n) : @GameState m n :=
  let b' := place s.board p s.turn
  { board := b', turn := nextPlayer s.turn }

/-- Checks if the game has reached a terminal state. -/
def isTerminal (s : @GameState m n) : Bool :=
  @isWinner m n k s.board Player.X ∨
  @isWinner m n k s.board Player.O ∨
  (@allPositions m n).all (fun p => (s.board p).isSome)

/-- The initial state for any m x n board. -/
def start : @GameState m n :=
  { board := emptyBoard, turn := Player.X }

end MnkGame
