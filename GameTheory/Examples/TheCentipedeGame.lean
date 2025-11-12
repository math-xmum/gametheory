import GameTheory.ExtensiveForm.Def

section CentipedeGame

/-!
  Finite Centipede Game (n rounds).

  Description:
  - round uses `Fin (n+1)` to represent 0..n (here we set root as round = 1).
  - Uses `Int` for money to avoid underflow issues with ℕ.
-/

inductive Player | I | II
  deriving DecidableEq, Repr

inductive Act | S | C
  deriving DecidableEq, Repr

/-- Outcome (payoffs) in thousands of dollars. -/
def Outcome := Int × Int

/--
  Node: round is restricted to Fin (n+1) (range 0..n),
  moneyI / moneyII are Int (to allow representing any integer and avoid underflow),
  turn indicates whose turn it is, ended indicates if someone has chosen Stop.
  Root is set as round = 1 (see root definition).
-/
structure CPNode (n : ℕ) where
  round : Fin (n + 1)
  moneyI : Int
  moneyII : Int
  turn : Player
  ended : Bool
deriving DecidableEq, Repr

/-- Get the Fin value corresponding to the maximum round -/
def maxRound {n : ℕ} : Fin (n + 1) := ⟨n, Nat.lt_succ_of_le (Nat.le_refl n)⟩

/-- Root: starts at round = 1, I has 1, II has 0, game not ended (amounts in thousands of dollars) -/
def root (n : ℕ) (h : 1 < n + 1 := by omega) : CPNode n :=
  ⟨⟨1, h⟩, 1, 0, Player.I, false⟩

/-- Action type for all nodes (S or C) -/
def CPAction {n : ℕ} (_ : CPNode n) := Act
instance {n : ℕ} : ∀ x : CPNode n, Nonempty (CPAction x) := fun _ => ⟨Act.C⟩

/-- Safely increment `Fin (n+1)` by 1: if already at n, stay at n (avoid wrapping back to 0) -/
def nextRound {n : ℕ} (r : Fin (n + 1)) : Fin (n + 1) :=
  if h : (r.val < n) then
    ⟨r.val + 1, by
      have H1 : r.val + 1 ≤ n := Nat.succ_le_of_lt h
      exact Nat.lt_succ_of_le H1⟩
  else
    ⟨n, by simp⟩

/--
  Transition:
  - S marks as ended
  - C transfers money (in thousands) and goes to nextRound, switches turn
  Player I pays 1 (thousand) to give 3 (thousand) to Player II, and vice versa
-/
def CP_move {n : ℕ} (x : CPNode n) (a : CPAction x) : CPNode n :=
  match x.turn, a with
  | _, Act.S =>
    { x with ended := true }
  | Player.I, Act.C =>
    { round := nextRound x.round,
      moneyI := x.moneyI - 1,
      moneyII := x.moneyII + 3,
      turn := Player.II,
      ended := false }
  | Player.II, Act.C =>
    { round := nextRound x.round,
      moneyI := x.moneyI + 3,
      moneyII := x.moneyII - 1,
      turn := Player.I,
      ended := false }

/-- Node type: if ended or reached round = n then terminal and return payoff, else return current acting player -/
def CP_nodetype {n : ℕ} (x : CPNode n) : Player ⊕ Outcome :=
  if x.ended then Sum.inr (x.moneyI, x.moneyII)
  else if x.round = maxRound then Sum.inr (x.moneyI, x.moneyII)
  else
    match x.turn with
    | Player.I => Sum.inl Player.I
    | Player.II => Sum.inl Player.II

/-- Build GameSpace instance -/
def CentipedeSpace (n : ℕ) : GameSpace Player Outcome where
  node := CPNode n
  action := CPAction
  action_intabited := fun _ => Nonempty.intro Act.C
  move := CP_move
  nodetype := CP_nodetype

/--
Perfect-information version (each player knows the state).
-/
def CentipedeGamePerfectInfo (n : ℕ) : Game Player Outcome :=
  (CentipedeSpace n).toPerfectInformationGame

end CentipedeGame
