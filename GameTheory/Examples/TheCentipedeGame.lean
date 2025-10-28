import GameTheory.ExtensiveForm.Def

section CentipedeGame

inductive Player | I | II
deriving DecidableEq, Repr

inductive Act | S | C
deriving DecidableEq, Repr

/-- Outcome (payoffs) in thousands of dollars. -/
def Outcome := Int × Int

/--
A game node represents:

the current round (0 ≤ round ≤ 100),

current till holdings (money of I and II),

and whose turn it is (Player I or II).
-/
structure CPNode where
round : ℕ
moneyI : Int
moneyII : Int
turn : Player
ended : Bool
deriving DecidableEq, Repr

/--
At round 0: I has $1000, II has $0.
-/
def root : CPNode := ⟨0, 1000, 0, Player.I, false⟩

/--
Action type (same everywhere): S or C.
-/
def CPAction (_ : CPNode) := Act
instance {n} : Inhabited (CPAction n) := ⟨Act.C⟩

/--
Transition function.
If a player stops → terminal (no more moves).
If continues:

transfers $1000 from current player to the other

game-master adds $2000 to the other’s till

advance round +1

switch turn.
-/
def CP_move (x : CPNode) (a : CPAction x) : CPNode :=
match x.turn, a with
| _, Act.S => x -- stay (terminal will be handled by nodetype)
| Player.I, Act.C =>
{ round := x.round + 1, moneyI := x.moneyI - 1000, moneyII := x.moneyII + 3000, turn := Player.II, ended := false }
| Player.II, Act.C =>
{ round := x.round + 1, moneyI := x.moneyI + 3000, moneyII := x.moneyII - 1000, turn := Player.I, ended := false }

/--
Determine node type:

if action = S, or round ≥ 100 → terminal with current money;

else → current player's move.
-/
def CP_nodetype (x : CPNode) : Player ⊕ Outcome :=
if x.ended then Sum.inr (x.moneyI, x.moneyII)
else if x.round ≥ 100 then Sum.inr (x.moneyI, x.moneyII)
else
match x.turn with
| Player.I => Sum.inl Player.I
| Player.II => Sum.inl Player.II

/--
Build the game space.
-/
def CentipedeSpace : GameSpace Player Outcome :=
{ node := CPNode, action := CPAction, action_intabited := by intro x; apply inferInstance, move := CP_move, nodetype := CP_nodetype }

/--
Perfect-information version (each player knows the state).
-/
def CentipedeGamePerfectInfo : Game Player Outcome :=
CentipedeSpace.toPerfectInformationGame

end CentipedeGame
