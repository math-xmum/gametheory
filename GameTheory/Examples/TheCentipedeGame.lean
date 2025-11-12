import GameTheory.ExtensiveForm.Def

section CentipedeGame

/-!
  Finite Centipede Game (bounded rounds).

  说明：
  - round 使用 `Fin 101` 表示 0..100 或 1..100（此处我们把 root 设为 round = 1）。
  - 我把“100”抽出成 `hundred` 以便复用和提高可读性。
  - 使用 `Int` 表示 money，避免 ℕ 的下溢问题。
-/

inductive Player | I | II
  deriving DecidableEq, Repr

inductive Act | S | C
  deriving DecidableEq, Repr

/-- Outcome (payoffs) in thousands of dollars. -/
def Outcome := Int × Int

/--
  节点：round 被限制为 Fin 101（值域 0..100），
  moneyI / moneyII 为 Int（允许表示任意整数以避免下溢陷阱），
  turn 表示谁行动，ended 表示是否已有人选择 Stop。
  Root 我们设为 round = 1（参见 root 的定义）。
-/
structure CPNodeBounded where
  round : Fin 101
  moneyI : Int
  moneyII : Int
  turn : Player
  ended : Bool
deriving DecidableEq, Repr

/-- `hundred` 表示 Fin 101 中的 100（方便复用与注释） -/
def hundred : Fin 101 := ⟨100, by decide⟩

/-- Root: 从 round = 1 开始，I 有 1000, II 有 0, 游戏未结束 -/
def root : CPNodeBounded := ⟨⟨1, by decide⟩, 1000, 0, Player.I, false⟩

/-- 全节点动作类型（S 或 C） -/
def CPActionBounded (_ : CPNodeBounded) := Act
instance {n} : Nonempty (CPActionBounded n) := ⟨Act.C⟩

/-- 安全地对 `Fin 101` 加 1：如果已经是 100，则保持 100（避免模回到 0） -/
def nextRound (r : Fin 101) : Fin 101 :=
  if h : (r.val < 100) then
    ⟨r.val + 1, by
      have H1 : r.val + 1 ≤ 100 := Nat.succ_le_of_lt h
      exact Nat.lt_of_le_of_lt H1 (by decide)⟩
  else
    ⟨100, by decide⟩

/-- Transition：S 标为 ended，C 做资金转移并 nextRound、换手。 -/
def CP_moveBounded (x : CPNodeBounded) (a : CPActionBounded x) : CPNodeBounded :=
  match x.turn, a with
  | _, Act.S =>
    { x with ended := true }
  | Player.I, Act.C =>
    { round := nextRound x.round,
      moneyI := x.moneyI - 1000,
      moneyII := x.moneyII + 3000,
      turn := Player.II,
      ended := false }
  | Player.II, Act.C =>
    { round := nextRound x.round,
      moneyI := x.moneyI + 3000,
      moneyII := x.moneyII - 1000,
      turn := Player.I,
      ended := false }

/-- Node type：如果 ended 或已到 round = 100 则终端并返回 payoff，否则返回当前行动玩家 -/
def CP_nodetypeBounded (x : CPNodeBounded) : Player ⊕ Outcome :=
  if x.ended then Sum.inr (x.moneyI, x.moneyII)
  else if x.round = hundred then Sum.inr (x.moneyI, x.moneyII)
  else
    match x.turn with
    | Player.I => Sum.inl Player.I
    | Player.II => Sum.inl Player.II

/-- Build GameSpace instance -/
def CentipedeSpace : GameSpace Player Outcome where
  node := CPNodeBounded
  action := CPActionBounded
  action_intabited := fun _ => Nonempty.intro Act.C
  move := CP_moveBounded
  nodetype := CP_nodetypeBounded

/--
Perfect-information version (each player knows the state).
-/
def CentipedeGamePerfectInfo : Game Player Outcome :=
  CentipedeSpace.toPerfectInformationGame

end CentipedeGame

open Sum

/-- For concreteness, a simple Strategy type is (x -> action x) -/
abbrev CPStrategy := (x : CPNodeBounded) -> CPActionBounded x

/-- Iterative play with fuel: sI for Player I, sII for Player II -/
def iter_play : ℕ → CPStrategy → CPStrategy → CPNodeBounded → CPNodeBounded
| 0,   _, _, x => x
| (k+1), sI, sII, x =>
  match CP_nodetypeBounded x with
  | inr _ => x
  | inl Player.I => iter_play k sI sII (CP_moveBounded x (sI x))
  | inl Player.II => iter_play k sI sII (CP_moveBounded x (sII x))

/-- Play from root with upper bound 101 -/
def play_under_profile (sI : CPStrategy) (sII : CPStrategy) : CPNodeBounded :=
  iter_play 101 sI sII root

/-- payoff of a profile (uses play_under_profile) -/
def payoff_of_profile (sI : CPStrategy) (sII : CPStrategy) : Outcome :=
  match CP_nodetypeBounded (play_under_profile sI sII) with
  | inr o => o
  | inl _ => (0, 0)

/-- payoff from an arbitrary starting node x under profile (sI, sII) -/
def payoff_from_node (sI : CPStrategy) (sII : CPStrategy) (x : CPNodeBounded) : Outcome :=
  match CP_nodetypeBounded (iter_play 101 sI sII x) with
  | inr o => o
  | inl _ => (0, 0)

/-- Always-stop strategies -/
def always_stop_I : CPStrategy := fun _ => Act.S
def always_stop_II : CPStrategy := fun _ => Act.S

def profile_all_stop_I := always_stop_I
def profile_all_stop_II := always_stop_II

/-
  Helpful lemmas about single-step moves
-/
theorem I_play_S_then_terminal (x : CPNodeBounded) :
  CP_nodetypeBounded (CP_moveBounded x Act.S) = inr (x.moneyI, x.moneyII) := by
  simp [CP_moveBounded, CP_nodetypeBounded]

theorem II_play_S_then_terminal (x : CPNodeBounded) :
  CP_nodetypeBounded (CP_moveBounded x Act.S) = inr (x.moneyI, x.moneyII) := by
  simp [CP_moveBounded, CP_nodetypeBounded]

theorem I_play_C_description (x : CPNodeBounded) (h : x.turn = Player.I) :
  (CP_moveBounded x Act.C).moneyI = x.moneyI - 1000 ∧
  (CP_moveBounded x Act.C).moneyII = x.moneyII + 3000 ∧
  (CP_moveBounded x Act.C).turn = Player.II := by
  simp [CP_moveBounded]
  constructor; rfl; constructor; rfl; rfl


theorem II_play_C_description (x : CPNodeBounded) :
  let x' := CP_moveBounded x Act.C in
  x'.moneyI = x.moneyI + 3000 ∧ x'.moneyII = x.moneyII - 1000 ∧ x'.turn = Player.I := by
  simp [CP_moveBounded]; constructor; rfl; constructor; rfl; rfl

/-
  Key lemma: at any I-node x, if II plays always_stop, then any deviation by I cannot
  strictly increase I's payoff (the first component).
-/
theorem I_cannot_gain_by_deviating_from_stop_at_node (x : CPNodeBounded)
  (h : CP_nodetypeBounded x = inl Player.I) (s : CPStrategy) :
  (payoff_from_node s profile_all_stop_II x).1 ≤ (payoff_from_node profile_all_stop_I profile_all_stop_II x).1 := by
  let a := s x
  cases a
  -- Case a = Act.S: identical immediate behavior
  ·
    have L1 : iter_play 101 s profile_all_stop_II x = iter_play 100 s profile_all_stop_II (CP_moveBounded x Act.S) := by
      simp [iter_play, h]
    have L2 : iter_play 101 profile_all_stop_I profile_all_stop_II x = iter_play 100 profile_all_stop_I profile_all_stop_II (CP_moveBounded x Act.S) := by
      simp [iter_play, h]
    have CONT : iter_play 100 s profile_all_stop_II (CP_moveBounded x Act.S) =
                iter_play 100 profile_all_stop_I profile_all_stop_II (CP_moveBounded x Act.S) := by rfl
    calc
      (payoff_from_node s profile_all_stop_II x).1
        = match CP_nodetypeBounded (iter_play 101 s profile_all_stop_II x) with | inr o => o.1 | inl _ => 0 := by rfl
      _ = match CP_nodetypeBounded (iter_play 100 s profile_all_stop_II (CP_moveBounded x Act.S)) with | inr o => o.1 | inl _ => 0 := by rw [L1]
      _ = match CP_nodetypeBounded (iter_play 100 profile_all_stop_I profile_all_stop_II (CP_moveBounded x Act.S)) with | inr o => o.1 | inl _ => 0 := by rw [CONT]
      _ = (payoff_from_node profile_all_stop_I profile_all_stop_II x).1 := by rw [L2]

  -- Case a = Act.C: after C, II will play S (profile_all_stop_II), so I's payoff is x.moneyI - 1000
  ·
    let x1 := CP_moveBounded x Act.C
    cases hnd : CP_nodetypeBounded x1
    · -- x1 terminal
      have Step : iter_play 101 s profile_all_stop_II x = iter_play 100 s profile_all_stop_II x1 := by simp [iter_play, h]
      have TerminalStep : iter_play 100 s profile_all_stop_II x1 = x1 := by simp [iter_play, hnd]
      calc
        (payoff_from_node s profile_all_stop_II x).1
          = match CP_nodetypeBounded (iter_play 101 s profile_all_stop_II x) with | inr o => o.1 | inl _ => 0 := by rfl
        _ = match CP_nodetypeBounded (iter_play 100 s profile_all_stop_II x1) with | inr o => o.1 | inl _ => 0 := by rw [Step]
        _ = (x1.moneyI : Int) := by rw [TerminalStep]; simp [CP_nodetypeBounded, hnd]
        _ = x.moneyI - 1000 := by
          have desc := I_play_C_description x
          dsimp at desc
          cases desc with hmi hrest; exact hmi
        _ ≤ x.moneyI := by apply Int.sub_le_self

    · -- x1 not terminal (hnd = inl _), then II will play S next and make terminal
      have node_x1_is_inl := hnd
      have desc := I_play_C_description x
      dsimp at desc
      cases desc with hmi hrest
      cases hrest with hmii hturn
      have Next : iter_play 100 s profile_all_stop_II x1 = iter_play 99 s profile_all_stop_II (CP_moveBounded x1 Act.S) := by
        simp [iter_play, node_x1_is_inl]
      have TermNode : CP_nodetypeBounded (CP_moveBounded x1 Act.S) = inr (x1.moneyI, x1.moneyII) := by
        have : CP_moveBounded x1 Act.S = { x1 with ended := true } := by rfl
        simp [this, CP_nodetypeBounded]
      have FinalStep : iter_play 99 s profile_all_stop_II (CP_moveBounded x1 Act.S) = CP_moveBounded x1 Act.S := by simp [iter_play, TermNode]
      calc
        (payoff_from_node s profile_all_stop_II x).1
          = match CP_nodetypeBounded (iter_play 101 s profile_all_stop_II x) with | inr o => o.1 | inl _ => 0 := by rfl
        _ = match CP_nodetypeBounded (iter_play 100 s profile_all_stop_II x1) with | inr o => o.1 | inl _ => 0 := by simp [iter_play, h]
        _ = match CP_nodetypeBounded (iter_play 99 s profile_all_stop_II (CP_moveBounded x1 Act.S)) with | inr o => o.1 | inl _ => 0 := by rw [Next]
        _ = (x1.moneyI : Int) := by
          rw [FinalStep]; simp [CP_nodetypeBounded, TermNode]
        _ = x.moneyI - 1000 := by exact hmi
        _ ≤ x.moneyI := by apply Int.sub_le_self

/-
  Mirror lemma for Player.II: at any II-node x, if I plays always_stop, then any deviation by II
  cannot strictly increase II's payoff (the second component).
-/
theorem II_cannot_gain_by_deviating_from_stop_at_node (x : CPNodeBounded)
  (h : CP_nodetypeBounded x = inl Player.II) (s : CPStrategy) :
  (payoff_from_node profile_all_stop_I s x).2 ≤ (payoff_from_node profile_all_stop_I profile_all_stop_II x).2 := by
  let a := s x
  cases a
  -- a = S
  ·
    have L1 : iter_play 101 profile_all_stop_I s x = iter_play 100 profile_all_stop_I s (CP_moveBounded x Act.S) := by simp [iter_play, h]
    have L2 : iter_play 101 profile_all_stop_I profile_all_stop_II x = iter_play 100 profile_all_stop_I profile_all_stop_II (CP_moveBounded x Act.S) := by simp [iter_play, h]
    have CONT : iter_play 100 profile_all_stop_I s (CP_moveBounded x Act.S) =
                iter_play 100 profile_all_stop_I profile_all_stop_II (CP_moveBounded x Act.S) := by rfl
    calc
      (payoff_from_node profile_all_stop_I s x).2
        = match CP_nodetypeBounded (iter_play 101 profile_all_stop_I s x) with | inr o => o.2 | inl _ => 0 := by rfl
      _ = match CP_nodetypeBounded (iter_play 100 profile_all_stop_I s (CP_moveBounded x Act.S)) with | inr o => o.2 | inl _ => 0 := by rw [L1]
      _ = match CP_nodetypeBounded (iter_play 100 profile_all_stop_I profile_all_stop_II (CP_moveBounded x Act.S)) with | inr o => o.2 | inl _ => 0 := by rw [CONT]
      _ = (payoff_from_node profile_all_stop_I profile_all_stop_II x).2 := by rw [L2]

  -- a = C
  ·
    let x1 := CP_moveBounded x Act.C
    cases hnd : CP_nodetypeBounded x1
    · -- x1 terminal
      have Step : iter_play 101 profile_all_stop_I s x = iter_play 100 profile_all_stop_I s x1 := by simp [iter_play, h]
      have TerminalStep : iter_play 100 profile_all_stop_I s x1 = x1 := by simp [iter_play, hnd]
      calc
        (payoff_from_node profile_all_stop_I s x).2
          = match CP_nodetypeBounded (iter_play 101 profile_all_stop_I s x) with | inr o => o.2 | inl _ => 0 := by rfl
        _ = match CP_nodetypeBounded (iter_play 100 profile_all_stop_I s x1) with | inr o => o.2 | inl _ => 0 := by rw [Step]
        _ = (x1.moneyII : Int) := by rw [TerminalStep]; simp [CP_nodetypeBounded, hnd]
        _ = x.moneyII - 1000 := by
          have desc := II_play_C_description x
          dsimp at desc; cases desc with hm1 hrest; cases hrest with hm2 hturn; exact hm2
        _ ≤ x.moneyII := by apply Int.sub_le_self
    · -- x1 not terminal -> now x1 is I-node, I will then play S
      have desc := II_play_C_description x
      dsimp at desc; cases desc with hm1 hrest; cases hrest with hm2 hturn
      have Next : iter_play 100 profile_all_stop_I s x1 = iter_play 99 profile_all_stop_I s (CP_moveBounded x1 Act.S) := by simp [iter_play, hnd]
      have TermNode : CP_nodetypeBounded (CP_moveBounded x1 Act.S) = inr (x1.moneyI, x1.moneyII) := by
        have : CP_moveBounded x1 Act.S = { x1 with ended := true } := by rfl
        simp [this, CP_nodetypeBounded]
      have FinalStep : iter_play 99 profile_all_stop_I s (CP_moveBounded x1 Act.S) = CP_moveBounded x1 Act.S := by simp [iter_play, TermNode]
      calc
        (payoff_from_node profile_all_stop_I s x).2
          = match CP_nodetypeBounded (iter_play 101 profile_all_stop_I s x) with | inr o => o.2 | inl _ => 0 := by rfl
        _ = match CP_nodetypeBounded (iter_play 100 profile_all_stop_I s x1) with | inr o => o.2 | inl _ => 0 := by simp [iter_play, h]
        _ = match CP_nodetypeBounded (iter_play 99 profile_all_stop_I s (CP_moveBounded x1 Act.S)) with | inr o => o.2 | inl _ => 0 := by rw [Next]
        _ = x1.moneyII := by rw [FinalStep]; simp [CP_nodetypeBounded, TermNode]
        _ = x.moneyII - 1000 := by exact hm2
        _ ≤ x.moneyII := by apply Int.sub_le_self

/- Final SPE theorem -/
theorem profile_all_stop_is_SPE :
  ∀ x : CPNodeBounded,
    match CP_nodetypeBounded x with
    | inr _ => True
    | inl Player.I => ∀ s : CPStrategy, (payoff_from_node s profile_all_stop_II x).1 ≤ (payoff_from_node profile_all_stop_I profile_all_stop_II x).1
    | inl Player.II => ∀ s : CPStrategy, (payoff_from_node profile_all_stop_I s x).2 ≤ (payoff_from_node profile_all_stop_I profile_all_stop_II x).2 := by
  intro x
  match CP_nodetypeBounded x with
  | inr _ => trivial
  | inl Player.I => intro s; apply I_cannot_gain_by_deviating_from_stop_at_node x rfl s
  | inl Player.II => intro s; apply II_cannot_gain_by_deviating_from_stop_at_node x rfl s
