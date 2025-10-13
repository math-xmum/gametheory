import GameTheory.StrategicForm.Def


section NashTheorem

namespace StrategicGame
variable {Player Outcome : Type*} [DecidableEq Player] (G : StrategicGame Player Outcome) [Fintype Player] (hG : G.isFintypeStrategy)


variable {k : Type*} [Semiring k] [CommMonoid k] [PartialOrder k]

variable (payoff : Outcome → k)

instance instfintype : Fintype ((j:Player) → G.Strategy j) :=
  @Pi.instFintype Player G.Strategy _ _ hG

def toMixedGame : StrategicGame Player k :=
  let pureStrategy_fintype := G.instfintype hG
  {
  Strategy := fun i => @stdSimplex k (G.Strategy i) _ _ (hG i)
  strategy_nonempty := fun i => sorry
  outcome := fun i => fun m => ∑ (s : (j:Player)→ G.Strategy j), (∏ (j:Player), m j (s j)) * payoff (G.outcome i s)
  }

theorem Nash_Theorem : ∃ x,  (G.toMixedGame hG payoff).NashEquilibrium id x := sorry

end StrategicGame



end NashTheorem
