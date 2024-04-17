import Mathlib

example : ∀ (n : ℕ ), n + 0 = n := by
  intro x
  rfl
  done

#check Nat.add_succ

example : ∀ (n:ℕ), 0 + n = n:= by
  intro x
  induction x with
  | zero => sorry
  | succ n ih => sorry

example: (R : Type)[CommRing R] (x y z :R) : (x+y)^2= x^2 + y^2 + 2*X*y :=by



example : 1000 < 2 ^ 10 := by
  decide

example : (1000  :ℝ ) < 2 ^ 10 := by
  norm_num
  --for two real number

-- a is a real number, so do
example: (a b: ℝ ) (ha : a > 5 )(h : a < b ) : a ^ 1000 < b ^ (2^10) := by
  calc a ^ 1000 < b ^ 1000 := by gcongr

  calc b ^ 1000 < b ^ (2^10) := by gcongr
  linarith
  norm_num

example: (k : ℕ ) : ∃ p , p.Prime ∧ p ≥ k := by
  let N:= k! + 1 --FACTORIAL + 1
  let p := minFac N
  use p
  constructor
  .--exact?/apply?/
   --ask lean if there are some stuff that i can use
   refine minFac.PRIME ?H/

    --use exact
   sorry
  .sorry
