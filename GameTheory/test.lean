import Mathlib

open List Rat


theorem maxval' :
  let f : List ℕ → ℚ := fun x => ((x.getD 1 0 + x.getD 3 0 + x.getD 5 0)*10 + (x.getD 0 0 + x.getD 2 0 + x.getD 4 0) : ℚ)/(((x.getD 7 0:ℚ) -x.getD 9 0)*10 + (x.getD 6 0:ℚ) - (x.getD 8 0)) ;
   (foldl (fun x y => x ⊔ f y) 0 <| (List.filter (fun (x:List ℕ) => x.getD 1 0 ≠ 0 ∧ x.getD 3 0 ≠ 0 ∧ x.getD 5 0 ≠ 0 ∧ x.getD 7 0 ≠ 0 ∧ x.getD 9 0 ≠ 0) <| (permutations (range 10)))) = (222:ℚ) := by
   native_decide
