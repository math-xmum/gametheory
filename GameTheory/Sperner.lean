import Mathlib.Analysis.Convex.SimplicialComplex.Basic

open BigOperators

namespace Geometry

variable (k : Type*) {E : Type*} [DecidableEq E] {ι : Type*} [hLO: LinearOrderedField k] [hCZ: CharZero k] [AddCommGroup E] [Module k E]

local notation "SC" => SimplicialComplex k E

section Subdivision

abbrev barycenter (s : Finset E) : E :=  (s.card:k)⁻¹ • (∑ x in s, x)


@[simp]
abbrev bary_simplex (L : List (Finset E))  : Finset E:= Finset.image (@barycenter k E _ _ _ ) L.toFinset

lemma bary_simplex.nonempty {L : List (Finset E)} (hL : L ≠ []) : (bary_simplex k L)≠ ∅ := by
  intro h
  have := L.toFinset_eq_empty_iff.1 <| Finset.image_eq_empty.mp h
  exact hL this

def chainSet (faces : Set (Finset E)) := {L : List (Finset E)| L≠ [] ∧ L.Forall (fun s => s ∈ faces) ∧   List.Pairwise (fun s t => t.1 ⊂ s.1) L}

--One have to establish vaorious properties of the chainSet


--One have to establish that the barycentric subdivision is a simplicial complex
def barycentric_subdivision (x : SC) : SC where
  faces := Set.image (bary_simplex k)  <| chainSet x.faces
  not_empty_mem := by
    intro ⟨L, ⟨hL1,_⟩,hL2⟩
    have := bary_simplex.nonempty k hL1
    exact this hL2

  indep := by sorry
  down_closed := by sorry
  inter_subset_convexHull := by sorry

end Subdivision

section SimplicialSimplex

class SimplicialSimplex (sc : SimplicialComplex k E) where
  extrema : Finset E
  extrema_in_vertices : extrea ⊆ sc.vertices
  extrema_indep : AffineIndependent k ((↑) : extrema → E)
  spanning : ∀ x:E, x ∈ convexHull k ↑extrema ↔ ∃ s ∈ sc.faces, x ∈ convexHull k s

section SimplicialSimplex

instance  subdivision (sc : SC) [hsc: SimplicialSimplex k sc]: SimplicialSimplex k (barycentric_subdivision k sc) where
  extrema := hsc.extrema
  extrema_in_vertices := by sorry
  extrema_indep := hsc.extrema_indep
  spanning := by sorry

-- TODO: define boundary SimplicialSimplex, show that it is also a SimplicialSimplex

-- TODO: Show that every point in a SimplicialSimplex is a convex combination of its extrema

-- TODO: define the support of a convex combination of the extrema

-- TODO: define proper coloring on a SimplicialSimplex

-- TODO: State the Sperner's Lemma

end SimplicialSimplex

end Geometry
