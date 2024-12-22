import Mathlib.Analysis.Convex.SimplicialComplex.Basic

open BigOperators
open Classical


namespace Geometry
open SimplicialComplex

variable (k : Type*) {E : Type*} {ι : Type*} [hLO: LinearOrderedField k]  [AddCommGroup E] [Module k E]

local notation "SC" => SimplicialComplex k E

noncomputable section Subdivision
variable [hCZ: CharZero k]

abbrev barycenter (s : Finset E) : E :=  (s.card:k)⁻¹ • (∑ x in s, x)


@[simp]
abbrev bary_simplex (L : List (Finset E))  : Finset E:= Finset.image (@barycenter k E _ _ _ ) L.toFinset

lemma bary_simplex.nonempty {L : List (Finset E)} (hL : L ≠ []) : (bary_simplex k L)≠ ∅ := by
  intro h
  have := L.toFinset_eq_empty_iff.1 <| Finset.image_eq_empty.mp h
  exact hL this

def chainSet (faces : Set (Finset E)) := {L : List (Finset E)| L≠ [] ∧ L.Forall (fun s => s ∈ faces) ∧   List.Pairwise (fun s t => t.1 ⊂ s.1) L}

--One have to establish various properties of the chainSet


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


class SimplicialSimplex (sc : SimplicialComplex k E) where
  extremes : Finset E
  extreme_in_vertices : ↑extremes ⊆ sc.vertices
  extreme_indep : AffineIndependent k (Subtype.val : extremes → E)
  spanning : ∀ x:E, x ∈ convexHull k ↑extremes ↔ ∃ s ∈ sc.faces, x ∈ convexHull k s

namespace SimplicialSimplex

instance  subdivision (sc : SC) [hsc: SimplicialSimplex k sc]: SimplicialSimplex k (barycentric_subdivision k sc) where
  extremes := hsc.extremes
  extreme_in_vertices := by sorry
  extreme_indep := hsc.extreme_indep
  spanning := by sorry




noncomputable section support
-- Suppose t is a set of points, x is in the convexHull of t
-- define the support of x to be the smallest subset of t such that x in the convexHull of t.

abbrev Support (t: Finset E) (x : E) : Set E :=
  if x ∈ convexHull k ↑t then
    ⋂ s ∈ { s | s ⊆ t ∧  x ∈ convexHull k s}, s
  else
    ∅


/-
Show that support is a subset of t if x is contained in
the convexHull of t
-/
lemma support_subset_face {t: Finset E} {x : E} : Support k t x ⊆ t:= by
  unfold Support
  split_ifs
  · apply Set.biInter_subset_of_mem
    constructor
    · simp only [subset_refl]
    · assumption
  · apply Set.empty_subset

instance support.fintype {t: Finset E} {x : E}: Fintype (Support k t x) := by
  let s := {e ∈ t | e ∈ Support k t x}
  apply Fintype.ofFinset s
  intro e
  rw [Finset.mem_filter]
  constructor
  · intro h; exact h.2
  · intro hx; exact ⟨support_subset_face k hx,hx⟩

abbrev Support' (t: Finset E) (x : E) : Finset E := Support k t x |>.toFinset

/-
Show that support is a subset of t if x is contained in
the convexHull of t
-/

lemma mem_convexHullsupport {t: Finset E} {x : E}
  (h1: x ∈ convexHull k ↑t)
  (h2 : AffineIndependent k ((↑):t → E)):
   x ∈ convexHull k (Support k t x):= by
   unfold Support
   simp only [h1, if_true]
   let S := {s | s ⊆ t ∧ x ∈ convexHull k ↑s}
   have hS_nonempty : S.Nonempty := ⟨t, subset_refl _, h1⟩



end support

variable {k} in
abbrev Coloring (sc : SimplicialComplex k E) (ι : Type*) := sc.vertices → ι

variable {k} in
def ProperColoring {sc : SimplicialComplex k E} [ss : SimplicialSimplex k sc] (c : Coloring sc E) :=
  ∀ x : sc.vertices, c x ∈ Support k ss.extremes x

variable {sc : SimplicialComplex k E}

section restriction

variable {α β : Type*} {s t: Set α} (h : s ⊆ t)

def res  (f : t→ β) : s → β := fun s => f ⟨s.1,h s.2 ⟩

lemma res_def : res h f x = f ⟨x.1, h x.2⟩ := rfl



end restriction


def iota (f : sc.faces) : f.1 → sc.vertices :=
  fun x => ⟨x.1, by
    rw [Geometry.SimplicialComplex.vertices_eq]
    have :∃ i ∈ sc.faces, ↑x ∈ i := by
      use f.1; exact ⟨f.2,x.2⟩
    simp [this]
    ⟩

variable {k} in
lemma faces_subset_vertices (f : sc.faces) : ↑f.1 ⊆ sc.vertices
  := by
    rw [Geometry.SimplicialComplex.vertices_eq]
    intro x hx
    have :∃ i ∈ sc.faces, ↑x ∈ i := by
      use f.1; exact ⟨f.2,hx⟩
    simp [this]


variable {k} in
def res_coloring (c : Coloring sc ι) (f : sc.faces) : f.1 → ι
  := res (faces_subset_vertices f: ↑f.1 ⊆ sc.vertices) c

variable [ss : SimplicialSimplex k sc]

variable {k} in
def Rainbowfacet  (c : Coloring sc E) (f : sc.facets)
 := res_coloring c ⟨f.1, facets_subset
 f.2⟩  '' Set.univ  = ss.extremes

section non_branching_theorem
  variable {n : ℕ} -- dimension
  variable (T : Type*) [TopologicalSpace T] -- topological space
  variable (τ : Simplex (n-1) T) -- (n-1)-simplex
  variable (δ : Simplex n T) -- n-simplex
  variable (δᵢ : Simplex n T) -- indexed n-simplex

  /-- Non-branching property: If τ is an (n-1)-simplex of T, then either τ is contained
      in the boundary of δ and then τ is contained in some δᵢ, or τ is not contained
      in the boundary of δ. -/
  theorem non_branching_property :
    (τ ⊆ Simplex.boundary δ → ∃ i, τ ⊆ δᵢ) ∧
    (τ ⊈ Simplex.boundary δ) :=
  sorry

end non_branching_theorem

theorem Sperner {c : Coloring sc E} (h : ProperColoring c) : ∃ f : sc.facets, Rainbowfacet c f := sorry

/-- The boundary of a SimplicialSimplex is the subcomplex consisting of all proper faces. -/
def boundary (sc : SC) [ss : SimplicialSimplex k sc] : SC where
  faces := {s ∈ sc.faces | s ⊂ ss.extremes}
  not_empty_mem := by
    rintro ⟨s, hs, hss⟩
    exact sc.not_empty_mem hs
  indep := by
    rintro s ⟨hs, _⟩
    exact sc.indep hs
  down_closed := by
    rintro t s ⟨hs, hss⟩ hts
    refine ⟨sc.down_closed hs hts, ?_⟩
    exact Finset.subset_trans hts hss
  inter_subset_convexHull := by
    rintro s t ⟨hs, _⟩ ⟨ht, _⟩
    exact sc.inter_subset_convexHull hs ht

namespace SimplicialSimplex

-- TODO: define boundary SimplicialSimplex, show that it is also a SimplicialSimplex

-- TODO: Show that every point in a SimplicialSimplex is a convex combination of its extrema

-- TODO: define the support of a convex combination of the extrema

-- TODO: define proper coloring on a SimplicialSimplex




end SimplicialSimplex




end Geometry


section Sperner


-- Define the notion of coloring.



-- TODO: State the Sperner's Lemma


end Sperner
