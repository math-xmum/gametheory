import Mathlib

open BigOperators
open Classical
open Set

noncomputable section

/-
Note that the simplex must be at least dimension 1
so we include the assumption that ι is non-trivial
-/
variable {k : Type*} {ι : Type*} [Fintype ι] [Nontrivial ι] [Field k] [LinearOrder k]
[IsStrictOrderedRing k] [DecidableEq ι] [DecidableEq k]


namespace Geometry
open SimplicialComplex


namespace SimplicialComplex

variable {k E : Type*} {ι : Type*} [Ring k] [PartialOrder k] [IsOrderedRing k] [AddCommGroup E] [Module k E]

variable {sc : SimplicialComplex k E}

def iota_aux (f : sc.faces) : f.1 → sc.vertices :=
  fun x => ⟨x.1, by
    rw [Geometry.SimplicialComplex.vertices_eq]
    have :∃ i ∈ sc.faces, ↑x ∈ i := by
      use f.1; exact ⟨f.2,x.2⟩
    simp [this]
    ⟩

def iota (f : sc.faces) : f.1 ↪ sc.vertices where
  toFun := iota_aux f
  inj' := by
    intro x y;simp only [iota_aux, Subtype.mk.injEq];intro; ext;assumption


end SimplicialComplex





/- We only treat the standard simplex case-/

class SimplicialSimplex (sc : SimplicialComplex k (ι→k)) where
  finite : Fintype sc.faces
  spanning : x ∈ stdSimplex k ι ↔ ∃ s ∈ sc.faces, x ∈ convexHull k s

attribute [instance] SimplicialSimplex.finite

variable (sc : SimplicialComplex k (ι→k)) [hss : SimplicialSimplex sc]

local notation "E" => (ι→k)

/-- Support is of an element x is the subset of basis with nonzero coefficeints --/
abbrev Support (x : E) : Finset ι:= Finset.filter (x · ≠ 0) (Finset.univ : Finset ι)

/- Support of a finite set in E is the union of the support of points in E-/
abbrev FSupport (f : Finset E) : Finset ι := Finset.biUnion f Support

namespace SimplicialSimplex

abbrev Coloring  := sc.vertices → ι

variable (c : Coloring sc)

variable {sc}

def Coloring.Proper :=
  ∀ x : sc.vertices, c x ∈ Support x.1

def Coloring.Color (f : sc.faces) := Finset.image (c ∘ sc.iota f) Finset.univ

def Coloring.Rainbowfacet  (f : sc.faces)
 := c.Color f = Finset.univ

def isInternal (f : sc.faces) := FSupport f.1 = Finset.univ

/- A Facet is a top dimension face-/
def isFacet (f : sc.faces) := f.1.card = (Finset.univ : Finset ι).card

/- A SubFacet is a face with dimension = (top dimension - 1) -/
def isSubFacet (f : sc.faces) := f.1.card + 1  = (Finset.univ : Finset ι).card


section NonBranchingTheorem

variable {v : ι}

lemma isFacet_of_lt_SubFacet {f g : sc.faces} (h1 : isSubFacet f) : f < g → isFacet g := by sorry

lemma NonBranching {f : sc.faces} (h1 : isInternal f) (h2 : isSubFacet f) : (Set.Ioi f).ncard = 2 := by sorry

end NonBranchingTheorem


variable (v : ι)

section Boundary

def res_face (f : Finset E) : Finset ({x | x ≠ v} → k) := Finset.image (restrict {x | x ≠ v}) f


variable (sc)  in
def _root_.Geometry.SimplicialComplex.Boundary [SimplicialSimplex sc] : SimplicialComplex k ({x | x ≠ v}→ k) where
  faces := (res_face v) '' {f ∈ sc.faces | v ∉ FSupport f}
  empty_notMem := by sorry
  indep := by sorry
  down_closed := by sorry
  inter_subset_convexHull := by sorry

instance Boundary.isSS : SimplicialSimplex (sc.Boundary v) := by sorry

end Boundary


section SpernerProof



theorem Sperner {c : Coloring sc} (h : c.Proper) : ∃ f : sc.faces, c.Rainbowfacet f := sorry

/-- The boundary of a SimplicialSimplex is the subcomplex consisting of all proper faces. -/
def boundary (sc : SimplicialComplex k (ι→k)) [ss : SimplicialSimplex sc] : SimplicialComplex k (ι→k) where
  faces := sorry
  empty_notMem := by
    sorry
  indep := by
    rintro s hs
    sorry
  down_closed := by
    intro t s hs hts
    sorry
  inter_subset_convexHull := by
    intro s t hs ht
    sorry

namespace SimplicialSimplex

-- TODO: define boundary SimplicialSimplex, show that it is also a SimplicialSimplex

-- TODO: Show that every point in a SimplicialSimplex is a convex combination of its extrema

-- TODO: define the support of a convex combination of the extrema

-- TODO: define proper coloring on a SimplicialSimplex




end SimplicialSimplex






section Sperner


-- Define the notion of coloring.



-- TODO: State the Sperner's Lemma


end Sperner
