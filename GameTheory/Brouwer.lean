import Mathlib
import Gametheory.Scarf
open Classical
set_option maxHeartbeats 3000000
/-
\subsection*{The standard simplex}

Let us turn to the non-combinatorial part of the proof of Brouwer’s
theorem. Let us fix a non-negative integer $n$, and let
$I = \{ 0, 1, \ldots, n \}$. Let us number the coordinates in
$\mathbb{R}^{n+1}$ by elements of $I$. For a point
$x \in \mathbb{R}^{n+1}$ let $x_i$ be the $i$-th coordinate of
$x$, so that $x = (x_0, x_1, \ldots, x_n)$. Let
$\Delta^n \subset \mathbb{R}^{n+1}$ be the standard $n$-simplex
defined by the equation
$$
x_0 + x_1 + \cdots + x_n = 1
$$
and the inequalities $x_i \geq 0$ with $i \in I$.
Let $l \geq 1$ be another integer and let $T = T_l$ be the set of all
$x \in \Delta^n$ such that every $x_i$ is an integer multiple of
$1/l$. The set $T$ will serve as a discrete approximation to $\Delta^n$.

\subsection*{The linear orders on $T$}

For each $i \in I$ let us choose a linear order $<_i$ on $T$ such that
\begin{equation}
x_i < y_i \;\; \text{implies} \;\; x <_i y
\end{equation}
for every $x,y \in T$ (obviously, such orders exist).


-/
section
/-- A dependent product of finite, indexed by finite, is a finite. -/
instance Pi.Lex.finite {α : Type*} {β : α → Type*} [DecidableEq α] [Finite α]
    [∀ a, Finite (β a)] : Finite (Πₗ a, β a) :=
        (Equiv.finite_iff toLex).1 Pi.finite

end

noncomputable section
open IndexedLOrder

variable (n l : ℕ+) (i : Fin n)

abbrev TT := {x : Πₗ (_ : Fin n), Fin (l+1) | ∑ i, (x i : ℕ)  = l}

instance TT.finite : Finite (TT n l) := by
  rw [Set.coe_eq_subtype]
  exact Subtype.finite

instance TT.inhabited : Inhabited (TT n l) where
  default :=
    ⟨ fun i => if i = 0 then Fin.last l else 0,  by
      simp only [TT, Set.mem_setOf_eq]
      rw [Finset.sum_eq_single (0 : Fin n)]
      · simp
      · intro b _ hb; simp [hb]
      · simp [Fin.val_last] ⟩

instance TT.funlike : FunLike (TT n l) (Fin n) (Fin (l+1)) where
  coe := fun a => a.1
  coe_injective' := by simp

variable {n l} in
def TTtostdSimplex (x : TT n l) : stdSimplex ℝ (Fin n) := ⟨fun i => x i / l, by
  rw [stdSimplex]
  constructor
  · intro;simp only[Set.coe_setOf]
    apply div_nonneg <;> simp
  · simp only [Set.coe_setOf];
    rw [<-Finset.sum_div, div_eq_one_iff_eq]
    · exact_mod_cast x.2
    · exact Iff.mpr Nat.cast_ne_zero (PNat.ne_zero l)
  ⟩

instance TT.CoestdSimplex : CoeOut (TT n l) (stdSimplex ℝ (Fin n)) where
  coe := TTtostdSimplex


variable {n l} in
abbrev TT.Ilt ( x y : TT n l) :=
  toLex (x i, x)  < toLex (y i, y)

instance TT.IST : IsStrictTotalOrder (TT n l) (TT.Ilt i) where
  trichotomous := by
    intro a b
    repeat rw [TT.Ilt]
    have h1 : toLex (a i, a) <  toLex (b i, b) ∨ toLex (a i, a) = toLex (b i, b) ∨ toLex (b i, b) < toLex (a i, a) :=
      by apply IsTrichotomous.trichotomous
    convert h1
    suffices hh : a = b → a i = b i from
      by simp;exact hh
    intro h;rw [h]
  irrefl := by simp
  trans := by
    intro a b c
    rw [TT.Ilt]
    apply lt_trans


variable {n l} in
instance TT.ILO : IndexedLOrder (Fin n) (TT n l) where
  IST := fun i => linearOrderOfSTO (TT.Ilt i)

set_option quotPrecheck false
local notation  lhs "<[" i "]" rhs => (IndexedLOrder.IST i).lt lhs rhs
local notation  lhs "≤[" i "]" rhs => (IndexedLOrder.IST i).le lhs rhs

lemma TT.Ilt_def (a b : TT n l) :
  (a <[i] b) ↔ TT.Ilt i a b := by
  rfl

lemma TT.Ilt_keyprop (a b : TT n l) :
  a i < b i → a <[i] b := by
  intro h
  rw [TT.Ilt_def,Ilt,Prod.Lex.lt_iff]
  simp [h]

/- Theorem 10
\begin{theorem}[theorem 10]
Let $\sigma \subset T$ and $C \subset I$. If $\sigma$ is dominant with
respect to $C$, then
$$
| x_i - y_i | < \frac{2 (n+1)}{l}
$$
for every $x,y \in \sigma$ and $i \in I$ and
$$
x_i < \frac{n+1}{l}
$$
for every $x \in \sigma$ and $i \in I \setminus C$.
\end{theorem}

\begin{proof}
For each $i \in I$ let $m(i) = \min\nolimits_i \sigma$. Let
$m_i = m(i)_i$ be the $i$-th coordinate of $m(i)$ for $i \in C$ and
let $m_i = 0$ for $i \in I \setminus C$. By using the triangle inequality
and the fact that $|C| \leq n+1$, we see that it is sufficient to prove that
$$
0 \leq x_i - m_i < \frac{|C|}{l}
$$
for every $x \in \sigma$ and $i \in I$. The inequalities
$0 \leq x_i - m_i$ hold by the definition of $m_i$.
As the first step toward the inequalities $x_i - m_i < |C|/ l$, let us prove that
\begin{equation}
1 - \sum_{k \in C} m_k < \frac{|C|}{l}.
\end{equation}
If this is not the case, then
$$
\sum_{k \in C} \left( m_k + \frac{1}{l} \right)
= \left( \sum_{k \in C} m_k \right) + \frac{|C|}{l} \leq 1 .
$$
Since every $m_i$ is a multiple of $1/l$, this implies that there exists a point
$M \in T$ such that $M_k \geq m_k + (1/l)$ and hence
$\min\nolimits_k \sigma <_k M$ for every $k \in C$. The contradiction with $\sigma$
being dominant with respect to $C$ proves the inequality.
Let $x \in \sigma$ and $i \in I$. If $i \in C$, then
$$
x_i - m_i \leq \sum_{k \in C} (x_k - m_k)
\leq \sum_{k \in I} x_k - \sum_{k \in C} m_k
= 1 - \sum_{k \in C} m_k .
$$
If $i \notin C$, then $m_i = 0$ and hence
$$
x_i - m_i = x_i \leq \sum_{k \notin C} x_k
= 1 - \sum_{k \in C} x_k \leq 1 - \sum_{k \in C} m_k .
$$
Together with the previous inequality these inequalities imply that
$x_i - m_i < |C|/ l$ for every $i \in I$.
\end{proof}-/


lemma size_bound_key (σ : Finset (TT n l)) (C : Finset (Fin n)) (h : TT.ILO.isDominant σ C)
(h2 : σ.Nonempty):
  l < ∑ k ∈ C, (σ.image (fun x => (x k : ℕ))).min' (by simp [Finset.image_nonempty, h2]) + C.card := by
  by_contra h_not
  push_neg at h_not
  let m := fun k => (σ.image (fun x => (x k : ℕ))).min' (by simp [Finset.image_nonempty, h2])
  have h_sum_bound : ∑ k ∈ C, m k + C.card ≤ l := h_not
  have h_sum_plus_one : ∑ k ∈ C, (m k + 1) ≤ l := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_one]
    exact h_sum_bound
  have h_exists_point : ∃ M : TT n l, ∀ k ∈ C, m k + 1 ≤ M k := by
    let M' : Fin n → ℕ := fun k => if k ∈ C then m k + 1 else 0
    let S := ∑ k, M' k
    have h_S_le_l : S ≤ l := by
      simp [S, M', h_sum_plus_one]
    let R := l - S
    let M_coords : Fin n → ℕ := fun k => if k = (0 : Fin n) then M' 0 + R else M' k
    have h_M_coords_sum : ∑ k, M_coords k = l := by
      have h1 : S = M' 0 + ∑ k in (Finset.univ : Finset (Fin n)).erase 0, M' k := by
        simp [S]
        rw [← Finset.sum_insert (Finset.notMem_erase 0 Finset.univ)]
        rw [Finset.insert_erase (Finset.mem_univ 0)]
      have : ∑ k, M_coords k = M_coords 0 + ∑ k in (Finset.univ : Finset (Fin n)).erase 0, M_coords k := by
        rw [← Finset.sum_insert (Finset.notMem_erase 0 Finset.univ)]
        rw [Finset.insert_erase (Finset.mem_univ 0)]
      rw [this]
      simp only [M_coords, if_true]
      have sum_eq : ∑ x ∈ Finset.univ.erase 0, (if x = 0 then M' 0 + R else M' x) = ∑ x ∈ Finset.univ.erase 0, M' x := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [if_neg (Finset.ne_of_mem_erase hk)]
      rw [sum_eq, add_comm (M' 0) R, add_assoc, ← h1]
      simp only [R]
      have hM'0_le_S : M' 0 ≤ S := by
        have : M' 0 ≤ ∑ k, M' k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
        exact this
      omega

    have h_M_coords_bound : ∀ k, M_coords k ≤ l := by
      intro k
      by_cases h_is_zero : k = 0
      · simp [h_is_zero, M_coords, R]
        have hM'0_le_S : M' 0 ≤ S := by
          have : M' 0 ≤ ∑ k, M' k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
          exact this
        omega
      · simp [h_is_zero, M_coords]
        by_cases hk_in_C : k ∈ C
        · simp [M', hk_in_C]; exact Nat.le_trans (Finset.single_le_sum (fun k _ => Nat.zero_le (m k + 1)) hk_in_C) h_sum_plus_one
        · simp [M', hk_in_C]
    let M_val : Fin n → Fin (l + 1) := fun k => ⟨M_coords k, Nat.lt_succ_of_le (h_M_coords_bound k)⟩
    use ⟨M_val, by simp [M_val, h_M_coords_sum]⟩
    intro k hk_in_C
    simp only [TT.funlike]
    by_cases h_is_zero : k = 0
    · rw [h_is_zero] at hk_in_C ⊢
      simp [M_val, M_coords, M', hk_in_C]
    · simp [M_val, M_coords, h_is_zero, M', hk_in_C]
  obtain ⟨M, hM⟩ := h_exists_point
  have h_min_less : ∀ k ∈ C, ∃ x_min ∈ σ, ∀ x ∈ σ, x_min ≤[k] x := by
    intro k _
    letI : LinearOrder (TT n l) := IndexedLOrder.IST k
    let x_min := σ.min' h2
    use x_min
    constructor
    · exact Finset.min'_mem σ h2
    · intro x hx
      exact Finset.min'_le σ x hx
  have h_contradiction : ∀ k ∈ C, ∃ x_min ∈ σ, x_min <[k] M := by
    intro k hk_in_C
    letI : LinearOrder (TT n l) := IndexedLOrder.IST k
    let x_min := σ.min' h2
    use x_min
    constructor
    · exact Finset.min'_mem σ h2
    · apply TT.Ilt_keyprop
      have h_min_coord : (x_min k : ℕ) = (σ.image (fun x => (x k : ℕ))).min' (by simp [Finset.image_nonempty, h2]) := by
        symm
        apply le_antisymm
        · apply Finset.min'_le
          apply Finset.mem_image_of_mem
          exact Finset.min'_mem σ h2
        · apply Finset.le_min'
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
          have h_x_min_le_x : x_min ≤[k] x := Finset.min'_le σ x hx
          by_cases h_case : (x_min k : ℕ) ≤ (x k : ℕ)
          · exact h_case
          · exfalso
            push_neg at h_case
            have h_x_lt_min : x <[k] x_min := by
              apply TT.Ilt_keyprop
              exact h_case
            exact not_lt.mpr h_x_min_le_x h_x_lt_min
      have h_nat_lt : (x_min k : ℕ) < (M k : ℕ) := by
        rw [h_min_coord]
        exact Nat.lt_of_succ_le (hM k hk_in_C)
      exact h_nat_lt
  have h_not_dominant : ¬ TT.ILO.isDominant σ C := by
    unfold isDominant
    push_neg
    use M
    intro k hk
    rcases h_contradiction k hk with ⟨x, hx, hlt⟩
    use x, hx
    letI : LinearOrder (TT n l) := IndexedLOrder.IST k
    rwa [← lt_iff_not_ge]
  exact h_not_dominant h



theorem size_bound_in (σ : Finset (TT n l)) (C : Finset (Fin n)) (h : TT.ILO.isDominant σ C):
    ∀ x ∈ σ, ∀ y ∈ σ, ∀ i : Fin n, abs ((x i : ℤ) - (y i : ℤ)) < 2 * (n + 1)
    := by
  by_cases hσ : σ.Nonempty
  · intro x hx y hy i
    let m k := (σ.image (fun z => (z k : ℕ))).min' (by simp [Finset.image_nonempty, hσ])
    let m' i := if h_i : i ∈ C then m i else 0
    have h_le_l_sub_sum : (l : ℕ) - ∑ k ∈ C, m k < C.card := by
      have h_key : l < ∑ k ∈ C, m k + C.card := size_bound_key n l σ C h hσ
      have h_sum_le_l : ∑ k ∈ C, m k ≤ l := by
        rcases hσ with ⟨x, hx⟩
        have h_m_le : ∀ k ∈ C, m k ≤ (x k : ℕ) := fun k _ =>
          Finset.min'_le (σ.image (fun z => (z k : ℕ))) (x k : ℕ) (Finset.mem_image_of_mem (fun z => (z k : ℕ)) hx)
        calc
          ∑ k ∈ C, m k ≤ ∑ k ∈ C, (x k : ℕ) := Finset.sum_le_sum h_m_le
          _ ≤ ∑ k, (x k : ℕ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (by simp)
          _ = l := x.2
      rw [Nat.sub_lt_iff_lt_add h_sum_le_l, add_comm]
      exact h_key
    have h_bound : ∀ z ∈ σ, (z i : ℕ) - m' i < C.card := by
      intro z hz
      by_cases hi_in_C : i ∈ C
      · simp [m', hi_in_C]
        have h_mi_le_zi : m i ≤ (z i : ℕ) := by
          apply Finset.min'_le
          apply Finset.mem_image_of_mem
          exact hz
        have h_zi_le_sum : (z i : ℕ) ≤ ∑ k ∈ C, (z k : ℕ) :=
          Finset.single_le_sum (fun k _ => Nat.zero_le (z k : ℕ)) hi_in_C
        have h_sum_z_le_l : ∑ k ∈ C, (z k : ℕ) ≤ l := by
          calc ∑ k ∈ C, (z k : ℕ) ≤ ∑ k, (z k : ℕ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (by simp)
          _ = l := z.2
        have h_diff_bound : (z i : ℕ) - m i ≤ l - ∑ k ∈ C, m k := by
          calc
          (z i : ℕ) - m i ≤ ∑ k ∈ C, ((z k : ℕ) - m k) :=
            Finset.single_le_sum (fun k _ => Nat.zero_le ((z k : ℕ) - m k)) hi_in_C
          _ = (∑ k ∈ C, (z k : ℕ)) - (∑ k ∈ C, m k) := by
            rw [Finset.sum_tsub_distrib]
            intro k hk
            apply Finset.min'_le
            apply Finset.mem_image_of_mem
            exact hz
          _ ≤ l - ∑ k ∈ C, m k := by
            apply Nat.sub_le_sub_right
            calc
              ∑ k ∈ C, (z k : ℕ) ≤ ∑ k, (z k : ℕ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (by simp)
              _ = l := z.2
        exact lt_of_le_of_lt h_diff_bound h_le_l_sub_sum

      · simp [m', hi_in_C]
        have h_sum_le : (z i : ℕ) + ∑ k ∈ C, (z k : ℕ) ≤ l := by
          calc
            (z i : ℕ) + ∑ k ∈ C, (z k : ℕ) = ∑ k ∈ insert i C, (z k : ℕ) := by
              rw [Finset.sum_insert hi_in_C]
            _ ≤ ∑ k, (z k : ℕ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by simp)
            _ = l := z.2
        have h_le_sub : (z i : ℕ) ≤ l - ∑ k ∈ C, (z k : ℕ) := Nat.le_sub_of_add_le h_sum_le
        have h_m_le_z : ∑ k ∈ C, m k ≤ ∑ k ∈ C, (z k : ℕ) := by
          apply Finset.sum_le_sum
          intro k hk
          apply Finset.min'_le
          apply Finset.mem_image_of_mem
          exact hz
        have h_sub_le_sub : l - ∑ k ∈ C, (z k : ℕ) ≤ l - ∑ k ∈ C, m k :=
          Nat.sub_le_sub_left h_m_le_z l
        exact lt_of_le_of_lt (h_le_sub.trans h_sub_le_sub) h_le_l_sub_sum
    have h_nonneg : ∀ z ∈ σ, 0 ≤ (z i : ℤ) - (m' i : ℤ) := by
      intro z hz
      by_cases hi_in_C : i ∈ C
      · simp [m', hi_in_C]
        have h_min_le : m i ≤ ↑(z i) := by
          apply Finset.min'_le
          apply Finset.mem_image_of_mem
          exact hz
        exact_mod_cast h_min_le
      · simp [m', hi_in_C]

    have h_abs_lt_2_card : abs ((x i : ℤ) - (y i : ℤ)) < 2 * (C.card : ℤ) := by
      have h_bound_int : ∀ z ∈ σ, (z i : ℤ) - (m' i : ℤ) < C.card := by
        intro z hz
        have := h_bound z hz
        simp only [m'] at this ⊢
        split_ifs at this ⊢ <;> linarith
      calc
        abs ((x i : ℤ) - (y i : ℤ)) = abs (((x i : ℤ) - (m' i : ℤ)) - ((y i : ℤ) - (m' i : ℤ))) := by rw [sub_sub_sub_cancel_right]
        _ ≤ abs ((x i : ℤ) - (m' i : ℤ)) + abs ((y i : ℤ) - (m' i : ℤ)) := by exact abs_sub_le _ _ _
        _ = ((x i : ℤ) - (m' i : ℤ)) + ((y i : ℤ) - (m' i : ℤ)) := by
          rw [abs_of_nonneg (h_nonneg x hx), abs_of_nonneg (h_nonneg y hy)]
        _ < (C.card : ℤ) + (C.card : ℤ) := by
          apply add_lt_add (h_bound_int x hx) (h_bound_int y hy)
        _ = 2 * (C.card : ℤ) := by rw [two_mul]
    have h_card_le_n : C.card ≤ n :=
      calc
        C.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ C)
        _ = n := by simp
    apply lt_trans h_abs_lt_2_card
    have : (2 * (C.card : ℤ)) < 2 * (n + 1 : ℤ) := by
      linarith [Int.ofNat_le.mpr h_card_le_n]
    exact this
  · sorry

theorem size_bound_out (σ : Finset (TT n l)) (C : Finset (Fin n)) (h : TT.ILO.isDominant σ C):
    ∀ x ∈ σ, ∀ i ∉ C, (x i : ℤ) < n + 1
    := by
  by_cases hσ : σ.Nonempty
  · intro x hx i hi_not_C
    let m k := (σ.image (fun z => (z k : ℕ))).min' (by simp [Finset.image_nonempty, hσ])
    have h_le_l_sub_sum : l - ∑ k ∈ C, m k < C.card := by
      have h_sum_le_l : ∑ k ∈ C, m k ≤ l := by
        rcases hσ with ⟨x, hx⟩
        have h_m_le : ∀ k ∈ C, m k ≤ (x k : ℕ) := fun k _ =>
          Finset.min'_le (σ.image (fun z => (z k : ℕ))) (x k : ℕ) (Finset.mem_image_of_mem (fun z => (z k : ℕ)) hx)
        calc
          ∑ k ∈ C, m k ≤ ∑ k ∈ C, (x k : ℕ) := Finset.sum_le_sum h_m_le
          _ ≤ ∑ k, (x k : ℕ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C) (by simp)
          _ = l := x.2
      rw [Nat.sub_lt_iff_lt_add h_sum_le_l, add_comm]
      exact size_bound_key n l σ C h hσ
    have h_bound : (x i : ℕ) < C.card := by
      have h_sum_le : (x i : ℕ) + ∑ k ∈ C, (x k : ℕ) ≤ l := by
        calc
          (x i : ℕ) + ∑ k ∈ C, (x k : ℕ) = ∑ k ∈ insert i C, (x k : ℕ) := by
            rw [Finset.sum_insert hi_not_C]
          _ ≤ ∑ k, (x k : ℕ) := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by simp)
          _ = l := x.2
      have h_le_sub : (x i : ℕ) ≤ l - ∑ k ∈ C, (x k : ℕ) := Nat.le_sub_of_add_le h_sum_le
      have h_m_le_x : ∑ k ∈ C, m k ≤ ∑ k ∈ C, (x k : ℕ) := by
        apply Finset.sum_le_sum
        intro k _
        apply Finset.min'_le
        apply Finset.mem_image_of_mem
        exact hx
      have h_sub_le_sub : l - ∑ k ∈ C, (x k : ℕ) ≤ l - ∑ k ∈ C, m k :=
        Nat.sub_le_sub_left h_m_le_x l
      exact lt_of_le_of_lt (h_le_sub.trans h_sub_le_sub) h_le_l_sub_sum
    have h_card_le_n : C.card ≤ n := by
      calc
        C.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ C)
        _ = n := by simp [Fintype.card_fin]
    have h_lt_n : (x i : ℤ) < ↑n := by
      apply lt_of_lt_of_le
      · exact Int.ofNat_lt.mpr h_bound
      · exact Int.ofNat_le.mpr h_card_le_n
    linarith
  · intro x hx
    exfalso
    exact hσ ⟨x, hx⟩

section Brouwer

/-\subsection*{Continuous self-maps of $\Delta^n$}

Now we turn to the final part of the proof of Brouwer’s theorem. Let
$f : \Delta^n \to \Delta^n$ be a continuous map. Recall that
$T = T_l$ depends on $l$. If
$$
x = ( x_0, x_1, \ldots, x_n ) \in T_l
\quad \text{and} \quad
y = ( y_0, y_1, \ldots, y_n ) = f(x) ,
$$
then
$$
x_0 + x_1 + \cdots + x_n = y_0 + y_1 + \cdots + y_n = 1
$$
and hence $y_i \geq x_i$ for some $i \in I$. Let $c(x)$ be equal to any such $i$.
This rule defines a coloring of $T_l$, i.e. a map $c : T_l \to I$.

By Theorem~8 for every $l$ there exists a properly colored cell, i.e. a pair
$(\sigma_l, C_l)$ such that $C_l$ is non-empty, $\sigma_l \subset T_l$ is
dominant with respect to $C_l$, and $C_l = c(\sigma_l)$. By Theorem~10 the
diameter of the sets $\sigma_l$ tends to $0$ when $l \to \infty$. Therefore,
after passing to a subsequence, still denoted by $\sigma_l$, we can assume that
all elements of $\sigma_l$ converge to the same point
$$
z = ( z_0, z_1, \ldots, z_n ) \in \Delta^n
$$
when $l \to \infty$. Let
$$
w = ( w_0, w_1, \ldots, w_n ) = f(z) .
$$
Since there are only finitely many subsets of $I$, after passing to a further
subsequence we can assume that $C_l = C$ for some non-empty subset
$C \subset I$ independent of $l$. Then $C = C_l = c(\sigma_l)$ for every $l$
and hence for every $l$ and every $i \in C$ there is a point
$z(i, l) \in \sigma_l$ such that $c(z(i,l)) = i$. By the choice of the
colorings $c$ passing to the limit $l \to \infty$ shows that $w_i \geq z_i$
for every $i \in C$.

At the same time Theorem~10 implies that $x_i < (n+1)/l$ for every
$x \in \sigma$ and $i \in I \setminus C$. By passing to the limit
$l \to \infty$ we conclude that $z_i = 0$ for every $i \in I \setminus C$.
Therefore
$$
\sum_{i \in C} z_i = 1.
$$
Since $w_i \geq z_i$ for every $i \in C$, this equality implies that
$$
\sum_{i \in C} w_i \geq 1.
$$
But
$$
\sum_{i \in I} w_i = 1 .
$$
It follows that $w_i = 0 = z_i$ for every $i \in I \setminus C$ and
$$
\sum_{i \in C} w_i = 1 = \sum_{i \in C} z_i .
$$
Since $w_i \geq z_i$ for every $i \in C$, this equality implies that
$w_i = z_i$ for every $i \in C$ also. Therefore $w_i = z_i$ for every
$i \in I$ and hence $f(z) = w = z$, i.e. $z$ is a fixed point of the
map $f$. This completes the proof of Brouwer’s fixed point theorem.
-/
--instance stdSimplex.cpt : CompactSpace ↑(stdSimplex ℝ (Fin n)) := inferInstance

variable (f : stdSimplex ℝ (Fin n) → stdSimplex ℝ (Fin n))

variable {n l}

instance stdSimplex.upidx (x y : stdSimplex ℝ (Fin n)) : Nonempty { i | x.1 i ≤ y.1 i} := by sorry

noncomputable def stdSimplex.pick (x  y : stdSimplex ℝ (Fin n)) := Classical.choice $ stdSimplex.upidx x y



def Fcolor (x : TT n l) : Fin n := stdSimplex.pick x (f x)

def room_seq (l' : ℕ) :=
  let l : PNat := ⟨l'+1,Nat.zero_lt_succ _⟩
  Classical.choice (TT.ILO.Scarf (@Fcolor n l f)).to_subtype

def room_point_seq (l' : ℕ) := pick_colorful_point
(Finset.mem_filter.1 (room_seq f l').2).2 |>.1



section finiteness
theorem exists_subseq_constant_of_finite_image {s : Finset α} (e : ℕ → α) (he : ∀ n, e n ∈ s ) :
  ∃ a ∈ s, ∃ g : ℕ ↪o ℕ,  (∀ n, e (g n) = a) := by
  sorry

end finiteness

lemma constant_index_set_nonempty : Nonempty {(a, g) :(Finset (Fin n)) × (ℕ ↪o ℕ) | ∀ l', (room_seq f (g l')).1.2 = a } := by
  obtain ⟨a, ha,g,hg⟩ := exists_subseq_constant_of_finite_image (s := Finset.univ)
    (fun x => (room_seq f x).1.2) (by simp)
  use ⟨a,g⟩; simp [hg]


/- room_seq ∘ gpkg.1.2 has constant value equal to gpkg.1.1-/
def gpkg :=  Classical.choice $ constant_index_set_nonempty f

abbrev g1 := gpkg f |>.1.2


open Topology

/- room_seq ∘ g1 ∘ hpkg.1.2 converge to a point in stdSimplex-/
def hpkg_aux:
  Nonempty {(z , h) : (stdSimplex ℝ  (Fin n)) × (ℕ → ℕ) | StrictMono h ∧ Filter.Tendsto
    (fun l => (room_point_seq f (g1 f l): stdSimplex ℝ (Fin n)))
    Filter.atTop (𝓝 z) } := sorry

def hpkg := Classical.choice  (hpkg_aux f)

/-
Use
-- StrictMono.id_le : ∀ {φ : ℕ → ℕ}, StrictMono φ → ∀ (n : ℕ), n ≤ φ n
-- OrderEmbedding.strictMono: (f : α ↪o β), StrictMono ⇑f
-/

theorem Brouwer (hf : Continuous f): ∃ x , f x = x := by
  use (hpkg f).1.1
  sorry


end Brouwer
