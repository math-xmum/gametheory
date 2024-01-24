import Mathlib.Data.Real.EReal
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Lattice

open Classical
open BigOperators

-- Single-parameter environments
structure SingleParameterEnvironment where
   I : Type* -- The set of bidders
   IInhabited : Inhabited I
   IFintype : Fintype I
   feasibleSet: I → Set ℝ -- feasibleSet
   feasibleSetInhabited: ∀ i, Inhabited (feasibleSet i)
   --val: I → ℝ  -- valuation of the item for each bidder

namespace SingleParameterEnvironment
variable (E: SingleParameterEnvironment)
variable {F: SingleParameterEnvironment}

instance : Inhabited E.I := E.IInhabited
instance : Fintype E.I := E.IFintype
instance : Inhabited (E.feasibleSet i) := E.feasibleSetInhabited _


--new valuation
abbrev Valuation := E.I → ℝ

-- The type of bids
abbrev Bids := E.I → ℝ


-- The subtype delete i-th bidder
abbrev I' i:= {j : F.I // j ≠ i}


abbrev Bids' (i : F.I) := I' i → ℝ

noncomputable def combineBids {i : F.I} (x : ℝ) (b' : Bids' i) : F.Bids
:= fun j => if h:j=i then x else b' ⟨j, h⟩

noncomputable def combineBidsPair {i : F.I} (b : ℝ × Bids' i) : F.Bids
:= combineBids b.1 b.2
attribute [coe] combineBidsPair

noncomputable instance  {i : F.I}: CoeOut (ℝ × (Bids' i)) F.Bids where
  coe := combineBidsPair


variable (i : F.I) (b' : Bids' i) (x : ℝ)

#check ((x,b'): F.Bids)

@[simp]
def Allocation := Π i, E.feasibleSet i

-- The type of allocation rule
@[simp]
def AllocationRule := E.Bids → E.Allocation


def Monotone (ar : F.AllocationRule) := ∀ i (x1 x2: ℝ) (b': Bids' i), x1 ≤ x2 →  (ar (x1,b') i) ≤  (ar (x2,b') i)
-- Payments

abbrev Payment:= E.I → ℝ

abbrev PaymentRule := E.Bids → E.Payment

-- Quasi_Linear utility
def utility (ar : F.AllocationRule) (pr : F.PaymentRule) (v : F.Valuation) (b : F.Bids) :
  F.I → ℝ := fun i => v i * (ar b i) - (pr b i)

-- `这里修改了一下定义中变量的顺序`，因为只有先固定 i 和 b' , 才能说一个对于vi的策略是dominant strategy
-- def dominant (ar : F.AllocationRule) (pr : F.PaymentRule) (v : F.Valuation) (i : F.I) (bi : ℝ) :=
--   ∀ (b' :Bids' i), utility ar pr v (bi,b') i ≥ utility ar pr v (bi, b') i
def dominant (ar : F.AllocationRule) (pr : F.PaymentRule) (v : F.Valuation) (i : F.I) (b' :Bids' i):=
  ∀ (bi : ℝ), utility ar pr v (v i ,b') i ≥ utility ar pr v (bi, b') i


-- 这里也`根据 dominant 的定义修改了一下变量的排列顺序`
-- def DSIC ar pr v := ∀ i:F.I,
--   (dominant ar pr v i (v i))
--   ∧ (∀ b' : Bids' i, utility ar pr v ((v i),b') i ≥ 0)
def DSIC ar pr v := ∀ (i:F.I) (b' : Bids' i),
  (dominant ar pr v i b') ∧ (utility ar pr v ((v i),b') i ≥ 0)

--利用dsic找一个特定的p，确实存在这个p
-- def Implementable (ar : F.AllocationRule) := ∀ v, ∃ pr : F.PaymentRule, DSIC ar pr v
-- `这里关于Implementable修改了一下 ∃ 和 ∀ 的顺序`，因为Paymentrule不会随着Valuation的改变而改变
-- Paymentrule一定是先于agents的存在而存在的
def Implementable (ar : F.AllocationRule) := ∃ pr : F.PaymentRule, ∀ v, DSIC ar pr v

lemma relation_h12(x1:ℝ )(x2:ℝ ): x1 ≤ x2 ↔ x1 - x2 ≤ 0 := by {
  constructor
  · intro h
    linarith
  · intro h
    linarith
}

theorem MyersonLemma (ar :F.AllocationRule) (v : F.Valuation):
Implementable ar ↔ Monotone ar := by {
  constructor
  · rintro h hj b'

    -- 定义两个取值为x1和x2的函数，用于后续代入得到不等式
    have v_x1 : F.I → ℝ := fun _ => x1
    have v_x2 : F.I → ℝ := fun _ => x2
    -- 分解 `har: Implementable ar`, 得到Implementable的等价条件
    obtain ⟨pr, h_DSIC⟩ := har
    -- 获得当valuation为 `v i = x1` 和 `v i = x2` 时，两个关于DSIC的论断
    have ⟨h_dom_x1, h_util_nonneg_x1⟩ := h_DSIC v_x1 i b'
    have ⟨h_dom_x2, h_util_nonneg_x2⟩ := h_DSIC v_x2 i b'

    -- 得到当 x1 ≤ x2 时两个关于效用的不等式
    have h_ux1_ge_ux2 := h_dom_x1 x2
    have h1 : x1 * (ar (x1, b') i) - (pr (x1, b') i) >= x1 * (ar (x2, b') i) - (pr (x2, b') i)
      := sorry

      -- 是`h_ux1_ge_ux2`的变形
    have h_ux2_ge_ux1 := h_dom_x2 x1
    have h2 : x2 * (ar (v_x2 i, b') i) - (pr (v_x2 i, b') i) >= x2 * (ar (x1, b') i) - (pr (x1, b') i)
      := sorry -- 是`h_ux2_ge_ux1`的变形

    -- 对两个不等式进行变形
    have h1' : x1 * ((ar (x2, b') i) - (ar (x1, b') i)) ≤ (pr (x2, b') i) - (pr (x1, b') i)
      := sorry -- 用 `h1` 和 `h2` 得到的不等式左端
    have h2' : (pr (x2, b') i) - (pr (x1, b') i) ≤ x2 * ((ar (x2, b') i) - (ar (x1, b') i))
      := sorry -- 用 `h1` 和 `h2` 得到的不等式右端

    -- 得到最终关于单调性的不等式
    have h : x1 * ((ar (x2, b') i) - (ar (x1, b') i)) ≤  x2 * ((ar (x2, b') i) - (ar (x1, b') i))
      := by apply le_trans h1' h2'
    have h' : (ar (x2, b') i) >= (ar (x1, b') i)
      := by sorry --用基本运算进行化简

    -- 得到单调性
    apply h'
  · rintro hmon
    use λ b i => b i
    rintro v i b'
    constructor
}
