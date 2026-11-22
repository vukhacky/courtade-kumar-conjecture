module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! Direct coverage by the five source rectangles numbered 14–18 and the moment half-plane, which contains the other seventeen regions. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Middle

def rectangle14 (a b : ℝ) : Prop :=
  a ∈ Icc (532301/800000 : ℝ) (228129/320000) ∧ b ∈ Icc (0 : ℝ) (1/16)
def rectangle15 (a b : ℝ) : Prop :=
  a ∈ Icc (228129/320000 : ℝ) (76043/100000) ∧ b ∈ Icc (0 : ℝ) (1/32)
def rectangle16 (a b : ℝ) : Prop :=
  a ∈ Icc (228129/320000 : ℝ) (2357333/3200000) ∧ b ∈ Icc (1/32 : ℝ) (1/16)
def rectangle17 (a b : ℝ) : Prop :=
  a ∈ Icc (2357333/3200000 : ℝ) (76043/100000) ∧ b ∈ Icc (1/32 : ℝ) (1/16)
def rectangle18 (a b : ℝ) : Prop :=
  a ∈ Icc (532301/800000 : ℝ) (228129/320000) ∧ b ∈ Icc (1/16 : ℝ) (1/8)

theorem last_band_rectangle_cover {a b : ℝ}
    (ha : a ∈ Icc (2/3 : ℝ) (76043/100000)) (hb : 0 ≤ b) :
    (64/25 : ℝ) ≤ 3*a+7*b ∨ rectangle14 a b ∨ rectangle15 a b ∨
      rectangle16 a b ∨ rectangle17 a b ∨ rectangle18 a b := by
  by_cases hm : (64/25 : ℝ) ≤ 3*a+7*b
  · exact Or.inl hm
  have hm' := lt_of_not_ge hm
  right
  by_cases hx : a ≤ (228129/320000 : ℝ)
  · by_cases hy : b ≤ (1/16 : ℝ)
    · left
      exact ⟨⟨by linarith [ha.1],hx⟩,⟨hb,hy⟩⟩
    · right; right; right; right
      exact ⟨⟨by linarith [ha.1],hx⟩,⟨(lt_of_not_ge hy).le,by linarith [ha.1]⟩⟩
  · have hx' := (lt_of_not_ge hx).le
    by_cases hy : b ≤ (1/32 : ℝ)
    · right; left
      exact ⟨⟨hx',ha.2⟩,⟨hb,hy⟩⟩
    · have hy' := (lt_of_not_ge hy).le
      have hbu : b ≤ (1/16 : ℝ) := by linarith
      by_cases hx2 : a ≤ (2357333/3200000 : ℝ)
      · right; right; left
        exact ⟨⟨hx',hx2⟩,⟨hy',hbu⟩⟩
      · right; right; right; left
        exact ⟨⟨(lt_of_not_ge hx2).le,ha.2⟩,⟨hy',hbu⟩⟩

end CK.Middle
