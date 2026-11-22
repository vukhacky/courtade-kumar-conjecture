module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic

/-! The positive-gap barrier from STOC `ub:barrier`. A nonnegative derivative
is required only where the gap is strictly positive. No selected coordinate
set or auxiliary optimization parameter is differentiated. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK

theorem positive_gap_barrier {a b : ℝ} (hab : a < b) {G : ℝ → ℝ}
    (hcont : ContinuousOn G (Icc a b))
    (hdiff : DifferentiableOn ℝ G (Ioo a b))
    (hend : G b ≤ 0)
    (hderiv : ∀ x ∈ Ioo a b, 0 < G x → 0 ≤ deriv G x) :
    ∀ x ∈ Icc a b, G x ≤ 0 := by
  intro x hx
  by_contra hn
  have hpos : 0 < G x := lt_of_not_ge hn
  have hxb : x < b := by
    apply lt_of_le_of_ne hx.2
    intro heq
    subst x
    exact (not_lt_of_ge hend) hpos
  let S : Set ℝ := Icc x b ∩ G ⁻¹' Iic (G x / 2)
  have hsub : Icc x b ⊆ Icc a b := Icc_subset_Icc_left hx.1
  have hclosed : IsClosed S := by
    exact (hcont.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hcompact : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hclosed (fun _ ht => ht.1)
  have hnonempty : S.Nonempty := ⟨b, ⟨⟨hxb.le, le_rfl⟩, by
    show G b ≤ G x / 2
    linarith⟩⟩
  obtain ⟨r, hrS, hrmin⟩ := hcompact.exists_isLeast hnonempty
  have hxr : x < r := by
    apply lt_of_le_of_ne hrS.1.1
    intro heq
    have hh : G x ≤ G x / 2 := by simpa [← heq] using hrS.2
    linarith
  have hrb : r ≤ b := hrS.1.2
  have hpos_before (y : ℝ) (hy : y ∈ Ioo x r) : 0 < G y := by
    have hnot : y ∉ S := by
      intro hyS
      have := hrmin hyS
      linarith [hy.2]
    have hlarge : G x / 2 < G y := by
      by_contra hh
      apply hnot
      exact ⟨⟨hy.1.le, hy.2.le.trans hrb⟩, le_of_not_gt hh⟩
    linarith
  have hinterval : Icc x r ⊆ Icc a b := by
    intro y hy
    exact ⟨hx.1.trans hy.1, hy.2.trans hrb⟩
  have hmono : MonotoneOn G (Icc x r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc x r) (hcont.mono hinterval)
    · intro y hy
      have hy' : y ∈ Ioo x r := by simpa only [interior_Icc] using hy
      exact (hdiff y ⟨lt_of_le_of_lt hx.1 hy'.1, lt_of_lt_of_le hy'.2 hrb⟩).mono
        (by simpa only [interior_Icc] using Ioo_subset_Ioo hx.1 hrb)
    · intro y hy
      have hy' : y ∈ Ioo x r := by simpa only [interior_Icc] using hy
      exact hderiv y ⟨lt_of_le_of_lt hx.1 hy'.1, lt_of_lt_of_le hy'.2 hrb⟩
        (hpos_before y hy')
  have hle := hmono ⟨le_rfl, hxr.le⟩ ⟨hxr.le, le_rfl⟩ hxr.le
  have hrhalf : G r ≤ G x / 2 := hrS.2
  linarith

end CK
