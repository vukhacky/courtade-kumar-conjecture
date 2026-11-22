module

public import CK.Basic.Entropy
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Scalar entropy calculus on its probability domain. The values at ±1 are
handled by continuity, not by differentiating a totalized logarithm there. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

def phiSlope (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (Real.log (1 + t) - Real.log (1 - t))

@[simp] theorem phiSlope_zero : phiSlope 0 = 0 := by simp [phiSlope]

@[fun_prop] theorem continuous_phi : Continuous phi := by
  unfold phi
  fun_prop

theorem hasDerivAt_phi {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt phi (phiSlope t) t := by
  have hp0 : (1 - t) / 2 ≠ 0 := by linarith [ht.2]
  have hp1 : (1 - t) / 2 ≠ 1 := by linarith [ht.1]
  have hplus : 1 + t ≠ 0 := by linarith [ht.1]
  have hminus : 1 - t ≠ 0 := by linarith [ht.2]
  have h := ((Real.hasDerivAt_binEntropy hp0 hp1).comp t
    (((hasDerivAt_id t).const_sub 1).div_const 2)).const_sub (Real.log 2)
  apply h.congr_deriv
  simp only [phiSlope, show 1 - (1 - t) / 2 = (1 + t) / 2 by ring,
    Real.log_div hplus (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div hminus (by norm_num : (2 : ℝ) ≠ 0)]
  ring

theorem hasDerivAt_phiSlope {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt phiSlope (1 / (1 - t ^ 2)) t := by
  have hplus : 1 + t ≠ 0 := by linarith [ht.1]
  have hminus : 1 - t ≠ 0 := by linarith [ht.2]
  have hsq : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht.2]
  have h := ((((hasDerivAt_id t).const_add 1).log hplus).sub
    (((hasDerivAt_id t).const_sub 1).log hminus)).const_mul (1 / 2 : ℝ)
  apply h.congr_deriv
  dsimp only [id_eq]
  field_simp [hplus, hminus, hsq]
  <;> ring

theorem phiSlope_eq_artanh {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    phiSlope t = Real.artanh t := by
  rw [Real.artanh_eq_half_log ⟨ht.1.le, ht.2.le⟩,
    Real.log_div (by linarith [ht.1]) (by linarith [ht.2])]
  rfl

theorem le_phiSlope {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : t ≤ phiSlope t := by
  rw [phiSlope_eq_artanh ⟨by linarith, ht1⟩]
  simpa using Real.sum_range_le_artanh ht0 ht1 1

theorem convexOn_phiSlope {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ConvexOn ℝ (Icc 0 t) phiSlope := by
  have hdom : Icc 0 t ⊆ Ioo (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], lt_of_le_of_lt hx.2 ht1⟩
  apply MonotoneOn.convexOn_of_deriv (convex_Icc 0 t)
  · intro x hx
    exact (hasDerivAt_phiSlope (hdom hx)).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_phiSlope (hdom (interior_subset hx))).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    have hx' := interior_subset hx
    have hy' := interior_subset hy
    rw [(hasDerivAt_phiSlope (hdom hx')).deriv,
      (hasDerivAt_phiSlope (hdom hy')).deriv]
    have hden : 0 < 1 - y ^ 2 := by
      nlinarith [hy'.1, hy'.2, ht1]
    have hsq : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx'.1 hxy 2
    exact one_div_le_one_div_of_le hden (by linarith)

theorem phiSlope_mul_le_mul {η t : ℝ} (hη : η ∈ Icc (0 : ℝ) 1)
    (ht0 : 0 ≤ t) (ht1 : t < 1) : phiSlope (η * t) ≤ η * phiSlope t := by
  have h := (convexOn_phiSlope ht0 ht1).2 (show (0 : ℝ) ∈ Icc 0 t from ⟨le_rfl, ht0⟩)
    (show t ∈ Icc 0 t from ⟨ht0, le_rfl⟩)
    (show 0 ≤ 1 - η by linarith [hη.2]) hη.1 (by ring : (1-η)+η=1)
  simpa only [smul_eq_mul, mul_zero, zero_add, phiSlope_zero] using h

theorem sq_div_two_le_phi_of_nonneg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t ^ 2 / 2 ≤ phi t := by
  let F : ℝ → ℝ := fun x => phi x - x ^ 2 / 2
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hD (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt F (phiSlope x - x) x := by
    have hd := (hasDerivAt_phi ⟨by linarith [hx.1], hx.2⟩).sub
      ((hasDerivAt_pow 2 x).div_const 2)
    apply hd.congr_deriv
    simp
  have hm : MonotoneOn F (Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hF.continuousOn
    · intro x hx
      exact (hD x (by simpa only [interior_Icc] using hx)).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hx
      exact sub_nonneg.mpr (le_phiSlope hx'.1.le hx'.2)
  have := hm (by norm_num : (0 : ℝ) ∈ Icc 0 1) ht ht.1
  simpa [F] using this

theorem sq_div_two_le_phi {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    t ^ 2 / 2 ≤ phi t := by
  by_cases h : 0 ≤ t
  · exact sq_div_two_le_phi_of_nonneg ⟨h, ht.2⟩
  · have hh : -t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1]
    simpa only [neg_sq, phi_neg] using sq_div_two_le_phi_of_nonneg hh

theorem phi_mul_le_sq_mul_of_nonneg {η t : ℝ} (hη : η ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) : phi (η*t) ≤ η^2 * phi t := by
  let F : ℝ → ℝ := fun x => η^2 * phi x - phi (η*x)
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hD (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt F (η^2 * phiSlope x - η * phiSlope (η*x)) x := by
    have hηx : η*x ∈ Ioo (-1 : ℝ) 1 := by
      constructor
      · nlinarith [hη.1, hx.1]
      · nlinarith [hη.2, hη.1, hx.1, hx.2]
    have hd := ((hasDerivAt_phi ⟨by linarith [hx.1], hx.2⟩).const_mul (η^2)).sub
      ((hasDerivAt_phi hηx).comp x ((hasDerivAt_id x).const_mul η))
    apply hd.congr_deriv
    ring
  have hm : MonotoneOn F (Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hF.continuousOn
    · intro x hx
      exact (hD x (by simpa only [interior_Icc] using hx)).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hx
      have hh := mul_le_mul_of_nonneg_left (phiSlope_mul_le_mul hη hx'.1.le hx'.2) hη.1
      nlinarith
  have hh := hm (by norm_num : (0 : ℝ) ∈ Icc 0 1) ht ht.1
  simpa [F] using hh

/-- The exact one-bit entropy contraction, valid at both endpoints. -/
theorem phi_mul_le_sq_mul {η t : ℝ} (hη : η ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (-1 : ℝ) 1) : phi (η*t) ≤ η^2 * phi t := by
  by_cases h : 0 ≤ t
  · exact phi_mul_le_sq_mul_of_nonneg hη ⟨h, ht.2⟩
  · have hh : -t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1]
    simpa only [mul_neg, phi_neg] using phi_mul_le_sq_mul_of_nonneg hη hh

end
end CK
