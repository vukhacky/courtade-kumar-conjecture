module

public import CK.Functional.Tensorization
public import CK.Analysis.BinaryEntropy
public import CK.Fourier.Laplacian
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Sharp cube log-Sobolev inequality in the source normalization:
`Ent(g²) ≤ 2 Dir(g)`. Arbitrary real functions and zeros are included. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
open Set
namespace CK
noncomputable section

theorem phiSlope_le_div_sqrt {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    phiSlope t ≤ t / Real.sqrt (1-t^2) := by
  have ht : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, ht1⟩
  rw [phiSlope_eq_artanh ht, ← Real.sinh_artanh ht]
  exact Real.self_le_sinh_iff.mpr (Real.artanh_nonneg ht0)

theorem phi_le_one_sub_sqrt_of_nonneg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    phi t ≤ 1 - Real.sqrt (1-t^2) := by
  let F : ℝ → ℝ := fun x => 1 - Real.sqrt (1-x^2) - phi x
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hD (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt F (x/Real.sqrt (1-x^2) - phiSlope x) x := by
    have hdpos : 0 < 1-x^2 := by nlinarith [hx.1,hx.2]
    have h := ((((hasDerivAt_pow 2 x).const_sub 1).sqrt (ne_of_gt hdpos)).const_sub 1).sub
      (hasDerivAt_phi ⟨by linarith [hx.1], hx.2⟩)
    apply h.congr_deriv
    dsimp
    ring
  have hm : MonotoneOn F (Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hF.continuousOn
    · intro x hx
      exact (hD x (by simpa only [interior_Icc] using hx)).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hx
      exact sub_nonneg.mpr (phiSlope_le_div_sqrt hx'.1.le hx'.2)
  have h := hm (by norm_num : (0 : ℝ) ∈ Icc 0 1) ht ht.1
  simp only [F, pow_two, zero_mul, sub_zero, Real.sqrt_one, sub_self, phi_zero] at h
  simpa only [pow_two] using (sub_nonneg.mp h)

theorem phi_le_one_sub_sqrt {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    phi t ≤ 1 - Real.sqrt (1-t^2) := by
  by_cases h : 0 ≤ t
  · exact phi_le_one_sub_sqrt_of_nonneg ⟨h,ht.2⟩
  · have hh : -t ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ht.1]⟩
    simpa only [phi_neg, neg_sq] using phi_le_one_sub_sqrt_of_nonneg hh

/-- Sharp two-point logarithmic Sobolev inequality. -/
theorem twoPointEntropy_sq_le (a b : ℝ) :
    twoPointEntropy (a^2) (b^2) ≤ (a-b)^2/2 := by
  have hs0 : 0 ≤ a^2+b^2 := add_nonneg (sq_nonneg a) (sq_nonneg b)
  rcases eq_or_lt_of_le hs0 with hs | hs
  · have ha : a = 0 := by nlinarith [sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a]
    simp [ha,hb,twoPointEntropy]
  have ht := pair_ratio_mem_Icc (sq_nonneg a) (sq_nonneg b)
  have hphi := phi_le_one_sub_sqrt ht
  have hsq : 0 ≤ 1-((a^2-b^2)/(a^2+b^2))^2 := by nlinarith [ht.1,ht.2]
  have hroot : (((a^2+b^2)/2)*Real.sqrt (1-((a^2-b^2)/(a^2+b^2))^2))^2 = (a*b)^2 := by
    rw [mul_pow, Real.sq_sqrt hsq]
    field_simp [ne_of_gt hs]
    ring
  have hp : 0 ≤ ((a^2+b^2)/2)*Real.sqrt (1-((a^2-b^2)/(a^2+b^2))^2) := by positivity
  have hab : a*b ≤ ((a^2+b^2)/2)*Real.sqrt (1-((a^2-b^2)/(a^2+b^2))^2) := by
    rcases le_total (a*b) 0 with hab | hab
    · exact hab.trans hp
    · exact (sq_le_sq₀ hab hp).mp hroot.ge
  have hm := mul_le_mul_of_nonneg_left hphi (div_nonneg hs0 (by norm_num : (0:ℝ)≤2))
  rw [twoPointEntropy_mean_phi (sq_nonneg a) (sq_nonneg b)]
  nlinarith

theorem two_mul_partial_sq_eq_update {n : ℕ} (i : Fin n) (g : Cube n → ℝ) (x : Cube n) :
    2 * coordinatePartial i g x ^ 2 =
      (g (Function.update x i false) - g (Function.update x i true))^2/2 := by
  cases hx : x i
  · have heq : Function.update x i false = x := by
      funext j
      by_cases hji : j = i
      · subst j; simp [hx]
      · simp [hji]
    simp only [coordinatePartial, flipCoordinate, hx, Bool.not_false, heq]
    ring
  · have heq : Function.update x i true = x := by
      funext j
      by_cases hji : j = i
      · subst j; simp [hx]
      · simp [hji]
    simp only [coordinatePartial, flipCoordinate, hx, Bool.not_true, heq]
    ring

/-- Kernel-checked sharp log-Sobolev for every real function on every finite
uniform cube, in the normalization used by the canonical STOC source. -/
theorem cube_logSobolev {n : ℕ} (g : Cube n → ℝ) :
    entropyFunctional (fun x => g x^2) ≤ 2 * dirichlet g := by
  calc
    entropyFunctional (fun x => g x^2) ≤
        ∑ i : Fin n, avg (coordinateEntropy (fun x => g x^2) i) :=
      entropyFunctional_tensorization n _ (fun x => sq_nonneg (g x))
    _ ≤ ∑ i : Fin n, avg (fun x => 2*coordinatePartial i g x^2) := by
      apply Finset.sum_le_sum
      intro i _
      apply avg_mono
      intro x
      rw [two_mul_partial_sq_eq_update]
      exact twoPointEntropy_sq_le _ _
    _ = 2 * dirichlet g := by
      simp only [avg_smul, ← Finset.mul_sum, dirichlet_eq_sum_partials]

end
end CK
