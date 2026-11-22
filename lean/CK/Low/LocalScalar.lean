module

public import CK.Functional.SignEntropy
public import CK.Certificate.LocalThreshold

/-! The scalar mean-compensation and coefficient deficit in the local
Courtade--Kumar comparison (STOC theorem `ub:local`). -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

def localDeficit (ρ a : ℝ) : ℝ :=
  (1 - ρ ^ 2) * signEntropy (ρ * a) - (1 - ρ ^ 2 * a) * signEntropy ρ

def localMeanCorrection (ρ a s : ℝ) : ℝ :=
  phi s - (1 - ρ ^ 2) * ((phi (s + ρ * a) + phi (s - ρ * a)) / 2 - phi (ρ * a))

def localMeanSlope (ρ a s : ℝ) : ℝ :=
  phiSlope s - (1 - ρ ^ 2) / 2 * (phiSlope (s + ρ * a) + phiSlope (s - ρ * a))

def localMeanCurvature (ρ a s : ℝ) : ℝ :=
  1 / (1 - s ^ 2) - (1 - ρ ^ 2) / 2 *
    (1 / (1 - (s + ρ * a) ^ 2) + 1 / (1 - (s - ρ * a) ^ 2))

theorem localMean_interior_domains {ρ a s : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) (hs : s ∈ Ioo (a - 1) (1 - a)) :
    s ∈ Ioo (-1 : ℝ) 1 ∧ (s + ρ * a) ∈ Ioo (-1 : ℝ) 1 ∧
      (s - ρ * a) ∈ Ioo (-1 : ℝ) 1 := by
  have hra0 : 0 ≤ ρ * a := mul_nonneg hρ.1 ha.1
  have hra1 : ρ * a ≤ a := by nlinarith [hρ.2, ha.1]
  exact ⟨⟨by linarith [hs.1, ha.1], by linarith [hs.2, ha.1]⟩,
    ⟨by linarith [hs.1, ha.1], by linarith [hs.2]⟩,
    ⟨by linarith [hs.1], by linarith [hs.2, ha.1]⟩⟩

theorem hasDerivAt_localMeanCorrection {ρ a s : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) (hs : s ∈ Ioo (a - 1) (1 - a)) :
    HasDerivAt (localMeanCorrection ρ a) (localMeanSlope ρ a s) s := by
  obtain ⟨hs0, hsp, hsm⟩ := localMean_interior_domains hρ ha hs
  have hd := (hasDerivAt_phi hs0).sub
    (((((hasDerivAt_phi hsp).comp s ((hasDerivAt_id s).add_const (ρ * a))).add
      ((hasDerivAt_phi hsm).comp s ((hasDerivAt_id s).sub_const (ρ * a)))).div_const 2).sub_const
      (phi (ρ * a)) |>.const_mul (1 - ρ ^ 2))
  apply hd.congr_deriv
  dsimp [localMeanSlope]
  ring

theorem hasDerivAt_localMeanSlope {ρ a s : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) (hs : s ∈ Ioo (a - 1) (1 - a)) :
    HasDerivAt (localMeanSlope ρ a) (localMeanCurvature ρ a s) s := by
  obtain ⟨hs0, hsp, hsm⟩ := localMean_interior_domains hρ ha hs
  have hp := (hasDerivAt_phiSlope hsp).comp s ((hasDerivAt_id s).add_const (ρ * a))
  have hm := (hasDerivAt_phiSlope hsm).comp s ((hasDerivAt_id s).sub_const (ρ * a))
  have hd := (hasDerivAt_phiSlope hs0).sub ((hp.add hm).const_mul ((1 - ρ ^ 2) / 2))
  apply hd.congr_deriv
  dsimp [localMeanCurvature]
  ring

theorem localMeanCurvature_nonneg {ρ a s : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) (hs : s ∈ Ioo (a - 1) (1 - a)) :
    0 ≤ localMeanCurvature ρ a s := by
  obtain ⟨hs0, hsp, hsm⟩ := localMean_interior_domains hρ ha hs
  have hsq (x : ℝ) (hx : x ∈ Ioo (-1 : ℝ) 1) : 0 < 1 - x ^ 2 := by
    nlinarith [mul_pos (by linarith [hx.1] : 0 < 1 + x) (by linarith [hx.2] : 0 < 1 - x)]
  have d0 := hsq s hs0
  have dp := hsq (s + ρ * a) hsp
  have dm := hsq (s - ρ * a) hsm
  have hap : 0 ≤ 1 - (s + a) ^ 2 := by
    have h1 : 0 ≤ 1 + (s + a) := by linarith [hs.1, ha.1]
    have h2 : 0 ≤ 1 - (s + a) := by linarith [hs.2]
    nlinarith [mul_nonneg h1 h2]
  have ham : 0 ≤ 1 - (s - a) ^ 2 := by
    have h1 : 0 ≤ 1 + (s - a) := by linarith [hs.1]
    have h2 : 0 ≤ 1 - (s - a) := by linarith [hs.2, ha.1]
    nlinarith [mul_nonneg h1 h2]
  have hsa : 0 ≤ 1 - s ^ 2 - a ^ 2 := by nlinarith
  have hr2 : 0 ≤ 1 - ρ ^ 2 := by nlinarith [mul_nonneg hρ.1 (sub_nonneg.mpr hρ.2)]
  have hid : localMeanCurvature ρ a s =
      ρ ^ 2 * ((1 - (s + a) ^ 2) * (1 - (s - a) ^ 2) +
        (1 - ρ ^ 2) * a ^ 2 * (1 - s ^ 2 - a ^ 2)) /
      ((1 - s ^ 2) * (1 - (s + ρ * a) ^ 2) * (1 - (s - ρ * a) ^ 2)) := by
    unfold localMeanCurvature
    field_simp [ne_of_gt d0, ne_of_gt dp, ne_of_gt dm]
    ring
  rw [hid]
  exact div_nonneg
    (mul_nonneg (sq_nonneg ρ) (add_nonneg (mul_nonneg hap ham)
      (mul_nonneg (mul_nonneg hr2 (sq_nonneg a)) hsa)))
    (mul_nonneg (mul_nonneg d0.le dp.le) dm.le)

theorem localMeanCorrection_convex {ρ a : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) :
    ConvexOn ℝ (Icc (a - 1) (1 - a)) (localMeanCorrection ρ a) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (f' := localMeanSlope ρ a) (f'' := localMeanCurvature ρ a)
  · unfold localMeanCorrection
    fun_prop
  · intro s hs
    exact (hasDerivAt_localMeanCorrection hρ ha (by simpa only [interior_Icc] using hs)).hasDerivWithinAt
  · intro s hs
    exact (hasDerivAt_localMeanSlope hρ ha (by simpa only [interior_Icc] using hs)).hasDerivWithinAt
  · intro s hs
    exact localMeanCurvature_nonneg hρ ha (by simpa only [interior_Icc] using hs)

@[simp] theorem localMeanCorrection_zero (ρ a : ℝ) : localMeanCorrection ρ a 0 = 0 := by
  simp only [localMeanCorrection, phi_zero, zero_add, zero_sub, phi_neg]
  ring

theorem localMeanCorrection_even (ρ a s : ℝ) :
    localMeanCorrection ρ a (-s) = localMeanCorrection ρ a s := by
  unfold localMeanCorrection
  rw [show -s + ρ * a = -(s - ρ * a) by ring,
    show -s - ρ * a = -(s + ρ * a) by ring]
  simp only [phi_neg]
  ring

theorem localMeanCorrection_nonneg {ρ a s : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 1) (hs : |s| + a ≤ 1) :
    0 ≤ localMeanCorrection ρ a s := by
  have hs1 : s ∈ Icc (a - 1) (1 - a) := by
    have hl := neg_abs_le s
    have hu := le_abs_self s
    constructor <;> linarith
  have hs2 : -s ∈ Icc (a - 1) (1 - a) := by
    constructor <;> linarith [hs1.1, hs1.2]
  have h := (localMeanCorrection_convex hρ ha).2 hs1 hs2
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at h
  rw [show (1 / 2 : ℝ) * s + (1 / 2) * -s = 0 by ring,
    localMeanCorrection_zero, localMeanCorrection_even] at h
  linarith

@[simp] theorem localDeficit_one (ρ : ℝ) : localDeficit ρ 1 = 0 := by
  simp [localDeficit]

theorem localDeficit_threshold_069 : (0 : ℝ) < localDeficit (457 / 500) (69 / 100) := by
  exact Certificate.local_threshold_069

theorem localDeficit_concave {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (localDeficit ρ) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hrx : ρ * x ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · nlinarith [mul_nonneg hρ.1 hx.1]
    · nlinarith [hx.2, mul_nonneg (sub_nonneg.mpr hρ.2) hx.1]
  have hry : ρ * y ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · nlinarith [mul_nonneg hρ.1 hy.1]
    · nlinarith [hy.2, mul_nonneg (sub_nonneg.mpr hρ.2) hy.1]
  have h := signEntropy_strictConcave.concaveOn.2 hrx hry ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have hr2 : 0 ≤ 1 - ρ ^ 2 := by nlinarith [mul_nonneg hρ.1 (sub_nonneg.mpr hρ.2)]
  have hm := mul_le_mul_of_nonneg_left h hr2
  have heq : ρ * (a * x + b * y) = a * (ρ * x) + b * (ρ * y) := by ring
  unfold localDeficit
  rw [heq]
  nlinarith [congrArg (fun z : ℝ => z * signEntropy ρ) hab]

theorem localDeficit_strictConcave {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    StrictConcaveOn ℝ (Icc (0 : ℝ) 1) (localDeficit ρ) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hrx : ρ * x ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · nlinarith [mul_nonneg hρ.1.le hx.1]
    · nlinarith [hx.2, mul_nonneg (sub_nonneg.mpr hρ.2.le) hx.1]
  have hry : ρ * y ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · nlinarith [mul_nonneg hρ.1.le hy.1]
    · nlinarith [hy.2, mul_nonneg (sub_nonneg.mpr hρ.2.le) hy.1]
  have hrne : ρ * x ≠ ρ * y := by
    intro h
    exact hxy (mul_left_cancel₀ (ne_of_gt hρ.1) h)
  have h := signEntropy_strictConcave.2 hrx hry hrne ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have hr2 : 0 < 1 - ρ ^ 2 := by nlinarith [mul_pos hρ.1 (sub_pos.mpr hρ.2)]
  have hm := mul_lt_mul_of_pos_left h hr2
  have heq : ρ * (a * x + b * y) = a * (ρ * x) + b * (ρ * y) := by ring
  unfold localDeficit
  rw [heq]
  nlinarith [congrArg (fun z : ℝ => z * signEntropy ρ) hab]

theorem localDeficit_nonneg_of_threshold {ρ A a : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1)
    (hA : A ∈ Icc (0 : ℝ) 1) (ha : a ∈ Icc A 1) (hM : 0 ≤ localDeficit ρ A) :
    0 ≤ localDeficit ρ a := by
  have h := (localDeficit_concave hρ).min_le_of_mem_Icc hA
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) ha
  rw [localDeficit_one, min_eq_right hM] at h
  exact h

end
end CK
