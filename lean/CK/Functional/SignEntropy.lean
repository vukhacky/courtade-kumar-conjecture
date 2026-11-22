module

public import CK.Low.Contraction

/-! Entropy as a function of a sign mean, and the posterior-entropy form
of finite noise contraction. -/

@[expose] public section
set_option autoImplicit false
namespace CK
noncomputable section

def signEntropy (t : ℝ) : ℝ := Real.binEntropy ((1 - t) / 2)

def posteriorEntropy {n : ℕ} (ρ : ℝ) (f : BooleanFunction n) : ℝ :=
  avg (fun x => signEntropy (noise ρ (lift f) x))

theorem signEntropy_eq_log_two_sub_phi (t : ℝ) :
    signEntropy t = Real.log 2 - phi t := by unfold signEntropy phi; ring

@[simp] theorem signEntropy_zero : signEntropy 0 = Real.log 2 := by
  simp [signEntropy_eq_log_two_sub_phi]

@[simp] theorem signEntropy_one : signEntropy 1 = 0 := by
  simp [signEntropy_eq_log_two_sub_phi]

@[simp] theorem signEntropy_neg_one : signEntropy (-1) = 0 := by
  simp [signEntropy_eq_log_two_sub_phi]

@[simp] theorem signEntropy_neg (t : ℝ) : signEntropy (-t) = signEntropy t := by
  simp only [signEntropy_eq_log_two_sub_phi, phi_neg]

theorem signEntropy_nonneg {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ signEntropy t := by
  exact Real.binEntropy_nonneg (by linarith [ht.2]) (by linarith [ht.1])

theorem avg_signEntropy {n : ℕ} (g : Cube n → ℝ) :
    avg (fun x => signEntropy (g x)) = Real.log 2 - avg (fun x => phi (g x)) := by
  simp_rw [signEntropy_eq_log_two_sub_phi]
  rw [avg_sub, avg_const]

theorem signEntropy_noise_ge {n : ℕ} {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (g : Cube n → ℝ) (hg : ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1) :
    η ^ 2 * avg (fun x => signEntropy (g x)) + (1 - η ^ 2) * signEntropy (avg g) ≤
      avg (fun x => signEntropy (noise η g x)) := by
  have h := phi_noise_gap_le hη g hg
  rw [avg_signEntropy, avg_signEntropy, signEntropy_eq_log_two_sub_phi]
  nlinarith

theorem information_eq_signEntropy_sub_posterior {n : ℕ} (ρ : ℝ)
    (f : BooleanFunction n) : information ρ f = signEntropy (mean f) - posteriorEntropy ρ f := by
  exact information_eq_entropy_difference ρ f

@[fun_prop] theorem continuous_signEntropy : Continuous signEntropy := by
  unfold signEntropy
  fun_prop

theorem hasDerivAt_signEntropy {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt signEntropy (-phiSlope t) t := by
  convert (hasDerivAt_phi ht).const_sub (Real.log 2) using 1
  exact funext signEntropy_eq_log_two_sub_phi

theorem signEntropy_strictConcave : StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) signEntropy := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hx' : (1 - x) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hy' : (1 - y) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hy.1, hy.2]
  have hne : (1 - x) / 2 ≠ (1 - y) / 2 := by intro h; apply hxy; linarith
  have h := Real.strictConcave_binEntropy.2 hx' hy' hne ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have heq : (1 - (a * x + b * y)) / 2 = a * ((1 - x) / 2) + b * ((1 - y) / 2) := by
    nlinarith
  unfold signEntropy
  rw [heq]
  exact h

end
end CK
