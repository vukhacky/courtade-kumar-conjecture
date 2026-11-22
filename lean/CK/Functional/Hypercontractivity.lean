module

public import CK.Functional.TwoPointBonami
public import CK.Functional.MixedNorm

/-! Bonami's restricted hypercontractivity, tensorized directly from the
proved two-point inequality by finite Minkowski. Uniform-cube `L^p` norms
are explicit finite averages, with no measure-theoretic convention hidden. -/

@[expose] public section
set_option autoImplicit false
namespace CK
noncomputable section

def cubeLpNorm {n : ℕ} (p : ℝ) (g : Cube n → ℝ) : ℝ :=
  (avg (fun x => |g x|^p))^(1/p)

theorem avg_nonneg {n : ℕ} (g : Cube n → ℝ) (hg : ∀ x, 0 ≤ g x) : 0 ≤ avg g := by
  have h := avg_mono hg
  simpa only [avg_const] using h

theorem sq_rpow_half {a : ℝ} (ha : 0 ≤ a) (p : ℝ) : (a^2)^(p/2)=a^p := by
  rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha]
  congr 1
  ring

theorem pairPowerMean_two_div {p a b : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    pairPowerMean (2/p) (a^p) (b^p) = ((a^2+b^2)/2)^(p/2) := by
  unfold pairPowerMean
  rw [← Real.rpow_mul ha, ← Real.rpow_mul hb,
    show p*(2/p) = 2 by field_simp,
    show 1/(2/p) = p/2 by field_simp]
  norm_num

theorem rpow_half_le_iff {p a b : ℝ} (hp : 0 < p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a^(p/2) ≤ b ↔ a ≤ b^(2/p) := by
  have h := Real.le_rpow_inv_iff_of_pos ha hb (div_pos hp (by norm_num : (0:ℝ)<2))
  simpa only [show (p/2)⁻¹=2/p by field_simp] using h.symm

def headNoise {n : ℕ} (η : ℝ) (g : Cube (n+1) → ℝ) (b : Bool) (x : Cube n) : ℝ :=
  bitKernel η b false*g (Fin.cons false x) + bitKernel η b true*g (Fin.cons true x)

theorem headNoise_nonneg {n : ℕ} {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (g : Cube (n+1) → ℝ) (hg : ∀ x, 0 ≤ g x) (b : Bool) (x : Cube n) :
    0 ≤ headNoise η g b x := by
  have hr : η ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hη.1],hη.2⟩
  exact add_nonneg (mul_nonneg (bitKernel_nonneg hr _ _) (hg _))
    (mul_nonneg (bitKernel_nonneg hr _ _) (hg _))

theorem noise_headNoise {n : ℕ} (η : ℝ) (g : Cube (n+1) → ℝ) (b : Bool) (x : Cube n) :
    noise η (headNoise η g b) x = noise η g (Fin.cons b x) := by
  unfold headNoise
  rw [noise_add, noise_smul, noise_smul, noise_cons]

theorem headNoise_bonami {n : ℕ} {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (g : Cube (n+1) → ℝ) (hg : ∀ x, 0 ≤ g x) (x : Cube n) :
    ((headNoise η g false x^2 + headNoise η g true x^2)/2)^((1+η^2)/2) ≤
      (g (Fin.cons false x)^(1+η^2) + g (Fin.cons true x)^(1+η^2))/2 := by
  have hp : (1+η^2) ∈ Set.Icc (1 : ℝ) 2 := ⟨by nlinarith [sq_nonneg η], by nlinarith [hη.1,hη.2]⟩
  have h := bonami_twoPoint hp (hg (Fin.cons false x)) (hg (Fin.cons true x))
  have he : (headNoise η g false x^2 + headNoise η g true x^2)/2 =
      ((g (Fin.cons false x)+g (Fin.cons true x))/2)^2 +
        ((1+η^2)-1)*((g (Fin.cons false x)-g (Fin.cons true x))/2)^2 := by
    simp only [headNoise, bitKernel, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
    ring
  rw [he]
  exact h

theorem noise_cube_zero (η : ℝ) (g : Cube 0 → ℝ) (x : Cube 0) : noise η g x = g x := by
  have hx : x = default := Subsingleton.elim _ _
  subst x
  simp [noise,bscKernel]
  congr 1
  exact Subsingleton.elim _ _

/-- Powered hypercontractivity for nonnegative cube functions. -/
theorem cube_hypercontractivity_power_nonneg (n : ℕ) {η : ℝ}
    (hη : η ∈ Set.Icc (0 : ℝ) 1) (g : Cube n → ℝ) (hg : ∀ x, 0 ≤ g x) :
    (avg (fun x => noise η g x^2))^((1+η^2)/2) ≤ avg (fun x => g x^(1+η^2)) := by
  let p : ℝ := 1+η^2
  have hp0 : 0 < p := by dsimp [p]; positivity
  have hp2 : p ≤ 2 := by dsimp [p]; nlinarith [hη.1,hη.2]
  change (avg (fun x => noise η g x^2))^(p/2) ≤ avg (fun x => g x^p)
  induction n with
  | zero =>
    rw [avg_cube_zero,avg_cube_zero,noise_cube_zero,sq_rpow_half (hg _) p]
  | succ n ih =>
    let k0 : Cube n → ℝ := headNoise η g false
    let k1 : Cube n → ℝ := headNoise η g true
    have hk0 : ∀ x, 0 ≤ k0 x := headNoise_nonneg hη g hg false
    have hk1 : ∀ x, 0 ≤ k1 x := headNoise_nonneg hη g hg true
    have h0 := ih k0 hk0
    have h1 := ih k1 hk1
    have h0' := (rpow_half_le_iff hp0 (avg_nonneg _ (fun x => sq_nonneg _))
      (avg_nonneg _ (fun x => Real.rpow_nonneg (hk0 x) p))).mp h0
    have h1' := (rpow_half_le_iff hp0 (avg_nonneg _ (fun x => sq_nonneg _))
      (avg_nonneg _ (fun x => Real.rpow_nonneg (hk1 x) p))).mp h1
    have hq : 1 ≤ 2/p := (le_div_iff₀ hp0).mpr (by simpa using hp2)
    have hmix := pairPowerMean_avg_le hq (fun x => k0 x^p) (fun x => k1 x^p)
      (fun x => Real.rpow_nonneg (hk0 x) p) (fun x => Real.rpow_nonneg (hk1 x) p)
    have he : avg (fun x => noise η g x^2) =
        (avg (fun x => noise η k0 x^2) + avg (fun x => noise η k1 x^2))/2 := by
      rw [avg_cube_cons, avg_pair]
      simp only [k0,k1,noise_headNoise]
    calc
      (avg (fun x => noise η g x^2))^(p/2) ≤
          pairPowerMean (2/p) (avg (fun x => k0 x^p)) (avg (fun x => k1 x^p)) := by
        unfold pairPowerMean
        rw [show 1/(2/p)=p/2 by field_simp]
        apply Real.rpow_le_rpow (avg_nonneg _ (fun x => sq_nonneg _))
        · rw [he]
          linarith
        · positivity
      _ ≤ avg (fun x => pairPowerMean (2/p) (k0 x^p) (k1 x^p)) := hmix
      _ = avg (fun x => ((k0 x^2+k1 x^2)/2)^(p/2)) := by
        congr 1
        funext x
        exact pairPowerMean_two_div hp0 (hk0 x) (hk1 x)
      _ ≤ avg (fun x => (g (Fin.cons false x)^p+g (Fin.cons true x)^p)/2) := by
        apply avg_mono
        intro x
        exact headNoise_bonami hη g hg x
      _ = avg (fun x => g x^p) := (avg_cube_cons (fun x : Cube (n+1) => g x^p)).symm

theorem abs_noise_le_noise_abs_nonneg {n : ℕ} {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (g : Cube n → ℝ) (x : Cube n) : |noise η g x| ≤ noise η (fun y => |g y|) x := by
  unfold noise
  calc
    _ ≤ ∑ y, |bscKernel η x y*g y| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      rw [abs_mul, abs_of_nonneg (bscKernel_nonneg ⟨by linarith [hη.1],hη.2⟩ x y)]

/-- Powered hypercontractivity for signed real cube functions. -/
theorem cube_hypercontractivity_power {n : ℕ} {η : ℝ}
    (hη : η ∈ Set.Icc (0 : ℝ) 1) (g : Cube n → ℝ) :
    (avg (fun x => noise η g x^2))^((1+η^2)/2) ≤ avg (fun x => |g x|^(1+η^2)) := by
  have hs (x : Cube n) : noise η g x^2 ≤ noise η (fun y => |g y|) x^2 := by
    have h := abs_noise_le_noise_abs_nonneg hη g x
    have hn := noise_nonneg_values hη (fun y => |g y|) (fun y => abs_nonneg (g y)) x
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hn).mpr h
  have h := Real.rpow_le_rpow (avg_nonneg _ (fun x => sq_nonneg _)) (avg_mono hs)
    (show 0 ≤ (1+η^2)/2 by positivity)
  exact h.trans (cube_hypercontractivity_power_nonneg n hη _ (fun x => abs_nonneg (g x)))

theorem cube_hypercontractivity_sq {n : ℕ} {η : ℝ}
    (hη : η ∈ Set.Icc (0 : ℝ) 1) (g : Cube n → ℝ) :
    avg (fun x => noise η g x^2) ≤ (avg (fun x => |g x|^(1+η^2)))^(2/(1+η^2)) := by
  exact (rpow_half_le_iff (by positivity : 0 < 1+η^2)
    (avg_nonneg _ (fun x => sq_nonneg _))
    (avg_nonneg _ (fun x => Real.rpow_nonneg (abs_nonneg _) _))).mp
    (cube_hypercontractivity_power hη g)

/-- The restricted Bonami inequality required by the STOC proof, with exact
uniform-cube norms, all signed functions, zeros, and both noise endpoints. -/
theorem cube_hypercontractivity {n : ℕ} {η : ℝ}
    (hη : η ∈ Set.Icc (0 : ℝ) 1) (g : Cube n → ℝ) :
    cubeLpNorm 2 (noise η g) ≤ cubeLpNorm (1+η^2) g := by
  have hp : 0 < 1+η^2 := by positivity
  have h := Real.rpow_le_rpow
    (Real.rpow_nonneg (avg_nonneg _ (fun x => sq_nonneg (noise η g x))) _)
    (cube_hypercontractivity_power hη g) (one_div_nonneg.mpr hp.le)
  rw [← Real.rpow_mul (avg_nonneg _ (fun x => sq_nonneg (noise η g x))),
    show ((1+η^2)/2)*(1/(1+η^2))=1/2 by field_simp] at h
  simpa only [cubeLpNorm, Real.rpow_two, sq_abs] using h

end
end CK
