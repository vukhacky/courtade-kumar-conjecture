module

public import CK.Functional.Product
public import CK.Analysis.BinaryEntropy
public import CK.Fourier.Noise
public import CK.Certificate.LogBounds

/-! Entropy contraction for every finite Boolean cube, proved by induction
over coordinates. The scalar contraction and convexity of conditional
two-point entropy handle nonnegative functions directly, including zeros. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

theorem twoPointEntropy_noise_le {η a b : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    twoPointEntropy (((1 + η) / 2) * a + ((1 - η) / 2) * b)
      (((1 - η) / 2) * a + ((1 + η) / 2) * b) ≤ η ^ 2 * twoPointEntropy a b := by
  by_cases hab : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  let m := (a + b) / 2
  let t := (a - b) / (a + b)
  have hm : 0 ≤ m := by dsimp [m]; positivity
  have heq₁ : ((1 + η) / 2) * a + ((1 - η) / 2) * b = m * (1 + η * t) := by
    dsimp [m, t]
    field_simp
    ring
  have heq₂ : ((1 - η) / 2) * a + ((1 + η) / 2) * b = m * (1 - η * t) := by
    dsimp [m, t]
    field_simp
    ring
  rw [heq₁, heq₂, twoPointEntropy_smul, twoPointEntropy_eq_phi,
    twoPointEntropy_mean_phi ha hb]
  have h := mul_le_mul_of_nonneg_left (phi_mul_le_sq_mul hη (pair_ratio_mem_Icc ha hb)) hm
  dsimp [m, t] at h ⊢
  nlinarith

/-- The sharp entropy contraction factor of the BSC product noise.
This is the full all-dimensional statement, with no tensorization or
external analytic inequality left as a hypothesis. -/
theorem entropyFunctional_noise_le (n : ℕ) {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (v : Cube n → ℝ) (hv : ∀ x, 0 ≤ v x) :
    entropyFunctional (noise η v) ≤ η ^ 2 * entropyFunctional v := by
  induction n with
  | zero => simp [entropyFunctional_cube_zero]
  | succ n ih =>
    let a : Cube n → ℝ := fun x => v (Fin.cons false x)
    let b : Cube n → ℝ := fun x => v (Fin.cons true x)
    let m : Cube n → ℝ := fun x => (a x + b x) / 2
    have ha : ∀ x, 0 ≤ a x := fun x => hv _
    have hb : ∀ x, 0 ≤ b x := fun x => hv _
    have hm : ∀ x, 0 ≤ m x := fun x =>
      div_nonneg (add_nonneg (ha x) (hb x)) (by norm_num)
    have hfirst : avg (fun x : Cube n =>
        twoPointEntropy (noise η v (Fin.cons false x)) (noise η v (Fin.cons true x))) ≤
        η ^ 2 * avg (fun x => twoPointEntropy (noise η a x) (noise η b x)) := by
      rw [← avg_smul]
      apply avg_mono
      intro x
      rw [noise_cons, noise_cons]
      simp only [bitKernel, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false]
      exact twoPointEntropy_noise_le hη (noise_nonneg_values hη a ha x)
        (noise_nonneg_values hη b hb x)
    have hmean : (fun x : Cube n =>
        (noise η v (Fin.cons false x) + noise η v (Fin.cons true x)) / 2) = noise η m := by
      funext x
      exact noise_mean_sections η v x
    rw [entropyFunctional_chain, hmean]
    calc
      _ ≤ η ^ 2 * avg (fun x => twoPointEntropy (noise η a x) (noise η b x)) +
          η ^ 2 * entropyFunctional m := add_le_add hfirst (ih m hm)
      _ ≤ η ^ 2 * avg (fun x => twoPointEntropy (a x) (b x)) +
          η ^ 2 * entropyFunctional m :=
        add_le_add (mul_le_mul_of_nonneg_left (avg_twoPointEntropy_noise_le hη a b ha hb)
          (sq_nonneg η)) le_rfl
      _ = η ^ 2 * entropyFunctional v := by
        rw [entropyFunctional_chain]
        dsimp [a, b, m]
        ring

theorem mulLog_one_add_add_one_sub (t : ℝ) :
    (1 + t) * Real.log (1 + t) + (1 - t) * Real.log (1 - t) = 2 * phi t := by
  have h := twoPointEntropy_eq_phi t
  unfold twoPointEntropy at h
  rw [show ((1 + t) + (1 - t)) / 2 = (1 : ℝ) by ring] at h
  simp only [Real.log_one, mul_zero, sub_zero] at h
  linarith

/-- Exact mean-corrected entropy identity. It is algebraic and does not
assume that the cube function is balanced. -/
theorem entropyFunctional_one_add_one_sub {n : ℕ} (g : Cube n → ℝ) :
    entropyFunctional (fun x => 1 + g x) + entropyFunctional (fun x => 1 - g x) =
      2 * (avg (fun x => phi (g x)) - phi (avg g)) := by
  have hplus : avg (fun x => 1 + g x) = 1 + avg g := by rw [avg_add, avg_const]
  have hminus : avg (fun x => 1 - g x) = 1 - avg g := by rw [avg_sub, avg_const]
  have hsum : avg (fun x => (1 + g x) * Real.log (1 + g x)) +
      avg (fun x => (1 - g x) * Real.log (1 - g x)) = 2 * avg (fun x => phi (g x)) := by
    rw [← avg_add]
    simp_rw [mulLog_one_add_add_one_sub]
    rw [avg_smul]
  unfold entropyFunctional
  rw [hplus, hminus]
  linarith [mulLog_one_add_add_one_sub (avg g)]

theorem phi_noise_gap_le {n : ℕ} {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1)
    (g : Cube n → ℝ) (hg : ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1) :
    avg (fun x => phi (noise η g x)) - phi (avg g) ≤
      η ^ 2 * (avg (fun x => phi (g x)) - phi (avg g)) := by
  have hp := entropyFunctional_noise_le n hη (fun x => 1 + g x)
    (fun x => by linarith [(hg x).1])
  have hm := entropyFunctional_noise_le n hη (fun x => 1 - g x)
    (fun x => by linarith [(hg x).2])
  have hnoiseplus : noise η (fun x => 1 + g x) = fun x => 1 + noise η g x := by
    funext x
    rw [noise_add, noise_const]
  have hnoiseminus : noise η (fun x => 1 - g x) = fun x => 1 - noise η g x := by
    funext x
    rw [noise_sub, noise_const]
  rw [hnoiseplus] at hp
  rw [hnoiseminus] at hm
  suffices h : 2 * (avg (fun x => phi (noise η g x)) - phi (avg g)) ≤
      2 * (η ^ 2 * (avg (fun x => phi (g x)) - phi (avg g))) by linarith
  calc
    2 * (avg (fun x => phi (noise η g x)) - phi (avg g)) =
        entropyFunctional (fun x => 1 + noise η g x) +
        entropyFunctional (fun x => 1 - noise η g x) := by
      rw [entropyFunctional_one_add_one_sub, avg_noise]
    _ ≤ η ^ 2 * entropyFunctional (fun x => 1 + g x) +
        η ^ 2 * entropyFunctional (fun x => 1 - g x) := add_le_add hp hm
    _ = η ^ 2 * (entropyFunctional (fun x => 1 + g x) +
        entropyFunctional (fun x => 1 - g x)) := by ring
    _ = 2 * (η ^ 2 * (avg (fun x => phi (g x)) - phi (avg g))) := by
      rw [entropyFunctional_one_add_one_sub]
      ring

theorem information_contraction {n : ℕ} {η ρ : ℝ}
    (hη : η ∈ Set.Icc (0 : ℝ) 1) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (f : BooleanFunction n) : information (η * ρ) f ≤ η ^ 2 * information ρ f := by
  have h := phi_noise_gap_le hη (noise ρ (lift f))
    (fun x => noise_mem_Icc ⟨by linarith [hρ.1], hρ.2⟩ (lift f)
      (fun y => sign_mem_Icc (f y)) x)
  simp only [noise_noise, avg_noise] at h
  exact h

theorem information_le_sq_mul_entropy_mean {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (f : BooleanFunction n) :
    information ρ f ≤ ρ ^ 2 * Real.binEntropy ((1 - mean f) / 2) := by
  have h := information_contraction hρ (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num) f
  simpa only [mul_one, information_one] using h

theorem entropy_mean_le_half_of_large_mean {n : ℕ} (f : BooleanFunction n)
    (hmean : (61 / 100 : ℝ) ≤ |mean f|) :
    Real.binEntropy ((1 - mean f) / 2) ≤ 1 / 2 := by
  have hdom := mean_mem_Icc f
  have habs : |mean f| ≤ 1 := abs_le.mpr hdom
  have heq : Real.binEntropy ((1 - mean f) / 2) =
      Real.binEntropy ((1 - |mean f|) / 2) := by
    rcases le_total 0 (mean f) with hp | hn
    · rw [abs_of_nonneg hp]
    · rw [abs_of_nonpos hn]
      simpa only [sub_neg_eq_add] using (binEntropy_sign_conventions (mean f)).symm
  rw [heq]
  calc
    _ ≤ Real.binEntropy (39 / 200) :=
      Real.binEntropy_strictMonoOn.monotoneOn
        ⟨by linarith, by have ha := abs_nonneg (mean f); linarith⟩
        (by norm_num) (by linarith)
    _ ≤ 1 / 2 := Certificate.largeMean_entropy_bound

/-- CK on the all-dimensional large-mean branch, in its analytic form.
The separate Shannon bridge transports this exact bound to mutual information. -/
theorem information_le_phi_of_large_mean {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (f : BooleanFunction n)
    (hmean : (61 / 100 : ℝ) ≤ |mean f|) : information ρ f ≤ phi ρ := by
  calc
    _ ≤ ρ ^ 2 * Real.binEntropy ((1 - mean f) / 2) := information_le_sq_mul_entropy_mean hρ f
    _ ≤ ρ ^ 2 * (1 / 2) := mul_le_mul_of_nonneg_left
      (entropy_mean_le_half_of_large_mean f hmean) (sq_nonneg ρ)
    _ = ρ ^ 2 / 2 := by ring
    _ ≤ phi ρ := sq_div_two_le_phi ⟨by linarith [hρ.1], hρ.2⟩

end
end CK
