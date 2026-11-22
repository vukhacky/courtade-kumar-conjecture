module

public import CK.Low.LocalScalar
public import CK.Fourier.Walsh

/-! Exact one-coordinate posterior entropy comparison at arbitrary mean.
The selected coordinate is arbitrary; coefficients of either sign are included. -/

@[expose] public section
set_option autoImplicit false
namespace CK
noncomputable section

def bitMix (ρ a b : ℝ) (c : Bool) : ℝ :=
  bitKernel ρ c false * a + bitKernel ρ c true * b

def sectionLift {n : ℕ} (f : BooleanFunction (n + 1)) (i : Fin (n + 1))
    (b : Bool) : Cube n → ℝ := fun x => lift f (i.insertNth b x)

def singleNoiseSection {n : ℕ} (ρ : ℝ) (f : BooleanFunction (n + 1))
    (i : Fin (n + 1)) (b : Bool) : Cube n → ℝ :=
  fun x => bitMix ρ (sectionLift f i false x) (sectionLift f i true x) b

theorem bitMix_mem_Icc {ρ a b : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (ha : a ∈ Set.Icc (-1 : ℝ) 1) (hb : b ∈ Set.Icc (-1 : ℝ) 1) (c : Bool) :
    bitMix ρ a b c ∈ Set.Icc (-1 : ℝ) 1 := by
  have h0 := bitKernel_nonneg ⟨by linarith [hρ.1], hρ.2⟩ c false
  have h1 := bitKernel_nonneg ⟨by linarith [hρ.1], hρ.2⟩ c true
  have hsum : bitKernel ρ c false + bitKernel ρ c true = 1 := by
    simpa only [Fintype.sum_bool, add_comm] using bitKernel_sum ρ c
  unfold bitMix
  constructor
  · nlinarith [mul_nonneg h0 (by linarith [ha.1] : 0 ≤ a + 1),
      mul_nonneg h1 (by linarith [hb.1] : 0 ≤ b + 1)]
  · nlinarith [mul_nonneg h0 (by linarith [ha.2] : 0 ≤ 1 - a),
      mul_nonneg h1 (by linarith [hb.2] : 0 ≤ 1 - b)]

theorem bitMix_boolean_entropy (ρ : ℝ) (a b : Bool) :
    (signEntropy (bitMix ρ (sign a) (sign b) false) +
      signEntropy (bitMix ρ (sign a) (sign b) true)) / 2 =
      |(sign b - sign a) / 2| * signEntropy ρ := by
  cases a <;> cases b <;> simp only [bitMix, bitKernel, sign_false, sign_true,
    Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  all_goals ring_nf
  all_goals simp
  all_goals ring

theorem mean_eq_section_avgs {n : ℕ} (f : BooleanFunction (n + 1)) (i : Fin (n + 1)) :
    mean f = (avg (sectionLift f i false) + avg (sectionLift f i true)) / 2 := by
  rw [mean, avg_cube_insertNth i, avg_pair]
  rfl

theorem fourier_singleton_eq_section_avgs {n : ℕ}
    (f : BooleanFunction (n + 1)) (i : Fin (n + 1)) :
    fourier (lift f) {i} = (avg (sectionLift f i true) - avg (sectionLift f i false)) / 2 := by
  rw [fourier_singleton, avg_cube_insertNth i]
  simp only [Fin.insertNth_apply_same, sign_false, sign_true, mul_neg_one, mul_one]
  rw [avg_pair, avg_neg]
  change (- avg (sectionLift f i false) + avg (sectionLift f i true)) / 2 = _
  ring

theorem abs_mean_add_abs_singleton_le_one_succ {n : ℕ}
    (f : BooleanFunction (n + 1)) (i : Fin (n + 1)) :
    |mean f| + |fourier (lift f) {i}| ≤ 1 := by
  have hf : avg (sectionLift f i false) ∈ Set.Icc (-1 : ℝ) 1 :=
    mean_mem_Icc (fun x => f (i.insertNth false x))
  have ht : avg (sectionLift f i true) ∈ Set.Icc (-1 : ℝ) 1 :=
    mean_mem_Icc (fun x => f (i.insertNth true x))
  have hm := mean_eq_section_avgs f i
  have ha := fourier_singleton_eq_section_avgs f i
  rcases le_total 0 (mean f) with hmp | hmn
  · rw [abs_of_nonneg hmp]
    rcases le_total 0 (fourier (lift f) {i}) with hap | han
    · rw [abs_of_nonneg hap]; linarith [ht.2]
    · rw [abs_of_nonpos han]; linarith [hf.2]
  · rw [abs_of_nonpos hmn]
    rcases le_total 0 (fourier (lift f) {i}) with hap | han
    · rw [abs_of_nonneg hap]; linarith [hf.1]
    · rw [abs_of_nonpos han]; linarith [ht.1]

theorem abs_mean_add_abs_singleton_le_one {n : ℕ}
    (f : BooleanFunction n) (i : Fin n) : |mean f| + |fourier (lift f) {i}| ≤ 1 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n => exact abs_mean_add_abs_singleton_le_one_succ f i

theorem avg_singleNoiseSection {n : ℕ} (ρ : ℝ) (f : BooleanFunction (n + 1))
    (i : Fin (n + 1)) (b : Bool) :
    avg (singleNoiseSection ρ f i b) = mean f + sign b * ρ * fourier (lift f) {i} := by
  unfold singleNoiseSection bitMix
  rw [avg_add, avg_smul, avg_smul, mean_eq_section_avgs f i, fourier_singleton_eq_section_avgs f i]
  cases b <;> simp only [bitKernel, sign_false, sign_true, Bool.false_eq_true,
    Bool.true_eq_false, ↓reduceIte] <;> ring

theorem noise_singleNoiseSection {n : ℕ} (ρ : ℝ) (f : BooleanFunction (n + 1))
    (i : Fin (n + 1)) (b : Bool) (x : Cube n) :
    noise ρ (singleNoiseSection ρ f i b) x = noise ρ (lift f) (i.insertNth b x) := by
  unfold singleNoiseSection bitMix
  rw [noise_add, noise_smul, noise_smul, noise_insertNth]
  rfl

theorem avg_singleNoiseSection_entropy {n : ℕ} (ρ : ℝ)
    (f : BooleanFunction (n + 1)) (i : Fin (n + 1)) :
    (avg (fun x => signEntropy (singleNoiseSection ρ f i false x)) +
      avg (fun x => signEntropy (singleNoiseSection ρ f i true x))) / 2 =
      signEntropy ρ * avg (fun x => |(sectionLift f i true x - sectionLift f i false x) / 2|) := by
  rw [← avg_pair]
  change avg (fun x => (signEntropy (bitMix ρ (sign (f (i.insertNth false x)))
    (sign (f (i.insertNth true x))) false) + signEntropy (bitMix ρ (sign (f (i.insertNth false x)))
    (sign (f (i.insertNth true x))) true)) / 2) = _
  simp_rw [bitMix_boolean_entropy]
  rw [show (fun x : Cube n => |(sign (f (i.insertNth true x)) - sign (f (i.insertNth false x))) / 2| * signEntropy ρ) =
    (fun x : Cube n => signEntropy ρ * |(sectionLift f i true x - sectionLift f i false x) / 2|) by
      funext x; dsimp [sectionLift, lift]; ring, avg_smul]

theorem abs_singleton_le_avg_section_difference {n : ℕ}
    (f : BooleanFunction (n + 1)) (i : Fin (n + 1)) :
    |fourier (lift f) {i}| ≤ avg (fun x => |(sectionLift f i true x - sectionLift f i false x) / 2|) := by
  have h := abs_avg_le_avg_abs (fun x => (sectionLift f i true x - sectionLift f i false x) / 2)
  rw [avg_div, avg_sub, ← fourier_singleton_eq_section_avgs f i] at h
  exact h

theorem posteriorEntropy_ge_coordinate_succ {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (f : BooleanFunction (n + 1)) (i : Fin (n + 1)) :
    (1 - ρ ^ 2) / 2 *
      (signEntropy (mean f + ρ * fourier (lift f) {i}) +
       signEntropy (mean f - ρ * fourier (lift f) {i})) +
      ρ ^ 2 * |fourier (lift f) {i}| * signEntropy ρ ≤ posteriorEntropy ρ f := by
  have hrange (b : Bool) (x : Cube n) : singleNoiseSection ρ f i b x ∈ Set.Icc (-1 : ℝ) 1 :=
    bitMix_mem_Icc hρ (sign_mem_Icc _) (sign_mem_Icc _) b
  have hfalse := signEntropy_noise_ge hρ (singleNoiseSection ρ f i false) (hrange false)
  have htrue := signEntropy_noise_ge hρ (singleNoiseSection ρ f i true) (hrange true)
  have hpost : posteriorEntropy ρ f =
      (avg (fun x => signEntropy (noise ρ (singleNoiseSection ρ f i false) x)) +
        avg (fun x => signEntropy (noise ρ (singleNoiseSection ρ f i true) x))) / 2 := by
    unfold posteriorEntropy
    rw [avg_cube_insertNth i, avg_pair]
    simp_rw [← noise_singleNoiseSection]
  have hlocal := avg_singleNoiseSection_entropy ρ f i
  have hcoeff := abs_singleton_le_avg_section_difference f i
  have hH : 0 ≤ signEntropy ρ := signEntropy_nonneg ⟨by linarith [hρ.1], hρ.2⟩
  have hweighted := mul_le_mul_of_nonneg_left hcoeff (mul_nonneg (sq_nonneg ρ) hH)
  rw [avg_singleNoiseSection, sign_false, neg_one_mul,
    show mean f + -ρ * fourier (lift f) {i} = mean f - ρ * fourier (lift f) {i} by ring] at hfalse
  rw [avg_singleNoiseSection, sign_true, one_mul] at htrue
  rw [hpost]
  nlinarith [congrArg (fun z : ℝ => ρ ^ 2 * z) hlocal]

theorem posteriorEntropy_ge_coordinate {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (f : BooleanFunction n) (i : Fin n) :
    (1 - ρ ^ 2) / 2 *
      (signEntropy (mean f + ρ * fourier (lift f) {i}) +
       signEntropy (mean f - ρ * fourier (lift f) {i})) +
      ρ ^ 2 * |fourier (lift f) {i}| * signEntropy ρ ≤ posteriorEntropy ρ f := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n => exact posteriorEntropy_ge_coordinate_succ hρ f i

theorem signEntropy_pair_abs (ρ a s : ℝ) :
    signEntropy (s + ρ * a) + signEntropy (s - ρ * a) =
      signEntropy (s + ρ * |a|) + signEntropy (s - ρ * |a|) := by
  rcases le_total 0 a with hp | hn
  · rw [abs_of_nonneg hp]
  · rw [abs_of_nonpos hn,
      show s + ρ * -a = s - ρ * a by ring,
      show s - ρ * -a = s + ρ * a by ring]
    ring

theorem localMeanCorrection_eq_signEntropy (ρ a s : ℝ) :
    localMeanCorrection ρ a s = phi s + (1 - ρ ^ 2) *
      ((signEntropy (s + ρ * a) + signEntropy (s - ρ * a)) / 2 - signEntropy (ρ * a)) := by
  simp only [signEntropy_eq_log_two_sub_phi]
  unfold localMeanCorrection
  ring

/-- The source local deficit inequality, uniformly over all means and
dimensions, for the absolute value of any specified singleton coefficient. -/
theorem information_deficit_ge_local {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (f : BooleanFunction n) (i : Fin n) :
    localDeficit ρ |fourier (lift f) {i}| ≤ phi ρ - information ρ f := by
  let a := |fourier (lift f) {i}|
  have hma := abs_mean_add_abs_singleton_le_one f i
  have ha : a ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨abs_nonneg _, by dsimp [a]; linarith [abs_nonneg (mean f)]⟩
  have hB := localMeanCorrection_nonneg hρ ha hma
  have hpost := posteriorEntropy_ge_coordinate hρ f i
  rw [signEntropy_pair_abs] at hpost
  have hid : localDeficit ρ a + localMeanCorrection ρ a (mean f) =
      phi (mean f) - signEntropy ρ + (1 - ρ ^ 2) / 2 *
        (signEntropy (mean f + ρ * a) + signEntropy (mean f - ρ * a)) +
        ρ ^ 2 * a * signEntropy ρ := by
    rw [localMeanCorrection_eq_signEntropy]
    unfold localDeficit
    ring
  have hgap : phi ρ - information ρ f = posteriorEntropy ρ f + phi (mean f) - signEntropy ρ := by
    rw [information_eq_signEntropy_sub_posterior, signEntropy_eq_log_two_sub_phi ρ,
      signEntropy_eq_log_two_sub_phi (mean f)]
    ring
  rw [hgap]
  change localDeficit ρ a ≤ _
  change _ + ρ ^ 2 * a * signEntropy ρ ≤ _ at hpost
  linarith

theorem information_le_phi_of_localDeficit {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (f : BooleanFunction n) (i : Fin n)
    (hM : 0 ≤ localDeficit ρ |fourier (lift f) {i}|) : information ρ f ≤ phi ρ := by
  linarith [information_deficit_ge_local hρ f i]

theorem information_le_phi_of_local_threshold {n : ℕ} {ρ A : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hA : A ∈ Set.Icc (0 : ℝ) 1)
    (f : BooleanFunction n) (i : Fin n) (hcoeff : A ≤ |fourier (lift f) {i}|)
    (hM : 0 ≤ localDeficit ρ A) : information ρ f ≤ phi ρ := by
  have hm := abs_mean_add_abs_singleton_le_one f i
  have ha : |fourier (lift f) {i}| ∈ Set.Icc A 1 :=
    ⟨hcoeff, by linarith [abs_nonneg (mean f)]⟩
  exact information_le_phi_of_localDeficit hρ f i
    (localDeficit_nonneg_of_threshold hρ hA ha hM)

theorem information_le_phi_at_0914_of_large_singleton {n : ℕ}
    (f : BooleanFunction n) (i : Fin n) (hcoeff : (69 / 100 : ℝ) ≤ |fourier (lift f) {i}|) :
    information (457 / 500) f ≤ phi (457 / 500) :=
  information_le_phi_of_local_threshold (by norm_num) (by norm_num) f i hcoeff
    localDeficit_threshold_069.le

end
end CK
