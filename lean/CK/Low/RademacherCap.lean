module

public import CK.Fourier.Rademacher
public import CK.Low.FirstLevel
public import CK.Low.DegreeEnergy
public import CK.Certificate.RademacherMajorant

/-! The small-coefficient Rademacher estimate used in the low-correlation argument, proved by finite moments. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

theorem coefficientPower_nonneg_of_even {n k : ℕ} (c : Fin n → ℝ) (hk : Even k) :
    0 ≤ coefficientPower c k :=
  Finset.sum_nonneg (fun i _ => hk.pow_nonneg (c i))

theorem coefficientPower_four_le {n : ℕ} (c : Fin n → ℝ) {b : ℝ}
    (h2 : coefficientPower c 2 = 1) (hc : ∀ i, c i^2 ≤ b) : coefficientPower c 4 ≤ b := by
  calc
    _ = ∑ i, (c i)^2*(c i)^2 := by unfold coefficientPower; congr 1; funext i; ring
    _ ≤ ∑ i, b*(c i)^2 := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (hc i) (sq_nonneg (c i)))
    _ = b*coefficientPower c 2 := by simp only [coefficientPower, Finset.mul_sum]
    _ = b := by rw [h2, mul_one]

theorem coefficientPower_six_le {n : ℕ} (c : Fin n → ℝ) {b : ℝ}
    (hc : ∀ i, c i^2 ≤ b) : coefficientPower c 6 ≤ b*coefficientPower c 4 := by
  calc
    _ = ∑ i, (c i)^2*(c i)^4 := by unfold coefficientPower; congr 1; funext i; ring
    _ ≤ ∑ i, b*(c i)^4 := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (hc i) (by positivity))
    _ = _ := by simp only [coefficientPower, Finset.mul_sum]

theorem coefficientPower_ten_le {n : ℕ} (c : Fin n → ℝ) {b : ℝ}
    (hc : ∀ i, c i^2 ≤ b) : coefficientPower c 10 ≤ b^3*coefficientPower c 4 := by
  calc
    _ = ∑ i, ((c i)^2)^3*(c i)^4 := by unfold coefficientPower; congr 1; funext i; ring
    _ ≤ ∑ i, b^3*(c i)^4 := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sq_nonneg (c i)) (hc i) 3) (by positivity))
    _ = _ := by simp only [coefficientPower, Finset.mul_sum]

theorem coefficientPower_div {n : ℕ} (c : Fin n → ℝ) (r : ℝ) (k : ℕ) :
    coefficientPower (fun i => c i/r) k = coefficientPower c k / r^k := by
  simp only [coefficientPower, div_pow, Finset.sum_div]

theorem rademacher_div {n : ℕ} (c : Fin n → ℝ) (r : ℝ) (x : Cube n) :
    rademacher (fun i => c i/r) x = rademacher c x / r := by
  unfold rademacher
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem rademacher_correlation {n : ℕ} (c : Fin n → ℝ) (g : Cube n → ℝ) :
    avg (fun x => g x * rademacher c x) = ∑ i, c i * fourier g {i} := by
  unfold rademacher
  simp only [Finset.mul_sum]
  rw [avg_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [fourier_singleton, ← avg_smul]
  congr 1
  funext x
  ring

theorem firstLevel_le_avg_abs_rademacher {n : ℕ} (f : BooleanFunction n) :
    fourierWeight (lift f) 1 ≤ avg (fun x => |rademacher (fun i => fourier (lift f) {i}) x|) := by
  have h := avg_mono (lift_mul_le_abs f (rademacher (fun i => fourier (lift f) {i})))
  rw [rademacher_correlation] at h
  simpa only [fourierWeight_one, pow_two] using h

theorem coefficientPower_singletons {n : ℕ} (f : BooleanFunction n) :
    coefficientPower (fun i => fourier (lift f) {i}) 2 = fourierWeight (lift f) 1 :=
  (fourierWeight_one (lift f)).symm

theorem avg_rademacherMajorant {n : ℕ} (c : Fin n → ℝ)
    (h2 : coefficientPower c 2 = 1) :
    avg (fun x => Certificate.rademacherMajorant (rademacher c x)) =
      Certificate.rademacherMomentMajorant (coefficientPower c 4) (coefficientPower c 6)
        (coefficientPower c 8) (coefficientPower c 10) := by
  simp only [Certificate.rademacherMajorant, avg_add, avg_sub, avg_smul, avg_const,
    rademacher_moment_two, rademacher_moment_four, rademacher_moment_six,
    rademacher_moment_eight, rademacher_moment_ten, h2, one_pow, mul_one]
  rfl

/-- A specialized finite Rademacher theorem, proved from exact moments
through order ten and a globally nonnegative polynomial certificate. -/
theorem normalized_rademacher_abs_lt {n : ℕ} (c : Fin n → ℝ)
    (h2 : coefficientPower c 2 = 1) (hc : ∀ i, |c i| ≤ (2/5 : ℝ)) :
    avg (fun x => |rademacher c x|) < 7/8 := by
  have hsq (i : Fin n) : c i^2 ≤ (4/25 : ℝ) := by
    have h := abs_le.mp (hc i)
    nlinarith [h.1, h.2]
  have hp4 : coefficientPower c 4 ∈ Set.Icc (0 : ℝ) (4/25) :=
    ⟨coefficientPower_nonneg_of_even c (by decide), coefficientPower_four_le c h2 hsq⟩
  have hp6 : coefficientPower c 6 ∈ Set.Icc (0 : ℝ) ((4/25)*coefficientPower c 4) :=
    ⟨coefficientPower_nonneg_of_even c (by decide), coefficientPower_six_le c hsq⟩
  have hp8 : 0 ≤ coefficientPower c 8 := coefficientPower_nonneg_of_even c (by decide)
  have hp10 : coefficientPower c 10 ∈ Set.Icc (0 : ℝ) ((4/25)^3*coefficientPower c 4) :=
    ⟨coefficientPower_nonneg_of_even c (by decide), coefficientPower_ten_le c hsq⟩
  calc
    _ ≤ avg (fun x => Certificate.rademacherMajorant (rademacher c x)) :=
      avg_mono (fun x => Certificate.abs_le_rademacherMajorant _)
    _ = _ := avg_rademacherMajorant c h2
    _ < 7/8 := Certificate.rademacherMomentMajorant_lt hp4 hp6 hp8 hp10

/-- The small-singleton part of the exact cap used in the STOC proof.
The threshold comparison is rational; the dimension is arbitrary. -/
theorem firstLevel_lt_cap_of_small_singletons {n : ℕ} (f : BooleanFunction n)
    (hf : ∀ i, |fourier (lift f) {i}| ≤ (87831/250000 : ℝ)) :
    fourierWeight (lift f) 1 < 193027/250000 := by
  by_contra hlt
  have hW : (193027/250000 : ℝ) ≤ fourierWeight (lift f) 1 := le_of_not_gt hlt
  let r : ℝ := Real.sqrt (fourierWeight (lift f) 1)
  have hWpos : 0 < fourierWeight (lift f) 1 := lt_of_lt_of_le (by norm_num) hW
  have hr : 0 < r := Real.sqrt_pos.2 hWpos
  have hr2 : r^2 = fourierWeight (lift f) 1 := Real.sq_sqrt hWpos.le
  let c : Fin n → ℝ := fun i => fourier (lift f) {i}/r
  have hc2 : coefficientPower c 2 = 1 := by
    rw [show c = (fun i => fourier (lift f) {i}/r) by rfl, coefficientPower_div,
      coefficientPower_singletons, hr2, div_self (ne_of_gt hWpos)]
  have hth : (87831/250000 : ℝ) ≤ (2/5)*r := by
    have hsq : (87831/250000 : ℝ)^2 < (4/25)*r^2 := by rw [hr2]; nlinarith [hW]
    nlinarith
  have hc (i : Fin n) : |c i| ≤ (2/5 : ℝ) := by
    dsimp [c]
    rw [abs_div, abs_of_pos hr, div_le_iff₀ hr]
    exact (hf i).trans hth
  have hnorm := (normalized_rademacher_abs_lt c hc2 hc).le
  have hscale : avg (fun x => |rademacher c x|) =
      avg (fun x => |rademacher (fun i => fourier (lift f) {i}) x|) / r := by
    dsimp only [c]
    simp only [rademacher_div, abs_div, abs_of_pos hr, avg_div]
  rw [hscale] at hnorm
  have he := (div_le_iff₀ hr).mp hnorm
  have hfirst := firstLevel_le_avg_abs_rademacher f
  have hrle : r ≤ (7/8 : ℝ) := by
    exact le_of_mul_le_mul_right (show r*r ≤ (7/8)*r by nlinarith [hfirst, he, hr2]) hr
  have hsquare := pow_le_pow_left₀ hr.le hrle 2
  rw [hr2] at hsquare
  norm_num at hsquare
  linarith

theorem oddLift_small_cap {n : ℕ} (f : BooleanFunction n)
    (hmean : |mean f| ≤ (87831/250000 : ℝ))
    (hf : ∀ i, |fourier (lift f) {i}| ≤ (87831/250000 : ℝ)) :
    fourierWeight (lift f) 1 + mean f^2 < 193027/250000 := by
  rw [← fourierWeight_oddLift_one]
  apply firstLevel_lt_cap_of_small_singletons
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [fourier_oddLift_zero] using hmean
  · simpa only [fourier_oddLift_succ] using hf j

end
end CK
