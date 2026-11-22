module

public import CK.Low.FirstLevel
public import CK.Low.YuCap
public import CK.Low.RademacherCap
public import CK.Certificate.FourierCapScalar

/-! Balanced-to-biased section reduction for the first-level cap.
The identities hold at an arbitrary specified coordinate. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

theorem fourier_sectionMean {n : ℕ} (i : Fin (n+1)) (g : Cube (n+1) → ℝ)
    (S : Finset (Fin n)) :
    fourier (sectionMean i g) S =
      (fourier (fun x => g (i.insertNth false x)) S +
        fourier (fun x => g (i.insertNth true x)) S)/2 := by
  have h : sectionMean i g = fun x => (1/2 : ℝ) *
      (g (i.insertNth false x) + g (i.insertNth true x)) := by
    funext x
    unfold sectionMean
    ring
  rw [h, fourier_smul, fourier_add]
  ring

theorem firstLevel_sectionMean_le {n : ℕ} (i : Fin (n+1)) (g : Cube (n+1) → ℝ) :
    fourierWeight (sectionMean i g) 1 ≤
      (fourierWeight (fun x => g (i.insertNth false x)) 1 +
        fourierWeight (fun x => g (i.insertNth true x)) 1)/2 := by
  simp only [fourierWeight_one, fourier_sectionMean]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_le_sum
  intro j _
  nlinarith [sq_nonneg (fourier (fun x => g (i.insertNth false x)) {j} -
    fourier (fun x => g (i.insertNth true x)) {j})]

theorem mean_boolean_section_false {n : ℕ} (i : Fin (n+1)) (f : BooleanFunction (n+1)) :
    mean (fun x => f (i.insertNth false x)) = mean f - fourier (lift f) {i} := by
  have hm := avg_cube_insertNth i (lift f)
  rw [avg_pair] at hm
  have ha := fourier_singleton_eq_avg_sectionDifference i (lift f)
  change fourier (lift f) {i} = avg (fun x =>
    (lift f (i.insertNth true x)-lift f (i.insertNth false x))/2) at ha
  rw [avg_div, avg_sub] at ha
  change mean f = (mean (fun x => f (i.insertNth false x)) +
    mean (fun x => f (i.insertNth true x)))/2 at hm
  change fourier (lift f) {i} = (mean (fun x => f (i.insertNth true x)) -
    mean (fun x => f (i.insertNth false x)))/2 at ha
  linarith

theorem mean_boolean_section_true {n : ℕ} (i : Fin (n+1)) (f : BooleanFunction (n+1)) :
    mean (fun x => f (i.insertNth true x)) = mean f + fourier (lift f) {i} := by
  have hm := avg_cube_insertNth i (lift f)
  rw [avg_pair] at hm
  have ha := fourier_singleton_eq_avg_sectionDifference i (lift f)
  change fourier (lift f) {i} = avg (fun x =>
    (lift f (i.insertNth true x)-lift f (i.insertNth false x))/2) at ha
  rw [avg_div, avg_sub] at ha
  change mean f = (mean (fun x => f (i.insertNth false x)) +
    mean (fun x => f (i.insertNth true x)))/2 at hm
  change fourier (lift f) {i} = (mean (fun x => f (i.insertNth true x)) -
    mean (fun x => f (i.insertNth false x)))/2 at ha
  linarith

theorem balanced_coordinate_bound_of_biased_bound {n : ℕ} (f : BooleanFunction n)
    (hf : Balanced f) (i : Fin n) {C : ℝ}
    (hbound : ∀ m : ℕ, ∀ h : BooleanFunction m,
      |mean h| = |fourier (lift f) {i}| → fourierWeight (lift h) 1 ≤ C) :
    fourierWeight (lift f) 1 ≤ fourier (lift f) {i}^2+C := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hfalse := hbound n (fun x => f (i.insertNth false x)) (by
      rw [mean_boolean_section_false, show mean f = 0 from hf, zero_sub, abs_neg])
    have htrue := hbound n (fun x => f (i.insertNth true x)) (by
      rw [mean_boolean_section_true, show mean f = 0 from hf, zero_add])
    have hsec := firstLevel_sectionMean_le i (lift f)
    rw [fourierWeight_sectionMean i (lift f)]
    change fourierWeight (sectionMean i (lift f)) 1 ≤
      (fourierWeight (lift (fun x => f (i.insertNth false x))) 1 +
        fourierWeight (lift (fun x => f (i.insertNth true x))) 1)/2 at hsec
    linarith

theorem elementary_cap_lt_of_medium_coefficient {a : ℝ}
    (ha : a ∈ Set.Icc (87831/250000 : ℝ) (1/2)) : a^2+1-a < 193027/250000 := by
  have hm : 0 ≤ a - (87831/250000 : ℝ) := sub_nonneg.mpr ha.1
  have hn : a + (87831/250000 : ℝ) - 1 ≤ 0 := by linarith [ha.2]
  have hp := mul_nonpos_of_nonneg_of_nonpos hm hn
  nlinarith

theorem firstLevel_mean_lt_cap_of_medium_singleton {n : ℕ} (f : BooleanFunction n)
    (i : Fin n) (ha : |fourier (lift f) {i}| ∈ Set.Icc (87831/250000 : ℝ) (1/2)) :
    fourierWeight (lift f) 1 + mean f^2 < 193027/250000 := by
  have h := firstLevel_mean_coordinate_cap f i
  have hscalar := elementary_cap_lt_of_medium_coefficient ha
  rw [sq_abs] at hscalar
  exact h.trans_lt hscalar

theorem balanced_firstLevel_high_cap {n : ℕ} (f : BooleanFunction n) (hf : Balanced f)
    (i : Fin n) (ha : (1/2 : ℝ) ≤ |fourier (lift f) {i}|) :
    fourierWeight (lift f) 1 ≤ fourier (lift f) {i}^2 +
      8*((1-|fourier (lift f) {i}|)/2)*Real.sqrt ((1-|fourier (lift f) {i}|)/2) -
      8*((1-|fourier (lift f) {i}|)/2)^2 := by
  have h := balanced_coordinate_bound_of_biased_bound f hf i (C :=
      8*((1-|fourier (lift f) {i}|)/2)*Real.sqrt ((1-|fourier (lift f) {i}|)/2) -
      8*((1-|fourier (lift f) {i}|)/2)^2) (by
    intro m g hg
    have hcap := firstLevel_biased_sqrt_cap g (by rw [hg]; exact ha)
    simpa only [hg] using hcap)
  linarith

def firstLevelLP (a : ℝ) : ℝ :=
  if a ≤ 1/2 then a^2+1-a else
    a^2 + 8*((1-a)/2)*Real.sqrt ((1-a)/2) - 8*((1-a)/2)^2

/-- Yu's balanced first-level cap, proved here at any specified coordinate.
The high branch uses positivity of a negative-parameter BSC kernel. -/
theorem balanced_firstLevel_le_LP {n : ℕ} (f : BooleanFunction n) (hf : Balanced f)
    (i : Fin n) : fourierWeight (lift f) 1 ≤ firstLevelLP |fourier (lift f) {i}| := by
  unfold firstLevelLP
  by_cases ha : |fourier (lift f) {i}| ≤ (1/2 : ℝ)
  · rw [ite_eq_left ha, sq_abs]
    exact firstLevel_coordinate_cap f i
  · rw [ite_eq_right ha, sq_abs]
    exact balanced_firstLevel_high_cap f hf i (le_of_lt (lt_of_not_ge ha))

theorem oddLift_LP_mean_bound {n : ℕ} (f : BooleanFunction n) :
    fourierWeight (lift f) 1 + mean f^2 ≤ firstLevelLP |mean f| := by
  have h := balanced_firstLevel_le_LP (oddLift f) (oddLift_balanced f) 0
  simpa only [fourierWeight_oddLift_one, fourier_oddLift_zero] using h

theorem oddLift_LP_singleton_bound {n : ℕ} (f : BooleanFunction n) (i : Fin n) :
    fourierWeight (lift f) 1 + mean f^2 ≤ firstLevelLP |fourier (lift f) {i}| := by
  have h := balanced_firstLevel_le_LP (oddLift f) (oddLift_balanced f) i.succ
  simpa only [fourierWeight_oddLift_one, fourier_oddLift_succ] using h

theorem oddLift_LP_max_bound {n : ℕ} (hn : 0 < n) (f : BooleanFunction n) :
    fourierWeight (lift f) 1 + mean f^2 ≤
      min (firstLevelLP (maxSingletonCoeff hn f)) (firstLevelLP |mean f|) := by
  apply le_min
  · obtain ⟨i, hi⟩ := exists_max_singleton hn f
    rw [hi]
    exact oddLift_LP_singleton_bound f i
  · exact oddLift_LP_mean_bound f

theorem balanced_firstLevel_lt_cap {n : ℕ} (f : BooleanFunction n) (hf : Balanced f)
    (hcoeff : ∀ i, |fourier (lift f) {i}| ≤ (69/100 : ℝ)) :
    fourierWeight (lift f) 1 < 193027/250000 := by
  classical
  by_cases hsmall : ∀ i, |fourier (lift f) {i}| ≤ (87831/250000 : ℝ)
  · exact firstLevel_lt_cap_of_small_singletons f hsmall
  · obtain ⟨i, hi⟩ := not_forall.mp hsmall
    have hlo : (87831/250000 : ℝ) ≤ |fourier (lift f) {i}| := (lt_of_not_ge hi).le
    by_cases hhi : |fourier (lift f) {i}| ≤ (1/2 : ℝ)
    · have h := firstLevel_mean_lt_cap_of_medium_singleton f i ⟨hlo,hhi⟩
      simpa only [show mean f=0 from hf, zero_pow (by decide : 2 ≠ 0), add_zero] using h
    · have ha : (1/2 : ℝ) ≤ |fourier (lift f) {i}| := (lt_of_not_ge hhi).le
      have h := balanced_firstLevel_high_cap f hf i ha
      have hs := Certificate.fourierCap_high_lt ⟨ha,hcoeff i⟩
      rw [sq_abs] at hs
      exact h.trans_lt hs

/-- The exact numerical cap needed for the low-correlation energy proof.
All branches are proved: the small-coefficient branch uses finite moments,
and the remaining branches use the proved two-piece LP bound. -/
theorem oddLift_firstLevel_lt_cap {n : ℕ} (f : BooleanFunction n)
    (hmean : |mean f| ≤ (69/100 : ℝ))
    (hcoeff : ∀ i, |fourier (lift f) {i}| ≤ (69/100 : ℝ)) :
    fourierWeight (lift f) 1 + mean f^2 < 193027/250000 := by
  rw [← fourierWeight_oddLift_one]
  apply balanced_firstLevel_lt_cap (oddLift f) (oddLift_balanced f)
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [fourier_oddLift_zero] using hmean
  · simpa only [fourier_oddLift_succ] using hcoeff j

end
end CK
