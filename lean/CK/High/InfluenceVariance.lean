module

public import CK.Fourier.Laplacian
public import CK.Fourier.Projection
public import CK.Functional.Hypercontractivity

/-! Exact coordinate shares of variance and the first quantitative
influence bound. The shares permit taking coordinatewise minima when
the logarithmic hypercontractive estimate is added. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

def coordinateL1 {n : ℕ} (g : Cube n → ℝ) (i : Fin n) : ℝ :=
  avg (fun x => |coordinatePartial i g x|)

def coordinateVarianceShare {n : ℕ} (g : Cube n → ℝ) (i : Fin n) : ℝ :=
  ∑ S : Finset (Fin n), if i ∈ S then fourier g S^2/(S.card : ℝ) else 0

def influencePolynomial (a : ℝ) : ℝ := (a+a^2)/2

theorem coordinateL1_nonneg {n : ℕ} (g : Cube n → ℝ) (i : Fin n) :
    0 ≤ coordinateL1 g i := by
  unfold coordinateL1
  exact avg_nonneg _ (fun x => abs_nonneg _)

theorem coordinatePartial_abs_le_one {n : ℕ} (g : Cube n → ℝ)
    (hg : ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1) (i : Fin n) (x : Cube n) :
    |coordinatePartial i g x| ≤ 1 := by
  rw [abs_le]
  unfold coordinatePartial
  constructor <;> linarith [(hg x).1,(hg x).2,(hg (flipCoordinate i x)).1,(hg (flipCoordinate i x)).2]

theorem coordinateL1_le_one {n : ℕ} (g : Cube n → ℝ)
    (hg : ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1) (i : Fin n) : coordinateL1 g i ≤ 1 := by
  have h := avg_mono (coordinatePartial_abs_le_one g hg i)
  simpa only [avg_const,coordinateL1] using h

theorem coordinatePartial_square_le_l1 {n : ℕ} (g : Cube n → ℝ)
    (hg : ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1) (i : Fin n) :
    avg (fun x => coordinatePartial i g x^2) ≤ coordinateL1 g i := by
  apply avg_mono
  intro x
  have h := coordinatePartial_abs_le_one g hg i x
  have hnon := abs_nonneg (coordinatePartial i g x)
  have hp := mul_nonneg hnon (sub_nonneg.mpr h)
  nlinarith only [hp,sq_abs (coordinatePartial i g x)]

theorem singleton_abs_le_coordinateL1 {n : ℕ} (g : Cube n → ℝ) (i : Fin n) :
    |fourier g {i}| ≤ coordinateL1 g i := by
  have he : fourier (coordinatePartial i g) {i} = fourier g {i} := by
    rw [fourier_coordinatePartial]
    simp
  rw [← he,fourier_singleton]
  have h := abs_avg_le_avg_abs (fun x => coordinatePartial i g x*sign (x i))
  have hp (x : Cube n) : |coordinatePartial i g x*sign (x i)| = |coordinatePartial i g x| := by
    rw [abs_mul]
    cases x i <;> simp
  simpa only [hp,coordinateL1] using h

theorem coordinateVarianceShare_nonneg {n : ℕ} (g : Cube n → ℝ) (i : Fin n) :
    0 ≤ coordinateVarianceShare g i :=
  Finset.sum_nonneg fun S _ => by split_ifs <;> positivity

theorem variance_eq_sum_coordinateVarianceShare {n : ℕ} (g : Cube n → ℝ) :
    variance g = ∑ i : Fin n, coordinateVarianceShare g i := by
  classical
  unfold coordinateVarianceShare
  rw [Finset.sum_comm]
  have hinner (S : Finset (Fin n)) :
      (∑ i : Fin n, if i ∈ S then fourier g S^2/(S.card : ℝ) else 0) =
      if S=∅ then 0 else fourier g S^2 := by
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul]
    by_cases hS : S=∅
    · simp [hS]
    · have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
      rw [if_neg hS]
      field_simp
  simp_rw [hinner]
  rw [variance_eq_sum_nonempty]
  have h := Finset.sum_erase_add (Finset.univ : Finset (Finset (Fin n)))
    (fun S => if S=∅ then (0 : ℝ) else fourier g S^2) (Finset.mem_univ ∅)
  simp only [ite_true,add_zero] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro S hS
  rw [if_neg (Finset.mem_erase.mp hS).1]

theorem coordinateVarianceShare_le_half_energy {n : ℕ} (g : Cube n → ℝ) (i : Fin n) :
    coordinateVarianceShare g i ≤
      (avg (fun x => coordinatePartial i g x^2)+fourier g {i}^2)/2 := by
  classical
  have hsingle : fourier g {i}^2 = ∑ S : Finset (Fin n), if S={i} then fourier g S^2 else 0 := by
    simp
  rw [coordinateVarianceShare,parseval,hsingle]
  simp_rw [fourier_coordinatePartial,ite_pow,zero_pow (by decide : 2 ≠ 0)]
  rw [← Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_le_sum
  intro S _
  by_cases hi : i ∈ S
  · by_cases hcard : S.card=1
    · obtain ⟨j,hj⟩ := Finset.card_eq_one.mp hcard
      have hij : i=j := by simpa only [hj,Finset.mem_singleton] using hi
      subst j
      simp [hj]
    · have hc : 2 ≤ S.card := by
        have hpos := Finset.card_pos.mpr (show S.Nonempty from ⟨i,hi⟩)
        omega
      have hcR : (2 : ℝ) ≤ S.card := by exact_mod_cast hc
      have hne : S ≠ {i} := by intro h; simpa [h] using hcard
      simp only [if_pos hi,if_neg hne,add_zero]
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hcR
  · have hne : S ≠ {i} := by intro h; simp [h] at hi
    simp [hi,hne]

theorem coordinateVarianceShare_le_polynomial {n : ℕ} (g : Cube n → ℝ)
    (hg : ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1) (i : Fin n) :
    coordinateVarianceShare g i ≤ influencePolynomial (coordinateL1 g i) := by
  have he := coordinateVarianceShare_le_half_energy g i
  have hq := coordinatePartial_square_le_l1 g hg i
  have hc := singleton_abs_le_coordinateL1 g i
  have hsq := pow_le_pow_left₀ (abs_nonneg (fourier g {i})) hc 2
  rw [sq_abs] at hsq
  unfold influencePolynomial
  linarith

theorem variance_le_sum_influencePolynomial {n : ℕ} (g : Cube n → ℝ)
    (hg : ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1) :
    variance g ≤ ∑ i : Fin n, influencePolynomial (coordinateL1 g i) := by
  rw [variance_eq_sum_coordinateVarianceShare]
  exact Finset.sum_le_sum (fun i _ => coordinateVarianceShare_le_polynomial g hg i)

theorem coordinatePartial_coordinateProjection {n : ℕ} (K : Finset (Fin n))
    (g : Cube n → ℝ) (i : Fin n) :
    coordinatePartial i (coordinateProjection K g) = coordinateProjection K (coordinatePartial i g) := by
  apply fourier_ext
  intro S
  simp only [fourier_coordinatePartial,fourier_coordinateProjection]
  split_ifs <;> rfl

theorem coordinatePartial_projection_of_not_mem {n : ℕ} (K : Finset (Fin n))
    (g : Cube n → ℝ) (i : Fin n) (hi : i ∉ K) :
    coordinatePartial i (coordinateProjection K g) = fun _ => 0 := by
  apply fourier_ext
  intro S
  rw [fourier_coordinatePartial,fourier_coordinateProjection,fourier_const]
  by_cases hS : i ∈ S
  · have hsub : ¬ S ⊆ K := by intro h; exact hi (h hS)
    simp [hS,hsub]
  · simp [hS]

theorem coordinateL1_projection_le {n : ℕ} (K : Finset (Fin n))
    (g : Cube n → ℝ) (i : Fin n) :
    coordinateL1 (coordinateProjection K g) i ≤ coordinateL1 g i := by
  rw [coordinateL1,coordinatePartial_coordinateProjection]
  have hp (x : Cube n) : |coordinateProjection K (coordinatePartial i g) x| ≤
      coordinateProjection K (fun y => |coordinatePartial i g y|) x :=
    abs_avg_le_avg_abs _
  have h := avg_mono hp
  rw [avg_coordinateProjection] at h
  exact h

theorem influencePolynomial_monotoneOn : MonotoneOn influencePolynomial (Set.Ici (0 : ℝ)) := by
  intro a ha b hb hab
  have hs := pow_le_pow_left₀ ha hab 2
  unfold influencePolynomial
  linarith

/-- Complete polynomial influence bound for an actual coordinate
conditional expectation, including the empty retained set. -/
theorem variance_projection_le_influencePolynomial {n : ℕ} (g : Cube n → ℝ)
    (hg : ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1) (K : Finset (Fin n)) :
    variance (coordinateProjection K g) ≤ ∑ i ∈ K, influencePolynomial (coordinateL1 g i) := by
  classical
  have h := variance_le_sum_influencePolynomial (coordinateProjection K g)
    (coordinateProjection_mem_Icc K hg)
  calc
    _ ≤ ∑ i : Fin n, influencePolynomial (coordinateL1 (coordinateProjection K g) i) := h
    _ ≤ ∑ i : Fin n, if i∈K then influencePolynomial (coordinateL1 g i) else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i∈K
      · rw [if_pos hi]
        exact influencePolynomial_monotoneOn (coordinateL1_nonneg _ i) (coordinateL1_nonneg _ i)
          (coordinateL1_projection_le K g i)
      · rw [if_neg hi,coordinateL1,coordinatePartial_projection_of_not_mem K g i hi]
        simp [influencePolynomial]
    _ = _ := by simp

end
end CK
