module

public import CK.High.Height
public import CK.High.SpectralLoss

/-! The discarded singleton budget for the high-correlation signed
multiplier. Every coordinate shares the actual entropy-production budget. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
open Set
namespace CK
noncomputable section

def spectralRetainedSet {n : ℕ} (ρ z : ℝ) (g : Cube n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => profileCoefficient ρ z ≤ |fourier g {i}|)

def retainedHeightBudget {n : ℕ} (K : Finset (Fin n)) (ρ : ℝ) (g : Cube n → ℝ) : ℝ :=
  ∑ i ∈ K, |fourier g {i}| *profileHeight ρ |fourier g {i}|

def spectralTau (γ t ρ z : ℝ) : ℝ :=
  spectralDeltaOutside γ t ρ*profileCoefficient ρ z/z

theorem spectralRetainedSet_mem {n : ℕ} {ρ z : ℝ} {g : Cube n → ℝ} {i : Fin n} :
    i ∈ spectralRetainedSet ρ z g ↔ profileCoefficient ρ z ≤ |fourier g {i}| := by
  simp [spectralRetainedSet]

theorem spectralRetainedSet_pos {n : ℕ} {ρ z : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hz : 0 < z) (g : Cube n → ℝ) {i : Fin n}
    (hi : i ∈ spectralRetainedSet ρ z g) : 0 < |fourier g {i}| :=
  (profileCoefficient_pos hρ hz).trans_le (spectralRetainedSet_mem.mp hi)

theorem retainedHeightBudget_nonneg {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (K : Finset (Fin n)) (g : Cube n → ℝ) :
    0 ≤ retainedHeightBudget K ρ g := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (abs_nonneg _) (profileHeight_nonneg hρ (abs_nonneg _))

theorem retainedHeightBudget_le_total {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (K : Finset (Fin n)) (g : Cube n → ℝ) :
    retainedHeightBudget K ρ g ≤
      ∑ i : Fin n, |fourier g {i}| *profileHeight ρ |fourier g {i}| := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ K)
  intro i _ _
  exact mul_nonneg (abs_nonneg _) (profileHeight_nonneg hρ (abs_nonneg _))

theorem spectralTau_nonneg {γ t ρ z : ℝ}
    (hγ : max 0 (Real.exp (2*t-3)/2-t) < γ)
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hz : 0 < z) : 0 ≤ spectralTau γ t ρ z :=
  div_nonneg (mul_nonneg (spectralDeltaOutside_nonneg hγ) (profileCoefficient_pos hρ hz).le) hz.le

theorem singleton_square_le_height {ρ z a : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hz : 0 < z)
    (ha : a ∈ Icc (0 : ℝ) (profileCoefficient ρ z)) :
    a^2 ≤ (profileCoefficient ρ z/z)*a*profileHeight ρ a := by
  rcases ha.1.eq_or_lt with rfl | ha0
  · simp
  have hb := profileCoefficient_pos hρ hz
  have hr := profileHeight_ratio_antitone hρ ha0 ha.2
  rw [profileHeight_profileCoefficient hρ hz] at hr
  have hcross := (div_le_div_iff₀ hb ha0).mp hr
  have hm := mul_le_mul_of_nonneg_right hcross ha0.le
  apply (mul_le_mul_iff_left₀ hz).mp
  have he : ((profileCoefficient ρ z/z)*a*profileHeight ρ a)*z =
      profileCoefficient ρ z*a*profileHeight ρ a := by field_simp
  rw [he]
  nlinarith only [hm]

theorem outsideSingletonEnergy_le_height {n : ℕ} {ρ z : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hz : 0 < z) (g : Cube n → ℝ) :
    outsideSingletonEnergy (spectralRetainedSet ρ z g) g ≤
      (profileCoefficient ρ z/z)*
        ((∑ i : Fin n, |fourier g {i}| *profileHeight ρ |fourier g {i}|)-
          retainedHeightBudget (spectralRetainedSet ρ z g) ρ g) := by
  classical
  rw [outsideSingletonEnergy,retainedHeightBudget,← Finset.sum_sdiff_eq_sub (Finset.subset_univ (spectralRetainedSet ρ z g)),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hnot := (Finset.mem_sdiff.mp hi).2
  have hle : |fourier g {i}| ≤ profileCoefficient ρ z := by
    exact (lt_of_not_ge (fun h => hnot (spectralRetainedSet_mem.mpr h))).le
  have h := singleton_square_le_height hρ hz ⟨abs_nonneg _,hle⟩
  simpa only [sq_abs,mul_assoc] using h

/-- Outside singleton losses are charged against the same production
budget after subtracting the retained-coordinate allocation. -/
theorem outside_singleton_cost {n : ℕ} {γ t ρ z : ℝ}
    (hγ : max 0 (Real.exp (2*t-3)/2-t) < γ)
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hz : 0 < z)
    (f : BooleanFunction n) (hf : ∃ u v, f u ≠ f v)
    (hgap : 0 < informationGap ρ f) :
    spectralDeltaOutside γ t ρ*outsideSingletonEnergy (spectralRetainedSet ρ z (lift f)) (lift f) ≤
      spectralTau γ t ρ z*(entropyProduction (noise ρ (lift f))/ρ-
        retainedHeightBudget (spectralRetainedSet ρ z (lift f)) ρ (lift f)) := by
  have h1 := mul_le_mul_of_nonneg_left (outsideSingletonEnergy_le_height hρ hz (lift f))
    (spectralDeltaOutside_nonneg (ρ := ρ) hγ)
  have h2 := mul_le_mul_of_nonneg_left (sub_le_sub_right (profileHeight_common_budget hρ f hf hgap)
    (retainedHeightBudget (spectralRetainedSet ρ z (lift f)) ρ (lift f)))
    (spectralTau_nonneg hγ hρ hz)
  unfold spectralTau at h2 ⊢
  have he : spectralDeltaOutside γ t ρ*(profileCoefficient ρ z/z)=
      spectralDeltaOutside γ t ρ*profileCoefficient ρ z/z := by ring
  rw [← mul_assoc,he] at h1
  exact h1.trans h2

end
end CK
