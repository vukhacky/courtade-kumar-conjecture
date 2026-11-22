module

public import CK.High.InfluenceVariance
public import CK.Reduction.Compression
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! A coordinate variance share is the integral of the noise energy of
the derivative with its sign coordinate removed.  The derivative remains
an explicit finite-cube function throughout. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
open MeasureTheory Set
namespace CK
noncomputable section

def demodulatedPartial {n : ℕ} (i : Fin n) (g : Cube n → ℝ) (x : Cube n) : ℝ :=
  sign (x i)*coordinatePartial i g x

def coordinateNoiseEnergy {n : ℕ} (g : Cube n → ℝ) (i : Fin n) (s : ℝ) : ℝ :=
  ∑ S : Finset (Fin n), if i∈S then s^(S.card-1)*fourier g S^2 else 0

theorem abs_demodulatedPartial {n : ℕ} (i : Fin n) (g : Cube n → ℝ) (x : Cube n) :
    |demodulatedPartial i g x| = |coordinatePartial i g x| := by
  unfold demodulatedPartial
  rw [abs_mul]
  cases x i <;> simp

theorem coordinatePartial_insertNth {n : ℕ} (i : Fin (n+1)) (g : Cube (n+1) → ℝ)
    (b : Bool) (x : Cube n) :
    coordinatePartial i g (i.insertNth b x) = sign b*sectionDifference i g x := by
  simp only [coordinatePartial,flipCoordinate,Fin.insertNth_apply_same,Fin.update_insertNth]
  cases b <;> simp [sectionDifference] <;> ring

theorem demodulatedPartial_insertNth {n : ℕ} (i : Fin (n+1)) (g : Cube (n+1) → ℝ)
    (b : Bool) (x : Cube n) :
    demodulatedPartial i g (i.insertNth b x) = sectionDifference i g x := by
  rw [demodulatedPartial,Fin.insertNth_apply_same,coordinatePartial_insertNth]
  rw [← mul_assoc,sign_mul_self,one_mul]

theorem noise_demodulatedPartial_insertNth {n : ℕ} (i : Fin (n+1))
    (g : Cube (n+1) → ℝ) (ρ : ℝ) (b : Bool) (x : Cube n) :
    noise ρ (demodulatedPartial i g) (i.insertNth b x) = noise ρ (sectionDifference i g) x := by
  rw [noise_insertNth]
  simp only [demodulatedPartial_insertNth]
  cases b <;> simp [bitKernel] <;> ring

theorem noise_coordinatePartial_insertNth {n : ℕ} (i : Fin (n+1))
    (g : Cube (n+1) → ℝ) (ρ : ℝ) (b : Bool) (x : Cube n) :
    noise ρ (coordinatePartial i g) (i.insertNth b x) =
      ρ*sign b*noise ρ (sectionDifference i g) x := by
  rw [noise_insertNth]
  simp only [coordinatePartial_insertNth,sign_false,sign_true,one_mul]
  rw [noise_smul]
  cases b <;> simp [bitKernel,sign] <;> ring

theorem noise_coordinatePartial_energy {n : ℕ} (i : Fin n) (g : Cube n → ℝ) (ρ : ℝ) :
    avg (fun x => noise ρ (coordinatePartial i g) x^2) =
      ρ^2*avg (fun x => noise ρ (demodulatedPartial i g) x^2) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [avg_cube_insertNth i,avg_cube_insertNth i,← avg_smul]
    congr 1
    funext x
    simp only [noise_coordinatePartial_insertNth,noise_demodulatedPartial_insertNth,
      sign_false,sign_true]
    ring

theorem coordinateNoiseEnergy_zero {n : ℕ} (g : Cube n → ℝ) (i : Fin n) :
    coordinateNoiseEnergy g i 0 = fourier g {i}^2 := by
  classical
  unfold coordinateNoiseEnergy
  have hterm (S : Finset (Fin n)) :
      (if i∈S then (0 : ℝ)^(S.card-1)*fourier g S^2 else 0) =
        if S={i} then fourier g S^2 else 0 := by
    by_cases hi : i∈S
    · by_cases hS : S={i}
      · simp [hS]
      · have hc1 : S.card ≠ 1 := by
          intro he
          obtain ⟨j,hj⟩ := Finset.card_eq_one.mp he
          have hij : i=j := by simpa only [hj,Finset.mem_singleton] using hi
          subst j
          exact hS hj
        have hc : S.card-1 ≠ 0 := by
          have hpos := Finset.card_pos.mpr (show S.Nonempty from ⟨i,hi⟩)
          omega
        simp [hi,hS,hc]
    · have hS : S ≠ {i} := by intro he; simp [he] at hi
      simp [hi,hS]
  simp_rw [hterm]
  simp

theorem coordinateNoiseEnergy_mul {n : ℕ} (g : Cube n → ℝ) (i : Fin n)
    {s : ℝ} (hs : 0 ≤ s) :
    s*coordinateNoiseEnergy g i s = avg (fun x => noise (Real.sqrt s) (coordinatePartial i g) x^2) := by
  classical
  rw [coordinateNoiseEnergy,parseval,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [fourier_noise,fourier_coordinatePartial]
  by_cases hi : i∈S
  · simp only [ite_eq_left hi,mul_pow]
    have hc : 1 ≤ S.card := Finset.card_pos.mpr ⟨i,hi⟩
    rw [← pow_mul,Nat.mul_comm S.card 2,pow_mul,Real.sq_sqrt hs]
    rw [← mul_assoc,← pow_succ',Nat.sub_add_cancel hc]
  · simp [hi]

theorem coordinateNoiseEnergy_eq_demodulated {n : ℕ} (g : Cube n → ℝ) (i : Fin n)
    {s : ℝ} (hs : 0 < s) :
    coordinateNoiseEnergy g i s = avg (fun x => noise (Real.sqrt s) (demodulatedPartial i g) x^2) := by
  have h := coordinateNoiseEnergy_mul g i hs.le
  rw [noise_coordinatePartial_energy,Real.sq_sqrt hs.le] at h
  exact mul_left_cancel₀ (ne_of_gt hs) h

theorem coordinateNoiseEnergy_continuous {n : ℕ} (g : Cube n → ℝ) (i : Fin n) :
    Continuous (coordinateNoiseEnergy g i) := by
  unfold coordinateNoiseEnergy
  apply continuous_finsetSum
  intro S _
  split_ifs <;> fun_prop

/-- Exact Fourier integral representation, with the degree-zero mode
excluded by the coordinate membership test. -/
theorem coordinateVarianceShare_integral {n : ℕ} (g : Cube n → ℝ) (i : Fin n) :
    coordinateVarianceShare g i = ∫ s in (0 : ℝ)..1, coordinateNoiseEnergy g i s := by
  classical
  unfold coordinateVarianceShare coordinateNoiseEnergy
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro S _
    by_cases hi : i∈S
    · simp only [ite_eq_left hi]
      rw [intervalIntegral.integral_mul_const,integral_pow]
      have hc : 1 ≤ S.card := Finset.card_pos.mpr ⟨i,hi⟩
      rw [Nat.sub_add_cancel hc]
      simp only [one_pow,zero_pow (by omega : S.card ≠ 0),sub_zero]
      have hcast : ((S.card-1 : ℕ) : ℝ)+1 = (S.card : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel hc
      rw [hcast]
      ring
    · simp [hi]
  · intro S _
    have hc : Continuous (fun s : ℝ => if i∈S then s^(S.card-1)*fourier g S^2 else 0) := by
      split_ifs <;> fun_prop
    exact hc.intervalIntegrable _ _

/-- Hypercontractivity, specialized to one coordinate share. -/
theorem coordinateNoiseEnergy_le_rpow {n : ℕ} (g : Cube n → ℝ)
    (hg : ∀ x, g x ∈ Icc (-1 : ℝ) 1) (i : Fin n) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    coordinateNoiseEnergy g i s ≤ (coordinateL1 g i)^(2/(1+s)) := by
  by_cases hs0 : s=0
  · rw [hs0,coordinateNoiseEnergy_zero]
    norm_num
    have h := pow_le_pow_left₀ (abs_nonneg (fourier g {i})) (singleton_abs_le_coordinateL1 g i) 2
    simpa only [sq_abs] using h
  · have hsp : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have hsqrt : Real.sqrt s ∈ Icc (0 : ℝ) 1 :=
      ⟨Real.sqrt_nonneg _, (Real.sqrt_le_one).2 hs.2⟩
    rw [coordinateNoiseEnergy_eq_demodulated g i hsp]
    have hh := cube_hypercontractivity_sq hsqrt (demodulatedPartial i g)
    rw [Real.sq_sqrt hs.1] at hh
    have hbase : avg (fun x => |demodulatedPartial i g x|^(1+s)) ≤ coordinateL1 g i := by
      unfold coordinateL1
      apply avg_mono
      intro x
      rw [abs_demodulatedPartial]
      exact Real.rpow_le_self_of_le_one (abs_nonneg _) (coordinatePartial_abs_le_one g hg i x)
        (by linarith [hs.1])
    exact hh.trans (Real.rpow_le_rpow
      (avg_nonneg _ (fun x => Real.rpow_nonneg (abs_nonneg _) _)) hbase (by positivity))

end
end CK
