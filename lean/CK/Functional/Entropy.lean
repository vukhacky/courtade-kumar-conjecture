module

public import CK.Basic.Entropy
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Data.Fin.Tuple.Basic

/-! The entropy functional on a finite uniform cube and its two-point
conditional version. All logarithms are natural. Nonnegative boundary
values are included, using continuity of `x * log x` at zero. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

def entropyFunctional {n : ℕ} (v : Cube n → ℝ) : ℝ :=
  avg (fun x => v x * Real.log (v x)) - avg v * Real.log (avg v)

def twoPointEntropy (a b : ℝ) : ℝ :=
  (a * Real.log a + b * Real.log b) / 2 -
    ((a + b) / 2) * Real.log ((a + b) / 2)

theorem mul_log_mul_identity (a b : ℝ) :
    (a * b) * Real.log (a * b) =
      a * (b * Real.log b) + b * (a * Real.log a) := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [Real.log_mul ha hb]
  ring

@[simp] theorem twoPointEntropy_zero : twoPointEntropy 0 0 = 0 := by
  simp [twoPointEntropy]

theorem twoPointEntropy_smul (c a b : ℝ) :
    twoPointEntropy (c * a) (c * b) = c * twoPointEntropy a b := by
  unfold twoPointEntropy
  rw [show (c * a + c * b) / 2 = c * ((a + b) / 2) by ring]
  rw [mul_log_mul_identity, mul_log_mul_identity, mul_log_mul_identity]
  ring

theorem twoPointEntropy_eq_phi (t : ℝ) :
    twoPointEntropy (1 + t) (1 - t) = phi t := by
  have hminus := mul_log_mul_identity (2 : ℝ) ((1 - t) / 2)
  have hplus := mul_log_mul_identity (2 : ℝ) ((1 + t) / 2)
  have h1 : (2 : ℝ) * ((1 - t) / 2) = 1 - t := by ring
  have h2 : (2 : ℝ) * ((1 + t) / 2) = 1 + t := by ring
  rw [h1] at hminus
  rw [h2] at hplus
  unfold twoPointEntropy phi
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog_eq_neg]
  rw [show ((1 + t) + (1 - t)) / 2 = (1 : ℝ) by ring]
  rw [show 1 - (1 - t) / 2 = (1 + t) / 2 by ring]
  simp only [Real.log_one, mul_zero, sub_zero]
  linarith

theorem twoPointEntropy_mean_phi {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    twoPointEntropy a b = ((a + b) / 2) * phi ((a - b) / (a + b)) := by
  by_cases hab : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  have h1 : ((a + b) / 2) * (1 + (a - b) / (a + b)) = a := by
    field_simp
    ring
  have h2 : ((a + b) / 2) * (1 - (a - b) / (a + b)) = b := by
    field_simp
    ring
  rw [← twoPointEntropy_eq_phi, ← twoPointEntropy_smul, h1, h2]

theorem pair_ratio_mem_Icc {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a - b) / (a + b) ∈ Set.Icc (-1 : ℝ) 1 := by
  by_cases hab : a + b = 0
  · simp [hab]
  have hp : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hab)
  constructor
  · apply (le_div_iff₀ hp).2
    linarith
  · apply (div_le_iff₀ hp).2
    linarith

theorem phi_convexOn_closed : ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) phi := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : (1 - x) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hy' : (1 - y) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hy.1, hy.2]
  have h := Real.strictConcave_binEntropy.concaveOn.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have heq : (1 - (a * x + b * y)) / 2 = a * ((1 - x) / 2) + b * ((1 - y) / 2) := by
    nlinarith
  unfold phi
  rw [heq]
  nlinarith [congrArg (fun z : ℝ => z * Real.log 2) hab]

theorem twoPointEntropy_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ twoPointEntropy a b := by
  rw [twoPointEntropy_mean_phi ha hb]
  exact mul_nonneg (by positivity) (phi_nonneg _)

theorem pair_sum_mul_ratio {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) * ((a - b) / (a + b)) = a - b := by
  by_cases hab : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [ha0, hb0]
  · field_simp

/-- Convexity and positive homogeneity of the two-point entropy,
in the form needed for arbitrary nonnegative finite mixtures. -/
theorem twoPointEntropy_sum_le {ι : Type*} [Fintype ι]
    (w a b : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    twoPointEntropy (∑ i, w i * a i) (∑ i, w i * b i) ≤
      ∑ i, w i * twoPointEntropy (a i) (b i) := by
  let A := ∑ i, w i * a i
  let B := ∑ i, w i * b i
  let S := A + B
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (ha i)
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (hb i)
  have hsum : ∑ i, w i * (a i + b i) = S := by
    simp [S, A, B, mul_add, Finset.sum_add_distrib]
  have hdiff : ∑ i, w i * (a i - b i) = A - B := by
    simp [A, B, mul_sub, Finset.sum_sub_distrib]
  change twoPointEntropy A B ≤ _
  by_cases hS : S = 0
  · have hA0 : A = 0 := by dsimp [S] at hS; linarith
    have hB0 : B = 0 := by dsimp [S] at hS; linarith
    rw [hA0, hB0, twoPointEntropy_zero]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (hw i) (twoPointEntropy_nonneg (ha i) (hb i))
  have hSpos : 0 < S := lt_of_le_of_ne (add_nonneg hA hB) (Ne.symm hS)
  let q := fun i => (w i * (a i + b i)) / S
  have hq : ∀ i, 0 ≤ q i := fun i =>
    div_nonneg (mul_nonneg (hw i) (add_nonneg (ha i) (hb i))) hSpos.le
  have hqsum : ∑ i, q i = 1 := by
    simp only [q, ← Finset.sum_div, hsum, div_self hS]
  have ht : ∑ i, q i * ((a i - b i) / (a i + b i)) = (A - B) / S := by
    calc
      _ = (∑ i, w i * ((a i + b i) * ((a i - b i) / (a i + b i)))) / S := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [q]
        ring
      _ = (∑ i, w i * (a i - b i)) / S := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [pair_sum_mul_ratio (ha i) (hb i)]
      _ = (A - B) / S := by rw [hdiff]
  have hj := phi_convexOn_closed.map_sum_le (t := Finset.univ)
    (w := q) (p := fun i => (a i - b i) / (a i + b i))
    (fun i _ => hq i) hqsum (fun i _ => pair_ratio_mem_Icc (ha i) (hb i))
  simp only [smul_eq_mul, ht] at hj
  rw [twoPointEntropy_mean_phi hA hB]
  change (S / 2) * phi ((A - B) / S) ≤ _
  calc
    _ ≤ (S / 2) * ∑ i, q i * phi ((a i - b i) / (a i + b i)) :=
      mul_le_mul_of_nonneg_left hj (by positivity)
    _ = ∑ i, w i * twoPointEntropy (a i) (b i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [twoPointEntropy_mean_phi (ha i) (hb i)]
      dsimp [q]
      field_simp

theorem twoPointEntropy_midpoint_le {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    twoPointEntropy ((a + c) / 2) ((b + d) / 2) ≤
      (twoPointEntropy a b + twoPointEntropy c d) / 2 := by
  have h := twoPointEntropy_sum_le (fun _ : Bool => (1 / 2 : ℝ))
    (fun i => if i then c else a) (fun i => if i then d else b)
    (by intro i; norm_num) (by intro i; cases i <;> simp [ha, hc])
    (by intro i; cases i <;> simp [hb, hd])
  simp at h
  convert h using 1 <;> congr 1 <;> ring

@[simp] theorem entropyFunctional_const (n : ℕ) (c : ℝ) :
    entropyFunctional (fun _ : Cube n => c) = 0 := by
  simp [entropyFunctional]

theorem entropyFunctional_nonneg {n : ℕ} {v : Cube n → ℝ} (hv : ∀ x, 0 ≤ v x) :
    0 ≤ entropyFunctional v := by
  have h := Real.convexOn_mul_log.map_sum_le
    (t := Finset.univ) (w := fun _ : Cube n => (Fintype.card (Cube n) : ℝ)⁻¹)
    (p := v) (by intros; positivity)
    (by simp) (by intro i _; exact hv i)
  simp only [smul_eq_mul, ← Finset.mul_sum] at h
  exact sub_nonneg.mpr h

end
end CK
