module

public import CK.Functional.Core
public import CK.Functional.AndEntropy
public import CK.Fourier.Walsh
public import CK.Fourier.Influences
public import CK.Basic.NoiseExtras

/-! Two-coordinate retained-core entropy, with the actual mean.
This module first proves every two-dimensional calculation explicitly. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

def andFunction : BooleanFunction 2 := fun x => x 0 && x 1
def orFunction : BooleanFunction 2 := fun x => x 0 || x 1

def andPosteriorEntropy (ρ : ℝ) : ℝ := posteriorEntropy ρ andFunction

theorem sum_cube_two (g : Cube 2 → ℝ) :
    ∑ x, g x = g ![false, false] + g ![false, true] +
      g ![true, false] + g ![true, true] := by
  have hs : (∑ x : Cube 2, g x) = ∑ p : Bool × Bool, g ![p.1, p.2] := by
    apply Fintype.sum_equiv (finTwoArrowEquiv Bool) g (fun p => g ![p.1, p.2])
    intro x
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hs]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  ring

theorem avg_cube_two (g : Cube 2 → ℝ) :
    avg g = (g ![false, false] + g ![false, true] +
      g ![true, false] + g ![true, true]) / 4 := by
  unfold avg
  rw [sum_cube_two, card_cube]
  norm_num
  ring

theorem noise_cube_two (ρ : ℝ) (g : Cube 2 → ℝ) (x : Cube 2) :
    noise ρ g x =
      bitKernel ρ (x 0) false * bitKernel ρ (x 1) false * g ![false, false] +
      bitKernel ρ (x 0) false * bitKernel ρ (x 1) true * g ![false, true] +
      bitKernel ρ (x 0) true * bitKernel ρ (x 1) false * g ![true, false] +
      bitKernel ρ (x 0) true * bitKernel ρ (x 1) true * g ![true, true] := by
  rw [noise, sum_cube_two]
  simp only [bscKernel, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]

theorem twoCube_function_values {α : Type*} (f : Cube 2 → α) (x : Cube 2) :
    f x = if x 0 then (if x 1 then f ![true, true] else f ![true, false])
      else (if x 1 then f ![false, true] else f ![false, false]) := by
  have hx : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
  conv_lhs => rw [hx]
  cases x 0 <;> cases x 1 <;> rfl

theorem monotone_boolean_two_cases (f : BooleanFunction 2) (hf : Monotone (lift f)) :
    f = (fun _ => false) ∨ f = (fun _ => true) ∨
      f = (fun x => x 0) ∨ f = (fun x => x 1) ∨ f = andFunction ∨ f = orFunction := by
  have h01 := hf (show ![false, false] ≤ ![false, true] by intro i; fin_cases i <;> decide)
  have h02 := hf (show ![false, false] ≤ ![true, false] by intro i; fin_cases i <;> decide)
  have h13 := hf (show ![false, true] ≤ ![true, true] by intro i; fin_cases i <;> decide)
  have h23 := hf (show ![true, false] ≤ ![true, true] by intro i; fin_cases i <;> decide)
  cases hff : f ![false, false] <;> cases hft : f ![false, true] <;>
    cases htf : f ![true, false] <;> cases htt : f ![true, true]
  all_goals norm_num [lift, hff, hft, htf, htt] at h01
  all_goals norm_num [lift, hff, hft, htf, htt] at h02
  all_goals norm_num [lift, hff, hft, htf, htt] at h13
  all_goals norm_num [lift, hff, hft, htf, htt] at h23
  all_goals
    solve
    | left; funext x; rw [twoCube_function_values f x]; simp [hff, hft, htf, htt]
    | right; left; funext x; rw [twoCube_function_values f x]; simp [hff, hft, htf, htt]
    | right; right; left; funext x; rw [twoCube_function_values f x]; simp [hff, hft, htf, htt]
    | right; right; right; left; funext x; rw [twoCube_function_values f x]; simp [hff, hft, htf, htt]
    | right; right; right; right; left; funext x; rw [twoCube_function_values f x];
        cases hx : x 0 <;> cases hy : x 1 <;> simp [hff, hft, htf, htt, andFunction, hx, hy]
    | right; right; right; right; right; funext x; rw [twoCube_function_values f x];
        cases hx : x 0 <;> cases hy : x 1 <;> simp [hff, hft, htf, htt, orFunction, hx, hy]

theorem noise_andFunction (ρ : ℝ) (x : Cube 2) :
    noise ρ (lift andFunction) x =
      2 * ((1 + ρ * sign (x 0)) / 2) * ((1 + ρ * sign (x 1)) / 2) - 1 := by
  rw [noise_cube_two]
  cases hx : x 0 <;> cases hy : x 1 <;>
    simp [andFunction, lift, bitKernel] <;> ring

theorem signEntropy_two_mul_sub_one (p : ℝ) :
    signEntropy (2 * p - 1) = Real.binEntropy p := by
  unfold signEntropy
  rw [show (1 - (2*p-1))/2 = 1-p by ring, Real.binEntropy_one_sub]

theorem andPosteriorEntropy_formula (ρ : ℝ) :
    andPosteriorEntropy ρ =
      (Real.binEntropy (((1-ρ)/2)^2) +
        2 * Real.binEntropy (((1-ρ)/2) * ((1+ρ)/2)) +
        Real.binEntropy (((1+ρ)/2)^2)) / 4 := by
  unfold andPosteriorEntropy posteriorEntropy
  simp_rw [noise_andFunction, mul_assoc, signEntropy_two_mul_sub_one]
  rw [avg_cube_two]
  norm_num
  simp only [← sub_eq_add_neg]
  rw [mul_comm ((1+ρ)/2) ((1-ρ)/2)]
  simp only [← pow_two]
  ring

theorem andPosteriorEntropy_le {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    andPosteriorEntropy ρ ≤ signEntropy ρ := by
  let p := (1-ρ)/2
  have hp : p ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> dsimp [p] <;> linarith [hρ.1,hρ.2]
  have hq : 1-p ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hp.2], by linarith [hp.1]⟩
  have hpp := binEntropy_mul_le hp hp
  have hpq := binEntropy_mul_le hp hq
  have hqq := binEntropy_mul_le hq hq
  rw [Real.binEntropy_one_sub] at hpq hqq
  rw [andPosteriorEntropy_formula]
  have hcomp : (1+ρ)/2 = 1-p := by dsimp [p]; ring
  rw [hcomp]
  change (Real.binEntropy (p^2) + 2*Real.binEntropy (p*(1-p)) +
    Real.binEntropy ((1-p)^2))/4 ≤ Real.binEntropy p
  simp only [← pow_two] at hpp hqq
  nlinarith

theorem noise_orFunction (ρ : ℝ) (x : Cube 2) :
    noise ρ (lift orFunction) x =
      - noise ρ (lift andFunction) (fun i => !(x i)) := by
  rw [noise_cube_two, noise_cube_two]
  cases hx : x 0 <;> cases hy : x 1 <;>
    simp [orFunction, andFunction, lift, bitKernel] <;> ring

theorem twoCube_not (a b : Bool) :
    (fun i : Fin 2 => !(![a,b] i)) = ![!a,!b] := by
  funext i
  fin_cases i <;> rfl

theorem posteriorEntropy_orFunction (ρ : ℝ) :
    posteriorEntropy ρ orFunction = andPosteriorEntropy ρ := by
  unfold posteriorEntropy andPosteriorEntropy
  simp_rw [noise_orFunction, signEntropy_neg]
  rw [avg_cube_two, posteriorEntropy, avg_cube_two]
  simp only [twoCube_not, Bool.not_false, Bool.not_true]
  norm_num
  ring

theorem posteriorEntropy_const (n : ℕ) (ρ : ℝ) (b : Bool) :
    posteriorEntropy ρ (fun _ : Cube n => b) = 0 := by
  unfold posteriorEntropy lift
  simp only [noise_const]
  cases b <;> simp

theorem posteriorEntropy_coordinate {n : ℕ} (ρ : ℝ) (i : Fin n) :
    posteriorEntropy ρ (fun x : Cube n => x i) = signEntropy ρ := by
  unfold posteriorEntropy lift
  simp_rw [noise_coordinate]
  have heq (x : Cube n) : signEntropy (ρ * sign (x i)) = signEntropy ρ := by
    cases hx : x i <;> simp
  simp_rw [heq]
  exact avg_const n _

/-- Complete entropy table of the six increasing Boolean functions on two bits. -/
theorem posteriorEntropy_two_ge {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (f : BooleanFunction 2) (hf : Monotone (lift f)) :
    fourier (lift f) {0} * signEntropy ρ +
      fourier (lift f) {1} * (2 * andPosteriorEntropy ρ - signEntropy ρ) ≤
      posteriorEntropy ρ f := by
  rcases monotone_boolean_two_cases f hf with h | h | h | h | h | h
  all_goals subst f
  · rw [posteriorEntropy_const]
    norm_num [fourier, avg_cube_two, walsh, lift]
  · rw [posteriorEntropy_const]
    norm_num [fourier, avg_cube_two, walsh, lift]
  · rw [posteriorEntropy_coordinate]
    norm_num [fourier, avg_cube_two, walsh, lift]
  · rw [posteriorEntropy_coordinate]
    norm_num [fourier, avg_cube_two, walsh, lift]
    linarith [andPosteriorEntropy_le hρ]
  · change _ ≤ andPosteriorEntropy ρ
    norm_num [fourier, avg_cube_two, walsh, lift, andFunction]
    linarith
  · rw [posteriorEntropy_orFunction]
    norm_num [fourier, avg_cube_two, walsh, lift, orFunction]
    linarith

/-- Averaging a section's singleton coefficient gives the original coefficient. -/
theorem avg_fourier_coreSections {k m : ℕ} (g : Cube (k + m) → ℝ) (i : Fin k) :
    avg (fun y : Cube m => fourier (fun x : Cube k => g (Fin.append x y)) {i}) =
      fourier g {i.castAdd m} := by
  simp_rw [fourier_singleton]
  rw [avg_cube_append (fun z => g z * sign (z (i.castAdd m)))]
  simp only [Fin.append_left]
  exact avg_avg_comm _

theorem monotone_append_section {k m : ℕ} {g : Cube (k+m) → ℝ}
    (hg : Monotone g) (y : Cube m) : Monotone (fun x : Cube k => g (Fin.append x y)) := by
  intro x x' hxx
  apply hg
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.append_left] using hxx j
  · simp only [Fin.append_right, le_refl]

/-- Two-coordinate entropy comparison in every ambient dimension. The
selected two-coordinate block is explicit, so no independence is implicit. -/
theorem posteriorEntropy_ge_twoCore {m : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (f : BooleanFunction (2 + m)) (hf : Monotone (lift f)) :
    ρ^2 * (fourier (lift f) {(0 : Fin 2).castAdd m} * signEntropy ρ +
      fourier (lift f) {(1 : Fin 2).castAdd m} *
        (2 * andPosteriorEntropy ρ - signEntropy ρ)) +
      (1-ρ^2) * avg (fun x : Cube 2 => signEntropy (noise ρ (coreAverage (lift f)) x)) ≤
      posteriorEntropy ρ f := by
  have hcore := signEntropy_noise_ge_core (k := 2) (m := m) hρ (lift f)
    (fun z => sign_mem_Icc (f z))
  have hsections := avg_mono (fun y : Cube m => posteriorEntropy_two_ge hρ
    (fun x : Cube 2 => f (Fin.append x y)) (monotone_append_section hf y))
  have hcoef0 : avg (fun y : Cube m =>
      fourier (lift (fun x : Cube 2 => f (Fin.append x y))) {0}) =
      fourier (lift f) {(0 : Fin 2).castAdd m} := avg_fourier_coreSections (lift f) 0
  have hcoef1 : avg (fun y : Cube m =>
      fourier (lift (fun x : Cube 2 => f (Fin.append x y))) {1}) =
      fourier (lift f) {(1 : Fin 2).castAdd m} := avg_fourier_coreSections (lift f) 1
  have havgmul {d : ℕ} (v : Cube d → ℝ) (c : ℝ) :
      avg (fun x => v x * c) = avg v * c := by
    simpa only [mul_comm] using avg_smul c v
  simp only [avg_add, havgmul, hcoef0, hcoef1] at hsections
  have hmul := mul_le_mul_of_nonneg_left hsections (sq_nonneg ρ)
  change _ ≤ posteriorEntropy ρ f at hcore
  exact le_trans (add_le_add hmul le_rfl) hcore

theorem avg_mul_const {n : ℕ} (g : Cube n → ℝ) (c : ℝ) :
    avg (fun x => g x * c) = avg g * c := by
  simpa only [mul_comm] using avg_smul c g

theorem avg_coreAverage {k m : ℕ} (g : Cube (k+m) → ℝ) :
    avg (coreAverage (k := k) (m := m) g) = avg g :=
  (avg_cube_append g).symm

theorem coreAverage_mem_Icc {k m : ℕ} (g : Cube (k+m) → ℝ)
    (hg : ∀ z, g z ∈ Set.Icc (-1 : ℝ) 1) (x : Cube k) :
    coreAverage g x ∈ Set.Icc (-1 : ℝ) 1 := by
  have hl := avg_mono (fun y : Cube m => (hg (Fin.append x y)).1)
  have hu := avg_mono (fun y : Cube m => (hg (Fin.append x y)).2)
  rw [avg_const] at hl hu
  exact ⟨hl, hu⟩

theorem walsh_append_map {k m : ℕ} (S : Finset (Fin k)) (x : Cube k) (y : Cube m) :
    walsh (S.map (Fin.castAddEmb m)) (Fin.append x y) = walsh S x := by
  simp only [walsh, Finset.prod_map, Fin.castAddEmb_apply, Fin.append_left]

theorem fourier_coreAverage {k m : ℕ} (g : Cube (k+m) → ℝ) (S : Finset (Fin k)) :
    fourier (coreAverage g) S = fourier g (S.map (Fin.castAddEmb m)) := by
  rw [fourier, fourier, avg_cube_append]
  simp only [walsh_append_map, coreAverage, avg_mul_const]

theorem twoCube_expansion (g : Cube 2 → ℝ) (x : Cube 2) :
    g x = avg g + fourier g {0} * sign (x 0) + fourier g {1} * sign (x 1) +
      fourier g {0,1} * sign (x 0) * sign (x 1) := by
  rw [twoCube_function_values g x]
  cases hx : x 0 <;> cases hy : x 1 <;>
    norm_num [fourier, avg_cube_two, walsh, hx, hy] <;> ring

theorem noise_twoCube_expansion (ρ : ℝ) (g : Cube 2 → ℝ) (x : Cube 2) :
    noise ρ g x = avg g + ρ * fourier g {0} * sign (x 0) +
      ρ * fourier g {1} * sign (x 1) + ρ^2 * fourier g {0,1} * sign (x 0) * sign (x 1) := by
  rw [noise_cube_two]
  cases hx : x 0 <;> cases hy : x 1 <;>
    norm_num [fourier, avg_cube_two, walsh, bitKernel, hx, hy] <;> ring

/-- The conditional mean is the actual degree-two Fourier polynomial, with
its constant coefficient retained. -/
theorem noise_twoCore_expansion {m : ℕ} (ρ : ℝ) (f : BooleanFunction (2+m)) (x : Cube 2) :
    noise ρ (coreAverage (lift f)) x = mean f +
      ρ * fourier (lift f) {(0 : Fin 2).castAdd m} * sign (x 0) +
      ρ * fourier (lift f) {(1 : Fin 2).castAdd m} * sign (x 1) +
      ρ^2 * fourier (lift f) {(0 : Fin 2).castAdd m, (1 : Fin 2).castAdd m} *
        sign (x 0) * sign (x 1) := by
  rw [noise_twoCube_expansion, avg_coreAverage]
  simp only [fourier_coreAverage, Finset.map_insert, Finset.map_singleton, Fin.castAddEmb_apply]
  rfl

theorem twoCore_singletons_sum_le_one {m : ℕ} (f : BooleanFunction (2+m)) :
    fourier (lift f) {(0 : Fin 2).castAdd m} +
      fourier (lift f) {(1 : Fin 2).castAdd m} ≤ 1 := by
  have hhi := (coreAverage_mem_Icc (k := 2) (m := m) (lift f)
    (fun z => sign_mem_Icc (f z)) ![true,true]).2
  have hlo := (coreAverage_mem_Icc (k := 2) (m := m) (lift f)
    (fun z => sign_mem_Icc (f z)) ![false,false]).1
  have ehi := twoCube_expansion (coreAverage (k := 2) (m := m) (lift f)) ![true,true]
  have elo := twoCube_expansion (coreAverage (k := 2) (m := m) (lift f)) ![false,false]
  simp only [fourier_coreAverage, Finset.map_insert, Finset.map_singleton,
    Fin.castAddEmb_apply] at ehi elo
  norm_num at ehi elo
  linarith

theorem monotone_singleton_nonneg {n : ℕ} {g : Cube n → ℝ} (hg : Monotone g) (i : Fin n) :
    0 ≤ fourier g {i} := by
  have h := abs_fourier_le_singleton_of_mem hg i {i} (by simp)
  exact (abs_nonneg _).trans h

theorem twoCore_interaction_abs_le_second {m : ℕ} (f : BooleanFunction (2+m))
    (hf : Monotone (lift f)) :
    |fourier (lift f) {(0 : Fin 2).castAdd m, (1 : Fin 2).castAdd m}| ≤
      fourier (lift f) {(1 : Fin 2).castAdd m} :=
  abs_fourier_le_singleton_of_mem hf _ _ (by simp)

end
end CK
