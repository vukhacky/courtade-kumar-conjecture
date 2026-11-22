module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

/-! The finite Boolean cube and the binary symmetric noise kernel. Stochasticity and the endpoint identities follow from finite sums. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

abbrev Cube (n : ℕ) := Fin n → Bool
abbrev BooleanFunction (n : ℕ) := Cube n → Bool

def sign (b : Bool) : ℝ := if b then 1 else -1
def lift {n : ℕ} (f : BooleanFunction n) : Cube n → ℝ := fun x => sign (f x)

def avg {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  (Fintype.card (Cube n) : ℝ)⁻¹ * ∑ x, g x

def mean {n : ℕ} (f : BooleanFunction n) : ℝ := avg (lift f)
def Balanced {n : ℕ} (f : BooleanFunction n) : Prop := mean f = 0
def IsSignedDictator {n : ℕ} (f : BooleanFunction n) : Prop :=
  ∃ i : Fin n, (∀ x, f x = x i) ∨ (∀ x, f x = !(x i))

def bitKernel (ρ : ℝ) (a b : Bool) : ℝ :=
  if a = b then (1 + ρ) / 2 else (1 - ρ) / 2

def bscKernel {n : ℕ} (ρ : ℝ) (x y : Cube n) : ℝ :=
  ∏ i, bitKernel ρ (x i) (y i)

def noise {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) (x : Cube n) : ℝ :=
  ∑ y, bscKernel ρ x y * g y

theorem card_cube (n : ℕ) : Fintype.card (Cube n) = 2 ^ n := by
  simp [Cube]

theorem card_cube_pos (n : ℕ) : 0 < (Fintype.card (Cube n) : ℝ) := by
  rw [card_cube]
  positivity

@[simp] theorem sign_false : sign false = -1 := rfl
@[simp] theorem sign_true : sign true = 1 := rfl
@[simp] theorem sign_not (b : Bool) : sign (!b) = - sign b := by cases b <;> simp [sign]
theorem sign_mem_Icc (b : Bool) : sign b ∈ Set.Icc (-1 : ℝ) 1 := by
  cases b <;> norm_num [sign]

@[simp] theorem avg_const (n : ℕ) (c : ℝ) : avg (fun _ : Cube n => c) = c := by
  simp [avg]

theorem avg_add {n : ℕ} (g h : Cube n → ℝ) :
    avg (fun x => g x + h x) = avg g + avg h := by
  simp [avg, Finset.sum_add_distrib, mul_add]

theorem avg_smul {n : ℕ} (c : ℝ) (g : Cube n → ℝ) :
    avg (fun x => c * g x) = c * avg g := by
  simp only [avg, ← Finset.mul_sum]
  ring

theorem avg_neg {n : ℕ} (g : Cube n → ℝ) :
    avg (fun x => -g x) = - avg g := by
  simp [avg]

theorem avg_sub {n : ℕ} (g h : Cube n → ℝ) :
    avg (fun x => g x - h x) = avg g - avg h := by
  simp [avg, Finset.sum_sub_distrib, mul_sub]

theorem avg_mono {n : ℕ} {g h : Cube n → ℝ} (hgh : ∀ x, g x ≤ h x) :
    avg g ≤ avg h := by
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hgh x)
    (inv_nonneg.mpr (le_of_lt (card_cube_pos n)))

theorem mean_mem_Icc {n : ℕ} (f : BooleanFunction n) : mean f ∈ Set.Icc (-1 : ℝ) 1 := by
  have hlo : avg (fun _ : Cube n => (-1 : ℝ)) ≤ avg (lift f) :=
    avg_mono (fun x => (sign_mem_Icc (f x)).1)
  have hhi : avg (lift f) ≤ avg (fun _ : Cube n => (1 : ℝ)) :=
    avg_mono (fun x => (sign_mem_Icc (f x)).2)
  rw [avg_const] at hlo hhi
  exact ⟨hlo, hhi⟩

theorem bitKernel_symm (ρ : ℝ) (a b : Bool) : bitKernel ρ a b = bitKernel ρ b a := by
  simp [bitKernel, eq_comm]

theorem bitKernel_sum (ρ : ℝ) (a : Bool) : ∑ b : Bool, bitKernel ρ a b = 1 := by
  cases a <;> simp [bitKernel] <;> ring

theorem bitKernel_nonneg {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (a b : Bool) :
    0 ≤ bitKernel ρ a b := by
  unfold bitKernel
  split_ifs <;> linarith [hρ.1, hρ.2]

theorem bscKernel_symm {n : ℕ} (ρ : ℝ) (x y : Cube n) :
    bscKernel ρ x y = bscKernel ρ y x := by
  simp only [bscKernel, bitKernel_symm ρ]

theorem bscKernel_nonneg {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (x y : Cube n) : 0 ≤ bscKernel ρ x y := by
  exact Finset.prod_nonneg fun i _ => bitKernel_nonneg hρ (x i) (y i)

theorem bscKernel_sum {n : ℕ} (ρ : ℝ) (x : Cube n) :
    ∑ y, bscKernel ρ x y = 1 := by
  unfold bscKernel
  rw [← Fintype.prod_sum]
  simp only [bitKernel_sum, Finset.prod_const_one]

theorem bscKernel_zero {n : ℕ} (x y : Cube n) :
    bscKernel 0 x y = (Fintype.card (Cube n) : ℝ)⁻¹ := by
  simp [bscKernel, bitKernel]

theorem bscKernel_one {n : ℕ} (x y : Cube n) :
    bscKernel 1 x y = if x = y then 1 else 0 := by
  classical
  by_cases h : x = y
  · subst y
    simp [bscKernel, bitKernel]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hh
      push Not at hh
      exact h (funext hh)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [bitKernel, hi])

theorem noise_zero {n : ℕ} (g : Cube n → ℝ) (x : Cube n) : noise 0 g x = avg g := by
  simp only [noise, bscKernel_zero, avg, Finset.mul_sum]

theorem noise_one {n : ℕ} (g : Cube n → ℝ) (x : Cube n) : noise 1 g x = g x := by
  classical
  simp [noise, bscKernel_one]

theorem noise_const {n : ℕ} (ρ c : ℝ) (x : Cube n) :
    noise ρ (fun _ : Cube n => c) x = c := by
  rw [noise, ← Finset.sum_mul, bscKernel_sum, one_mul]

theorem noise_neg {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) (x : Cube n) :
    noise ρ (fun y => -g y) x = - noise ρ g x := by
  simp [noise]

theorem avg_noise {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) :
    avg (noise ρ g) = avg g := by
  unfold avg noise
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.sum_mul]
  have hsum : ∑ x : Cube n, bscKernel ρ x y = 1 := by
    simp only [bscKernel_symm ρ _ y]
    exact bscKernel_sum ρ y
  rw [hsum, one_mul]

theorem noise_mem_Icc {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (g : Cube n → ℝ) (hg : ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1) (x : Cube n) :
    noise ρ g x ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor
  · calc
      -1 = noise ρ (fun _ : Cube n => -1) x := (noise_const ρ (-1) x).symm
      _ ≤ noise ρ g x := Finset.sum_le_sum fun y _ =>
        mul_le_mul_of_nonneg_left (hg y).1 (bscKernel_nonneg hρ x y)
  · calc
      noise ρ g x ≤ noise ρ (fun _ : Cube n => 1) x := Finset.sum_le_sum fun y _ =>
        mul_le_mul_of_nonneg_left (hg y).2 (bscKernel_nonneg hρ x y)
      _ = 1 := noise_const ρ 1 x

end
end CK
