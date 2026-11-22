module

public import CK.Functional.Product
public import CK.Fourier.Projection

/-! Harris association on the uniform finite cube, proved by induction
on the coordinates. Conditional association is expressed by the actual
coordinate-average projection. Real increasing functions need not be
nonnegative. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

theorem monotone_cube_cons {n : ℕ} (b : Bool) :
    Monotone (fun x : Cube n => (Fin.cons b x : Cube (n+1))) := by
  intro x y hxy i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact le_rfl
  · exact hxy j

theorem cube_cons_false_le_true {n : ℕ} (x : Cube n) :
    (Fin.cons false x : Cube (n+1)) ≤ (Fin.cons true x : Cube (n+1)) := by
  intro i
  refine Fin.cases ?_ (fun _ => le_rfl) i
  simp only [Fin.cons_zero]
  exact Bool.false_le true

theorem monotone_section {n : ℕ} {g : Cube (n+1) → ℝ} (hg : Monotone g) (b : Bool) :
    Monotone (fun x : Cube n => g (Fin.cons b x)) := hg.comp (monotone_cube_cons b)

theorem avg_section_mono {n : ℕ} {g : Cube (n+1) → ℝ} (hg : Monotone g) :
    avg (fun x : Cube n => g (Fin.cons false x)) ≤
      avg (fun x : Cube n => g (Fin.cons true x)) :=
  avg_mono (fun x => hg (cube_cons_false_le_true x))

/-- Uniform Harris association in every finite dimension, including zero. -/
theorem harris {n : ℕ} (f g : Cube n → ℝ) (hf : Monotone f) (hg : Monotone g) :
    avg f * avg g ≤ avg (fun x => f x * g x) := by
  induction n with
  | zero => simp only [avg_cube_zero, le_refl]
  | succ n ih =>
    have h0 := ih (fun x => f (Fin.cons false x)) (fun x => g (Fin.cons false x))
      (monotone_section hf false) (monotone_section hg false)
    have h1 := ih (fun x => f (Fin.cons true x)) (fun x => g (Fin.cons true x))
      (monotone_section hf true) (monotone_section hg true)
    have hf01 := avg_section_mono hf
    have hg01 := avg_section_mono hg
    rw [avg_cube_cons f, avg_cube_cons g, avg_cube_cons (fun x => f x * g x)]
    rw [avg_pair, avg_pair, avg_pair]
    nlinarith [mul_nonneg (sub_nonneg.mpr hf01) (sub_nonneg.mpr hg01)]

theorem monotone_coordinateMask_right {n : ℕ} (K : Finset (Fin n)) (x : Cube n) :
    Monotone (coordinateMask K x) := by
  intro y z hyz i
  by_cases hi : i ∈ K
  · simp only [coordinateMask, ite_eq_left hi, le_refl]
  · simpa only [coordinateMask, ite_eq_right hi] using hyz i

theorem conditional_harris {n : ℕ} (K : Finset (Fin n)) (f g : Cube n → ℝ)
    (hf : Monotone f) (hg : Monotone g) (x : Cube n) :
    coordinateProjection K f x * coordinateProjection K g x ≤
      coordinateProjection K (fun y => f y * g y) x := by
  exact harris (fun y => f (coordinateMask K x y)) (fun y => g (coordinateMask K x y))
    (hf.comp (monotone_coordinateMask_right K x))
    (hg.comp (monotone_coordinateMask_right K x))

theorem avg_projected_mul_le {n : ℕ} (K : Finset (Fin n)) (f g : Cube n → ℝ)
    (hf : Monotone f) (hg : Monotone g) :
    avg (fun x => coordinateProjection K f x * coordinateProjection K g x) ≤
      avg (fun x => f x * g x) := by
  calc
    _ ≤ avg (coordinateProjection K (fun x => f x * g x)) :=
      avg_mono (conditional_harris K f g hf hg)
    _ = _ := avg_coordinateProjection K _

theorem noise_cons_false_le_true {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    {f : Cube (n+1) → ℝ} (hf : Monotone f) (x : Cube n) :
    noise ρ f (Fin.cons false x) ≤ noise ρ f (Fin.cons true x) := by
  have h01 : noise ρ (fun y => f (Fin.cons false y)) x ≤
      noise ρ (fun y => f (Fin.cons true y)) x :=
    noise_mono ⟨by linarith [hρ.1], hρ.2⟩ (fun y => hf (cube_cons_false_le_true y)) x
  rw [noise_cons, noise_cons]
  norm_num [bitKernel]
  nlinarith [mul_nonneg hρ.1 (sub_nonneg.mpr h01)]

/-- Nonnegative-correlation BSC noise preserves coordinate monotonicity. -/
theorem noise_monotone {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    {f : Cube n → ℝ} (hf : Monotone f) : Monotone (noise ρ f) := by
  induction n with
  | zero =>
    intro x y _
    have hxy : x = y := by funext i; exact Fin.elim0 i
    rw [hxy]
  | succ n ih =>
    have h0 := ih (monotone_section hf false)
    have h1 := ih (monotone_section hf true)
    intro x y hxy
    have ht : Fin.tail x ≤ Fin.tail y := fun j => hxy j.succ
    have hhead : x 0 ≤ y 0 := hxy 0
    calc
      noise ρ f x = noise ρ f (Fin.cons (x 0) (Fin.tail x)) := by
        rw [Fin.cons_self_tail]
      _ ≤ noise ρ f (Fin.cons (x 0) (Fin.tail y)) := by
        rw [noise_cons, noise_cons]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (h0 ht)
            (bitKernel_nonneg ⟨by linarith [hρ.1], hρ.2⟩ _ _))
          (mul_le_mul_of_nonneg_left (h1 ht)
            (bitKernel_nonneg ⟨by linarith [hρ.1], hρ.2⟩ _ _))
      _ ≤ noise ρ f (Fin.cons (y 0) (Fin.tail y)) := by
        cases hx : x 0 <;> cases hy : y 0
        · exact le_rfl
        · exact noise_cons_false_le_true hρ hf _
        · have hh : (true : Bool) ≤ false := by simpa only [hx, hy] using hhead
          have heq : (false : Bool) = true := Bool.eq_true_of_true_le hh
          cases heq
        · exact le_rfl
      _ = noise ρ f y := by rw [Fin.cons_self_tail]

end
end CK
