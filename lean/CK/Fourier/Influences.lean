module

public import CK.Fourier.Parseval
public import CK.Functional.Product

/-! Coordinate half-differences, Boolean influences, and the coefficient
bounds used by the conditional Harris argument. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

def flipCoordinate {n : ℕ} (i : Fin n) (x : Cube n) : Cube n :=
  Function.update x i (!(x i))

theorem flipCoordinate_apply_same {n : ℕ} (i : Fin n) (x : Cube n) :
    flipCoordinate i x i = !(x i) := by simp [flipCoordinate]

theorem flipCoordinate_apply_ne {n : ℕ} (i j : Fin n) (hji : j ≠ i) (x : Cube n) :
    flipCoordinate i x j = x j := by simp [flipCoordinate, hji]

theorem flipCoordinate_involutive {n : ℕ} (i : Fin n) :
    Function.Involutive (flipCoordinate i) := by
  intro x
  funext j
  by_cases hji : j = i
  · subst j; simp [flipCoordinate]
  · simp [flipCoordinate, hji]

def flipCoordinateEquiv {n : ℕ} (i : Fin n) : Cube n ≃ Cube n where
  toFun := flipCoordinate i
  invFun := flipCoordinate i
  left_inv := flipCoordinate_involutive i
  right_inv := flipCoordinate_involutive i

theorem avg_flipCoordinate {n : ℕ} (i : Fin n) (g : Cube n → ℝ) :
    avg (fun x => g (flipCoordinate i x)) = avg g := by
  unfold avg
  congr 1
  exact (flipCoordinateEquiv i).sum_comp g

theorem walsh_flipCoordinate {n : ℕ} (i : Fin n) (S : Finset (Fin n)) (x : Cube n) :
    walsh S (flipCoordinate i x) = if i ∈ S then -walsh S x else walsh S x := by
  classical
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi]
    have hrest : (∏ j ∈ S.erase i, sign (flipCoordinate i x j)) =
        ∏ j ∈ S.erase i, sign (x j) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [flipCoordinate_apply_ne i j (Finset.mem_erase.mp hj).1]
    rw [walsh, ← Finset.prod_erase_mul S (fun j => sign (flipCoordinate i x j)) hi,
      hrest, flipCoordinate_apply_same, sign_not, walsh,
      ← Finset.prod_erase_mul S (fun j => sign (x j)) hi]
    ring
  · rw [ite_eq_right hi]
    unfold walsh
    apply Finset.prod_congr rfl
    intro j hj
    rw [flipCoordinate_apply_ne i j (by intro h; subst j; exact hi hj)]

theorem fourier_flipCoordinate {n : ℕ} (i : Fin n) (g : Cube n → ℝ)
    (S : Finset (Fin n)) :
    fourier (fun x => g (flipCoordinate i x)) S =
      if i ∈ S then -fourier g S else fourier g S := by
  classical
  rw [fourier, ← avg_flipCoordinate i
    (fun x => g (flipCoordinate i x) * walsh S x)]
  have hinv (x : Cube n) : flipCoordinate i (flipCoordinate i x) = x :=
    flipCoordinate_involutive i x
  simp only [hinv, walsh_flipCoordinate]
  split_ifs
  · simp only [mul_neg, avg_neg]
    rfl
  · rfl

def coordinatePartial {n : ℕ} (i : Fin n) (g : Cube n → ℝ) (x : Cube n) : ℝ :=
  (g x - g (flipCoordinate i x)) / 2

def influence {n : ℕ} (i : Fin n) (f : BooleanFunction n) : ℝ :=
  avg (fun x => |coordinatePartial i (lift f) x|)

theorem fourier_coordinatePartial {n : ℕ} (i : Fin n) (g : Cube n → ℝ)
    (S : Finset (Fin n)) : fourier (coordinatePartial i g) S =
      if i ∈ S then fourier g S else 0 := by
  classical
  have hp : coordinatePartial i g = fun x => (1/2 : ℝ) *
      (g x - g (flipCoordinate i x)) := by funext x; simp [coordinatePartial]; ring
  rw [hp, fourier_smul, fourier_sub, fourier_flipCoordinate]
  split_ifs <;> ring

theorem le_flipCoordinate_of_false {n : ℕ} (i : Fin n) (x : Cube n) (hx : x i = false) :
    x ≤ flipCoordinate i x := by
  intro j
  by_cases hji : j = i
  · subst j
    rw [flipCoordinate_apply_same, hx]
    exact Bool.false_le true
  · rw [flipCoordinate_apply_ne i j hji]

theorem flipCoordinate_le_of_true {n : ℕ} (i : Fin n) (x : Cube n) (hx : x i = true) :
    flipCoordinate i x ≤ x := by
  intro j
  by_cases hji : j = i
  · subst j
    rw [flipCoordinate_apply_same, hx]
    exact Bool.false_le true
  · rw [flipCoordinate_apply_ne i j hji]

theorem coordinatePartial_eq_abs_mul_sign {n : ℕ} {g : Cube n → ℝ} (hg : Monotone g)
    (i : Fin n) (x : Cube n) :
    coordinatePartial i g x = |coordinatePartial i g x| * sign (x i) := by
  cases hx : x i
  · have hle := hg (le_flipCoordinate_of_false i x hx)
    have hp : coordinatePartial i g x ≤ 0 := by unfold coordinatePartial; linarith
    rw [abs_of_nonpos hp, sign_false]
    ring
  · have hle := hg (flipCoordinate_le_of_true i x hx)
    have hp : 0 ≤ coordinatePartial i g x := by unfold coordinatePartial; linarith
    rw [abs_of_nonneg hp, sign_true, mul_one]

theorem fourier_singleton_eq_avg_abs_partial {n : ℕ} {g : Cube n → ℝ} (hg : Monotone g)
    (i : Fin n) : fourier g {i} = avg (fun x => |coordinatePartial i g x|) := by
  have hf : fourier (coordinatePartial i g) {i} = fourier g {i} := by
    rw [fourier_coordinatePartial]
    simp
  rw [← hf, fourier_singleton]
  have hp (x : Cube n) : coordinatePartial i g x * sign (x i) =
      |coordinatePartial i g x| := by
    calc
      _ = (|coordinatePartial i g x| * sign (x i)) * sign (x i) :=
        congrArg (fun r => r * sign (x i)) (coordinatePartial_eq_abs_mul_sign hg i x)
      _ = _ := by rw [mul_assoc, sign_mul_self, mul_one]
  simp_rw [hp]

theorem abs_fourier_le_singleton_of_mem {n : ℕ} {g : Cube n → ℝ} (hg : Monotone g)
    (i : Fin n) (S : Finset (Fin n)) (hi : i ∈ S) :
    |fourier g S| ≤ fourier g {i} := by
  have hf : fourier (coordinatePartial i g) S = fourier g S := by
    rw [fourier_coordinatePartial, ite_eq_left hi]
  rw [← hf, fourier, fourier_singleton_eq_avg_abs_partial hg i]
  calc
    _ ≤ avg (fun x => |coordinatePartial i g x * walsh S x|) := abs_avg_le_avg_abs _
    _ = _ := by
      congr 1
      funext x
      rw [abs_mul]
      have hw : |walsh S x| = 1 := by
        have h := walsh_sq S x
        nlinarith [sq_abs (walsh S x), abs_nonneg (walsh S x)]
      rw [hw, mul_one]

theorem influence_eq_singleton {n : ℕ} (f : BooleanFunction n)
    (hf : Monotone (lift f)) (i : Fin n) : influence i f = fourier (lift f) {i} :=
  (fourier_singleton_eq_avg_abs_partial hf i).symm

theorem abs_coordinatePartial_boolean_eq_sq {n : ℕ} (f : BooleanFunction n)
    (i : Fin n) (x : Cube n) :
    |coordinatePartial i (lift f) x| = coordinatePartial i (lift f) x ^ 2 := by
  change |(sign (f x)-sign (f (flipCoordinate i x)))/2| =
    ((sign (f x)-sign (f (flipCoordinate i x)))/2)^2
  cases h1 : f x <;> cases h2 : f (flipCoordinate i x) <;> norm_num [sign]

theorem influence_eq_avg_sq_partial {n : ℕ} (f : BooleanFunction n) (i : Fin n) :
    influence i f = avg (fun x => coordinatePartial i (lift f) x ^ 2) := by
  unfold influence
  simp only [abs_coordinatePartial_boolean_eq_sq]

theorem singleton_nonneg_of_monotone {n : ℕ} {g : Cube n → ℝ} (hg : Monotone g)
    (i : Fin n) : 0 ≤ fourier g {i} := by
  rw [fourier_singleton_eq_avg_abs_partial hg i]
  have h := avg_mono (fun x : Cube n => abs_nonneg (coordinatePartial i g x))
  simpa only [avg_const] using h

theorem singleton_pair_le_one {n : ℕ} (f : BooleanFunction n) (i j : Fin n)
    (hij : i ≠ j) : fourier (lift f) {i} + fourier (lift f) {j} ≤ 1 := by
  have hp (x : Cube n) : lift f x * sign (x i) + lift f x * sign (x j) ≤
      1 + sign (x i) * sign (x j) := by
    change sign (f x) * sign (x i) + sign (f x) * sign (x j) ≤
      1 + sign (x i) * sign (x j)
    cases hf : f x <;> cases hi : x i <;> cases hj : x j <;> norm_num [sign]
  have h := avg_mono hp
  rw [avg_add, avg_add, avg_const] at h
  have ho : avg (fun x : Cube n => sign (x i) * sign (x j)) = 0 := by
    simpa [walsh_singleton, hij] using walsh_orthogonality ({i} : Finset (Fin n)) {j}
  rw [ho, add_zero] at h
  simpa only [fourier_singleton] using h

theorem exists_positive_singleton_of_monotone_nonconstant {n : ℕ}
    {g : Cube n → ℝ} (hg : Monotone g) (hnc : ∃ x y, g x ≠ g y) :
    ∃ i : Fin n, 0 < fourier g {i} := by
  classical
  have hS : ∃ S : Finset (Fin n), S.Nonempty ∧ fourier g S ≠ 0 := by
    by_contra h
    push Not at h
    have hc : g = fun _ : Cube n => avg g := by
      apply fourier_ext
      intro S
      rw [fourier_const]
      by_cases he : S = ∅
      · subst S; simp [fourier_empty]
      · rw [ite_eq_right he, h S (Finset.ne_empty_iff_nonempty.mp he)]
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy (by rw [hc])
  obtain ⟨S, hSne, hS0⟩ := hS
  obtain ⟨i, hi⟩ := hSne
  exact ⟨i, (abs_pos.mpr hS0).trans_le (abs_fourier_le_singleton_of_mem hg i S hi)⟩

theorem first_level_positive_of_monotone_nonconstant {n : ℕ}
    {g : Cube n → ℝ} (hg : Monotone g) (hnc : ∃ x y, g x ≠ g y) :
    0 < fourierWeight g 1 := by
  classical
  obtain ⟨i, hi⟩ := exists_positive_singleton_of_monotone_nonconstant hg hnc
  have hle : fourier g {i} ^ 2 ≤ fourierWeight g 1 := by
    unfold fourierWeight
    have h := Finset.single_le_sum (s := (Finset.univ : Finset (Finset (Fin n))))
      (f := fun S => if S.card = 1 then fourier g S ^ 2 else 0)
      (fun S _ => by split_ifs <;> positivity) (Finset.mem_univ ({i} : Finset (Fin n)))
    simpa using h
  exact (sq_pos_of_pos hi).trans_le hle

end
end CK
