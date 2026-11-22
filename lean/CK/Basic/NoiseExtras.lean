module

public import CK.Basic.Cube
public import CK.Fourier.Noise

/-! Coordinate moments of the explicit product BSC kernel. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

theorem bitKernel_sign_sum (ρ : ℝ) (a : Bool) :
    ∑ b : Bool, bitKernel ρ a b * sign b = ρ * sign a := by
  cases a <;> simp [bitKernel, sign] <;> ring

theorem noise_coordinate {n : ℕ} (ρ : ℝ) (i : Fin n) (x : Cube n) :
    noise ρ (fun y => sign (y i)) x = ρ * sign (x i) := by
  classical
  unfold noise bscKernel
  have hprod (y : Cube n) :
      (∏ j : Fin n, bitKernel ρ (x j) (y j)) * sign (y i) =
        ∏ j : Fin n, bitKernel ρ (x j) (y j) *
          (if j = i then sign (y j) else 1) := by
    rw [Finset.prod_mul_distrib]
    simp
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun j b => bitKernel ρ (x j) b *
    (if j = i then sign b else 1))]
  have hsum (j : Fin n) :
      (∑ b : Bool, bitKernel ρ (x j) b * (if j = i then sign b else 1)) =
        if j = i then ρ * sign (x j) else 1 := by
    by_cases h : j = i
    · subst j
      simp only
      exact bitKernel_sign_sum ρ (x i)
    · simp only [ite_eq_right h, mul_one]
      exact bitKernel_sum ρ (x j)
  simp_rw [hsum]
  simp

theorem mean_coordinate {n : ℕ} (i : Fin n) : mean (fun x : Cube n => x i) = 0 := by
  have h := noise_coordinate 0 i (fun _ => false)
  change avg (fun y => sign (y i)) = 0
  simpa [noise_zero] using h

theorem mean_complement {n : ℕ} (f : BooleanFunction n) :
    mean (fun x => !(f x)) = -mean f := by
  change avg (fun x => sign (!(f x))) = -avg (fun x => sign (f x))
  simp only [sign_not, avg_neg]

theorem signedDictator_balanced {n : ℕ} {f : BooleanFunction n}
    (hf : IsSignedDictator f) : Balanced f := by
  rcases hf with ⟨i, hi | hi⟩
  · have heq : f = fun x => x i := funext hi
    rw [heq]
    exact mean_coordinate i
  · have heq : f = fun x => !(x i) := funext hi
    unfold Balanced
    rw [heq, mean_complement, mean_coordinate, neg_zero]

/-- A nonconstant Boolean summary has a strictly interior posterior mean
under strictly positive BSC weights. -/
theorem noise_lift_mem_Ioo {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1)
    (f : BooleanFunction n) (hf : ∃ u v, f u ≠ f v) (x : Cube n) :
    noise ρ (lift f) x ∈ Set.Ioo (-1 : ℝ) 1 := by
  classical
  obtain ⟨u, v, huv⟩ := hf
  have hfalse : ∃ y, f y = false := by
    cases hu : f u <;> cases hv : f v
    · exact ⟨u, hu⟩
    · exact ⟨u, hu⟩
    · exact ⟨v, hv⟩
    · exact (huv (hu.trans hv.symm)).elim
  have htrue : ∃ y, f y = true := by
    cases hu : f u <;> cases hv : f v
    · exact (huv (hu.trans hv.symm)).elim
    · exact ⟨v, hv⟩
    · exact ⟨u, hu⟩
    · exact ⟨u, hu⟩
  constructor
  · obtain ⟨y, hy⟩ := htrue
    calc
      -1 = noise ρ (fun _ : Cube n => -1) x := (noise_const ρ (-1) x).symm
      _ < noise ρ (lift f) x := by
        apply Finset.sum_lt_sum
        · intro z _
          exact mul_le_mul_of_nonneg_left (sign_mem_Icc (f z)).1
            (le_of_lt (bscKernel_pos hρ x z))
        · refine ⟨y, Finset.mem_univ y, ?_⟩
          change bscKernel ρ x y * (-1) < bscKernel ρ x y * sign (f y)
          rw [hy, sign_true]
          nlinarith [bscKernel_pos hρ x y]
  · obtain ⟨y, hy⟩ := hfalse
    calc
      noise ρ (lift f) x < noise ρ (fun _ : Cube n => 1) x := by
        apply Finset.sum_lt_sum
        · intro z _
          exact mul_le_mul_of_nonneg_left (sign_mem_Icc (f z)).2
            (le_of_lt (bscKernel_pos hρ x z))
        · refine ⟨y, Finset.mem_univ y, ?_⟩
          change bscKernel ρ x y * sign (f y) < bscKernel ρ x y * 1
          rw [hy, sign_false]
          nlinarith [bscKernel_pos hρ x y]
      _ = 1 := noise_const ρ 1 x

end
end CK
