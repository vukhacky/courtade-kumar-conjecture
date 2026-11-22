module

public import CK.Profile.MovingFamily

/-! Exact whole-cell residual bounds. The low-cap residual is affine;
the high-cap mass/cap ratio is monotone by a polynomial factorization. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Profile
noncomputable section

theorem low_residual_domain {A B l u x : ℝ} (k : ℕ) (hA : A ≤ 0)
    (hx : x ∈ Icc l u)
    (hl : A*l+B-(k : ℝ)*l ≤ l) (hu : 0 ≤ A*u+B-(k : ℝ)*u) :
    A*x+B-(k : ℝ)*x ∈ Icc (0 : ℝ) x := by
  have hk := Nat.cast_nonneg (α := ℝ) k
  have hx₁ := mul_le_mul_of_nonpos_left hx.1 (show A-(k : ℝ)-1 ≤ 0 by linarith)
  have hx₂ := mul_le_mul_of_nonpos_left hx.2 (show A-(k : ℝ) ≤ 0 by linarith)
  constructor <;> nlinarith only [hx₁,hx₂,hl,hu]

theorem high_tail_cross_mono {A B a b : ℝ} (hA : A ≤ 0)
    (hab : a ≤ b) (hb : b ≤ 1) (hB : 0 ≤ B+A*b) :
    (A*a^2+B)*(1-b)^2 ≤ (A*b^2+B)*(1-a)^2 := by
  have hAa := mul_le_mul_of_nonpos_left hab hA
  have hBa : 0 ≤ B+A*a := by linarith only [hAa,hB]
  have hfactor : 0 ≤ (b-a)*((1-a)*(B+A*b)+(1-b)*(B+A*a)) :=
    mul_nonneg (sub_nonneg.mpr hab)
      (add_nonneg (mul_nonneg (by linarith only [hab,hb]) hB)
        (mul_nonneg (sub_nonneg.mpr hb) hBa))
  nlinarith only [hfactor]

theorem high_residual_domain {A B l u a : ℝ} (k : ℕ) (hA : A ≤ 0)
    (ha : a ∈ Icc l u) (hu1 : u < 1) (hB : 0 ≤ B+A*u)
    (hl : 0 ≤ A*l^2+B-(k : ℝ)*(1-l)^2)
    (hu : A*u^2+B-(k : ℝ)*(1-u)^2 ≤ (1-u)^2) :
    A*a^2+B-(k : ℝ)*(1-a)^2 ∈ Icc (0 : ℝ) ((1-a)^2) := by
  have hBa : 0 ≤ B+A*a := by
    have h := mul_le_mul_of_nonpos_left ha.2 hA
    linarith only [h,hB]
  have hlcross := high_tail_cross_mono hA ha.1 (ha.2.trans hu1.le) hBa
  have hucross := high_tail_cross_mono hA ha.2 hu1.le hB
  have hcapl : 0 < (1-l)^2 := sq_pos_of_pos (by linarith [ha.1,ha.2])
  have hcapu : 0 < (1-u)^2 := sq_pos_of_pos (sub_pos.mpr hu1)
  have hlprod := mul_le_mul_of_nonneg_right (show (k : ℝ)*(1-l)^2 ≤ A*l^2+B by linarith only [hl]) (sq_nonneg (1-a))
  have huprod := mul_le_mul_of_nonneg_right (show A*u^2+B ≤ ((k : ℝ)+1)*(1-u)^2 by nlinarith only [hu]) (sq_nonneg (1-a))
  have hlow : (k : ℝ)*(1-a)^2 ≤ A*a^2+B := (mul_le_mul_iff_left₀ hcapl).mp (by nlinarith only [hlcross,hlprod])
  have hupp : A*a^2+B ≤ ((k : ℝ)+1)*(1-a)^2 := (mul_le_mul_iff_left₀ hcapu).mp (by nlinarith only [hucross,huprod])
  constructor <;> nlinarith only [hlow,hupp]

theorem high_residual_domain_squared {A B l u x : ℝ} (k : ℕ) (hA : A ≤ 0)
    (hl0 : 0 ≤ l) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hx : x ∈ Icc (l^2) (u^2)) (hB : 0 ≤ B+A*u)
    (hl : 0 ≤ A*l^2+B-(k : ℝ)*(1-l)^2)
    (hu : A*u^2+B-(k : ℝ)*(1-u)^2 ≤ (1-u)^2) :
    A*x+B-(k : ℝ)*highCap x ∈ Icc (0 : ℝ) (highCap x) := by
  have hx0 : 0 ≤ x := (sq_nonneg l).trans hx.1
  have hsq := Real.sq_sqrt hx0
  have hla : l ≤ Real.sqrt x := (sq_le_sq₀ hl0 (Real.sqrt_nonneg x)).mp (by linarith only [hsq,hx.1])
  have hau : Real.sqrt x ≤ u := (sq_le_sq₀ (Real.sqrt_nonneg x) hu0).mp (by linarith only [hsq,hx.2])
  simpa only [hsq,highCap] using high_residual_domain k hA ⟨hla,hau⟩ hu1 hB hl hu

/-- A concave quadratic is nonnegative between two nonnegative endpoints. -/
theorem high_residual_nonneg {A B l u a : ℝ} (k : ℕ) (hA : A ≤ 0)
    (ha : a ∈ Icc l u)
    (hl : 0 ≤ A*l^2+B-(k : ℝ)*(1-l)^2)
    (hu : 0 ≤ A*u^2+B-(k : ℝ)*(1-u)^2) :
    0 ≤ A*a^2+B-(k : ℝ)*(1-a)^2 := by
  rcases eq_or_lt_of_le (ha.1.trans ha.2) with heq | hlu
  · have hae : a=l := by linarith only [ha.1,ha.2,heq]
    simpa only [hae] using hl
  have hkA : 0 ≤ (k : ℝ)-A := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hp := mul_nonneg hkA (mul_nonneg (sub_nonneg.mpr ha.1) (sub_nonneg.mpr ha.2))
  have hp₁ := mul_nonneg (sub_nonneg.mpr ha.2) hl
  have hp₂ := mul_nonneg (sub_nonneg.mpr ha.1) hu
  have hd : 0 < u-l := sub_pos.mpr hlu
  have hprod : 0 ≤ (u-l)*(A*a^2+B-(k : ℝ)*(1-a)^2) := by
    nlinarith only [mul_nonneg hd.le hp,hp₁,hp₂]
  exact (mul_nonneg_iff_of_pos_left hd).mp hprod

/-- A global quadratic upper bound, used when the tail/cap ratio changes direction. -/
theorem high_residual_le_cap_discriminant {A B a : ℝ} (k : ℕ) (hA : A ≤ 0)
    (hdisc : B*((k : ℝ)+1-A)+A*((k : ℝ)+1) ≤ 0) :
    A*a^2+B-(k : ℝ)*(1-a)^2 ≤ (1-a)^2 := by
  have hd : 0 < (k : ℝ)+1-A := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hsq := sq_nonneg (((k : ℝ)+1-A)*a-((k : ℝ)+1))
  have hp : ((k : ℝ)+1-A)*(A*a^2+B-(k : ℝ)*(1-a)^2-(1-a)^2) ≤ 0 := by
    nlinarith only [hdisc,hsq]
  by_contra hh
  have hhpos : 0 < A*a^2+B-(k : ℝ)*(1-a)^2-(1-a)^2 := by linarith only [hh]
  have hbad := mul_pos hd hhpos
  linarith only [hp,hbad]

theorem high_residual_domain_discriminant_squared {A B l u x : ℝ} (k : ℕ)
    (hA : A ≤ 0) (hl0 : 0 ≤ l) (hu0 : 0 ≤ u)
    (hx : x ∈ Icc (l^2) (u^2))
    (hl : 0 ≤ A*l^2+B-(k : ℝ)*(1-l)^2)
    (hu : 0 ≤ A*u^2+B-(k : ℝ)*(1-u)^2)
    (hdisc : B*((k : ℝ)+1-A)+A*((k : ℝ)+1) ≤ 0) :
    A*x+B-(k : ℝ)*highCap x ∈ Icc (0 : ℝ) (highCap x) := by
  have hx0 : 0 ≤ x := (sq_nonneg l).trans hx.1
  have hsq := Real.sq_sqrt hx0
  have hla : l ≤ Real.sqrt x := (sq_le_sq₀ hl0 (Real.sqrt_nonneg x)).mp (by linarith only [hsq,hx.1])
  have hau : Real.sqrt x ≤ u := (sq_le_sq₀ (Real.sqrt_nonneg x) hu0).mp (by linarith only [hsq,hx.2])
  have hlow := high_residual_nonneg k hA ⟨hla,hau⟩ hl hu
  have hupp := high_residual_le_cap_discriminant (a := Real.sqrt x) k hA hdisc
  simpa only [hsq,highCap,mem_Icc] using And.intro hlow hupp

end
end CK.Profile
