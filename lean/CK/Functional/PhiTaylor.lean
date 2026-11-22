module

public import CK.Analysis.BinaryEntropy

/-! Finite Taylor bounds for binary-entropy deficit, proved by exact second
-derivative identities. No infinite series or untrusted approximation enters
the proof. The upper bound uses a fixed rationalizable radius. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
open Set
namespace CK
noncomputable section

def phiTaylorTerm (k : ℕ) (t : ℝ) : ℝ := t^(2*k+2)/((2*(k:ℝ)+2)*(2*k+1))
def phiTaylorTermSlope (k : ℕ) (t : ℝ) : ℝ := t^(2*k+1)/(2*(k:ℝ)+1)
def phiTaylor (N : ℕ) (t : ℝ) : ℝ := ∑ k ∈ Finset.range N, phiTaylorTerm k t
def phiTaylorSlope (N : ℕ) (t : ℝ) : ℝ := ∑ k ∈ Finset.range N, phiTaylorTermSlope k t
def phiTaylorCurvature (N : ℕ) (t : ℝ) : ℝ := ∑ k ∈ Finset.range N, t^(2*k)

/-- The Taylor polynomial after factoring out `t²` and setting `x=t²`. -/
def phiTaylorBase (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, x^k/((2*(k:ℝ)+2)*(2*k+1))

/-- Rational polynomial lower envelope for `localDeficit rho a / rho²`.
`R` is the correlation radius and `L` an upper bound for natural `log 2`. -/
def localTaylorPolynomial (N M : ℕ) (a R L x : ℝ) : ℝ :=
  (a-1)*L + (1-a*x)*phiTaylorBase N x - (1-x)*
    (a^2*phiTaylorBase M (a^2*x) +
      (1/(1-(a*R)^2))*a^(2*M+2)*x^M/((2*(M:ℝ)+2)*(2*M+1)))

theorem hasDerivAt_phiTaylorTerm (k : ℕ) (t : ℝ) :
    HasDerivAt (phiTaylorTerm k) (phiTaylorTermSlope k t) t := by
  apply ((hasDerivAt_pow (2*k+2) t).div_const ((2*(k:ℝ)+2)*(2*k+1))).congr_deriv
  unfold phiTaylorTermSlope
  rw [show 2*k+2-1=2*k+1 by omega]
  push_cast
  have h1 : (2*(k:ℝ)+1) ≠ 0 := by positivity
  have h2 : (2*(k:ℝ)+2) ≠ 0 := by positivity
  field_simp

theorem hasDerivAt_phiTaylorTermSlope (k : ℕ) (t : ℝ) :
    HasDerivAt (phiTaylorTermSlope k) (t^(2*k)) t := by
  apply ((hasDerivAt_pow (2*k+1) t).div_const (2*(k:ℝ)+1)).congr_deriv
  rw [show 2*k+1-1=2*k by omega]
  push_cast
  have h1 : (2*(k:ℝ)+1) ≠ 0 := by positivity
  field_simp

theorem hasDerivAt_phiTaylor (N : ℕ) (t : ℝ) :
    HasDerivAt (phiTaylor N) (phiTaylorSlope N t) t := by
  unfold phiTaylor phiTaylorSlope
  exact HasDerivAt.fun_sum (u := Finset.range N) (fun k _ => hasDerivAt_phiTaylorTerm k t)

theorem hasDerivAt_phiTaylorSlope (N : ℕ) (t : ℝ) :
    HasDerivAt (phiTaylorSlope N) (phiTaylorCurvature N t) t := by
  unfold phiTaylorSlope phiTaylorCurvature
  exact HasDerivAt.fun_sum (u := Finset.range N) (fun k _ => hasDerivAt_phiTaylorTermSlope k t)

theorem phiTaylorTerm_even (k : ℕ) (t : ℝ) : phiTaylorTerm k (-t)=phiTaylorTerm k t := by
  simp only [phiTaylorTerm, pow_add, pow_mul, neg_sq]

theorem phiTaylor_even (N : ℕ) (t : ℝ) : phiTaylor N (-t)=phiTaylor N t := by
  simp only [phiTaylor,phiTaylorTerm_even]

@[simp] theorem phiTaylorTerm_zero (k : ℕ) : phiTaylorTerm k 0=0 := by
  simp [phiTaylorTerm]

@[simp] theorem phiTaylor_zero (N : ℕ) : phiTaylor N 0=0 := by
  simp [phiTaylor]

theorem phiTaylorCurvature_geometric (N : ℕ) (t : ℝ) :
    (1-t^2)*phiTaylorCurvature N t = 1-t^(2*N) := by
  induction N with
  | zero => simp [phiTaylorCurvature]
  | succ N ih =>
    rw [phiTaylorCurvature,Finset.sum_range_succ]
    rw [show 2*(N+1)=2*N+2 by omega, pow_add]
    change (1-t^2)*(phiTaylorCurvature N t+t^(2*N))=1-t^(2*N)*t^2
    nlinarith only [ih]

theorem phiTaylorCurvature_remainder (N : ℕ) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    1/(1-t^2)-phiTaylorCurvature N t = t^(2*N)/(1-t^2) := by
  have hn : 1-t^2 ≠ 0 := by nlinarith [ht.1,ht.2]
  have h := phiTaylorCurvature_geometric N t
  field_simp [hn]
  nlinarith only [h]

theorem phiTaylor_le_phi (N : ℕ) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    phiTaylor N t ≤ phi t := by
  let F : ℝ → ℝ := fun x => phi x-phiTaylor N x
  have hc : ConvexOn ℝ (Icc (-1 : ℝ) 1) F := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (f' := fun x => phiSlope x-phiTaylorSlope N x)
      (f'' := fun x => 1/(1-x^2)-phiTaylorCurvature N x)
    · dsimp [F]
      unfold phiTaylor phiTaylorTerm
      fun_prop
    · intro x hx
      exact ((hasDerivAt_phi (by simpa only [interior_Icc] using hx)).sub
        (hasDerivAt_phiTaylor N x)).hasDerivWithinAt
    · intro x hx
      exact ((hasDerivAt_phiSlope (by simpa only [interior_Icc] using hx)).sub
        (hasDerivAt_phiTaylorSlope N x)).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Ioo (-1 : ℝ) 1 := by simpa only [interior_Icc] using hx
      rw [phiTaylorCurvature_remainder N hx']
      exact div_nonneg (by rw [pow_mul]; positivity) (by nlinarith [hx'.1,hx'.2])
  have hn : -t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have h := hc.2 ht hn (by norm_num : (0:ℝ)≤1/2) (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)+1/2=1)
  simp only [smul_eq_mul] at h
  rw [show (1/2:ℝ)*t+(1/2)*(-t)=0 by ring] at h
  simp only [F,phi_zero,phiTaylor_zero,sub_self,phi_neg,phiTaylor_even] at h
  linarith

/-- A uniform finite upper Taylor bound throughout `[-r,r]`, with `r<1`.
The coefficient `1/(1-r²)` is fixed before differentiating. -/
theorem phi_le_phiTaylor_bound (N : ℕ) {r t : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (ht : t ∈ Icc (-r) r) :
    phi t ≤ phiTaylor N t + (1/(1-r^2))*phiTaylorTerm N t := by
  let B : ℝ := 1/(1-r^2)
  let F : ℝ → ℝ := fun x => phiTaylor N x+B*phiTaylorTerm N x-phi x
  have hc : ConvexOn ℝ (Icc (-r) r) F := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (f' := fun x => phiTaylorSlope N x+B*phiTaylorTermSlope N x-phiSlope x)
      (f'' := fun x => phiTaylorCurvature N x+B*x^(2*N)-1/(1-x^2))
    · dsimp [F]
      unfold phiTaylor phiTaylorTerm
      fun_prop
    · intro x hx
      have hx' : x ∈ Ioo (-1 : ℝ) 1 := by
        simp only [interior_Icc,mem_Ioo] at hx
        constructor <;> linarith [hx.1,hx.2]
      exact (((hasDerivAt_phiTaylor N x).add ((hasDerivAt_phiTaylorTerm N x).const_mul B)).sub
        (hasDerivAt_phi hx')).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Ioo (-1 : ℝ) 1 := by
        simp only [interior_Icc,mem_Ioo] at hx
        constructor <;> linarith [hx.1,hx.2]
      exact (((hasDerivAt_phiTaylorSlope N x).add ((hasDerivAt_phiTaylorTermSlope N x).const_mul B)).sub
        (hasDerivAt_phiSlope hx')).hasDerivWithinAt
    · intro x hx
      have hx0 : x ∈ Ioo (-r) r := by simpa only [interior_Icc] using hx
      have hx' : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx0.1],by linarith [hx0.2]⟩
      have hrpos : 0 < 1-r^2 := by nlinarith
      have hx2 : x^2 ≤ r^2 := by nlinarith [hx0.1,hx0.2]
      have hinv : 1/(1-x^2) ≤ B :=
        one_div_le_one_div_of_le hrpos (by linarith)
      have he : phiTaylorCurvature N x+B*x^(2*N)-1/(1-x^2) =
          x^(2*N)*(B-1/(1-x^2)) := by
        calc
          _ = B*x^(2*N)-(1/(1-x^2)-phiTaylorCurvature N x) := by ring
          _ = _ := by rw [phiTaylorCurvature_remainder N hx']; ring
      rw [he]
      exact mul_nonneg (by rw [pow_mul]; positivity) (sub_nonneg.mpr hinv)
  have hn : -t ∈ Icc (-r) r := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have h := hc.2 ht hn (by norm_num : (0:ℝ)≤1/2) (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)+1/2=1)
  simp only [smul_eq_mul] at h
  rw [show (1/2:ℝ)*t+(1/2)*(-t)=0 by ring] at h
  simp only [F,phi_zero,phiTaylor_zero,phiTaylorTerm_zero,mul_zero,add_zero,
    sub_self,phi_neg,phiTaylor_even,phiTaylorTerm_even] at h
  dsimp [B] at h
  linarith

theorem phiTaylor_eq_sq_base (N : ℕ) (t : ℝ) :
    phiTaylor N t = t^2*phiTaylorBase N (t^2) := by
  unfold phiTaylor phiTaylorBase
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [phiTaylorTerm,pow_add,pow_mul]
  ring

theorem phiTaylorTerm_mul (N : ℕ) (a t : ℝ) :
    phiTaylorTerm N (a*t) =
      t^2*(a^(2*N+2)*(t^2)^N/((2*(N:ℝ)+2)*(2*N+1))) := by
  simp only [phiTaylorTerm,mul_pow,pow_add,pow_mul]
  ring

theorem localTaylorPolynomial_identity (N M : ℕ) (a R L t : ℝ) :
    t^2*localTaylorPolynomial N M a R L (t^2) =
      (a-1)*t^2*L + (1-a*t^2)*phiTaylor N t -
        (1-t^2)*(phiTaylor M (a*t) + (1/(1-(a*R)^2))*phiTaylorTerm M (a*t)) := by
  rw [phiTaylor_eq_sq_base,phiTaylor_eq_sq_base,phiTaylorTerm_mul]
  simp only [mul_pow]
  unfold localTaylorPolynomial
  ring

end
end CK
