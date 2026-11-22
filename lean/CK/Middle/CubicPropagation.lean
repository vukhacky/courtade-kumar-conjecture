module

public import CK.Middle.CubicScalar
public import CK.Certificate.CubicCurvature

/-! Uniform cubic endpoint propagation. The algebraic curvature bounds are
certified on a complete two-dimensional rectangle; logarithm remainders and
entropy derivatives are proved analytically. No finite sampling is used. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section
namespace CubicAnalysis
open Certificate.CubicCurvature

def V (M x : ℝ) : ℝ := N x/C M x
def V1 (M x : ℝ) : ℝ := D1 M x/(C M x)^2
def V2 (M x : ℝ) : ℝ := D2 M x/(C M x)^3

def F (M x : ℝ) : ℝ := cubicEntropyQuotient x*V M x
def F1 (M x : ℝ) : ℝ := cubicEntropyQuotientSlope x*V M x+cubicEntropyQuotient x*V1 M x
def F2 (M x : ℝ) : ℝ := cubicEntropyQuotientCurvature x*V M x+
  2*cubicEntropyQuotientSlope x*V1 M x+cubicEntropyQuotient x*V2 M x

def K (M x : ℝ) : ℝ := cubicEntropyQuotient x/C M x
def K1 (M x : ℝ) : ℝ := (cubicEntropyQuotientSlope x*C M x-
  cubicEntropyQuotient x*C1 M x)/(C M x)^2
def K2 (M x : ℝ) : ℝ := (cubicEntropyQuotientCurvature x*(C M x)^2-
  2*cubicEntropyQuotientSlope x*C M x*C1 M x+
  cubicEntropyQuotient x*(2*(C1 M x)^2-C M x*C2 M x))/(C M x)^3

theorem C_pos {M x : ℝ} (hM : M ∈ Icc (3/4 : ℝ) (83/100))
    (hx : x ∈ Icc (0 : ℝ) (43/500)) : 0 < C M x := by
  have h := (bounds hM hx).1
  linarith

theorem C1_nonneg {M x : ℝ} (hM : M ∈ Icc (3/4 : ℝ) (83/100))
    (hx : x ∈ Icc (0 : ℝ) (43/500)) : 0 ≤ C1 M x := by
  have h1 : 0 ≤ 5-8*x+3*x^2 := by nlinarith [hx.2,sq_nonneg x]
  have h2 := mul_nonneg (sub_nonneg.mpr hM.1) h1
  unfold C1
  nlinarith [hx.2,sq_nonneg x]

theorem C2_nonpos {M x : ℝ} (hM : M ∈ Icc (3/4 : ℝ) (83/100))
    (hx : x ∈ Icc (0 : ℝ) (43/500)) : C2 M x ≤ 0 := by
  have h1 : 6*x-8 ≤ 0 := by linarith [hx.2]
  have h2 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hM.1) h1
  unfold C2
  nlinarith only [h2,hx.2]

theorem hasDerivAt_C (M x : ℝ) : HasDerivAt (C M) (C1 M x) x := by
  have h := (((hasDerivAt_id x).const_mul (-3+5*M)).const_add (3-2*M) |>.add
    ((hasDerivAt_pow 2 x).const_mul (1-4*M))).add ((hasDerivAt_pow 3 x).const_mul M)
  exact h.congr_deriv (by norm_num [C1]; ring)

theorem hasDerivAt_C1 (M x : ℝ) : HasDerivAt (C1 M) (C2 M x) x := by
  have h := (((hasDerivAt_id x).const_mul (2*(1-4*M))).const_add (-3+5*M)).add
    ((hasDerivAt_pow 2 x).const_mul (3*M))
  exact h.congr_deriv (by norm_num [C2]; ring)

theorem hasDerivAt_N (x : ℝ) : HasDerivAt N (N1 x) x := by
  have h := ((((hasDerivAt_id x).const_mul 3).const_add (1/2)).sub
    ((hasDerivAt_pow 2 x).const_mul 3)).add (hasDerivAt_pow 3 x)
  exact h.congr_deriv (by norm_num [N1]; ring)

theorem hasDerivAt_N1 (x : ℝ) : HasDerivAt N1 (N2 x) x := by
  have h := (((hasDerivAt_id x).const_mul 6).const_sub 3).add
    ((hasDerivAt_pow 2 x).const_mul 3)
  exact h.congr_deriv (by norm_num [N2]; ring)

theorem hasDerivAt_V {M x : ℝ} (hC : C M x ≠ 0) : HasDerivAt (V M) (V1 M x) x := by
  exact ((hasDerivAt_N x).div (hasDerivAt_C M x) hC).congr_deriv (by
    unfold V1 D1
    ring)

theorem hasDerivAt_D1 (M x : ℝ) :
    HasDerivAt (D1 M) (N2 x*C M x-N x*C2 M x) x := by
  have h := ((hasDerivAt_N1 x).mul (hasDerivAt_C M x)).sub
    ((hasDerivAt_N x).mul (hasDerivAt_C1 M x))
  exact h.congr_deriv (by ring)

theorem hasDerivAt_V1 {M x : ℝ} (hC : C M x ≠ 0) : HasDerivAt (V1 M) (V2 M x) x := by
  have h := (hasDerivAt_D1 M x).div ((hasDerivAt_C M x).pow 2) (pow_ne_zero 2 hC)
  apply h.congr_deriv
  unfold V2 D2
  norm_num
  field_simp

theorem V_bounds {M x : ℝ} (hM : M ∈ Icc (3/4 : ℝ) (83/100))
    (hx : x ∈ Icc (0 : ℝ) (43/500)) :
    0 ≤ V M x ∧ V M x ≤ 3/5 ∧ V1 M x ≤ 2 ∧
    -7+30*x ≤ V2 M x ∧ V2 M x ≤ 0 ∧ 1/3-2*x ≤ V M x-2*x*V1 M x := by
  obtain ⟨_,_,hN0,hNu,hD1,hD2l,hD2u,hVD⟩ := bounds hM hx
  have hC := C_pos hM hx
  refine ⟨div_nonneg hN0 hC.le, (div_le_iff₀ hC).mpr hNu,
    (div_le_iff₀ (sq_pos_of_pos hC)).mpr hD1,
    (le_div_iff₀ (pow_pos hC 3)).mpr hD2l,div_nonpos_of_nonpos_of_nonneg hD2u (pow_nonneg hC.le 3),?_⟩
  have hid : V M x-2*x*V1 M x = (N x*C M x-2*x*D1 M x)/(C M x)^2 := by
    unfold V V1
    field_simp
  rw [hid]
  exact (le_div_iff₀ (sq_pos_of_pos hC)).mpr hVD

theorem hasDerivAt_F {M x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 2) (hC : C M x ≠ 0) :
    HasDerivAt (F M) (F1 M x) x :=
  (hasDerivAt_cubicEntropyQuotient hx).mul (hasDerivAt_V hC)

theorem hasDerivAt_F1 {M x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 2) (hC : C M x ≠ 0) :
    HasDerivAt (F1 M) (F2 M x) x := by
  have h := ((hasDerivAt_cubicEntropyQuotientSlope hx).mul (hasDerivAt_V hC)).add
    ((hasDerivAt_cubicEntropyQuotient hx).mul (hasDerivAt_V1 hC))
  exact h.congr_deriv (by unfold F2; ring)

theorem F2_scaled_identity (M : ℝ) {x : ℝ} (hx : x ≠ 0) :
    2*x^2*F2 M x = V M x-2*x*V1 M x+2*x*signEntropy (1-x)*V2 M x-
      4*x^2*cubicLogRemainderSlope x*V1 M x-2*x^2*cubicLogRemainderCurvature x*V M x := by
  unfold F2 cubicLogRemainderSlope cubicLogRemainderCurvature cubicEntropyQuotient
  field_simp
  ring

theorem F2_pos {M x : ℝ} (hM : M ∈ Icc (3/4 : ℝ) (83/100))
    (hx : x ∈ Ioc (0 : ℝ) (43/500)) : 0 < F2 M x := by
  obtain ⟨hV0,hVu,hV1,hV2,_,hVD⟩ := V_bounds hM ⟨hx.1.le,hx.2⟩
  have hH0 := signEntropy_nonneg (show 1-x ∈ Icc (-1 : ℝ) 1 from
    ⟨by linarith [hx.2],by linarith [hx.1]⟩)
  have hH := signEntropy_le_cubic_endpoint (show 1-x ∈ Icc (457/500 : ℝ) 1 from
    ⟨by linarith [hx.2],by linarith [hx.1]⟩)
  have hx0 : 0 ≤ x := hx.1.le
  have hB1 := mul_le_mul_of_nonneg_left hV2 (show 0 ≤ 2*x*signEntropy (1-x) by positivity)
  have hB2 := mul_le_mul_of_nonpos_left hH (show 2*x*(-7+30*x) ≤ 0 by
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith [hx.2]))
  have hr1 := cubicLogRemainderSlope_le hx
  have hr10 := cubicLogRemainderSlope_nonneg hx
  have hr2 := cubicLogRemainderCurvature_le hx
  have hR1 := mul_le_mul_of_nonneg_left hV1 hr10
  have hR1' : cubicLogRemainderSlope x*V1 M x ≤ 26/100 := by nlinarith only [hR1,hr1]
  have hR1s := mul_le_mul_of_nonneg_left hR1' (show 0 ≤ 4*x^2 by positivity)
  have hR2 := mul_le_mul_of_nonneg_right hr2 hV0
  have hR2' : cubicLogRemainderCurvature x*V M x ≤ 3/100 := by nlinarith only [hR2,hVu]
  have hR2s := mul_le_mul_of_nonneg_left hR2' (show 0 ≤ 2*x^2 by positivity)
  have hpoly : 0 < (1/3 : ℝ)-(113/25)*x+(97/10)*x^2 := by
    have hm := mul_nonneg (show 0 ≤ 43/500-x by linarith [hx.2])
      (show 0 ≤ 113/25-(97/10)*(x+43/500) by linarith [hx.2])
    nlinarith only [hm]
  have hid := F2_scaled_identity M hx.1.ne'
  have hscaled : 0 < 2*x^2*F2 M x := by
    nlinarith only [hid,hVD,hB1,hB2,hR1s,hR2s,hpoly]
  exact pos_of_mul_pos_right hscaled (by positivity)

theorem hasDerivAt_K {M x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 2) (hC : C M x ≠ 0) :
    HasDerivAt (K M) (K1 M x) x :=
  (hasDerivAt_cubicEntropyQuotient hx).div (hasDerivAt_C M x) hC

theorem hasDerivAt_K1 {M x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 2) (hC : C M x ≠ 0) :
    HasDerivAt (K1 M) (K2 M x) x := by
  have h := (((hasDerivAt_cubicEntropyQuotientSlope hx).mul (hasDerivAt_C M x)).sub
    ((hasDerivAt_cubicEntropyQuotient hx).mul (hasDerivAt_C1 M x))).div
    ((hasDerivAt_C M x).pow 2) (pow_ne_zero 2 hC)
  apply h.congr_deriv
  unfold K2
  norm_num
  field_simp
  ring

theorem K2_nonneg {M x : ℝ} (hM : M ∈ Icc (3/4 : ℝ) (83/100))
    (hx : x ∈ Ioc (0 : ℝ) (43/500)) : 0 ≤ K2 M x := by
  have hC := C_pos hM ⟨hx.1.le,hx.2⟩
  have hC1 := C1_nonneg hM ⟨hx.1.le,hx.2⟩
  have hC2 := C2_nonpos hM ⟨hx.1.le,hx.2⟩
  have hL := cubicEntropyQuotient_nonneg hx
  have hL1 := cubicEntropyQuotientSlope_nonpos hx
  have hL2 := cubicEntropyQuotientCurvature_nonneg hx
  apply div_nonneg ?_ (pow_nonneg hC.le 3)
  have h0 := mul_nonneg hL2 (sq_nonneg (C M x))
  have h1 := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg hL1 hC.le) hC1
  have h2 := mul_nonneg hL (show 0 ≤ 2*(C1 M x)^2-C M x*C2 M x by
    have hcc := mul_nonpos_of_nonneg_of_nonpos hC.le hC2
    nlinarith [sq_nonneg (C1 M x)])
  nlinarith only [h0,h1,h2]

theorem convexOn_F {M : ℝ} (hM : M ∈ Icc (3/4 : ℝ) (83/100)) :
    ConvexOn ℝ (Ioc (0 : ℝ) (43/500)) (F M) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := F1 M) (f'' := F2 M) (convex_Ioc _ _)
  · intro x hx
    exact (hasDerivAt_F ⟨hx.1,by linarith [hx.2]⟩
      (C_pos hM ⟨hx.1.le,hx.2⟩).ne').continuousAt.continuousWithinAt
  · intro x hx
    have h : x ∈ Ioo (0 : ℝ) (43/500) := by simpa using hx
    exact (hasDerivAt_F ⟨h.1,by linarith [h.2]⟩ (C_pos hM ⟨h.1.le,h.2.le⟩).ne').hasDerivWithinAt
  · intro x hx
    have h : x ∈ Ioo (0 : ℝ) (43/500) := by simpa using hx
    exact (hasDerivAt_F1 ⟨h.1,by linarith [h.2]⟩ (C_pos hM ⟨h.1.le,h.2.le⟩).ne').hasDerivWithinAt
  · intro x hx
    have h : x ∈ Ioo (0 : ℝ) (43/500) := by simpa using hx
    exact (F2_pos hM ⟨h.1,h.2.le⟩).le

theorem convexOn_K {M : ℝ} (hM : M ∈ Icc (3/4 : ℝ) (83/100)) :
    ConvexOn ℝ (Ioc (0 : ℝ) (43/500)) (K M) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := K1 M) (f'' := K2 M) (convex_Ioc _ _)
  · intro x hx
    exact (hasDerivAt_K ⟨hx.1,by linarith [hx.2]⟩
      (C_pos hM ⟨hx.1.le,hx.2⟩).ne').continuousAt.continuousWithinAt
  · intro x hx
    have h : x ∈ Ioo (0 : ℝ) (43/500) := by simpa using hx
    exact (hasDerivAt_K ⟨h.1,by linarith [h.2]⟩ (C_pos hM ⟨h.1.le,h.2.le⟩).ne').hasDerivWithinAt
  · intro x hx
    have h : x ∈ Ioo (0 : ℝ) (43/500) := by simpa using hx
    exact (hasDerivAt_K1 ⟨h.1,by linarith [h.2]⟩ (C_pos hM ⟨h.1.le,h.2.le⟩).ne').hasDerivWithinAt
  · intro x hx
    have h : x ∈ Ioo (0 : ℝ) (43/500) := by simpa using hx
    exact K2_nonneg hM ⟨h.1,h.2.le⟩

end CubicAnalysis

theorem cubicC_eq_reversed (ρ M : ℝ) :
    cubicC ρ M = Certificate.CubicCurvature.C M (1-ρ) := by
  unfold cubicC Certificate.CubicCurvature.C
  ring

theorem cubicKappa_eq_reversed (ρ M : ℝ) :
    cubicKappa ρ M = CubicAnalysis.K M (1-ρ) := by
  unfold cubicKappa CubicAnalysis.K cubicEntropyQuotient
  rw [show 1-(1-ρ)=ρ by ring,div_div,cubicC_eq_reversed]

theorem cubicC_pos {ρ M : ℝ} (hM : M ∈ Icc (3/4 : ℝ) (83/100))
    (hρ : ρ ∈ Icc (457/500 : ℝ) 1) : 0 < cubicC ρ M := by
  rw [cubicC_eq_reversed]
  exact CubicAnalysis.C_pos hM ⟨by linarith [hρ.2],by linarith [hρ.1]⟩

theorem cubicKappa_lower {ρ M : ℝ} (hM : M ∈ Icc (3/4 : ℝ) (83/100))
    (hρ : ρ ∈ Ico (457/500 : ℝ) 1) : 5/4 ≤ cubicKappa ρ M := by
  have hx : 1-ρ ∈ Ioc (0 : ℝ) (43/500) := ⟨by linarith [hρ.2],by linarith [hρ.1]⟩
  have hC := CubicAnalysis.C_pos hM ⟨hx.1.le,hx.2⟩
  have hCupper := (Certificate.CubicCurvature.bounds hM ⟨hx.1.le,hx.2⟩).2.1
  have hL := cubicEntropyQuotient_ge_two hx
  rw [cubicKappa_eq_reversed,CubicAnalysis.K]
  apply (le_div_iff₀ hC).mpr
  linarith

theorem cubicKappa_prior_credit {ρ M : ℝ} (hM : M ∈ Icc (3/4 : ℝ) (83/100))
    (hρ : ρ ∈ Ico (457/500 : ℝ) 1) : cubicKappa ρ M*(1-ρ^3) < 1/2 := by
  have hC := cubicC_pos hM ⟨hρ.1,hρ.2.le⟩
  have hClow : (67/50 : ℝ) ≤ cubicC ρ M := by
    rw [cubicC_eq_reversed]
    exact (Certificate.CubicCurvature.bounds hM
      ⟨by linarith [hρ.2],by linarith [hρ.1]⟩).1
  have hH := signEntropy_le_cubic_endpoint ⟨hρ.1,hρ.2.le⟩
  have hH0 := signEntropy_nonneg (show ρ ∈ Icc (-1 : ℝ) 1 from
    ⟨by linarith [hρ.1],hρ.2.le⟩)
  have hρ0 : 0 ≤ ρ := by linarith [hρ.1]
  have hnum : 1+ρ+ρ^2 ≤ 3 := by nlinarith [hρ.2]
  have hmul := mul_le_mul_of_nonneg_left hnum hH0
  have hid : cubicKappa ρ M*(1-ρ^3) = signEntropy ρ*(1+ρ+ρ^2)/cubicC ρ M := by
    unfold cubicKappa
    field_simp [show 1-ρ ≠ 0 by linarith [hρ.2]]
    ring
  rw [hid]
  apply (div_lt_iff₀ hC).mpr
  nlinarith only [hmul,hH,hClow]

theorem cubicGate_reversed_identity (ρ M t : ℝ) :
    (1-t)*(CubicAnalysis.F M (1-ρ)+(t-1/2)*CubicAnalysis.K M (1-ρ)) =
      cubicKappa ρ M*(1-t)*(1+t-ρ^3) := by
  rw [cubicKappa_eq_reversed]
  unfold CubicAnalysis.F CubicAnalysis.V CubicAnalysis.K
  have hN : Certificate.CubicCurvature.N (1-ρ) = 3/2-ρ^3 := by
    unfold Certificate.CubicCurvature.N
    ring
  rw [hN]
  ring

theorem energyChi_nonpos_of_gate {c b t : ℝ} (ht : t < 1)
    (hg : c*(1-t)*(1+t-b) ≤ signEntropy t) : energyChi c b t ≤ 0 := by
  have hd : 0 < 1-t := by linarith
  have h : c*(1+t-b) ≤ signEntropy t/(1-t) :=
    (le_div_iff₀ hd).mpr (by nlinarith only [hg])
  unfold energyChi
  simp only [mul_div_assoc,neg_div]
  linarith

theorem gate_of_energyChi_nonpos {c b t : ℝ} (ht : t < 1)
    (hc : energyChi c b t ≤ 0) : c*(1-t)*(1+t-b) ≤ signEntropy t := by
  have hm := mul_nonpos_of_nonpos_of_nonneg hc (show 0 ≤ 1-t by linarith)
  have hid : energyChi c b t*(1-t) = -2*signEntropy t+2*c*(1+t-b)*(1-t) := by
    unfold energyChi
    field_simp [show 1-t ≠ 0 by linarith]
  rw [hid] at hm
  nlinarith only [hm]

/-- The source cubic endpoint-propagation lemma on its full parameter range.
The endpoint gates may use distinct supporting tangents. -/
theorem cubic_entropy_gate_of_endpoints {M lo hi ρ : ℝ}
    (hM : M ∈ Icc (3/4 : ℝ) (83/100)) (hlo : (457/500 : ℝ) ≤ lo) (hhi : hi < 1)
    (hρ : ρ ∈ Icc lo hi)
    (hgateLo : ∀ t ∈ Icc (0 : ℝ) 1, cubicKappa lo M*(1-t)*(1+t-lo^3) ≤ signEntropy t)
    (hgateHi : ∀ t ∈ Icc (0 : ℝ) 1, cubicKappa hi M*(1-t)*(1+t-hi^3) ≤ signEntropy t) :
    ∀ t ∈ Icc (0 : ℝ) 1, cubicKappa ρ M*(1-t)*(1+t-ρ^3) ≤ signEntropy t := by
  have hlohi : lo ≤ hi := hρ.1.trans hρ.2
  have hρdom : ρ ∈ Ico (457/500 : ℝ) 1 := ⟨hlo.trans hρ.1,hρ.2.trans_lt hhi⟩
  have highGate (t : ℝ) (ht : t ∈ Icc (1/2 : ℝ) 1) :
      cubicKappa ρ M*(1-t)*(1+t-ρ^3) ≤ signEntropy t := by
    have hs : ConvexOn ℝ (Ioc (0 : ℝ) (43/500))
        (fun x => (1-t)*(CubicAnalysis.F M x+(t-1/2)*CubicAnalysis.K M x)) := by
      refine ⟨convex_Ioc _ _, ?_⟩
      intro x hx y hy a b ha hb hab
      have hF := (CubicAnalysis.convexOn_F hM).2 hx hy ha hb hab
      have hK := (CubicAnalysis.convexOn_K hM).2 hx hy ha hb hab
      simp only [smul_eq_mul] at hF hK ⊢
      have hKm := mul_le_mul_of_nonneg_left hK (sub_nonneg.mpr ht.1)
      have hsum := add_le_add hF hKm
      have hmul := mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr ht.2)
      nlinarith only [hmul]
    have h := hs.le_max_of_mem_Icc
      (show 1-hi ∈ Ioc (0 : ℝ) (43/500) from ⟨by linarith,by linarith⟩)
      (show 1-lo ∈ Ioc (0 : ℝ) (43/500) from ⟨by linarith,by linarith⟩)
      (show 1-ρ ∈ Icc (1-hi) (1-lo) from ⟨by linarith [hρ.2],by linarith [hρ.1]⟩)
    simp only [smul_eq_mul,cubicGate_reversed_identity] at h
    exact h.trans (max_le (hgateHi t ⟨by linarith [ht.1],ht.2⟩)
      (hgateLo t ⟨by linarith [ht.1],ht.2⟩))
  intro t ht
  by_cases hhalf : (1/2 : ℝ) ≤ t
  · exact highGate t ⟨hhalf,ht.2⟩
  · have hmid := highGate (1/2) (by norm_num)
    have hchi := energyChi_nonpos_of_gate (by norm_num : (1/2 : ℝ) < 1) hmid
    have hκ := cubicKappa_lower hM hρdom
    have hslope : 0 ≤ energyChiSlope (cubicKappa ρ M) (1/2) := by
      rw [energyChiSlope_eq]
      norm_num
      linarith [log_three_fourths_lower]
    have ht1 : t < 1 := by linarith [lt_of_not_ge hhalf]
    have htan := energyChi_le_tangent (cubicKappa ρ M) (ρ^3)
      (show (1/2 : ℝ) ∈ Ioo (0 : ℝ) 1 by norm_num) (show t ∈ Ico (0 : ℝ) 1 from ⟨ht.1,ht1⟩)
    have hm := mul_nonpos_of_nonpos_of_nonneg (show t-1/2 ≤ 0 by linarith [lt_of_not_ge hhalf]) hslope
    apply gate_of_energyChi_nonpos ht1
    linarith only [htan,hchi,hm]

end
end CK
