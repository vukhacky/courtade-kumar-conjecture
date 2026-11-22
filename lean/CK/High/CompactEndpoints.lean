module

public import CK.High.Compact
public import CK.High.CompactIdentities

/-! The four normalized endpoint margins in the pinned compact verifier
correspond to the convex spectral-cost bounds in `CK.High.Compact`. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section
open Certificate

theorem heightF_ratio_raw_formula {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    heightF u/heightF v = Real.exp (-2*(u-v))*
      (Compact.raw u*Compact.rho v/(Compact.raw v*Compact.rho u)) := by
  have hρu : 0 < Compact.rho u := by rw [compact_scalar_rho]; exact (tanh_mem_Ioo_positive hu).1
  have hρv : 0 < Compact.rho v := by rw [compact_scalar_rho]; exact (tanh_mem_Ioo_positive hv).1
  have he : Real.exp (-2*(u-v))=Compact.q u/Compact.q v := by
    unfold Compact.q
    rw [←Real.exp_sub]
    congr 1
    ring
  rw [←compact_scalar_F u,←compact_scalar_F v,he]
  unfold Compact.F
  field_simp [hρu.ne',hρv.ne',(compact_raw_pos hu).ne',(compact_raw_pos hv).ne',
    (compact_q_pos u).ne',(compact_q_pos v).ne']

theorem log_heightF_raw_formula {v : ℝ} (hv : 0 < v) :
    Real.log (heightF v) = -2*v+Real.log (Compact.raw v)-Real.log (Compact.rho v) := by
  have hρ : 0 < Compact.rho v := by rw [compact_scalar_rho]; exact (tanh_mem_Ioo_positive hv).1
  rw [←compact_scalar_F v,Compact.F,
    Real.log_div (mul_pos (compact_q_pos v) (compact_raw_pos hv)).ne' hρ.ne',
    Real.log_mul (compact_q_pos v).ne' (compact_raw_pos hv).ne']
  simp only [Compact.q,Real.log_exp]

theorem compact_pointHeight_pos {u : ℝ} (hu : (9/4 : ℝ) ≤ u) (kind : Compact.PointKind) :
    0 < Compact.pointHeight u kind := by
  have hd := compact_height_domains hu
  cases kind with
  | low => exact hd.1
  | middle => dsimp [Compact.pointHeight]; linarith only [hu]
  | top => exact hd.1.trans (hd.2.1.trans hd.2.2.1)

theorem compact_sourceDiff_eq (u : ℝ) (kind : Compact.PointKind) (hk : kind ≠ .top) :
    Compact.sourceDiff u kind=u-Compact.pointHeight u kind := by
  cases kind <;> simp [Compact.sourceDiff,Compact.pointHeight,Compact.z] at * <;> ring

theorem compact_sourceA_eq {u : ℝ} (hu : (9/4 : ℝ) ≤ u)
    (kind : Compact.PointKind) (hk : kind ≠ .top) :
    Compact.sourceA u kind=heightF u/heightF (Compact.pointHeight u kind) := by
  have hv := compact_pointHeight_pos hu kind
  have hu0 : 0 < u := by linarith only [hu]
  rw [heightF_ratio_raw_formula hu0 hv,←compact_sourceDiff_eq u kind hk]
  cases kind <;> simp [Compact.sourceA] at *

theorem compact_sourceLog_eq {u : ℝ} (hu : (9/4 : ℝ) ≤ u)
    (kind : Compact.PointKind) (hk : kind ≠ .top) :
    Compact.sourceLog u kind=Real.log (4/(Compact.sourceA u kind)) := by
  have hv := compact_pointHeight_pos hu kind
  have hu0 : 0 < u := by linarith only [hu]
  rw [compact_sourceA_eq hu kind hk,
    Real.log_div (by norm_num) (div_pos (heightF_pos hu0) (heightF_pos hv)).ne',
    Real.log_div (heightF_pos hu0).ne' (heightF_pos hv).ne',
    log_heightF_raw_formula hu0,log_heightF_raw_formula hv]
  unfold Compact.sourceLog
  rw [compact_sourceDiff_eq u kind hk]
  ring

theorem compact_sourceA_top (u : ℝ) : Compact.sourceA u .top=compactUpperCoefficient u := rfl

def arcsineTangentNumerator (c v : ℝ) : ℝ :=
  (1-arcsineRemainderSlope c)*(v-c)+(c-arcsineRemainder c)

theorem compact_arcsine_chord {c : ℝ} (hc : 0 < c) :
    Real.arctan ((Real.exp c-Real.exp (-c))/2)^2*
      (1+Real.exp (-2*c))/(1-Real.exp (-2*c)) = c-arcsineRemainder c := by
  rw [←Real.sinh_eq,arcsineRemainder,arcsin_tanh_eq_arctan_sinh,tanh_eq_heightExpParameter]
  unfold heightExpParameter
  field_simp
  <;> ring

theorem compact_arcsine_constant (c : ℝ) :
    1-(1-Real.arctan ((Real.exp c-Real.exp (-c))/2)/
      ((Real.exp c-Real.exp (-c))/2))^2 = 1-arcsineRemainderSlope c := by
  rw [←Real.sinh_eq]
  rfl

theorem quadraticCoefficientValue_tangent_formula {ρ c Δ₁ Δ₂ a v : ℝ} (hv : 0 < v) :
    quadraticCoefficientValue ρ c Δ₁ Δ₂ a v =
      (ρ*arcsineTangentNumerator c v+
        (Real.pi^2/4)*(Δ₂*(1+a)/2+(Δ₁-Δ₂)*a))/v := by
  unfold quadraticCoefficientValue arcsineTangentNumerator
  field_simp
  ring

theorem logarithmicCoefficientValue_tangent_formula {ρ c Δ₁ Δ₂ a v : ℝ} (hv : 0 < v) :
    logarithmicCoefficientValue ρ c Δ₁ Δ₂ a v =
      (ρ*arcsineTangentNumerator c v+
        (Real.pi^2/4)*(Δ₂*(2*(1-a/4)/Real.log (4/a))+(Δ₁-Δ₂)*a))/v := by
  unfold logarithmicCoefficientValue arcsineTangentNumerator
  field_simp
  ring

def compactClearingFactor (u : ℝ) : ℝ :=
  (1+Compact.t u*Compact.w u)*(1+Compact.w u)*(1+2*Compact.w u)

theorem compactClearingFactor_pos {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    0 < compactClearingFactor u := by
  have hg := compactGamma_pos u
  have ht := (compact_parameter_domains hu).1
  unfold compactClearingFactor
  rw [compact_scalar_t,compact_scalar_w]
  positivity

theorem compact_deltaTwo_cleared {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    compactClearingFactor u*spectralDeltaTwo (compactGamma u) (compactT u) (Real.tanh u) =
      (Compact.t u-2)*Compact.rho u^4*(1+Compact.w u) := by
  have hg := compactGamma_pos u
  have ht := (compact_parameter_domains hu).1
  have hgt : compactGamma u+compactT u ≠ 0 := by linarith
  have hg2 : compactGamma u+2 ≠ 0 := by linarith
  unfold compactClearingFactor spectralDeltaTwo shiftedMultiplier
  rw [compact_scalar_t,compact_scalar_w,compact_scalar_rho]
  field_simp [hg.ne',hgt,hg2]
  ring

theorem compact_deltaDifference_cleared {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    compactClearingFactor u*
      (spectralDeltaOne (compactGamma u) (compactT u) (Real.tanh u)-
        spectralDeltaTwo (compactGamma u) (compactT u) (Real.tanh u)) =
      Compact.rho u^2*(1+Compact.t u*Compact.w u+
        (Compact.t u-2)*Compact.d u*(1+Compact.w u)) := by
  have hg := compactGamma_pos u
  have ht := (compact_parameter_domains hu).1
  have hgt : compactGamma u+compactT u ≠ 0 := by linarith
  have hg1 : compactGamma u+1 ≠ 0 := by linarith
  have hg2 : compactGamma u+2 ≠ 0 := by linarith
  unfold compactClearingFactor spectralDeltaOne spectralDeltaTwo shiftedMultiplier
  rw [compact_scalar_t,compact_scalar_w,compact_scalar_rho,compact_scalar_d]
  field_simp [hg.ne',hgt,hg1,hg2]
  ring

theorem compact_base_cleared {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    (1+Compact.t u*Compact.w u)*compactNumerator u =
      Compact.P*Compact.t u*Compact.rho u^2-
        (Compact.G u+Compact.t u*Compact.q u)*Compact.CS*Compact.psi u := by
  have hg := compactGamma_pos u
  have ht := (compact_parameter_domains hu).1
  have hgt : compactGamma u+compactT u ≠ 0 := by linarith
  rw [compact_scalar_t,compact_scalar_w,compact_scalar_rho,compact_scaled_gamma,
    compact_scalar_CS,compact_scalar_P]
  unfold compactNumerator spectralNumerator shiftedMultiplier
  rw [←compact_scalar_psi]
  field_simp [hg.ne',hgt]

def compactQuadMarginValue (u v A a : ℝ) : ℝ :=
  (v*(1+Compact.w u)*(1+2*Compact.w u)*
      (Compact.P*Compact.t u*Compact.rho u^2-
        (Compact.G u+Compact.t u*Compact.q u)*Compact.CS*Compact.psi u)-
    u*Compact.rho u*(1+Compact.t u*Compact.w u)*(1+Compact.w u)*(1+2*Compact.w u)*A)-
  u*Compact.P*Compact.rho u^2*
      (1+Compact.t u*Compact.w u+(Compact.t u-2)*Compact.d u*(1+Compact.w u))*a-
  (u*Compact.P*(Compact.t u-2)*Compact.rho u^4*(1+Compact.w u))*(1+a)/2

def compactLogMarginValue (u v A a L : ℝ) : ℝ :=
  ((v*(1+Compact.w u)*(1+2*Compact.w u)*
      (Compact.P*Compact.t u*Compact.rho u^2-
        (Compact.G u+Compact.t u*Compact.q u)*Compact.CS*Compact.psi u)-
    u*Compact.rho u*(1+Compact.t u*Compact.w u)*(1+Compact.w u)*(1+2*Compact.w u)*A)-
  u*Compact.P*Compact.rho u^2*
      (1+Compact.t u*Compact.w u+(Compact.t u-2)*Compact.d u*(1+Compact.w u))*a)*L-
  (u*Compact.P*(Compact.t u-2)*Compact.rho u^4*(1+Compact.w u))*2*(1-a/4)

theorem compactQuadMarginValue_factorization {u v A a : ℝ}
    (hu : (9/4 : ℝ) ≤ u) (hv : 0 < v) :
    compactQuadMarginValue u v A a =
      u*v*compactClearingFactor u*(compactNumerator u/u-
        (Real.tanh u*A+(Real.pi^2/4)*
          (spectralDeltaTwo (compactGamma u) (compactT u) (Real.tanh u)*(1+a)/2+
            (spectralDeltaOne (compactGamma u) (compactT u) (Real.tanh u)-
              spectralDeltaTwo (compactGamma u) (compactT u) (Real.tanh u))*a))/v) := by
  have hu0 : 0 < u := by linarith only [hu]
  have hbase := compact_base_cleared hu
  have htwo := compact_deltaTwo_cleared hu
  have hdiff := compact_deltaDifference_cleared hu
  have hfirst : v*(1+Compact.w u)*(1+2*Compact.w u)*
      (Compact.P*Compact.t u*Compact.rho u^2-
        (Compact.G u+Compact.t u*Compact.q u)*Compact.CS*Compact.psi u)=
      v*compactClearingFactor u*compactNumerator u := by
    rw [←hbase]
    unfold compactClearingFactor
    ring
  have ha' : u*Compact.P*Compact.rho u^2*
      (1+Compact.t u*Compact.w u+(Compact.t u-2)*Compact.d u*(1+Compact.w u))*a =
      u*Compact.P*(compactClearingFactor u*
        (spectralDeltaOne (compactGamma u) (compactT u) (Real.tanh u)-
          spectralDeltaTwo (compactGamma u) (compactT u) (Real.tanh u)))*a := by
    rw [hdiff]
    ring
  have ht' : u*Compact.P*(Compact.t u-2)*Compact.rho u^4*(1+Compact.w u)=
      u*Compact.P*(compactClearingFactor u*
        spectralDeltaTwo (compactGamma u) (compactT u) (Real.tanh u)) := by
    rw [htwo]
    ring
  unfold compactQuadMarginValue
  rw [hfirst,ha',ht',compact_scalar_rho,compact_scalar_P]
  unfold compactClearingFactor
  field_simp
  ring

theorem compactLogMarginValue_factorization {u v A a L : ℝ}
    (hu : (9/4 : ℝ) ≤ u) (hv : 0 < v) (hL : L ≠ 0) :
    compactLogMarginValue u v A a L =
      u*v*compactClearingFactor u*L*(compactNumerator u/u-
        (Real.tanh u*A+(Real.pi^2/4)*
          (spectralDeltaTwo (compactGamma u) (compactT u) (Real.tanh u)*(2*(1-a/4)/L)+
            (spectralDeltaOne (compactGamma u) (compactT u) (Real.tanh u)-
              spectralDeltaTwo (compactGamma u) (compactT u) (Real.tanh u))*a))/v) := by
  have hu0 : 0 < u := by linarith only [hu]
  have hbase := compact_base_cleared hu
  have htwo := compact_deltaTwo_cleared hu
  have hdiff := compact_deltaDifference_cleared hu
  have hfirst : v*(1+Compact.w u)*(1+2*Compact.w u)*
      (Compact.P*Compact.t u*Compact.rho u^2-
        (Compact.G u+Compact.t u*Compact.q u)*Compact.CS*Compact.psi u)=
      v*compactClearingFactor u*compactNumerator u := by
    rw [←hbase]
    unfold compactClearingFactor
    ring
  have ha' : u*Compact.P*Compact.rho u^2*
      (1+Compact.t u*Compact.w u+(Compact.t u-2)*Compact.d u*(1+Compact.w u))*a =
      u*Compact.P*(compactClearingFactor u*
        (spectralDeltaOne (compactGamma u) (compactT u) (Real.tanh u)-
          spectralDeltaTwo (compactGamma u) (compactT u) (Real.tanh u)))*a := by
    rw [hdiff]
    ring
  have ht' : u*Compact.P*(Compact.t u-2)*Compact.rho u^4*(1+Compact.w u)=
      u*Compact.P*(compactClearingFactor u*
        spectralDeltaTwo (compactGamma u) (compactT u) (Real.tanh u)) := by
    rw [htwo]
    ring
  unfold compactLogMarginValue
  rw [hfirst,ha',ht',compact_scalar_rho,compact_scalar_P]
  unfold compactClearingFactor
  field_simp
  ring

theorem compact_pointHeight_le {u : ℝ} (hu : (9/4 : ℝ) ≤ u) (kind : Compact.PointKind) :
    Compact.pointHeight u kind ≤ u := by
  have hd := compact_height_domains hu
  cases kind with
  | low => exact (hd.2.1.trans hd.2.2.1).le.trans hd.2.2.2
  | middle => exact hd.2.2.1.le.trans hd.2.2.2
  | top => exact hd.2.2.2

theorem compact_sourceA_mem {u : ℝ} (hu : (9/4 : ℝ) ≤ u)
    (kind : Compact.PointKind) (hk : kind ≠ .top) : Compact.sourceA u kind ∈ Ioc (0 : ℝ) 1 := by
  rw [compact_sourceA_eq hu kind hk]
  exact heightF_ratio_mem_Ioc (by linarith only [hu])
    (compact_pointHeight_pos hu kind) (compact_pointHeight_le hu kind)

theorem compact_sourceLog_pos {u : ℝ} (hu : (9/4 : ℝ) ≤ u)
    (kind : Compact.PointKind) (hk : kind ≠ .top) : 0 < Compact.sourceLog u kind := by
  rw [compact_sourceLog_eq hu kind hk]
  exact influence_log_pos (compact_sourceA_mem hu kind hk)

theorem compact_log_margin_value {u : ℝ} (hu : (9/4 : ℝ) ≤ u)
    (kind : Compact.PointKind) (hk : kind ≠ .top) :
    Compact.endpointMargin u .logarithmic kind =
      compactLogMarginValue u (Compact.pointHeight u kind)
        (arcsineTangentNumerator (compactZ u) (Compact.pointHeight u kind))
        (Compact.sourceA u kind) (Compact.sourceLog u kind) := by
  have hz := (compact_height_domains hu).1
  cases kind with
  | low =>
      simp only [Compact.endpointMargin,Compact.pointHeight,compact_scalar_z]
      rw [compact_arcsine_chord hz]
      unfold compactLogMarginValue arcsineTangentNumerator
      ring
  | middle =>
      simp only [Compact.endpointMargin,Compact.pointHeight,compact_scalar_z]
      rw [compact_arcsine_chord hz,compact_arcsine_constant]
      rfl
  | top => exact (hk rfl).elim

theorem compact_quad_margin_value {u : ℝ} (hu : (9/4 : ℝ) ≤ u)
    (kind : Compact.PointKind) (hk : kind ≠ .low) :
    Compact.endpointMargin u .quadratic kind =
      compactQuadMarginValue u (Compact.pointHeight u kind)
        (arcsineTangentNumerator (compactTop u) (Compact.pointHeight u kind))
        (Compact.sourceA u kind) := by
  have ht := compact_pointHeight_pos hu .top
  change 0 < compactTop u at ht
  cases kind with
  | low => exact (hk rfl).elim
  | middle =>
      simp only [Compact.endpointMargin,Compact.pointHeight,compact_scalar_top]
      rw [compact_arcsine_chord ht,compact_arcsine_constant]
      rfl
  | top =>
      simp only [Compact.endpointMargin,Compact.pointHeight,compact_scalar_top]
      rw [compact_arcsine_chord ht]
      unfold compactQuadMarginValue arcsineTangentNumerator
      ring

theorem compact_log_endpoint_of_margin {u : ℝ} (hu : (9/4 : ℝ) ≤ u)
    (kind : Compact.PointKind) (hk : kind ≠ .top)
    (hmargin : 0 < Compact.endpointMargin u .logarithmic kind) :
    logarithmicCoefficientValue (Real.tanh u) (compactZ u)
      (spectralDeltaOne (compactGamma u) (compactT u) (Real.tanh u))
      (spectralDeltaTwo (compactGamma u) (compactT u) (Real.tanh u))
        (Compact.sourceA u kind) (Compact.pointHeight u kind) < compactNumerator u/u := by
  have hu0 : 0 < u := by linarith only [hu]
  have hv := compact_pointHeight_pos hu kind
  have hL := compact_sourceLog_pos hu kind hk
  rw [compact_log_margin_value hu kind hk,compactLogMarginValue_factorization hu hv hL.ne',
    compact_sourceLog_eq hu kind hk,←logarithmicCoefficientValue_tangent_formula hv] at hmargin
  have hLp : 0 < Real.log (4/Compact.sourceA u kind) := influence_log_pos (compact_sourceA_mem hu kind hk)
  have hp : 0 < u*Compact.pointHeight u kind*compactClearingFactor u*
      Real.log (4/Compact.sourceA u kind) :=
    mul_pos (mul_pos (mul_pos hu0 hv) (compactClearingFactor_pos hu)) hLp
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hp).mp hmargin)

theorem compact_quad_endpoint_of_margin {u : ℝ} (hu : (9/4 : ℝ) ≤ u)
    (kind : Compact.PointKind) (hk : kind ≠ .low)
    (hmargin : 0 < Compact.endpointMargin u .quadratic kind) :
    quadraticCoefficientValue (Real.tanh u) (compactTop u)
      (spectralDeltaOne (compactGamma u) (compactT u) (Real.tanh u))
      (spectralDeltaTwo (compactGamma u) (compactT u) (Real.tanh u))
        (Compact.sourceA u kind) (Compact.pointHeight u kind) < compactNumerator u/u := by
  have hu0 : 0 < u := by linarith only [hu]
  have hv := compact_pointHeight_pos hu kind
  rw [compact_quad_margin_value hu kind hk,compactQuadMarginValue_factorization hu hv,
    ←quadraticCoefficientValue_tangent_formula hv] at hmargin
  have hp : 0 < u*Compact.pointHeight u kind*compactClearingFactor u :=
    mul_pos (mul_pos hu0 hv) (compactClearingFactor_pos hu)
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hp).mp hmargin)

theorem compact_logLow_of_margin {u : ℝ} (hu : (9/4 : ℝ) ≤ u)
    (hmargin : 0 < Compact.lowerLogMargin u) : compactLogLow u < compactNumerator u/u := by
  have h := compact_log_endpoint_of_margin hu .low (by decide) hmargin
  rw [compact_sourceA_eq hu .low (by decide)] at h
  have hz : 0 < compactZ u := (compact_height_domains hu).1
  have hzu : compactZ u ≤ u := compact_pointHeight_le hu .low
  unfold compactLogLow
  rw [logarithmicTangentMajorant_eq_coefficient (heightF_pos (by linarith only [hu]))
    hz (heightF_ratio_mem_Ioc (by linarith only [hu]) hz hzu).2]
  simpa only [Compact.pointHeight,compact_scalar_z] using h

theorem compact_logMiddle_of_margin {u : ℝ} (hu : (9/4 : ℝ) ≤ u)
    (hmargin : 0 < Compact.middleLogMargin u) : compactLogMiddle u < compactNumerator u/u := by
  have h := compact_log_endpoint_of_margin hu .middle (by decide) hmargin
  rw [compact_sourceA_eq hu .middle (by decide)] at h
  have hv : 0 < 2*u/3 := by linarith only [hu]
  have hvu : 2*u/3 ≤ u := by linarith only [hu]
  unfold compactLogMiddle
  rw [logarithmicTangentMajorant_eq_coefficient (heightF_pos (by linarith only [hu]))
    hv (heightF_ratio_mem_Ioc (by linarith only [hu]) hv hvu).2]
  simpa only [Compact.pointHeight] using h

theorem compact_quadMiddle_of_margin {u : ℝ} (hu : (9/4 : ℝ) ≤ u)
    (hmargin : 0 < Compact.middleQuadMargin u) : compactQuadMiddle u < compactNumerator u/u := by
  have h := compact_quad_endpoint_of_margin hu .middle (by decide) hmargin
  rw [compact_sourceA_eq hu .middle (by decide)] at h
  unfold compactQuadMiddle
  rw [quadraticTangentMajorant_eq_coefficient]
  exact h

theorem compact_quadTop_of_margin {u : ℝ} (hu : (9/4 : ℝ) ≤ u)
    (hmargin : 0 < Compact.upperQuadMargin u) : compactQuadTop u < compactNumerator u/u := by
  exact compact_quad_endpoint_of_margin hu .top (by decide) hmargin

end
end CK
