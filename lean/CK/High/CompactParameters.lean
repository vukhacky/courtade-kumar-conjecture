module

public import CK.High.TailNumerator
public import CK.High.CostGeometryBase

/-! Analytic admissibility and mean compensation for the single compact
parameter rule from the STOC source. Every estimate holds on a whole half-line. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

def compactZ (u : ℝ) : ℝ := Real.log u+u/25-2/5
def compactT (u : ℝ) : ℝ := 49*u/100+7/5
def compactGamma (u : ℝ) : ℝ := Real.exp (49*u/50-1/5)/2+Real.exp (9*u/20+1/4)
def compactAlpha (u : ℝ) : ℝ := 1-2*Real.exp (-u)
def compactTop (u : ℝ) : ℝ := u+(2*u+1)*Real.log (compactAlpha u)/(4*u+1)

theorem log_le_half_of_two_le {u : ℝ} (hu : (2 : ℝ) ≤ u) : Real.log u ≤ u/2 := by
  have hu0 : 0 < u := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < u/2 by positivity)
  rw [Real.log_div hu0.ne' (by norm_num)] at h
  linarith only [h,Certificate.log_two_coarse_bounds.2]

theorem compactZ_bounds {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    0 < compactZ u ∧ compactZ u < 2*u/3 := by
  have hu2 : (2 : ℝ) ≤ u := by linarith
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hu2
  have hh := log_le_half_of_two_le hu2
  unfold compactZ
  constructor <;> linarith only [hl,hh,hu,Certificate.log_two_coarse_bounds.1]

theorem compactGamma_pos (u : ℝ) : 0 < compactGamma u := by unfold compactGamma; positivity

theorem compact_parameter_domains {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    (2 : ℝ) ≤ compactT u ∧
      max 0 (Real.exp (2*compactT u-3)/2-compactT u) < compactGamma u := by
  have ht : (2 : ℝ) ≤ compactT u := by unfold compactT; linarith
  refine ⟨ht,max_lt (compactGamma_pos u) ?_⟩
  have he : 2*compactT u-3=49*u/50-1/5 := by unfold compactT; ring
  rw [he]
  unfold compactGamma
  linarith only [Real.exp_pos (9*u/20+1/4),ht]

theorem hasDerivAt_compactGamma_gap (u : ℝ) :
    HasDerivAt (fun s => compactGamma s-(5/2)*compactT s)
      ((49/100)*Real.exp (49*u/50-1/5)+(9/20)*Real.exp (9*u/20+1/4)-49/40) u := by
  have ha := ((((hasDerivAt_id u).const_mul (49/50)).sub_const (1/5)).exp).div_const 2
  have hb := (((hasDerivAt_id u).const_mul (9/20)).add_const (1/4)).exp
  have ht := (((hasDerivAt_id u).const_mul (49/100)).add_const (7/5)).const_mul (5/2)
  convert (ha.add hb).sub ht using 1
  · funext s
    dsimp [compactGamma,compactT]
    ring_nf
  · dsimp
    ring_nf

theorem compactGamma_gap_monotone :
    MonotoneOn (fun u => compactGamma u-(5/2)*compactT u) (Ici (9/4 : ℝ)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg
    (f' := fun u => (49/100)*Real.exp (49*u/50-1/5)+(9/20)*Real.exp (9*u/20+1/4)-49/40)
    (convex_Ici _)
  · intro u _
    exact (hasDerivAt_compactGamma_gap u).continuousAt.continuousWithinAt
  · intro u _
    exact (hasDerivAt_compactGamma_gap u).hasDerivWithinAt
  · intro u hu
    have hu' : (9/4 : ℝ) < u := by simpa using hu
    have he := Real.add_one_le_exp (49*u/50-1/5)
    have hb := Real.exp_pos (9*u/20+1/4)
    nlinarith only [hu',he,hb]

theorem compactGamma_gap_at_base :
    0 < compactGamma (9/4)-(5/2)*compactT (9/4) := by
  have ha := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 401/200) 4
  have hb := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 101/80) 4
  norm_num [Finset.sum_range_succ] at ha hb
  norm_num [compactGamma,compactT]
  linarith only [ha,hb]

theorem compactGamma_gt_five_halves_t {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    (5/2)*compactT u < compactGamma u := by
  have hm := compactGamma_gap_monotone (show (9/4 : ℝ) ∈ Ici (9/4) from le_rfl)
    hu hu
  linarith only [hm,compactGamma_gap_at_base]

theorem compact_shiftedMultiplier_bound {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    shiftedMultiplier (compactGamma u) (compactT u) ≤ (2/7)*compactGamma u := by
  have hg := compactGamma_pos u
  have ht := (compact_parameter_domains hu).1
  have hgt := compactGamma_gt_five_halves_t hu
  unfold shiftedMultiplier
  apply (div_le_iff₀ (show 0 < compactGamma u+compactT u by linarith)).mpr
  have hm := mul_le_mul_of_nonneg_left hgt.le hg.le
  nlinarith only [hm]

theorem compact_tanh_defect {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    1-Real.tanh u^2 < (1/20 : ℝ) := by
  have hb := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 9/2) 10
  norm_num [Finset.sum_range_succ] at hb
  have hebase : (80 : ℝ) < Real.exp (9/2) := by linarith only [hb]
  have he : (80 : ℝ) < Real.exp (2*u) :=
    hebase.trans_le (Real.exp_le_exp.mpr (by linarith))
  have hn : Real.exp (-2*u) < (1/80 : ℝ) := by
    rw [show -2*u=-(2*u) by ring,Real.exp_neg]
    simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 80) he
  have ht := tanh_square_tail_bound u
  rw [←exp_neg_twice] at ht
  linarith only [ht,hn]

theorem compact_mean_transfer_lower {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    (26/875)*compactGamma u ≤ meanTransferCoefficient
      ((Real.pi^2/4)*shiftedMultiplier (compactGamma u) (compactT u))
      (compactGamma u*Certificate.arcsineSharpConstant) (Real.tanh u) := by
  have hr := tanh_mem_Ioo_positive (by linarith : 0 < u)
  have hr2 : Real.tanh u^2 ≤ 1 := by nlinarith only [hr.1,hr.2]
  have hd0 : 0 ≤ 1-Real.tanh u^2 := sub_nonneg.mpr hr2
  have hd := compact_tanh_defect hu
  have hlog : Real.log 2 ≤ (7/10 : ℝ) := by
    linarith only [Certificate.log_two_coarse_bounds.2]
  have hmul := mul_le_mul_of_nonneg_left hlog hd0
  have hB : (93/200 : ℝ) ≤ 1/2-(1-Real.tanh u^2)*Real.log 2 := by
    nlinarith only [hmul,hd]
  have hB0 : 0 ≤ 1/2-(1-Real.tanh u^2)*Real.log 2 := by linarith only [hB]
  have hC := mul_le_mul_of_nonneg_right Certificate.arcsineSharpConstant_bounds.1.le hB0
  have hg := compactGamma_pos u
  have hCB : (93/125 : ℝ) ≤ Certificate.arcsineSharpConstant*
      (1/2-(1-Real.tanh u^2)*Real.log 2) := by nlinarith only [hC,hB]
  have hmean := mul_le_mul_of_nonneg_left hCB hg.le
  have hk0 := shiftedMultiplier_nonneg hg (show 0 ≤ compactT u by linarith [(compact_parameter_domains hu).1])
  have hk := compact_shiftedMultiplier_bound hu
  have hkr := mul_le_mul_of_nonneg_left hr2 hk0
  have hp := mul_le_mul_of_nonneg_right pi_square_quarter_bounds.2.le
    (mul_nonneg hk0 (sq_nonneg (Real.tanh u)))
  unfold meanTransferCoefficient
  nlinarith only [hmean,hk,hkr,hp]

theorem compact_mean_transfer_pos {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    0 < meanTransferCoefficient
      ((Real.pi^2/4)*shiftedMultiplier (compactGamma u) (compactT u))
      (compactGamma u*Certificate.arcsineSharpConstant) (Real.tanh u) :=
  (mul_pos (by norm_num : (0 : ℝ) < 26/875) (compactGamma_pos u)).trans_le
    (compact_mean_transfer_lower hu)

theorem compactAlpha_monotone : Monotone compactAlpha := by
  intro u v huv
  have he := Real.exp_le_exp.mpr (neg_le_neg huv)
  unfold compactAlpha
  linarith only [he]

theorem compactAlpha_at_base : Real.exp (-(1/4 : ℝ)) < compactAlpha (9/4) := by
  have hE : (729/100 : ℝ) < Real.exp 2 := by
    rw [show (2 : ℝ)=1+1 by norm_num,Real.exp_add]
    nlinarith only [exp_one_gt_twentyseven_tenths,sq_nonneg (Real.exp 1-27/10)]
  have hq := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/4)
  norm_num at hq
  have hm := mul_le_mul_of_nonneg_left
    (show (9/32 : ℝ) ≤ Real.exp (1/4)-1 by linarith only [hq]) (Real.exp_pos 2).le
  have hp : 2 < Real.exp 2*(Real.exp (1/4)-1) := by nlinarith only [hm,hE]
  have hb : 2+Real.exp 2 < Real.exp (9/4) := by
    rw [show (9/4 : ℝ)=2+1/4 by norm_num,Real.exp_add]
    nlinarith only [hp]
  have hi₁ : Real.exp (9/4 : ℝ)*Real.exp (-(1/4 : ℝ))=Real.exp 2 := by
    rw [←Real.exp_add]
    norm_num
  have hi₂ : Real.exp (9/4 : ℝ)*Real.exp (-(9/4 : ℝ))=1 := by
    rw [←Real.exp_add]
    norm_num
  apply (mul_lt_mul_iff_right₀ (Real.exp_pos (9/4 : ℝ))).mp
  unfold compactAlpha
  nlinarith only [hi₁,hi₂,hb]

theorem compactAlpha_lower {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    Real.exp (-(1/4 : ℝ)) < compactAlpha u :=
  compactAlpha_at_base.trans_le (compactAlpha_monotone hu)

theorem compactAlpha_mem {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    compactAlpha u ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨(Real.exp_pos _).trans (compactAlpha_lower hu),?_⟩
  unfold compactAlpha
  linarith only [Real.exp_pos (-u)]

theorem compactAlpha_log_lower {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    -(1/4 : ℝ) < Real.log (compactAlpha u) := by
  have h := Real.log_lt_log (Real.exp_pos (-(1/4 : ℝ))) (compactAlpha_lower hu)
  simpa only [Real.log_exp] using h

theorem compactAlpha_inverse_domain {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    Real.exp (2-u) ≤ compactAlpha u := by
  apply (Real.le_log_iff_exp_le (compactAlpha_mem hu).1).mp
  linarith only [compactAlpha_log_lower hu,hu]

theorem compactTop_bounds {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    u-1/4 < compactTop u ∧ compactTop u ≤ u := by
  have hu0 : 0 < u := by linarith only [hu]
  have hden : 0 < 4*u+1 := by positivity
  have hc : 0 ≤ (2*u+1)/(4*u+1) := by positivity
  have hc1 : (2*u+1)/(4*u+1) ≤ 1 := (div_le_one hden).mpr (by linarith only [hu])
  have ha := compactAlpha_mem hu
  have hlog : Real.log (compactAlpha u) ≤ 0 := Real.log_nonpos ha.1.le ha.2.le
  have hm := mul_nonpos_of_nonneg_of_nonpos hc hlog
  have hl := mul_le_mul_of_nonpos_right hc1 hlog
  have hlow := compactAlpha_log_lower hu
  unfold compactTop
  rw [show (2*u+1)*Real.log (compactAlpha u)/(4*u+1)=
    ((2*u+1)/(4*u+1))*Real.log (compactAlpha u) by ring]
  constructor <;> linarith only [hm,hl,hlow]

theorem compact_height_domains {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    0 < compactZ u ∧ compactZ u < 2*u/3 ∧ 2*u/3 < compactTop u ∧ compactTop u ≤ u := by
  have hz := compactZ_bounds hu
  have ht := compactTop_bounds hu
  exact ⟨hz.1,hz.2,by linarith only [ht.1,hu],ht.2⟩

theorem log_nine_lt_nine_fourths : Real.log 9 < (9/4 : ℝ) := by
  have hb := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 9/4) 7
  norm_num [Finset.sum_range_succ] at hb
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 9)).mpr
  linarith only [hb]

end
end CK
