module

public import CK.High.RefundAverage
public import CK.High.ArctanEnergy
public import CK.High.EdgeHyperbolic

/-! Coordinate summation for the simultaneous arcsine refinement. All coordinates share the same production sum. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

private theorem edge_arcsine_refund_ordered {x y : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) (hyx : y < x) :
    edgeRefund ((signEntropy x+signEntropy y)/2) |(x-y)/2| ≤
      (x-y)*(Real.artanh x-Real.artanh y)/4-((Real.arcsin x-Real.arcsin y)/2)^2 := by
  let a := (Real.artanh x+Real.artanh y)/2
  let b := (Real.artanh x-Real.artanh y)/2
  have hb : 0 < b := by
    have h := Real.artanh_lt_artanh hy.1 hx.2 hyx
    dsimp [b]
    linarith only [h]
  have hx' : Real.tanh (a+b)=x := by
    rw [show a+b=Real.artanh x by dsimp [a,b]; ring]
    exact Real.tanh_artanh hx
  have hy' : Real.tanh (a-b)=y := by
    rw [show a-b=Real.artanh y by dsimp [a,b]; ring]
    exact Real.tanh_artanh hy
  have hd := tanh_edge_half_difference a b
  rw [hx',hy'] at hd
  have hangle := arcsin_tanh_edge_half_difference a b
  rw [hx',hy'] at hangle
  have hR := arctan_hyperbolic_refund a hb
  rw [←hd,←hangle] at hR
  have he : 0 < (signEntropy x+signEntropy y)/2 := by
    have h1 : 0 < signEntropy x := Profile.meanEntropy_pos hx
    have h2 : 0 < signEntropy y := Profile.meanEntropy_pos hy
    positivity
  have hdpos : 0 < (x-y)/2 := by linarith only [hyx]
  have hCGN := Profile.edge_entropy_profile hx hy
  change Profile.profile ((signEntropy x+signEntropy y)/2) |(x-y)/2| ≤ _ at hCGN
  rw [abs_of_pos hdpos,profile_eq_mul_edgeHeight] at hCGN
  have hheight : edgeHeight ((signEntropy x+signEntropy y)/2) ((x-y)/2) ≤ b := by
    apply (mul_le_mul_iff_right₀ hdpos).mp
    dsimp [b]
    nlinarith only [hCGN]
  have hmono := arcsineRemainder_strictMono.monotoneOn
    (edgeHeight_nonneg he hdpos.le) hb.le hheight
  have hmul := mul_le_mul_of_nonneg_left hmono hdpos.le
  rw [abs_of_pos hdpos,edgeRefund]
  dsimp [b] at hR
  nlinarith only [hmul,hR]

/-- The exact scalar edge refund, including equal edge endpoints. -/
theorem edge_arcsine_refund {x y : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    edgeRefund ((signEntropy x+signEntropy y)/2) |(x-y)/2| ≤
      (x-y)*(Real.artanh x-Real.artanh y)/4-((Real.arcsin x-Real.arcsin y)/2)^2 := by
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have h := edge_arcsine_refund_ordered hy hx hxy
    have habs : |(y-x)/2|=|(x-y)/2| := by rw [abs_div,abs_div,abs_sub_comm]
    rw [habs,add_comm (signEntropy y) (signEntropy x)] at h
    nlinarith only [h]
  · simp
  · exact edge_arcsine_refund_ordered hx hy hyx

private theorem coordinate_refund_sum
    (hscalar : ∀ {x y : ℝ}, x ∈ Set.Ioo (-1 : ℝ) 1 → y ∈ Set.Ioo (-1 : ℝ) 1 →
      edgeRefund ((signEntropy x+signEntropy y)/2) |(x-y)/2| ≤
        (x-y)*(Real.artanh x-Real.artanh y)/4-((Real.arcsin x-Real.arcsin y)/2)^2)
    {n : ℕ} (g : Cube n → ℝ) (hg : ∀ x, g x ∈ Set.Ioo (-1 : ℝ) 1) :
    dirichlet (fun x => Real.arcsin (g x)) +
      (∑ i : Fin n, edgeRefund (avg (fun x => signEntropy (g x))) |fourier g {i}|) ≤
      entropyProduction g := by
  rw [dirichlet_eq_sum_partials,entropyProduction_eq_edges,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hj := edgeRefund_le_average i g hg
  have hs := avg_mono (fun x => hscalar (hg x) (hg (flipCoordinate i x)))
  rw [avg_sub] at hs
  have hj' : edgeRefund (avg (fun x => signEntropy (g x))) |fourier g {i}| ≤
      avg (fun x => edgeRefund ((signEntropy (g x)+signEntropy (g (flipCoordinate i x)))/2)
        |(g x-g (flipCoordinate i x))/2|) := by
    simpa only [Profile.edgeEntropy,Profile.abs_orientedEdge,Profile.meanEntropy,signEntropy] using hj
  have hprod : avg (fun x => (g x-g (flipCoordinate i x)) *
      (phiSlope (g x)-phiSlope (g (flipCoordinate i x)))/4) =
      avg (fun x => (g x-g (flipCoordinate i x)) *
      (Real.artanh (g x)-Real.artanh (g (flipCoordinate i x)))/4) := by
    congr 1
    funext x
    rw [phiSlope_eq_artanh (hg x),phiSlope_eq_artanh (hg (flipCoordinate i x))]
  rw [hprod]
  change avg (fun x => ((Real.arcsin (g x)-Real.arcsin (g (flipCoordinate i x)))/2)^2)+_ ≤ _
  linarith only [hj',hs]

private theorem selected_coordinate_refund_sum
    (hscalar : ∀ {x y : ℝ}, x ∈ Set.Ioo (-1 : ℝ) 1 → y ∈ Set.Ioo (-1 : ℝ) 1 →
      edgeRefund ((signEntropy x+signEntropy y)/2) |(x-y)/2| ≤
        (x-y)*(Real.artanh x-Real.artanh y)/4-((Real.arcsin x-Real.arcsin y)/2)^2)
    {n : ℕ} (g : Cube n → ℝ) (hg : ∀ x, g x ∈ Set.Ioo (-1 : ℝ) 1) (K : Finset (Fin n)) :
    dirichlet (fun x => Real.arcsin (g x)) +
      (∑ i ∈ K, edgeRefund (avg (fun x => signEntropy (g x))) |fourier g {i}|) ≤
      entropyProduction g := by
  have h := coordinate_refund_sum hscalar g hg
  have he : 0 < avg (fun x => signEntropy (g x)) := by
    change 0 < (Fintype.card (Cube n) : ℝ)⁻¹*∑ x, signEntropy (g x)
    apply mul_pos (inv_pos.mpr (card_cube_pos n))
    have hp (x : Cube n) : 0 < signEntropy (g x) := Profile.meanEntropy_pos (hg x)
    exact Finset.sum_pos' (fun x _ => (hp x).le)
      ⟨(fun _ => false),Finset.mem_univ _,hp _⟩
  have hsum : (∑ i ∈ K, edgeRefund (avg (fun x => signEntropy (g x))) |fourier g {i}|) ≤
      ∑ i : Fin n, edgeRefund (avg (fun x => signEntropy (g x))) |fourier g {i}| := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ K)
      (fun i _ _ => edgeRefund_nonneg he (abs_nonneg _))
  linarith only [h,hsum]

/-- All chosen coordinates use the same Dirichlet and production budgets. -/
theorem entropyProduction_ge_dirichlet_refund {n : ℕ}
    (g : Cube n → ℝ) (hg : ∀ x, g x ∈ Set.Ioo (-1 : ℝ) 1) (K : Finset (Fin n)) :
    dirichlet (fun x => Real.arcsin (g x)) +
      (∑ i ∈ K, edgeRefund (avg (fun x => signEntropy (g x))) |fourier g {i}|) ≤
      entropyProduction g :=
  selected_coordinate_refund_sum (fun hx hy => edge_arcsine_refund hx hy) g hg K

theorem arcsine_refinement {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (f : BooleanFunction n) (hf : ∃ u v, f u ≠ f v) (K : Finset (Fin n)) :
    dirichlet (fun x => Real.arcsin (noise ρ (lift f) x)) +
      (∑ i ∈ K, edgeRefund (conditionalEntropy ρ f) (ρ*|fourier (lift f) {i}|)) ≤
      entropyProduction (noise ρ (lift f)) := by
  have hg : ∀ x, noise ρ (lift f) x ∈ Set.Ioo (-1 : ℝ) 1 :=
    noise_lift_mem_Ioo ⟨by linarith [hρ.1],hρ.2⟩ f hf
  have h := entropyProduction_ge_dirichlet_refund (noise ρ (lift f)) hg K
  have hcoeff (i : Fin n) : |fourier (noise ρ (lift f)) {i}|=ρ*|fourier (lift f) {i}| := by
    rw [fourier_noise]
    simp only [Finset.card_singleton,pow_one,abs_mul,abs_of_pos hρ.1]
  simpa only [hcoeff,conditionalEntropy,signEntropy] using h

/-- Positive-gap specialization of the simultaneous arcsine refinement.
The input function and retained coordinate set are fixed, and no budget
is spent independently on different coordinates. -/
theorem arcsine_refinement_positive_gap {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (f : BooleanFunction n) (hf : ∃ u v, f u ≠ f v)
    (hgap : 0 < informationGap ρ f) (K : Finset (Fin n)) :
    dirichlet (fun x => Real.arcsin (noise ρ (lift f) x)) +
      ρ*(∑ i ∈ K, |fourier (lift f) {i}| *arcsineRemainder (profileHeight ρ |fourier (lift f) {i}|)) ≤
      entropyProduction (noise ρ (lift f)) := by
  have h := arcsine_refinement hρ f hf K
  have hE := Profile.conditionalEntropy_pos hρ f hf
  have hEH := conditionalEntropy_lt_of_positive_gap f hgap
  have hsum : (∑ i ∈ K, edgeRefund (signEntropy ρ) (ρ*|fourier (lift f) {i}|)) ≤
      ∑ i ∈ K, edgeRefund (conditionalEntropy ρ f) (ρ*|fourier (lift f) {i}|) := by
    apply Finset.sum_le_sum
    intro i _
    exact edgeRefund_antitone_left hE hEH.le (mul_nonneg hρ.1.le (abs_nonneg _))
  have hid : (∑ i ∈ K, edgeRefund (signEntropy ρ) (ρ*|fourier (lift f) {i}|)) =
      ρ*(∑ i ∈ K, |fourier (lift f) {i}| *arcsineRemainder (profileHeight ρ |fourier (lift f) {i}|)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold edgeRefund profileHeight
    ring
  rw [hid] at hsum
  linarith only [h,hsum]

end
end CK
