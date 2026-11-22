module

public import CK.Fourier.Influences
public import CK.Basic.ShannonBridge
public import CK.Fourier.Noise

/-! Coordinate sorting. The construction is independent of the noise
parameter, preserves the mean, and increases information for every BSC
parameter in `[0,1]`. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

theorem phi_pair_spread_le {b d e : ℝ} (hde : |d| ≤ e)
    (hminus : b-e ∈ Set.Icc (-1 : ℝ) 1) (hplus : b+e ∈ Set.Icc (-1 : ℝ) 1) :
    phi (b+d) + phi (b-d) ≤ phi (b+e) + phi (b-e) := by
  have he : 0 ≤ e := le_trans (abs_nonneg d) hde
  rcases eq_or_lt_of_le he with heq | hepos
  · have he0 : e = 0 := heq.symm
    have hd0 : d = 0 := abs_nonpos_iff.mp (by simpa [he0] using hde)
    simp [he0, hd0]
  · have hden : 0 < 2*e := by positivity
    have hα : 0 ≤ (e+d)/(2*e) := div_nonneg (by linarith [(abs_le.mp hde).1]) hden.le
    have hβ : 0 ≤ (e-d)/(2*e) := div_nonneg (by linarith [(abs_le.mp hde).2]) hden.le
    have hsum : (e+d)/(2*e)+(e-d)/(2*e)=1 := by field_simp; ring
    have hp := phi_convexOn_closed.2 hminus hplus hβ hα (by linarith [hsum])
    have hm := phi_convexOn_closed.2 hminus hplus hα hβ hsum
    simp only [smul_eq_mul] at hp hm
    have hp' : (e-d)/(2*e)*(b-e)+(e+d)/(2*e)*(b+e)=b+d := by field_simp; ring
    have hm' : (e+d)/(2*e)*(b-e)+(e-d)/(2*e)*(b+e)=b-d := by field_simp; ring
    rw [hp'] at hp
    rw [hm'] at hm
    have hr : ((e-d)/(2*e)*phi (b-e)+(e+d)/(2*e)*phi (b+e))+
        ((e+d)/(2*e)*phi (b-e)+(e-d)/(2*e)*phi (b+e)) = phi (b+e)+phi (b-e) := by
      calc
        _ = ((e+d)/(2*e)+(e-d)/(2*e))*(phi (b+e)+phi (b-e)) := by ring
        _ = _ := by rw [hsum, one_mul]
    linarith

def coordinateSort {n : ℕ} (i : Fin n) (f : BooleanFunction n) : BooleanFunction n :=
  fun x => if x i then max (f (Function.update x i false)) (f (Function.update x i true))
    else min (f (Function.update x i false)) (f (Function.update x i true))

theorem coordinateSort_insertNth {n : ℕ} (i : Fin (n+1)) (f : BooleanFunction (n+1))
    (b : Bool) (x : Cube n) :
    coordinateSort i f (i.insertNth b x) =
      if b then max (f (i.insertNth false x)) (f (i.insertNth true x))
      else min (f (i.insertNth false x)) (f (i.insertNth true x)) := by
  simp only [coordinateSort, Fin.insertNth_apply_same, Fin.update_insertNth]

theorem sign_min_add_sign_max (a b : Bool) :
    sign (min a b) + sign (max a b) = sign a + sign b := by
  cases a <;> cases b <;> norm_num [sign]

theorem sign_max_sub_sign_min (a b : Bool) :
    sign (max a b) - sign (min a b) = |sign b - sign a| := by
  cases a <;> cases b <;> norm_num [sign]

theorem mean_coordinateSort {n : ℕ} (i : Fin n) (f : BooleanFunction n) :
    mean (coordinateSort i f) = mean f := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    unfold mean
    rw [avg_cube_insertNth i, avg_cube_insertNth i (lift f)]
    congr 1
    funext x
    simp only [lift, coordinateSort_insertNth, Bool.false_eq_true, ↓reduceIte]
    rw [sign_min_add_sign_max]

def sectionMean {n : ℕ} (i : Fin (n+1)) (g : Cube (n+1) → ℝ) (x : Cube n) : ℝ :=
  (g (i.insertNth false x) + g (i.insertNth true x))/2

def sectionDifference {n : ℕ} (i : Fin (n+1)) (g : Cube (n+1) → ℝ) (x : Cube n) : ℝ :=
  (g (i.insertNth true x) - g (i.insertNth false x))/2

theorem sectionMean_coordinateSort {n : ℕ} (i : Fin (n+1)) (f : BooleanFunction (n+1)) :
    sectionMean i (lift (coordinateSort i f)) = sectionMean i (lift f) := by
  funext x
  simp only [sectionMean, lift, coordinateSort_insertNth, Bool.false_eq_true, ↓reduceIte]
  rw [sign_min_add_sign_max]

theorem sectionDifference_coordinateSort {n : ℕ} (i : Fin (n+1)) (f : BooleanFunction (n+1)) :
    sectionDifference i (lift (coordinateSort i f)) = fun x => |sectionDifference i (lift f) x| := by
  funext x
  simp only [sectionDifference, lift, coordinateSort_insertNth, Bool.false_eq_true, ↓reduceIte]
  rw [sign_max_sub_sign_min, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem noise_insertNth_mean_difference {n : ℕ} (i : Fin (n+1)) (ρ : ℝ)
    (g : Cube (n+1) → ℝ) (b : Bool) (x : Cube n) :
    noise ρ g (i.insertNth b x) = noise ρ (sectionMean i g) x +
      sign b * ρ * noise ρ (sectionDifference i g) x := by
  rw [noise_insertNth]
  have hm : sectionMean i g = fun y => (1/2 : ℝ) *
      (g (i.insertNth false y) + g (i.insertNth true y)) := by funext y; simp [sectionMean]; ring
  have hd : sectionDifference i g = fun y => (1/2 : ℝ) *
      (g (i.insertNth true y) - g (i.insertNth false y)) := by funext y; simp [sectionDifference]; ring
  rw [hm, hd, noise_smul, noise_smul, noise_add, noise_sub]
  cases b <;> simp [bitKernel, sign] <;> ring

theorem abs_noise_le_noise_abs {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (g : Cube n → ℝ) (x : Cube n) : |noise ρ g x| ≤ noise ρ (fun y => |g y|) x := by
  apply abs_le.mpr
  constructor
  · have h := noise_mono hρ (fun y => neg_abs_le (g y)) x
    rw [noise_neg] at h
    exact h
  · exact noise_mono hρ (fun y => le_abs_self (g y)) x

theorem information_coordinateSort_le {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin n) (f : BooleanFunction n) : information ρ f ≤ information ρ (coordinateSort i f) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    unfold information
    rw [mean_coordinateSort]
    apply sub_le_sub_right
    rw [avg_cube_insertNth i, avg_cube_insertNth i]
    apply avg_mono
    intro x
    have hr : ρ ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hρ.1], hρ.2⟩
    have hdom (b : Bool) := noise_mem_Icc hr (lift (coordinateSort i f))
      (fun y => sign_mem_Icc (coordinateSort i f y)) (i.insertNth b x)
    simp only [noise_insertNth_mean_difference, sectionMean_coordinateSort,
      sectionDifference_coordinateSort, sign_false, sign_true, neg_one_mul, one_mul] at hdom ⊢
    have hde : |ρ * noise ρ (sectionDifference i (lift f)) x| ≤
        ρ * noise ρ (fun y => |sectionDifference i (lift f) y|) x := by
      rw [abs_mul, abs_of_nonneg hρ.1]
      exact mul_le_mul_of_nonneg_left (abs_noise_le_noise_abs hr _ x) hρ.1
    have h := phi_pair_spread_le (b := noise ρ (sectionMean i (lift f)) x) hde
      (by simpa only [sign_false, neg_one_mul, sub_eq_add_neg, neg_mul, one_mul] using hdom false)
      (by simpa only [sign_true, one_mul] using hdom true)
    simp only [sub_eq_add_neg, neg_mul] at h ⊢
    linarith

theorem fourier_singleton_eq_avg_sectionDifference {n : ℕ} (i : Fin (n+1))
    (g : Cube (n+1) → ℝ) : fourier g {i} = avg (sectionDifference i g) := by
  rw [fourier_singleton, avg_cube_insertNth i]
  congr 1
  funext x
  simp only [sectionDifference, Fin.insertNth_apply_same, sign_false, sign_true,
    mul_neg_one, mul_one]
  ring

theorem fourier_coordinateSort_self {n : ℕ} (i : Fin n) (f : BooleanFunction n) :
    |fourier (lift f) {i}| ≤ fourier (lift (coordinateSort i f)) {i} := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [fourier_singleton_eq_avg_sectionDifference, fourier_singleton_eq_avg_sectionDifference,
      sectionDifference_coordinateSort]
    exact abs_avg_le_avg_abs _

theorem fourier_coordinateSort_other {n : ℕ} (i j : Fin n) (hji : j ≠ i)
    (f : BooleanFunction n) :
    fourier (lift (coordinateSort i f)) {j} = fourier (lift f) {j} := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
    rw [fourier_singleton, fourier_singleton, avg_cube_insertNth i, avg_cube_insertNth i]
    congr 1
    funext x
    simp only [lift, coordinateSort_insertNth, Fin.insertNth_apply_succAbove,
      Bool.false_eq_true, ↓reduceIte, ← add_mul, sign_min_add_sign_max]

def MonotoneIn {n : ℕ} (i : Fin n) (f : BooleanFunction n) : Prop :=
  ∀ x y, (∀ j, j ≠ i → x j = y j) → x i ≤ y i → f x ≤ f y

theorem coordinateSort_monotoneIn {n : ℕ} (i : Fin n) (f : BooleanFunction n) :
    MonotoneIn i (coordinateSort i f) := by
  intro x y hxy hi
  have hup (b : Bool) : Function.update x i b = Function.update y i b := by
    funext j
    by_cases hji : j = i
    · subst j; simp
    · simp only [Function.update_of_ne hji, hxy j hji]
  unfold coordinateSort
  rw [hup false, hup true]
  cases hx : x i <;> cases hy : y i
  · simp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact min_le_max
  · have hh : (true : Bool) ≤ false := by simpa only [hx, hy] using hi
    have heq : (false : Bool) = true := Bool.eq_true_of_true_le hh
    cases heq
  · simp

theorem coordinateSort_preserves_monotoneIn {n : ℕ} (i j : Fin n) (hji : j ≠ i)
    (f : BooleanFunction n) (hf : MonotoneIn j f) : MonotoneIn j (coordinateSort i f) := by
  intro x y hxy hj
  have hix : x i = y i := hxy i (Ne.symm hji)
  have hs (b : Bool) : f (Function.update x i b) ≤ f (Function.update y i b) := by
    apply hf
    · intro k hkj
      by_cases hki : k = i
      · subst k; simp
      · simp only [Function.update_of_ne hki, hxy k hkj]
    · simpa only [Function.update_of_ne hji] using hj
  unfold coordinateSort
  rw [hix]
  cases y i
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact min_le_min (hs false) (hs true)
  · simp only [↓reduceIte]
    exact max_le_max (hs false) (hs true)

theorem monotone_of_monotoneIn {n : ℕ} (f : BooleanFunction n)
    (hf : ∀ i, MonotoneIn i f) : Monotone f := by
  induction n with
  | zero =>
    intro x y _
    have hxy : x = y := by funext i; exact Fin.elim0 i
    rw [hxy]
  | succ n ih =>
    have hsec (b : Bool) : Monotone (fun x : Cube n => f (Fin.cons b x)) := by
      apply ih
      intro i x y hxy hi
      apply hf i.succ (Fin.cons b x) (Fin.cons b y)
      · intro j
        refine Fin.cases (fun _ => by simp) (fun k hki => ?_) j
        simp only [Fin.cons_succ]
        exact hxy k (by intro hk; exact hki (congrArg Fin.succ hk))
      · simpa only [Fin.cons_succ] using hi
    intro x y hxy
    have hh : f (Fin.cons (x 0) (Fin.tail x)) ≤ f (Fin.cons (y 0) (Fin.tail x)) := by
      apply hf 0
      · intro j
        exact Fin.cases (fun hj => False.elim (hj rfl)) (fun _ _ => rfl) j
      · simpa only [Fin.cons_zero] using hxy 0
    have ht := hsec (y 0) (show Fin.tail x ≤ Fin.tail y from fun i => hxy i.succ)
    simpa only [Fin.cons_self_tail] using hh.trans ht

theorem sign_monotone : Monotone sign := by
  intro a b hab
  cases a <;> cases b <;> norm_num [sign] at hab ⊢
  have heq : (false : Bool) = true := Bool.eq_true_of_true_le hab
  cases heq

theorem monotone_lift_of_monotone {n : ℕ} (f : BooleanFunction n) (hf : Monotone f) :
    Monotone (lift f) := sign_monotone.comp hf

theorem exists_compression_on {n : ℕ} (K : Finset (Fin n)) (f : BooleanFunction n) :
    ∃ g : BooleanFunction n,
      (∀ i ∈ K, MonotoneIn i g) ∧ mean g = mean f ∧
      (∀ ρ ∈ Set.Icc (0 : ℝ) 1, information ρ f ≤ information ρ g) ∧
      (∀ i ∈ K, |fourier (lift f) {i}| ≤ fourier (lift g) {i}) ∧
      (∀ i ∉ K, fourier (lift g) {i} = fourier (lift f) {i}) := by
  classical
  induction K using Finset.induction_on with
  | empty =>
    refine ⟨f, ?_, rfl, ?_, ?_, ?_⟩
    · simp
    · intro ρ hρ; exact le_rfl
    · simp
    · intro i hi; rfl
  | @insert i K hi ih =>
    obtain ⟨g, hgmon, hgmean, hginfo, hgcoeff, hgother⟩ := ih
    refine ⟨coordinateSort i g, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with hji | hj
      · subst j
        exact coordinateSort_monotoneIn i g
      · exact coordinateSort_preserves_monotoneIn i j (by intro h; subst j; exact hi hj) g (hgmon j hj)
    · rw [mean_coordinateSort, hgmean]
    · intro ρ hρ
      exact (hginfo ρ hρ).trans (information_coordinateSort_le hρ i g)
    · intro j hj
      rcases Finset.mem_insert.mp hj with hji | hj
      · subst j
        rw [← hgother i hi]
        exact fourier_coordinateSort_self i g
      · rw [fourier_coordinateSort_other i j (by intro h; subst j; exact hi hj)]
        exact hgcoeff j hj
    · intro j hj
      have hji : j ≠ i := by intro h; subst j; exact hj (Finset.mem_insert_self _ _)
      rw [fourier_coordinateSort_other i j hji]
      exact hgother j (by intro hjK; exact hj (Finset.mem_insert_of_mem hjK))

/-- One fixed compressed function works simultaneously for every `ρ ∈ [0,1]`.
The mean correction in information is preserved exactly. -/
theorem exists_monotone_compression {n : ℕ} (f : BooleanFunction n) :
    ∃ g : BooleanFunction n, Monotone (lift g) ∧ mean g = mean f ∧
      (∀ ρ ∈ Set.Icc (0 : ℝ) 1, information ρ f ≤ information ρ g) ∧
      (∀ i, |fourier (lift f) {i}| ≤ fourier (lift g) {i}) := by
  obtain ⟨g, hgmon, hgmean, hginfo, hgcoeff, _⟩ := exists_compression_on Finset.univ f
  exact ⟨g, monotone_lift_of_monotone g
    (monotone_of_monotoneIn g (fun i => hgmon i (Finset.mem_univ _))),
    hgmean, hginfo, fun i => hgcoeff i (Finset.mem_univ _)⟩

theorem minSignedDictatorDistance_le_of_singletons {n : ℕ} (hn : 0 < n)
    (f g : BooleanFunction n) (hfg : ∀ i, |fourier (lift f) {i}| ≤ fourier (lift g) {i}) :
    minSignedDictatorDistance hn g ≤ minSignedDictatorDistance hn f := by
  obtain ⟨i, hi⟩ := exists_max_singleton hn f
  have hmax : maxSingletonCoeff hn f ≤ maxSingletonCoeff hn g := by
    rw [hi]
    exact (hfg i).trans ((le_abs_self _).trans (singleton_le_max hn g i))
  rw [minSignedDictatorDistance_eq, minSignedDictatorDistance_eq]
  linarith

theorem exists_monotone_compression_shannon {n : ℕ} (hn : 0 < n) (f : BooleanFunction n) :
    ∃ g : BooleanFunction n, Monotone (lift g) ∧ mean g = mean f ∧
      (∀ ρ ∈ Set.Icc (0 : ℝ) 1, mutualInformation ρ f ≤ mutualInformation ρ g) ∧
      (∀ i, |fourier (lift f) {i}| ≤ fourier (lift g) {i}) ∧
      minSignedDictatorDistance hn g ≤ minSignedDictatorDistance hn f := by
  obtain ⟨g, hgmon, hgmean, hginfo, hgcoeff⟩ := exists_monotone_compression f
  refine ⟨g, hgmon, hgmean, ?_, hgcoeff, minSignedDictatorDistance_le_of_singletons hn f g hgcoeff⟩
  intro ρ hρ
  rw [mutualInformation_eq_information hρ, mutualInformation_eq_information hρ]
  exact hginfo ρ hρ

end
end CK
