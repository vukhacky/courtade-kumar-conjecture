module

public import CK.Fourier.Influences

/-! Finite coordinate selections with dimension hypotheses explicit. -/

@[expose] public section
set_option autoImplicit false
namespace CK.Middle
noncomputable section

theorem exists_largest_singleton {n : ℕ} (hn : 0 < n) (f : BooleanFunction n) :
    ∃ i : Fin n, ∀ j, fourier (lift f) {j} ≤ fourier (lift f) {i} := by
  obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin n => fourier (lift f) {i}) (fin_univ_nonempty hn)
  exact ⟨i,fun j => hmax j (Finset.mem_univ j)⟩

theorem exists_second_singleton {n : ℕ} (hn : 2 ≤ n) (f : BooleanFunction n) (i : Fin n) :
    ∃ j : Fin n, i ≠ j ∧ ∀ l : Fin n, l ≠ i → fourier (lift f) {l} ≤ fourier (lift f) {j} := by
  classical
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have hne : (Finset.univ.erase i : Finset (Fin n)).Nonempty := by
    obtain ⟨j,hji⟩ := exists_ne i
    exact ⟨j,by simp [hji]⟩
  obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image (Finset.univ.erase i)
    (fun j : Fin n => fourier (lift f) {j}) hne
  refine ⟨j,Ne.symm (Finset.mem_erase.mp hj).1,?_⟩
  intro l hli
  exact hmax l (by simp [hli])

end
end CK.Middle
