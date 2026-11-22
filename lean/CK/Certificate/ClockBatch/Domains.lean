module
public import CK.Certificate.ClockBatch.All
@[expose] public section
set_option autoImplicit false
namespace CK.Certificate.ClockBatch
noncomputable section

namespace C00
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C00

namespace C01
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C01

namespace C02
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C02

namespace C03
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v003 ≤ 1
    have h := v003_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C03

namespace C04
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v009 ≤ 1
    have h := v009_bound.2
    norm_num at h
    linarith
  · change v016 ≤ 1
    have h := v016_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C04

namespace C05
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v007 ≤ 1
    have h := v007_bound.2
    norm_num at h
    linarith
  · change v012 ≤ 1
    have h := v012_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v007
    have h := v007_bound.1
    norm_num at h
    linarith
end C05

namespace C06
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v003 ≤ 1
    have h := v003_bound.2
    norm_num at h
    linarith
  · change v005 ≤ 1
    have h := v005_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C06

namespace C07
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C07

namespace C08
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v003 ≤ 1
    have h := v003_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C08

namespace C09
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C09

namespace C10
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v003 ≤ 1
    have h := v003_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C10

namespace C11
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v003 ≤ 1
    have h := v003_bound.2
    norm_num at h
    linarith
  · change v005 ≤ 1
    have h := v005_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C11

namespace C12
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C12

namespace C13
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C13

namespace C14
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v003 ≤ 1
    have h := v003_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C14

namespace C15
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v003 ≤ 1
    have h := v003_bound.2
    norm_num at h
    linarith
  · change v005 ≤ 1
    have h := v005_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C15

namespace C16
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C16

namespace C17
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C17

namespace C18
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v003 ≤ 1
    have h := v003_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C18

namespace C19
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v003 ≤ 1
    have h := v003_bound.2
    norm_num at h
    linarith
  · change v005 ≤ 1
    have h := v005_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C19

namespace C20
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C20

namespace C21
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C21

namespace C22
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v003 ≤ 1
    have h := v003_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C22

namespace C23
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v003 ≤ 1
    have h := v003_bound.2
    norm_num at h
    linarith
  · change v005 ≤ 1
    have h := v005_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C23

namespace C24
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v003 ≤ 1
    have h := v003_bound.2
    norm_num at h
    linarith
  · change v005 ≤ 1
    have h := v005_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C24

namespace C25
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v003 ≤ 1
    have h := v003_bound.2
    norm_num at h
    linarith
  · change v005 ≤ 1
    have h := v005_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C25

namespace C26
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v003 ≤ 1
    have h := v003_bound.2
    norm_num at h
    linarith
  · change v005 ≤ 1
    have h := v005_bound.2
    norm_num at h
    linarith
  · change v007 ≤ 1
    have h := v007_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C26

namespace C27
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v003 ≤ 1
    have h := v003_bound.2
    norm_num at h
    linarith
  · change v005 ≤ 1
    have h := v005_bound.2
    norm_num at h
    linarith
  · change v007 ≤ 1
    have h := v007_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C27

namespace C28
theorem parameters_le_one : ∀ i, parameters i ≤ 1 := by
  intro i
  fin_cases i
  · change v001 ≤ 1
    have h := v001_bound.2
    norm_num at h
    linarith
  · change v003 ≤ 1
    have h := v003_bound.2
    norm_num at h
    linarith
  · change v005 ≤ 1
    have h := v005_bound.2
    norm_num at h
    linarith
  · change v007 ≤ 1
    have h := v007_bound.2
    norm_num at h
    linarith
theorem positive_term : ∃ i, 0 < weights i ∧ 0 < parameters i := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [weights]
  · change 0 < v001
    have h := v001_bound.1
    norm_num at h
    linarith
end C28

end
end CK.Certificate.ClockBatch
