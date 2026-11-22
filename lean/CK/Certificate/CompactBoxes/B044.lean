module
public import CK.Certificate.CompactChecks.B044
public import CK.Certificate.CompactProgram
@[expose] public section
set_option maxRecDepth 50000
set_option maxHeartbeats 0
namespace CK.Certificate.CompactData.B044
open CK.Certificate.CompactCircuit CK.Certificate.Interval
theorem master_positive : ∀ u ∈ Set.Icc (lo:ℝ) (hi:ℝ), 0<Compact.master u := by
  have hh := taylor_positive program wide center lo hi masterIndex
    (by decide +kernel) wide_checked center_checked (by decide +kernel)
  simpa only [master_identity] using hh
theorem lowerLogMargin_positive : ∀ u ∈ Set.Icc (lo:ℝ) (hi:ℝ), 0<Compact.lowerLogMargin u := by
  have hh := taylor_positive program wide center lo hi lowerLogMarginIndex
    (by decide +kernel) wide_checked center_checked (by decide +kernel)
  simpa only [lowerLogMargin_identity] using hh
theorem middleLogMargin_positive : ∀ u ∈ Set.Icc (lo:ℝ) (hi:ℝ), 0<Compact.middleLogMargin u := by
  have hh := taylor_positive program wide center lo hi middleLogMarginIndex
    (by decide +kernel) wide_checked center_checked (by decide +kernel)
  simpa only [middleLogMargin_identity] using hh
theorem middleQuadMargin_positive : ∀ u ∈ Set.Icc (lo:ℝ) (hi:ℝ), 0<Compact.middleQuadMargin u := by
  have hh := taylor_positive program wide center lo hi middleQuadMarginIndex
    (by decide +kernel) wide_checked center_checked (by decide +kernel)
  simpa only [middleQuadMargin_identity] using hh
theorem upperQuadMargin_positive : ∀ u ∈ Set.Icc (lo:ℝ) (hi:ℝ), 0<Compact.upperQuadMargin u := by
  have hh := taylor_positive program wide center lo hi upperQuadMarginIndex
    (by decide +kernel) wide_checked center_checked (by decide +kernel)
  simpa only [upperQuadMargin_identity] using hh
end CK.Certificate.CompactData.B044
