import Formalism.FlagUnipotentLattices.Bundle0008
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.OperatorHilbertSchmidtNorm
import Formalism.FlagUnipotentLattices.Bundle0006
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.NearFarVolumeBounds
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.KappaConstantAssembly

-- bundled from Formalism.FlagUnipotentLattices.CuspThresholdBound
section
namespace Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts

theorem nearTotalAbs : Formalism.HermitianLatticeCounting.S7.NearTotalAbs := Formalism.HermitianLatticeCounting.P.near_region_total_abs
theorem cusp_threshold_bound : Formalism.HermitianLatticeCounting.S7.CuspidalityThreshold := Formalism.HermitianLatticeCounting.P.threshold_cusp_numeric
theorem threshCuspOp : Formalism.HermitianLatticeCounting.S7.ThreshCuspOp := Formalism.HermitianLatticeCounting.P.threshold_cusp_operator
theorem pZero : Formalism.HermitianLatticeCounting.S7.PZero := Formalism.HermitianLatticeCounting.P.probability_zero
theorem cubeMult : Formalism.HermitianLatticeCounting.S7.CubeMult := Formalism.HermitianLatticeCounting.P.cube_multiplication
theorem volLevel : Formalism.HermitianLatticeCounting.S7.VolLevel := Formalism.HermitianLatticeCounting.P.volume_level
theorem deepChainV : Formalism.HermitianLatticeCounting.S7.DeepChainV := Formalism.HermitianLatticeCounting.P.deep_region_chain_volume

end Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts
end

-- bundled from Formalism.FlagUnipotentLattices.KappaAssemblyOf
section
namespace Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds

theorem polarInv : Formalism.HermitianLatticeCounting.S7.PolarInv := Formalism.HermitianLatticeCounting.P.polar_decomposition_inverse
theorem allSumRate : Formalism.HermitianLatticeCounting.S7.AllSumRate := Formalism.HermitianLatticeCounting.P.all_sum_rate
theorem threshCount : Formalism.HermitianLatticeCounting.S7.ThreshCount := Formalism.HermitianLatticeCounting.P.threshold_count
theorem layerCount : Formalism.HermitianLatticeCounting.S7.LayerCount := Formalism.HermitianLatticeCounting.P.layer_count
theorem kappaAssembly : Formalism.HermitianLatticeCounting.S7.KappaAssembly := Formalism.HermitianLatticeCounting.P.kappa_constant_assembly
theorem logVolumeBound : Formalism.HermitianLatticeCounting.S7.LogVolumeBound := Formalism.HermitianLatticeCounting.P.log_volume_bound
theorem stepsRoom : Formalism.HermitianLatticeCounting.S7.StepsRoom := Formalism.HermitianLatticeCounting.P.room_for_iterations

end Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds
end

