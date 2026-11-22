import Development.WeilBound.ThetaLifts.TowerModels.Bundle0004
import Development.WeilBound.ThetaLifts.TowerModels.Bundle0005
import Development.WeilBound.ThetaLifts.TowerModels.Bundle0007
import Development.WeilBound.ThetaLifts.TowerModels.Bundle0006

noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem planeEx : PlaneEx := ⟨planeHerm, planeSkew⟩

theorem pairEx (h : WeilPairExists) : PairEx := pairEx_of modelEx (weilEx_of h)

end PositivityTheory.ThKG.Tow

end
