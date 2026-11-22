import Development.WeilBound.ThetaLifts.TowerModels.Bundle0003
import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle0004
import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.Bundle0002
import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.ExistsFinitePlaceVacuumAnyDarbouxCoordinates
import Development.WeilBound.ThetaLifts.TowerModels.Bundle0002
import Development.WeilBound.ThetaLifts.TowerModels.Bundle0006

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.ModelEx
section
noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem modelEx : ModelEx := by
  intro F E _ _ _ _ _ σ B hB n d X W r s r' s' hX hW
  classical
  obtain ⟨co, hco⟩ := Tw.RatDarboux.exists_rational_darboux_of_isGood B hB X W r s r' s' hX hW
  obtain ⟨-, ⟨μ, 𝓕, hμ, h𝓕⟩, -⟩ := PositivityTheory.ThKF.unimodularity_holds F E σ hB.cm n X.J 1 (by simpa using hX.herm) (det_herm hX)
  have hS := Tw.VacIndic.eventually_isVac_indicator B hB X W r s r' s' hX hW co hco
  have hA := Tw.VacAny.exists_isVac_any_darboux B hB X W r s r' s' hX hW co
  let M₀ : Model σ X W := ⟨co, fun _ => 0, 0, ∅⟩
  let ind : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v =>
    Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let vac : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v =>
    if M₀.IsVac B.ψ v (ind v) then ind v else (hA v).choose
  refine ⟨⟨co, vac, μ, 𝓕⟩, ⟨hco, fun v => ?_, ?_, hμ, h𝓕⟩⟩
  · show M₀.IsVac B.ψ v (vac v)
    by_cases h : M₀.IsVac B.ψ v (ind v)
    · simp only [vac, if_pos h]; exact h
    · simp only [vac, if_neg h]; exact (hA v).choose_spec
  · filter_upwards [hS] with v hv
    show vac v = ind v
    exact if_pos hv

end PositivityTheory.ThKG.Tow

end
end

-- bundled from Development.WeilBound.ThetaLifts.TowerModels.PlaneSkew
section
noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem planeHerm : PlaneHerm := by
  intro F E _ _ _ _ _ σ B hB n n₁ hn hn₁ Y r s hr hs hY i₀ i₁ h01 h1n
  simp only [Pln.isHerm_iff] at hY ⊢
  exact Pln.exists_plane hB (Or.inl rfl) (by simp) (fun e => by simp) _ isIntegral_one
    (fun v => Pln.val_le_one_of_intE (B.τ v)) n n₁ hn hn₁ Y r s hr hs hY i₀ i₁ h01 h1n

theorem planeSkew : PlaneSkew := by
  intro F E _ _ _ _ _ σ B hB n n₁ hn hn₁ Y r s hr hs hY i₀ i₁ h01 h1n
  simp only [Pln.isSkew_iff] at hY ⊢
  exact Pln.exists_plane hB (Or.inr rfl) (by simp) (fun e => by simp) _ Pln.one_mem_codE
    (fun v => Pln.val_le_one_of_codE hB.cm hB.std (hB.psiP v v.2) (B.τ v)) n n₁ hn hn₁ Y r s hr hs hY i₀ i₁ h01 h1n

end PositivityTheory.ThKG.Tow

end
end

