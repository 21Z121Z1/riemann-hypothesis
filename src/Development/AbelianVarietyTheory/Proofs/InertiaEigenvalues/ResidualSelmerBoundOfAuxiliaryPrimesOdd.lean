import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleFormsSpanOddResidueChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanTwoOfGaloisHypothesis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerFinrankEqDual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstHalfLocalCohomologyVanishingOfLocalDualityT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReciprocityAuxiliaryPlacesSecondHalf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliaryPrimesPrescribedFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerDeterminantOrderBoundStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsElementsSelmerFormsSmallCorank
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualBoundOfComponents

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ResSel

theorem residual_bound_of_parts : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → GreenbergWiles → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), ResidualBoundOddPrimes bkP := by
  intro hC hPT hCD hT hLF hLT hLE hGF hGE hU hA _ D N X bkP
  have hgw : ∀ i s, GalHyp bkP i s → EqDim bkP i s := fun i s h =>
    _root_.GlobalTheory.ResDual.eqDim hC hPT hCD hT hLF hLT hLE hGF hGE hU hA D N X bkP i s h
  refine _root_.GlobalTheory.ResSel.OddBound.residual_bound_of_parts D N X bkP (fun i => _root_.GlobalTheory.ChosenPrimes.stepAB hC D N X i)
    (fun i => _root_.GlobalTheory.ChooseForms.chooseH hGF D N X bkP i fun s h =>
      ⟨_root_.GlobalTheory.ResSel.SpanOddPf.spanOdd D N X bkP i s h, _root_.GlobalTheory.ResSel.AltSpan.spanTwo_of_galHyp D N X bkP i s h, hgw i s h⟩)
    (fun i s h => ?_)
  have hk := _root_.GlobalTheory.ScalarFrob.firstHalf hLF hLT hLE hT D N X bkP i s h
  exact GlobalTheory.T.residual_selmer_determinant_order_bound hT D N X bkP i s h hk
    (_root_.GlobalTheory.ResRecip.reciprocity hC hPT hCD hT hLF hLT hLE hGF hGE hU hA D N X bkP i s h hk) (hgw i s h)

end GlobalTheory.ResSel
