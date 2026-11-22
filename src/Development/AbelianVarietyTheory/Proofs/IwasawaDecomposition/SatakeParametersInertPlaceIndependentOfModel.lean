import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GEquivIntL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeAlgebraCompUnitaryGroupAntidiagTransportMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryTorusUnipotentCosetTransportIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitarySatakeInvariantAntidiagTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertHeckeOperatorIndepOfInertDatum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertSatakeParametersEqOfIsoStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

namespace GlobalTheory.SatInd

theorem satAt_indep : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π π' : NG.AutRep L n), π.Iso π' → ∀ v w, NG.OverPl w v → ∀ (Dv Dv' : InertDatum L n v w) α, NG.SatAt π Dv α → NG.SatAt π' Dv' α := by
  intro L _ _ _ n π π' hiso v w _ Dv Dv' α hsat
  have h1 : NG.SatAt π Dv' α := by
    obtain ⟨f, hfS, hf0, U, hU, hUv, hH⟩ := hsat
    refine ⟨f, hfS, hf0, U, hU, hUv, fun h' hh' => ?_⟩
    have hm : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
    rw [_root_.GlobalTheory.SatInd.heckeFunI_indepDatum L n v w Dv Dv' U _ h' hh'.1 f,
      hH _ (_root_.GlobalTheory.SatInd.guMap_hecke_comap (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') n h' hh'),
      _root_.GlobalTheory.SatInd.satU_guMap (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') Dv.ϖ Dv'.ϖ _ n (n / 2) h' hh'.1
        (_root_.GlobalTheory.SatInd.cosetT_iff (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') Dv.ϖ Dv'.ϖ _ _ n (n / 2)
          Dv.unram Dv'.unram hm)]
  exact GlobalTheory.T.inertSatakeParameters_eq_of_iso L n π π' hiso v w Dv' α
    (_root_.GlobalTheory.SatInd.CosetFin.finite_inert_support L n v w Dv' (_root_.GlobalTheory.SatInd.DCoset.finite_dcoset Dv'.ϖ Dv'.σw _ n Dv'.unram) (_root_.GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv')) h1

end GlobalTheory.SatInd
