import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0749
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0735
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0399
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationUnramifiedOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationPullbackOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0018
import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorLevelsUnramifiedStatement
import Formalism.SharpRestriction.LevelLetterCocycles.WachFrobeniusLatticeUnramifiedFunctor
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0025
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0751
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0473
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0744
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0041
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0057
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0408
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0333
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqZeroOfDiag
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0441
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0419
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0552
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimensionSaturationUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0702
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0628
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumEqConstMulPetersson
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsMulInfiniteAdelicGL
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem idemS_mul_sInf (S : Finset (HeightOneSpectrum (𝓞 E))) (x : Cinf E) : idemS S * sInf E x = sInf E x :=
  Prod.ext (one_mul _) (mul_zero _)

theorem one_sub_idemS_mul_sInf (S : Finset (HeightOneSpectrum (𝓞 E))) (x : Cinf E) :
    (1 - idemS S) * sInf E x = 0 := by
  rw [sub_mul, one_mul, idemS_mul_sInf, sub_self]

theorem prS_infGL (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (y : GL (Fin a) (Cinf E)) :
    prS S a (infGL E a y) = infGL E a y := by
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - idemS S * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j +
      idemS S * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
        sInf E (y i j)) =
    (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) + sInf E (y i j)
  rw [mul_add, mul_sub, idemS_mul_sInf, idemS_mul_sInf]
  ring

theorem prO_infGL (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (y : GL (Fin a) (Cinf E)) :
    prO S a (infGL E a y) = 1 := by
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (1 - idemS S) * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j +
      (1 - idemS S) * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
        sInf E (y i j)) =
    (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
  rw [mul_add, mul_sub, one_sub_idemS_mul_sInf, one_sub_idemS_mul_sInf]
  ring

theorem prS_prO_mul_infGL : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GA E a) (y : GL (Fin a) (Cinf E)),
    prS S a (g * infGL E a y) = prS S a g * infGL E a y ∧ prO S a (g * infGL E a y) = prO S a g := by
  intro E _ _ _ a S g y
  refine ⟨?_, ?_⟩
  · rw [map_mul, prS_infGL]
  · rw [map_mul, prO_infGL, mul_one]

end GlobalTheory.SchurExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsOnSupportedAtPlaces
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E]

theorem fst_idemS (S : Finset (HeightOneSpectrum (𝓞 E))) : (idemS S : Ad E).1 = 1 := rfl

open Classical in
theorem pLoc_pFin_idemS (S : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 E)) :
    pLoc E w (pFin E (idemS S)) = if w ∈ S then 1 else 0 := rfl

theorem prS_apply (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (g : GA E a) (i j : Fin a) :
    (prS S a g : Matrix (Fin a) (Fin a) (Ad E)) i j =
      (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - idemS S * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j +
        idemS S * (g : Matrix (Fin a) (Fin a) (Ad E)) i j := rfl

theorem prO_apply (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (g : GA E a) (i j : Fin a) :
    (prO S a g : Matrix (Fin a) (Fin a) (Ad E)) i j =
      (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (1 - idemS S) * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j +
        (1 - idemS S) * (g : Matrix (Fin a) (Fin a) (Ad E)) i j := rfl

theorem pLoc_pFin_idemS_of_not_mem {S : Finset (HeightOneSpectrum (𝓞 E))} {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ S) :
    pLoc E w (pFin E (idemS S)) = 0 := by
  classical
  rw [pLoc_pFin_idemS]; simp [hw]

theorem pLoc_pFin_one_sub_idemS_of_mem {S : Finset (HeightOneSpectrum (𝓞 E))} {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ S) :
    pLoc E w (pFin E (1 - idemS S)) = 0 := by
  classical
  rw [map_sub, map_sub, map_one, map_one, pLoc_pFin_idemS]; simp [hw]

theorem one_sub_idemS_mul_eq_zero {S : Finset (HeightOneSpectrum (𝓞 E))} {x : Ad E}
    (h : ∀ w ∉ S, pLoc E w (pFin E x) = 0) : (1 - idemS S) * x = 0 := by
  refine Prod.ext ?_ (Subtype.ext (funext fun w => ?_))
  · change (1 - (idemS S : Ad E).1) * x.1 = 0
    rw [fst_idemS, sub_self, zero_mul]
  · change pLoc E w (pFin E ((1 - idemS S) * x)) = pLoc E w (pFin E 0)
    rw [map_mul, map_mul, map_zero, map_zero]
    by_cases hw : w ∈ S
    · rw [pLoc_pFin_one_sub_idemS_of_mem hw, zero_mul]
    · rw [h w hw, mul_zero]

theorem pLoc_pFin_one_apply (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (i j : Fin a) :
    pLoc E w (pFin E ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j)) = (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j := by
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

theorem pLoc_pFin_apply_of_mem_supS {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))} {g : GA E a}
    (hg : g ∈ GlobalTheory.JSW.supS E a S) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ S) (i j : Fin a) :
    pLoc E w (pFin E ((g : Matrix (Fin a) (Fin a) (Ad E)) i j)) = (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j := by
  have h := congrArg (fun x : GL (Fin a) (w.adicCompletion E) => (x : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) (hg w hw)
  exact h

theorem one_sub_idemS_mul_sub_eq_zero {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))} {g : GA E a}
    (hg : g ∈ GlobalTheory.JSW.supS E a S) (i j : Fin a) :
    (1 - idemS S) * ((g : Matrix (Fin a) (Fin a) (Ad E)) i j - (1 : Matrix (Fin a) (Fin a) (Ad E)) i j) = 0 :=
  one_sub_idemS_mul_eq_zero fun w hw => by
    rw [map_sub, map_sub, pLoc_pFin_apply_of_mem_supS hg hw, pLoc_pFin_one_apply, sub_self]

theorem prS_prO_supS (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) :
    (∀ g ∈ GlobalTheory.JSW.supS E a S, prS S a g = g ∧ prO S a g = 1) ∧ ∀ g, prS S a g ∈ GlobalTheory.JSW.supS E a S := by
  refine ⟨fun g hg => ⟨?_, ?_⟩, fun g w hw => ?_⟩
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [prS_apply]
    linear_combination (-1 : Ad E) * one_sub_idemS_mul_sub_eq_zero hg i j
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [prO_apply]
    change _ = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
    linear_combination (one_sub_idemS_mul_sub_eq_zero hg i j)
  · refine Units.ext (Matrix.ext fun i j => ?_)
    change pLoc E w (pFin E ((prS S a g : Matrix (Fin a) (Fin a) (Ad E)) i j)) = (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j
    rw [prS_apply, map_add, map_sub, map_mul, map_mul, map_add, map_sub, map_mul, map_mul,
      pLoc_pFin_idemS_of_not_mem hw, pLoc_pFin_one_apply]
    ring

end GlobalTheory.SchurExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLProjectionsUpperUnitriangularGenericChar
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E]

theorem coe_cornerGL_idemHom_apply {R : Type} [CommRing R] {a : ℕ} (e : R) (he : IsIdempotentElem e)
    (g : GL (Fin a) R) (i j : Fin a) :
    ((cornerGL a (idemHom e he) g : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) i j =
      (1 : Matrix (Fin a) (Fin a) R) i j - e * (1 : Matrix (Fin a) (Fin a) R) i j + e * (g : Matrix (Fin a) (Fin a) R) i j :=
  rfl

theorem cornerGL_idemHom_mem_NA {a : ℕ} (e : Ad E) (he : IsIdempotentElem e) {u : GA E a}
    (hu : u ∈ GlobalTheory.JSW.NA E a) : cornerGL a (idemHom e he) u ∈ GlobalTheory.JSW.NA E a := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [coe_cornerGL_idemHom_apply, hu.1 i j hij, Matrix.one_apply_ne (ne_of_lt hij).symm]
    ring
  · rw [coe_cornerGL_idemHom_apply, hu.2 i, Matrix.one_apply_eq]
    ring

theorem cornerGL_idemHom_add_apply {R : Type} [CommRing R] {a : ℕ} (e : R) (he : IsIdempotentElem e)
    (g : GL (Fin a) R) {i j : Fin a} (hij : i ≠ j) :
    ((cornerGL a (idemHom e he) g : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) i j +
      ((cornerGL a (idemHom (1 - e) he.one_sub) g : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) i j =
      (g : Matrix (Fin a) (Fin a) R) i j := by
  rw [coe_cornerGL_idemHom_apply, coe_cornerGL_idemHom_apply, Matrix.one_apply_ne hij]
  ring

theorem superDiag_cornerGL_idemHom_add {R : Type} [CommRing R] {a : ℕ} (e : R) (he : IsIdempotentElem e)
    (g : GL (Fin a) R) :
    GlobalTheory.Whittaker.superDiag (cornerGL a (idemHom e he) g) +
      GlobalTheory.Whittaker.superDiag (cornerGL a (idemHom (1 - e) he.one_sub) g) = GlobalTheory.Whittaker.superDiag g := by
  unfold GlobalTheory.Whittaker.superDiag
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j.val = i.val + 1 := (Finset.mem_filter.1 hj).2
  have hij : i ≠ j := fun h => by rw [h] at hj'; omega
  exact cornerGL_idemHom_add_apply e he g hij

theorem prS_prO_NA_psiN :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
      ∀ u ∈ GlobalTheory.JSW.NA E a, prS S a u ∈ GlobalTheory.JSW.NA E a ∧ prO S a u ∈ GlobalTheory.JSW.NA E a ∧
        GlobalTheory.JSW.psiN (prS S a u) * GlobalTheory.JSW.psiN (prO S a u) = GlobalTheory.JSW.psiN u := by
  intro E _ _ _ a S u hu
  refine ⟨cornerGL_idemHom_mem_NA _ _ hu, cornerGL_idemHom_mem_NA _ _ hu, ?_⟩
  unfold GlobalTheory.JSW.psiN
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  exact congrArg (fun x => ((GroundTheory.Global.adelicChar E x : Circle) : ℂ))
    (superDiag_cornerGL_idemHom_add (idemS S) (isIdempotentElem_idemS S) u)

end GlobalTheory.SchurExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleConjugatePairPlacesEqOfTwistConditionAStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleConjugatePairPlaces_eq_of_twOK : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X),
  GlobalTheory.UnivChar.IsUnivChar Y → ∀ (i : X.Tw) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) → admissibleConjugatePairPlaces X i Q M = Q := by
  first | exact @GlobalTheory.AdmAll.admissibleConjugatePairPlaces_eq_of_twist_condition | exact GlobalTheory.AdmAll.admissibleConjugatePairPlaces_eq_of_twist_condition | (intros; apply GlobalTheory.AdmAll.admissibleConjugatePairPlaces_eq_of_twist_condition <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArcTheoremToolsOfWachModuleConclusions
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.ArcTools

theorem arc_tools_from_clauses :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      UnusedSlot80.SaturationArcLifting D HW F ∧ UnusedSlot80.SaturationEtale D HW F ∧ ArcLiftingSetup.SaturationFrobeniusPullback D HW F ∧ UnusedSlot80.GammaPreservesUniformiser D HW F ∧
      UnusedSlot80.KillerAtLevels D HW F ∧ UnusedSlot80.KillerBoundWithConstant D HW F 8 ∧ UnusedSlot80.KillerAtLevelsSecondForm D HW F ∧
      UnusedSlot80.FirstFiltrationArcLifting D HW F ∧ UnusedSlot80.FirstFiltrationEtale D HW F ∧ UnusedSlot80.SecondFiltrationArcLifting D HW F ∧ UnusedSlot80.SecondFiltrationEtale D HW F ∧
      UnusedSlot80.FiltrationPropertiesEtale D HW F Cm ∧ UnusedSlot80.H1fBaseChangeFree D := by
  intro D HW F Cm
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, c2, a, b, c, d, l3, pE⟩ := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  have hNat : HerrComplexNaturality.HerrNaturality D HW F :=
    HerrComplexNaturality.herr_naturality_theorem_holds D HW F (GlobalTheory.HerrFull.herr_part_a_every_record D HW F)
  have sA : UnusedSlot80.SaturationArcLifting D HW F := UnusedSlot80.saturation_general_statement D HW F ⟨p1, p9⟩
  have sE : UnusedSlot80.SaturationEtale D HW F := UnusedSlot80.saturation_unramified_statement D HW F ⟨p1, p9⟩
  have sP : ArcLiftingSetup.SaturationFrobeniusPullback D HW F := UnusedSlot80.saturation_pullback_statement D HW F p9
  have pi : UnusedSlot80.GammaPreservesUniformiser D HW F := UnusedSlot80.gamma_uniformizer_divisible_statement D HW F p9
  have kL : UnusedSlot80.KillerAtLevels D HW F := UnusedSlot80.annihilator_levels_unramified_statement D HW F Cm ⟨p4, p9⟩
  have kA : UnusedSlot80.KillerBoundWithConstant D HW F 8 := UnusedSlot80.killer_first_theorem_holds D HW F (le_refl _) ⟨kL, pi⟩
  have kE : UnusedSlot80.KillerAtLevelsSecondForm D HW F := UnusedSlot80.killer_second_theorem_holds D HW F pi
  have f1A : UnusedSlot80.FirstFiltrationArcLifting D HW F := UnusedSlot80.firstFiltrationTheoremCaseA D HW F ⟨p2, p5, p9, a, hNat⟩
  have f1E : UnusedSlot80.FirstFiltrationEtale D HW F := UnusedSlot80.firstFiltrationTheoremEtale D HW F ⟨p2, p5, p9, a, hNat⟩
  have f2A : UnusedSlot80.SecondFiltrationArcLifting D HW F := UnusedSlot80.second_filtration_theorem_arc_lifting D HW F ⟨⟨p7, p9, b⟩, f1A⟩
  have f2E : UnusedSlot80.SecondFiltrationEtale D HW F := UnusedSlot80.cohomology_class_unramified_statement D HW F ⟨⟨p7, p9, b⟩, f1E⟩
  have tE : UnusedSlot80.FiltrationPropertiesEtale D HW F Cm := UnusedSlot80.tools_unramified_statement D HW F Cm ⟨p3, p4, p9⟩
  have bc : UnusedSlot80.H1fBaseChangeFree D := UnusedSlot80.base_change_statement D
  exact ⟨sA, sE, sP, pi, kL, kA, kE, f1A, f1E, f2A, f2E, tE, bc⟩

end GlobalTheory.ArcTools
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangePartitionsPerm
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

noncomputable section

namespace GlobalTheory.BCPerm

theorem main : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (x : D.nd.X i)
    (P0 PI : D.naut.AV i) (Pa0 Pa : List (Part D.naut.CG)), D.naut.ptV i P0 = some x →
    D.naut.ptV i PI = some x → IsBCV D.nd D.naut i P0 Pa0 → IsBCV D.nd D.naut i PI Pa → Pa0.Perm Pa := by
  intro D ht h2 h5 i x P0 PI Pa0 Pa hx hx' hB0 hB
  have hG : GlobalTheory.RowTie.GalIso D.nd D.naut i := by
    intro P Pb hPb
    obtain ⟨ρ, hc, hss, hw⟩ := GlobalTheory.T.exists_galois_rep_base_change_twist D ht h2 i P Pb hPb
    exact ⟨ρ, hc, hss, fun w _ => (hw w).2⟩
  have hC : GlobalTheory.RowTie.ChebSplit D.nd := by
    intro S
    rw [dense_iff_closure_eq]
    exact h5.2.2.1 (S : Set (PlE D.host)) S.finite_toSet
  have hAN : GlobalTheory.RowCopy.IsobaricDiscreteSelfDualStrongMultiplicityOne D.nd D.naut := h5.2.1
  have hS := GlobalTheory.RowTie.splitBC_of_galIso D.R D.host D.what₂ D.nd D.naut i hG hC hAN
  have hd0 : (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) ≠ 0 := by
    split_ifs
    exacts [D.host.pde'_prime.ne_zero, D.host.pde_prime.ne_zero]
  have hfin : (placesOver D.host.E (D.nd.l i) ∪ (D.nd.S i : Set (PlE D.host)) ∪ (D.nd.Q i : Set (PlE D.host)) ∪
      placesOver D.host.E (D.host.g 0) ∪ placesOver D.host.E (D.host.g 1) ∪
      placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde)).Finite := by
    refine (((((GlobalTheory.RowTie.placesOver_finite_of_ne_zero _ _ (D.nd.lPrime i).out.ne_zero).union
      (D.nd.S i).finite_toSet).union (D.nd.Q i).finite_toSet).union
      (GlobalTheory.RowTie.placesOver_finite_of_ne_zero _ _ (D.host.g_prime 0).ne_zero)).union
      (GlobalTheory.RowTie.placesOver_finite_of_ne_zero _ _ (D.host.g_prime 1).ne_zero)).union
      (GlobalTheory.RowTie.placesOver_finite_of_ne_zero _ _ hd0)
  have hev : ∀ᶠ v in Filter.cofinite, IsSplitPl D.host v → D.naut.locV i P0 v = D.naut.locV i PI v := by
    rw [Filter.eventually_cofinite]
    refine hfin.subset fun v hv => ?_
    by_contra hn
    simp only [Set.mem_union, Finset.mem_coe, not_or] at hn
    obtain ⟨⟨⟨⟨⟨hl, hSv⟩, hQv⟩, hg0⟩, hg1⟩, hdv⟩ := hn
    refine hv fun hsp => GlobalTheory.RowTie.locV_eq_of_pt D.nd D.naut i hx hx' ⟨hsp, hl, hSv, hQv⟩ ?_ hdv
    intro k
    fin_cases k
    exacts [hg0, hg1]
  exact hS P0 PI hev Pa0 Pa hB0 hB

end GlobalTheory.BCPerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseCoverFramesDifferByRationalIsometryStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_cover_frames_differ_by_rational_isometry : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ h : GA D (T.V j σ), ∃ γ : GL (Fin D.R.r) D.host.E, (((T.U j σ).X (T.dict j σ h).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h).1).Λ : Set _) ∧ (∀ v w, herm ((T.U j σ).X (T.dict j σ h).1).Gm ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h).1).Gm v w) ∧ (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) := by
  first | exact @GlobalTheory.CoverFrameMove.frames_differ | exact GlobalTheory.CoverFrameMove.frames_differ | (intros; apply GlobalTheory.CoverFrameMove.frames_differ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BhattScholzeIntegral
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem bhattScholzeIntegral : GlobalTheory.Published.BhattScholzeIntegral := by
  intro l _ K P₀ e H
  obtain ⟨a, ha⟩ := GlobalTheory.T.etaleRealisation_indep_ainfModel l K P₀ e H
  refine ⟨?_, ?_⟩
  · intro P AI hstd V _ _ _ _ _ _ _ ρ L hc hcr
    obtain ⟨M, j₀, hj₀⟩ := GlobalTheory.T.crystallineLattice_prismaticFCrystal_perfectPrism l K P AI hstd V ρ L hc hcr
    obtain ⟨j, hj⟩ := ((ha M).2 ↥L.T (fun g => actT L g)).1 j₀ hj₀
    exact ⟨M, j, hj⟩
  · intro T T' _ _ _ _ ρ ρ' E E' j j' hj hj' f hf
    obtain ⟨j₀, hj₀, e₀⟩ := ((ha E).2 T ρ).2 j hj
    obtain ⟨j₀', hj₀', e₀'⟩ := ((ha E').2 T' ρ').2 j' hj'
    obtain ⟨u, hu⟩ := GlobalTheory.T.exists_FCrystalHom_of_equivariantEtaleMap_ainf l K T ρ T' ρ' E E' j₀ j₀' hj₀ hj₀' f hf
    refine ⟨u, fun x => ?_, fun u' hu' => ?_⟩
    · exact (e₀' _).symm.trans ((congrArg j₀' (u.u_tr a x).symm).trans
        ((hu _).trans (congrArg (f.lTensor (WCb l)) (e₀ x))))
    · refine GlobalTheory.T.fCrystalHom_eq_of_etale_realisation_perfectPrism l K T' ρ' E E' j₀' hj₀' u' u fun y => ?_
      obtain ⟨x, rfl⟩ := (ha E).1.2 y
      exact (congrArg j₀' (u'.u_tr a x)).trans ((e₀' _).trans ((hu' x).trans
        ((congrArg (f.lTensor (WCb l)) (e₀ x).symm).trans (hu _).symm)))

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoTopOfLocalTateDualityEulerChar
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TopClosing

theorem blochKatoTop_of_localTateDuality_eulerChar_alt : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), tableLineDegreeTwo.aux₃ D HW F := by
  intro _ hdual heul D HW F Cm
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, -, hE⟩ :
      Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  obtain ⟨a23, a24⟩ := tableLineDegreeTwo.ainf_clauses_of_theorem D HW F hE
  have hA : Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F := GlobalTheory.HerrFull.herr_part_a_every_record D HW F
  have hFN : Formalism.MainNotions.HerrComplexNaturality.FN D HW F := GlobalTheory.Decompl.fontaine_and_decompletion D HW F
  have a16 : tableLineDegreeTwo.adm16 D HW F :=
    Formalism.MainNotions.InvariantsGenerators.herr_lattice_of_fon D HW F ⟨hA, GlobalTheory.T.invariants_statement_holds D HW F hFN, GlobalTheory.T.fontaine_fullFaithful_exact_psi D HW F⟩
  have a17 : tableLineDegreeTwo.adm17 D HW F :=
    (Formalism.MainNotions.InvariantsGenerators.herr_lattice_rest_iff D HW F).2
      ⟨GlobalTheory.EtaleSub.exists_lattice_of_pow_mem D HW F, GlobalTheory.ExtDict.extension_rule D HW F⟩
  have a21 : tableLineDegreeTwo.adm21 D HW F := GlobalTheory.SenMult.stmtSen D HW F Cm ⟨a2, a4, a5, a9, a11⟩
  exact GlobalTheory.TopBridge.twistedLatticeCohomology_theoremTOP D HW F Cm
    ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, ⟨hdual, heul⟩,
      GlobalTheory.FiltrationJumpMultiplicity.blochKato_dimension_saturation_unramified D, GlobalTheory.T.crystalline_characters_given_jumps_unramified_twists D HW F, a21, GlobalTheory.CrysFormalism.crysLit_all D, a23, a24⟩

end GlobalTheory.TopClosing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDiagGLMemAdelicGLSupportedAtFinitePlaces
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

theorem blockGL_mem_supS : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∀ h ∈ GlobalTheory.JSW.supS E (m + 1) S, GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h ∈ GlobalTheory.JSW.supS E (m + r + 1 + 1) S := by
  intro E _ _ m r S h hh w hw
  have hmap : Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E))
      (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h) =
      GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1)
        (Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) h) :=
    Units.ext (GroundTheory.Automorphic.FourierWhittaker.map_blockMat _ _ (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)))
  rw [hmap, hh w hw, map_one]

end GlobalTheory.SchurExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumEqConstMulPeterssonStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.class_sum_eq_const_mul_petersson : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ), IsInvForm a β → ∃ B, IsPetersson a B ∧ ∀ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (T : Finset (GAf L n)), IsBounded J → (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → IsClassReps J T → ∃ c : ℝ, 0 < c ∧ ∀ f ∈ NG.TypeSp a.ρ J χ, ∀ f' ∈ NG.TypeSp a.ρ J χ, classSum a β J T f f' = (c : ℂ) * B f f' := by
  first | exact @GlobalTheory.ClassPet.classSum_eq_pet | exact GlobalTheory.ClassPet.classSum_eq_pet | (intros; apply GlobalTheory.ClassPet.classSum_eq_pet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionIsoSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_iso_split_place : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (S : Reading P.T), IsTrue P S → ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = D.naut.plGw k v → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ F ∈ D.naut.typeV i PI, ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) = GlobalTheory.BlockType.blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • (P.M.loc i).real F := by
  first | exact @GlobalTheory.TypeVecEig.main | exact GlobalTheory.TypeVecEig.main | (intros; apply GlobalTheory.TypeVecEig.main <;> assumption)
end

