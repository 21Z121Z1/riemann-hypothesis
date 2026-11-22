import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0746
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0352
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0745
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0373
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0747
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0749
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1294
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.SatakeDualWeyl.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0733
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0748

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelFullAtInertPlacePrincipalElsewhereStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_full_at_inert_place_principal_elsewhere : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (N : ℕ), 0 < N → ∃ U : Subgroup (GAf L n), (∀ κ, NG.Cong L n N κ → κ ∈ U) ∧ (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) ∧ ∀ κ ∈ U, ∃ a b : GAf L n, κ = a * b ∧ a ∈ Umax L n ∧ TrivOutside {v} a ∧ NG.Cong L n N b ∧ ∀ x : GAf L n, TrivOutside {v} x → b * x = x * b := by
  first | exact @GlobalTheory.InertLevel.exists_level | exact GlobalTheory.InertLevel.exists_level | (intros; apply GlobalTheory.InertLevel.exists_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalExtensionOfFiniteIndexWeilSubgroupStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localExtension_of_finiteIndex_weilSubgroup : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (H : Subgroup (Weil h)), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∃ (L : IntermediateField E Ω), FiniteDimensional E L ∧ IsLocalExt L h ∧ ∀ σ : Weil h, σ ∈ H ↔ ∀ x : L, (σ : G E Ω) (x : Ω) = x := by
  first | exact @GlobalTheory.LocalExtField.exists_localExt_of_finiteIndex | exact GlobalTheory.LocalExtField.exists_localExt_of_finiteIndex | (intros; apply GlobalTheory.LocalExtField.exists_localExt_of_finiteIndex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenNhdOneInUnitaryPrincipalCongruenceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_nhd_one_in_unitary_principal_congruence : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (N : ℕ), 0 < N → ∃ O : Set (finU L n), IsOpen O ∧ (1 : finU L n) ∈ O ∧ ∀ k ∈ O, ∀ x : GAf L n, F.j x = (k : UA L n) → NG.Cong L n N x := by
  first | exact @GlobalTheory.CongOpen.exists_open_cong | exact GlobalTheory.CongOpen.exists_open_cong | (intros; apply GlobalTheory.CongOpen.exists_open_cong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatUEigenvectorStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_satU_eigenvector_alt : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K) (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (T : (Formalism.UG.GU σ n → ℂ) → Module.End ℂ V), (∀ h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), ∀ h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (h₁ + h₂) = T h₁ + T h₂) → (∀ (c : ℂ), ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (c • h) = c • T h) → T (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) 1) = 1 → (∀ h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), ∀ h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (Formalism.UG.conv (Formalism.UG.KU σ n) h₁ h₂) = T h₁ * T h₂) → ∀ x₀ : V, x₀ ≠ 0 → ∃ α : Fin (n / 2) → ℂ, ∃ x : V, x ≠ 0 ∧ ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T h x = Formalism.UG.SatU ϖ q h α • x := by
  first | exact @GlobalTheory.HeckeSatakeEigen.exists_satU_eigenvector | exact GlobalTheory.HeckeSatakeEigen.exists_satU_eigenvector | (intros; apply GlobalTheory.HeckeSatakeEigen.exists_satU_eigenvector <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterOfUnramifiedInertDefiniteUn
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertSatakeGiven

theorem continuous_of_valuation_eq {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (s : K →+* K) (hs : ∀ x, Valued.v (s x) = Valued.v x) : Continuous s := by
  have h : Filter.Tendsto s (nhds 0) (nhds 0) := by
    rw [(Valued.hasBasis_nhds_zero K Γ₀).tendsto_iff (Valued.hasBasis_nhds_zero K Γ₀)]
    intro γ _
    refine ⟨γ, trivial, fun x hx => ?_⟩
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
    rwa [hs]
  exact continuous_of_continuousAt_zero s (by simpa [ContinuousAt] using h)

theorem exists_hasSatAt : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (w : HeightOneSpectrum (𝓞 L)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal → ¬ IsSplitAt w → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → IsUnramU U w → ∃ α0 : Fin (n / 2) → ℂˣ, HasSatAt U w s ϖ q α0 := by
  intro L _ _ _ n U hU w hun hns s ϖ q hs hI hph
  have hsph : (GlobalTheory.DefU.AU.mk ⟨U, hU⟩).Sph w := (GlobalTheory.DefU.AU.sph_mk _ w).2 hph
  obtain ⟨α0, hα⟩ := (GlobalTheory.T.definiteUnitary_spherical_iff_hasSatake_inert L n _ w hun hns).1 hsph
  rw [GlobalTheory.DefU.AU.isSat_mk] at hα
  obtain ⟨s', ϖ', q', hs', hI', hsat⟩ := hα
  have hss : s' = s := by
    apply DFunLike.coe_injective
    refine (HeightOneSpectrum.denseRange_algebraMap L w).equalizer (continuous_of_valuation_eq s' hI'.2.1)
      (continuous_of_valuation_eq s hI.2.1) (funext fun k => ?_)
    simp only [Function.comp_apply, hs', hs]
  subst hss
  have hqq : q' = q := Nat.pow_left_injective (n := 2) (by norm_num) (hI'.2.2.2.2.2.2.symm.trans hI.2.2.2.2.2.2)
  subst hqq
  obtain ⟨b, hb, hbJ, p, hp, σ, hc, hS⟩ := hsat
  exact ⟨α0, b, hb, hbJ, p, hp, σ, hc, hS.1, fun x hx h0 => (hS.2 x hx h0).of_unif hI' hI⟩

end GlobalTheory.InertSatakeGiven

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeparatingCharacterConjugateHalfSplitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separating_character_conjugate_half_split : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (ϖ : OI v), Irreducible ϖ → ∀ (N : ℕ) (x : WO S T), IsHalf (cA D e) x → ¬ InPow ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) x) → ∃ y, IsHalf e y ∧ (∀ z ∈ halfPow φ S T (frCo φ βS) (frCo φ βT) e ϖ N, ψ (symplO S T z y) = 1) ∧ ψ (symplO S T x y) ≠ 1 := by
  first | exact @GlobalTheory.DownLift.GenSplit.exists_sep_char | exact GlobalTheory.DownLift.GenSplit.exists_sep_char | (intros; apply GlobalTheory.DownLift.GenSplit.exists_sep_char <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothWhittakerBumpAdelicGL
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump in

theorem GlobalTheory.WhitBump.exists_bump_glob : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ b : GA E (a + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA E (a + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (a + 1)), IsCompact C ∧ ∀ p, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (a + 1), u⁻¹ * p ∈ C) ∧ (∃ U : Subgroup (GL (Fin (a + 1)) (Af E)), IsOpen (U : Set (GL (Fin (a + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (a + 1) u) = b g) ∧ ∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (a + 1)) := by
  intro E _ _ _ m
  obtain ⟨f, hf, hfc, hfs, hf1⟩ := exists_bumpInf_ne (E := E) (n := m + 1)
  obtain ⟨h1, hN, hK, hsupp⟩ := bumpFin_spec (E := E) (n := m + 1) fun u hu hk => psiFin_integral u hu hk
  set c := bumpInf f (oneL E (m + 1)) with hc
  let pI : GA E (m + 1) → GL (Fin (m + 1)) (Cinf E) := fun g => GeneralLinearGroup.map (pInf E) g
  let pF : GA E (m + 1) → GL (Fin (m + 1)) (Af E) := fun g => GeneralLinearGroup.map (pFin E) g
  refine ⟨fun g => bumpInf f (toL (pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) / c * bumpFin (pF g),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [pI, pF, map_one, Units.val_one, h1, mul_one]
    exact div_self hf1
  · intro u hu g
    simp only [pI, pF, map_mul, Units.val_mul]
    have e := bumpInf_mul f _ (pInf_mem_unipB hu) (toL ((GeneralLinearGroup.map (pInf E) g : GL (Fin (m + 1)) (Cinf E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)))
    erw [e]
    rw [hN _ (pFin_mem_unipB hu), psiN_eq]
    ring
  · let T := tsupport f
    let C : Set (GA E (m + 1)) := (fun q : GL (Fin (m + 1)) (Cinf E) × GL (Fin (m + 1)) (Af E) =>
      infGL E (m + 1) q.1 * finGL E (m + 1) q.2) ''
        ({y : GL (Fin (m + 1)) (Cinf E) | toL (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) ∈ T} ×ˢ
          (GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E (m + 1) : Set (GL (Fin (m + 1)) (Af E))))
    refine ⟨C, ?_, ?_⟩
    · refine ((isCompact_setOf_toL T hfc hfs).prod
        (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E (m + 1))).image ?_
      exact ((GlobalTheory.ConstTermSmooth.continuous_infGL).comp continuous_fst).mul
        (continuous_finGL_bump.comp continuous_snd)
    · intro p hp
      have hI : bumpInf f (toL (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) ≠ 0 := by
        intro h; apply hp; simp only [h, zero_div, zero_mul]
      have hF : bumpFin (pF p) ≠ 0 := by
        intro h; apply hp; simp only [h, mul_zero]
      obtain ⟨t, ht⟩ : ∃ t, f (toL (nu t * Matrix.of (toL (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))))) ≠ 0 := by
        by_contra hall
        push_neg at hall
        have hall' : ∀ t, f (toL (nu t * (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)))) = 0 := hall
        apply hI
        unfold bumpInf
        simp [hall']
      obtain ⟨uf, huf, hk⟩ := hsupp _ hF
      refine ⟨infGL E (m + 1) (nuGL t)⁻¹ * finGL E (m + 1) uf,
        mem_NA_of (inv_mem (nuGL_mem t)) huf, ⟨(nuGL t * pI p, uf⁻¹ * pF p), ⟨?_, hk⟩, ?_⟩⟩
      · exact subset_tsupport f ht
      · refine ga_ext ?_ ?_ <;> simp [pI, pF]
  · refine ⟨GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E (m + 1),
      GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E (m + 1), fun k hk g => ?_⟩
    simp only [pI, pF, map_mul, pInf_finGL, pFin_finGL, mul_one]
    rw [hK k hk]
  · intro g
    have hsm := contDiffOn_bumpInf f hf hfc hfs
    set L := lmul (toL (pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) with hL
    have hmaps : Set.MapsTo L (invSet E (m + 1)) (invSet E (m + 1)) := fun x hx => by
      have hx' : IsUnit (Matrix.of x) := hx
      change IsUnit ((pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) * Matrix.of x)
      exact (pI g).isUnit.mul hx'
    have h2 : ContDiffOn ℝ ∞ (fun x : Lie E (m + 1) => bumpInf f (L x)) (invSet E (m + 1)) :=
      hsm.comp (L.contDiff.contDiffOn) hmaps
    have hl : ContDiffOn ℝ ∞ (fun x : Lie E (m + 1) => bumpInf f (L x) / c * bumpFin (pF g))
        (invSet E (m + 1)) := (h2.div_const c).mul contDiffOn_const
    refine hl.congr fun x hx => ?_
    have hx' : IsUnit (Matrix.of x) := hx
    rw [chart, dif_pos hx']
    simp only [pI, pF, map_mul, pInf_infGL, pFin_infGL, mul_one, Units.val_mul, IsUnit.unit_spec]
    rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitaryRationalMatrixOfFirstPresentationPoStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_rational_matrix_of_first_presentation_point : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (γQ : GQ L n), ∃ (γ : UA L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ ∧ (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom := by
  first | exact @GlobalTheory.RatPtsBridge.exists_ratGL | exact GlobalTheory.RatPtsBridge.exists_ratGL | (intros; apply GlobalTheory.RatPtsBridge.exists_ratGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeilRepGoodTwist
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilTwistExists

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isHeckeChar_mul' {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) (h' : IsHeckeChar D χ') :
    IsHeckeChar D (χ * χ') :=
  ⟨h.1.mul h'.1, fun x => by rw [MonoidHom.mul_apply, h.2 x, h'.2 x, mul_one]⟩

theorem isHeckeChar_inv' {χ : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ :=
  ⟨h.1.inv, fun x => by rw [MonoidHom.inv_apply, h.2 x, inv_one]⟩

theorem resEta_zero_of_real {χ ξ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D ξ n) (hr : ∀ a, χ (idF D a) = 1) :
    ResEta D χ 0 :=
  ⟨h.1, fun η _ a => by rw [hr, pow_zero]⟩

theorem exists_isWeil : ∀ (D : D7) (S T : HSp D) (B : Base S T), GlobalTheory.Published.WeilRepresentationUnitaryPair → B.Good →
    IsStdChar D B.F.ψ (-1) → ∀ t : Twist D Circle, t.Good → ∃ ω, B.IsWeil t.chi ω := by
  intro D S T B hW hB hψ t ht
  have hEta : ResEta D B.eta 1 := hB.eta.2.2.1
  have h0 : ResEta D (B.mu * t.chi) 0 := by
    refine resEta_zero_of_real hEta fun a => ?_
    rw [MonoidHom.mul_apply, Base.mu, MonoidHom.mul_apply, hB.real, ht.real, hB.de.real, one_mul, one_mul]
  have hH : IsHeckeChar D (B.mu * t.chi) :=
    isHeckeChar_mul' (isHeckeChar_mul' hB.hecke hB.de.isHeckeChar) ht.isHeckeChar
  have hS : ResEta D (B.mu * t.chi) S.rank :=
    Formalism.L2.Theta.resEta_parity h0 (by rw [Nat.even_iff.1 hB.even])
  have hT : ResEta D (B.mu * t.chi * B.eta⁻¹) T.rank := by
    have h1 := Formalism.L2.Theta.resEta_mul h0 (Formalism.L2.Theta.resEta_inv hEta)
    exact Formalism.L2.Theta.resEta_parity h1 (by rw [Nat.odd_iff.1 hB.odd])
  exact hW D B.F.ψ S T _ _ hψ hH (isHeckeChar_mul' hH (isHeckeChar_inv' hB.eta.1)) hS hT

end GlobalTheory.WeilTwistExists

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlaceSplitIdempotentOrInertStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_place_split_idempotent_or_inert : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D), IsFinIdem D v f → (∃ e, Formalism.L2.Theta.IsSplitIdem D e ∧ e + Formalism.L2.Theta.cA D e = f) ∨ (∃ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.UG.IsInertAt D.host.F D.host.E v w) := by
  first | exact @GlobalTheory.PlaceDichotomy.split_or_inert_idem | exact GlobalTheory.PlaceDichotomy.split_or_inert_idem | (intros; apply GlobalTheory.PlaceDichotomy.split_or_inert_idem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameBaseEqCoverFrameMovedByArithmetic
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.CoverFrameArith

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem arch_rat {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r) (ρ : GA D V) (hρ : ρ ∈ GQ V) :
    ∃ R : GL (Fin r) D.host.E, ∀ (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ),
      Formalism.MainNotions.StandardLattice.IsInfEmb τ θ → ∀ u : GA D V,
        Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (ρ * u)) =
          (R : Matrix (Fin r) (Fin r) D.host.E).map τ * Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ u) := by
  subst hr
  obtain ⟨R, -, -, hRa⟩ := GlobalTheory.MarkCoset.rational_matrix V ρ hρ
  have hre : ∀ m : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) m = m := fun m => by
    ext i j
    rfl
  refine ⟨R, fun τ θ hθ u => ?_⟩
  rw [hre, hre, archM, archM, map_mul, Units.val_mul, Matrix.map_mul, ← archM, hRa τ θ hθ]

theorem mulVec_add_nsmul {A : Type} [CommRing A] {n : ℕ} (m : Matrix (Fin n) (Fin n) A) (N : ℕ) (y y' : Fin n → A) :
    m *ᵥ (y + N • y') = m *ᵥ y + N • (m *ᵥ y') := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul]

set_option maxHeartbeats 1000000 in

theorem conj_move {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r) (δa g₀ κ : GA D V) (hδ : δa ∈ GQ V) (N : ℕ)
    (hN : N ≠ 0) (hκ : ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V κ).1.mulVec z - z = N • y)
    (hκ' : ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V κ⁻¹).1.mulVec z - z = N • y)
    (he : finHom V (g₀⁻¹ * δa * g₀) = finHom V κ) (L : Submodule (𝓞 D.host.E) (Fin r → D.host.E))
    (hL : (L : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V g₀ : Set _))
    (G : Matrix (Fin r) (Fin r) D.host.E) (hG : G = -(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) :
    ∃ Δ : GL (Fin r) D.host.E,
      (∀ v w, herm G ((Δ : Matrix (Fin r) (Fin r) D.host.E) *ᵥ v) ((Δ : Matrix (Fin r) (Fin r) D.host.E) *ᵥ w) =
        herm G v w) ∧
      (∀ v, v ∈ L ↔ (Δ : Matrix (Fin r) (Fin r) D.host.E) *ᵥ v ∈ L) ∧
      (∀ v ∈ L, ∃ u ∈ L, (Δ : Matrix (Fin r) (Fin r) D.host.E) *ᵥ v = v + N • u) ∧
      ∀ (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), Formalism.MainNotions.StandardLattice.IsInfEmb τ θ →
        ∀ u : GA D V, Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (δa * u)) =
          (Δ : Matrix (Fin r) (Fin r) D.host.E).map τ * Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ u) := by
  subst hr
  have hgr : Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) V.gram = V.gram := by
    ext i j
    rfl
  have hre : ∀ m : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) m = m := fun m => by
    ext i j
    rfl
  rw [hgr] at hG
  obtain ⟨Δ, hΔu, hΔf, hΔa⟩ := GlobalTheory.MarkCoset.rational_matrix V δa hδ
  have hmem : ∀ v, v ∈ L ↔ finVec V v ∈ latGHat V g₀ := fun v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D V _).1, ← SetLike.mem_coe, hL]
    exact Set.ext_iff.1 (Set.image_id _) v
  have hfh : finHom V (δa * g₀ * κ⁻¹) = finHom V g₀ := by
    have e : δa * g₀ * κ⁻¹ = g₀ * (g₀⁻¹ * δa * g₀) * κ⁻¹ := by group
    rw [e, map_mul, map_mul, he, map_inv, mul_inv_cancel_right]
  have hLh : latGHat V (δa * g₀ * κ⁻¹) = latGHat V g₀ := by
    unfold latGHat gLat
    rw [hfh]
  obtain ⟨ht1, -⟩ := GlobalTheory.MarkCoset.transport (finHom V) (latGHat V) (fun g => (GlobalTheory.MarkCoset.latG_spec D V g).2) N
    δa g₀ κ⁻¹ (GlobalTheory.MarkCoset.level_latGHat V N κ⁻¹ hκ')
    (by rw [inv_inv]; exact GlobalTheory.MarkCoset.level_latGHat V N κ hκ)
  rw [hLh] at ht1
  refine ⟨Δ, fun v w => by rw [hG]; exact hΔu v w, fun v => by rw [hmem, hmem, ← hΔf]; exact ht1 _,
    fun v hv => ?_, fun τ θ hθ u => ?_⟩
  · obtain ⟨y, hy, hyz⟩ := ((GlobalTheory.MarkCoset.latG_spec D V g₀).2 _).1 ((hmem v).1 hv)
    obtain ⟨y', hy', ey⟩ := GlobalTheory.MarkCoset.level_latGHat V N κ hκ y hy
    have hc : (finHom V δa).1 *ᵥ ((finHom V g₀).1 *ᵥ y) = (finHom V g₀).1 *ᵥ ((finHom V κ).1 *ᵥ y) := by
      rw [← he, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul,
        show g₀ * (g₀⁻¹ * δa * g₀) = δa * g₀ by group]
    have hs : finVec V ((Δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v - v) =
        finVec V ((Δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) - finVec V v := by
      funext i
      simp only [finVec, Pi.sub_apply, TensorProduct.tmul_sub]
    have key : finVec V ((Δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v - v) =
        N • ((finHom V g₀).1 *ᵥ y') := by
      rw [hs, ← hΔf, ← hyz, hc, ey, mulVec_add_nsmul, add_sub_cancel_left]
    obtain ⟨w, hw, e⟩ := GlobalTheory.MarkCoset.finVec_div V N hN _ _ key
    refine ⟨w, (hmem w).2 ?_, sub_eq_iff_eq_add'.1 e⟩
    rw [hw]
    exact ((GlobalTheory.MarkCoset.latG_spec D V g₀).2 _).2 ⟨y', hy', rfl⟩
  · rw [hre, hre, archM, archM, map_mul, Units.val_mul, Matrix.map_mul, ← archM, hΔa τ θ hθ]

set_option maxHeartbeats 4000000 in

theorem frame_move_arith : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (h h₀ : GA D (T.V j σ)), (C.dict₂ h).1 = (C.dict₂ h₀).1 → ∀ γ₀ : GL (Fin D.R.r) D.host.E, (((T.U j σ).X (T.dict j σ h₀).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h₀).1).Λ : Set _) → (∀ v w, herm ((T.U j σ).X (T.dict j σ h₀).1).Gm ((γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h₀).1).Gm v w) → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h₀).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h₀).1).Ψ), mat (T.dict j σ h₀).2 ⟨τ, h₁⟩ = (γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h₀).2 ⟨τ, h₂⟩) → ∃ δ ∈ ((T.U j σ).X (T.dict j σ h).1).Γ, ∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * ((γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) := by
  intro D T hT j hj σ hσ C hC h h₀ hh γ₀ _ _ hfr0
  have hk : (T.dict j σ h).1 = (T.dict j σ h₀).1 :=
    GlobalTheory.CoverRead.CompIndep.comp_eq_of_cover D T hT j hj σ hσ C hC h h₀ hh
  obtain ⟨hr₁, g₁, e₁, F₁, ik₁, φ₁, th₁, hι, -, hth₁, -, hd₁⟩ := hT.adPin j hj σ hσ
  obtain ⟨⟨-, hMl, -, hIl, -⟩, -, -, hU₂, hdom, hr₂, g₂, e₂, F₂, ik₂, φ₂, th₂, -, hth₂, -, hd₂⟩ := hC
  obtain ⟨hr₀, hW₁⟩ := hT.modelW j hj σ hσ
  have hU₁ := hT.unf j hj σ hσ
  have hK := hT.levelK j hj σ hσ
  rw [← hT.pins.2.1.1] at hK
  obtain ⟨γ₁, hγ₁, hL₁, hm₁, hf₁⟩ := hd₁ h
  obtain ⟨γ₁', hγ₁', hL₁', hm₁', hf₁'⟩ := hd₁ h₀
  obtain ⟨γ₂, hγ₂, hL₂, hm₂, hf₂⟩ := hd₂ h
  obtain ⟨γ₂', hγ₂', hL₂', hm₂', hf₂'⟩ := hd₂ h₀

  obtain ⟨M₀, hM₀⟩ := arch_rat (T.V j σ) hr₁ (γ₁' * γ₂'⁻¹) (mul_mem hγ₁' (inv_mem hγ₂'))
  have hΨ : ∀ (g : GA D (T.V j σ)) τ, τ ∈ ((T.U j σ).X (T.dict j σ g).1).Ψ ↔ τ ∈ (C.U₂.X (C.dict₂ g).1).Ψ :=
    fun g τ => ((hU₁.2.1 _).2 τ).trans ((hU₂.2.1 _).2 τ).symm
  have hM0eq : (M₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) = γ₀ := by
    obtain ⟨τ, t₂⟩ : ∃ τ, τ ∈ (C.U₂.X (C.dict₂ h₀).1).Ψ := by
      by_cases h0 : D.host.φ₀ ∈ (C.U₂.X (C.dict₂ h₀).1).Ψ
      · exact ⟨_, h0⟩
      · exact ⟨_, not_not.1 (mt ((C.U₂.X (C.dict₂ h₀).1).cmType _).2 h0)⟩
    have t₁ := (hΨ h₀ τ).2 t₂
    have a₁ := hf₁' ⟨τ, t₁⟩
    have a₂ := hf₂' ⟨τ, t₂⟩
    rw [GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth₂ _ ⟨τ, t₂⟩) (hth₁ _ ⟨τ, t₁⟩)] at a₂
    have e : γ₁' * h₀ = γ₁' * γ₂'⁻¹ * (γ₂' * h₀) := by group
    rw [e, hM₀ τ _ (hth₁ _ ⟨τ, t₁⟩), Matrix.mul_assoc, ← a₂] at a₁
    have a₃ := (hfr0 τ t₂ t₁).symm.trans a₁
    have hu : IsUnit (mat (C.dict₂ h₀).2 ⟨τ, t₂⟩) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit (hdom h₀ ⟨τ, t₂⟩).1)
    exact (Matrix.map_injective τ.injective (hu.mul_right_cancel a₃)).symm

  rw [← hk] at hL₁' hm₁'
  rw [← hh] at hL₂' hm₂'
  have hinj : ∀ hr : (T.V j σ).rank = D.R.r,
      Function.Injective (fun v : Fin (T.V j σ).rank → D.host.E => v ∘ Fin.cast hr.symm) := fun hr u v huv =>
    funext fun i => congrFun huv (Fin.cast hr i)
  have hLb : latG (T.V j σ) (γ₁' * h₀) = latG (T.V j σ) (γ₁ * h) :=
    SetLike.coe_injective ((hinj hr₁).image_injective (hL₁'.symm.trans hL₁))
  have hLc : latG (T.V j σ) (γ₂ * h) = latG (T.V j σ) (γ₂' * h₀) :=
    SetLike.coe_injective ((hinj hr₂).image_injective (hL₂.symm.trans hL₂'))

  obtain ⟨a₁, ha₁, k₁, hk₁, eak₁⟩ := (GlobalTheory.UnitarySplit.real_finite_split D (T.V j σ)).1 ((γ₁' * h₀)⁻¹ * (γ₁ * h))
  obtain ⟨a₂, ha₂, k₂, hk₂, eak₂⟩ := (GlobalTheory.UnitarySplit.real_finite_split D (T.V j σ)).1 ((γ₂ * h)⁻¹ * (γ₂' * h₀))
  have hk₁K : k₁ ∈ T.Kf j σ := by
    refine (hT.kfHalf j hj σ hσ k₁).2 ⟨hk₁, ?_⟩
    have hmA := hm₁'
    have hmB := hm₁
    rw [show (T.Q.l.M : ℕ) = T.Q.l.M * 1 from (mul_one _).symm] at hmA hmB
    exact GlobalTheory.CoverRead.CompIndep.congr_of_marked (T.V j σ) _ hι _ _ one_ne_zero _ _
      (fun b hb => by rwa [Nat.cast_one, one_mul]) (γ₁' * h₀) (γ₁ * h) k₁
      (by rw [eak₁, map_mul, show finHom (T.V j σ) a₁ = 1 from ha₁, one_mul]) hLb _ hmA hmB
  have hp : C.d.pd ≠ 0 := fun h0 => by
    have := C.d.l₂.three_le
    rw [hMl, h0] at this
    omega
  have hk₂K : k₂ ∈ T.Kf j σ := by
    refine (hT.kfHalf j hj σ hσ k₂).2 ⟨hk₂, ?_⟩
    have hmA := hm₂
    have hmB := hm₂'
    rw [hMl] at hmA hmB
    exact GlobalTheory.CoverRead.CompIndep.congr_of_marked (T.V j σ) _ hι _ _ hp _ _
      (GlobalTheory.CoverRead.CompIndep.ratio_mul_mem T.Q.l C.d.l₂ _ _ hMl hIl) (γ₂ * h) (γ₂' * h₀) k₂
      (by rw [eak₂, map_mul, show finHom (T.V j σ) a₂ = 1 from ha₂, one_mul]) hLc _ hmA hmB
  have hκK : k₁ * k₂ ∈ T.Kf j σ := mul_mem hk₁K hk₂K
  have he : finHom (T.V j σ) ((γ₁' * h₀)⁻¹ * (γ₁ * γ₂⁻¹ * γ₂' * γ₁'⁻¹) * (γ₁' * h₀)) =
      finHom (T.V j σ) (k₁ * k₂) := by
    have e : (γ₁' * h₀)⁻¹ * (γ₁ * γ₂⁻¹ * γ₂' * γ₁'⁻¹) * (γ₁' * h₀) =
        ((γ₁' * h₀)⁻¹ * (γ₁ * h)) * ((γ₂ * h)⁻¹ * (γ₂' * h₀)) := by group
    rw [e, map_mul, eak₁, eak₂, map_mul, map_mul, show finHom (T.V j σ) a₁ = 1 from ha₁,
      show finHom (T.V j σ) a₂ = 1 from ha₂, one_mul, one_mul, map_mul]
  have hM0' : T.Q.l.M ≠ 0 := by
    have := T.Q.l.three_le
    omega
  have hδa : γ₁ * γ₂⁻¹ * γ₂' * γ₁'⁻¹ ∈ GQ (T.V j σ) :=
    mul_mem (mul_mem (mul_mem hγ₁ (inv_mem hγ₂)) hγ₂') (inv_mem hγ₁')
  obtain ⟨Δ, hΔi, hΔl, hΔc, hΔa⟩ := conj_move (T.V j σ) hr₁ _ (γ₁' * h₀) (k₁ * k₂) hδa T.Q.l.M hM0'
    ((hK _).1 hκK).2 ((hK _).1 (inv_mem hκK)).2 he _ hL₁' _ (hW₁ (T.dict j σ h).1).1
  refine ⟨Δ, GlobalTheory.PrincCore.mem_group_of_congruent D T.toCore hT.toLawsM j hj σ hσ _ Δ ⟨hΔi, hΔl⟩ hΔc,
    fun τ t₂ t₁ => ?_⟩
  have a₁ := hf₁ ⟨τ, t₁⟩
  have a₂ := hf₂ ⟨τ, t₂⟩
  rw [GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth₂ _ ⟨τ, t₂⟩) (hth₁ _ ⟨τ, t₁⟩)] at a₂
  have e : γ₁ * h = (γ₁ * γ₂⁻¹ * γ₂' * γ₁'⁻¹) * ((γ₁' * γ₂'⁻¹) * (γ₂ * h)) := by group
  rw [a₁, e, hΔa τ _ (hth₁ _ ⟨τ, t₁⟩), hM₀ τ _ (hth₁ _ ⟨τ, t₁⟩), Matrix.mul_assoc, Matrix.mul_assoc, ← a₂, hM0eq]

end GlobalTheory.CoverFrameArith
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertFrameConjExtendsAndFrameMapSurjectiveStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_frame_conj_extends_and_frame_map_surjective : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), 0 < n → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w n → Formalism.UG.cT Dv.σw b.val * b.val = Formalism.UG.antiJ (w.adicCompletion L) n → ∀ p : locU n w →* Formalism.UG.GU Dv.σw n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → (∀ x : L, Dv.σw (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) ∧ Function.Surjective p := by
  first | exact @GlobalTheory.InertFrameConj.conj_and_surjective | exact GlobalTheory.InertFrameConj.conj_and_surjective | (intros; apply GlobalTheory.InertFrameConj.conj_and_surjective <;> assumption)
end

