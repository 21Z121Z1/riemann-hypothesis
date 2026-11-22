import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0862
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0516
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0404
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0336
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0565
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SubsingletonOfScalar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateReferenceCharactersGoodEmbeddings
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0482
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0861
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0863
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0735
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0753
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0787
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0594
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0757

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HoweDualityCompactPairPolynomialFockAllRealPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeDuality_compactPair_polynomialFock_allRealPlaces : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (BS : GlobalTheory.ExportSeries.GLR D n) (K : Type) [Group K] (r : K →* GlobalTheory.ExportSeries.GLR D n), (∀ (k : K) (τ : D.what₂.Tau), ((GlobalTheory.ExportSeries.inBasis BS (r k) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → (∀ g : GlobalTheory.ExportSeries.GLR D n, (∀ τ, ((GlobalTheory.ExportSeries.inBasis BS g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∃ k, r k = g) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : K →* Module.End ℂ W), (∀ U : Submodule ℂ W, (∀ k, U.map (ρ k) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ M : Submodule ℂ (W →ₗ[ℂ] PolF D m n), (∀ ψ ∈ M, ∀ (k : K) (w' : W), ψ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (ψ w')) → (∀ ψ ∈ M, ∀ (τ : D.what₂.Tau) (Z : Matrix (Fin m) (Fin m) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) Z ∘ₗ ψ ∈ M) → M ≠ ⊥ → ∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ w')) → φ ∈ M := by
  first | exact @GlobalTheory.HoweCompactAlg.mem_of_equivariant | exact GlobalTheory.HoweCompactAlg.mem_of_equivariant | (intros; apply GlobalTheory.HoweCompactAlg.mem_of_equivariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdxAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LFun (IsSplitChart IsInertChart KGL)
open GlobalTheory.AdelicU

noncomputable section
namespace GlobalTheory.LocKerMod

def idxAt {D : D7} (T : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} (w : HeightOneSpectrum (𝓞 D.host.E))
    (h : w.under (𝓞 D.host.F) = v) (g : GlobalTheory.FinZeta.Gv T v) : ℕ :=
  ((GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup.map
    (GlobalTheory.LFun.locMat D.sp.cm.sig T.gram h g).1.mulVecLin.toAddMonoidHom).relIndex
    (GlobalTheory.LFun.latAt w (frameLat T)).toAddSubgroup

end GlobalTheory.LocKerMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFramedPointGoodReductionDefiniteSignatur
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GoodPts GlobalTheory.DefiniteAbelian
open scoped CategoryTheory.Obj

namespace GlobalTheory.GoodDefinite

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem abLocus_eq_univ_of_definite (Xo : Moduli Dw l) (hq : Dw.q = 0) (T : CDVR) (x : Sp T.Fr ⟶ Xo.X)
    (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m₁ : SABMap t' Xo.univ.t x)
    (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))) : abLocus G.G = Set.univ := by
  obtain ⟨m, hm, hw⟩ := exists_w0_relation H
  obtain ⟨b, hb⟩ := Spec.map_surjective (x ≫ Xo.s)
  let β : KA l →+* T.Fr := b.hom
  have hβ : x ≫ Xo.s = spMap β := hb.symm
  have : CharZero T.Fr := (RingHom.charZero_iff β.injective).1 inferInstance
  let ρ : T.Fr := β (baseKA l).ρ
  have hρ : ρ ^ 2 = -(H.d : T.Fr) := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have hm' : (4 : T.Fr) * m = 1 + H.d := by exact_mod_cast hm
  let z : T.Fr := (1 + ρ) / 2
  have hz2 : 2 * z = 1 + ρ := mul_div_cancel₀ _ two_ne_zero
  have hz : z * z + m = z := mul_left_cancel₀ (show (4 : T.Fr) ≠ 0 by norm_num) (by
    linear_combination (2 * z + ρ - 1) * hz2 + hρ + hm')
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : T.V, algebraMap T.V T.Fr z₀ = z := by
    rcases ValuationRing.isInteger_or_isInteger T.V z with h | ⟨u, hu⟩
    · exact h
    · by_cases h0 : z = 0
      · exact ⟨0, by rw [h0, map_zero]⟩
      · refine ⟨1 - m * u, ?_⟩
        rw [map_sub, map_one, map_mul, map_natCast, hu]
        field_simp
        linear_combination -hz
  let L := AlgebraicClosure T.Fr
  let a : T.Fr →+* L := algebraMap T.Fr L
  have : CharZero L := (RingHom.charZero_iff a.injective).1 inferInstance
  have hdet := (Xo.univ.geom L (spMap a ≫ x) (a.comp β) (by rw [Category.assoc, hβ, sp_comp])).1
  have h₁ := actsBy_of_detCond Dw hq _ (spMap a ≫ x) _ (a z)
    (by rw [← map_ofNat a 2, ← map_mul, hz2, map_add, map_one]; rfl) hdet
  have h₂ := (actsBy_pull m₂.cart (m₂.act H.w0) (spMap a) _).1 ((actsBy_pull m₁.cart (m₁.act H.w0) (spMap a) _).2 h₁)
  have := G.semi.smooth
  have := G.semi.separated
  have := G.act.hom H.w0
  have h₃ : ActsBy G.G (G.act.act H.w0) (𝟙 _) z₀ := by
    refine actsBy_of_injective (a.comp (algebraMap T.V T.Fr))
      (a.injective.comp (IsFractionRing.injective T.V T.Fr)) _ _ ?_
    rw [Category.comp_id, ← sp_comp, RingHom.comp_apply, hz₀]
    exact h₂
  refine Set.eq_univ_of_forall fun p K _ _ t _ => ?_
  obtain ⟨j, hj⟩ := Spec.map_surjective t
  have h₄ := actsBy_baseChange (k := K) j.hom (𝟙 _) _ h₃
  have ht : spMap j.hom ≫ 𝟙 _ = t := (Category.comp_id _).trans hj
  rw [ht] at h₄
  obtain ⟨X⟩ := G.semi.fibres K t
  exact isProper_of_actsBy X (OAct.pullback t G.G G.act) H.d_prime hm hw _
    ((actsBy_pull (isGrpPullback_pullback G.G t) (pullback.lift_fst _ _ _) _ _).2 (by rwa [Category.id_comp]))

theorem good_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.q = 0 →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), Good y := by
  intro E _ _ _ H Dw l Xo c hq T io y
  obtain ⟨G, t', m₁, m₂, -⟩ := y.2.2
  exact ⟨G, t', m₁, m₂, GlobalTheory.GoodProper.isProper_of_abLocus_eq_univ E H Dw l Xo T _ G t' m₁ m₂
    (abLocus_eq_univ_of_definite Xo hq T _ G t' m₁ m₂)⟩

end GlobalTheory.GoodDefinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsProperSemiAbelianTripleOfAbelianLocusEqUnivStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_semiAbelian_triple_of_abelianLocus_eq_univ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : CDVR) (x : Sp T.Fr ⟶ Xo.X) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (_ : SABMap t' Xo.univ.t x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))), abLocus G.G = Set.univ → IsProper G.G.hom := by
  first | exact @GlobalTheory.GoodProper.isProper_of_abLocus_eq_univ | exact GlobalTheory.GoodProper.isProper_of_abLocus_eq_univ | (intros; apply GlobalTheory.GoodProper.isProper_of_abLocus_eq_univ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelChoiceMuUnramifiedOutsideTypePlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelChoice_mu_unramified_outside_type_places : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0), L.Is μ0 → SplitSet L.Pg → ∀ j : Fin D.R.m, UnramOutside (L.mu0 ((j : ℕ) + 1)) L.Pg := by
  first | exact @GlobalTheory.TypePlaceUnram.unramOutside_mu0_of_splitSet | exact GlobalTheory.TypePlaceUnram.unramOutside_mu0_of_splitSet | (intros; apply GlobalTheory.TypePlaceUnram.unramOutside_mu0_of_splitSet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUniformizerTorusTranslateUnipotentQuotiStatement
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_uniformizerTorus_translate_unipotentQuotient : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (μ : Measure (GA E n)) [μ.IsHaarMeasure] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (𝓕 : Set (GA E n)),
    IsFundamentalDomain (GlobalTheory.CellDec.NE E n) 𝓕 μ → ∀ F : GA E n → ℝ≥0∞, Measurable F →
    (∀ u ∈ GlobalTheory.CellDec.NA E n, ∀ g, F (u * g) = F g) →
    ∫⁻ g in 𝓕, F ((GlobalTheory.CellDec.tl n ϖ l)⁻¹ * g) ∂μ = ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) * ∫⁻ g in 𝓕, F g ∂μ := by
  first | exact @GlobalTheory.CellDec.lintegral_tl_inv_mul | exact GlobalTheory.CellDec.lintegral_tl_inv_mul | (intros; apply GlobalTheory.CellDec.lintegral_tl_inv_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremBOfBlochKatoTateDualityEulerCStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLiftingTheoremB_of_blochKato_tateDuality_eulerChar : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ C : ℝ, (320 : ℝ) ≤ C → ArcLiftingSetup.aux₃ D HW F C := by
  first | exact @GlobalTheory.theoremB_closing | exact GlobalTheory.theoremB_closing | (intros; apply GlobalTheory.theoremB_closing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSelfDualLatticeIffIntegralFrameMatricesHalfStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_selfDualLattice_iff_integral_frameMatrices_half : ∀ {D : D7} {S T : HSp D} {F : GlobalTheory.ExportSeries.Frame S T}, F.Good → ∀ {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)},
    GlobalTheory.ExportSeries.PlacesOK Pg Q → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ {x : WO S T}, IsHalf (GlobalTheory.ExportSeries.halfIdem Pg Q) x →
      (x ∈ F.lat ↔ IsIntM (frMapAdj S T F.βS F.βT x) ∧ IsIntM (frMapO S T F.βS F.βT x)) := by
  first | exact @GlobalTheory.ExportSeries.LatHalf.mem_lat_iff_isIntM_halfIdem | exact GlobalTheory.ExportSeries.LatHalf.mem_lat_iff_isIntM_halfIdem | (intros; apply GlobalTheory.ExportSeries.LatHalf.mem_lat_iff_isIntM_halfIdem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairFixedVectorLatticeVacuumOffLevelsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairFixedVector_latticeVacuum_offLevels : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → GlobalTheory.FinZeta.VacFin R.ψ (Vc D i) (Wc D i) v (R.vP i t) := by
  first | exact @GlobalTheory.RawLift.vacFin_off | exact GlobalTheory.RawLift.vacFin_off | (intros; apply GlobalTheory.RawLift.vacFin_off <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameResidueCharTrivialSplitPlaceOffUnramifiedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_residue_char_trivial_split_place_off_unramified : ∀ (D : D7) (M : Type) [CommGroup M] (χ : (AE D)ˣ →* M) (Q P : Finset (Pl D.host.E)), UnramOutside χ Q → SplitSet P → Q ⊆ P → ∀ PP ∈ P, PP ∉ Q → IsResAt χ PP 1 := by
  first | exact @GlobalTheory.ConjTwist.isResAt_one_of_unram | exact GlobalTheory.ConjTwist.isResAt_one_of_unram | (intros; apply GlobalTheory.ConjTwist.isResAt_one_of_unram <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesTypeUnderSupportedLiftsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_type_under_supported_lifts : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ ω : PairRep S T, B.IsWeil 1 ω → ∀ (u : G0 B.G.Pg T.rank) (hu : u ∈ B.G.P.H), ∃ κ : GA D T, Lev.IsLevelLift T B.F.βT B.G.levT u κ ∧ SuppAt (idem B.G.Pg) T κ ∧ ∀ (Q : Finset (Pl D.host.E)), B.admitted Q → ∀ (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) (h : GA D S) (P : PolF D T.rank S.rank) (g : GA D T), series B.F ω (B.vecAt Q φ) h P (g * κ) = ((B.G.P.chi ⟨u, hu⟩ : ℂˣ) : ℂ) * series B.F ω (B.vecAt Q φ) h P g := by
  first | exact @GlobalTheory.TypeSupportLift.series_type_supp | exact GlobalTheory.TypeSupportLift.series_type_supp | (intros; apply GlobalTheory.TypeSupportLift.series_type_supp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedSeriesSpecialisedUniversalDatumMemSpan
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SpecSpan

open Classical in

theorem series_sum {D : D7} {S T : HSp D} (B : Base S T) (hB : B.Good) (ω : PairRep S T) {τs : Type} (s : Finset τs)
    (c : τs → ℂ) (f : τs → WO S T → ℂ) (hf : ∀ τ, IsThetaFunO B.F.ψ S T (f τ)) (h : GA D S) (P : PolF D T.rank S.rank) :
    series B.F ω (∑ τ ∈ s, c τ • f τ) h P = ∑ τ ∈ s, c τ • series B.F ω (f τ) h P := by
  have hθ : ∀ s : Finset τs, IsThetaFunO B.F.ψ S T (∑ τ ∈ s, c τ • f τ) := fun s => by
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty]; exact GlobalTheory.OrientedHeis.theta_zero
    | insert a s ha ih => rw [Finset.sum_insert ha]; exact GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (hf a)) ih
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    funext g
    rw [series_apply]
    change ω (h, g) (pureTensorO B.F.ψ B.F.θ S T (fun _ => 1) B.F.sT (fun τ => (B.F.BS τ).val) B.F.BT 0 P) 0 = 0
    rw [GlobalTheory.FockFiniteHeis.pureTensorO_zero _ _ _ _ hB.frame.vac.1 hB.frame.vac.2.inf, map_zero]
    rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    funext g
    simp only [series_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    change ω (h, g) (pureTensorO B.F.ψ B.F.θ S T (fun _ => 1) B.F.sT (fun τ => (B.F.BS τ).val) B.F.BT
      (c a • f a + ∑ τ ∈ s, c τ • f τ) P) 0 = c a * ω (h, g) (pureTensorO B.F.ψ B.F.θ S T (fun _ => 1) B.F.sT (fun τ => (B.F.BS τ).val) B.F.BT
      (f a) P) 0 + ω (h, g) (pureTensorO B.F.ψ B.F.θ S T (fun _ => 1) B.F.sT (fun τ => (B.F.BS τ).val) B.F.BT
      (∑ τ ∈ s, c τ • f τ) P) 0
    rw [GlobalTheory.FockFiniteHeis.pureTensorO_lin _ _ _ _ hB.frame.vac.1 hB.frame.vac.2.inf _ _ _ _ _ (hf a) (hθ s), map_add, map_smul]
    rfl

theorem theta_vecAt {D : D7} {S T : HSp D} {B : Base S T} (hB : B.Good) {Q : Finset (Pl D.host.E)} (hQ : B.admitted Q)
    (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) : IsThetaFunO B.F.ψ S T (B.vecAt Q φ) :=
  GlobalTheory.GalLift.Vec.theta_of_thetaAt hB.frame.vac.1 hB.frame.vac.2.inf (Base.isThetaAt_vecAt hB hQ φ) hB.frame.vac.2.theta

open Classical in

theorem twist_series_mem_span {D : D7} {S T : HSp D} (B : Base S T) (hB : B.Good) (hS : S.SigOK) (ω : PairRep S T)
    (hω : B.IsWeil 1 ω) (t : Twist D Circle) (hQ : B.admitted t.Q) (O : Subring ℂ) (ι : ↥t.Q → Type) [∀ PP, Fintype (ι PP)]
    (a : ∀ PP, ι PP → ℂ) (ha : ∀ PP u, a PP u ∈ O) (g : ∀ PP, ι PP → GL (Fin S.rank) (kP PP.1))
    (loc : ∀ PP : ↥t.Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ)
    (hloc : ∀ PP y, loc PP y = ∑ u, a PP u * flat (t.resC PP.1) (y * (g PP u : Matrix (Fin S.rank) (Fin S.rank) (kP PP.1))))
    (h : GA D S) (P : PolF D T.rank S.rank) :
    twistBy T t.chi (series B.F ω (B.vecAt t.Q loc) h P) ∈ Submodule.span O (B.genSet ω t h P) := by
  let φ : (∀ PP, ι PP) → ∀ PP : ↥t.Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ :=
    fun τ PP y => flat (t.resC PP.1) (y * (g PP (τ PP) : Matrix (Fin S.rank) (Fin S.rank) (kP PP.1)))
  have hvec : B.vecAt t.Q loc = ∑ τ : (∀ PP, ι PP), (∏ PP, a PP (τ PP)) • B.vecAt t.Q (φ τ) := by
    have e1 : B.locFn t.Q loc = ∑ τ : (∀ PP, ι PP), (∏ PP, a PP (τ PP)) • B.locFn t.Q (φ τ) := by
      funext y
      simp only [Base.locFn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hloc]
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Finset.prod_mul_distrib]
      ring
    change B.F.vecL B.G _ (B.locFn t.Q loc) = ∑ τ : (∀ PP, ι PP), (∏ PP, a PP (τ PP)) • B.F.vecL B.G _ (B.locFn t.Q (φ τ))
    rw [e1, map_sum]
    simp only [map_smul]
  rw [hvec, series_sum B hB ω _ _ _ (fun τ => theta_vecAt hB hQ (φ τ)), map_sum]
  refine Submodule.sum_mem _ fun τ _ => ?_
  obtain ⟨hQτ, hsupp, hmove⟩ := GlobalTheory.T.thetaSeries_integralSourceTranslation_right_mul D S T B hB hS ω hω t.Q hQ (fun PP => g PP (τ PP))
  have e2 : series B.F ω (B.vecAt t.Q (φ τ)) h P = series B.F ω (B.vecFlat t) (h * hQτ) P :=
    hmove (fun PP => flat (t.resC PP.1)) h P
  rw [map_smul, e2]
  have hmem : ∏ PP, a PP (τ PP) ∈ O := Subring.prod_mem _ fun PP _ => ha PP (τ PP)
  have e3 : (∏ PP, a PP (τ PP)) • twistBy T t.chi (series B.F ω (B.vecFlat t) (h * hQτ) P) =
      (⟨_, hmem⟩ : O) • twistBy T t.chi (series B.F ω (B.vecFlat t) (h * hQτ) P) := rfl
  rw [e3]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨hQτ, hsupp, rfl⟩)

end GlobalTheory.SpecSpan

namespace GlobalTheory.SpecSpan

open Classical in

theorem univ_spec {k : Type} [Field k] [Finite k] {r n : ℕ} {C : Type} [AddCommGroup C] [Fintype C]
    [Fintype (Planes k r n)] (β : DetBases k r n) (κ : kˣ →* Multiplicative C) (ν : Multiplicative C →* ℂˣ)
    (g : Planes k r n → GL (Fin n) k) (c : Planes k r n → kˣ)
    (hg : ∀ U y, dU β U y = (c U : k) * (topL r (y * (g U : Matrix (Fin n) (Fin n) k))).det)
    (y : Matrix (Fin r) (Fin n) k) :
    ∑ a : C, (ν (Multiplicative.ofAdd a) : ℂ) * ((univCoef β κ a y : ℚ) : ℂ) =
      ∑ U : Planes k r n, ((Nat.card k : ℂ) ^ (r * (n - r)))⁻¹ * (ν (κ (c U)) : ℂ) *
        flat (ν.comp κ) (y * (g U : Matrix (Fin n) (Fin n) k)) := by
  have hterm : ∀ U : Planes k r n, ∑ a : C, (ν (Multiplicative.ofAdd a) : ℂ) * (((univTerm β κ y U).coeff a : ℚ) : ℂ) =
      (ν (κ (c U)) : ℂ) * flat (ν.comp κ) (y * (g U : Matrix (Fin n) (Fin n) k)) := by
    intro U
    unfold univTerm
    by_cases hC : Compl U.1 y
    · rw [dif_pos hC]
      have hd : dU β U y ≠ 0 := (dU_ne_zero_iff β U y).2 hC
      have hdet : (topL r (y * (g U : Matrix (Fin n) (Fin n) k))).det ≠ 0 := by
        intro h0; apply hd; rw [hg, h0, mul_zero]
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      rw [Finset.sum_eq_single (Multiplicative.toAdd (κ (Units.mk0 _ hd)))]
      · rw [if_pos rfl, Rat.cast_one, mul_one, flat_of_isUnit (ν.comp κ) (u := Units.mk0 _ hdet) rfl]
        have e : Units.mk0 _ hd = c U * Units.mk0 _ hdet := Units.ext (by simp [hg])
        rw [ofAdd_toAdd, e, map_mul, map_mul, Units.val_mul, MonoidHom.comp_apply]
      · intro a _ ha
        rw [if_neg (Ne.symm ha), Rat.cast_zero, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dif_neg hC]
      have hd : dU β U y = 0 := by
        by_contra h; exact hC ((dU_ne_zero_iff β U y).1 h)
      have hdet : ¬ IsUnit (topL r (y * (g U : Matrix (Fin n) (Fin n) k))).det := by
        rw [isUnit_iff_ne_zero]; intro h0
        rw [hg] at hd
        exact h0 ((mul_eq_zero.1 hd).resolve_left (c U).ne_zero)
      rw [flat_of_not_isUnit _ hdet, mul_zero]
      simp
  have hcoef : ∀ a : C, univCoef β κ a y =
      ((Nat.card k : ℚ) ^ (r * (n - r)))⁻¹ * ∑ U : Planes k r n, (univTerm β κ y U).coeff a := by
    intro a
    rw [univCoef, univ, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, AddMonoidAlgebra.coeff_sum,
      Finsupp.finsetSum_apply]
    congr 1
    exact Finset.sum_congr (by congr; exact Subsingleton.elim _ _) fun _ _ => rfl
  simp only [hcoef, Rat.cast_mul, Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast, Rat.cast_sum]
  rw [Finset.sum_congr rfl fun U _ => (by rw [mul_assoc, ← hterm U] :
    ((Nat.card k : ℂ) ^ (r * (n - r)))⁻¹ * (ν (κ (c U)) : ℂ) * flat (ν.comp κ) (y * (g U : Matrix (Fin n) (Fin n) k)) =
      ((Nat.card k : ℂ) ^ (r * (n - r)))⁻¹ * ∑ a : C, (ν (Multiplicative.ofAdd a) : ℂ) * (((univTerm β κ y U).coeff a : ℚ) : ℂ))]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun U _ => Finset.sum_congr rfl fun a _ => by ring

end GlobalTheory.SpecSpan

namespace GlobalTheory.SpecSpan

theorem specSer_mem_span : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (ρ : Setup X), ρ.Good →
  ∀ (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y →
  ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) → InRange X i Q →
    ∀ (s : Finset (Pl D.host.E)) (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      ρ.IsDatum i j b s h P → (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) →
      specSer ρ Y i j b k Q M χ h P ∈
        Submodule.span (ρ.eOk i b k).range (ρ.gens i j b k Q (χ.comp (Y.delU i Q M)) h P) := by
  intro D N X ρ hρ Y hY i j b k Q M χ hT _ s h P _ _
  classical
  have hA : admissibleConjugatePairPlaces X i Q M = Q := GlobalTheory.T.admissibleConjugatePairPlaces_eq_of_twOK Y hY i k Q M χ hT
  obtain ⟨-, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D N X ρ hρ i j b k Q (χ.comp (Y.delU i Q M)) hT
  have hS : (Vc D j).SigOK := D.sp.V_sig _
  haveI : ∀ PP : Pl D.host.E, Fintype (Planes (kP PP) (Wc D j).rank (Vc D j).rank) := fun PP => Fintype.ofFinite _
  choose gC cC hgc using fun (PP : Pl D.host.E) (U : Planes (kP PP) (Wc D j).rank (Vc D j).rank) =>
    GlobalTheory.T.quotientRowsExteriorDet_eq_const_mul_topBlockDet (kP PP) (Wc D j).rank (Vc D j).rank (ρ.β j PP) U
  have key : ∀ (Q₀ : Finset (Pl D.host.E)), Q₀ = (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).Q →
      ∀ (loc : ∀ PP : ↥Q₀, Matrix (Fin (Wc D j).rank) (Fin (Vc D j).rank) (kP PP.1) → ℂ)
        (a : ∀ PP : ↥Q₀, Planes (kP PP.1) (Wc D j).rank (Vc D j).rank → ℂ),
        (∀ PP u, a PP u ∈ (ρ.eOk i b k).range) →
        (∀ PP y, loc PP y = ∑ u, a PP u * flat ((ρ.tw i b k Q (χ.comp (Y.delU i Q M))).resC PP.1)
          (y * (gC PP.1 u : Matrix (Fin (Vc D j).rank) (Fin (Vc D j).rank) (kP PP.1)))) →
        twistBy (Wc D j) (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).chi
          (series (ρ.B i j b).F (ρ.om i j b 1) ((ρ.B i j b).vecAt Q₀ loc) h P) ∈
          Submodule.span (ρ.eOk i b k).range (ρ.gens i j b k Q (χ.comp (Y.delU i Q M)) h P) := by
    intro Q₀ hQ₀
    subst hQ₀
    intro loc a ha hloc
    exact twist_series_mem_span (ρ.B i j b) (hρ.base i j b) hS (ρ.om i j b 1) (hρ.weil_base i j b) _ hadm _
      (fun PP => Planes (kP PP.1) (Wc D j).rank (Vc D j).rank) a ha (fun PP u => gC PP.1 u) loc hloc h P

  let ν : ∀ PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)), Multiplicative (ZMod (X.l i ^ M)) →* ℂˣ := fun PP =>
    (Units.map (ρ.eOk i b k).toMonoidHom).comp (χ.comp (AddMonoidHom.toMultiplicative
      ((spread Y i Q M (ρ.ch i)).comp (AddMonoidHom.single (fun _ : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) => ZMod (X.l i ^ M)) PP))))
  have hν : ∀ PP a, (ν PP (Multiplicative.ofAdd a) : ℂ) =
      ρ.eOk i b k ((χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) (Pi.single PP a))) : (X.Ok i k)ˣ) : X.Ok i k) := by
    intro PP a; rfl
  have hres : ∀ PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)),
      (ν PP).comp ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).kap PP.1) = (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).resC PP.1 := by
    intro PP
    ext x
    rw [GlobalTheory.T.residueCharacter_twist_universalChar_at_chosen_place ρ hρ Y hY i b k Q M χ hT PP x, MonoidHom.comp_apply, ← hν, ofAdd_toAdd]
  have hnS : ∀ PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)), PP.1 ∉ X.S0 i := fun PP =>
    Finset.disjoint_left.1 hT.2.1 (admissibleConjugatePairPlaces_subset i Q M (mem_half.1 PP.2).1)
  let qi : Pl D.host.E → ℂ := fun PP => ((Nat.card (kP PP) : ℂ) ^ ((Wc D j).rank * ((Vc D j).rank - (Wc D j).rank)))⁻¹
  have hqi : ∀ PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)), qi PP.1 ∈ (ρ.eOk i b k).range := by
    intro PP
    obtain ⟨w, hw⟩ := GlobalTheory.T.isUnit_card_residueField_off_exceptional_places X i k PP.1 (hnS PP)
    refine ⟨((w⁻¹ ^ ((Wc D j).rank * ((Vc D j).rank - (Wc D j).rank)) : (X.Ok i k)ˣ) : X.Ok i k), ?_⟩
    have e : ρ.eOk i b k (w : X.Ok i k) = (Nat.card (kP PP.1) : ℂ) := by rw [hw, map_natCast]
    have e' : ρ.eOk i b k (w : X.Ok i k) ≠ 0 := by
      intro h0; exact w.ne_zero ((map_eq_zero_iff _ (ρ.eOk_injective i b k)).1 h0)
    have e2 : ρ.eOk i b k ((w⁻¹ : (X.Ok i k)ˣ) : X.Ok i k) = (Nat.card (kP PP.1) : ℂ)⁻¹ := by
      rw [← e]
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    show _ = ((Nat.card (kP PP.1) : ℂ) ^ ((Wc D j).rank * ((Vc D j).rank - (Wc D j).rank)))⁻¹
    rw [Units.val_pow_eq_pow_val, map_pow, e2, inv_pow]
  refine key _ (by show half _ _ = half _ _; rw [hA]) (specLoc ρ Y i j b k Q M χ)
    (fun PP U => qi PP.1 * (ν PP ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).kap PP.1 (cC PP.1 U)) : ℂ)) ?_ ?_
  · intro PP U
    refine Subring.mul_mem _ (hqi PP) ?_
    exact ⟨_, rfl⟩
  · intro PP y
    have := univ_spec (ρ.β j PP.1) ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).kap PP.1) (ν PP) (gC PP.1) (cC PP.1)
      (hgc PP.1) y
    rw [hres PP] at this
    exact this
end GlobalTheory.SpecSpan

end
end

