import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
import Formalism.LocalToGlobal.IndefiniteReal.TopMult
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0556
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0965
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0967
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0817
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0803
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongruenceLevelMapsIntoLatticeCongruence
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0962
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0966
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1986
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0053
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0037
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2014
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0968
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfFive
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0793
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0811
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SqEqOneOfFixDat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnisotropicTermsMeanZeroUnipotentRadical
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0213
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0273
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenSubgroupHermitianLatticeEqStandard
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LatOpen.exists_open_hLat_std : ∀ (D : D7) (V : HSp D), Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∃ J : Subgroup (Bridge.Gf V), IsOpen (J : Set (Bridge.Gf V)) ∧ ∀ x ∈ J, Bridge.hLat V x = Formalism.L2.Pj.stdLat D.host.E V.rank := by
  intro D V h1
  refine ⟨(GlobalTheory.Member.PrincLevel.levelGroup V 1).map (finHom V).rangeRestrict,
    GlobalTheory.SmoothVac.isOpen_map_levelGroup V one_pos, ?_⟩
  rintro x ⟨k, hk, rfl⟩
  rw [← h1]
  have hk' := GlobalTheory.Member.PrincLevel.finCong_inv hk.2
  have hm := GlobalTheory.Member.PrincLevel.finCong_map hk.2
  have hm' := GlobalTheory.Member.PrincLevel.finCong_map hk'
  have hL := GlobalTheory.StdFrameCong.pj_latHat_eq V
  have e1 : ((((finHom V).rangeRestrict k)⁻¹ : Bridge.Gf V) :
      GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) = finHom V k⁻¹ := by
    rw [← map_inv]; rfl
  have e0 : (((1 : Bridge.Gf V)⁻¹ : Bridge.Gf V) : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) = 1 := by
    rw [inv_one]; rfl
  unfold Bridge.hLat
  refine congrArg (Submodule.span _) (Set.ext fun v => ?_)
  show _ ∈ latHat D.host.F D.host.E (L0c D V) ↔ _ ∈ latHat D.host.F D.host.E (L0c D V)
  rw [e1, e0, Units.val_one, Matrix.one_mulVec, ← hL]
  constructor
  · intro h
    have := hm _ h
    have ekk : (finHom V k).1 * (finHom V k⁻¹).1 = 1 := by
      rw [← Units.val_mul, ← map_mul (finHom V) k k⁻¹, mul_inv_cancel k, map_one, Units.val_one]
    rwa [Matrix.mulVec_mulVec, ekk, Matrix.one_mulVec] at this
  · exact hm' _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalHeckeOperatorsAdelicReading
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeFamRead

set_option autoImplicit false

open Formalism.BasicNotions.TH Formalism.IndefR.Mult

theorem isDC_one {G : Type} [Group G] (J : Subgroup G) : Formalism.IndefR.Bridge.IsDC J 1 {1} := by
  refine ⟨fun a ha => ⟨1, 1, by simpa using ha⟩, ?_⟩
  rintro g ⟨k, k', rfl⟩
  exact ⟨1, ⟨Finset.mem_singleton_self _, by simpa using J.mul_mem k.2 k'.2⟩, fun a ha => Finset.mem_singleton.1 ha.1⟩

theorem isHeckeAt_zero_one {D : D7} (V : HSp D) {P : PlE D.host} (hP : Formalism.BasicNotions.IsSplitPl D.host P) :
    IsHeckeAt V P 0 1 := by
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P ((GlobalTheory.HeckeTieCompare.isSplitPl_iff P).1 hP)
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
  exact ⟨e, ϖ, he, h1, h2, GlobalTheory.HeckeParts.isHeckeElt_one V he.1 ϖ⟩

theorem rat_side (hT : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform) (hS : ∀ (D : D7) (X : GlobalTheory.TwInputs.RealSide D) (i : Fin D.R.m) (hV : X.core.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res X.core (sg0 D X.A3.A)) = Wc D i), GlobalTheory.HeckeSup.ReadsCusp X.core X.R.toRealDat X.geo.κ i (Formalism.IndefR.FWT.res X.core (sg0 D X.A3.A)) hV)
    (hA : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Formalism.L2.Pj.CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : Formalism.IndefR.FWT.FWTie T R κ v₀) (i : Fin D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ hV : T.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res T (sg0 D A)) = Wc D i, Formalism.IndefR.FWT.JEvAt T R κ v₀ i (sg0 D A) hV) → Function.Injective ((R.FW i).j (sg0 D A)) → (∀ hV : T.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res T (sg0 D A)) = Wc D i, GlobalTheory.HeckeSup.ReadsCusp T R κ i (Formalism.IndefR.FWT.res T (sg0 D A)) hV) → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R i) (D : D7) (X : RealSide D) (i : Fin D.R.m) : GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke X.R.toRealDat i := by
  refine hA D X.Γ X.Pl0 X.T X.A3.A X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.geo.fw i hT X.char.lev X.char.fam X.char.models
    (fun hV => X.inGeo.jEvExists i _ (Formalism.IndefR.FWT.base_embedding_good X.core X.R.toRealDat X.geo.fw.alg_eq X.geo.fw.laws.pins.2.2.1) hV)
    ?_ (hS D X i)
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  by_contra h
  have h1 := (X.unif i (sg0 D X.A3.A)).1 1 (fun _ => x) (linearIndependent_unique_iff.2 h)
  exact h1.ne_zero 0 hx

theorem exists_family_one (hrat : ∀ (D : D7) (X : RealSide D) (i : Fin D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke X.R.toRealDat i)
    (D : D7) (X : RealSide D) (S : RatDat D.ntw) (YS : NExpRealS X.R X.cG S) :
    ∃ hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j), (∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (hL j)) ∧
      (∀ j P, hL j 0 P = 1) ∧ GlobalTheory.ExportPin.Reads X.R X.cG S YS hL := by
  obtain ⟨hL, hs, hr⟩ := GlobalTheory.T.exists_rational_hecke_family_on_rational_datum_forms D X.Γ X.Pl0 X.I0 X.T X.A3 X.core.Q.c.F X.R X.cG S YS X.char.lev X.char.allPl (hrat D X)
  refine ⟨fun j k P => if k = 0 then 1 else hL j k P, fun j h1 h2 k P x hx => ?_, fun j P => if_pos rfl, ?_⟩
  · by_cases hk : k = 0
    · simp only [hk, if_true, Module.End.one_apply]
      exact hx
    · simp only [hk, if_false]
      exact hs j h1 h2 k P x hx
  · intro i k P hsp hso hk α Rc hα hdc x
    by_cases h0 : k = 0
    · subst h0
      have e1 := hr i 0 P hsp hso hk α Rc hα hdc x
      have e2 := hr i 0 P hsp hso hk 1 {1} (isHeckeAt_zero_one _ hsp) (isDC_one _) x
      have e3 : ∀ F, heckeOn (X.R.MW i (sg0 D X.A3.A)) {1} F = F := by
        intro F
        ext v g
        simp [heckeOn, postOn, heckeLin]
      rw [e3] at e2
      simp only [pow_zero, zero_mul, inv_one, mul_one, one_smul] at e1 e2 ⊢
      exact e2.symm.trans e1
    · simp only [h0, if_false]
      exact hr i k P hsp hso hk α Rc hα hdc x

theorem exists_family_reads : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → ∀ (D : D7) (X : RealSide D), ∀ (S : RatDat D.ntw) (YS : NExpRealS X.R X.cG S), ∃ hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j), (∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (hL j)) ∧ (∀ j P, hL j 0 P = 1) ∧ GlobalTheory.ExportPin.Reads X.R X.cG S YS hL :=
  fun hD hT hR D X S YS => exists_family_one (rat_side hT (GlobalTheory.T.heckeTransform_cuspForms_reads_cosetSum hD hR) GlobalTheory.T.exists_rationalHecke_read_as_cosetSums) D X S YS

end GlobalTheory.HeckeFamRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSectionFamilyNoCommonZeroLargeWeight
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SpanFamily

set_option maxHeartbeats 1000000 in

theorem holSub0_le_span_cuspA_of_lastPos : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ →
    ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → LastPos (T.Q.Dw j) a →
    4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n →
    Formalism.L2.Pj.holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤
      Submodule.span ℂ (rdU (T.U j σ) '' (T.cuspA j a n : Set (T.R j))) := by
  intro D T h j hj σ hσ a n hdom hlast hn
  have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  obtain ⟨hrk, hM⟩ := h.modelW j hj σ hσ
  have key := GlobalTheory.Dict.holSub0_le_span_cusp GlobalTheory.chartIndependence_unconditional D.host.E T.Q.H (T.Q.Dw j) T.Q.l
    (T.Q.Xo j) T.Q.c D.R.r (fun s => Formalism.L2.PjFree.Unf.ofPj (T.U j s)) hr h.pins.2.1.2
    (fun s hs => (Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj s hs)) σ hσ
    (fun k k' => ⟨(hM k).1.trans (hM k').1.symm, (hM k).2.trans (hM k').2.symm⟩)
    (fun k => GlobalTheory.PrincCore.mem_group_of_congruent D T.toCore h.toLawsM j hj σ hσ k)
    a n hdom hlast hn
    (fun k => h.chiTriv j hj σ hσ a n hdom k)
  intro P hP
  exact key ⟨hP.1, hP.2⟩

theorem exists_complex_point {K A : Type} [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    (σ : K →+* ℂ) (I : Ideal A) (hI : I ≠ ⊤) : ∃ ψ : A →ₐ[K] CAt σ, ∀ x ∈ I, ψ x = 0 := by
  obtain ⟨M, hMmax, hle⟩ := Ideal.exists_le_maximal _ hI
  let _ : Field (A ⧸ M) := Ideal.Quotient.field M
  have : Module.Finite K (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ M)
  let _ : Algebra K ℂ := σ.toAlgebra
  let κ : (A ⧸ M) →ₐ[K] ℂ := IsAlgClosed.lift
  refine ⟨κ.comp (Ideal.Quotient.mkₐ K M), fun x hx => ?_⟩
  show κ (Ideal.Quotient.mk M x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.2 (hle hx), map_zero]

theorem evR_of_frMap {D : D7} (T : CoreJ D) (h : LawsJ T) {j : ℕ} (hj : Formalism.L2.Pj.InR D j) (f : T.R j)
    (hf : IsNatural (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) f)
    {S : Type} [CommRing S] [Algebra T.Q.c.F S] (p : TRing T.Q.c.F) (ψ : p.R →ₐ[T.Q.c.F] S)
    (y : FrPt (T.Q.Xo j) T.Q.c p.R) (z : FrPt (T.Q.Xo j) T.Q.c S) (hz : FrMap ψ y z) :
    evR (T.Q.Xo j) T.Q.c f z = ψ (f p y) := by
  have hT : FromTest (K := T.Q.c.F) (fun S _ _ => FrPt (T.Q.Xo j) T.Q.c S) (fun φ y z => FrMap φ y z) z :=
    ⟨p, ψ, y, hz⟩
  unfold evR evalAt
  rw [dif_pos hT]
  exact h.evalWD j hj f hf S _ p _ ψ _ y z hT.choose_spec.choose_spec.choose_spec hz

set_option maxHeartbeats 1000000 in

theorem exists_family : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∃ (b : (D.host.E →+* ℂ) × ℕ → ℕ) (m N : ℕ) (t : Fin N → Rul (T.Q.Xo j) T.Q.c), Dom b m ∧ (∀ i, t i ∈ sec (T.Q.Xo j) T.Q.c b m) ∧ (∀ (p : TRing T.Q.c.F) (y : FrPt (T.Q.Xo j) T.Q.c p.R), Ideal.span (Set.range fun i => t i p y) = ⊤) ∧ ∀ P ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n), ∀ i, P * rdU (T.U j σ) (t i) ∈ Submodule.span ℂ (rdU (T.U j σ) '' (sec (T.Q.Xo j) T.Q.c (a + b) (n + m) : Set (Rul (T.Q.Xo j) T.Q.c))) := by
  intro D T h j hj σ hσ a n hdom
  obtain ⟨b, m, hbm, hlast, hm, hnz⟩ := GlobalTheory.T.exists_dominantWeight_cuspSections_noCommonZero D T h j hj σ hσ
  haveI : FiniteDimensional T.Q.c.F (T.cuspA j b m) := h.cuspFD j hj b m hbm
  haveI : Module.Free T.Q.c.F (T.cuspA j b m) := Module.Free.of_divisionRing _ _
  let B := Module.finBasis T.Q.c.F (T.cuspA j b m)
  have hsec : ∀ i, (B i : T.R j) ∈ sec (T.Q.Xo j) T.Q.c b m := fun i => cusp_le_sec _ _ _ _ _ (B i).2
  refine ⟨b, m, _, fun i => (B i : T.R j), hbm, hsec, ?_, ?_⟩
  · intro p y
    by_contra hne
    have hL := (GlobalTheory.Reg.evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c).1
    obtain ⟨ψ, hψ⟩ := exists_complex_point σ _ hne
    obtain ⟨z, hz⟩ := hL.bc p.R (CAt σ) ψ y
    have hz0 : ∀ i, evR (T.Q.Xo j) T.Q.c (B i : T.R j) z = 0 := fun i => by
      rw [evR_of_frMap T h hj _ (hsec i).1 p ψ y z hz]
      exact hψ _ (Ideal.subset_span ⟨i, rfl⟩)
    haveI : IsDomain (CAt σ) := inferInstanceAs (IsDomain ℂ)
    obtain ⟨k, x, t, ht⟩ := (h.unf j hj σ hσ).2.2.1 z
    have hx0 : ∀ i, rdU (T.U j σ) (B i : T.R j) k x.1 = 0 := fun i => by
      have hw := GlobalTheory.ArcQ.evR_frBor_of_isDomain hL (hsec i) t _ z ht
      rw [hz0 i] at hw
      have hu : wchar (ex (T.Q.Dw j) b m) t ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun c _ => pow_ne_zero _ (t c).ne_zero
      have h0 := (mul_eq_zero.1 hw.symm).resolve_left hu
      simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos x.2]
      exact congrArg toC h0
    let ev : FDSec (T.U j σ).X →ₗ[ℂ] ℂ :=
      { toFun := fun P => P k x.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hall : ∀ f ∈ T.cuspA j b m, rdU (T.U j σ) f k x.1 = 0 := by
      intro f hf
      have key : ∀ g : T.cuspA j b m, g ∈ Submodule.span T.Q.c.F (Set.range B) →
          rdU (T.U j σ) (g : T.R j) k x.1 = 0 := by
        intro g0 hg0
        induction hg0 using Submodule.span_induction with
        | mem g hg =>
          obtain ⟨i, rfl⟩ := hg
          exact hx0 i
        | zero => rw [Submodule.coe_zero, map_zero]; rfl
        | add g g' _ _ hg hg' =>
          rw [Submodule.coe_add, map_add, Pi.add_apply, Pi.add_apply, hg, hg', add_zero]
        | smul c g _ hg =>
          rw [Submodule.coe_smul, map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, hg, smul_zero]
      exact key ⟨f, hf⟩ (B.mem_span _)
    have hle : Submodule.span ℂ (rdU (T.U j σ) '' (T.cuspA j b m : Set (T.R j))) ≤ LinearMap.ker ev := by
      rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      exact hall f hf
    obtain ⟨P, hP, hPx⟩ := hnz k x.1 x.2
    exact hPx (hle (holSub0_le_span_cuspA_of_lastPos D T h j hj σ hσ b m hbm hlast hm hP))
  · intro P hP i
    have hrd : rdU (T.U j σ) (B i : T.R j) ∈ holSub (T.U j σ).X (laU (T.U j σ) b m) :=
      ((mem_cusp _ _ _ _ _ _).1 (B i).2).2 σ hσ
    have hdab : Dom (a + b) (n + m) := ⟨fun τ => (hdom.1 τ).add (hbm.1 τ), hdom.2.add hbm.2⟩
    have hprod : P * rdU (T.U j σ) (B i : T.R j) ∈
        Formalism.L2.Pj.holSub0 (T.U j σ).X (laU (T.U j σ) (a + b) (n + m)) := by
      refine ⟨?_, fun k x hx => by simp [hP.2 k x hx]⟩
      have hP1 := (GlobalTheory.CuspProduct.mem_holSub_iff _ _ _).1 hP.1
      have hr1 := (GlobalTheory.CuspProduct.mem_holSub_iff _ _ _).1 hrd
      refine (GlobalTheory.CuspProduct.mem_holSub_iff _ _ _).2 fun k => ?_
      rw [show laU (T.U j σ) (a + b) (n + m) k = laU (T.U j σ) a n k + laU (T.U j σ) b m k from
        GlobalTheory.CuspProduct.laU_add (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) a b n m hdom.2 hbm.2 k]
      exact (siegelSpaceAlgebra_holds (E := D.host.E) D.R.r _ _ _ 0).2.1 _ (hP1 k) _ (hr1 k).1
    have hlast' : LastPos (T.Q.Dw j) (a + b) := fun τ hτ hm0 =>
      lt_of_lt_of_le (hlast τ hτ hm0) (by simp)
    have hs := holSub0_le_span_cuspA_of_lastPos D T h j hj σ hσ (a + b) (n + m) hdab hlast' (by omega) hprod
    exact Submodule.span_mono (Set.image_mono (cusp_le_sec _ _ _ _ _)) hs

end GlobalTheory.SpanFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsVacuumIdentityConstantsUniformisedCover
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.CoverCc

theorem exists_ccIs_cover : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, C.IsUnif → ∃ cc : C.U₂.Comp → ℂ, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) C.U₂ (castDict hV C.dict₂) (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) (T.x₀ ((i : ℕ) + 1) T.σ₀) (R.ωP i A.μ0) (R.vacP i) cc := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hlev hgrp hfam hmods hthP hT i hstd hV C hC
  have hC5 : GlobalTheory.Core5 R F := ⟨hlev, hgrp, hfam, hmods, hthP⟩
  have hσ0 : GoodEmb T.Q.c T.σ₀ := rfl
  obtain ⟨hP, hV0, h1, h2, h3, h4, h5⟩ :=
    GlobalTheory.AdTh.RecPair.isPair_record_ofFive D G Pl0 T0 A _ R F hC5 i A.μ0 hstd
  have hM := GlobalTheory.AdTh.models_at_record_ofFive D G Pl0 T0 A T R F κ v₀ hC5 hT i T.σ₀ rfl
  have hχ : (Lift.chrTh (R.toLevCh.mu A.μ0) R.eta ((i : ℕ) + 1)).1 = T.chiW ((i : ℕ) + 1) T.σ₀ := by
    rw [chiTie_of_chiR T R hT.alg hT.laws.pins.2.2.1 hT.chiR i]
    ext1 x
    change R.mu0 _ x * R.xi A.μ0 x = _
    rw [TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hC5.lev.xi_base ▸ hC5.lev.xi A.μ0) x, mul_one]
  have hcast : ∀ (W : HSp D) (hV : T.V ((i : ℕ) + 1) T.σ₀ = W),
      MuVal W (T.chiW ((i : ℕ) + 1) T.σ₀) (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) ∧ ∀ γ ∈ GQ W, ∀ h,
        castDict hV (T.mu ((i : ℕ) + 1) T.σ₀) (γ * h) = castDict hV (T.mu ((i : ℕ) + 1) T.σ₀) h := by
    intro W hV
    subst hV
    have hu := hT.laws.muUnit _ (inR i) _ hσ0
    exact ⟨hT.laws.muVal _ (inR i) _ hσ0, fun γ hγ h => (hu.1 γ h).trans (by rw [hu.2.2.1 γ hγ, one_mul]; rfl)⟩
  obtain ⟨hmu, hmuQ⟩ := hcast _ hV
  obtain ⟨-, -, -, -, -, -, hr1, hrt, -, -, hdom, -⟩ := hM (T.dict ((i : ℕ) + 1) T.σ₀ 1).1
  obtain ⟨hD, hFT, -, hσ₂⟩ := GlobalTheory.T.uniformisedCover_isDictionary_frameCompatible D G Pl0 T0 A T R F κ v₀ hL hlev hgrp hfam hmods hthP hT i hstd hV C hC
  exact GlobalTheory.AdTh.CcEx.exists_ccIs_of_pair GlobalTheory.chartIndependence_unconditional hP (hχ ▸ hmu) hmuQ (rank_Wc i) hrt
    C.U₂ hσ₂ hC.2.2.2.1 hr1 hC.2.1 hdom hV0 h1 h2 h3 h4 h5 _ _ hD.2.2.1 (fun k τ => hD.2.2.2.1 k τ.1 τ.2)
    (fun k => (hFT k).1) (hC5.thP.vP i A.μ0).1 _

end GlobalTheory.CoverCc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteMatrixEqOneOfEqOneAtPlacesOver
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries.FinOneAt

set_option maxHeartbeats 1600000 in

theorem oneAt_fin_eq_one : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E _ x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ (a : Af D.host.F) (k : D.host.F) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ), Valued.v (a (HeightOneSpectrum.under (𝓞 D.host.F) P) - algebraMap D.host.F (HeightOneSpectrum.adicCompletion D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) P)) k) ≤ WithZero.exp (-(n : ℤ)) → Valued.v ((ι (a ⊗ₜ[D.host.F] 1)) P - algebraMap D.host.E (HeightOneSpectrum.adicCompletion D.host.E P) (algebraMap D.host.F D.host.E k)) ≤ WithZero.exp (-(n : ℤ))) → ∀ (V : HSp D) (l : ℕ) (z : GA D V), OneAt V l z → ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((l : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∀ i j, ((Matrix.GeneralLinearGroup.map ι.toRingHom (fin V z).1).1 i j) Q = ((1 : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) i j) Q := by
  intro D ι hι hint happ V l z hz Q hlQ i j
  let α : Af D.host.F := singleV D.host.F (Q.under (𝓞 D.host.F)) 1
  have hε : IsPlaceIdem D (Q.under (𝓞 D.host.F)) (pairA D.host.F 0 α) :=
    ⟨α, rfl, GlobalTheory.PlaceIdem.single_same _, fun v' h => GlobalTheory.PlaceIdem.single_ne h⟩
  have hlv : ((l : ℕ) : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal := by
    show _ ∈ Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) Q.asIdeal
    rw [Ideal.mem_comap, map_natCast]
    exact hlQ
  have h0 := hz _ _ hε hlv i j
  have hα : ι (finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α))) Q = 1 := by
    change ι (α ⊗ₜ[D.host.F] (1 : D.host.E)) Q = 1
    refine sub_eq_zero.1 (GlobalTheory.PlaceIdem.eq_zero_of_val Q _ fun n => ?_)
    have := happ α 1 Q n (by
      rw [map_one, GlobalTheory.PlaceIdem.single_same, sub_self, map_zero]
      exact zero_le)
    rwa [map_one, map_one] at this
  have h1 : ι (finPart D ((Formalism.L2.Theta.mt V z - 1) i j)) Q = 0 := by
    have := congrArg (fun x => ι (finPart D x) Q) h0
    simp only [map_mul, map_zero] at this
    rw [GlobalTheory.PlaceIdem.mul_ap, hα, one_mul] at this
    exact this
  have hm : ((Matrix.GeneralLinearGroup.map ι.toRingHom (fin V z).1).1 i j) = ι (finPart D (Formalism.L2.Theta.mt V z i j)) := rfl
  rw [hm]
  rw [Matrix.sub_apply, map_sub, map_sub] at h1
  refine (sub_eq_zero.1 h1).trans ?_
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one, map_one]
    rfl
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, RingHom.map_zero]
    exact congrArg (fun x : FiniteAdeleRing (𝓞 D.host.E) D.host.E => x Q) (map_zero ι)

end GlobalTheory.LevelSeries.FinOneAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeQuotientIntegralFramedPointCompleteFieldStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeQuotient_integral_framed_point_complete_field : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), HeckeStable YS iC b j := by
  first | exact @GlobalTheory.HeckeStableAt.heckeStable | exact GlobalTheory.HeckeStableAt.heckeStable | (intros; apply GlobalTheory.HeckeStableAt.heckeStable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLevelLiftBaseOfRealisationLiftStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLevelLift_of_isLevelLift_realisation : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (g : X.Γ) (κ : GA D (Wc D j)),
    Lev.IsLevelLift (Wc D j) (X.R.βW j) (X.R.datWp j X.R.triv) (X.R.eG g) κ →
    Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b (X.cG (X.R.eG g))) κ := by
  first | exact @GlobalTheory.TwistLiftW.isLevelLift_base_of_realisation_lift | exact GlobalTheory.TwistLiftW.isLevelLift_base_of_realisation_lift | (intros; apply GlobalTheory.TwistLiftW.isLevelLift_base_of_realisation_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsThetaFunctionOfMemSpanVacuumTranslates
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem isThetaFunO_of_mem_trSp : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (e : AE D) (M : ℕ) (O : Subring ℂ), ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O, IsThetaFunO ψ V W f := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP e M O f hf
  have hψ : IsStdChar D ψ (-1) := hP.1.weil.std
  have h0 : IsThetaFunO ψ V W f₀ := GlobalTheory.OneMapRef.isThetaFunO_of_isVacO hP.2.2.2.2.2.2.2.2
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, -, -, rfl⟩ := hx
    exact GlobalTheory.AnisoMean.isTheta_heisO hψ h0 y
  | zero => exact GlobalTheory.LocMod.LinSpace.isThetaFunO_zero ψ V W
  | add x y _ _ hx hy => exact GlobalTheory.LocMod.LinSpace.isThetaFunO_add hx hy
  | smul a x _ hx =>
    rw [Subring.smul_def]
    exact GlobalTheory.LocMod.LinSpace.isThetaFunO_smul (a : ℂ) hx

end GlobalTheory.LevelSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisUnitMatchAllRanks
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem unitMatch_all : ∀ r, UnitMatch r :=
  GlobalTheory.T.jacquetRallisUnitMatch_of_weilRep_quadratic GlobalTheory.T.weilRepresentation_quadraticField_exists

end GlobalTheory.JR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealPointsActFockByRealComponentsBasisStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPoints_act_fock_by_realComponents_basis : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), ∃ (w : GlobalTheory.ExportSeries.Weight D (Vc D i).rank) (BS : GlobalTheory.ExportSeries.GLR D (Vc D i).rank) (r : ↥(GinfC (Vc D i)) →* GlobalTheory.ExportSeries.GLR D (Vc D i).rank), (∀ (u : ↥(GinfC (Vc D i))) (P : PolF D (Wc D i).rank (Vc D i).rank), R.ωP i t ((u : GA D (Vc D i)), 1) (R.ptP i t P) = R.ptP i t (GlobalTheory.ExportSeries.fockGL (Wc D i).rank w BS (r u) P)) ∧ (∀ (u : ↥(GinfC (Vc D i))) (τ : D.what₂.Tau), ((GlobalTheory.ExportSeries.inBasis BS (r u) τ : GL (Fin (Vc D i).rank) ℂ) : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ) ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ) ∧ (∀ g : GlobalTheory.ExportSeries.GLR D (Vc D i).rank, (∀ τ, ((GlobalTheory.ExportSeries.inBasis BS g τ : GL (Fin (Vc D i).rank) ℂ) : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ) ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ) → ∃ u, r u = g) ∧ (∀ (τ : D.what₂.Tau) (j : Fin (Wc D i).rank), (R.MW i (sg0 D A)).ε τ j = decide ((j : ℕ) < w.p τ)) := by
  first | exact @GlobalTheory.RealPtsFock.real_points_fock | exact GlobalTheory.RealPtsFock.real_points_fock | (intros; apply GlobalTheory.RealPtsFock.real_points_fock <;> assumption)
end

