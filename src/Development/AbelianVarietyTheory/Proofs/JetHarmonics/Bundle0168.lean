import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0160
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointMoveCalculus
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0016
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.UnitFramesGeneratorRatioModulusOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0101
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0096
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0098
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0013
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0016
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0032
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0034
import Development.AbelianVarietyTheory.Definitions.Jets.IsAppBox
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0019
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ColumnValueFSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0036
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0035
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0012
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0004
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0167
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0133
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0132
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0128

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryTriangularPeriodsOfFramePointMove
section
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.LevelCusp

theorem apply_of_cols {α : Type} {m : α → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : α, Fin (m τ))
    (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (cf : ∀ τ, Fin (m τ) → Fin (m τ) → ℂ)
    (hcol : ∀ τ i, h (Pi.single (e.symm ⟨τ, i⟩) 1) =
      ∑ j, cf τ i j • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) (z : Fin g → ℂ) (τ : α) (i : Fin (m τ)) :
    h z (e.symm ⟨τ, i⟩) = ∑ j, cf τ j i * z (e.symm ⟨τ, j⟩) := by
  classical
  refine Pi.single_induction (p := fun z => h z (e.symm ⟨τ, i⟩) = ∑ j, cf τ j i * z (e.symm ⟨τ, j⟩)) z (by simp)
    (fun z w hz hw => by simp only [map_add, Pi.add_apply, hz, hw, mul_add, Finset.sum_add_distrib]) fun n a => ?_
  · beta_reduce
    obtain ⟨⟨τ', i'⟩, rfl⟩ := e.symm.surjective n
    have h1 : (Pi.single (e.symm ⟨τ', i'⟩) a : Fin g → ℂ) = a • (Pi.single (e.symm ⟨τ', i'⟩) 1 : Fin g → ℂ) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [h1, map_smul, hcol]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Pi.single_apply, EmbeddingLike.apply_eq_iff_eq]
    by_cases hτ : τ = τ'
    · subst hτ
      simp [mul_comm]
    · simp [hτ]

set_option maxHeartbeats 1000000 in

theorem exists_isometry_tri_of_frMove : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMove ρ ν (U.un k x) y' → FrBor t (U.un k' x') y' → ∃ (gam : (U.X k).Λ ≃ₗ[𝓞 E] (U.X k').Λ) (A : (E →+* ℂ) → ℕ → ℕ → ℂ), (∀ u v : (U.X k).Λ, Algebra.trace ℚ E (-(U.X k').ξ0 * herm (U.X k').Gm (gam u : Fin r → E) (gam v : Fin r → E)) = Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (u : Fin r → E) (v : Fin r → E))) ∧ (∀ τ i j, j < i → A τ i j = 0) ∧ (∀ τ, ∀ i < Dw.mult τ, ∀ v : (U.X k).Λ, Formalism.L2.PjFree.perFr (U.X k') x'.1 (gam v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) i = ∑ j ∈ Finset.range (Dw.mult τ), A τ i j * Formalism.L2.PjFree.perFr (U.X k) x.1 (v : Fin r → E) (Formalism.L2.PjFree.relab c σ τ) j) ∧ ∀ τ (i : Fin (Dw.mult τ)), A τ i i = Formalism.L2.PjFree.toC (t (some ⟨τ, i⟩) : CAt σ) := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U _ hU ρ ν k k' x x' y' t hM hB
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hEF, hpt⟩ := hU
  obtain ⟨P, hP, p, hPx, hv, -⟩ := hpt k x
  obtain ⟨P', hP', p', hPx', hv', -⟩ := hpt k' x'
  obtain ⟨gam, h, hiso, hh, hex⟩ := exists_isometry_of_sabMap F ν p p'
    (by rw [← hPx, ← hPx', ← hB.1]; exact hM.1.symm)
  choose cf hcf1 hcf2 hcf3 using hB.2.1
  have hcol : ∀ τ i, h.toLinearMap (Pi.single (e.symm ⟨τ, i⟩) 1) =
      (∑ j, (show ℂ from cf τ i j) • (Pi.single (e.symm ⟨τ, j⟩) 1 : Fin g → ℂ)) := by
    intro τ i
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F _ P' p' _ ((U.un k' x').u τ) _ (hv' τ) (cf τ i)
      (y'.u τ i)).1 (hPx' ▸ hcf3 τ i)
    have d0 := FibreDeriv.isDerivAt0_comp (hv τ i) ν.φ
    simp only [← hex] at d0
    have d2 := (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F _ P' p') h.toLinearMap _ _).1 d0
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ P' p'
    rw [hM.2.1] at d1
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  refine ⟨(φ k).symm ≪≫ₗ gam ≪≫ₗ φ k',
    fun τ i j => if hij : i < Dw.mult τ ∧ j < Dw.mult τ then
      Formalism.L2.PjFree.toC (cf τ ⟨j, hij.2⟩ ⟨i, hij.1⟩) else 0, fun u v => ?_, fun τ i j hji => ?_,
    fun τ i hi v => ?_, fun τ i => ?_⟩
  · obtain ⟨u, rfl⟩ := (φ k).surjective u
    obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [← hEF, ← hEF, hiso]
  · beta_reduce
    split_ifs with hij
    · exact hcf2 τ _ _ hji
    · rfl
  · obtain ⟨v, rfl⟩ := (φ k).surjective v
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    have a1 := hP' (gam v) (e.symm ⟨τ, ⟨i, hi⟩⟩)
    rw [Equiv.apply_symm_apply] at a1
    rw [← a1, hh, Finset.sum_range]
    refine (apply_of_cols e h.toLinearMap (fun τ i j => cf τ i j) hcol (P v) τ ⟨i, hi⟩).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    rw [hP, Equiv.apply_symm_apply, dif_pos ⟨hi, j.2⟩]
    rfl
  · beta_reduce
    rw [dif_pos ⟨i.2, i.2⟩]
    exact congrArg _ (hcf1 τ i)

end GlobalTheory.LevelCusp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsProductDataCopiesTrivialisationValuation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.PowData

set_option maxHeartbeats 1000000 in

theorem exists_powData : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
 letI := H.starRing
 ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ → (∃ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q) ∧ ∀ n : ℕ, ∃ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) (_ : GrpObj G') (_ : IsCommMonObj G') (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (_ : UnifPowOf3 pD pA pG U' P.U) (_ : Module (𝓞 E) D'.toPre.X) (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) ∧ (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ Q : P.D.toPre.X → ℤ, IsQ P.D.toPre ϖ Q → ∀ (α : 𝓞 E) (N : ℕ), 0 < N → α * star α = (N : 𝓞 E) → ∃ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), NuGe D' (sumQ pD.xe Q) F v 1 θ 0 ∧ ThFrame D' ϖ F θ ∧ PullAl D' F oD' α 1 N θ θα := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C P ϖ hϖ
  obtain ⟨hL, hL2, -, hL4, -⟩ := firstFiveLaws
  have hT := GlobalTheory.twistBaseChange
  refine ⟨?_, fun n => ?_⟩
  · choose Q hQ using exists_QVal hϖ P.D
    exact ⟨Q, hQ⟩
  obtain ⟨t', P', pG, pD, pA, ⟨PU⟩, -⟩ := PelUnifPowerDvr.main hL hT T.V E H C.I.G P n
  obtain ⟨M, oD, hx, hact⟩ := powOAct_of_globalFns hL.globalFns E H T.V C.I.G P n P'.D pD
  refine ⟨P'.D, P'.A, t'.G, inferInstance, inferInstance, pD, pA, pG, P'.U, PU, M, oD, hx, hact, ?_⟩
  intro F _ _ _ _ _ _ v hv Q hQ α N hN hα
  obtain ⟨θ, hν, hθ⟩ := exists_thetaFrame hL hL2 hL4 hT T.V ϖ hϖ P'.D (sumQ pD.xe Q)
    (QBox.main T.V ϖ hϖ n P.D P'.D pD Q hQ) F v hv
  letI := M
  have hw : TraceFormTwistIso P'.D.toPre oD H.w0 :=
    PsiWZeroProd.main T.V n P.D.toPre P'.D.toPre pD (𝓞 E) (fun a x => funext (hx a x)) P.oD oD hact H.w0 P.w0
  obtain ⟨f, -, hf⟩ := PullLin.exists_pull_linearMap hL T.V P'.D F (𝓞 E) oD H.w0 hw α N 1 hN le_rfl hα
  exact ⟨θ, f θ, hν, hθ, (hf _ _).2 rfl⟩

end GlobalTheory.PowData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRationalIsometryOfTraceIsometryStatement
section
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_isometry_of_trace_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r), (∀ τ : E →+* ℂ, ‖τ X.ξ0‖ = ‖τ X'.ξ0‖) → ∀ (gam : X.Λ ≃ₗ[𝓞 E] X'.Λ), (∀ u v : X.Λ, Algebra.trace ℚ E (-X'.ξ0 * herm X'.Gm (gam u : Fin r → E) (gam v : Fin r → E)) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (u : Fin r → E) (v : Fin r → E))) → ∃ (a : GL (Fin r) E) (ε : E), (ε = 1 ∨ ε = -1) ∧ X'.ξ0 = ε * X.ξ0 ∧ (∀ v : X.Λ, (a : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E) = (gam v : Fin r → E)) ∧ (∀ v, v ∈ X.Λ ↔ (a : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ X'.Λ) ∧ ∀ u v, herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = ε * herm X.Gm u v := by
  first | exact @GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry | exact GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry | (intros; apply GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsThetaOfField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open GlobalTheory.BoxApp

namespace GlobalTheory.ThetaLift

theorem exists_theta_zero {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left) {T : Over S} (x : T ⟶ A) :
    ∃ θ : ThetaGrp A L ((0 : ℕ) : ℤ) T, θ.pt = x := by
  refine ⟨⟨x, ⟨fun _ => 1⟩, ?_⟩, rfl⟩
  refine isGen_of_gm (M := L) (K := Fin 2) (φ := ![(snd T A).left, (translPt A x).left])
    (ε := ![((0 : ℕ) : ℤ), -((0 : ℕ) : ℤ)]) _ fun w j j' h h' => ?_
  refine (map_one _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (map_one _)).symm)
  simp [trF, Fin.prod_univ_two]

theorem exists_theta_of_field : ∀ (K : Type) [Field K] (A : PolAV (Sp K)) (Y : Over (Sp K)) (F : Type) [Field F] (e : Y.left ≅ Sp F) (k : ℕ) (x : Y ⟶ A.A), x ^ k = 1 → ∃ θ : ThetaGrp A.A A.L (k : ℤ) Y, θ.pt = x := by
  intro K _ A Y F _ e k x hx
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact exists_theta_zero A.L x
  · have : Subsingleton (Sp F) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
    have : Nonempty (Sp F) := inferInstanceAs (Nonempty (PrimeSpectrum F))
    have : Subsingleton Y.left := e.hom.homeomorph.toEquiv.subsingleton
    have : Nonempty Y.left := e.hom.homeomorph.toEquiv.nonempty
    exact GlobalTheory.BoxTheta.exists_theta GlobalTheory.firstFiveLaws.1.kerPow A hk x hx

end GlobalTheory.ThetaLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTranslatedNormalisedPullbackSection
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory

namespace TransPullEx

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (L : RigLB A)

theorem exists_isNormPull (φ : A ⟶ A) [IsMonHom φ] (a b : ℤ)
    (β : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) (hβ : β.IsGen)
    {T : Over S} (s : LB.Sec (LPow A L.L b T)) : ∃ s', IsNormPull A L φ a b s s' := by
  have hL := L.isLB
  have ha : eSec A ≫ φ.left = eSec A := by simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨α₀, hα₀, hv₀⟩ := exists_gen hL (φ' := ![𝟙 A.left, φ.left]) (ε' := ![a, -b])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, ha, Category.comp_id]
      rw [← zpow_add, ← zpow_add, ← zpow_add, show -a + - -b + (a + -b) = 0 by ring, zpow_zero,
        _root_.mul_one])
    (LB.mulGen L.L _ _ _ _ β (LB.pullGen L.L _ _ (LB.mulGen L.L _ _ _ _
      (LB.invGen L.L _ _ (LB.pullGen L.L _ _ β (eSec A)))
      (LB.mulGen L.L _ _ _ _ (rigPow A L.L L.rig a) (rigPow A L.L L.rig (-b)))) A.hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hβ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hβ _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (NormMulUniv.rigPow_isGen L.rigGen _)
        (NormMulUniv.rigPow_isGen L.rigGen _))) _))
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ≫ φ).left]) (ε' := ![a, -b])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ a) (Category.comp_id _)
      · rfl)
    (LB.pullGen L.L ![𝟙 A.left, φ.left] ![a, -b] α₀ (snd T A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨s', hs', -⟩ := existsUnique_isTwistPull S A L.L hL T (endOver A T φ) (snd T A ≫ φ) (lift_snd _ _) a b α hα s
  refine ⟨s', α₀, α, hα₀, corr_of_val hL fun y J hJ => ?_, corr_of_val hL fun y J hJ => hv _ _ y J hJ, hs'⟩
  rw [val_pull hJ, hv₀ _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, NormMulUniv.eSec_hom, Category.comp_id,
    val_mul hJ, val_inv, val_pull hJ, mul_inv_cancel_left]

end TransPullEx

theorem exists_isTransPull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (F : Type) [Field F] [IsAlgClosed F] (xF : Sp F ⟶ Xo.X) (α : 𝓞 E) (N : ℕ), Odd N → α * star α = (N : 𝓞 E) → ∀ (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (ptO Xo xF))) (b : ptO Xo xF ⟶ Xo.univ.t.G), b ^ N = 1 → ∃ hh, IsTransPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) N s b hh := by
  intro E _ _ _ H Dw l Xo c F _ _ xF α N hN hα s b hb
  letI := H.starRing
  have hLaw : Laws := firstFiveLaws.1
  have := UnivPol.isLocallyNoetherian Xo
  have := Xo.univ.t.act.hom α
  have hL := Xo.univ.t.PP.isLB
  have h := PullGenG.hasGen_pull Xo.univ.t.PP Xo.univ.t.cub Xo.univ.t.act.toRingAct H.w0 α N hα (Xo.univ.t.adj α)
    Xo.univ.t.prim 1
  rw [Nat.one_mul] at h
  obtain ⟨β, hβ⟩ := h.gen hL (K' := Fin 2) ![𝟙 Xo.univ.t.G.left, (Xo.univ.t.act.act α).left] ![(N : ℤ), -1] rfl
  obtain ⟨h₁, hh₁⟩ := TransPullEx.exists_isNormPull Xo.univ.t.PP (Xo.univ.t.act.act α) (N : ℤ) 1 β hβ s
  obtain ⟨⟨U, hU⟩, -⟩ := symLift_exists_unique_of_cast hLaw Xo.X (UnivPol.pol Xo) N hN
    (UnivPol.isUnit_natCast Xo _ hN.pos) (N : ℤ) rfl (ptO Xo xF) b hb
  obtain ⟨hh, hhh, -⟩ := existsUnique_isTwistPull Xo.X Xo.univ.t.G Xo.univ.t.PP.L hL (ptO Xo xF)
    (translT _ U.pt) (translPt _ U.pt) (lift_snd _ _) (N : ℤ) (N : ℤ) U.φ U.isGen h₁
  exact ⟨hh, h₁, hh₁, hb, U, hU, hhh⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FiniteOrderThetaOperatorsRatioRootOfUnity
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory

theorem exists_rootOfUnity_smul_of_pow_eq_one {F N : Type} [Field F] [AddCommGroup N] [Module F N]
    (Φ : Module.End F N) (ζ ξ : F) {M M' : ℕ} (hM : 1 ≤ M) (hM' : 1 ≤ M')
    (h : (ζ • Φ) ^ M = 1) (h' : (ξ • Φ) ^ M' = 1) :
    ∃ u : F, (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧ ξ • Φ = u • (ζ • Φ) := by
  rcases subsingleton_or_nontrivial (Module.End F N) with hs | hn
  · exact ⟨1, ⟨1, Nat.one_pos, one_pow _⟩, Subsingleton.elim _ _⟩
  have hζ : ζ ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_pow (by omega)] at h
    exact zero_ne_one h
  have e : ξ • Φ = (ξ / ζ) • (ζ • Φ) := by rw [smul_smul, div_mul_cancel₀ _ hζ]
  refine ⟨ξ / ζ, ⟨M * M', by positivity, ?_⟩, e⟩
  have a : (ξ • Φ) ^ (M * M') = 1 := by rw [mul_comm M M', pow_mul, h', one_pow]
  rw [e, smul_pow, pow_mul (ζ • Φ), h, one_pow] at a
  have b : ((ξ / ζ) ^ (M * M') - 1) • (1 : Module.End F N) = 0 := by rw [sub_smul, a, one_smul, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 b).resolve_right one_ne_zero)

theorem finOrd_ratio_rootOfUnity : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (w w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (ζ ζ' : F), w.IsGen → w'.IsGen → FinOrd D F k p w ζ → FinOrd D F k p w' ζ' → ∃ u : F, (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧ ∀ s t₀ t t₀' t' : Fam D.toPre F k, PhiRel D.toPre F k p w s t₀ → Fam.IsSmul D.toPre F ζ t₀ t → PhiRel D.toPre F k p w' s t₀' → Fam.IsSmul D.toPre F ζ' t₀' t' → Fam.IsSmul D.toPre F u t t' := by
  intro V _ _ _ _ ϖ _ D F _ _ k hk p w w' ζ ζ' hw hw' h h'
  have hG : GlobalFnsSt := GlobalTheory.firstFiveLaws.1.globalFns
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hG V _ D F k hk p w hw
  obtain ⟨Φ', hΦ'⟩ := phiFun_of_globalFns hG V _ D F k hk p w' hw'
  obtain ⟨c, hc⟩ := ThetaFinOrd.exists_scalar hG p w' w hw' hw Φ' Φ
    (fun s => (hΦ' _ _).2 rfl) (fun s => (hΦ _ _).2 rfl)
  obtain ⟨M, hM, hU⟩ := (ThetaFinOrd.finOrd_iff p w ζ Φ hΦ).1 h
  obtain ⟨M', hM', hW⟩ := (ThetaFinOrd.finOrd_iff p w' ζ' Φ' hΦ').1 h'
  rw [hc, smul_smul] at hW
  obtain ⟨u, hu, e⟩ := exists_rootOfUnity_smul_of_pow_eq_one (F := F) (N := Fam D.toPre F k) Φ ζ (ζ' * c)
    hM hM' hU hW
  refine ⟨u, hu, fun s t₀ t t₀' t' a b a' b' => ?_⟩
  rw [hΦ] at a
  rw [hΦ'] at a'
  rw [DVR.isSmul_iff] at b b' ⊢
  have f := LinearMap.congr_fun e s
  simp only [LinearMap.smul_apply] at f
  rw [b', a', b, a, hc, LinearMap.smul_apply, smul_smul, f]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrMoveValues
section
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.MoveValues

open GlobalTheory.MoveCalc

noncomputable abbrev cpt : Sp ℂ := IsLocalRing.closedPoint ℂ

noncomputable def ev : (Sp ℂ).presheaf.stalk cpt →+* ℂ := (stalkClosedPointIso (CommRingCat.of ℂ)).hom.hom

theorem mem_iff {X : Scheme.{0}} (f : Sp ℂ ⟶ X) (U : X.Opens) : f cpt ∈ U ↔ ⊤ ≤ f ⁻¹ᵁ U :=
  ⟨fun h p _ => by
    rw [Subsingleton.elim (α := PrimeSpectrum ℂ) p cpt]
    exact h, fun h => h trivial⟩

theorem ev_gs {X : Scheme.{0}} (f : Sp ℂ ⟶ X) (U : X.Opens) (h : f cpt ∈ U) (a : Γ(X, U)) :
    ev (gs f cpt U a) = valAt' f U a := by
  have h' := (mem_iff f U).1 h
  rw [gs_eq f cpt U h, valAt', dif_pos h', valAt, ← germ_stalkClosedPointIso_hom (CommRingCat.of ℂ)]
  exact congrArg ev (TopCat.Presheaf.germ_res_apply (Sp ℂ).presheaf (homOfLE h') cpt trivial _).symm

theorem ev_gm {X : Scheme.{0}} (f : Sp ℂ ⟶ X) (U : X.Opens) (h : f cpt ∈ U) (a : Γ(X, U)ˣ) :
    ev (gm f cpt U a).val = valAt' f U a.val :=
  (congrArg ev (gs_unit f cpt U h a).symm).trans (ev_gs f U h _)

section General

variable {X Y Y' : Scheme.{0}} {L : LB X} {F : X ⟶ X}

theorem mem_div {p : Sp ℂ ⟶ X} {i j : L.ι} :
    ⊤ ≤ p ⁻¹ᵁ (LB.div (L.pull F) L).U ((fun _ => i), j) ↔ F (p cpt) ∈ L.U i ∧ p cpt ∈ L.U j :=
  (mem_iff p _).symm.trans (and_congr_left' (mem_pull (F := F) (J := fun _ => i)))

theorem ev_gw (w : LB.Iso L (L.pull F)) (p : Sp ℂ ⟶ X) {i j : L.ι} (hi : F (p cpt) ∈ L.U i) (hj : p cpt ∈ L.U j) :
    ev (gw w p cpt i j).val =
      valAt' p ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val :=
  ev_gm p _ (show p cpt ∈ (L.pull F).U (fun _ => i) ⊓ L.U j from ⟨mem_pull.2 hi, hj⟩) _

theorem val_ne (w : LB.Iso L (L.pull F)) (p : Sp ℂ ⟶ X) {i j : L.ι} (hi : F (p cpt) ∈ L.U i) (hj : p cpt ∈ L.U j) :
    valAt' p ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val ≠ 0 := by
  rw [← ev_gw w p hi hj]
  exact ((gw w p cpt i j).isUnit.map ev).ne_zero

theorem val_pgen {w : LB.Iso L (L.pull F)} (h : PGen w) (p : Sp ℂ ⟶ X) {i j i' j' : L.ι}
    (hi : F (p cpt) ∈ L.U i) (hj : p cpt ∈ L.U j) (hi' : F (p cpt) ∈ L.U i') (hj' : p cpt ∈ L.U j') :
    valAt' p ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val *
        valAt' p (L.U j ⊓ L.U j') (L.g j j').val =
      valAt' (p ≫ F) (L.U i ⊓ L.U i') (L.g i i').val *
        valAt' p ((LB.div (L.pull F) L).U ((fun _ => i'), j')) (w.s ((fun _ => i'), j')).val := by
  have e : gw w p cpt i j * gm p cpt _ (L.g j j') = gm (p ≫ F) cpt _ (L.g i i') * gw w p cpt i' j' := by
    rw [h _ p cpt i i' j j' hi hi' hj hj', mul_right_comm, inv_mul_cancel_right]
  rw [← ev_gw w p hi hj, ← ev_gw w p hi' hj', ← ev_gm p (L.U j ⊓ L.U j') ⟨hj, hj'⟩,
    ← ev_gm (p ≫ F) (L.U i ⊓ L.U i') ⟨hi, hi'⟩, ← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul, e]

theorem val_pmaps {w : LB.Iso L (L.pull F)} {e : Y ⟶ X} {t : LB.Gen (L.pull e)} {ρ : Y ⟶ Y} (he : e ≫ F = ρ ≫ e)
    (h : PMaps w (K := PUnit) (fun _ => e) (fun _ => e) (fun _ => 1) t t ρ) (x : Sp ℂ ⟶ Y) {i j : L.ι}
    (hi : F ((x ≫ e) cpt) ∈ L.U i) (hj : (x ≫ e) cpt ∈ L.U j) :
    valAt' (x ≫ ρ) ((L.pull e).U (fun _ => i)) (t.s (fun _ => i)).val =
      valAt' (x ≫ e) ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val *
        valAt' x ((L.pull e).U (fun _ => j)) (t.s (fun _ => j)).val := by
  have A := h _ x cpt (fun _ => i) (fun _ => j) (fun _ => hi) (fun _ => hj)
  rw [Fintype.prod_unique, zpow_one] at A
  have m : (x ≫ ρ) cpt ∈ (L.pull e).U (fun _ => i) := mem_pull.2 (by
    have h' : (e ≫ F) (x cpt) ∈ L.U i := hi
    rw [he] at h'
    exact h')
  rw [← ev_gw w (x ≫ e) hi hj, ← ev_gm (x ≫ ρ) _ m, ← ev_gm x ((L.pull e).U (fun _ => j)) (mem_pull.2 hj),
    ← map_mul, ← Units.val_mul]
  exact congrArg (fun u : ((Sp ℂ).presheaf.stalk cpt)ˣ => ev u.val) A

theorem val_carry {w : LB.Iso L (L.pull F)} {q : Y ⟶ X} {q' : Y' ⟶ X} {pm : Y ⟶ Y'} (hpm : pm ≫ q' = q ≫ F)
    {a : Fam L q} {a' : Fam L q'} (h : Carry w pm a a') (pt : Sp ℂ ⟶ Y) {i j : L.ι}
    (hi : F ((pt ≫ q) cpt) ∈ L.U i) (hj : (pt ≫ q) cpt ∈ L.U j) :
    valAt' (pt ≫ pm) _ (a' fun _ => i) =
      valAt' (pt ≫ q) ((LB.div (L.pull F) L).U ((fun _ => i), j)) (w.s ((fun _ => i), j)).val *
        valAt' pt _ (a fun _ => j) := by
  have m : (pt ≫ pm) cpt ∈ LB.wchart L (fun _ : Fin 1 => q') (fun _ => i) := mem_chart.2 (by
    have h' : (q ≫ F) (pt cpt) ∈ L.U i := hi
    rw [← hpm] at h'
    exact h')
  rw [← ev_gw w (pt ≫ q) hi hj, ← ev_gs (pt ≫ pm) _ m,
    ← ev_gs pt (LB.wchart L (fun _ : Fin 1 => q) (fun _ => j)) (mem_chart.2 hj), ← map_mul]
  exact congrArg ev (h _ pt cpt i j hi hj)

end General

theorem frMove_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (y y' : FrPt Xo c (CAt σ)), FrMove ρ ν y y' → ∃ (O : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → Xo.univ.t.G.left.Opens) (ω : ∀ i j, Γ(Xo.univ.t.G.left, O i j)), (∀ i j (p : Sp ℂ ⟶ Xo.univ.t.G.left), ⊤ ≤ p ⁻¹ᵁ O i j ↔ (⊤ ≤ (p ≫ ν.φ) ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ p ⁻¹ᵁ Xo.univ.t.PP.L.U j)) ∧ (∀ i j (p : Sp ℂ ⟶ Xo.univ.t.G.left), ⊤ ≤ p ⁻¹ᵁ O i j → valAt' p (O i j) (ω i j) ≠ 0) ∧ (∀ i j i' j' (p : Sp ℂ ⟶ Xo.univ.t.G.left), ⊤ ≤ p ⁻¹ᵁ O i j → ⊤ ≤ p ⁻¹ᵁ O i' j' → valAt' p (O i j) (ω i j) * valAt' p (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val = valAt' (p ≫ ν.φ) (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * valAt' p (O i' j') (ω i' j')) ∧ (∀ i j (x : Sp ℂ ⟶ Xo.X) (p : Sp ℂ ⟶ Xo.univ.t.G.left), p = x ≫ eSec Xo.univ.t.G → ⊤ ≤ p ⁻¹ᵁ O i j → valAt' (x ≫ ρ) ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val = valAt' p (O i j) (ω i j) * valAt' x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧ ∀ i j (pt : Sp ℂ ⟶ Gx y.x) (pt' : Sp ℂ ⟶ Gx y'.x) (p : Sp ℂ ⟶ Xo.univ.t.G.left), pt ≫ Formalism.L2.PjFree.gxFst y.x = p → pt ≫ Formalism.L2.PjFree.gxSnd y.x = 𝟙 (Sp ℂ) → pt' ≫ Formalism.L2.PjFree.gxFst y'.x = p ≫ ν.φ → pt' ≫ Formalism.L2.PjFree.gxSnd y'.x = 𝟙 (Sp ℂ) → ⊤ ≤ p ⁻¹ᵁ O i j → valAt' pt' ((PPx y'.x).U (fun _ => i)) (y'.s.f (fun _ => i)) = valAt' p (O i j) (ω i j) * valAt' pt ((PPx y.x).U (fun _ => j)) (y.s.f (fun _ => j)) := by
  intro E _ _ _ H Dw l Xo c σ ρ ν y y' h
  obtain ⟨hx, hu, pm, w, hf, hs, hw, hc⟩ := frMove_iff_carry.1 h
  obtain ⟨g, r, -⟩ := (cubIso_iff ν w).1 hw
  refine ⟨fun i j => (LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j),
    fun i j => (w.s ((fun _ => i), j)).val, fun i j p => ?_, fun i j p hp => ?_, fun i j i' j' p hp hp' => ?_,
    fun i j x p e hp => ?_, fun i j pt pt' p e₁ e₂ e₃ e₄ hp => ?_⟩
  · exact mem_div.trans (and_congr (mem_iff (p ≫ ν.cm.F) _) (mem_iff p _))
  · exact val_ne w p (mem_div.1 hp).1 (mem_div.1 hp).2
  · exact val_pgen g p (mem_div.1 hp).1 (mem_div.1 hp).2 (mem_div.1 hp').1 (mem_div.1 hp').2
  · subst e
    have A := val_pmaps ν.cm.e_comm r x (mem_div.1 hp).1 (mem_div.1 hp).2
    rw [ν.base] at A
    exact A
  · subst e₁
    obtain rfl : pt' = pt ≫ pm := by
      apply Limits.pullback.hom_ext
      · exact e₄.trans (e₂.symm.trans ((Category.assoc _ _ _).trans (congrArg (pt ≫ ·) hf)).symm)
      · exact e₃.trans ((Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (congrArg (pt ≫ ·) hs)).symm)
    exact val_carry hs hc pt (mem_div.1 hp).1 (mem_div.1 hp).2

end GlobalTheory.MoveValues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlacesMatchCmTypeFrobeniusOfParameters
section
set_option autoImplicit false

namespace GlobalTheory.GoodDepth

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

theorem placeTie_of_pins : ∀ (D : D7) (L : SizeData₂ D) (T : Core D), T.Q.Pins →
    PlaceTie (numOf D L) T.Q.c (fun z => DV.tauEmb D (plOf D z)) := by
  intro D L T hp
  have hh := hp.1
  refine ⟨?_, ?_, hh.1, D.host.hostE_isGalois, ?_, ?_, ?_⟩
  · intro z z' h
    exact (plOf_bijective_card D).1.1 (GlobalTheory.LeafCompare.tauEmb_inj h)
  · intro τ
    constructor
    · intro hτ
      obtain ⟨t, ht⟩ := GlobalTheory.LeafCompare.exists_tau T.Q hh τ hτ
      obtain ⟨z, hz⟩ := (plOf_bijective_card D).1.2 t
      exact ⟨z, by rw [ht, ← hz]⟩
    · rintro ⟨z, rfl⟩
      exact hh.2.2.2 _
  · intro σ τ
    exact D.host.galE_injective (by
      rw [D.host.galE_mul, D.host.galE_mul, mul_comm])
  · intro p hp h2 hq hd
    exact GlobalTheory.GoodDepth.not_dvd_discr_host D.R D.host p hp h2 hq hd
  · intro la hla z x
    exact GlobalTheory.FrobPlace.frob_place D L T.Q.H _ T.Q.c la hla z x

end GlobalTheory.GoodDepth
end

