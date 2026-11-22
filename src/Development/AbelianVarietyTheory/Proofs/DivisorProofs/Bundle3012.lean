import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2733
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2751
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2905
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1470
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2895
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0018
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2826
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2953
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2928
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExtensionSecPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2929
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2830
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBiextensionExpansionGeneratorOfTauBimult
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageModelMetricsSemiPositive
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.ImageModelSemi

open GlobalTheory.CxPts GlobalTheory.TrueGeo.OfLattice ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem semiPos_of_isModelOf : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → L.SemiPos D := by
  intro K V Ω _ _ _ _ _ _ _ _ Nm W ev D X _ p L ψ s hM hev
  obtain ⟨N, n, b, g, A, c, gw, hF, hg, hc, hφ⟩ := hM.fs
  intro τ
  obtain ⟨σ, rfl⟩ : ∃ σ : K →+* ℂ, σ.comp (algebraMap (𝓞 K) K) = τ := ⟨_, extEmb_comp τ⟩
  let M : Matrix (Fin n) (Fin N) ℂ := fun k a => ∑ m, σ (c k m) * A σ m a
  have hz : Weight.NoCommonZero fun a =>
      ∑ j, M j a • secVal p (σ.comp (algebraMap (𝓞 K) K)) (s (gw j)) := by
    intro i y hy
    by_contra! h0
    have hS : ∑ a, ‖∑ k, M k a * valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun a _ => ?_
      have h1 := h0 a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
      rw [show (∑ k, M k a * valR y.1 (L.B.U i) ((s (gw k)).f i)) = 0 from h1]
      simp
    obtain ⟨w, hw⟩ := TopologicalSpace.Opens.mem_iSup.1
      (hM.bpf.ge (TopologicalSpace.Opens.mem_top (y.1 (IsLocalRing.closedPoint ℂ))))
    have hne := (secVal_ne_zero_iff (s w) hy).2 (mem_ptsIn.2 hw)
    have hb := GlobalTheory.T.norm_sq_semilinear_le_latticeFrame_norm_sq K V Nm W N n b g A c gw σ (fun w => valR y.1 (L.B.U i) ((s w).f i)) hF hg hc
      (fun m β u x hx => GlobalTheory.T.valR_imageModelSection_semilinear K V Ω Nm W ev D X p L ψ s hM hev _ i y hy m β u x hx) w
    rw [hS, mul_zero] at hb
    exact hne (by
      have : ‖valR y.1 (L.B.U i) ((s w).f i)‖ = 0 := by nlinarith [norm_nonneg (valR y.1 (L.B.U i) ((s w).f i))]
      exact norm_eq_zero.1 this)
  have key : (L.φ (σ.comp (algebraMap (𝓞 K) K))).φ = (combWeight L.isLB (fun k => s (gw k)) M hz).φ :=
    funext fun i => funext fun y => (hφ σ i y).trans (combWeight_φ L.isLB (fun k => s (gw k)) M hz i y).symm
  intro i ch y hy ξ
  have := semiPosReg_combWeight L.isLB (fun k => s (gw k)) M hz D i ch y hy ξ
  rw [key]
  exact this

end GlobalTheory.ImageModelSemi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabiliserGeneratedDiagAntidiag
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVac

theorem gen_diag_anti : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ H : Subgroup (GlobalTheory.DblVac.UD σ G.W),
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PAnti σ G.W → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ G.W v, g ∈ H := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hv H hD hA g hg
  obtain ⟨p, hpK, hpD, hpgK, hbig⟩ := GlobalTheory.T.exists_diagonalStabiliser_mul_mem_bigCell_inert σ B G.W _ _ hT.base hT.geo.hW v w hv g hg
  obtain ⟨q, hqK, hqA, p', hp'K, hp'D, he⟩ := GlobalTheory.T.doubledVacuumStabilizer_gaussDecomposition_bigCell σ G.W v (hT.base.inert v w hv).1 (p * g) hpgK hbig
  have hg' : g = p⁻¹ * (q * p') := by rw [← he]; group
  rw [hg']
  exact H.mul_mem (H.inv_mem (hD p hpK hpD)) (H.mul_mem (hA q hqK hqA) (hD p' hp'K hp'D))

end GlobalTheory.DblVac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCharpolyOfMonicIntegralAnnihilator
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
open Polynomial

namespace GlobalTheory.AV.AbVar

theorem int_of_charpoly_rat_of_monic_annihilator : ∀ (k V : Type) [Field k] [Algebra ℚ k] [AddCommGroup V] [Module k V] [Module.Finite k V] (φ : V →ₗ[k] V) (P : Polynomial ℚ) (Q : Polynomial ℤ), Q.Monic → Polynomial.aeval φ Q = 0 → P.map (algebraMap ℚ k) = φ.charpoly → ∃ P₀ : Polynomial ℤ, P₀.map (algebraMap ℤ ℚ) = P := by
  intro k V _ _ _ _ _ φ P Q hQ hφ hP
  have hinj : Function.Injective (algebraMap ℚ k) := (algebraMap ℚ k).injective
  have hPm : P.Monic := Polynomial.monic_of_injective hinj (by rw [hP]; exact LinearMap.charpoly_monic φ)
  set Qq : ℚ[X] := Q.map (algebraMap ℤ ℚ) with hQq
  have hmap : Qq.map (algebraMap ℚ k) = Q.map (algebraMap ℤ k) := by
    rw [hQq, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hG : aeval φ (Q.map (algebraMap ℤ k)) = 0 := by
    rw [aeval_map_algebraMap]; exact hφ
  have hd := GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank φ _ hG
  rw [← hP, ← hmap, ← Polynomial.map_pow, Polynomial.map_dvd_map' (algebraMap ℚ k)] at hd
  have hd' : P ∣ (Q ^ Module.finrank k V).map (algebraMap ℤ ℚ) := by
    rw [Polynomial.map_pow]; exact hd
  obtain ⟨P₀, hP₀⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ (hQ.pow _) hd'
  refine ⟨P₀, ?_⟩
  rw [hPm.leadingCoeff, Polynomial.C_1, _root_.mul_one] at hP₀
  exact hP₀

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCombinationTermsRationalPointFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntEval
open GlobalTheory.UT.CoefBasic GlobalTheory.ExpansionValueZero GlobalTheory.BoxExpansion

theorem coef_comb_pull : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (g : GtPt D (𝟙_ (Over (Sp R)))) (g' : GtPtF D (FractionRing R)), GtPt.IsPullF (FractionRing R) (toUnit (TF (R := R) (FractionRing R))).left g g' → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, g.b.left] (DegPre.lineε 1))) (l : FractionRing R), l ≠ 0 → ∀ (k : ℕ) (wk : Frm D (FractionRing R) k g'.b), wk.IsGen → (∀ (z : (TF (R := R) (FractionRing R)).left) (J : ((TF (R := R) (FractionRing R)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → GlobalTheory.UT.cst (FractionRing R) z (l ^ k) * (val wk (𝟙 _) z J).val = (val t (toUnit (TF (R := R) (FractionRing R))).left z J ^ k).val) → ∀ (s : Fam D (FractionRing R) k) (n : ℕ) (c : Fin n → FractionRing R) (fs : Fin n → ∀ α : D.X, D.SecB k α), (∀ α : D.X, GeneratorPullback.SecLin D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (s.s α) (D.famφB α) (DegPre.famε k) (fun i => fs i α) (DegPre.prB D (FractionRing R)).left (fun i => scal (fst (TF (R := R) (FractionRing R)) D.P.A).left (c i))) → ∀ a : Fin n → D.X → R, (∀ (i : Fin n) (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → sval (fs i α) (r ≫ g.b.left) z J * (val (g.s α) r z J).val * (val t r z J ^ k).val = Geo.Tor.cst r z (a i α) * (val (L := D.P.L) D.rig r z J ^ k).val) → ∀ α : D.X, l ^ k * coef s g' wk α = ∑ i, c i * algebraMap R (FractionRing R) (a i α) := by
  intro R _ _ D g g' hP t l hl k wk hwk hl' s n c fs hs a ha α
  have hτ : (toUnit (TF (R := R) (FractionRing R))).left = jFK (R := R) (FractionRing R) ≫ jK R := by
    have := Over.w (toUnit (TF (R := R) (FractionRing R)))
    simpa using this
  have hb : g'.b.left = (toUnit (TF (R := R) (FractionRing R))).left ≫ g.b.left := hP.1
  have hlk : (l ^ k) ≠ 0 := pow_ne_zero _ hl
  suffices key : IsCoef k g' wk α (s.s α) ((l ^ k)⁻¹ * ∑ i, c i * algebraMap R (FractionRing R) (a i α)) by
    rw [coef_eq key, ← _root_.mul_assoc, mul_inv_cancel₀ hlk, _root_.one_mul]
  intro z J hJ
  have e₂ : (lift (𝟙 (TF (R := R) (FractionRing R))) g'.b).left ≫ (DegPre.prB D (FractionRing R)).left =
      (toUnit (TF (R := R) (FractionRing R))).left ≫ g.b.left := by
    rw [← Over.comp_left]
    erw [lift_snd]
    exact hb
  have e₃ : (lift (𝟙 (TF (R := R) (FractionRing R))) g'.b).left ≫ (fst (TF (R := R) (FractionRing R)) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have v : val (g'.s α) (𝟙 _) z J = val (g.s α) (toUnit (TF (R := R) (FractionRing R))).left z J := by
    rw [val_corr hJ (hP.2 α), val_pull hJ, Category.id_comp]
  have bi : ∀ i, gs (lift (𝟙 (TF (R := R) (FractionRing R))) g'.b).left z ⊤
      (scal (fst (TF (R := R) (FractionRing R)) D.P.A).left (c i)) = cstH z (c i) := fun i =>
    ((gs_pull _ _ z ⊤ trivial _).trans (by rw [e₃]; rfl)).trans (cst_eq z _)
  have hai : ∀ i, sval (fs i α) ((toUnit (TF (R := R) (FractionRing R))).left ≫ g.b.left) z J *
      (val (g.s α) (toUnit (TF (R := R) (FractionRing R))).left z J).val *
      (val t (toUnit (TF (R := R) (FractionRing R))).left z J ^ k).val =
      cstH z (algebraMap R (FractionRing R) (a i α)) *
        (val (L := D.P.L) D.rig (toUnit (TF (R := R) (FractionRing R))).left z J ^ k).val := fun i => by
    rw [ha i α _ _ z J hJ]
    congr 1
    rw [hτ, GlobalTheory.UT.EvalZero.cst_base]
    simp
  have hr : rigV D (TF (R := R) (FractionRing R)).hom z J =
      val (L := D.P.L) D.rig (toUnit (TF (R := R) (FractionRing R))).left z J := by
    rw [hτ]; rfl
  have hw := hl' z J hJ
  rw [cst_eq] at hw ⊢
  refine ((IsUnit.mk0 _ hlk).map (cstH (R := R) z)).mul_left_cancel ?_
  rw [secLin_val (hs α) _ z hJ, e₂, v, hr]
  simp only [bi]
  rw [← _root_.mul_assoc, ← map_mul, ← _root_.mul_assoc, mul_inv_cancel₀ hlk, _root_.one_mul, map_sum,
    Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := hai i
  have h2 := hw
  simp only [Units.val_pow_eq_pow_val, map_mul] at h1 h2 ⊢
  linear_combination (-(cstH (R := R) z (c i))) * h1 - cstH (R := R) z (c i) *
    sval (fs i α) ((toUnit (TF (R := R) (FractionRing R))).left ≫ g.b.left) z J *
    (val (g.s α) (toUnit (TF (R := R) (FractionRing R))).left z J).val * h2

end GlobalTheory.Poinc.IntEval
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRelationKillsMixedSectionSumsLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix

noncomputable section
namespace GlobalTheory.Mum.Two.Mix

set_option maxHeartbeats 1000000 in

theorem level : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Over₀ U₁ U₂ a b → ∀ (u : ∀ χ, LB.Gen (CmpLB D₁.toPre D₂.toPre b (h χ) χ)), (∀ χ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → val ((U₂.gt e).t χ) (x ≫ ((Over.pullback (thick R I e)).map a).left) z (rr J) = val ((U₁.gt e).t (h χ)) x z (rl J) * val (u χ) (x ≫ (U₁.gt e).pG.left) z J) → ∀ (j j' e : ℕ) (N : Type) [Fintype N] (ρ : N → R) (σ : N → H0 U₂.LG.L j) (σ' : N → H0 U₁.LG.L j') (f : N → ∀ α : D₂.toPre.X, D₂.toPre.SecB j α) (f' : N → ∀ α : D₁.toPre.X, D₁.toPre.SecB j' α), (∀ ν, U₂.ExpandsAt e j (σ ν) (f ν)) → (∀ ν, U₁.ExpandsAt e j' (σ' ν) (f' ν)) → (∀ (Z : Scheme.{0}) (r : Z ⟶ G₁.left) (z : Z) (J₁ J₂), Good U₁.LG.L z J₁ → Good U₂.LG.L z J₂ → ∑ ν, constVal (r ≫ G₁.hom) z (ρ ν) * (sval (σ ν) (r ≫ a.left) z J₂ * sval (σ' ν) r z J₁) = 0) → ∀ (m : ∀ α, {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} → LB.Sec (LB.LinComb (JN D₁.toPre D₂.toPre) (mixφ D₁.toPre D₂.toPre b α) (MixedConv.mixε j j'))), (∀ α p (Z : Scheme.{0}) (r : Z ⟶ D₁.toPre.P.A.left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → sval (m α p) r z J = ∑ ν, constVal (r ≫ D₁.toPre.P.A.hom) z (ρ ν) * (sval (f ν p.1.1) (r ≫ b.left) z (rr J) * sval (f' ν p.1.2) r z (rl J) * (val (u p.1.1) r z J * val (MixedConv.cubB D₁.toPre (h p.1.1) p.1.2) r z (rl J)).val)) → ∀ (α : D₁.toPre.X), ∃ S : Finset {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α}, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D₁.toPre.P.A).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → (∀ i ∉ S, sval (m α i) (r ≫ (D₁.toPre.prBe I e).left) z J = 0) ∧ ∑ i ∈ S, sval (m α i) (r ≫ (D₁.toPre.prBe I e).left) z J = 0 := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a b h hO u hu j j' e N _ ρ σ σ' f f' hE hE' hrel m hm α
  classical
  obtain ⟨S, hS⟩ := MixedConv.expand_common U₂ e j σ f hE
  obtain ⟨S', hS'⟩ := MixedConv.expand_common U₁ e j' σ' f' hE'
  have pl := isPart_inl D₁.toPre.P.L D₂.toPre.P.L
  have pr := isPart_inr D₁.toPre.P.L D₂.toPre.P.L
  let ae := ((Over.pullback (thick R I e)).map a).left
  have hpe : ae ≫ pGl U₂ e = pGl U₁ e ≫ b.left := by
    have h₁ := congrArg (fun q => q.left) (hO e)
    have h₂ : ((Over.pullback (thick R I e)).map b).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ b.left :=
      pullback.lift_fst _ _ _
    show _ ≫ (U₂.gt e).q.left ≫ pullback.fst _ _ = ((U₁.gt e).q.left ≫ pullback.fst _ _) ≫ _
    rw [← Category.assoc]
    exact (congrArg (· ≫ pullback.fst _ _) h₁).trans ((Category.assoc _ _ _).trans
      ((congrArg ((U₁.gt e).q.left ≫ ·) h₂).trans (Category.assoc _ _ _).symm))
  have hfe : ae ≫ fGl I G₂ e = fGl I G₁ e ≫ a.left := pullback.lift_fst _ _ _
  have hp : ∀ {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e G₁).left),
      (x ≫ ae) ≫ pGl U₂ e = (x ≫ pGl U₁ e) ≫ b.left :=
    fun x => by rw [Category.assoc, Category.assoc, hpe]
  have hf : ∀ {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e G₁).left),
      (x ≫ ae) ≫ fGl I G₂ e = (x ≫ fGl I G₁ e) ≫ a.left :=
    fun x => by rw [Category.assoc, Category.assoc, hfe]
  let d : ∀ α, SecOver D₁.toPre.P.A.hom
      (LB.LinComb (JN D₁.toPre D₂.toPre) (mixφ D₁.toPre D₂.toPre b α) (MixedConv.mixε j j')) := fun α =>
    ∑ p ∈ (S ×ˢ S').subtype (fun p => h p.1 + p.2 = α), (m α p : SecOver D₁.toPre.P.A.hom _)
  have lift : ∀ n : LB.Sec (LB.LinComb (JN D₁.toPre D₂.toPre) (mixφ D₁.toPre D₂.toPre b α) (MixedConv.mixε j j')),
      (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J →
        sval n (x ≫ pGl U₁ e) z J = 0) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D₁.toPre.P.A).left) (z : Z) (J),
        Good (JN D₁.toPre D₂.toPre) z J → sval n (r ≫ (D₁.toPre.prBe I e).left) z J = 0 := fun n hn Z r z J hJ =>
    GlobalTheory.LiftTest.main R I D₁.toPre e G₁ (U₁.gt e) D₁.toPre.P.A (𝟙 _) _ (JN D₁.toPre D₂.toPre)
      (jn_isLB D₁.toPre D₂.toPre) _ _ _ n
      (fun Z x r hr z J hJ => by
        obtain rfl : r = x ≫ pGl U₁ e := (Category.comp_id r).symm.trans hr
        exact hn Z x z J hJ) Z _
      ⟨r ≫ pullback.snd _ _, by
        rw [Category.assoc, Category.assoc]; exact congrArg (r ≫ ·) pullback.condition.symm⟩ z J hJ
  refine ⟨(S ×ˢ S').subtype (fun p => h p.1 + p.2 = α), fun Z r z J hJ => ⟨fun i hi => ?_, ?_⟩⟩
  · refine lift _ (fun Z x z J hJ => ?_) Z r z J hJ
    rw [hm α i _ _ z J hJ]
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [Finset.mem_subtype, Finset.mem_product, not_and_or] at hi
    rcases hi with hi | hi
    · rw [← hp, (hS ν Z (x ≫ ae) z (rr J) (pr.good hJ)).1 _ hi, zero_mul, zero_mul, mul_zero]
    · rw [(hS' ν Z x z (rl J) (pl.good hJ)).1 _ hi, mul_zero, zero_mul, mul_zero]
  · refine (sval_sum' (π := D₁.toPre.P.A.hom) hJ _ _ _).symm.trans (lift (d α) (fun Z x z J hJ => ?_) Z r z J hJ)
    refine GlobalTheory.T.sectionValue_eq_zero_weightIndependence_level R I D₁.toPre e G₁ (U₁.gt e) D₁.toPre.P.A (𝟙 _) _ (JN D₁.toPre D₂.toPre)
      (jn_isLB D₁.toPre D₂.toPre) coprod.inl Prod.fst pl _
      (mixφ D₁.toPre D₂.toPre b) (MixedConv.mixε j j') d (insert α ((S ×ˢ S').image fun p => h p.1 + p.2)) ?_ α
      (Finset.mem_insert_self _ _) Z x _ (Category.comp_id _) z J hJ
    intro Z x r hr z J hJ
    obtain rfl : r = x ≫ pGl U₁ e := (Category.comp_id r).symm.trans hr
    have hJl : Good D₁.toPre.P.L z (rl J) := pl.good hJ
    have hJr : Good D₂.toPre.P.L z (rr J) := pr.good hJ
    obtain ⟨J₁, hJ₁⟩ := CoefBasic.exists_good' U₁.LG.isLB z
    obtain ⟨J₂, hJ₂⟩ := CoefBasic.exists_good' U₂.LG.isLB z
    let T : D₂.toPre.X × D₁.toPre.X → Z.presheaf.stalk z := fun p =>
      ∑ ν, constVal ((x ≫ pGl U₁ e) ≫ D₁.toPre.P.A.hom) z (ρ ν) *
      ((sval (f ν p.1) ((x ≫ ae) ≫ pGl U₂ e) z (rr J) * (val (tG U₂ e p.1) (x ≫ ae) z (rr J)).val) *
        (sval (f' ν p.2) (x ≫ pGl U₁ e) z (rl J) * (val (tG U₁ e p.2) x z (rl J)).val))
    have k₁ : ∀ β, sval (d β) (x ≫ pGl U₁ e) z J * (val ((U₁.gt e).t β) x z (rs coprod.inl Prod.fst J)).val =
        ∑ p ∈ (S ×ˢ S').filter (fun p => h p.1 + p.2 = β), T p := fun β => by
      refine (congrArg (· * _) (sval_sum' (π := D₁.toPre.P.A.hom) hJ _ _ _)).trans ?_
      rw [← Finset.sum_subtype_eq_sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      obtain ⟨⟨χ, δ⟩, rfl⟩ := p
      rw [hm _ _ _ _ z J hJ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ν _ => ?_
      have a₁ := congrArg Units.val (MixedConv.t_mul_val U₁ e (h χ) δ x z hJl)
      have a₂ := congrArg Units.val (hu χ e Z x z J hJ)
      simp only [Units.val_mul] at a₁ a₂ ⊢
      rw [hp]
      linear_combination (constVal ((x ≫ pGl U₁ e) ≫ D₁.toPre.P.A.hom) z (ρ ν) *
        sval (f ν χ) ((x ≫ pGl U₁ e) ≫ b.left) z (rr J) * sval (f' ν δ) (x ≫ pGl U₁ e) z (rl J) *
        (val (u χ) (x ≫ pGl U₁ e) z J).val) * a₁ -
        (constVal ((x ≫ pGl U₁ e) ≫ D₁.toPre.P.A.hom) z (ρ ν) *
        sval (f ν χ) ((x ≫ pGl U₁ e) ≫ b.left) z (rr J) * sval (f' ν δ) (x ≫ pGl U₁ e) z (rl J) *
        (val (tG U₁ e δ) x z (rl J)).val) * a₂
    refine (Finset.sum_congr rfl fun β _ => k₁ β).trans ((Finset.sum_fiberwise_of_maps_to (fun p hp =>
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp)) T).trans ?_)
    have hc : (x ≫ pGl U₁ e) ≫ D₁.toPre.P.A.hom = (x ≫ fGl I G₁ e) ≫ G₁.hom := by
      rw [Category.assoc, Category.assoc]
      exact congrArg (x ≫ ·) ((Over.w (U₁.gt e).pG).trans (Over.w (fstG I e G₁)).symm)
    have k₂ := hrel Z (x ≫ fGl I G₁ e) z J₁ J₂ hJ₁ hJ₂
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun ν _ => ?_) ((Finset.mul_sum _ _ _).symm.trans
      ((congrArg (((wv U₂ e (x ≫ ae) z (rr J ((x ≫ ae) ≫ pGl U₂ e)) (J₂ (((x ≫ ae) ≫ fGl I G₂ e) ≫ 𝟙 _)) ^ j).val *
        (wv U₁ e x z (rl J (x ≫ pGl U₁ e)) (J₁ ((x ≫ fGl I G₁ e) ≫ 𝟙 _)) ^ j').val) * ·) k₂).trans (mul_zero _)))
    rw [← Finset.mul_sum, Finset.sum_product]
    dsimp only
    rw [← Finset.sum_mul_sum, ← (hS ν Z (x ≫ ae) z (rr J) hJr).2 J₂ hJ₂,
      ← (hS' ν Z x z (rl J) hJl).2 J₁ hJ₁, hc, ← hf]
    ring

end GlobalTheory.Mum.Two.Mix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralThetaFamilyOverDegenerationFamilyPullbacStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralThetaFamily_over_degenerationFamilyPullback : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (k : ℕ) (F₀ : IntFam I D k) (E F : Type) [Field E] [Field F] [Algebra (FractionRing R) E] [Algebra (FractionRing R) F] [Algebra E F] [IsScalarTower (FractionRing R) E F] (s : Fam D E k), F₀.Over s → F₀.Over (famPull D E F GlobalTheory.globalFns_holds k s) := by
  first | exact @GlobalTheory.Mum.UpExt.over_famPull | exact GlobalTheory.Mum.UpExt.over_famPull | (intros; apply GlobalTheory.Mum.UpExt.over_famPull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrallyClosedPointLevelExtendsStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrally_closed_point_level_extends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ), (p : ℂ) ∈ W.nonunits → l'.A = p ^ n →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (ξ : Sp R ⟶ Y.X)
      (y : Sp (FractionRing R) ⟶ Xo'.XF c'), spMap (algebraMap R (FractionRing R)) ≫ ξ = y ≫ Y.j → ∀ (a : Dw.La)
      (κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ),
      (∀ (e σ : Over.mk y ⟶ Y.oF.t.G), e.left = y ≫ (Y.oF.etaA a).left → σ ^ (p ^ n) = 1 →
        Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e σ
          (unitOn (Units.map (algebraMap R (FractionRing R)).toMonoidHom (κ (σ.left ≫ Y.m.φ))))) →
    ∀ (f : R) (wf : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ ξ) ⟶ Y.t.G), wf ^ (p ^ n) = 1 →
    ∀ (g : Localization.Away f →+* FractionRing R), g.comp (algebraMap R _) = algebraMap R (FractionRing R) →
    ∀ (x0 : R →+* 𝓞_ℂ_[p]) (φ : Localization.Away f →+* ℂ_[p]),
      φ.comp (algebraMap R _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp x0 →
    ∀ (yy : Sp ℂ_[p] ⟶ Xo'.XF c'), spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ spMap x0 ≫ ξ = yy ≫ Y.j →
    ∀ (e σ : Over.mk yy ⟶ Y.oF.t.G), e.left = yy ≫ (Y.oF.etaA a).left → σ.left ≫ Y.m.φ = spMap φ ≫ wf.left →
      σ ^ (p ^ n) = 1 ∧ Out.WeilIs Y.oF.t.G Y.oF.t.PP.L ((p ^ n : ℕ) : ℤ) e σ
        (unitOn (Units.map ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp x0).toMonoidHom (κ (spMap g ≫ wf.left)))) := by
  first | exact @GlobalTheory.WeilSpec.weil_spec | exact GlobalTheory.WeilSpec.weil_spec | (intros; apply GlobalTheory.WeilSpec.weil_spec <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBiextensionComparisonGeneratorOfAdjointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBiextensionComparisonGenerator_of_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₀ : DegPre R) (q : D.P.A ⟶ D₀.P.A) (j : D₀.P.A ⟶ D.P.A), IsMonHom q → IsMonHom j → AdjCls (cls D.P.L D.P.isLB) (cls D₀.P.L D₀.P.isLB) q j → CmpTwo D D₀ q j := by
  first | exact @GlobalTheory.Mum.PowData.cmpTwo_of_adjCls | exact GlobalTheory.Mum.PowData.cmpTwo_of_adjCls | (intros; apply GlobalTheory.Mum.PowData.cmpTwo_of_adjCls <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBiextensionExpansionGeneratorOfTauBimultStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBiextensionExpansionGenerator_of_tauBimult : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (K : Type) [Fintype K] (n : K → ℤ) (T : Over (Sp R)) (x : T ⟶ D.P.A) (y : K → (T ⟶ D.P.A)), Expand D n x y := by
  first | exact @GlobalTheory.Mum.PowData.expand_of_tauBimult | exact GlobalTheory.Mum.PowData.expand_of_tauBimult | (intros; apply GlobalTheory.Mum.PowData.expand_of_tauBimult <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedTrivialLocusRigidifiedBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_trivialLocus_rigidified_bundle : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (L₀ N : LB A.left), IsAbelianScheme A → L₀.IsLB → Out.RelAmple A L₀ → N.IsLB → Out.Rigidified A N → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → ((∃ s : (N.pull φ').Gen, s.IsGen) ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  first | exact @GlobalTheory.TrivLocus.trivLocus_closed | exact GlobalTheory.TrivLocus.trivLocus_closed | (intros; apply GlobalTheory.TrivLocus.trivLocus_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCompletionOfQuasiFiniteGaloisRigidStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEtaleCompletion_of_quasiFinite_galoisRigid : ∀ (O R : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O] [CharZero O] [Algebra.EssFiniteType ℤ O] [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (f : O →+* R) [IsLocalHom f], IsAdicComplete (maximalIdeal R) R → (∀ p : Ideal R, p.IsPrime → (maximalIdeal O).map f ≤ p → p = maximalIdeal R) → ((residue R).comp f).Finite → ringKrullDim O ≤ ringKrullDim R → GalRigid f → IsEtaleCompletion f ∧ ((residue R).comp f).FormallyUnramified := by
  first | exact @GlobalTheory.QFEtale.isEtaleCompletion_of_galRigid | exact GlobalTheory.QFEtale.isEtaleCompletion_of_galRigid | (intros; apply GlobalTheory.QFEtale.isEtaleCompletion_of_galRigid <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteOfSurjectiveOfDimEq
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isFinite_of_surjective_of_dim_eq : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim → Surjective f.hom.left → IsFinite f.hom.left := by
  intro K _ A B f hd hs
  have dB : SmoothOfRelativeDimension A.dim B.X.hom := hd ▸ B.smooth
  exact GlobalTheory.OntoFinite.isFinite_of_surjective A.ab B.ab A.smooth dB f.hom

end GlobalTheory.AV.AbVar
end

