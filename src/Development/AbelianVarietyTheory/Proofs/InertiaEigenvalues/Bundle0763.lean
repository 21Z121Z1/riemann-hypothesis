import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0754
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0050
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0757
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0749
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0755
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0745
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0756

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineClassFromMonodromyKernelElementStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_class_from_monodromy_kernel_element : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Numerics l e N η H Sig U → ∀ T : QLat LL, IsGood a ϖ Pl T Sig U → ∀ Pk : Pack a ϖ η H T, ∀ c ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, ∃ y ∈ Pk.D.Y, Pk.D.Mon y = 0 ∧ Pk.R.ClassOf y ((l : ↥LL.1) ^ GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N (maxPeriod l Sig) • c) := by
  first | exact @GlobalTheory.BKGal.ExtClass.main | exact GlobalTheory.BKGal.ExtClass.main | (intros; apply GlobalTheory.BKGal.ExtClass.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubledLagrangianTermDependsOnlyOnIsotropicMeans
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section
namespace GlobalTheory.LagMeans

set_option maxHeartbeats 400000 in

theorem lagTerm_eq_of_means : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → ∀ (Y : Lag W) (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), IsLagFrame W Y C → ∀ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) → ∀ (ν : Measure (Mx D s V.rank)) (𝓨 : Set (Mx D s V.rank)), IsCovolOne (GlobalTheory.MixModel.ratMx D s V.rank) ν 𝓨 → ∀ f₁ f₁' f₂ : WO V W → ℂ, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₁' → IsThetaFunO ψ V W f₂ → (∀ x : WO V W, HMul.hMul ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) I * W.gram).map (incA D)) x = (0 : Mx D s V.rank) → ∫ y in 𝓨, f₁ (HMul.hMul (I.map (incA D)) y + x) ∂ν = ∫ y in 𝓨, f₁' (HMul.hMul (I.map (incA D)) y + x) ∂ν) → lagTerm μ 𝓕 C f₁ f₂ = lagTerm μ 𝓕 C f₁' f₂ := by
  intro D ψ hψ V W μ 𝓕 hμ Y C hC s I hI hspan ν 𝓨 hν f₁ f₁' f₂ h₁ h₁' h₂ hmean
  have hmem : ∀ j, ((fun a => I a j), (0 : Fin W.rank → D.host.E)) ∈ Y.1 := fun j => by
    have : (fun a => I a j) ∈ Y.1.comap (LinearMap.inl D.host.E _ _) := hspan ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this
  have mcol : ∀ k, ((fun a => C.1 a k), (fun a => C.2 a k)) ∈ Y.1 := fun k => hC ▸ Submodule.subset_span ⟨k, rfl⟩
  obtain ⟨t, J, K, L, M, e1, e2, e3, e4, e5, e6, e7⟩ := GlobalTheory.T.exists_adapted_frame_of_isotropic_columns' D.host.E W.rank Y.1 Y.2.1 C hC s I hI.2.1 hmem
  obtain ⟨η, 𝓥, hη⟩ := GlobalTheory.MixModel.exists_isCovolOne D t V.rank
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.integral_fundamentalDomain_eq_iterated_rationalSplitting D W.rank V.rank s t J K L M e3 e4 e5 e6 e7 μ 𝓕 hμ ν 𝓨 hν η 𝓥 hη
  have hB : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) I * W.gram * C.1 = 0 := by
    rw [Matrix.mul_assoc]
    funext j k
    have := Y.2.2 _ (hmem j) _ (mcol k)
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero] at this
    simpa only [Matrix.mul_apply, GlobalTheory.MixModel.cT_sig, Matrix.conjTranspose_apply, Matrix.zero_apply] using this
  have hψ' : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  have per : ∀ f, IsThetaFunO ψ V W f → ∀ γ ∈ GlobalTheory.MixModel.ratMx D W.rank V.rank, ∀ u : Mx D W.rank V.rank,
      f (ratMul C.1 (γ + u)) * star (f₂ (ratMul C.2 (γ + u))) = f (ratMul C.1 u) * star (f₂ (ratMul C.2 u)) := by
    rintro f hf _ ⟨γ, rfl⟩ u
    exact GlobalTheory.RawLift.Model.integrand_periodic hψ' hC hf h₂ γ u
  have cont : ∀ f, IsThetaFunO ψ V W f → Continuous fun u : Mx D W.rank V.rank => f (ratMul C.1 u) * star (f₂ (ratMul C.2 u)) :=
    fun f hf => (hf.cont.comp (continuous_const.matrix_mul continuous_id)).mul
      (continuous_star.comp (h₂.cont.comp (continuous_const.matrix_mul continuous_id)))
  unfold lagTerm
  rw [hκ _ (cont f₁ h₁) (per f₁ h₁), hκ _ (cont f₁' h₁') (per f₁' h₁')]
  congr 1
  congr 1
  funext v
  have r1 : ∀ y : Mx D s V.rank, ratMul C.1 (HMul.hMul (J.map (incA D)) y + HMul.hMul (K.map (incA D)) v) =
      HMul.hMul (I.map (incA D)) y + HMul.hMul ((C.1 * K).map (incA D)) v := fun y => by
    unfold ratMul
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, e1]
  have r2 : ∀ y : Mx D s V.rank, ratMul C.2 (HMul.hMul (J.map (incA D)) y + HMul.hMul (K.map (incA D)) v) =
      HMul.hMul ((C.2 * K).map (incA D)) v := fun y => by
    unfold ratMul
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, e2,
      Matrix.map_zero (incA D) (map_zero (incA D))]
    simp only [Matrix.zero_mul, zero_add]
  simp only [r1, r2]
  rw [integral_mul_const, integral_mul_const]
  congr 1
  refine hmean _ ?_
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.mul_assoc, hB, Matrix.zero_mul, Matrix.map_zero (incA D) (map_zero (incA D))]
  exact Matrix.zero_mul _

end GlobalTheory.LagMeans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyAdelicGLProjectionsFiniteNearOneStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_adelicGLProjections_finite_near_one : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (V V' : Set (GL (Fin a) (Af E))), V ∈ 𝓝 (1 : GL (Fin a) (Af E)) → V' ∈ 𝓝 (1 : GL (Fin a) (Af E)) → ∀ᶠ k in 𝓝 (1 : GL (Fin a) (Af E)), (∃ k' ∈ V, prS S a (finGL E a k) = finGL E a k') ∧ ∃ k'' ∈ V', prO S a (finGL E a k) = finGL E a k'' := by
  first | (exact @GlobalTheory.SchurExt.eventually_prS_prO_finGL) | (exact GlobalTheory.SchurExt.eventually_prS_prO_finGL) | (intros; apply GlobalTheory.SchurExt.eventually_prS_prO_finGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdelicExtensionOfAlgebraicWeightDefiniteUnStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_extension_of_algebraicWeight_definiteUnitary : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n), ∃ R : UA L n →* Module.End ℂ a.W, (∀ k ∈ finU L n, R k = 1) ∧ (∀ (γ : UA L n) (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ → (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → R γ = a.ρ γQ) ∧ ∀ (v : a.W) (μ : Module.Dual ℂ a.W), Continuous fun g : UA L n => μ (R g v) := by
  first | exact @GlobalTheory.WeightRealExt.exists_extension | exact GlobalTheory.WeightRealExt.exists_extension | (intros; apply GlobalTheory.WeightRealExt.exists_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCanonicalInertTensorCompletionEquiv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
noncomputable section

namespace GlobalTheory.InertTransferCanon

theorem exists_canonical_equiv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ Dv : InertDatum L n v w, (∀ x : L, Dv.σw (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → ∃ e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) ≃+* w.adicCompletion L, (∀ x, e (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L)) x) = Dv.σw (e x)) ∧ (∀ x, x ∈ Formalism.UG.tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L)) (Formalism.UG.intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v) ↔ e x ∈ Formalism.UG.intL (w.adicCompletion L)) ∧ ∀ z : AL L, e (compAt L v z) = F.κ z w := by
  intro L _ _ _ n F v w hov Dv hs
  obtain ⟨hu, hns, -⟩ := GlobalTheory.InertOfUnramInv.inert_of_isUnramInv L v w hov Dv.σw Dv.ϖ _ hs Dv.unram
  have hunder : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext hov
  have hw : Formalism.UG.IsInertAt (maximalRealSubfield L) L v w := by
    have h := GlobalTheory.InertPlaceConj.isInertAt_of_not_split w hu hns
    rwa [hunder] at h
  obtain ⟨c, hc, -⟩ := GlobalTheory.LFun.InertChart.existsUnique_isConjAt
    (IsCMField.complexConj L).toAlgHom hw hunder
  obtain ⟨ϖ', hU'⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv (GlobalTheory.InertDatumExist.isCMExt L) hw hc
  have hsc : Dv.σw = c := by
    apply DFunLike.coe_injective
    refine GlobalTheory.UnramCompletion.ringHom_ext_of_continuous w
      (GlobalTheory.InertDatumGiven.continuous_of_valued_eq _ Dv.unram.2.1)
      (GlobalTheory.InertDatumGiven.continuous_of_valued_eq c hU'.2.1) fun k => ?_
    rw [hs, GlobalTheory.LFun.InertChart.conj_algebraMap hc]
    rfl
  have hO : Formalism.UG.Ov L w = Formalism.UG.intL (w.adicCompletion L) := Subring.ext fun _ => Iff.rfl
  let e := (Algebra.TensorProduct.comm (maximalRealSubfield L) L
    (v.adicCompletion (maximalRealSubfield L))).toRingEquiv.trans (GlobalTheory.LFun.InertChart.complEquiv hw hunder)

  obtain ⟨i, hic, hi⟩ := F.right w v hov
  have hiy : ∀ y : maximalRealSubfield L,
      i (algebraMap _ (v.adicCompletion (maximalRealSubfield L)) y) =
        GlobalTheory.LFun.complMap hunder (algebraMap _ (v.adicCompletion (maximalRealSubfield L)) y) := by
    intro y
    rw [GlobalTheory.LFun.complMap_algebraMap]
    have h1 := hi (algebraMap (maximalRealSubfield L) _ y)
    have h2 : (1 : L) ⊗ₜ[maximalRealSubfield L]
        (algebraMap (maximalRealSubfield L) (FiniteAdeleRing (𝓞 (maximalRealSubfield L)) (maximalRealSubfield L)) y) =
        (algebraMap (maximalRealSubfield L) L y) ⊗ₜ 1 := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul']
    rw [h2, F.left] at h1
    exact h1.symm
  have hieq : (i : v.adicCompletion (maximalRealSubfield L) → w.adicCompletion L) = GlobalTheory.LFun.complMap hunder :=
    (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L) v).equalizer hic
      (GlobalTheory.LFun.InertChart.continuous_complMap hunder) (funext hiy)
  refine ⟨e, ?_, ?_, ?_⟩
  · intro x
    show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _
        (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom _ x)) =
      Dv.σw (GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ x))
    rw [hsc, hc]
    congr 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  · intro x
    rw [GlobalTheory.InertDatumExist.mem_tensInt_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw hunder, hO]
    exact Iff.rfl
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]; rfl
    | tmul x a =>
      have hk : F.κ (x ⊗ₜ a) = F.κ (x ⊗ₜ 1) * F.κ (1 ⊗ₜ a) := by
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ (compAt L v (x ⊗ₜ a))) = _
      have hm : ∀ p q : FiniteAdeleRing (𝓞 L) L, (p * q) w = p w * q w := fun _ _ => rfl
      rw [hk, F.left, hm, hi, hieq]
      show GlobalTheory.LFun.complMap hunder (a v) * algebraMap L _ x = _
      rw [mul_comm]
      rfl

end GlobalTheory.InertTransferCanon

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChangeStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_rep_base_change : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm2 D → ∀ (i : D.nd.Loc) (P : D.naut.AV i) (Pa : List (Formalism.BasicNotions.Part D.naut.CG)), IsBCV D.nd D.naut i P Pa → ∃ ρ : GE D.nd →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), (SumRepresentations.At.ContQ D.nd i ρ ∧ IsSSRep ρ ∧ (∀ w, D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ ∀ τ, InducesW D.nd i τ w → (D.naut.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) = (D.naut.infWt i ((D.naut.iotaQC i).toRingHom.comp τ)).map (fun z => -z + ((D.R.nV : ℂ) - 1) / 2)) := by
  first | exact @GlobalTheory.GalIsoBC.galRep_isobaric | exact GlobalTheory.GalIsoBC.galRep_isobaric | (intros; apply GlobalTheory.GalIsoBC.galRep_isobaric <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodFrameRealisationStatement
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
theorem _root_.GlobalTheory.T.exists_good_frame_realisation : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (F3 : Face3 D A3), Rl.Char3 F3 → ∀ j : Fin D.R.m, ∃ F : Frame (Vc D j) (Wc D j), F.Good ∧ IsStdChar D F.ψ (-1) ∧ F.ψ = Rl.ψ ∧ F.θ = Rl.θ ∧ F.sT = cart (Rl.MW j (sg0 D A3.A)) ∧ (∀ τ, (F.BS τ).val = Rl.BV j τ) ∧ F.BT = onb (Rl.MW j (sg0 D A3.A)) ∧ F.ΛS = Rl.ΛV j ∧ F.ΛT = Rl.ΛW j ∧ F.βS = Rl.βV j ∧ F.βT = Rl.βW j ∧ F.f₀ = Rl.vacP j ∧ Lev.IsBaseFrame (Vc D j) F.βS F.ΛS 1 ∧ Lev.IsBaseFrame (Wc D j) F.βT F.ΛT 1 := by
  first | exact @GlobalTheory.FrameOfReal.exists_frame_real | exact GlobalTheory.FrameOfReal.exists_frame_real | (intros; apply GlobalTheory.FrameOfReal.exists_frame_real <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLadicCoefficientFieldEmbeddingsComplexStatement
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
theorem _root_.GlobalTheory.T.exists_ladicCoefficientField_embeddings_complex : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (f0 : ∀ i, Bool → (FractionRing (X.O0 i) →+* ℂ)), (∀ i b x, f0 i b ((if b then X.emb0 i else X.emb0b i) x) = embLL0 D x) → (∀ i k, Cardinal.mk (FractionRing (X.Ok i k)) ≤ Cardinal.continuum) → ∃ (e : ∀ i, Bool → (FractionRing (X.O i) →+* ℂ)) (ek : ∀ i, Bool → ∀ k, FractionRing (X.Ok i k) →+* ℂ), (∀ i b x, e i b (sideEmb X i b x) = embLL0 D x) ∧ (∀ i b k (x : X.O i), ek i b k (algebraMap (X.Ok i k) (FractionRing (X.Ok i k)) (algebraMap (X.O i) (X.Ok i k) x)) = e i b (algebraMap (X.O i) (FractionRing (X.O i)) x)) ∧ (∀ i b (y : X.O0 i), IsIntegral ℤ y → e i b (algebraMap (X.O i) (FractionRing (X.O i)) (algebraMap (X.O0 i) (X.O i) y)) = f0 i b (algebraMap (X.O0 i) (FractionRing (X.O0 i)) y)) := by
  first | exact @GlobalTheory.EmbExt.exists_side_embeddings | exact GlobalTheory.EmbExt.exists_side_embeddings | (intros; apply GlobalTheory.EmbExt.exists_side_embeddings <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNhdsOneConjLowerUnipotentSchurBlocksSmall
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt Filter
open scoped ContDiff Topology

namespace GlobalTheory.SchurNear

variable {E : Type} [Field E] [NumberField E] {α : Type}

theorem continuous_pLoc (w : HeightOneSpectrum (𝓞 E)) : Continuous (pLoc E w) :=
  RestrictedProduct.continuous_eval w

theorem exists_inv (x : Af E) (h0 : ∀ w, pLoc E w x ≠ 0)
    (h1 : ∀ w : HeightOneSpectrum (𝓞 E), (pLoc E w x)⁻¹ ∈ w.adicCompletionIntegers E) :
    ∃ y ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E, x * y = 1 := by
  refine ⟨⟨fun w => (pLoc E w x)⁻¹, Eventually.of_forall h1⟩, h1, ?_⟩
  refine Subtype.ext (funext fun w => ?_)
  exact mul_inv_cancel₀ (h0 w)

theorem eventually_inv (S : Finset (HeightOneSpectrum (𝓞 E))) {l : Filter α} {f : α → Af E}
    (hf : Tendsto f l (𝓝 1)) (hS : ∀ᶠ a in l, ∀ w ∉ S, pLoc E w (f a) = 1) :
    ∀ᶠ a in l, ∃ y ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E, f a * y = 1 := by
  have h : ∀ w ∈ S, ∀ᶠ a in l, pLoc E w (f a) ≠ 0 ∧ (pLoc E w (f a))⁻¹ ∈ w.adicCompletionIntegers E := by
    intro w _
    have h1 : Tendsto (fun a => pLoc E w (f a)) l (𝓝 1) := by
      have := ((continuous_pLoc w).tendsto 1).comp hf
      rwa [map_one] at this
    have h2 : Tendsto (fun a => (pLoc E w (f a))⁻¹) l (𝓝 1) := by
      have := h1.inv₀ one_ne_zero
      rwa [inv_one] at this
    refine (h1.eventually_ne one_ne_zero).and ?_
    exact h2.eventually ((Valued.isOpen_valuationSubring _).mem_nhds (one_mem (w.adicCompletionIntegers E)))
  filter_upwards [(eventually_all_finset S).2 h, hS] with a ha hb
  refine exists_inv _ (fun w => ?_) (fun w => ?_)
  · by_cases hw : w ∈ S
    · exact (ha w hw).1
    · rw [hb w hw]; exact one_ne_zero
  · by_cases hw : w ∈ S
    · exact (ha w hw).2
    · rw [hb w hw, inv_one]; exact one_mem _

theorem tendsto_inverse (S : Finset (HeightOneSpectrum (𝓞 E))) {l : Filter α} {f : α → Af E}
    (hf : Tendsto f l (𝓝 1)) (hS : ∀ᶠ a in l, ∀ w ∉ S, pLoc E w (f a) = 1) :
    Tendsto (fun a => Ring.inverse (f a)) l (𝓝 1) := by
  intro W hW
  have hO := GroundTheory.Global.isCompact_integralFiniteAdeles E
  have hN : ∀ᶠ c in 𝓝 (1 : Af E), ∀ y ∈ (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)),
      1 + (1 - c) * y ∈ W := by
    refine hO.eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Continuous fun z : Af E × Af E => 1 + (1 - z.1) * z.2 := by fun_prop
    have h := hc.tendsto ((1 : Af E), y)
    simp only [sub_self, zero_mul, add_zero] at h
    exact h hW
  change ∀ᶠ a in l, Ring.inverse (f a) ∈ W
  filter_upwards [hf.eventually hN, eventually_inv S hf hS] with a ha ⟨y, hy, hxy⟩
  have hu : IsUnit (f a) := IsUnit.of_mul_eq_one y hxy
  have : Ring.inverse (f a) = 1 + (1 - f a) * y := by
    have h1 := Ring.inverse_mul_cancel _ hu
    linear_combination (1 - Ring.inverse (f a)) * hxy + y * h1
  rw [this]; exact ha y hy

theorem matrix_near (S : Finset (HeightOneSpectrum (𝓞 E))) {n : ℕ} {l : Filter α}
    {g : α → Matrix (Fin n) (Fin n) (Af E)}
    (hg : Tendsto g l (𝓝 1)) (hS : ∀ᶠ a in l, ∀ w ∉ S, (g a).map (pLoc E w) = 1) :
    (∀ᶠ a in l, IsUnit (g a).det) ∧ Tendsto (fun a => (g a)⁻¹) l (𝓝 1) ∧
      Tendsto (fun a => mkGL (g a)) l (𝓝 1) := by
  have hd : Tendsto (fun a => (g a).det) l (𝓝 1) := by
    have := ((continuous_id.matrix_det (X := Matrix (Fin n) (Fin n) (Af E))).tendsto 1).comp hg
    simpa [Function.comp_def] using this
  have hdS : ∀ᶠ a in l, ∀ w ∉ S, pLoc E w (g a).det = 1 := by
    filter_upwards [hS] with a ha w hw
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ha w hw, Matrix.det_one]
  have hu : ∀ᶠ a in l, IsUnit (g a).det := by
    filter_upwards [eventually_inv S hd hdS] with a ⟨y, _, hy⟩
    exact IsUnit.of_mul_eq_one y hy
  have hadj : Tendsto (fun a => (g a).adjugate) l (𝓝 1) := by
    have := ((continuous_id.matrix_adjugate (X := Matrix (Fin n) (Fin n) (Af E))).tendsto 1).comp hg
    simpa [Function.comp_def] using this
  have hi : Tendsto (fun a => (g a)⁻¹) l (𝓝 1) := by
    have := (tendsto_inverse S hd hdS).smul hadj
    simpa only [one_smul, Matrix.inv_def] using this
  refine ⟨hu, hi, ?_⟩
  rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
  have h2 := (MulOpposite.continuous_op.tendsto _).comp hi
  have h3 := hg.prodMk_nhds h2
  refine Tendsto.congr' ?_ h3
  filter_upwards [hu] with a ha
  simp only [Function.comp, Units.embedProduct_apply, Matrix.coe_units_inv, coe_mkGL ha]

section Alg
variable {R T : Type} [CommRing R] [CommRing T] {m r : ℕ}

theorem blk_one : blk (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = Matrix.fromBlocks 1 0 0 1 := by
  rw [blk, Matrix.submatrix_one_equiv, Matrix.fromBlocks_one]

theorem Aof_one : Aof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  rw [Aof, blk_one, Matrix.toBlocks_fromBlocks₁₁]
theorem Bof_one : Bof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Bof, blk_one, Matrix.toBlocks_fromBlocks₁₂]
theorem Cof_one : Cof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Cof, blk_one, Matrix.toBlocks_fromBlocks₂₁]
theorem Dof_one : Dof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  rw [Dof, blk_one, Matrix.toBlocks_fromBlocks₂₂]

theorem conj_one (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) : conjLowUni Y 1 = 1 := by
  rw [conjLowUni, mul_one, lowUni, lowUni, unblk, unblk, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem lowUni_map (p : R →+* T) (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) :
    (lowUni Y).map p = lowUni (Y.map p) := by
  rw [lowUni, lowUni, unblk, unblk, ← Matrix.submatrix_map, Matrix.fromBlocks_map]
  simp

theorem conj_map (p : R →+* T) (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R)
    (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (hk : k.map p = 1) :
    (conjLowUni Y k).map p = 1 := by
  rw [← conj_one (Y.map p), conjLowUni, conjLowUni, Matrix.map_mul, Matrix.map_mul, lowUni_map, lowUni_map, hk,
    Matrix.map_neg _ (map_neg p)]

theorem Dof_map (p : R →+* T) (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : M.map p = 1) :
    (Dof M).map p = 1 := by
  rw [← Dof_one (m := m), ← h]; rfl

theorem Scof_map (p : R →+* T) (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : M.map p = 1) :
    (Scof M).map p = 1 := by
  have hA : (Aof M).map p = 1 := by rw [← Aof_one (r := r), ← h]; rfl
  have hB : (Bof M).map p = 0 := by rw [← Bof_one (m := m) (r := r), ← h]; rfl
  rw [Scof, Matrix.map_sub _ (map_sub p), Matrix.map_mul, Matrix.map_mul, hA, hB]
  simp

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_lowUni : Continuous (lowUni : Matrix (Fin (r + 1)) (Fin (m + 1)) R → _) :=
  (Continuous.matrix_fromBlocks continuous_const continuous_const continuous_id continuous_const).matrix_submatrix _ _

theorem continuous_conj {Z : Type} [TopologicalSpace Z] {f : Z → Matrix (Fin (r + 1)) (Fin (m + 1)) R}
    {g : Z → Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun z => conjLowUni (f z) (g z)) := by
  have h1 : Continuous fun z => lowUni (f z) := continuous_lowUni.comp hf
  have h2 : Continuous fun z => lowUni (-f z) := continuous_lowUni.comp hf.neg
  exact (h1.matrix_mul hg).matrix_mul h2

theorem tendsto_mul {a b c : ℕ} {l : Filter α} {f : α → Matrix (Fin a) (Fin b) R} {g : α → Matrix (Fin b) (Fin c) R}
    {x : Matrix (Fin a) (Fin b) R} {y : Matrix (Fin b) (Fin c) R} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun t => f t * g t) l (𝓝 (x * y)) := by
  have hc : Continuous fun z : Matrix (Fin a) (Fin b) R × Matrix (Fin b) (Fin c) R => z.1 * z.2 :=
    Continuous.matrix_mul (A := fun z : Matrix (Fin a) (Fin b) R × Matrix (Fin b) (Fin c) R => z.1)
      (B := fun z => z.2) continuous_fst continuous_snd
  have h := (hc.tendsto (x, y)).comp (hf.prodMk_nhds hg)
  simpa only [Function.comp_def] using h

end Alg

theorem blocks_near (S : Finset (HeightOneSpectrum (𝓞 E))) {m r : ℕ} {l : Filter α}
    {g : α → Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)}
    (hg : Tendsto g l (𝓝 1)) (hS : ∀ᶠ a in l, ∀ w ∉ S, (g a).map (pLoc E w) = 1) :
    (∀ᶠ a in l, IsUnit (Dof (g a)).det) ∧ Tendsto (fun a => mkGL (Dof (g a))) l (𝓝 1) ∧
      Tendsto (fun a => mkGL (Scof (g a))) l (𝓝 1) ∧ Tendsto (fun a => Yof (g a)) l (𝓝 0) ∧
      Tendsto (fun a => Xof (g a)) l (𝓝 0) := by
  have hA : Tendsto (fun a => Aof (g a)) l (𝓝 1) := by
    rw [← Aof_one (r := r)]
    exact (Continuous.tendsto (f := Aof) (continuous_matrix fun i j => continuous_id.matrix_elem _ _) _).comp hg
  have hB : Tendsto (fun a => Bof (g a)) l (𝓝 0) := by
    rw [← Bof_one]
    exact (Continuous.tendsto (f := Bof) (continuous_matrix fun i j => continuous_id.matrix_elem _ _) _).comp hg
  have hC : Tendsto (fun a => Cof (g a)) l (𝓝 0) := by
    rw [← Cof_one]
    exact (Continuous.tendsto (f := Cof) (continuous_matrix fun i j => continuous_id.matrix_elem _ _) _).comp hg
  have hD : Tendsto (fun a => Dof (g a)) l (𝓝 1) := by
    rw [← Dof_one (m := m)]
    exact (Continuous.tendsto (f := Dof) (continuous_matrix fun i j => continuous_id.matrix_elem _ _) _).comp hg
  obtain ⟨hu, hi, hm⟩ := matrix_near S hD (hS.mono fun a ha w hw => Dof_map _ _ (ha w hw))
  have hSc : Tendsto (fun a => Scof (g a)) l (𝓝 1) := by
    have := hA.sub (tendsto_mul (tendsto_mul hB hi) hC)
    simpa only [Scof, Matrix.mul_zero, sub_zero] using this
  refine ⟨hu, hm, (matrix_near S hSc (hS.mono fun a ha w hw => Scof_map _ _ (ha w hw))).2.2, ?_, ?_⟩
  · simpa only [Yof, Matrix.mul_zero] using tendsto_mul hi hC
  · simpa only [Xof, Matrix.zero_mul] using tendsto_mul hB hi

theorem conj_near (S : Finset (HeightOneSpectrum (𝓞 E))) {m r : ℕ} {Z : Type} [TopologicalSpace Z]
    (π : Z → Matrix (Fin (r + 1)) (Fin (m + 1)) (Af E)) (hπ : Continuous π) (z₀ : Z) :
    let l : Filter (GL (Fin (m + r + 1 + 1)) (Af E) × Z) :=
      𝓝 (1, z₀) ⊓ 𝓟 {z | ∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) z.1 = 1}
    Tendsto (fun z : GL (Fin (m + r + 1 + 1)) (Af E) × Z => conjLowUni (π z.2) z.1.val) l (𝓝 1) ∧
      ∀ᶠ z in l, ∀ w ∉ S, (conjLowUni (π z.2) z.1.val).map (pLoc E w) = 1 := by
  intro l
  constructor
  · have hc : Continuous fun z : GL (Fin (m + r + 1 + 1)) (Af E) × Z => conjLowUni (π z.2) z.1.val :=
      continuous_conj (f := fun z : GL (Fin (m + r + 1 + 1)) (Af E) × Z => π z.2) (g := fun z => z.1.val)
        (hπ.comp continuous_snd) (Units.continuous_val.comp continuous_fst)
    have := hc.tendsto (1, z₀)
    simp only [Units.val_one, conj_one] at this
    exact this.mono_left inf_le_left
  · refine eventually_inf_principal.2 (Eventually.of_forall fun z hz w hw => conj_map _ _ _ ?_)
    exact congrArg Units.val (hz w hw)

theorem blocks_small : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (Uβ : Subgroup (GL (Fin (m + 1)) (Af E))) (Ub : Subgroup (GL (Fin (r + 1)) (Af E))), IsOpen (Uβ : Set (GL (Fin (m + 1)) (Af E))) → IsOpen (Ub : Set (GL (Fin (r + 1)) (Af E))) → ∀ (Krow : Set (Fin (m + 1) → Af E)) (Kcol : Set (Fin (r + 1) → Af E)), IsCompact Krow → IsCompact Kcol → ∃ W ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ k ∈ W, (∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) k = 1) → ∀ Y : Matrix (Fin (r + 1)) (Fin (m + 1)) (Af E), (∀ i j, Y i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) → IsUnit (Dof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))).det ∧ mkGL (Dof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))) ∈ Ub ∧ mkGL (Scof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))) ∈ Uβ ∧ (∀ i j, Yof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) ∧ ∀ ρ ∈ Krow, ∀ γ ∈ Kcol, (∑ j, ∑ l, ρ j * Xof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) j l * γ l) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
  intro E _ _ m r S Uβ Ub hβ hb Krow Kcol hrow hcol
  have hO := GroundTheory.Global.isCompact_integralFiniteAdeles E
  have hOo : (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)) ∈ 𝓝 (0 : Af E) :=
    GroundTheory.Global.isOpen_integralFiniteAdeles.mem_nhds (zero_mem _)
  set KY : Set (Matrix (Fin (r + 1)) (Fin (m + 1)) (Af E)) :=
    {Y | ∀ i j, Y i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E} with hKY
  have hK : IsCompact KY := by
    have := isCompact_pi_infinite (X := fun _ : Fin (r + 1) => Fin (m + 1) → Af E)
      (fun _ => isCompact_pi_infinite (fun _ : Fin (m + 1) => hO))
    exact this
  have h1 : ∀ᶠ k in 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ Y ∈ KY,
      (∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) k = 1) →
      IsUnit (Dof (conjLowUni Y k.val)).det ∧ mkGL (Dof (conjLowUni Y k.val)) ∈ Ub ∧
        mkGL (Scof (conjLowUni Y k.val)) ∈ Uβ ∧
        ∀ i j, Yof (conjLowUni Y k.val) i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
    refine hK.eventually_forall_of_forall_eventually fun Y _ => ?_
    obtain ⟨a, b⟩ := conj_near S id continuous_id Y
    obtain ⟨c1, c2, c3, c4, -⟩ := blocks_near S a b
    refine eventually_inf_principal.1 (c1.and ((c2.eventually (hb.mem_nhds Ub.one_mem)).and
      ((c3.eventually (hβ.mem_nhds Uβ.one_mem)).and ?_)))
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    exact (((continuous_id.matrix_elem i j).tendsto 0).comp c4).eventually hOo
  have h2 : ∀ᶠ k in 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ z ∈ KY ×ˢ (Krow ×ˢ Kcol),
      (∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) k = 1) →
      (∑ j, ∑ l, z.2.1 j * Xof (conjLowUni z.1 k.val) j l * z.2.2 l) ∈
        GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
    refine (hK.prod (hrow.prod hcol)).eventually_forall_of_forall_eventually fun z₀ _ => ?_
    obtain ⟨a, b⟩ := conj_near S Prod.fst continuous_fst z₀
    obtain ⟨-, -, -, -, c⟩ := blocks_near S a b
    refine eventually_inf_principal.1 (Tendsto.eventually (p := fun x => x ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) ?_ hOo)
    have hc : Continuous fun t : Matrix (Fin (m + 1)) (Fin (r + 1)) (Af E) × (Fin (m + 1) → Af E) × (Fin (r + 1) → Af E) =>
        ∑ j, ∑ l, t.2.1 j * t.1 j l * t.2.2 l := by fun_prop
    have h3 := (hc.tendsto (0, z₀.2)).comp (c.prodMk_nhds
      (((continuous_snd.comp continuous_snd).tendsto (1, z₀)).mono_left inf_le_left))
    simp only [Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero] at h3
    exact h3
  refine ⟨_, h1.and h2, fun k hk hS Y hY => ?_⟩
  obtain ⟨a, b, c, d⟩ := hk.1 Y hY hS
  exact ⟨a, b, c, d, fun ρ hρ γ hγ => hk.2 (Y, ρ, γ) ⟨hY, hρ, hγ⟩ hS⟩

end GlobalTheory.SchurNear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterOfUnramifiedInertDefiniteUnStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_satakeParameter_of_unramified_inert_definiteUnitary : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (w : HeightOneSpectrum (𝓞 L)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal → ¬ IsSplitAt w → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → IsUnramU U w → ∃ α0 : Fin (n / 2) → ℂˣ, HasSatAt U w s ϖ q α0 := by
  first | exact @GlobalTheory.InertSatakeGiven.exists_hasSatAt | exact GlobalTheory.InertSatakeGiven.exists_hasSatAt | (intros; apply GlobalTheory.InertSatakeGiven.exists_hasSatAt <;> assumption)
end

