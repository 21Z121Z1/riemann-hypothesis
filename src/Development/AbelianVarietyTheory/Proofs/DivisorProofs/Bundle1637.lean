import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1593
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfInvertibleLinearChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1608
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1609
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0096
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackGluedQuotientKernelPairOfCover
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.GlueQuotPB

theorem isIso_of_isPullback_openCover {X Y : Scheme.{0}} (f : X ⟶ Y) (𝒱 : Y.OpenCover)
    {Z : 𝒱.I₀ → Scheme.{0}} (k : ∀ i, Z i ⟶ X) (g : ∀ i, Z i ⟶ 𝒱.X i)
    (h : ∀ i, IsPullback (k i) (g i) f (𝒱.f i)) (hg : ∀ i, IsIso (g i)) : IsIso f := by
  have key := (IsZariskiLocalAtTarget.iff_of_openCover (P := MorphismProperty.isomorphisms Scheme.{0})
    (f := f) 𝒱).2
  refine key fun i => ?_
  have e : ((h i).isoIsPullback _ _ (IsPullback.of_hasPullback f (𝒱.f i))).hom ≫
      pullback.snd f (𝒱.f i) = g i := by simp
  change IsIso (pullback.snd f (𝒱.f i))
  have hgi := hg i
  have e2 : pullback.snd f (𝒱.f i) =
      ((h i).isoIsPullback _ _ (IsPullback.of_hasPullback f (𝒱.f i))).inv ≫ g i := by
    exact (Iso.eq_inv_comp _).2 e
  rw [e2]
  infer_instance

theorem isIso_of_pullback_openCover {S : Scheme.{0}} (𝒰 : S.OpenCover) {X Y : Over S} (c : X ⟶ Y)
    (hc : ∀ j, IsIso ((Over.pullback (𝒰.f j)).map c)) : IsIso c := by
  suffices hl : IsIso c.left by
    have : IsIso ((Over.forget S).map c) := hl
    exact isIso_of_reflects_iso c (Over.forget S)
  refine isIso_of_isPullback_openCover c.left (𝒰.pullback₁ Y.hom)
    (fun j => pullback.fst X.hom (𝒰.f j)) (fun j => ((Over.pullback (𝒰.f j)).map c).left) (fun j => ?_)
    (fun j => by
      have := hc j
      exact (inferInstance : IsIso ((Over.forget _).map ((Over.pullback (𝒰.f j)).map c))))
  refine IsPullback.of_bot (v₂₁ := pullback.snd Y.hom (𝒰.f j)) (v₂₂ := Y.hom) (h₃₁ := 𝒰.f j) ?_ ?_
    (IsPullback.of_hasPullback Y.hom (𝒰.f j))
  · convert IsPullback.of_hasPullback X.hom (𝒰.f j) using 1
    · simp only [Over.pullback_map_left]
      erw [pullback.lift_snd]
    · exact Over.w c
  · change _ = _ ≫ pullback.fst Y.hom (𝒰.f j)
    simp only [Over.pullback_map_left]
    erw [pullback.lift_fst]

theorem hom_ext_of_pullback_openCover {S : Scheme.{0}} (𝒰 : S.OpenCover) {X Y : Over S} (f g : X ⟶ Y)
    (h : ∀ j, (Over.pullback (𝒰.f j)).map f = (Over.pullback (𝒰.f j)).map g) : f = g := by
  ext1
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ X.hom) _ _ fun j => ?_
  have e := congrArg (fun u => u.left ≫ pullback.fst Y.hom (𝒰.f j)) (h j)
  change pullback.fst X.hom (𝒰.f j) ≫ f.left = pullback.fst X.hom (𝒰.f j) ≫ g.left
  simp only [Over.pullback_map_left] at e
  erw [pullback.lift_fst, pullback.lift_fst] at e
  exact e

theorem baseChange_translation {T T' : Scheme.{0}} (t : T' ⟶ T) (A H : Over T) [GrpObj A] [GrpObj H] (i : H ⟶ A) :
    ∃ e : (Over.pullback t).obj (H ⊗ A) ≅ (Over.pullback t).obj H ⊗ (Over.pullback t).obj A,
      e.hom ≫ ((fst ((Over.pullback t).obj H) ((Over.pullback t).obj A) ≫ (Over.pullback t).map i) *
          snd ((Over.pullback t).obj H) ((Over.pullback t).obj A)) =
        (Over.pullback t).map ((fst H A ≫ i) * snd H A) ∧
      e.hom ≫ snd ((Over.pullback t).obj H) ((Over.pullback t).obj A) = (Over.pullback t).map (snd H A) := by
  refine ⟨(Functor.Monoidal.μIso (Over.pullback t) H A).symm, ?_, ?_⟩
  · rw [Iso.symm_hom, Functor.Monoidal.μIso_inv, MonObj.comp_mul, Functor.map_mul, Functor.map_comp,
      Functor.OplaxMonoidal.δ_fst_assoc, Functor.OplaxMonoidal.δ_snd]
  · rw [Iso.symm_hom, Functor.Monoidal.μIso_inv, Functor.OplaxMonoidal.δ_snd]

theorem isPullback_translation_of_cover : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H G : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A) (Q : A ⟶ G)
    (B : ∀ j, Over (𝒰.X j)) (ψ : ∀ j, (B j).left ⟶ G.left) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j),
    (∀ j, IsPullback (ψ j) (B j).hom G.hom (𝒰.f j)) → (∀ j, (q j).left ≫ ψ j = pullback.fst A.hom (𝒰.f j) ≫ Q.left) → (∀ j, IsPullback ((fst ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A) ≫ (Over.pullback (𝒰.f j)).map i) * snd ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A)) (snd ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A)) (q j) (q j)) → IsPullback ((fst H A ≫ i) * snd H A) (snd H A) Q Q := by
  intro S 𝒰 A H G _ _ i Q B ψ q hψ hq hloc

  let φ : ∀ j, B j ≅ (Over.pullback (𝒰.f j)).obj G := fun j =>
    Over.isoMk (hψ j).isoPullback (by simp)
  have hQ : ∀ j, (Over.pullback (𝒰.f j)).map Q = q j ≫ (φ j).hom := by
    intro j
    ext1
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left, Over.comp_left, Category.assoc]
      erw [pullback.lift_fst]
      simp [φ, hq j]
    · simp only [Over.pullback_map_left, Over.comp_left, Category.assoc]
      erw [pullback.lift_snd]
      simp [φ]
  choose e he₁ he₂ using fun j => baseChange_translation (𝒰.f j) A H i
  have w : ((fst H A ≫ i) * snd H A) ≫ Q = snd H A ≫ Q := by
    refine hom_ext_of_pullback_openCover 𝒰 _ _ fun j => ?_
    rw [Functor.map_comp, Functor.map_comp, ← he₁ j, ← he₂ j, hQ j, Category.assoc, Category.assoc,
      (hloc j).w_assoc]
  have hF : ∀ j, IsPullback ((Over.pullback (𝒰.f j)).map ((fst H A ≫ i) * snd H A))
      ((Over.pullback (𝒰.f j)).map (snd H A)) ((Over.pullback (𝒰.f j)).map Q)
      ((Over.pullback (𝒰.f j)).map Q) := by
    intro j
    refine IsPullback.of_iso (hloc j) (e j).symm (Iso.refl _) (Iso.refl _) (φ j) ?_ ?_ ?_ ?_
    · simp [← he₁ j]
    · simp [← he₂ j]
    · simp [hQ j]
    · simp [hQ j]
  let c : H ⊗ A ⟶ pullback Q Q := pullback.lift _ _ w
  have hc : IsIso c := by
    refine isIso_of_pullback_openCover 𝒰 c fun j => ?_
    have hP := (IsPullback.of_hasPullback Q Q).map (Over.pullback (𝒰.f j))
    have : (Over.pullback (𝒰.f j)).map c = ((hF j).isoIsPullback _ _ hP).hom := by
      apply hP.hom_ext
      · rw [IsPullback.isoIsPullback_hom_fst, ← Functor.map_comp]
        exact congrArg (Over.pullback (𝒰.f j)).map (pullback.lift_fst _ _ w)
      · rw [IsPullback.isoIsPullback_hom_snd, ← Functor.map_comp]
        exact congrArg (Over.pullback (𝒰.f j)).map (pullback.lift_snd _ _ w)
    rw [this]
    infer_instance
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso c) (pullback.lift_fst _ _ w)
    (pullback.lift_snd _ _ w)

end GlobalTheory.GlueQuotPB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunOfSmoothRealHeisenbergLevel
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section

namespace GlobalTheory.ThetaOfSmF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_theta_infPartF {τ : E →+* ℂ} {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmbF τ θ) :
    Continuous fun z : AEF F E => θ (infPartF F E z) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := isModuleTopology_AE F E
  let b := Module.finBasis F E
  let bb := Algebra.TensorProduct.basis (AF F) b
  have hz : ∀ z : AEF F E, θ (infPartF F E z) = ∑ i, θ (fstA F (bb.repr z i) ⊗ₜ[F] (1 : E)) * τ (b i) := by
    intro z
    conv_lhs => rw [← bb.sum_repr z]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    show θ (fstA F (bb.repr z i) ⊗ₜ[F] b i) = _
    rw [← hθ.1 (b i), ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hc : ∀ i, Continuous fun z : AEF F E => bb.repr z i := fun i =>
    IsModuleTopology.continuous_of_linearMap (bb.coord i)
  refine (continuous_finset_sum _ fun i _ => ?_).congr fun z => (hz z).symm
  exact (hθ.2.comp (continuous_fst.comp (hc i))).mul continuous_const

end GlobalTheory.ThetaOfSmF

open GlobalTheory.ThetaOfSmF in

theorem GlobalTheory.ThetaOfSmF.theta_of_smF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (hψ : IsCharAF F B.ψ) (f : BBF σ JS JT ξ₀ B.ψ), Sm (rhoVF σ JS JT ξ₀ B.ψ hψ ι) f →
        (∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
          ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u f.1 = f.1) →
        IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ θ hθ ι hι hψ f hF hl
  refine ⟨f.2, hl, f.1.continuous, fun k L hL hL0 w => ?_⟩
  obtain ⟨lam, hlc, hlam⟩ := GlobalTheory.HeisLineDiffF.exists_log (GlobalTheory.T.standardTraceAddChar_isStandardChar_of_admissibleCMBase F E σ B hB)

  let P : (Fin k → ℝ) →+ (IxF F nS nT → ℂ) :=
    { toFun := fun t => piWF θ (L t)
      map_zero' := by
        funext p
        simp only [piWF, map_zero, Matrix.zero_apply, Pi.zero_apply]
      map_add' := fun s t => by
        funext p
        simp only [piWF, map_add, Matrix.add_apply, Pi.add_apply] }
  have hP : Continuous P := continuous_pi fun p =>
    (continuous_theta_infPartF (hθ p.2)).comp ((continuous_apply p.1.2).comp ((continuous_apply p.1.1).comp hL))
  have hLP : ∀ t, L t = iotaVF ι (P t) := by
    intro t
    ext i j
    refine sub_eq_zero.1 (hι.ext _ ?_ fun w' => ?_)
    · have h0 : finPartF F E (L t i j) = 0 := congrFun (congrFun (hL0 t) i) j
      rw [map_sub, h0]
      simp only [iotaVF, Matrix.of_apply, hι.fin, sub_zero]
    · rw [map_sub, map_sub]
      simp only [iotaVF, Matrix.of_apply, hι.comp]
      show θ w' (infPartF F E (L t i j)) - θ w' (infPartF F E (L t i j)) = 0
      exact sub_self _

  let φ : (Fin k → ℝ) →+ ℂ :=
    { toFun := fun t => -lam (symplOHF σ JS JT ξ₀ w (L t))
      map_zero' := by rw [map_zero L, GlobalTheory.HeisLineDiffF.symplOHF_zero_right, map_zero, neg_zero]
      map_add' := fun s t => by rw [map_add L, GlobalTheory.HeisLineDiffF.symplOHF_add_right, map_add, neg_add] }
  have hφ : Continuous φ := (hlc.comp (GlobalTheory.HeisLineDiffF.continuous_symplOHF σ JS JT ξ₀ w hL)).neg
  have e : (fun t => f.1 (w + L t)) =
      fun t => Complex.exp (φ.toRealLinearMap hφ t) * ev _ _ w (rhoVF σ JS JT ξ₀ B.ψ hψ ι (P.toRealLinearMap hP t) f) := by
    funext t
    have h1 : (rhoVF σ JS JT ξ₀ B.ψ hψ ι (P t) f).1 w = heisOF σ JS JT ξ₀ B.ψ (L t) f.1 w := by
      show (rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι (P t)) f).1 w = _
      rw [coe_rhoBF, ← hLP t]
    have h2 : B.ψ (-(symplOHF σ JS JT ξ₀ w (L t))) = Complex.exp (φ t) := by
      rw [hlam _ (by rw [map_neg, GlobalTheory.HeisLineDiffF.sndA_symplOHF σ JS JT ξ₀ w _ (hL0 t), neg_zero]), map_neg]
      rfl
    show f.1 (w + L t) = Complex.exp (φ t) * ev _ _ w (rhoVF σ JS JT ξ₀ B.ψ hψ ι (P t) f)
    rw [ev_apply, h1, ← h2, heisOF, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one,
      one_mul]
  rw [e]
  exact (φ.toRealLinearMap hφ).contDiff.cexp.mul
    (((ev _ _ w).restrictScalars ℝ).contDiff.comp (hF.comp (P.toRealLinearMap hP).contDiff))

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfInvertibleLinearChangeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isVeryAmpleBySections_of_invertible_linear_change : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (H : LB X) (n : ℕ) (s : Fin (n + 1) → H.Sec) (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R), IsUnit a.det → H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy f H s → GlobalTheory.AbLaw.VeryAmpleBy f H (fun i => ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • s j) := by
  first | exact @GlobalTheory.veryAmpleBy_linChange | exact GlobalTheory.veryAmpleBy_linChange | (intros; apply GlobalTheory.veryAmpleBy_linChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedFDerivApplyEqFoldrDirectionalFderivStatement
section
open IsDedekindDomain NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedFDeriv_apply_eq_foldr_directional_fderiv : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (g : E → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g →
    ∀ (j : ℕ) (m : Fin j → E) (x : E),
      iteratedFDeriv ℝ j g x m = (List.ofFn m).foldr (fun v g' => fun z => fderiv ℝ g' z v) g x := by
  first | exact @GlobalTheory.iteratedFDeriv_apply_eq_foldr_fderiv | exact GlobalTheory.iteratedFDeriv_apply_eq_foldr_fderiv | (intros; apply GlobalTheory.iteratedFDeriv_apply_eq_foldr_fderiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerFormApplyStatement
section
open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_homO_eq_augmentationQuotient_of_scalar_character : ∀ {k O C W V : Type*} [Field k] [Ring O] [CommRing C] [Algebra C O] [AddCommGroup W] [Module k W] [FiniteDimensional k W] [AddCommGroup V] [Module k V] [FiniteDimensional k V] (σW : O →+* Module.End k W) (τ : O →+* Module.End k V) (χ : C →+* k), (∀ c, τ (algebraMap C O c) = χ c • 1) → finrank k (homO σW τ) = finrank k (homO (qAct σW (mSub σW χ ⊤) (mSub_stable σW χ ⊤ (fun _ _ _ => trivial))) τ) := by
  first | exact @GlobalTheory.HTRho.finrank_homO_eq_quot_mSub | exact GlobalTheory.HTRho.finrank_homO_eq_quot_mSub | (intros; apply GlobalTheory.HTRho.finrank_homO_eq_quot_mSub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.LagrTheta

def lagrInt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m nS nT : ℕ}
    (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)) (C : Matrix (Fin m) (Fin nT) (AF F ⊗[F] E))
    (f : Matrix (Fin m) (Fin nS) (AF F ⊗[F] E) → ℂ) : ℂ :=
  ∫ u in 𝓕, f (C * u) ∂ν

end GlobalTheory.LagrTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevMoveCommLevelMapOfTrivialMod
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LevPull
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open OverMove in

theorem levMove_comm_levelMap_of_trivial_mod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → (∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (IntermediateField.inclusion h).toRingHom) → ∀ (ρ₂ : d.Xo₂.X ⟶ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂) (g gA : Dw.La →ₗ[𝓞 E] Dw.La), IsIso ρ₂ → IsLevMove ρ₂ ν₂ g gA → (∀ a, g a - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → ρ₂ ≫ d.r = d.r ∧ ν₂.φ ≫ d.m.φ = d.m.φ := by
  intro E _ _ _ H Dw l Xo c n d _ hLev hA2 hover ρ₂ ν₂ g gA _ hmv hg
  have hL : Out.Laws := GlobalTheory.T.abelianScheme_laws_unconditional.1
  obtain ⟨hd, hM, -, -, -, hE, -⟩ := hLev
  have hA : l.A = 1 := Nat.eq_one_of_dvd_one (hA2 ▸ hd.2.2)
  have hK : KA l ≤ KA d.l₂ := by
    show IntermediateField.adjoin ℚ {H.rt0, zeta l.A} ≤ IntermediateField.adjoin ℚ {H.rt0, zeta d.l₂.A}
    rw [hA, hA2]
  have hb := hover hK
  have hred : IsReduced d.Xo₂.X := by
    haveI := d.Xo₂.smooth
    exact (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ d.Xo₂.s
      (SmoothOfRelativeDimension.smooth Dw.dim _)).1
  have hpd : d.pd = d.l₂.M / l.M := by
    rw [hM, Nat.mul_div_cancel_left _ (lt_of_lt_of_le (by norm_num) l.three_le)]
  have L₁ : Lev d.m := ⟨hpd ▸ hE.1, hE.2⟩
  obtain ⟨o, ⟨p⟩⟩ := obj_pull E H Dw l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (d.r ≫ Xo.s) d.r rfl rfl
    (by rw [LevelFibre.spMap_id', Category.comp_id]) Xo.univ
  obtain ⟨u, hu, F₁⟩ := exists_fib p L₁ (x := 𝟙 _) (Category.id_comp _)
  obtain ⟨u₂, hu₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν₂ u
  have hA1 : ∀ a, d.Xo₂.univ.etaA a = 1 := fun a => by
    have := d.Xo₂.univ.etaA_ker a
    rwa [hA2, one_smul] at this
  have hfix : ∀ a, (d.Xo₂.univ.eta (g a) ^ (d.l₂.M / l.M)).left = (d.Xo₂.univ.eta a ^ (d.l₂.M / l.M)).left :=
    fun a => by
      apply d.m.cart.1.hom_ext
      · rw [L₁.1, L₁.1, LevelActionLaws.eta_congr Xo (hg a)]
      · rw [LevelFibre.sec_w, LevelFibre.sec_w]
  have hone : (1 : 𝟙_ (Over d.Xo₂.X) ⟶ d.Xo₂.univ.t.G).left ≫ ν₂.φ = ρ₂ ≫ (1 : 𝟙_ (Over d.Xo₂.X) ⟶ d.Xo₂.univ.t.G).left := by
    have := hmv.2.2 0
    rwa [hA1, hA1] at this
  have F₂ : Fib o u₂ := by
    refine ⟨fun a => ?_, fun a => ?_⟩
    · rw [hu₂, ← Category.assoc, F₁.1, Category.id_comp, ← hfix, pow_left_comp ν₂ (hmv.2.1 a), Category.id_comp, hfix]
    · rw [hu₂, ← Category.assoc, F₁.2, Category.id_comp, Category.id_comp, hA1, one_pow]
      exact hone
  obtain ⟨q, hq⟩ := exists_objMap F₂ L₁
  have hr : (𝟙 _ ≫ ρ₂) ≫ d.r = d.r := by
    refine (Xo.rep d.Xo₂.X (d.r ≫ Xo.s) hred o).unique ⟨?_, ⟨q⟩⟩ ⟨rfl, ⟨p⟩⟩
    rw [Category.id_comp, Category.assoc, hb, ← Category.assoc, hmv.1]
  obtain ⟨q', hq'⟩ := LevelFibre.sab_cast hr q.toSABMap
  have e : p.toSABMap.φ = q'.φ := sabMap_eq_of_level_eq hL obj_isAbelianScheme_dim_rigidified_sym E H Dw l _ _ _ _ _ _
    _ _ Xo.univ o _ (Or.inl hred) p.toSABMap q' fun a => ⟨_, p.eta a, by rw [hq']; exact (q.eta a).trans (by rw [hr])⟩
  rw [hq', hq, ← hu, hu₂, Category.assoc] at e
  have : IsIso u.φ := u.cart.1.isIso_fst_of_isIso
  refine ⟨by simpa using hr, ((cancel_epi u.φ).1 e).symm⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralRationalPairFundDomainEqIterated
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped Pointwise

namespace GlobalTheory.PeriodicIterated

section General

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]

theorem prod_isAddFundamentalDomain (Γ₁ : AddSubgroup V) (Γ : AddSubgroup (V × V))
    (hΓ : ∀ w : V × V, w ∈ Γ ↔ w.1 ∈ Γ₁ ∧ w.2 ∈ Γ₁) (μ : Measure V) [SFinite μ]
    (𝓕₁ : Set V) (h : IsAddFundamentalDomain Γ₁ 𝓕₁ μ) :
    IsAddFundamentalDomain Γ (𝓕₁ ×ˢ 𝓕₁) (μ.prod μ) where
  nullMeasurableSet := h.nullMeasurableSet.prod h.nullMeasurableSet
  ae_covers := by
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae h.ae_covers
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae h.ae_covers
    filter_upwards [h1, h2] with p ha hb
    obtain ⟨a, ha⟩ := ha
    obtain ⟨b, hb⟩ := hb
    exact ⟨⟨((a : V), (b : V)), (hΓ _).2 ⟨a.2, b.2⟩⟩, ha, hb⟩
  aedisjoint := by
    intro g g' hne
    have hset : ∀ k : Γ, k +ᵥ (𝓕₁ ×ˢ 𝓕₁) =
        ((⟨(k : V × V).1, ((hΓ _).1 k.2).1⟩ : Γ₁) +ᵥ 𝓕₁) ×ˢ
          ((⟨(k : V × V).2, ((hΓ _).1 k.2).2⟩ : Γ₁) +ᵥ 𝓕₁) := by
      intro k
      ext ⟨x, y⟩
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_prod, AddSubgroup.vadd_def,
        AddSubgroup.coe_neg, vadd_eq_add, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg]
    show μ.prod μ ((g +ᵥ (𝓕₁ ×ˢ 𝓕₁)) ∩ (g' +ᵥ (𝓕₁ ×ˢ 𝓕₁))) = 0
    rw [hset g, hset g', Set.prod_inter_prod, Measure.prod_prod]
    by_cases h1 : (g : V × V).1 = (g' : V × V).1
    · have h2 : (g : V × V).2 ≠ (g' : V × V).2 := by
        intro h2
        exact hne (Subtype.ext (Prod.ext h1 h2))
      have := h.aedisjoint (i := ⟨(g : V × V).2, ((hΓ _).1 g.2).2⟩)
        (j := ⟨(g' : V × V).2, ((hΓ _).1 g'.2).2⟩) (fun h' => h2 (congrArg Subtype.val h'))
      rw [show μ _ = 0 from this, mul_zero]
    · have := h.aedisjoint (i := ⟨(g : V × V).1, ((hΓ _).1 g.2).1⟩)
        (j := ⟨(g' : V × V).1, ((hΓ _).1 g'.2).1⟩) (fun h' => h1 (congrArg Subtype.val h'))
      rw [show μ _ = 0 from this, zero_mul]

theorem lintegral_fundamentalDomain_eq_iterated (Γ₁ : AddSubgroup V) [Countable Γ₁]
    (Γ : AddSubgroup (V × V)) (hΓ : ∀ w : V × V, w ∈ Γ ↔ w.1 ∈ Γ₁ ∧ w.2 ∈ Γ₁)
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (mW : MeasurableSpace (V × V)) (hmW : mW = Prod.instMeasurableSpace)
    (ν : @Measure (V × V) mW) (hν : @Measure.IsAddHaarMeasure _ _ _ mW ν)
    (𝓕 : Set (V × V)) (h𝓕 : @IsAddFundamentalDomain Γ _ _ _ mW 𝓕 ν)
    (𝓕₁ : Set V) (h𝓕₁ : IsAddFundamentalDomain Γ₁ 𝓕₁ μ) :
    ∃ c₁ : ENNReal, c₁ ≠ 0 ∧ c₁ ≠ ⊤ ∧ ∀ G : V × V → ENNReal, @Measurable _ _ mW _ G →
      (∀ γ ∈ Γ, ∀ w, G (γ + w) = G w) →
      ∫⁻ w in 𝓕, G w ∂ν = c₁ * ∫⁻ x in 𝓕₁, ∫⁻ y in 𝓕₁, G (x, y) ∂μ ∂μ := by
  subst hmW
  haveI := hν
  haveI : Countable Γ := by
    have hinj : Function.Injective (fun k : Γ =>
        ((⟨(k : V × V).1, ((hΓ _).1 k.2).1⟩ : Γ₁), (⟨(k : V × V).2, ((hΓ _).1 k.2).2⟩ : Γ₁))) := by
      intro k k' hk
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at hk
      exact Subtype.ext (Prod.ext hk.1 hk.2)
    exact hinj.countable
  have hmeq := Measure.isAddLeftInvariant_eq_smul ν (μ.prod μ)
  set c : NNReal := Measure.addHaarScalarFactor ν (μ.prod μ)
  have hcpos : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν (μ.prod μ)
  have hν' : ν = (c : ENNReal) • μ.prod μ := by
    rw [← ENNReal.smul_def]; exact hmeq
  refine ⟨(c : ENNReal), by exact_mod_cast hcpos.ne', ENNReal.coe_ne_top, fun G hG hper => ?_⟩
  have hD : IsAddFundamentalDomain Γ (𝓕₁ ×ˢ 𝓕₁) ν :=
    (prod_isAddFundamentalDomain Γ₁ Γ hΓ μ 𝓕₁ h𝓕₁).mono (by rw [hν']; exact Measure.smul_absolutelyContinuous)
  rw [h𝓕.setLIntegral_eq hD G (fun g x => hper g g.2 x), hν', Measure.restrict_smul,
    lintegral_smul_measure, ← Measure.prod_restrict, lintegral_prod _ hG.aemeasurable, smul_eq_mul]

end General

end GlobalTheory.PeriodicIterated

namespace GlobalTheory.PeriodicIterated

theorem countable_ratVec (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Countable (GlobalTheory.ThetaParseval.ratVec F κ) := by
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  exact (AddMonoidHom.rangeRestrict_surjective _).countable

theorem mem_ratPair_iff_ratVec (F : Type) [Field F] [NumberField F] (κ : Type)
    (w : (κ → AF F) × (κ → AF F)) :
    w ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ ↔
      w.1 ∈ GlobalTheory.ThetaParseval.ratVec F κ ∧ w.2 ∈ GlobalTheory.ThetaParseval.ratVec F κ := by
  rw [GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff, GlobalTheory.ThetaParseval.mem_ratVec_iff,
    GlobalTheory.ThetaParseval.mem_ratVec_iff]
  constructor
  · rintro ⟨y, z, rfl⟩
    exact ⟨⟨y, rfl⟩, ⟨z, rfl⟩⟩
  · rintro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    exact ⟨y, z, Prod.ext hy hz⟩

theorem lintegral_ratPair_fundamentalDomain_eq_iterated : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (ν : @Measure ((κ → AF F) × (κ → AF F)) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ (𝓕 : Set ((κ → AF F) × (κ → AF F))), @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) _ _ _ (borel _) 𝓕 ν →
    ∀ (𝓕₁ : Set (κ → AF F)), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ →
    ∃ c₁ : ENNReal, c₁ ≠ 0 ∧ c₁ ≠ ⊤ ∧ ∀ G : (κ → AF F) × (κ → AF F) → ENNReal, @Measurable _ _ (borel _) _ G →
      (∀ γ ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ, ∀ w, G (γ + w) = G w) →
      ∫⁻ w in 𝓕, G w ∂ν = c₁ * ∫⁻ x in 𝓕₁, ∫⁻ y in 𝓕₁, G (x, y) ∂μ ∂μ := by
  intro F _ _ κ _ μ hμ ν hν 𝓕 h𝓕 𝓕₁ h𝓕₁
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := countable_ratVec F κ
  haveI := hμ
  exact lintegral_fundamentalDomain_eq_iterated (GlobalTheory.ThetaParseval.ratVec F κ)
    (GlobalTheory.WeilUnitaryTransport.ratPair F κ) (mem_ratPair_iff_ratVec F κ) μ (borel _)
    (Prod.borelSpace (α := κ → AF F) (β := κ → AF F)).measurable_eq.symm ν hν 𝓕 h𝓕 𝓕₁ h𝓕₁

end GlobalTheory.PeriodicIterated

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSqCompContinuousLinearEquivMixedSpaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_sq_comp_continuousLinearEquiv_mixedSpace : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (n : ℕ)
    (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)),
    ∃ c : ℝ≥0∞, ∀ h : (κ → mixedEmbedding.mixedSpace F) → ℂ,
      ∫⁻ x, ‖h (Q x)‖ₑ ^ 2 = c * ∫⁻ z, ‖h z‖ₑ ^ 2 := by
  first | exact @GlobalTheory.lintegral_sq_comp_linearEquiv_mixed | exact GlobalTheory.lintegral_sq_comp_linearEquiv_mixed | (intros; apply GlobalTheory.lintegral_sq_comp_linearEquiv_mixed <;> assumption)
end

