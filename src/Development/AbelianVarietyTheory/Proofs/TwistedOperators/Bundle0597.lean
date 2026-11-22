import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0340
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0554
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0404
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0576
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GkGeneratedCuspFormsOfType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0343
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0578
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0579
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteOfMemGKModuleGeneratedBy
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.GKGenKFin

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

def kGrp : Subgroup (GA D V) :=
  Subgroup.closure {k | ∃ τ g, GlobalTheory.CuspGK.InK M τ g ∧ k = atTau θ V τ g}

theorem kGrp_le : kGrp θ M ≤ GinfC V :=
  (Subgroup.closure_le _).2 fun _ ⟨τ, g, _, e⟩ => e ▸ GlobalTheory.FinTranslate.atTau_mem θ V τ g

theorem rTr_mul (x y : GA D V) (f : GA D V → ℂ) : rTr V (x * y) f = rTr V x (rTr V y f) := by
  funext g
  simp only [rTr, mul_assoc]

theorem rTr_inv_rTr (x : GA D V) (f : GA D V → ℂ) : rTr V x⁻¹ (rTr V x f) = f := by
  funext g
  simp only [rTr, inv_mul_cancel_right]

theorem rTr_mem_of_kStable {W : Submodule ℂ (GA D V → ℂ)} (hW : FiniteDimensional ℂ W)
    (hK : GlobalTheory.KTypeProj.KStable θ M W) {k : GA D V} (hk : k ∈ kGrp θ M) : ∀ f ∈ W, rTr V k f ∈ W := by
  refine Subgroup.closure_induction (p := fun k _ => ∀ f ∈ W, rTr V k f ∈ W) (fun x hx => ?_) ?_
    (fun x y _ _ hx hy => ?_) (fun x _ hx => ?_) hk
  · obtain ⟨τ, g, hg, rfl⟩ := hx
    exact hK τ g hg
  · intro f hf
    have e : rTr V 1 f = f := funext fun g => by simp [rTr]
    rw [e]
    exact hf
  · intro f hf
    rw [rTr_mul]
    exact hx _ (hy f hf)
  · let T : W →ₗ[ℂ] W := ((GlobalTheory.KTypeProj.rTrL x).restrict (p := W) (q := W) fun f hf => hx f hf)
    have hinj : Function.Injective T := by
      intro a b hab
      apply Subtype.ext
      have h1 : rTr V x a.1 = rTr V x b.1 := congrArg Subtype.val hab
      have h2 := congrArg (rTr V x⁻¹) h1
      rwa [rTr_inv_rTr, rTr_inv_rTr] at h2
    have hsurj := LinearMap.injective_iff_surjective.1 hinj
    intro f hf
    obtain ⟨h, hh⟩ := hsurj ⟨f, hf⟩
    have e : rTr V x h.1 = f := congrArg Subtype.val hh
    rw [← e, rTr_inv_rTr]
    exact h.2

theorem isKFinite_smul {Φ : GA D V → ℂ} {K : Subgroup (GA D V)} (h : GlobalTheory.Doubling.IsKFinite K Φ) (c : ℂ) :
    GlobalTheory.Doubling.IsKFinite K (c • Φ) := by
  obtain ⟨W, hW, hm⟩ := GlobalTheory.Doubling.isKFinite_iff.1 h
  exact GlobalTheory.Doubling.isKFinite_iff.2 ⟨W, hW, fun k hk => by
    exact W.smul_mem c (hm k hk)⟩

def kfinSm (hθ : IsInfFam θ) : Submodule ℂ (GA D V → ℂ) where
  carrier := {x | IsAutFunSm θ V x ∧ GlobalTheory.Doubling.IsKFinite (kGrp θ M) x}
  zero_mem' := ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_zero θ V, .of_invariant fun _ _ _ => rfl⟩
  add_mem' := fun h h' => ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_add h.1 h'.1, h.2.add h'.2⟩
  smul_mem' := fun c _ h => ⟨GlobalTheory.Mem.AutSpace.isAutFunSm_smul c h.1, isKFinite_smul h.2 c⟩

theorem exists_kStable {x : GA D V → ℂ} (h : GlobalTheory.Doubling.IsKFinite (kGrp θ M) x) :
    ∃ Y : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Y ∧ x ∈ Y ∧ GlobalTheory.KTypeProj.KStable θ M Y := by
  refine ⟨GlobalTheory.Doubling.kSpan (kGrp θ M) x, h, Submodule.subset_span ⟨1, one_mem _, funext fun g => by simp⟩, ?_⟩
  intro τ g hg f hf
  have ha : atTau θ V τ g ∈ kGrp θ M := Subgroup.subset_closure ⟨τ, g, hg, rfl⟩
  have hle : GlobalTheory.Doubling.kSpan (kGrp θ M) x ≤
      (GlobalTheory.Doubling.kSpan (kGrp θ M) x).comap (GlobalTheory.KTypeProj.rTrL (atTau θ V τ g)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    refine Submodule.subset_span ⟨atTau θ V τ g * k, mul_mem ha hk, ?_⟩
    funext y
    simp only [GlobalTheory.KTypeProj.rTrL_apply, rTr, mul_assoc]
  exact hle hf

theorem isGKSub_kfinSm (hθ : IsInfFam θ) : GlobalTheory.CuspGK.IsGKSub θ M (kfinSm θ M hθ) where
  k τ g hg f hf := ⟨GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ V f hf.1 τ g hg.1,
    hf.2.translate (Subgroup.subset_closure ⟨τ, g, hg, rfl⟩)⟩
  lie τ X hX f hf := ⟨GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX hf.1,
    GlobalTheory.CuspLie.isKFinite_Rder hθ hX (kGrp_le θ M) hf.1.smooth hf.2⟩

theorem kFinite_of_mem_gkGen : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ → ∀ ψ : GA D V → ℂ,
    IsAutFunSm θ V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ GlobalTheory.KTypeProj.KStable θ M W) →
    ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∃ Y : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Y ∧ x ∈ Y ∧
      GlobalTheory.KTypeProj.KStable θ M Y := by
  intro D θ V S M hθ ψ hψ ⟨W, hW, hψW, hK⟩ x hx
  have hm : ψ ∈ kfinSm θ M hθ :=
    ⟨hψ, GlobalTheory.Doubling.isKFinite_iff.2 ⟨W, hW, fun k hk => rTr_mem_of_kStable θ M hW hK hk ψ hψW⟩⟩
  exact exists_kStable θ M (GlobalTheory.CuspGK.gkGen_le θ M hm (isGKSub_kfinSm θ M hθ) hx).2

end GlobalTheory.GKGenKFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KTypeClassSubmodule
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.PlaceDecomp

theorem hasCtp_closed : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → GlobalTheory.FunPr.Hypotheses₂ → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) (τ : D.what₂.Tau), (∀ f f' : GA D N.V → ℂ, f ∈ Cls θ N U → f' ∈ Cls θ N U → f + f' ∈ Cls θ N U) → (0 : GA D N.V → ℂ) ∈ Cls θ N U → (∀ (c : ℂ) (f : GA D N.V → ℂ), f ∈ Cls θ N U → c • f ∈ Cls θ N U) → (∀ T T' : N.M.H τ → N.M.H τ, HasCtp θ N U (TyOf θ N ρ) τ T → HasCtp θ N U (TyOf θ N ρ) τ T' → HasCtp θ N U (TyOf θ N ρ) τ (fun w => T w + T' w) ∧ HasCtp θ N U (TyOf θ N ρ) τ (fun w => T (T' w))) ∧ (∀ (c : ℂ) (T : N.M.H τ → N.M.H τ), HasCtp θ N U (TyOf θ N ρ) τ T → HasCtp θ N U (TyOf θ N ρ) τ (fun w => c • T w)) ∧ HasCtp θ N U (TyOf θ N ρ) τ (fun _ => 0) := by
  intro D θ _ hp N U W _ _ ρ τ hadd _ hsmul
  haveI : CompleteSpace (N.M.H τ) := (N.M.ds τ).1
  have hσ := (std_of_isDS hp.harishChandraModules (N.M.ds τ)).1
  have hs : ∀ (c : ℂ) (T : N.M.H τ → N.M.H τ), HasCtp θ N U (TyOf θ N ρ) τ T →
      HasCtp θ N U (TyOf θ N ρ) τ (fun w => c • T w) := by
    rintro c T ⟨A, hA, hm⟩
    refine ⟨fun φ => c • A φ, ⟨fun f hf => (hA.cont f hf).const_smul c, fun f f' hf hf' => ?_, fun a f hf => ?_,
      fun f hf => hsmul c _ (hA.maps f hf), fun τ' h f hf ht x => ?_, fun τ' h g hg f hf => ?_,
      fun τ' h X hX f hf => ?_⟩, fun φ hφ x S v ℓ C hS hc h => (hm φ hφ x S v ℓ C hS hc h).smul hσ hS c⟩
    · simp only [hA.add f f' hf hf', smul_add]
    · simp only [hA.smul a f hf, smul_comm c a]
    · exact Submodule.smul_mem _ c (hA.keep τ' h f hf ht x)
    · simp only [hA.tr τ' h g hg f hf]
      rfl
    · simp only [hA.lie τ' h X hX f hf, GlobalTheory.Mem.AutSpace.Rder_smul]
  refine ⟨?_, hs, ?_⟩
  · rintro T T' ⟨A, hA, hm⟩ ⟨A', hA', hm'⟩
    refine ⟨⟨fun φ => A φ + A' φ, ⟨fun f hf => (hA.cont f hf).add (hA'.cont f hf), fun f f' hf hf' => ?_,
      fun a f hf => ?_, fun f hf => hadd _ _ (hA.maps f hf) (hA'.maps f hf), fun τ' h f hf ht x => ?_,
      fun τ' h g hg f hf => ?_, fun τ' h X hX f hf => ?_⟩,
      fun φ hφ x S v ℓ C hS hc h => (hm φ hφ x S v ℓ C hS hc h).add hσ (hm' φ hφ x S v ℓ C hS hc h) hS⟩,
      ⟨fun φ => A (A' φ), ⟨fun f hf => hA.cont _ (hA'.cont f hf), fun f f' hf hf' => ?_, fun a f hf => ?_,
      fun f hf => hA.maps _ (hA'.maps f hf), fun τ' h f hf ht => hA.keep τ' h _ (hA'.maps f hf) (hA'.keep τ' h f hf ht),
      fun τ' h g hg f hf => ?_, fun τ' h X hX f hf => ?_⟩,
      fun φ hφ x S v ℓ C hS hc h => hm _ (hA'.maps φ hφ) x S _ ℓ C hS hc (hm' φ hφ x S v ℓ C hS hc h)⟩⟩
    · simp only [hA.add f f' hf hf', hA'.add f f' hf hf']
      abel
    · simp only [hA.smul a f hf, hA'.smul a f hf, smul_add]
    · exact Submodule.add_mem _ (hA.keep τ' h f hf ht x) (hA'.keep τ' h f hf ht x)
    · simp only [hA.tr τ' h g hg f hf, hA'.tr τ' h g hg f hf]
      rfl
    · simp only [hA.lie τ' h X hX f hf, hA'.lie τ' h X hX f hf]
      exact (GlobalTheory.Mem.AutSpace.Rder_add (hA.maps f hf).1.1.smooth (hA'.maps f hf).1.1.smooth hX).symm
    · simp only [hA'.add f f' hf hf', hA.add _ _ (hA'.cont f hf) (hA'.cont f' hf')]
    · simp only [hA'.smul a f hf, hA.smul a _ (hA'.cont f hf)]
    · simp only [hA'.tr τ' h g hg f hf, hA.tr τ' h g hg _ (hA'.maps f hf)]
    · simp only [hA'.lie τ' h X hX f hf, hA.lie τ' h X hX _ (hA'.maps f hf)]
  · simpa using hs 0 _ (hasCtp_id θ N U _ τ)

end GlobalTheory.PlaceDecomp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KTypeClassTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.PlaceDecomp

theorem hasCtp_translate : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → GlobalTheory.FunPr.Hypotheses₂ → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) (τ : D.what₂.Tau), ∀ g ∈ UJset (N.M.ε τ), HasCtp θ N U (TyOf θ N ρ) τ (N.M.σ τ g) := by
  intro D θ hθ hp N U W _ _ ρ τ g hg
  haveI : IsTopologicalGroup (GA D N.V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  haveI : CompleteSpace (N.M.H τ) := (N.M.ds τ).1
  have hσ : Std (N.M.ε τ) (N.M.σ τ) := std_of_isDS hp.harishChandraModules (N.M.ds τ)
  have hk : (N.M.fr τ)⁻¹ * g * N.M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) := conj_inv_mem hP hJ hg
  have comm : ∀ τ', τ' ≠ τ → ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ'),
      atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ) * atTau θ N.V τ' h =
        atTau θ N.V τ' h * atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ) :=
    fun τ' hne h hh => GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ N.V τ τ' (Ne.symm hne) _ hk h hh
  refine ⟨rTr N.V (atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ)), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro f hf
    exact hf.comp (continuous_mul_right _)
  · intro f f' _ _
    rfl
  · intro c f _
    rfl
  · rintro f ⟨⟨a1, a2, a3⟩, a4⟩
    refine ⟨⟨GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ N.V f a1 τ _ hk, GlobalTheory.Cusp.isCuspFun_rTr a2 _,
      fun τ' => GlobalTheory.CuspGKForms.isTypeAt_rTr hθ (a3 τ') hk⟩, fun k hkU hkf x => ?_⟩
    simp only [rTr]
    rw [mul_assoc x, ← GlobalTheory.PointAtPlaceHom.comm_of_mem N.V (GlobalTheory.PointAtPlaceHom.atTau_mem N.V τ _) hkf, ← mul_assoc x]
    exact a4 k hkU hkf _
  · intro τ' hne f _ hf x
    have e : (fun k => rTr N.V (atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ)) f
        (x * GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k)) =
        fun k => f (x * atTau θ N.V τ ((N.M.fr τ)⁻¹ * g * N.M.fr τ) *
          GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k) := funext fun k => by
      simp only [rTr, GlobalTheory.Published.AutFin.kAt]
      rw [mul_assoc x, mul_assoc x, comm τ' hne _
        (GlobalTheory.Published.AutFin.conj_mem_UH (N.M.fr_unit τ') (N.M.fr_gram τ') k)]
    show (fun k => _) ∈ _
    rw [e]
    exact hf _
  · intro τ' hne h hh f _
    funext x
    simp only [rTr]
    rw [mul_assoc x, mul_assoc x, comm τ' hne h hh]
  · intro τ' hne X hX f _
    funext x
    simp only [Rder, rTr, oneP]
    congr 1
    funext t
    rw [mul_assoc x, mul_assoc x, comm τ' hne _
      (GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit N.V τ') hX t)]
  · intro φ _ x S v ℓ C hS _ h
    exact h.translate hσ.1 hS hg fun y hy => by
      simp only [res, rTr, at_mul hθ hP hJ hy hg, mul_assoc x]

end GlobalTheory.PlaceDecomp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeDepthCompFrameBlockBoundedPeriodic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open ValuativeRel Formalism.L2.Host
open Matrix

namespace GlobalTheory.DepthBound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_unit_bound {ι : Type} [Fintype ι] (f : ι → k) :
    ∃ R : kˣ, ∀ i, valuation k (f i) ≤ valuation k (R : k) := by
  classical
  let γ : ValueGroupWithZero k := ∏ i, max 1 (valuation k (f i))
  have h1 : 1 ≤ γ := Finset.one_le_prod' (fun i _ => le_max_left _ _)
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective γ
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact absurd (hx ▸ h1) (not_le.2 zero_lt_one)
  refine ⟨Units.mk0 x hx0, fun i => ?_⟩
  rw [Units.val_mk0, hx]
  exact (le_max_right _ _).trans
    (Finset.single_le_prod' (f := fun j => max 1 (valuation k (f j))) (fun j _ => le_max_left _ _) (Finset.mem_univ i))

theorem frameMatrixSecondColumnBlock_mul_transpose {A A' D : Type} [Fintype A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
    (σ : A ⊕ A' ≃ D) : Y0 k σ * (Y0 k σ)ᵀ = 1 := by
  ext i j
  rw [frameMatrixSecondColumnBlock_mul_apply]
  by_cases hij : i = j
  · subst hij; simp [Y0]
  · simp [Y0, Matrix.one_apply, hij, Ne.symm hij]

theorem latticeDepth_comp_frameBlock_bounded_periodic : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (σ : A ⊕ A' ≃ D) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → ∀ (c : D → kˣ) {Ψ : Matrix A' D k → ℂ}, HasDepth ϖ e (diagLat c) Ψ → ∀ h : GL D k, ∃ R : kˣ, ∃ N : ℕ, (∀ g : Matrix A' A' k, Ψ (g * (Y0 k σ * h.val)) ≠ 0 → ∀ i j, valuation k (g i j) ≤ valuation k (R : k)) ∧ ∀ g Z : Matrix A' A' k, (∀ i j, valuation k (Z i j) ≤ valuation k ((ϖ ^ N : kˣ) : k)) → Ψ ((g + Z) * (Y0 k σ * h.val)) = Ψ (g * (Y0 k σ * h.val)) := by
  intro k _ _ _ _ A A' D _ _ _ _ _ _ σ ϖ e hϖ c Ψ hΨ h
  set Y : Matrix A' D k := Y0 k σ * h.val with hYdef
  set W : Matrix D A' k := (h⁻¹).val * (Y0 k σ)ᵀ with hWdef
  have hYW : Y * W = 1 := by
    rw [hYdef, hWdef, Matrix.mul_assoc, ← Matrix.mul_assoc h.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, frameMatrixSecondColumnBlock_mul_transpose]
  obtain ⟨R, hR⟩ := exists_unit_bound (fun p : D × A' => (c p.1 : k) * W p.1 p.2)
  obtain ⟨R', hR'⟩ := exists_unit_bound (fun p : A' × D => Y p.1 p.2 / (((ϖ ^ e) * c p.2 : kˣ) : k))
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hR'0 : valuation k (R' : k) ≠ 0 := by simp
  obtain ⟨N, hN⟩ := exists_pow_lt₀ hlt (Units.mk0 (valuation k (R' : k))⁻¹ (inv_ne_zero hR'0))
  have hN' : valuation k (ϖ : k) ^ N * valuation k (R' : k) ≤ 1 := by
    have : valuation k (ϖ : k) ^ N ≤ (valuation k (R' : k))⁻¹ := by simpa using hN.le
    calc valuation k (ϖ : k) ^ N * valuation k (R' : k)
        ≤ (valuation k (R' : k))⁻¹ * valuation k (R' : k) := mul_le_mul' this le_rfl
      _ = 1 := inv_mul_cancel₀ hR'0
  refine ⟨R, N, ?_, ?_⟩
  · intro g hg i j
    have hmem : g * Y ∈ matLat A' (diagLat c) := by
      by_contra hc; exact hg (hΨ.1 _ hc)
    have hg' : g = (g * Y) * W := by rw [Matrix.mul_assoc, hYW, Matrix.mul_one]
    rw [hg', Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    calc valuation k ((g * Y) i l) * valuation k (W l j)
        ≤ valuation k (c l : k) * valuation k (W l j) := mul_le_mul' (mem_diagLat.1 (hmem i) l) le_rfl
      _ = valuation k ((c l : k) * W l j) := (map_mul _ _ _).symm
      _ ≤ valuation k (R : k) := hR (l, j)
  · intro g Z hZ
    rw [Matrix.add_mul]
    refine hΨ.2 _ _ fun i => ?_
    rw [smul_diagLat, mem_diagLat]
    intro m
    show valuation k ((Z * Y) i m) ≤ _
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    have hpos : 0 < valuation k ((((ϖ ^ e) * c m : kˣ)) : k) := zero_lt_iff.2 (by simp)
    have h1 := hR' (l, m)
    simp only at h1
    rw [map_div₀, div_le_iff₀ hpos] at h1
    have hz : valuation k (Z i l) ≤ valuation k (ϖ : k) ^ N := by
      simpa [Units.val_pow_eq_pow_val, map_pow] using hZ i l
    calc valuation k (Z i l) * valuation k (Y l m)
        ≤ valuation k (ϖ : k) ^ N * (valuation k (R' : k) * valuation k ((((ϖ ^ e) * c m : kˣ)) : k)) :=
          mul_le_mul' hz h1
      _ = (valuation k (ϖ : k) ^ N * valuation k (R' : k)) * valuation k ((((ϖ ^ e) * c m : kˣ)) : k) :=
          (mul_assoc _ _ _).symm
      _ ≤ 1 * valuation k ((((ϖ ^ e) * c m : kˣ)) : k) := mul_le_mul' hN' le_rfl
      _ = _ := one_mul _

end GlobalTheory.DepthBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviThetaValueLeDetMulRationalSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviThetaValue_le_det_mul_rational_sum : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec S S₀ r)
    (χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
    IsWeilDatumO ψ S T χS χT om →
    ∃ (μ' : Measure (Mx D T.rank r)) (𝓕' : Set (Mx D T.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D T.rank r) μ' 𝓕' ∧
      ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ α : GL (Fin r) (Formalism.L2.Theta.AE D),
        ‖om (d.levi α, 1) f 0‖ₑ ≤ ENNReal.ofReal (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank α) *
          ∑' ξ : Matrix (Fin T.rank) (Fin r) D.host.E,
            ‖d.mixS T ψ μ' 𝓕' f (HMul.hMul (ξ.map (incA D) : Mx D T.rank r) α.1) 0‖ₑ := by
  first | exact @GlobalTheory.LeviThetaSum.levi_sum | exact GlobalTheory.LeviThetaSum.levi_sum | (intros; apply GlobalTheory.LeviThetaSum.levi_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftResMulSub
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.ColSubst

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem liftRes_mul_sub {A C : Type} [Fintype C] {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (T : A → C → Res k e)
    (N : Matrix C C 𝒪[k]) (i : A) (j : C) :
    valuation k ((liftRes (Matrix.of T * N.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e)) :
        A → C → Res k e) - liftRes T * N.map (fun x => (x : k))) i j) ≤ valuation k ((ϖ ^ e : kˣ) : k) := by
  set r : 𝒪[k] := Quotient.out ((Matrix.of T * N.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e))) i j) -
    ∑ l, Quotient.out (T i l) * N l j with hr
  have h1 : ((liftRes (Matrix.of T * N.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e)) :
        A → C → Res k e) - liftRes T * N.map (fun x => (x : k))) i j) = (r : k) := by
    simp [hr, liftRes, Matrix.mul_apply]
  rw [h1, ← GlobalTheory.SplitFlip.Model.val_le_iff_mem hϖ, ← Ideal.Quotient.eq_zero_iff_mem, hr, map_sub, map_sum]
  simp [Matrix.mul_apply, Ideal.Quotient.mk_out]

theorem sum_liftRes_mul {A C : Type} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C] {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ)
    (N N' : Matrix C C 𝒪[k]) (hN : N * N' = 1) (F : Matrix A C k → ℂ)
    (hF : ∀ T Z : Matrix A C k, (∀ i j, valuation k (Z i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)) → F (T + Z) = F T) :
    ∑ T : A → C → Res k e, F (liftRes T * N.map (fun x => (x : k))) = ∑ T : A → C → Res k e, F (liftRes T) := by
  classical
  set π := Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e) with hπ
  let φ : (A → C → Res k e) → (A → C → Res k e) := fun T => Matrix.of T * N.map π
  have hinj : Function.Injective φ := by
    intro T T' h
    have h2 := congrArg (fun M : Matrix A C (Res k e) => M * N'.map π) h
    simp only [φ, Matrix.mul_assoc, ← Matrix.map_mul, hN, Matrix.map_one _ (map_zero π) (map_one π),
      Matrix.mul_one] at h2
    exact h2
  have hbij : Function.Bijective φ := Finite.injective_iff_bijective.1 hinj
  rw [← hbij.sum_comp (fun T => F (liftRes T))]
  refine Finset.sum_congr rfl fun T _ => ?_
  symm
  rw [show liftRes (φ T) = liftRes T * N.map (fun x => (x : k)) +
    (liftRes (φ T) - liftRes T * N.map (fun x => (x : k))) by abel]
  exact hF _ _ fun i j => liftRes_mul_sub hϖ e T N i j

end GlobalTheory.ColSubst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSplitPlaceFinitePointsOffPrimesOfSupportedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_splitPlaceFinitePointsOffPrimes_of_supported : ∀ {D : D7} (V : HSp D) (Q : Finset ℕ) (s : GfC V),
    GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) (∏ q ∈ Q, q) (finHom V s.1).1 → s ∈ GlobalTheory.MovedKappaEx.splitOff V Q := by
  first | exact @GlobalTheory.MovedKappaEx.mem_splitOff_of_suppSplit | exact GlobalTheory.MovedKappaEx.mem_splitOff_of_suppSplit | (intros; apply GlobalTheory.MovedKappaEx.mem_splitOff_of_suppSplit <;> assumption)
end

