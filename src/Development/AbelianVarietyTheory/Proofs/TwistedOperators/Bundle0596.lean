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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0340
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0233
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0554
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0574
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0343
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0253
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0497
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0494
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0570
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0579
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmOfMemGkGen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KTypeAdm

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

def smAut (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) : Submodule ℂ (GA D V → ℂ) where
  carrier := {f | IsAutFunSm θ V f}
  add_mem' := fun ha hb => GlobalTheory.Mem.AutSpace.isAutFunSm_add ha hb
  zero_mem' := GlobalTheory.Mem.AutSpace.isAutFunSm_zero θ V
  smul_mem' := fun c _ ha => GlobalTheory.Mem.AutSpace.isAutFunSm_smul c ha

theorem isAutFunSm_of_mem_gkGen (hθ : IsInfFam θ) {ψ : GA D V → ℂ} (hψ : IsAutFunSm θ V ψ) :
    ∀ f ∈ GlobalTheory.CuspGK.gkGen θ M ψ, IsAutFunSm θ V f := by
  have hA : GlobalTheory.CuspGK.IsGKSub θ M (smAut θ V) :=
    ⟨fun τ g hg f hf => GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ V f hf τ g hg.1,
      fun τ X hX f hf => GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX hf⟩
  exact fun f hf => GlobalTheory.CuspGK.gkGen_le θ M (A := smAut θ V) hψ hA hf

theorem level_gkGen {ψ : GA D V → ℂ} (hψ : IsAutFunSm θ V ψ) :
    ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧
      ∀ f ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ u ∈ U, u ∈ GfC V → ∀ g, f (g * u) = f g := by
  obtain ⟨U, hU, hψU⟩ := hψ.level
  let A : Submodule ℂ (GA D V → ℂ) :=
    { carrier := {f | ∀ u ∈ U, u ∈ GfC V → ∀ g, f (g * u) = f g}
      add_mem' := fun ha hb u hu hu' g => by simp only [Pi.add_apply, ha u hu hu' g, hb u hu hu' g]
      zero_mem' := fun _ _ _ _ => rfl
      smul_mem' := fun c f hf u hu hu' g => by simp only [Pi.smul_apply, hf u hu hu' g] }
  have hA : GlobalTheory.CuspGK.IsGKSub θ M A := by
    refine ⟨fun τ g _ f hf u hu hu' x => ?_, fun τ X _ f hf u hu hu' x => ?_⟩
    · show f (x * u * atTau θ V τ g) = f (x * atTau θ V τ g)
      rw [mul_assoc, ← GlobalTheory.PointAtPlaceHom.comm_of_mem V (GlobalTheory.PointAtPlaceHom.atTau_mem (θ := θ) V τ g) hu',
        ← mul_assoc]
      exact hf u hu hu' _
    · have := congrFun (GlobalTheory.Mem.FinTranslate.Rder_rTr (θ := θ) hu' τ X f) x
      rw [show rTr V u f = f from funext (hf u hu hu')] at this
      exact this.symm
  exact ⟨U, hU, fun f hf => GlobalTheory.CuspGK.gkGen_le θ M (A := A) (fun u hu hu' g => hψU u hu hu' g) hA hf⟩

theorem gelf_mem_of_isGKSub {A : Submodule ℂ (GA D V → ℂ)} (hA : GlobalTheory.CuspGK.IsGKSub θ M A) (τ : D.what₂.Tau) (k : ℕ) :
    ∀ f ∈ A, gelf θ V τ k f ∈ A := by
  intro f hf
  have hC : ∀ Z, ∀ g ∈ A, RderC θ V τ Z g ∈ A := fun Z g hg => by
    obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem (V := V) τ Z
    exact A.add_mem (hA.lie τ _ h1 g hg) (A.smul_mem _ (hA.lie τ _ h2 g hg))
  have key : ∀ l : List ((GA D V → ℂ) → (GA D V → ℂ)), (∀ F ∈ l, ∀ g ∈ A, F g ∈ A) →
      l.foldr (fun F acc => F acc) f ∈ A := by
    intro l hl
    induction l with
    | nil => exact hf
    | cons F l ih => exact hl F (by simp) _ (ih fun F' hF' => hl F' (by simp [hF']))
  refine Submodule.sum_mem _ fun idx _ => key _ fun F hF => ?_
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hF
  exact hC _

end GlobalTheory.KTypeAdm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmRealProd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

open Classical

namespace GlobalTheory.DefiniteDecomp

open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

variable {D : D7}

theorem pairwise_commute {θ : InfFam D} {V : HSp D} {g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (h : IsInfFam θ ∧ ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    ((Finset.univ : Finset D.what₂.Tau) : Set D.what₂.Tau).Pairwise
      (Function.onFun Commute fun τ => atTau θ V τ (g τ)) :=
  fun τ _ τ' _ hne => GlobalTheory.PointAtPlaceComm.atTau_comm D θ h.1 V τ τ' hne _ (h.2 τ) _ (h.2 τ')

def realProd (θ : InfFam D) (V : HSp D) (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) : GA D V :=
  if h : IsInfFam θ ∧ ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) then
    Finset.univ.noncommProd (fun τ => atTau θ V τ (g τ)) (pairwise_commute h)
  else 1

variable {θ : InfFam D} {V : HSp D}

theorem update_mem {g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (τ₀ : D.what₂.Tau) {g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ₀)) (τ : D.what₂.Tau) :
    Function.update g τ₀ g' τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  by_cases h : τ = τ₀
  · subst h; rw [Function.update_self]; exact hg'
  · rw [Function.update_of_ne h]; exact hg τ

theorem realProd_update (hθ : IsInfFam θ) {g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (τ₀ : D.what₂.Tau) {g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ₀)) :
    realProd θ V (Function.update g τ₀ g') = atTau θ V τ₀ g' * realProd θ V (Function.update g τ₀ 1) := by
  classical
  have h1 := update_mem hg τ₀ hg'
  have h2 := update_mem hg τ₀ (GlobalTheory.PointAtPlaceHom.one_mem_UH (gramAt D V τ₀))
  unfold realProd
  rw [dif_pos ⟨hθ, h1⟩, dif_pos ⟨hθ, h2⟩, ← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ τ₀),
    ← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ τ₀) (fun τ => atTau θ V τ (Function.update g τ₀ 1 τ))]
  simp only [Function.update_self, GlobalTheory.PointAtPlaceHom.atTau_one hθ, one_mul]
  congr 1
  refine Finset.noncommProd_congr rfl (fun τ hτ => ?_) _
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ), Function.update_of_ne (Finset.ne_of_mem_erase hτ)]

theorem realProd_commute (hθ : IsInfFam θ) {g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (τ₀ : D.what₂.Tau) {g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ₀)) :
    Commute (atTau θ V τ₀ g') (realProd θ V (Function.update g τ₀ 1)) := by
  classical
  have h2 := update_mem hg τ₀ (GlobalTheory.PointAtPlaceHom.one_mem_UH (gramAt D V τ₀))
  unfold realProd
  rw [dif_pos ⟨hθ, h2⟩]
  refine Finset.noncommProd_commute _ _ _ _ fun τ _ => ?_
  by_cases h : τ = τ₀
  · subst h
    rw [Function.update_self, GlobalTheory.PointAtPlaceHom.atTau_one hθ]
    exact Commute.one_right _
  · exact GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ V τ₀ τ (Ne.symm h) _ hg' _ (h2 τ)

theorem realProd_one (hθ : IsInfFam θ) : realProd θ V (fun _ => 1) = 1 := by
  unfold realProd
  rw [dif_pos ⟨hθ, fun τ => GlobalTheory.PointAtPlaceHom.one_mem_UH _⟩]
  rw [Finset.noncommProd_eq_pow_card _ _ _ 1 fun τ _ => GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ, one_pow]

theorem isAutFunSm_realProd (hθ : IsInfFam θ) (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    {φ : GA D V → ℂ} (hφ : IsAutFunSm θ V φ) : IsAutFunSm θ V (rTr V (realProd θ V g) φ) := by
  unfold realProd
  split_ifs with h
  · refine Finset.noncommProd_induction _ _ _ (fun x => ∀ ψ, IsAutFunSm θ V ψ → IsAutFunSm θ V (rTr V x ψ))
      (fun a b ha hb ψ hψ => ?_) (fun ψ hψ => ?_) (fun τ _ ψ hψ => ?_) φ hφ
    · have e : rTr V (a * b) ψ = rTr V a (rTr V b ψ) := funext fun x => by simp only [rTr, mul_assoc]
      rw [e]; exact ha _ (hb _ hψ)
    · have e : rTr V 1 ψ = ψ := funext fun x => by simp only [rTr, mul_one]
      rw [e]; exact hψ
    · exact GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau D θ hθ V ψ hψ τ _ (h.2 τ)
  · have e : rTr V 1 φ = φ := funext fun x => by simp only [rTr, mul_one]
    rw [e]; exact hφ

theorem rep_mul {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) {g h : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hh : h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    M.rep τ (g * h) = (M.rep τ g).comp (M.rep τ h) := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  have e : M.fr τ * (g * h) * (M.fr τ)⁻¹ = (M.fr τ * g * (M.fr τ)⁻¹) * (M.fr τ * h * (M.fr τ)⁻¹) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (M.fr τ)⁻¹ (M.fr τ), Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  unfold DSModel.rep
  rw [e]
  exact (M.ds τ).2.2.1.1.2 _ (GlobalTheory.Published.HermitianUnique.frame_mem (M.fr_unit τ) (M.fr_gram τ) (M.fr_gram τ) hg) _
    (GlobalTheory.Published.HermitianUnique.frame_mem (M.fr_unit τ) (M.fr_gram τ) (M.fr_gram τ) hh)

theorem rep_one {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) : M.rep τ 1 = 1 := by
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  unfold DSModel.rep
  rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hd]
  exact (M.ds τ).2.2.1.1.1

theorem sm_eq_top {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) [FiniteDimensional ℂ (M.H τ)] :
    M.sm τ = ⊤ := by
  rw [GlobalTheory.SmVec.sm_eq]
  refine Submodule.orthogonal_eq_bot_iff.1 ((Submodule.eq_bot_iff _).2 fun y hy => ?_)
  exact GlobalTheory.SmVec.eq_zero_of_inner_smooth (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1
    fun u hu => (Submodule.mem_orthogonal _ _).1 hy u hu

theorem equiv_one {H G : Type} [AddCommGroup H] [Module ℂ H] [Module.Free ℂ H] [Module.Finite ℂ H] [Mul G]
    (K : Set G) (ρ : G → (H →ₗ[ℂ] H)) (hρ : ∀ g ∈ K, ∀ h ∈ K, ρ (g * h) = ρ g ∘ₗ ρ h)
    {m : ℕ} (k : Fin m → G) (hk : ∀ j, k j ∈ K) (B : Fin m → (H →ₗ[ℂ] H))
    (hB : ∀ i, ∀ h ∈ K, B i ∘ₗ ρ h = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) • B j)
    (f : G → ℂ) (hf : ∀ g ∈ K, f g = ∑ j, f (k j) * LinearMap.trace ℂ H (ρ g ∘ₗ B j))
    (hmul : ∀ g ∈ K, ∀ h ∈ K, g * h ∈ K) (e : H →ₗ[ℂ] ℂ) (v : H) {h : G} (hh : h ∈ K) :
    ∑ j, e (B j (ρ h v)) * f (k j) = ∑ j, e (B j v) * f (h * k j) := by
  have e1 : ∀ j, f (h * k j) = ∑ i, f (k i) * LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) := by
    intro j
    rw [hf _ (hmul _ hh _ (hk j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hρ _ hh _ (hk j), LinearMap.comp_assoc, LinearMap.trace_comp_comm', LinearMap.comp_assoc]
  have e2 : ∀ i, e (B i (ρ h v)) = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) * e (B j v) := by
    intro i
    have := congrArg (fun L : H →ₗ[ℂ] H => e (L v)) (hB i h hh)
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      map_smul, smul_eq_mul] at this
    exact this
  simp only [e1, e2, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.DefiniteDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspFunOfApprox
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ThLiftCusp

theorem isCuspFun_of_approx {D : D7} (V : HSp D) (f : GA D V → ℂ) (hf : Continuous f)
    (hl : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) (N : ℕ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ ψ : GA D V → ℂ, Continuous ψ ∧ (∀ γ ∈ GQ V, ∀ g, ψ (γ * g) = ψ g) ∧ IsCuspFun V ψ ∧
      ∀ g, ‖ψ g - f g‖ ≤ ε * GlobalTheory.Grow.height V g ^ N) : IsCuspFun V f := by
  choose ψ hψ using fun n : ℕ => h (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
  refine GlobalTheory.CuspLimit.isCuspFun_of_tendsto D V N ψ f (fun n => ⟨(hψ n).1, (hψ n).2.1, (hψ n).2.2.1⟩) hf hl ?_
  have hb : ∀ n : ℕ, GlobalTheory.Size.growthSize V N (ψ n - f) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := fun n =>
    (GlobalTheory.Size.growthSize_le_iff Nat.one_div_pos_of_nat.le).2 fun g => by simpa using (hψ n).2.2.2 g
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => zero_le) hb
  simpa using (ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat)

end GlobalTheory.ThLiftCusp

namespace GlobalTheory.ThLiftCusp

theorem norm_lift_sub_le {X H : Type} [MeasurableSpace X] (μ : Measure X) (K K' : H → X → ℂ) (φ φ' : X → ℂ)
    (u : H → ℝ) (w : X → ℝ) (C e δ : ℝ) (hC : 0 ≤ C) (he : 0 ≤ e) (hu : ∀ h, 0 ≤ u h)
    (hK : ∀ h x, ‖K h x‖ ≤ C * u h * w x) (hKK : ∀ h x, ‖K' h x - K h x‖ ≤ e * u h * w x)
    (h1 : Integrable (fun x => w x * ‖φ x‖) μ) (h2 : Integrable (fun x => w x * ‖φ' x - φ x‖) μ)
    (hδ : ∫ x, w x * ‖φ' x - φ x‖ ∂μ ≤ δ)
    (hA : ∀ h, Integrable (fun x => K' h x * φ' x) μ) (hB : ∀ h, Integrable (fun x => K h x * φ x) μ) (h : H) :
    ‖∫ x, K' h x * φ' x ∂μ - ∫ x, K h x * φ x ∂μ‖ ≤ u h * (e * ∫ x, w x * ‖φ x‖ ∂μ + (e + C) * δ) := by
  rw [← integral_sub (hA h) (hB h)]
  have hpt : ∀ x, ‖K' h x * φ' x - K h x * φ x‖ ≤
      u h * (e * (w x * ‖φ x‖) + (e + C) * (w x * ‖φ' x - φ x‖)) := fun x => by
    have e1 : K' h x * φ' x - K h x * φ x =
        (K' h x - K h x) * φ x + (K' h x - K h x) * (φ' x - φ x) + K h x * (φ' x - φ x) := by ring
    rw [e1]
    refine (norm_add₃_le).trans ?_
    rw [norm_mul, norm_mul, norm_mul]
    have a1 := mul_le_mul_of_nonneg_right (hKK h x) (norm_nonneg (φ x))
    have a2 := mul_le_mul_of_nonneg_right (hKK h x) (norm_nonneg (φ' x - φ x))
    have a3 := mul_le_mul_of_nonneg_right (hK h x) (norm_nonneg (φ' x - φ x))
    nlinarith
  have hint : Integrable (fun x => u h * (e * (w x * ‖φ x‖) + (e + C) * (w x * ‖φ' x - φ x‖))) μ :=
    ((h1.const_mul e).add (h2.const_mul (e + C))).const_mul (u h)
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) hint
    (Filter.Eventually.of_forall hpt)).trans ?_
  rw [integral_const_mul, integral_add (h1.const_mul e) (h2.const_mul (e + C)), integral_const_mul,
    integral_const_mul]
  exact mul_le_mul_of_nonneg_left (by nlinarith) (hu h)

end GlobalTheory.ThLiftCusp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPrimFrameGlMulIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

namespace GlobalTheory.PrimFrameLeft

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D]

theorem row_mul_eq_sum (M : Matrix A A k) (Y : Matrix A D k) (i : A) :
    (M * Y).row i = ∑ l, M i l • Y.row l := by
  funext j
  simp [Matrix.mul_apply, Finset.sum_apply, Matrix.row]

theorem span_O_row_mul_le (M : Matrix A A k) (hM : ∀ i j, M i j ∈ 𝒪[k]) (Y : Matrix A D k) :
    Submodule.span 𝒪[k] (Set.range (M * Y).row) ≤ Submodule.span 𝒪[k] (Set.range Y.row) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [row_mul_eq_sum]
  exact Submodule.sum_mem _ fun l _ =>
    Submodule.smul_mem _ (⟨M i l, hM i l⟩ : 𝒪[k]) (Submodule.subset_span ⟨l, rfl⟩)

theorem span_k_row_mul_le (M : Matrix A A k) (Y : Matrix A D k) :
    Submodule.span k (Set.range (M * Y).row) ≤ Submodule.span k (Set.range Y.row) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [row_mul_eq_sum]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

theorem span_O_row_gl_mul (g : GL A k) (hg : g ∈ KO k A) (Y : Matrix A D k) :
    Submodule.span 𝒪[k] (Set.range (g.val * Y).row) = Submodule.span 𝒪[k] (Set.range Y.row) := by
  obtain ⟨h1, h2⟩ := (mem_KO_iff g).1 hg
  refine le_antisymm (span_O_row_mul_le _ h1 Y) ?_
  have := span_O_row_mul_le _ h2 (g.val * Y)
  rwa [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this

theorem span_k_row_gl_mul (g : GL A k) (Y : Matrix A D k) :
    Submodule.span k (Set.range (g.val * Y).row) = Submodule.span k (Set.range Y.row) := by
  refine le_antisymm (span_k_row_mul_le _ Y) ?_
  have := span_k_row_mul_le (g⁻¹).val (g.val * Y)
  rwa [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] at this

theorem mem_matLat_iff_span_le (Λ : Submodule 𝒪[k] (D → k)) (Y : Matrix A D k) :
    Y ∈ matLat A Λ ↔ Submodule.span 𝒪[k] (Set.range Y.row) ≤ Λ := by
  rw [Submodule.span_le, mem_matLat]
  exact ⟨fun h => by rintro _ ⟨i, rfl⟩; exact h i, fun h i => h ⟨i, rfl⟩⟩

theorem isPrimFrame_gl_mul_iff (Λ : Submodule 𝒪[k] (D → k)) (g : GL A k) (hg : g ∈ KO k A)
    (Y : Matrix A D k) : IsPrimFrame Λ (g.val * Y) ↔ IsPrimFrame Λ Y := by
  have hrank : (g.val * Y).rank = Y.rank :=
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
  unfold IsPrimFrame
  rw [hrank, mem_matLat_iff_span_le, mem_matLat_iff_span_le, span_O_row_gl_mul g hg, span_k_row_gl_mul]

end GlobalTheory.PrimFrameLeft
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteDecompositionAssembleRealPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFiniteDecomposition_assemble_realPlaces : ∀ (D : D7) (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (𝒞 : Set (GA D N.V → ℂ)) (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop), (∀ f ∈ 𝒞, Continuous f) → (∀ τ, GlobalTheory.KFinDecomp.DecompAt θ N 𝒞 Ty τ) → ∀ ψ ∈ 𝒞, (∀ τ, Ty τ ψ) → ∃ (n : ℕ) (T₀ : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap N.M) (u : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M), (∀ j v, T₀ j v ∈ 𝒞) ∧ (∀ j, ∀ τ, ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ), (w : N.M.H τ) = N.M.rep τ k (v τ) → T₀ j (Function.update v τ w) = rTr N.V (atTau θ N.V τ k) (T₀ j v)) ∧ (∀ j, ∀ τ, ∀ X ∈ lieAt N.V τ, ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ), (w : N.M.H τ) = dRep (N.M.rep τ) X (v τ) → T₀ j (Function.update v τ w) = Rder θ N.V τ X (T₀ j v)) ∧ ψ = ∑ j, T₀ j (u j) := by
  first | exact @GlobalTheory.KFinDecomp.assemble_places | exact GlobalTheory.KFinDecomp.assemble_places | (intros; apply GlobalTheory.KFinDecomp.assemble_places <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KTypeClassAddMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace

noncomputable section
namespace GlobalTheory.KFinDecomp

theorem cls_add : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → GlobalTheory.FunPr.Hypotheses₂ → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (f f' : GA D N.V → ℂ), f ∈ Cls θ N U → f' ∈ Cls θ N U → f + f' ∈ Cls θ N U := by
  intro D θ hθ hPr N U f f' hf hf'
  obtain ⟨⟨a1, a2, a3⟩, a4⟩ := hf
  obtain ⟨⟨b1, b2, b3⟩, b4⟩ := hf'
  refine ⟨⟨GlobalTheory.Mem.AutSpace.isAutFunSm_add a1 b1, GlobalTheory.MultMem.isCuspFun_add a1.toIsAutFun b1.toIsAutFun a2 b2,
    fun τ => GlobalTheory.CuspGKForms.isTypeAt_add hPr hθ a1 b1 (a3 τ) (b3 τ)⟩, fun k hk hkf g => ?_⟩
  simp only [Pi.add_apply, a4 k hk hkf g, b4 k hk hkf g]

end GlobalTheory.KFinDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftCast
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowReal

theorem left_cast {D : D7} {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)} (X : LSp D) (h : X = ⟨D.sp.X', Λ⟩)
    (φ : GA D D.sp.X' → ℂ) (hφ : ∀ γ ∈ GQ D.sp.X', ∀ g, φ (γ * g) = φ g) :
    ∀ γ ∈ GQ X.sp, ∀ g, φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) (γ * g)) =
      φ (cast (congrArg (fun X : LSp D => GA D X.sp) h) g) := by
  subst h
  exact hφ

theorem gen_left : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch =>
    (∀ a ξ, ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g,
      pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) (γ * g) =
        pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) g) ∧
    ∀ t y η, ∀ γ ∈ GQ (ch.G.V (.grid 0 D.R.m)), ∀ g, formGen ch t y η (γ * g) = formGen ch t y η g := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch _ => ?_⟩⟩
  refine ⟨fun a ξ γ hγ g => GlobalTheory.RowBplus.pairVec_left ch.G ch.W.θ ξ (col_mem ch a) hγ g, fun t y η => ?_⟩
  have hm := hS.core.models
  exact left_cast (columnBlock R.toLevCh D.R.m) (colY_m R.toLevCh) (fun g => η (R.cX.ext ((R.HX t).e y) g))
    (fun γ hγ g => congrArg η
      (GlobalTheory.ThetaProjEquiv.ext_left R.cX ((R.HX t).e y) _ _ ((hm.HX t).2.1.le ⟨y, rfl⟩) γ hγ g))

end GlobalTheory.RowReal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGridPairWeilLatticeIffStandardOfHalfStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_gridPairWeilLattice_iff_standard_of_half : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ) (t : T) (p : Pair T), DefPair D.R.m p → ∀ (e : AE D), IsIdemSum e (locPl G t) → ∀ x : WO (G.pS p) (G.pT p), IsHalf e x → (x ∈ pairLat G p ↔ x ∈ latO (G.pS p) (G.pT p) (S.N.latS p : Set (Fin (G.pS p).rank → D.host.E)) (S.N.latT p : Set (Fin (G.pT p).rank → D.host.E)) fun _ => True) := by
  first | exact @GlobalTheory.StdHalfLat.mem_pairLat_iff_std | exact GlobalTheory.StdHalfLat.mem_pairLat_iff_std | (intros; apply GlobalTheory.StdHalfLat.mem_pairLat_iff_std <;> assumption)
end

