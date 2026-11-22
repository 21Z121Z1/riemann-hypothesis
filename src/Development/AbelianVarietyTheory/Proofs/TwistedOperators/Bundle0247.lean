import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0225
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0183
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0224
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0243
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLeaf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0021
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0245
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompletionTensorAllRootsMapBijectiveCmStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll GlobalTheory.TrEll.RealTorus
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completionTensorAllRootsMap_bijective_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (w : InfinitePlace F) (τ : EmbOver E w), Function.Bijective (PsiAll P τ) := by
  first | exact @GlobalTheory.TrEll.RealTorus.PsiAll_bijective | exact GlobalTheory.TrEll.RealTorus.PsiAll_bijective | (intros; apply GlobalTheory.TrEll.RealTorus.PsiAll_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexDerivativeRightDerivativeCommutator
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DerBracket

open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem bracket_mem_lieAt {τ : D.what₂.Tau} {X Y : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (hY : Y ∈ lieAt V τ) : X * Y - Y * X ∈ lieAt V τ := by

  have hX0 : Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 := hX
  have hY0 : Yᴴ * gramAt D V τ + gramAt D V τ * Y = 0 := hY
  have hX' : Xᴴ * gramAt D V τ = -(gramAt D V τ * X) := eq_neg_of_add_eq_zero_left hX0
  have hY' : Yᴴ * gramAt D V τ = -(gramAt D V τ * Y) := eq_neg_of_add_eq_zero_left hY0
  have e1 : Yᴴ * Xᴴ * gramAt D V τ = gramAt D V τ * Y * X := by
    rw [Matrix.mul_assoc Yᴴ Xᴴ, hX', Matrix.mul_neg, ← Matrix.mul_assoc Yᴴ, hY', Matrix.neg_mul, neg_neg]
  have e2 : Xᴴ * Yᴴ * gramAt D V τ = gramAt D V τ * X * Y := by
    rw [Matrix.mul_assoc Xᴴ Yᴴ, hY', Matrix.mul_neg, ← Matrix.mul_assoc Xᴴ, hX', Matrix.neg_mul, neg_neg]
  show (X * Y - Y * X)ᴴ * gramAt D V τ + gramAt D V τ * (X * Y - Y * X) = 0
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, e1, e2]
  noncomm_ring

private theorem mem_smF_of_mem_smFun (R : GlobalTheory.SmoothForms.RealPoints θ V) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) :
    φ ∈ GlobalTheory.SmoothForms.SmF θ V :=
  (GlobalTheory.SmoothForms.isSmoothInf_iff φ).1 ((GlobalTheory.SmoothForms.smooth_iff R φ).1 hφ)

private theorem rder_eq_opInf_atPlace (R : GlobalTheory.SmoothForms.RealPoints θ V) (τ : D.what₂.Tau) (X : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ)
    (ψ : GlobalTheory.SmoothForms.SmF θ V) :
    Rder θ V τ X.1 ψ.1 = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ X) ψ).1 := by
  rw [GlobalTheory.SmoothForms.opInf_coe]
  exact GlobalTheory.SmoothForms.Rder_eq R τ X ψ.1

theorem Rder_bracket (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (hY : Y ∈ lieAt V τ) :
    Rder θ V τ X (Rder θ V τ Y φ) = Rder θ V τ Y (Rder θ V τ X φ) + Rder θ V τ (X * Y - Y * X) φ := by

  have R : GlobalTheory.SmoothForms.RealPoints θ V := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  have hXY := bracket_mem_lieAt hX hY
  set ψ : GlobalTheory.SmoothForms.SmF θ V := ⟨φ, mem_smF_of_mem_smFun R hφ⟩ with hψ
  set Xl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨X, (GlobalTheory.SmoothForms.mem_lieAt_iff τ X).1 hX⟩ with hXl
  set Yl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨Y, (GlobalTheory.SmoothForms.mem_lieAt_iff τ Y).1 hY⟩ with hYl
  set Zl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨X * Y - Y * X, (GlobalTheory.SmoothForms.mem_lieAt_iff τ _).1 hXY⟩ with hZl
  have e := GlobalTheory.SmoothForms.opAt_bracket R τ Xl Yl Zl rfl
  have a1 : Rder θ V τ Y φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl) ψ).1 := rder_eq_opInf_atPlace R τ Yl ψ
  have a2 : Rder θ V τ X φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ).1 := rder_eq_opInf_atPlace R τ Xl ψ
  have a3 : Rder θ V τ X (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl) ψ).1 =
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl)
        (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl) ψ)).1 := rder_eq_opInf_atPlace R τ Xl _
  have a4 : Rder θ V τ Y (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ).1 =
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl)
        (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ)).1 := rder_eq_opInf_atPlace R τ Yl _
  have a5 : Rder θ V τ (X * Y - Y * X) φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Zl) ψ).1 :=
    rder_eq_opInf_atPlace R τ Zl ψ
  rw [a1, a3, a2, a4, a5, e, LinearMap.sub_apply, Submodule.coe_sub]
  change _ = _ + ((GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl)
        (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl) ψ)).1 -
      (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Yl)
        (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ)).1)
  abel

theorem Rder_comm (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) {τ τ' : D.what₂.Tau} (hτ : τ ≠ τ')
    {X Y : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (hY : Y ∈ lieAt V τ') :
    Rder θ V τ X (Rder θ V τ' Y φ) = Rder θ V τ' Y (Rder θ V τ X φ) := by

  have R : GlobalTheory.SmoothForms.RealPoints θ V := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  set ψ : GlobalTheory.SmoothForms.SmF θ V := ⟨φ, mem_smF_of_mem_smFun R hφ⟩ with hψ
  set Xl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ := ⟨X, (GlobalTheory.SmoothForms.mem_lieAt_iff τ X).1 hX⟩ with hXl
  set Yl : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.LieAt V τ' := ⟨Y, (GlobalTheory.SmoothForms.mem_lieAt_iff τ' Y).1 hY⟩ with hYl
  have hc := (GlobalTheory.SmoothForms.opAt_comm R hτ Xl Yl).eq
  have a1 : Rder θ V τ' Y φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ' Yl) ψ).1 := rder_eq_opInf_atPlace R τ' Yl ψ
  have a2 : Rder θ V τ X φ = (GlobalTheory.SmoothForms.opInf R (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.atPlace V τ Xl) ψ).1 := rder_eq_opInf_atPlace R τ Xl ψ
  rw [a1, a2, rder_eq_opInf_atPlace R τ Xl, rder_eq_opInf_atPlace R τ' Yl]
  exact congrArg Subtype.val (LinearMap.congr_fun hc ψ)

private theorem commutator_add_I_smul' {n : ℕ} (A B X : Matrix (Fin n) (Fin n) ℂ) :
    (A + Complex.I • B) * X - X * (A + Complex.I • B) = (A * X - X * A) + Complex.I • (B * X - X * B) := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
  abel

theorem RderC_Rder : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ τ' : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ), ∀ X ∈ lieAt V τ, ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, (RderC θ V τ Z (Rder θ V τ X φ) = Rder θ V τ X (RderC θ V τ Z φ) + RderC θ V τ (Z * X - X * Z) φ) ∧ (τ' ≠ τ → RderC θ V τ' Z (Rder θ V τ X φ) = Rder θ V τ X (RderC θ V τ' Z φ)) := by
  intro D θ hθ V τ τ' Z X hX φ hφ
  constructor
  ·
    obtain ⟨hA, hB⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
    have hZ := GlobalTheory.SmoothAutCheck.parts_sum V τ Z
    set A := (1 / 2 : ℂ) • (Z + conjAt V τ Z) with hAdef
    set B := (1 / (2 * Complex.I)) • (Z - conjAt V τ Z) with hBdef
    have hc := commutator_add_I_smul' A B X
    rw [hZ] at hc
    have hAX := bracket_mem_lieAt hA hX
    have hBX := bracket_mem_lieAt hB hX
    have e1 : RderC θ V τ (Z * X - X * Z) φ =
        Rder θ V τ (A * X - X * A) φ + Complex.I • Rder θ V τ (B * X - X * B) φ := by
      rw [hc, GlobalTheory.Mem.RealTranslate.RderC_add hθ hφ, GlobalTheory.Mem.RealTranslate.RderC_smul hθ hφ,
        GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hAX, GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hBX]
    rw [e1]
    show Rder θ V τ A (Rder θ V τ X φ) + Complex.I • Rder θ V τ B (Rder θ V τ X φ) =
      Rder θ V τ X (Rder θ V τ A φ + Complex.I • Rder θ V τ B φ) + _
    rw [Rder_bracket hθ hφ hA hX, Rder_bracket hθ hφ hB hX,
      Rder_add (Rder_mem hφ hA) ((SmFun θ V).smul_mem _ (Rder_mem hφ hB)) hX, Rder_smul]
    rw [smul_add]
    abel
  ·
    intro hne
    obtain ⟨hA, hB⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ' Z
    show Rder θ V τ' ((1 / 2 : ℂ) • (Z + conjAt V τ' Z)) (Rder θ V τ X φ) +
        Complex.I • Rder θ V τ' ((1 / (2 * Complex.I)) • (Z - conjAt V τ' Z)) (Rder θ V τ X φ) =
      Rder θ V τ X (Rder θ V τ' ((1 / 2 : ℂ) • (Z + conjAt V τ' Z)) φ +
        Complex.I • Rder θ V τ' ((1 / (2 * Complex.I)) • (Z - conjAt V τ' Z)) φ)
    rw [Rder_add (Rder_mem hφ hA) ((SmFun θ V).smul_mem _ (Rder_mem hφ hB)) hX, Rder_smul,
      Rder_comm hθ hφ hne hA hX, Rder_comm hθ hφ hne hB hX]

end GlobalTheory.DerBracket

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjFormsSpherical
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjSph

open GlobalTheory.Hk3

variable {D : D7} {V : HSp D} {P : Pl D.host.E}

theorem adForms_iff {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* G)
    (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (F : G → W) :
    F ∈ Bridge.AdForms ι ρ J χ ↔
      (∀ h (k : J), F (h * k) = ((χ k : ℂˣ) : ℂ) • F h) ∧ ∀ γ h, F (ι γ * h) = ρ γ (F h) := by
  change (∀ (γ : Γ) (h : G) (k : J), F (ι γ * h * k) = ((χ k : ℂˣ) : ℂ) • ρ γ (F h)) ↔ _
  constructor
  · intro hF
    refine ⟨fun h k => ?_, fun γ h => ?_⟩
    · simpa using hF 1 h k
    · simpa using hF γ h 1
  · rintro ⟨hR, hL⟩ γ h k
    rw [hR, hL]

def hkG {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (φ : GA D V →* G) (P : Pl D.host.E) (c : List ℤ →₀ ℂ)
    (F : G → W) : G → W :=
  fun h => c.sum fun d z => z • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (h * φ γ)

theorem dual_hkG {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (φ : GA D V →* G) (l : W →ₗ[ℂ] ℂ) (c : List ℤ →₀ ℂ)
    (F : G → W) (x : GA D V) : l (hkG φ P c F (φ x)) = hk V P c (fun y => l (F (φ y))) x := by
  rw [GlobalTheory.LevOp.hk_apply]
  show l (c.sum fun d z => z • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (φ x * φ γ)) = _
  rw [map_finsuppSum, Finsupp.sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_smul, map_sum, smul_eq_mul]
  congr 1
  show _ = ∑ γ ∈ GlobalTheory.Hk3.rep V P d, l (F (φ (x * γ)))
  simp only [map_mul]

theorem hkG_left {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (φ : GA D V →* G) (c : List ℤ →₀ ℂ)
    (F : G → W) (g : G) (T : W →ₗ[ℂ] W) (hF : ∀ h, F (g * h) = T (F h)) (h : G) :
    hkG φ P c F (g * h) = T (hkG φ P c F h) := by
  show (c.sum fun d z => z • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (g * h * φ γ)) =
    T (c.sum fun d z => z • ∑ γ ∈ GlobalTheory.Hk3.rep V P d, F (h * φ γ))
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun d _ => ?_
  rw [map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [mul_assoc, hF]

theorem hkG_right {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (φ : GA D V →* G) (hφ : Function.Surjective φ)
    {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {J : Subgroup (GA D V)}
    (hJ : ∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅)) (c : List ℤ →₀ ℂ) (F : G → W)
    (hF : ∀ k ∈ hyp V P, ∀ h, F (h * φ k) = F h) {k₁ k₂ : GA D V} (hk₁ : k₁ ∈ J)
    (s₁ : SuppF V f k₁) (s₂ : SuppF V (1 - f) k₂) (z : ℂ) (hz : ∀ h, F (h * φ (k₁ * k₂)) = z • F h) (h : G) :
    hkG φ P c F (h * φ (k₁ * k₂)) = z • hkG φ P c F h := by
  obtain ⟨x, rfl⟩ := hφ h
  rw [← map_mul φ x (k₁ * k₂), ← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, map_smul, dual_hkG, dual_hkG, sub_eq_zero, smul_eq_mul]
  have hinv : ∀ k ∈ hyp V P, ∀ y, (fun y => l (F (φ y))) (y * k) = (fun y => l (F (φ y))) y := by
    intro k hk y
    show l (F (φ (y * k))) = l (F (φ y))
    rw [map_mul, hF k hk]
  rw [GlobalTheory.LevOp.hk_translate hP hJ c hinv hk₁ s₁ s₂ x]
  have hsc : (fun y => (fun y => l (F (φ y))) (y * (k₁ * k₂))) = z • fun y => l (F (φ y)) := by
    funext y
    show l (F (φ (y * (k₁ * k₂)))) = z * l (F (φ y))
    rw [map_mul φ y (k₁ * k₂), hz, map_smul, smul_eq_mul]
  rw [hsc, map_smul]
  rfl

set_option maxHeartbeats 1000000 in

theorem adForms_spherical (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ)
    (L : LevDat D.host.E ℂ V.rank) (hB : IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hPP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ρ : GQ V →* Module.End ℂ W)
    (χ' : (levEnv V β L).J →* ℂˣ) (hχ' : ∀ k, (((levEnv V β L).χ k : ℂˣ) : ℂ) = 1 → ((χ' k : ℂˣ) : ℂ) = 1)
    {F : Bridge.Gf V → W} (hF : F ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J χ') (c : List ℤ →₀ ℂ) :
    (∀ k ∈ hyp V P, ∀ h, F (h * (finHom V).rangeRestrict k) = F h) ∧
      hkF V P c F ∈ Bridge.AdForms (Bridge.ratF V) ρ (levEnv V β L).J χ' := by
  obtain ⟨e, f, hP⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.1 P
  have hPf := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP
  obtain ⟨hJf, hχf, hsplit⟩ := (GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places V β Λ N (flag1L L) hB).2 P e f hP hN hPP
  have hFl := (adForms_iff (Bridge.ratF V) ρ (levEnv V β L).J χ' F).1 hF
  have hinv : ∀ k ∈ hyp V P, ∀ h, F (h * (finHom V).rangeRestrict k) = F h := by
    rintro k ⟨hkK, e', f', hP', hk⟩ h
    obtain ⟨-, rfl⟩ := hPf.2.2.2.1 e' f' hP'
    have hkJ : k ∈ levG V β (flag1L L) := (hJf k hk).2 hkK
    have hmem : (finHom V).rangeRestrict k ∈ (levEnv V β L).J :=
      (GlobalTheory.SplitHeckeAdj.mem_J V β L (hPf.2.2.1 k hk)).2 hkJ
    have h1 : (((levEnv V β L).χ ⟨_, hmem⟩ : ℂˣ) : ℂ) = 1 := by
      rw [GlobalTheory.SplitHeckeAdj.chi_eq V β L hmem]
      exact hχf k hkJ hk
    rw [hFl.1 h ⟨_, hmem⟩, hχ' _ h1, one_smul]
  refine ⟨hinv, (adForms_iff (Bridge.ratF V) ρ (levEnv V β L).J χ' _).2 ⟨fun h k => ?_, fun γ h => ?_⟩⟩
  · obtain ⟨g, hgG, hg⟩ := GlobalTheory.SplitHeckeAdj.fin_lift V (k : Bridge.Gf V)
    have hgJ : g ∈ levG V β (flag1L L) := by
      refine (GlobalTheory.SplitHeckeAdj.mem_J V β L hgG).1 ?_
      rw [hg]
      exact k.2
    obtain ⟨k₁, hk₁, k₂, -, s₁, s₂, rfl⟩ := hsplit g hgJ
    have hz : ∀ h', F (h' * (finHom V).rangeRestrict (k₁ * k₂)) = ((χ' k : ℂˣ) : ℂ) • F h' := by
      intro h'
      rw [show (finHom V).rangeRestrict (k₁ * k₂) = (k : Bridge.Gf V) from hg]
      exact hFl.1 h' k
    have key := hkG_right (P := P) (finHom V).rangeRestrict (MonoidHom.rangeRestrict_surjective _) hP
      (J := levG V β (flag1L L)) hJf c F hinv hk₁ s₁ s₂ _ hz h
    rw [show (finHom V).rangeRestrict (k₁ * k₂) = (k : Bridge.Gf V) from hg] at key
    exact key
  · exact hkG_left (P := P) (finHom V).rangeRestrict c F (Bridge.ratF V γ) (ρ γ) (hFl.2 γ) h

set_option maxHeartbeats 1000000 in

theorem conjForms_spherical : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), ∀ c₀, GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjForms R i σ c₀ c c₁ H j → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → ∀ cV (y : H.H), (∀ k ∈ GlobalTheory.Hk3.hyp (Vc D i) P, ∀ h, H.e y (h * (finHom _).rangeRestrict k) = H.e y h) ∧ ∃ y' : H.H, H.e y' = GlobalTheory.Hk3.hkF (Vc D i) P cV (H.e y) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hR i σ c c₁ H j c₀ hC P hG cV y
  obtain ⟨χ', hχc, hIs⟩ := hC.model
  obtain ⟨-, hrange, -⟩ := hIs
  have hSD : ∃ c, IsBaseFrame (Vc D i) (R.βV i) (R.ΛV i) (1 ^ c) := hR.βV i
  obtain ⟨n, hB⟩ := hSD
  have hN : (((1 ^ n : ℕ) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have htriv : ∀ k, (((levEnv (Vc D i) (R.βV i) (R.datVt i A.μ0)).χ k : ℂˣ) : ℂ) = 1 → ((χ' k : ℂˣ) : ℂ) = 1 := by
    intro k hk
    obtain ⟨a, ha, hb⟩ := hχc k
    have ha1 : a = 1 := D.what₂.embLL.injective (by rw [ha, hk, map_one])
    rw [← hb, ha1, map_one]
  have hPP : ∀ PP, PP ∈ (R.datVt i A.μ0).Pg ∨ PP ∈ (R.datVt i A.μ0).Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := hG
  have key := adForms_spherical (V := Vc D i) (P := P) (R.βV i) (R.ΛV i) (1 ^ n) (R.datVt i A.μ0) hB hN hPP c.coef.ρ χ' htriv (F := H.e y) (by
      have h0 := LinearMap.mem_range_self H.e y
      rw [hrange] at h0
      exact h0) cV
  have k1 : ∀ k ∈ GlobalTheory.Hk3.hyp (Vc D i) P, ∀ h, H.e y (h * (finHom (Vc D i)).rangeRestrict k) = H.e y h := by
    intro k hk h
    exact key.1 k hk h
  refine ⟨fun k hk h => Eq.trans ?_ (k1 k hk h), ?_⟩
  · congr! 2
  have h3 : GlobalTheory.Hk3.hkF (Vc D i) P cV (H.e y) ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (levJ R i A.μ0) χ' := key.2
  have h4 : GlobalTheory.Hk3.hkF (Vc D i) P cV (H.e y) ∈ LinearMap.range H.e := (SetLike.ext_iff.mp hrange _).mpr h3
  obtain ⟨y', hy'⟩ := h4
  exact ⟨y', hy'⟩

end GlobalTheory.ConjSph

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjFrameToRealLieAlgebraSpec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.ConjHol.ToLie

lemma conj_mem_sgn {n : ℕ} (d : Fin n → ℂ) (hd : ∀ a, star (d a) = d a)
    (A : Matrix (Fin n) (Fin n) ℂ) (h : Aᴴ * diagonal d + diagonal d * A = 0) :
    (A.map (starRingEnd ℂ))ᴴ * diagonal d + diagonal d * A.map (starRingEnd ℂ) = 0 := by
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply, Matrix.zero_apply,
    Matrix.conjTranspose_apply, Matrix.map_apply] at hij ⊢
  have := congrArg star hij
  simp only [star_add, star_mul', star_star, star_zero, hd] at this
  simpa [RCLike.star_def, add_comm, mul_comm] using this

end GlobalTheory.AdSpan.ConjHol.ToLie

open GlobalTheory.AdSpan.ConjHol GlobalTheory.HolRead.AdExt in
theorem GlobalTheory.AdSpan.ConjHol.ToLie.toLieC_spec : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas), C.IsB B → ∀ Z ∈ GlobalTheory.HolRead.unitLie C.X, (∀ ρ, (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z ρ).1 = B ρ * (mat Z (C.m.e ρ)).map (starRingEnd ℂ) * (B ρ)⁻¹) ∧ GlobalTheory.AdSpan.ConjHol.toLieC C R B (I • Z) = 0 := by
  intro D S T C R B hB Z hZ
  have hfix : ∀ ρ, conjAt T ρ (B ρ * (mat Z (C.m.e ρ)).map (starRingEnd ℂ) * (B ρ)⁻¹)
      = B ρ * (mat Z (C.m.e ρ)).map (starRingEnd ℂ) * (B ρ)⁻¹ := by
    intro ρ
    have hW := GlobalTheory.AdSpan.ConjHol.ToLie.conj_mem_sgn _ ?_ _ (hZ (C.m.e ρ))
    · have hB' : (B ρ)ᴴ * gramAt D T ρ * B ρ = diagonal fun (a : Fin T.rank) => ((sgn C.X.p0 (a : ℕ) : ℝ) : ℂ) := hB ρ
      have hL := conj_mem_lie (isUnit_det_B C hB ρ) hB' hW
      exact conj_eq_of_mem_lie (R.1 ρ).2 hL
    · intro a; simp
  refine ⟨fun ρ => ?_, ?_⟩
  · show ((HolRead.AdExt.toLie R B fun ρ => C.m.e ρ) (conjL Z) ρ).1 = _
    rw [toLie_val, mat_conjL, hfix ρ]
    module
  · funext ρ
    apply Subtype.ext
    show ((HolRead.AdExt.toLie R B fun ρ => C.m.e ρ) (conjL (I • Z)) ρ).1 = (0 : Matrix (Fin T.rank) (Fin T.rank) ℂ)
    have hc : conjL (I • Z) = I • (-(conjL Z)) := by
      funext τ a b
      simp [conjL]
    have hm : mat (-(conjL Z)) (C.m.e ρ) = -(mat (conjL Z) (C.m.e ρ)) := rfl
    have hneg : ∀ M : Matrix (Fin T.rank) (Fin T.rank) ℂ,
        conjAt T ρ (B ρ * -M * (B ρ)⁻¹) = -(conjAt T ρ (B ρ * M * (B ρ)⁻¹)) := by
      intro M; simp [conjAt]
    rw [hc, toLie_I, hm, hneg, mat_conjL, hfix ρ]
    simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjTranslatedRowEvaluationLevelProjectorFixed
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowEvalHH.LevelFix

theorem castGA_symm_mem {I I' : Formalism.MainNotions.S.AutInst} (p : I = I') (γ : I'.GA) (hγ : γ ∈ I'.GFset) :
    (castGA p).symm γ ∈ I.GFset := by
  subst p
  exact hγ

theorem iotaX_symm_rat {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (γ : X.B.I.GA) (hγ : γ ∈ X.B.I.GFset) : (iotaX X h).symm γ ∈ GQ (D.sp.Y 0) := by
  refine (Formalism.IndefR.RationalEmbedding.iota_rat D ((iotaX X h).symm γ)).2 ?_
  show Formalism.IndefR.RationalEmbedding.iota D ((Formalism.IndefR.RationalEmbedding.iota D).symm ((castGA h.symm).symm γ)) ∈ _
  rw [ContinuousMulEquiv.apply_symm_apply]
  exact castGA_symm_mem _ γ hγ

theorem mult_lev {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}
    {θ : D.what₂.Tau → TensorProduct (↥D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf ↥D.host.F) D.host.E →+* ℂ}
    {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M} (hT : T ∈ Mult θ M J χ) :
    ∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  induction hT using Submodule.span_induction with
  | mem x hx => exact hx.lev
  | zero => intro v k _ g; simp
  | add x y _ _ hx hy =>
    intro v k hk g
    simp only [MultilinearMap.add_apply, Pi.add_apply, hx v k hk g, hy v k hk g, mul_add]
  | smul a x _ hx =>
    intro v k hk g
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx v k hk g]
    ring

end GlobalTheory.RowEvalHH.LevelFix

open GlobalTheory.RowEvalHH GlobalTheory.RowEvalHH.LevelFix in

theorem GlobalTheory.RowEvalHH.Re_evF : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → LevelMatchA R F X h t → ∀ S ∈ EP R F, ∀ y : ∀ τ, ↥(GlobalTheory.RowEvalHH.Wsub R X c τ), X.B.Re (GlobalTheory.RowEvalHH.evF R X h t c S y) = GlobalTheory.RowEvalHH.evF R X h t c S y := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod hHost hιE t c ht hLM S hS y
  classical
  have hSM := Formalism.IndefR.Mult.goodPart_le _ _ _ _ _ hS
  have hcl := Formalism.IndefR.PeterssonHilbertSpace.mult_cont_left (MP R) R.θ _ _ hSM (vecOf R X c y)
  have hlev := mult_lev hSM (vecOf R X c y)
  let ιY : X.B.I.GA ≃* GA D (Yc D 0) := (iotaX X h).symm.toMulEquiv
  unfold evF
  by_cases hm : MemLp (fun x => ev (MP R) (vecOf R X c y) S
      (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) 2 (muX X)
  · rw [dif_pos hm]
    set f : X.B.I.GA → ℂ := fun x => ev (MP R) (vecOf R X c y) S
      (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t) with hf
    have hm0 : MemLp (fun x => star (f x)) 2 (muX X) := hm.star
    have eF : star (hm.toLp f) = hm0.toLp (fun x => star (f x)) := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_star (hm.toLp f), hm.coeFn_toLp, hm0.coeFn_toLp] with x a1 a2 a3
      rw [a1, a3, Pi.star_apply, a2]
    rw [eF]
    have hfY : ∀ x, f x = S (vecOf R X c y) (ιY x * t) := fun x => rfl
    have hinv : ∀ γ ∈ X.B.I.GFset, ∀ x, star (f (γ * x)) = star (f x) := by
      intro γ hγ x
      congr 1
      rw [hfY, hfY, map_mul, mul_assoc]
      exact hcl.2 _ (iotaX_symm_rat X h γ hγ) _
    have hmeas : Measurable fun x => star (f x) := by
      haveI : IsTopologicalGroup (GA D (D.sp.Y 0)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
      have : Continuous f := hcl.1.comp ((iotaX X h).symm.continuous.mul continuous_const)
      exact (continuous_star.comp this).measurable
    have hright : ∀ k ∈ X.K2, ∀ x, star (f (x * (1, k))) = X.chi2 k * star (f x) := by
      intro k hk x
      have ek : (kap X h t k : GA D (Yc D 0)) = t⁻¹ * ιY (1, k) * t := rfl
      have e2 : ιY (x * (1, k)) * t = (ιY x * t) * kap X h t k := by
        rw [ek, map_mul]
        simp only [mul_assoc, mul_inv_cancel_left]
      have h1 : f (x * (1, k)) = star (X.chi2 k) * f x := by
        have hl := hlev _ (hLM k hk).1 (ιY x * t)
        rw [(hLM k hk).2] at hl
        rw [hfY, hfY, e2]
        exact hl
      rw [h1, star_mul', star_star, mul_comm]
    have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
    have hKL := Formalism.L2.SG.Closed.level_subgroup_properties X
    have hKM : MeasurableSet X.K2 := (Formalism.L2.SG.PoincareInHH.Cut.level_subgroup_isClopen X hK hKL).isOpen.measurableSet
    have hfix : ∀ᵐ z ∂(X.B.I.muA X.B.μf), ∫ g, X.B.e g * star (f (z * (1, g))) ∂X.B.μf = star (f z) := by
      refine Filter.Eventually.of_forall fun z => ?_
      have hvol : (X.B.μf X.K2).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hKL.2.2.1.ne', hKL.2.2.2.ne⟩
      have hfun : (fun g => X.B.e g * star (f (z * (1, g)))) =
          X.K2.indicator (fun _ => star (f z) / ((X.B.μf X.K2).toReal : ℂ)) := by
        funext g
        rw [X.e_eq g]
        by_cases hg : g ∈ X.K2
        · have hg' : g ∈ Formalism.L2.SG.HidaSetting.K2set X.B.I X.B.g X.e0 X.z0 X.bw := hg
          rw [if_pos hg', Set.indicator_of_mem hg, hright g hg z]
          have hn : ‖X.chi2 g‖ = 1 := hK.2.2.2.2 g hg
          have hc : star (X.chi2 g) * X.chi2 g = 1 := by
            rw [RCLike.star_def, RCLike.conj_mul, hn]; simp
          show star (X.chi2 g) / ((X.B.μf X.K2).toReal : ℂ) * (X.chi2 g * star (f z)) =
            star (f z) / ((X.B.μf X.K2).toReal : ℂ)
          rw [div_mul_eq_mul_div, ← mul_assoc, hc, one_mul]
        · have hg' : g ∉ Formalism.L2.SG.HidaSetting.K2set X.B.I X.B.g X.e0 X.z0 X.bw := hg
          rw [if_neg hg', Set.indicator_of_notMem hg, zero_mul]
      rw [hfun, integral_indicator hKM, setIntegral_const]
      simp only [measureReal_def, Complex.real_smul]
      have hC : ((X.B.μf X.K2).toReal : ℂ) ≠ 0 := by exact_mod_cast hvol
      rw [mul_div_assoc', mul_div_cancel_left₀ _ hC]
    exact Formalism.L2.SG.Pf.idempotent_fixes_invariant_L2 X (fun x => star (f x)) hmeas hinv hm0 hfix
  · rw [dif_neg hm]
    have h0 : (star (0 : L2X X)) = 0 := (Formalism.L2.SG.RowDict.conjL (muX X)).map_zero
    rw [h0, map_zero]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateMaximalCompactMemParahoricLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_maximalCompact_mem_parahoricLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ k ∈ X.B.I.Kset, kap X h t k ∈ GfC (Yc D 0) ∧ finE (Yc D 0) (kap X h t k) ∈ Formalism.L2.DIV.parLev D.sp.cm (Yc D 0).gram (R.βY 0) (R.dat0 R.triv) := by
  first | exact @GlobalTheory.KapLevel.kap_mem_parLev | exact GlobalTheory.KapLevel.kap_mem_parLev | (intros; apply GlobalTheory.KapLevel.kap_mem_parLev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockFromSquareIntegrabilityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectors_overVacuum_isometry : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.VacuumFock D := by
  first | exact @GlobalTheory.VacuumFockLaws.vacuumFock_onObjects | exact GlobalTheory.VacuumFockLaws.vacuumFock_onObjects | (intros; apply GlobalTheory.VacuumFockLaws.vacuumFock_onObjects <;> assumption)
end

