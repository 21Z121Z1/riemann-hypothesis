import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0350
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0382

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLeftIntertwinesHeisenbergDerivative
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.HeisOrbit

namespace GlobalTheory.HeisOrbit

theorem weil_heisDeriv_intertw_left {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (χX χW : Chr F E) (om : Rep σ X W) (hψ : IsStd ψ) (hW : M.IsWeil ψ χX χW om) (g : UA σ X.J)
    (Tg : SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d))
    (hTg : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, 1)) f (Tg f)) (u : Matrix (Fin n) (Fin d) (AE F E))
    (hu : At (evI F) u) (f f₁ : SInf F (Fin n × Fin d)) (hf : ActsD (evI F) (M.heisLine ψ u) f f₁) (y) :
    Tg f₁ y = GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co (mat g * u)).1
      (GlobalTheory.HeisOrbit.archCo M.co (mat g * u)).2 (Tg f) y := by
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ (incM F X.J) (incM F W.J) M.co hψ
  have hS := hW.isUSplitting
  have laws := GlobalTheory.RealLift.actsLaws F (Fin n × Fin d)
  have h1 : f₁ = D u f := by
    have hAD : ActsD (evI F) (M.heisLine ψ u) f (D u f) :=
      (laws f (D u f) (D u f)).1 (M.heisLine ψ u) (fun t => by funext x; simp [Model.heisLine, Darboux.rho, schr])
        (hD u hu f).1
    exact (laws f f₁ (D u f)).2.2.1 _ hf hAD
  have h2 : ∀ (f' : SInf F (Fin n × Fin d)) (g' : (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ), g' ∈ SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) →
      om (g, 1) (pureA F f' g') = pureA F (Tg f') g' := by
    intro f' g' hg
    have hr : Rest (evI F) (⇑f') (fun x => g' (fun i => (x i).2)) := by
      refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨f', g', hg, rfl⟩⟩
      show g' _ = g' _
      congr 1
      funext i
      show (x i).2 + (z i).2 = (x i).2
      rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz, add_zero]
    exact hTg f' _ hr
  set g₀ : (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ := (GlobalTheory.RealLift.intPts F (Fin n × Fin d)).indicator 1 with hg₀def
  have hg₀ : g₀ ∈ SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) := GlobalTheory.RealLift.indicator_intPts_mem_SB
  have hg₀0 : g₀ 0 = 1 := by rw [hg₀def, Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts]; rfl
  set x₀ := GlobalTheory.RealLift.ptAt y (0 : Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) with hx₀
  set u' := mat g * u with hu'def
  have hu' : At (evI F) u' := fun a ha => by rw [hu'def, ← Matrix.mul_smul, hu a ha, Matrix.mul_zero]
  have hl := GlobalTheory.RealLift.eval_mem_adm (F := F) x₀
  have hl' := hS.adm (g, 1) _ hl
  have dA := (hD u hu f).1 g₀ hg₀ _ hl'
  have dB := (hD u' hu' (Tg f)).1 g₀ hg₀ _ hl
  have hfun : (fun t : ℝ => (LinearMap.proj x₀ ∘ₗ om (g, 1)) (M.co.rho ψ (realAd F t • u) (pureA F f g₀))) =
      fun t : ℝ => (LinearMap.proj x₀ : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ)
        (M.co.rho ψ (realAd F t • u') (pureA F (Tg f) g₀)) := by
    funext t
    rw [LinearMap.comp_apply, hS.impl (g, 1) _ _ (Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩), h2 f g₀ hg₀]
    congr 3
    simp [actAB, hu'def, mat, Matrix.mul_smul]
  rw [hfun] at dA
  have e := dA.unique dB
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, h2 _ g₀ hg₀, hx₀, GlobalTheory.RealLift.pureA_ptAt, hg₀0,
    mul_one] at e
  rw [h1, e, (hD u' hu' (Tg f)).2]
  rfl

end GlobalTheory.HeisOrbit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorRightIntertwinesHeisenbergDerivative
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit

namespace GlobalTheory.HeisOrbit

open GlobalTheory.WeilM

theorem weil_heisDeriv_intertw {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (χX χW : Chr F E) (om : Rep σ X W) (hψ : IsStd ψ) (hW : M.IsWeil ψ χX χW om) (h : UA σ W.J)
    (Th : SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d))
    (hTh : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) f (Th f)) (u : Matrix (Fin n) (Fin d) (AE F E))
    (hu : At (evI F) u) (f f₁ : SInf F (Fin n × Fin d)) (hf : ActsD (evI F) (M.heisLine ψ u) f f₁) (y) :
    Th f₁ y = GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co (u * (mat h)ᵀ)).1
      (GlobalTheory.HeisOrbit.archCo M.co (u * (mat h)ᵀ)).2 (Th f) y := by
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ (incM F X.J) (incM F W.J) M.co hψ
  have hS := hW.isUSplitting
  have laws := GlobalTheory.RealLift.actsLaws F (Fin n × Fin d)

  have h1 : f₁ = D u f := by
    have hAD : ActsD (evI F) (M.heisLine ψ u) f (D u f) :=
      (laws f (D u f) (D u f)).1 (M.heisLine ψ u) (fun t => by funext x; simp [Model.heisLine, Darboux.rho, schr])
        (hD u hu f).1
    exact (laws f f₁ (D u f)).2.2.1 _ hf hAD

  have h2 : ∀ (f' : SInf F (Fin n × Fin d)) (g : (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ), g ∈ SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) →
      om (1, h) (pureA F f' g) = pureA F (Th f') g := by
    intro f' g hg
    have hr : Rest (evI F) (⇑f') (fun x => g (fun i => (x i).2)) := by
      refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨f', g, hg, rfl⟩⟩
      show g _ = g _
      congr 1
      funext i
      show (x i).2 + (z i).2 = (x i).2
      rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz, add_zero]
    exact hTh f' _ hr

  set g₀ : (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ := (GlobalTheory.RealLift.intPts F (Fin n × Fin d)).indicator 1 with hg₀def
  have hg₀ : g₀ ∈ SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) := GlobalTheory.RealLift.indicator_intPts_mem_SB
  have hg₀0 : g₀ 0 = 1 := by rw [hg₀def, Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts]; rfl
  set x₀ := GlobalTheory.RealLift.ptAt y (0 : Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) with hx₀
  set u' := u * (mat h)ᵀ with hu'def
  have hu' : At (evI F) u' := fun a ha => by rw [hu'def, ← Matrix.smul_mul, hu a ha, Matrix.zero_mul]
  have hl := GlobalTheory.RealLift.eval_mem_adm (F := F) x₀
  have hl' := hS.adm (1, h) _ hl
  have dA := (hD u hu f).1 g₀ hg₀ _ hl'
  have dB := (hD u' hu' (Th f)).1 g₀ hg₀ _ hl
  have hfun : (fun t : ℝ => (LinearMap.proj x₀ ∘ₗ om (1, h)) (M.co.rho ψ (realAd F t • u) (pureA F f g₀))) =
      fun t : ℝ => (LinearMap.proj x₀ : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ)
        (M.co.rho ψ (realAd F t • u') (pureA F (Th f) g₀)) := by
    funext t
    rw [LinearMap.comp_apply, hS.impl (1, h) _ _ (Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩), h2 f g₀ hg₀]
    congr 3
    simp [actAB, hu'def, mat, Matrix.smul_mul]
  rw [hfun] at dA
  have e := dA.unique dB
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, h2 _ g₀ hg₀, hx₀, GlobalTheory.RealLift.pureA_ptAt, hg₀0,
    mul_one] at e
  rw [h1, e, (hD u' hu' (Th f)).2]
  rfl

end GlobalTheory.HeisOrbit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittExtensionSumMulMiddleCoordinate
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.BumpMix

variable {D : D7}

theorem witt_extension_sum_mul_middle_coordinate {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x a : Mx D T.rank ρ) (w₀ : WO S₀ T) :
    (d.extY T a + d.extX T x + d.ext0 T w₀) ⬝ d.j0 = w₀ := by
  simp only [HypDec.extX_apply, HypDec.extY_apply, HypDec.matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc, HypDec.pX_j0,
    HypDec.pY_j0, HypDec.p0_j0, Matrix.mul_one, Matrix.mul_zero, zero_add, add_zero]

theorem coord_jX {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x a : Mx D T.rank ρ) (w₀ : WO S₀ T) :
    (d.extY T a + d.extX T x + d.ext0 T w₀) ⬝ d.jX = x := by
  simp only [HypDec.extX_apply, HypDec.extY_apply, HypDec.matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc, HypDec.pX_jX,
    HypDec.pY_jX, HypDec.p0_jX, Matrix.mul_one, Matrix.mul_zero, zero_add, add_zero]

theorem coord_jY {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x a : Mx D T.rank ρ) (w₀ : WO S₀ T) :
    (d.extY T a + d.extX T x + d.ext0 T w₀) ⬝ d.jY = a := by
  simp only [HypDec.extX_apply, HypDec.extY_apply, HypDec.matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc, HypDec.pX_jY,
    HypDec.pY_jY, HypDec.p0_jY, Matrix.mul_one, Matrix.mul_zero, zero_add, add_zero]

theorem eq_coords {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (u : WO S T) :
    u = d.extX T (u ⬝ d.jX) + d.ext0 T (u ⬝ d.j0) + d.extY T (u ⬝ d.jY) :=
  ((d.coordS T).symm_apply_apply u).symm

theorem symplOH_Y_X {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x a : Mx D T.rank ρ) :
    symplOH S T (d.extY T a) (d.extX T x) = -trHalf D (pairS T x a) := by
  rw [symplOH_skew, d.symplOH_extX_extY]

def poinX (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (β : Mx D T.rank ρ → ℂ) (u : WO S T) : ℂ :=
  ∑' γ : Matrix (Fin T.rank) (Fin ρ) D.host.E,
    ψ (trHalf D (pairS T (u ⬝ d.jX + 2 • rat γ) (u ⬝ d.jY))) * β (u ⬝ d.jX + rat γ)

theorem poinX_coords (ψ : AddChar (AF D.host.F) ℂ) {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (β : Mx D T.rank ρ → ℂ) (x a : Mx D T.rank ρ) (w₀ : WO S₀ T) :
    poinX ψ d T β (d.extY T a + d.extX T x + d.ext0 T w₀) =
      ∑' γ : Matrix (Fin T.rank) (Fin ρ) D.host.E, ψ (trHalf D (pairS T (x + 2 • rat γ) a)) * β (x + rat γ) := by
  simp only [poinX, coord_jX, coord_jY]

example (ψ : AddChar (AF D.host.F) ℂ) {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) :
    poinX ψ d T 0 = 0 := by
  funext u; simp [poinX]

end GlobalTheory.BumpMix

end
end

