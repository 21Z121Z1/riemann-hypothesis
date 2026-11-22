import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0358
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0324
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0350
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0228
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0357
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0277
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0315
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0327
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0351
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0328
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0326
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0320
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0339
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0348
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAbovePlaceOfTrivialUnits
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnrOverPlace

theorem unrAt_of_unramAt : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F),
    IsPlaceIdem D v ε → GlobalTheory.WeilParts.UnramAt ε χ → ∀ w : HeightOneSpectrum (𝓞 D.host.E),
    w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χ w := by
  intro D χ v ε hε hu w hw x hx
  obtain ⟨h1, h2⟩ := (GlobalTheory.LFun.EulerTie.isUnitAt_iff w x).1 hx
  have hc := GlobalTheory.LFun.EulerTie.comp_finComp (F := D.host.F) (E := D.host.E)
  obtain ⟨k0, k1, -⟩ := GlobalTheory.CMPrimeIdele.place_comp hc hε
  have key : χ (GlobalTheory.LFun.locIdele D.host.F w x) = 1 := by
    refine hu _ ?_ ((GlobalTheory.LFun.EulerTie.locIdele_int_iff w x).2 h1) (by
      rw [← map_inv]; exact (GlobalTheory.LFun.EulerTie.locIdele_int_iff w x⁻¹).2 h2)
    refine hc.ext' ?_ fun Q ↦ ?_
    · have k0' : GlobalTheory.CMPrimeIdele.infPart D.host.F D.host.E (algebraMap (AF D.host.F) (AE D) ε) = 0 := k0
      have k2 : GlobalTheory.CMPrimeIdele.infPart D.host.F D.host.E ((GlobalTheory.LFun.locIdele D.host.F w x : AE D) - 1) = 0 := by
        rw [map_sub, (GlobalTheory.LFun.EulerTie.parts_locIdele w x).1, map_one, sub_self]
      rw [map_mul, k0', zero_mul, k2]
    · rw [GlobalTheory.CMPrimeIdele.ev_mul]
      by_cases hQ : Q = w
      · subst hQ
        rw [k1 Q hw, one_mul]
      · have e : GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E ((GlobalTheory.LFun.locIdele D.host.F w x : AE D) - 1) Q = 0 := by
          rw [map_sub, map_one]
          show GlobalTheory.LFun.EulerTie.finComp D.host.F D.host.E (GlobalTheory.LFun.locIdele D.host.F w x : AE D) Q - 1 = 0
          rw [GlobalTheory.LFun.EulerTie.finComp_locIdele_ne hQ, sub_self]
        rw [e, mul_zero]
  show Circle.toUnits (χ (GlobalTheory.LFun.locIdele D.host.F w x)) = 1
  rw [key, map_one]

end GlobalTheory.UnrOverPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergArchimedeanDiffOperatorHasDerivAtFamil
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

noncomputable section

namespace GlobalTheory.HeisOrbit.DOpDeriv

theorem hasDerivAt_fderiv_family {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : ℝ × E → ℂ) (hH : ContDiff ℝ 2 H) (g : E → ℂ)
    (hg : ∀ y, HasDerivAt (fun t => H (t, y)) (g y) 0) (P : ℝ → E) (P' : E) (hP : HasDerivAt P P' 0) (y : E) :
    HasDerivAt (fun t => fderiv ℝ (fun z => H (t, z)) y (P t))
      (fderiv ℝ g y (P 0) + fderiv ℝ (fun z => H (0, z)) y P') 0 := by
  have hd : Differentiable ℝ H := hH.differentiable (by norm_num)
  have hd1 : Differentiable ℝ (fderiv ℝ H) :=
    (hH.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1 : ∀ (t : ℝ) (v : E), fderiv ℝ (fun z => H (t, z)) y v = fderiv ℝ H (t, y) (0, v) := by
    intro t v
    have := ((hd (t, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)).fderiv
    have e : (fun z => H (t, z)) = H ∘ (fun z => (t, z)) := rfl
    rw [e, this]
    simp
  have h2 : g = fun z => fderiv ℝ H (0, z) (1, 0) := by
    funext z
    have hc : HasDerivAt (fun t : ℝ => (t, z)) ((1 : ℝ), (0 : E)) 0 :=
      (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) z)
    have := (hd (0, z)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
    exact (hg z).unique this
  have h3 : ∀ v : E, fderiv ℝ g y v = fderiv ℝ (fderiv ℝ H) (0, y) (0, v) (1, 0) := by
    intro v
    have a := (hd1 (0, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right (0 : ℝ) y)
    have b := (a.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : E)) y)).fderiv
    have e : g = fun z => ((fderiv ℝ H) ∘ (fun z => ((0 : ℝ), z))) z (1, 0) := h2
    rw [e, b]
    simp
  have hs : IsSymmSndFDerivAt ℝ H (0, y) :=
    hH.contDiffAt.isSymmSndFDerivAt (by simp)
  have hc : HasDerivAt (fun t : ℝ => (t, y)) ((1 : ℝ), (0 : E)) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) y)
  have a := (hd1 (0, y)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
  have hQ : HasDerivAt (fun t : ℝ => ((0 : ℝ), P t)) ((0 : ℝ), P') 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk hP
  have b := a.clm_apply hQ
  simp only [h1, h3]
  rw [hs.eq (0, P 0) (1, 0)]
  exact b

theorem dOp_hasDerivAt : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (G : ℝ → SInf F κ) (P Q : ℝ → (κ → mixedEmbedding.mixedSpace F))
    (g' : SInf F κ) (P' Q' : κ → mixedEmbedding.mixedSpace F),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => G p.1 p.2) →
    (∀ y, HasDerivAt (fun t => G t y) (g' y) 0) → HasDerivAt P P' 0 → HasDerivAt Q Q' 0 → ∀ y,
    HasDerivAt (fun t => GlobalTheory.HeisOrbit.dOp (P t) (Q t) (G t) y) (GlobalTheory.HeisOrbit.dOp (P 0) (Q 0) g' y + GlobalTheory.HeisOrbit.dOp P' Q' (G 0) y) 0 := by
  intro F _ _ κ _ G P Q g' P' Q' hG hg hP hQ y
  have h1 := hasDerivAt_fderiv_family (fun p : ℝ × (κ → mixedEmbedding.mixedSpace F) => G p.1 p.2)
    (hG.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))) g' hg P P' hP y
  let L : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
    { toFun := fun q => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * q i)
      map_add' := by
        intro a b
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add]
      map_smul' := by
        intro c a
        simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul, RingHom.id_apply] }
  have h2 : HasDerivAt (fun t => L (Q t)) (L Q') 0 :=
    (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hQ
  have h3 := ((h2.ofReal_comp.const_mul (2 * Real.pi * Complex.I : ℂ)).mul (hg y))
  have h4 := h1.sub h3
  refine HasDerivAt.congr_deriv (f := fun t => GlobalTheory.HeisOrbit.dOp (P t) (Q t) (G t) y) h4 ?_
  symm
  simp only [GlobalTheory.HeisOrbit.dOp]
  change _ = fderiv ℝ g' y (P 0) + fderiv ℝ (G 0) y P' - (2 * Real.pi * Complex.I *
    ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * Q' i) : ℝ) : ℂ) * G 0 y + 2 * Real.pi * Complex.I *
    ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * Q 0 i) : ℝ) : ℂ) * g' y)
  ring

end GlobalTheory.HeisOrbit.DOpDeriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivativeMemFockAlgebraicThetaVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareComm.AlgDeriv

open Complex GlobalTheory.FockIndep GlobalTheory.ArchRec.DerFock
open scoped Real

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem exists_dRho_pure_all (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (sS frS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (εS : D.what₂.Tau → Fin S.rank → Bool)
    (sT frT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (εT : D.what₂.Tau → Fin T.rank → Bool)
    (hfS : ∀ ρ, GlobalTheory.ArchRec.IsFrameOf (gramAt D S ρ) (sS ρ) (εS ρ) (frS ρ))
    (hfT : ∀ ρ, GlobalTheory.ArchRec.IsFrameOf (gramAt D T ρ) (sT ρ) (εT ρ) (frT ρ))
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    ∃ L : Module.End ℂ (MvPolynomial (FVar D T.rank S.rank) ℂ), ∀ f, IsThetaFunO ψ S T f →
      IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f → ∀ P,
      Datum.dRho (heisO ψ S T) θ τ z (pureTensorL (aPlusAll (heisO ψ S T) θ (fun ρ => cplxO (sS ρ) (sT ρ))
        (fun ρ => (frS ρ)⁻¹) (fun ρ => (frT ρ)⁻¹)) f P) =
      pureTensorL (aPlusAll (heisO ψ S T) θ (fun ρ => cplxO (sS ρ) (sT ρ))
        (fun ρ => (frS ρ)⁻¹) (fun ρ => (frT ρ)⁻¹)) f (L P) := by
  classical
  have hS := fun ρ => isCartanInv_of_isFrameOf (hfS ρ)
  have hT := fun ρ => isCartanInv_of_isFrameOf (hfT ρ)
  let A : FVar D T.rank S.rank → (WO S T → ℂ) → (WO S T → ℂ) :=
    aPlusAll (heisO ψ S T) θ (fun ρ => cplxO (sS ρ) (sT ρ)) (fun ρ => (frS ρ)⁻¹) (fun ρ => (frT ρ)⁻¹)
  let u : Fin T.rank × Fin S.rank → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun k => unitMap (frS τ)⁻¹ (frT τ)⁻¹ k.1 k.2
  let α : Fin T.rank × Fin S.rank → ℂ := fun k =>
    if (εT τ k.1 == εS τ k.2) then (frT τ * z * (frS τ)⁻¹) k.1 k.2
    else starRingEnd ℂ ((frT τ * z * (frS τ)⁻¹) k.1 k.2)
  let c : FVar D T.rank S.rank → ℂ := fun k => if k.1 = τ then (fockScale D τ : ℂ)⁻¹ * (-(4 * π * I) *
    ((omDir S T τ z τ (u k.2) : ℝ) + I * (omDir S T τ (cplxO (sS τ) (sT τ) z) τ (u k.2) : ℝ))) else 0
  refine ⟨(1 / 2 : ℂ) • ((∑ k, c k • (MvPolynomial.pderiv k).toLinearMap) +
    (fockScale D τ : ℂ) • ∑ k : Fin T.rank × Fin S.rank,
      α k • LinearMap.mulLeft ℂ (MvPolynomial.X ((τ, k.1, k.2) : FVar D T.rank S.rank))), fun f hf hv P => ?_⟩
  have hadd : ∀ g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → IsThetaFunO ψ S T (g + g') :=
    fun _ _ => GlobalTheory.OrientedHeis.theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (a • g) :=
    fun a _ => GlobalTheory.OrientedHeis.theta_smul a
  have hA : ∀ k g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (A k g) := fun k _ h => aPlus_theta hψ hθ k.1 _ _ h
  have hc : ∀ i j g, IsThetaFunO ψ S T g → A i (A j g) = A j (A i g) := by
    rintro ⟨ρ, a, b⟩ ⟨ρ', a', b'⟩ g h
    by_cases e : ρ = ρ'
    · subst e
      exact aPlus_comm (hS ρ) (hT ρ) _ _ hψ hθ h
    · exact GlobalTheory.TwoPlaceComm.aPlus_comm_ne hψ hθ e _ _ _ _ h
  have Aadd : ∀ i g g', IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → A i (g + g') = A i g + A i g' :=
    fun i _ _ h h' => aPlus_add hψ hθ i.1 _ _ h h'
  have Asm : ∀ i (a : ℂ) g, IsThetaFunO ψ S T g → A i (a • g) = a • A i g :=
    fun i a _ h => aPlus_smul hψ hθ i.1 _ _ a h
  have hm := pure_mem hadd hsm hA hf P
  have hBA : ∀ j g, IsThetaFunO ψ S T g → Datum.annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z (A j g) =
      A j (Datum.annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z g) + c j • g := by
    rintro ⟨ρ, a, b⟩ g h
    by_cases e : ρ = τ
    · subst e
      refine (annih_aPlus (hS ρ) (hT ρ) z (u (a, b)) hψ hθ h).trans ?_
      congr 2
      exact (if_pos rfl).symm
    · rw [show c (ρ, a, b) = 0 from if_neg e, zero_smul, add_zero]
      exact GlobalTheory.TwoPlaceComm.annih_aPlus_ne hψ hθ (Ne.symm e) _ _ _ _ h
  have h1 := pure_deriv (B := Datum.annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z) (c := c) hadd hsm hA hc Aadd Asm
    (fun _ _ h h' => annih_add hψ hθ _ _ _ h h') (fun a _ h => annih_smul hψ hθ _ _ _ a h) hBA hf (hv z) P
  have h2 : Datum.aPlus (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z (pureTensorL A f P) =
      pureTensorL A f (∑ k : Fin T.rank × Fin S.rank,
        α k • (MvPolynomial.X ((τ, k.1, k.2) : FVar D T.rank S.rank) * P)) := by
    conv_lhs => rw [eq_sum_unitMap (hfS τ).1 (hfT τ).1 z]
    rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ (sS τ) (sT τ) hm, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ τ (sS τ) (sT τ) hm _ _ (cplxO_unitMap (hfS τ) (hfT τ) k.1 k.2), map_smul,
      pure_X_mul hadd hsm hA hc Aadd Asm hf]
    rfl
  have h3 : ∀ g, Datum.dRho (heisO ψ S T) θ τ z g =
      (1 / 2 : ℂ) • (Datum.annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z g +
        (fockScale D τ : ℂ) • Datum.aPlus (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z g) := fun g => by
    rw [Datum.aPlus, smul_smul, mul_inv_cancel₀ (fockScale_ne_zero τ), one_smul, Datum.annih, Datum.crea]
    module
  change Datum.dRho (heisO ψ S T) θ τ z (pureTensorL A f P) = pureTensorL A f _
  rw [h3, h1, h2, ← map_smul, ← map_add, ← map_smul]
  congr 1
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.mulLeft_apply]
  rfl

end GlobalTheory.SquareComm.AlgDeriv

open GlobalTheory.SquareComm.AlgDeriv in

theorem GlobalTheory.SquareComm.dRho_mem_algF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X), ∀ f ∈ algF ψ θ ε A B, ∀ (τ : D.what₂.Tau) (z : Matrix (Fin X.rank) (Fin S.rank) ℂ),
      dRho (heisO ψ (sgn ε S) X) θ τ z f ∈ algF ψ θ ε A B := by
  intro D ψ θ hψ hθ ε S X A B f hf τ z
  have hth : ∀ g ∈ algF ψ θ ε A B, IsThetaFunO ψ (sgn ε S) X g := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f₀, P, hf₀, rfl⟩ := hx
      exact GlobalTheory.FockIndep.pure_mem (A := aPlusAll (heisO ψ (sgn ε S) X) θ
          (fun ρ => cplxO ((frSgn ε A).cart ρ) (B.cart ρ)) A.onb B.onb) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
        (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun k _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ k.1 _ _ h) hf₀.1 P
    | zero => exact GlobalTheory.OrientedHeis.theta_zero
    | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
    | smul a x _ hx => exact GlobalTheory.OrientedHeis.theta_smul a hx
  obtain ⟨L, hL⟩ := exists_dRho_pure_all (S := sgn ε S) (T := X) hψ hθ (frSgn ε A).cart (frSgn ε A).fr (frSgn ε A).ε
    B.cart B.fr B.ε (fun ρ => ⟨(frSgn ε A).fr_unit ρ, (frSgn ε A).fr_gram ρ, rfl⟩)
    (fun ρ => ⟨B.fr_unit ρ, B.fr_gram ρ, rfl⟩) τ z
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f₀, P, hf₀, rfl⟩ := hx
    exact Submodule.subset_span ⟨f₀, L P, hf₀, hL f₀ hf₀.1 (hf₀.2 τ) P⟩
  | zero =>
    have h0 := GlobalTheory.FockIndep.dRho_smul (S := sgn ε S) (T := X) hψ hθ τ z 0 (GlobalTheory.OrientedHeis.theta_zero (ψ := ψ) (S := sgn ε S) (T := X))
    rw [zero_smul, zero_smul] at h0
    rw [h0]
    exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    rw [GlobalTheory.FockIndep.dRho_add (S := sgn ε S) (T := X) hψ hθ τ z (hth x hx) (hth y hy)]
    exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
    rw [GlobalTheory.FockIndep.dRho_smul (S := sgn ε S) (T := X) hψ hθ τ z a (hth x hx)]
    exact Submodule.smul_mem _ a ih

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianWittIndexLeNegativeSignatureStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianWittIndex_le_negative_signature : ∀ {D : D7} (M : HSp D) {p : ℕ} {τ : D.what₂.Tau}, Formalism.UG.HasSignature (gramAt D M τ) (M.rank - p) p → ∀ {r : ℕ} {Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E}, GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf → r ≤ p := by
  first | exact @GlobalTheory.WittSig.wittIndex_le_neg | exact GlobalTheory.WittSig.wittIndex_le_neg | (intros; apply GlobalTheory.WittSig.wittIndex_le_neg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfiniteHeightTransposeGramUnitaryLeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infiniteHeight_transposeGramUnitary_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E} (hJ : J = D.host.xi0 • reindex e e X.gramᵀ), ∃ C : NNReal, ∀ h : GA D X, ∏ w, GlobalTheory.AdelicU.htInf D.host.F w (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (kapX X e hJ h).1) ≤ C * ∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.infHt θ X τ h := by
  first | exact @GlobalTheory.HtInfKapX.htInf_kapX_le | exact GlobalTheory.HtInfKapX.htInf_kapX_le | (intros; apply GlobalTheory.HtInfKapX.htInf_kapX_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitesimalCharacterDifferenceStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinitesimal_character_difference : GlobalTheory.Published.LanglandsClassification → ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε) (h : 0 < I.a), I.j ⟨0, h⟩ = 1 → ∀ χ : Fin n → ℂ, (∀ (k : ℕ) v, IsKFin ε I.ρ v → ∃ N : ℕ, actU ε I.ρ ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) v = 0) → ∃ i j, i ≠ j ∧ χ i - χ j = I.s ⟨0, h⟩ := by
  first | exact @GlobalTheory.IndCap.infChar_sub_eq_of_line | exact GlobalTheory.IndCap.infChar_sub_eq_of_line | (intros; apply GlobalTheory.IndCap.infChar_sub_eq_of_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableThetaMatrixCoeffIsotropicRational
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMean

theorem integrable_coef : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)), μ.IsAddHaarMeasure → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Integrable (fun y => ∫ u in 𝓕, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) μ := by
  intro D V W a b P Q hP hQ _hiso ψ hψ μ hμ ν 𝓕 hν h𝓕 G G' hG hG'
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨U, hU, hvan⟩ := GlobalTheory.T.thetaMatrixCoeff_eq_zero_unless_character_trivial D V W ψ hψ ν 𝓕 hν h𝓕 G G' hG hG'
  obtain ⟨K, hK, hKmem⟩ := GlobalTheory.T.finitePart_mem_compact_of_isotropicAnnihilator D V W a b P Q hP hQ ψ hψ U hU
  refine GlobalTheory.T.integrable_adelicMatrix_rapid_decay_compact_finite D a b μ hμ θ hθ _ (GlobalTheory.T.continuous_thetaMatrixCoeff_along_sandwich D V W a b P Q ψ hψ ν 𝓕 hν h𝓕 G G' hG hG') K hK ?_ ?_
  · intro y hy
    by_contra hne
    apply hy
    refine hKmem y fun u hu hu0 => ?_
    by_contra h1
    exact hne (hvan _ u hu hu0 h1)
  · refine GlobalTheory.T.rapid_decay_all_real_coordinates_of_functionals D V W a b P Q hP hQ θ hθ _ fun τ z m => ?_
    obtain ⟨C, hC⟩ := GlobalTheory.T.thetaMatrixCoeff_rapid_decay_real_functional D V W ψ hψ ν 𝓕 hν h𝓕 G G' hG hG' θ hθ τ z m
    exact ⟨C, fun y => hC _⟩

end GlobalTheory.IsoMean

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegratedOperatorNormalizedIndicatorProdFixedStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integratedOperator_normalizedIndicatorProd_fixed : ∀ (D : D7) (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ (K' : ∀ v, Subgroup (GLoc D.sp.cm.sig V.gram v)), (∀ v, IsOpen (K' v : Set (GLoc D.sp.cm.sig V.gram v))) → (∀ v, K' v ≤ Kv V v) → (∀ᶠ v in cofinite, K' v = Kv V v) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W) (x : W), (∀ g : GfC V, (∀ v, finLoc V v g ∈ K' v) → σ g x = x) → ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (fun v => normInd (μf v) (K' v : Set (GLoc D.sp.cm.sig V.gram v)))) P → P x = x := by
  first | exact @GlobalTheory.TrIdem.integralOp_normInd_fix | exact GlobalTheory.TrIdem.integralOp_normInd_fix | (intros; apply GlobalTheory.TrIdem.integralOp_normInd_fix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleAdmissibleFiniteLength
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory.HCChar

theorem simple_of_isIrrAdm : GlobalTheory.Published.KFiniteCoefficientsAnalytic → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsIrrAdm ε π →
    (∀ Y : Submodule ℂ H, IsGKSub ε π Y → Y = ⊥ ∨ Y = kFinVec ε π) ∧ HasFiniteLength ε π := by
  intro hA n ε H _ _ _ π hπ
  have key : ∀ Y : Submodule ℂ H, IsGKSub ε π Y → Y = ⊥ ∨ Y = kFinVec ε π := fun Y hY => by
    obtain ⟨h1, h2⟩ := GlobalTheory.T.closure_gK_submodule hA n ε H π hπ.2.1 Y hY
    rcases hπ.2.2 Y.topologicalClosure Y.isClosed_topologicalClosure h1 with e | e
    · left; rw [← h2, e, bot_inf_eq]
    · right; rw [← h2, e, top_inf_eq]
  refine ⟨key, 1, fun r Y hY hm => ?_⟩
  by_contra hr
  have hr : 1 < r := not_le.1 hr
  have a : Y ⟨0, by omega⟩ < Y ⟨1, by omega⟩ := hm (Fin.mk_lt_mk.2 (by omega))
  have b : Y ⟨1, by omega⟩ < Y ⟨2, by omega⟩ := hm (Fin.mk_lt_mk.2 (by omega))
  rcases key _ (hY ⟨1, by omega⟩) with e | e
  · exact not_lt_bot (e ▸ a)
  · rcases key _ (hY ⟨2, by omega⟩) with e' | e'
    · exact not_lt_bot (e' ▸ b)
    · exact b.ne (e.trans e'.symm)

end GlobalTheory.HCChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.RealDict

variable {D : D7}

def sgE (ε : Bool) : D.host.E := if ε then 1 else -1

def PublishedHyps (D : D7) {n d : ℕ} (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E n) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws)
    (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w) : Prop :=
  IsCMExt D.host.F D.host.E D.sp.cm.sig ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ' ∧
    (∀ i j, D.sp.cm.sig (Xs.J j i) = Xs.J i j) ∧ Xs.J.det ≠ 0 ∧
    (∀ i j, D.sp.cm.sig (Ws.J j i) = -Ws.J i j) ∧ Ws.J.det ≠ 0 ∧
    ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χX n ∧
    ResEtaPow (Units.map (algebraMap D.host.F (AF D.host.F)).toMonoidHom).range χW d ∧
    IsHecke D.host.F D.host.E χX ∧ IsHecke D.host.F D.host.E χW ∧ Mo.IsWeil ψ' χX χW om ∧
    (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Xs.J.map (τ w).1) (Xs.θ w)) ∧
    (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • Ws.J.map (τ w).1) (Ws.θ w))

structure IsPairReading (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X) (ω : WRep M X)
    (Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws) (ψ' : AddChar (AF D.host.F) ℂ)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Xs Ws) (τ : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w) : Prop where

  psi : ψ' = ψ

  JX : Xs.J = sgE (D := D) ε • M.gram

  JW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank))

  cart : ∀ w, ∃ t, (∀ x, (τ w).1 x = conj (tauE D t x)) ∧ Xs.θ w = (if ε then 1 else -1 : ℂ) • A.cart t ∧
    Ws.θ w = (B.cart t).map conj

  good : Mo.IsGood ψ'

  transp : GlobalTheory.TripleRead.IsTransp ψ ε Mo om ω (Equiv.refl (Fin X.rank)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU M (sgE (D := D) ε) JX)
    (GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) JW)

def IsFockMap (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X)
    {Xs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank} {Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Xs Ws)
    (Φ : PolF D X.rank M.rank →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin M.rank × Fin X.rank)) : Prop :=
  ∃ (f₀ : WO (sgn ε M) X → ℂ) (r : (Fin M.rank × Fin X.rank → AF D.host.F) → ℂ),
    IsVacF ψ θ (frSgn ε A) B f₀ ∧ f₀ ≠ 0 ∧
    ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ P) r ∧
      GlobalTheory.TripleRead.thO Mo ψ (sgn ε M).gram (Equiv.refl (Fin X.rank))
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (Φ P) r) = ptF ψ θ (frSgn ε A) B f₀ P

end GlobalTheory.RealDict

end
end

