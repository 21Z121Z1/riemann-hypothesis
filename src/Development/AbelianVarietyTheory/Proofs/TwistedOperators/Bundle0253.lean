import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0232
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0011
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIdempotentMulOfUnitTopBlockReductions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelsAreCoverSeries

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InducedKFiniteRestrictionStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_k_finite_restriction : ∀ (n : ℕ) (ε : Fin n → Bool) (I : Datum ε) (φ : UJ ε → I.V), φ ∈ I.fns → IsKFinFun φ → (∃ f' ∈ I.dualFns, IsKFinFun f' ∧ ∀ k ∈ KG ε, f' k = φ k) ∧ IsKFinIn I.M I.σ (φ 1) ∧ (φ ≠ 0 → ∃ k ∈ KG ε, φ k ≠ 0) := by
  first | exact @GlobalTheory.DualInd.dualFn_values | exact GlobalTheory.DualInd.dualFn_values | (intros; apply GlobalTheory.DualInd.dualFn_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InducedModuleNontrivialStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_module_nontrivial : ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε), Nontrivial I.H := by
  first | exact @GlobalTheory.IndNonzero.indModule_nontrivial | exact GlobalTheory.IndNonzero.indModule_nontrivial | (intros; apply GlobalTheory.IndNonzero.indModule_nontrivial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionInStagesIntertwiningStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induction_in_stages_intertwining : ∀ {n a b : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a} {W' : Flag n b} {β : Fin b → Fin a} {U V : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (τ : Matrix (Fin n) (Fin n) ℂ → (U →L[ℂ] U)) (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (s : Fin a → ℂ) (s' : Fin b → ℂ) (Fsp : Submodule ℂ (UJ ε → U)) (ι : Fsp →ₗ[ℂ] V), (∀ m ∈ leviOne ε W, ∀ u ∈ flagN ε W, m * u * m⁻¹ ∈ flagN ε W') → (∀ x t, IsSplit ε W x t → IsSplit ε W' (x ∘ β) t ∧ ∀ m ∈ leviOne ε W, m * t = t * m) → (∀ v, τ 1 v = v) → (∀ x : Fin a → ℝ, pairing (fun _ => 1) (s' + rho n fun _ => 1) (x ∘ β) = pairing j (s + rho n j) x) → (∀ y ∈ leviOne ε W, ∀ f f' : Fsp, (∀ g, f'.1 g = f.1 (g * y)) → σ (uMat y) (ι f) = ι f') → ∀ {F : UJ ε → U}, F ∈ indFun ⊤ (fun _ => 1) W' τ s' → (∀ g, restr (leviOne ε W) F g ∈ Fsp) → ∀ u ∈ flagN ε W, ∀ m ∈ leviOne ε W, ∀ x t, IsSplit ε W x t → ∀ g, stageFun (leviOne ε W) Fsp ι F (u * m * t * g) = Complex.exp (pairing j (s + rho n j) x) • σ (uMat m) (stageFun (leviOne ε W) Fsp ι F g) := by
  first | exact @GlobalTheory.RealInd.Stages.stageFun_law | exact GlobalTheory.RealInd.Stages.stageFun_law | (intros; apply GlobalTheory.RealInd.Stages.stageFun_law <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionInStagesRestrictionStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induction_in_stages_restriction : ∀ {n a b : ℕ} {ε : Fin n → Bool} {W : Flag n a} {W' : Flag n b} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] (τ : Matrix (Fin n) (Fin n) ℂ → (U →L[ℂ] U)) (s' : Fin b → ℂ) (y : Fin b → ℝ), (∀ x t, IsSplit ε W' x t → t ∈ leviOne ε W → pairing (fun _ => 1) s' x = pairing (fun _ => 1) (fun l => Complex.I * y l) x) → ∀ {F : UJ ε → U}, F ∈ indFun ⊤ (fun _ => 1) W' τ s' → ∀ g, restr (leviOne ε W) F g ∈ indFun (leviOne ε W) (fun _ => 1) W' τ (fun l => Complex.I * y l) := by
  first | exact @GlobalTheory.RealInd.Stages.restr_mem_indFun_stage | exact GlobalTheory.RealInd.Stages.restr_mem_indFun_stage | (intros; apply GlobalTheory.RealInd.Stages.restr_mem_indFun_stage <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceHomLatticeComponentsScaledIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InertHomLattice

variable {D : D7}

theorem intL_iff {w : HeightOneSpectrum (𝓞 D.host.E)} (x : w.adicCompletion D.host.E) :
    x ∈ Formalism.UG.intL (w.adicCompletion D.host.E) ↔ x ∈ Formalism.UG.Ov D.host.E w := Iff.rfl

theorem compAt_sigR {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : w.under (𝓞 D.host.F) = v) {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E}
    (hc : IsConjAt D.sp.cm.sig hv c) (y : Af D.host.F ⊗[D.host.F] D.host.E) :
    compAt D.host.F w (sigR (Af D.host.F) D.sp.cm.sig y) = c (compAt D.host.F w y) := by
  rw [compAt_apply, compAt_apply, finAdEquiv_apply hv, finAdEquiv_apply hv, hc]
  congr 1
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a m => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem exists_gen (w : HeightOneSpectrum (𝓞 D.host.E)) :
    ∃ a₀ ∈ D.host.AA, algebraMap D.host.E (w.adicCompletion D.host.E) a₀ ≠ 0 ∧
      ∀ a ∈ D.host.AA, (algebraMap D.host.E (w.adicCompletion D.host.E) a₀)⁻¹ *
        algebraMap D.host.E (w.adicCompletion D.host.E) a ∈ Formalism.UG.Ov D.host.E w := by
  have hfg : (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).FG :=
    FractionalIdeal.fg_of_isUnit _ (Ne.isUnit (GlobalTheory.SplitHomLattice.ideal_ne_zero D))
  obtain ⟨s, hs⟩ := hfg
  have hne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.coe_empty, Submodule.span_empty] at hs
    exact GlobalTheory.SplitHomLattice.ideal_ne_zero D (FractionalIdeal.coeToSubmodule_eq_bot.1 hs.symm)
  let π := algebraMap D.host.E (w.adicCompletion D.host.E)
  obtain ⟨a₀, ha₀, hmax⟩ := s.exists_max_image (fun a => Valued.v (π a)) hne
  have hle : ∀ a ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E), Valued.v (π a) ≤ Valued.v (π a₀) := by
    intro a ha
    rw [← hs] at ha
    induction ha using Submodule.span_induction with
    | mem a ha => exact hmax a ha
    | zero => simp only [map_zero, zero_le]
    | add x y _ _ hx hy => rw [RingHom.map_add]; exact (Valuation.map_add_le _ hx hy)
    | smul o x _ hx =>
      have ho : Valued.v (π (o : D.host.E)) ≤ 1 := by
        rw [Formalism.UG.P.levelaf_valued_algebraMap, show w.valuation D.host.E (o : D.host.E) = w.intValuation o from
          w.valuation_of_algebraMap o]
        exact w.intValuation_le_one o
      rw [show o • x = (o : D.host.E) * x from rfl, RingHom.map_mul, Valuation.map_mul]
      exact (mul_le_of_le_one_left' ho).trans hx
  have h0 : π a₀ ≠ 0 := by
    intro h
    apply GlobalTheory.SplitHomLattice.ideal_ne_zero D
    rw [FractionalIdeal.eq_zero_iff]
    intro a ha
    have := hle a ha
    rw [h, map_zero, le_zero_iff, map_eq_zero] at this
    exact (map_eq_zero π).1 this
  refine ⟨a₀, ?_, h0, fun a ha => ?_⟩
  · show a₀ ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)
    rw [← hs]; exact Submodule.subset_span ha₀
  · show Valued.v ((π a₀)⁻¹ * π a) ≤ 1
    rw [Valuation.map_mul, map_inv₀, inv_mul_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0))]
    exact hle a ha

theorem mul_vecMulVec_mul_apply {K : Type} [CommRing K] {m n : ℕ} (A : Matrix (Fin m) (Fin m) K)
    (B : Matrix (Fin n) (Fin n) K) (t : Fin m → K) (r : Fin n → K) (p : Fin m) (q : Fin n) :
    (A * Matrix.vecMulVec t r * B) p q = (A *ᵥ t) p * (r ᵥ* B) q := by
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, Matrix.vecMul, dotProduct,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem compW_liftFin (w : HeightOneSpectrum (𝓞 D.host.E)) (z : Af D.host.F ⊗[D.host.F] D.host.E) :
    GlobalTheory.InertHomIdx.compW D w (GlobalTheory.LatticeStable.liftFin D z) = compAt D.host.F w z := by
  rw [GlobalTheory.InertHomIdx.compW, RingHom.comp_apply, GlobalTheory.SplitHomLattice.finPart_liftFin]

theorem compAt_one_tmul (w : HeightOneSpectrum (𝓞 D.host.E)) (y : D.host.E) :
    compAt D.host.F w ((1 : Af D.host.F) ⊗ₜ[D.host.F] y) = algebraMap D.host.E (w.adicCompletion D.host.E) y := by
  rw [compAt_tmul]
  simp

end GlobalTheory.InertHomLattice

namespace GlobalTheory.InertHomLattice

variable {D : D7}

theorem map_compW_sum (S T : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : w.under (𝓞 D.host.F) = v) {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E}
    (hc : IsConjAt D.sp.cm.sig hv c) (a₀ : D.host.E)
    (Y : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E))
    (A : Matrix (Fin T.rank) (Fin T.rank) (w.adicCompletion D.host.E))
    (A' : Matrix (Fin S.rank) (Fin S.rank) (w.adicCompletion D.host.E)) :
    Matrix.map (∑ i, ∑ j, GlobalTheory.LatticeStable.liftFin D (singleAt D.host.F w (Y i j)) •
      GlobalTheory.SplitHomLattice.rk S T a₀ (fun k => singleAt D.host.F w (A' k j)) (fun k => singleAt D.host.F w (A k i)) : WO S T)
      (GlobalTheory.InertHomIdx.compW D w) =
    algebraMap D.host.E (w.adicCompletion D.host.E) a₀ •
      (A * Y * (Formalism.UG.cT c A' * S.gram.map (algebraMap D.host.E (w.adicCompletion D.host.E)))) := by
  refine Matrix.ext fun p q => ?_
  rw [Matrix.map_apply, Matrix.sum_apply, map_sum]
  simp only [Matrix.sum_apply, map_sum, Matrix.smul_apply, smul_eq_mul, map_mul, compW_liftFin, compAt_singleAt,
    GlobalTheory.SplitHomLattice.rk, Matrix.of_apply, compAt_sigR hv hc, compAt_one_tmul]
  simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring
end GlobalTheory.InertHomLattice

namespace GlobalTheory.InertHomLattice

theorem mem_map_latF_iff : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsInertAt D.host.F D.host.E v w → ∀ a : GL (Fin T.rank) (w.adicCompletion D.host.E), IsFrameAt w (frameLat T) a → ∃ (c₀ : w.adicCompletion D.host.E) (b : GL (Fin S.rank) (w.adicCompletion D.host.E)), c₀ ≠ 0 ∧ ∀ X : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), X ∈ (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).toAddSubgroup.map (GlobalTheory.InertHomIdx.matW S T w) ↔ c₀ • ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * X * b.1) ∈ GlobalTheory.InertHomIdx.intMat (w.adicCompletion D.host.E) T.rank S.rank := by
  intro D S T v w hv hw a ha
  obtain ⟨c, hc, -⟩ := InertChart.existsUnique_isConjAt D.sp.cm.sig hw hv
  have hlat := GlobalTheory.HeckeDual.isLattice_frameLat S
  obtain ⟨aS, haS⟩ := InertChart.exists_isFrameAt (L := frameLat S) hw hlat.fg hlat.span_eq_top
  obtain ⟨a₀, ha₀, h0, hgen⟩ := exists_gen (D := D) w
  set π := algebraMap D.host.E (w.adicCompletion D.host.E) with hπ
  set G : Matrix (Fin S.rank) (Fin S.rank) (w.adicCompletion D.host.E) := S.gram.map π with hG
  set B : Matrix (Fin S.rank) (Fin S.rank) (w.adicCompletion D.host.E) := Formalism.UG.cT c aS.1 * G with hB
  have hBu : IsUnit B.det := by
    rw [hB, Matrix.det_mul, isUnit_iff_ne_zero]
    refine mul_ne_zero ?_ ?_
    · rw [Formalism.UG.cT, Matrix.det_transpose, show (aS.1.map c).det = c aS.1.det from (RingHom.map_det c aS.1).symm]
      exact (map_ne_zero c).2 (Matrix.det_ne_zero_of_left_inverse (B := (aS⁻¹).1) (by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]))
    · rw [hG, show (S.gram.map π).det = π S.gram.det from (RingHom.map_det π S.gram).symm]
      exact ((GlobalTheory.LatVac.gram_det_isUnit S).map π).ne_zero
  refine ⟨(π a₀)⁻¹, (Matrix.nonsingInvUnit B hBu)⁻¹, inv_ne_zero h0, fun X => ⟨fun h => ?_, fun h => ?_⟩⟩
  · obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.1 h
    rw [GlobalTheory.InertHomIdx.matW_apply]
    have hx' : (x : WO S T) ∈ latO S T (frameLat S) (frameLat T) fun _ => True := hx
    have hb : ((Matrix.nonsingInvUnit B hBu)⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1 = B⁻¹ := rfl
    let Φ : WO S T →+ Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) := AddMonoidHom.mk'
      (fun u => (π a₀)⁻¹ • ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *
        u.map (GlobalTheory.InertHomIdx.compW D w) * ((Matrix.nonsingInvUnit B hBu)⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1))
      fun u u' => by simp only [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, smul_add]
    suffices hle : latO S T (frameLat S) (frameLat T) (fun _ => True) ≤
        (GlobalTheory.InertHomIdx.intMat (w.adicCompletion D.host.E) T.rank S.rank).comap Φ from hle hx'
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, -, a1, ha1, s, hs, t, ht, rfl⟩
    set lam := GlobalTheory.AdeleBaseChange.locMap D.host.F w (α (w.under (𝓞 D.host.F))) with hlam
    have hlamO : lam ∈ Formalism.UG.Ov D.host.E w := GlobalTheory.AdeleBaseChange.locMap_int w _ (hα _)
    have hmap : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
        (a1 * t i * ∑ k, star (s k) * S.gram k j) : WO S T).map (GlobalTheory.InertHomIdx.compW D w) =
        (lam * π a1) • Matrix.vecMulVec (fun i => π (t i)) ((fun k => c (π (s k))) ᵥ* G) := by
      ext i j
      have e1 : GlobalTheory.InertHomIdx.compW D w (pairA D.host.F 0 α ⊗ₜ[D.host.F]
          (a1 * t i * ∑ k, star (s k) * S.gram k j)) =
          lam * π (a1 * t i * ∑ k, star (s k) * S.gram k j) := compAt_tmul w α _
      rw [Matrix.map_apply, Matrix.of_apply, e1, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
      have hconj : ∀ y, c (π y) = π (star y) := fun y => InertChart.conj_algebraMap hc y
      simp only [map_mul, map_sum, Matrix.vecMul, dotProduct, hG, Matrix.map_apply, hconj]
      ring_nf
    have hy : ∀ p, ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ fun i => π (t i)) p ∈ Formalism.UG.Ov D.host.E w := by
      refine (ha _).2 ?_
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      exact Submodule.subset_span ⟨t, ht, rfl⟩
    set z := (aS⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1 *ᵥ fun k => π (s k) with hz
    have hzO : ∀ k, z k ∈ Formalism.UG.Ov D.host.E w := by
      refine (haS _).2 ?_
      rw [hz, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      exact Submodule.subset_span ⟨s, hs, rfl⟩
    have hsz : (fun k => π (s k)) = aS.1 *ᵥ z := by
      rw [hz, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have hcs : (fun k => c (π (s k))) = (fun k => c (z k)) ᵥ* Formalism.UG.cT c aS.1 := by
      funext k
      rw [Formalism.UG.cT, Matrix.vecMul_transpose, show c (π (s k)) = c ((fun k => π (s k)) k) from rfl, hsz]
      exact RingHom.map_mulVec c aS.1 z k
    have hr : ((fun k => c (π (s k))) ᵥ* G) ᵥ* ((Matrix.nonsingInvUnit B hBu)⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1 =
        fun k => c (z k) := by
      rw [hb, hcs, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, ← hB, Matrix.mul_nonsing_inv B hBu, Matrix.vecMul_one]
    intro p q
    show ((π a₀)⁻¹ • ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
        (a1 * t i * ∑ k, star (s k) * S.gram k j) : WO S T).map (GlobalTheory.InertHomIdx.compW D w) *
        ((Matrix.nonsingInvUnit B hBu)⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1 :
        Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E))) p q ∈ _
    rw [hmap, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_vecMulVec_mul_apply, hr]
    have h1 := hgen a1 ha1
    have h2 := InertChart.conj_mem hw hc (hzO q)
    rw [intL_iff, show (π a₀)⁻¹ * (lam * π a1 * (((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ fun i => π (t i)) p * c (z q))) =
      lam * ((π a₀)⁻¹ * π a1) * ((((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 *ᵥ fun i => π (t i)) p) * c (z q)) by ring]
    exact mul_mem (mul_mem hlamO h1) (mul_mem (hy p) h2)
  · set Y := (π a₀)⁻¹ • ((a⁻¹ : GL (Fin T.rank) (w.adicCompletion D.host.E)).1 * X *
        ((Matrix.nonsingInvUnit B hBu)⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1) with hY
    have hb : ((Matrix.nonsingInvUnit B hBu)⁻¹ : GL (Fin S.rank) (w.adicCompletion D.host.E)).1 = B⁻¹ := rfl
    have hX : X = π a₀ • (a.1 * Y * B) := by
      rw [hY, hb, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ h0, one_smul]
      simp only [Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul B hBu, Matrix.mul_one, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.one_mul]
    have hsingle : ∀ {n : ℕ} (i : Fin n) (k : Fin n), (Pi.single i 1 : Fin n → w.adicCompletion D.host.E) k ∈ Formalism.UG.Ov D.host.E w := by
      intro n i k
      rw [Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have htI : ∀ i, (fun k => singleAt D.host.F w (a.1 k i)) ∈ Formalism.L2.NTheta.LamHat T := fun i => by
      have := (ha (Pi.single i 1)).1 (hsingle i)
      rw [Matrix.mulVec_single_one] at this
      exact singleAt_mem_lamHat this
    have hsJ : ∀ j, (fun k => singleAt D.host.F w (aS.1 k j)) ∈ Formalism.L2.NTheta.LamHat S := fun j => by
      have := (haS (Pi.single j 1)).1 (hsingle j)
      rw [Matrix.mulVec_single_one] at this
      exact singleAt_mem_lamHat this
    have hu : (∑ i, ∑ j, GlobalTheory.LatticeStable.liftFin D (singleAt D.host.F w (Y i j)) •
        GlobalTheory.SplitHomLattice.rk S T a₀ (fun k => singleAt D.host.F w (aS.1 k j))
          (fun k => singleAt D.host.F w (a.1 k i)) : WO S T) ∈ latO S T (L0c D S) (L0c D T) fun _ => True :=
      sum_mem fun i _ => sum_mem fun j _ => GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _
        (by rw [GlobalTheory.SplitHomLattice.finPart_liftFin]; exact singleAt_mem_intAE (h i j)) _
        (GlobalTheory.SplitHomLattice.rk_mem S T ha₀ (hsJ j) (htI i))
    rw [hermitianSpaceBaseLattice_eq_frameLattice, hermitianSpaceBaseLattice_eq_frameLattice] at hu
    refine AddSubgroup.mem_map.2 ⟨GlobalTheory.FinWeilO.XF.mk _ (GlobalTheory.SplitScalar.latO_fin hu), hu, ?_⟩
    rw [GlobalTheory.InertHomIdx.matW_apply, GlobalTheory.FinWeilO.XF.coe_mk]
    exact (map_compW_sum S T hv hc a₀ Y a.1 aS.1).trans hX.symm

end GlobalTheory.InertHomLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableMatrixCoeffCyclicSpan
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory

theorem unitaryRep_inner_map {n : ℕ} {ε : Fin n → Bool} {U : Type} [NormedAddCommGroup U]
    [InnerProductSpace ℂ U] {π : UJ ε →* (U →L[ℂ] U)} (hπ : IsUnitaryRep π) (h : UJ ε) (x y : U) :
    ⟪π h x, π h y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let L : U →ₗᵢ[ℂ] U := ⟨(π h).toLinearMap, hπ.norm_apply h⟩
  exact L.inner_map_map x y

theorem isMulRightInvariant_haar_UJ {n : ℕ} (ε : Fin n → Bool) (μ : Measure (UJ ε))
    [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  haveI : (muG ε).IsHaarMeasure := by unfold muG; infer_instance
  have hμ := Measure.isMulLeftInvariant_eq_smul μ (muG ε)
  constructor
  intro g
  rw [hμ, Measure.map_smul, indefinite_unitary_unimodular n ε g]

theorem span_orbit_coeff_memLp {n : ℕ} {ε : Fin n → Bool} (μ : Measure (UJ ε)) [μ.IsHaarMeasure]
    {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] {π : UJ ε →* (U →L[ℂ] U)}
    (hπ : IsUnitaryRep π) (q : ℝ≥0∞) (v : U) (hv : MemLp (fun g => ⟪v, π g v⟫_ℂ) q μ)
    (u : U) (hu : u ∈ Submodule.span ℂ (Set.range fun g => π g v))
    (u' : U) (hu' : u' ∈ Submodule.span ℂ (Set.range fun g => π g v)) :
    MemLp (fun g => ⟪u', π g u⟫_ℂ) q μ := by
  haveI := isMulRightInvariant_haar_UJ ε μ

  have gen : ∀ h g₀ : UJ ε, MemLp (fun g => ⟪π h v, π g (π g₀ v)⟫_ℂ) q μ := by
    intro h g₀
    have e : (fun g => ⟪π h v, π g (π g₀ v)⟫_ℂ) =
        (fun g => ⟪v, π g v⟫_ℂ) ∘ (fun g => h⁻¹ * g) ∘ (fun g => g * g₀) := by
      funext g
      simp only [Function.comp]
      rw [← ContinuousLinearMap.mul_apply, ← map_mul,
        ← unitaryRep_inner_map hπ h⁻¹ (π h v), ← ContinuousLinearMap.mul_apply, ← map_mul,
        ← ContinuousLinearMap.mul_apply (π h⁻¹), ← map_mul, inv_mul_cancel, map_one,
        ContinuousLinearMap.one_apply]
    rw [e]
    exact (hv.comp_measurePreserving (measurePreserving_mul_left μ h⁻¹)).comp_measurePreserving
      (measurePreserving_mul_right μ g₀)
  have step1 : ∀ h : UJ ε, ∀ u ∈ Submodule.span ℂ (Set.range fun g => π g v),
      MemLp (fun g => ⟪π h v, π g u⟫_ℂ) q μ := by
    intro h u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g₀, rfl⟩ := hx
      exact gen h g₀
    | zero =>
      have : (fun g => ⟪π h v, π g (0 : U)⟫_ℂ) = 0 := by funext g; simp
      rw [this]; exact MemLp.zero
    | add x y _ _ hx hy =>
      have : (fun g => ⟪π h v, π g (x + y)⟫_ℂ) =
          (fun g => ⟪π h v, π g x⟫_ℂ) + (fun g => ⟪π h v, π g y⟫_ℂ) := by
        funext g; simp [map_add, inner_add_right]
      rw [this]; exact hx.add hy
    | smul c x _ hx =>
      have : (fun g => ⟪π h v, π g (c • x)⟫_ℂ) = c • (fun g => ⟪π h v, π g x⟫_ℂ) := by
        funext g; simp [map_smul, inner_smul_right]
      rw [this]; exact hx.const_smul c
  induction hu' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    exact step1 h u hu
  | zero =>
    have : (fun g => ⟪(0 : U), π g u⟫_ℂ) = 0 := by funext g; simp
    rw [this]; exact MemLp.zero
  | add x y _ _ hx hy =>
    have : (fun g => ⟪x + y, π g u⟫_ℂ) = (fun g => ⟪x, π g u⟫_ℂ) + (fun g => ⟪y, π g u⟫_ℂ) := by
      funext g; simp [inner_add_left]
    rw [this]; exact hx.add hy
  | smul c x _ hx =>
    have : (fun g => ⟪c • x, π g u⟫_ℂ) = (starRingEnd ℂ c) • (fun g => ⟪x, π g u⟫_ℂ) := by
      funext g; simp [inner_smul_left, mul_comm]
    rw [this]; exact hx.const_smul _

theorem span_orbit_coeff_integrable : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → ∀ (p : ℝ), 1 ≤ p → ∀ v : U, Integrable (fun g => ‖⟪v, π g v⟫_ℂ‖ ^ p) μ → ∀ u ∈ Submodule.span ℂ (Set.range fun g => π g v), ∀ u' ∈ Submodule.span ℂ (Set.range fun g => π g v), Integrable (fun g => ‖⟪u', π g u⟫_ℂ‖ ^ p) μ := by
  intro n ε μ _ U _ _ π hπ p hp v hv u hu u' hu'
  have hp0 : (0 : ℝ) < p := by linarith
  have hq0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hqt : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have cont : ∀ a b : U, Continuous fun g => ⟪a, π g b⟫_ℂ := fun a b =>
    continuous_const.inner (hπ.continuous_apply b)
  have hv' : MemLp (fun g => ⟪v, π g v⟫_ℂ) (ENNReal.ofReal p) μ := by
    rw [← integrable_norm_rpow_iff (cont v v).aestronglyMeasurable hq0 hqt, hpr]
    exact hv
  have h := span_orbit_coeff_memLp μ hπ _ v hv' u hu u' hu'
  rw [← integrable_norm_rpow_iff (cont u' u).aestronglyMeasurable hq0 hqt, hpr] at h
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIdempotentMulOfUnitTopBlockReductionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_idempotent_mul_of_unit_topBlock_reductions : ∀ {D : D7} (m n : ℕ), n ≤ m → ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ (u : Matrix (Fin m) (Fin n) (EAf D)) (γ : GL (Fin n) (EAf D)), IsIntM u → IsIntM (HMul.hMul u (γ⁻¹ : GL (Fin n) (EAf D)).1) → (∀ i j, toEAf D e * u i j = u i j) → (∀ PP ∈ Z, IsUnit (topL n (redM PP u)).det) → (∀ PP ∈ Z, IsUnit (topL n (redM PP (HMul.hMul u (γ⁻¹ : GL (Fin n) (EAf D)).1))).det) → IsIntM (toEAf D e • γ.1) ∧ IsIntM (toEAf D e • (γ⁻¹ : GL (Fin n) (EAf D)).1) ∧ ∀ PP ∈ Z, topL n (redM PP (HMul.hMul u (γ⁻¹ : GL (Fin n) (EAf D)).1)) * redM PP (toEAf D e • γ.1) = topL n (redM PP u) := by
  first | exact @GlobalTheory.HalfUnit.int_of_unit_tops | exact GlobalTheory.HalfUnit.int_of_unit_tops | (intros; apply GlobalTheory.HalfUnit.int_of_unit_tops <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspFunOfTendstoModerateGrowthSize
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspLimit

theorem integral_eq_zero_of_approx {X : Type} [MeasurableSpace X] {μ : Measure X} {u : ℕ → X → ℂ} {v : X → ℂ}
    {w : X → ℝ} (hu : ∀ n, Integrable (u n) μ) (hv : Integrable v μ) (hw : Integrable w μ)
    (h0 : ∀ n, ∫ x, u n x ∂μ = 0) (h : ∀ ε : ℝ, 0 < ε → ∃ n, ∀ x, ‖u n x - v x‖ ≤ ε * w x) :
    ∫ x, v x ∂μ = 0 := by
  have key : ∀ ε : ℝ, 0 < ε → ‖∫ x, v x ∂μ‖ ≤ ε * ∫ x, w x ∂μ := fun ε hε => by
    obtain ⟨n, hn⟩ := h ε hε
    have e : ∫ x, (u n x - v x) ∂μ = -∫ x, v x ∂μ := by rw [integral_sub (hu n) hv, h0, zero_sub]
    rw [← norm_neg, ← e, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hw.const_mul ε) (Filter.Eventually.of_forall hn)
  have t : Filter.Tendsto (fun ε : ℝ => ε * ∫ x, w x ∂μ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 * ∫ x, w x ∂μ)) :=
    ((continuous_id.mul continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [zero_mul] at t
  exact norm_le_zero_iff.1 (ge_of_tendsto t (eventually_nhdsWithin_of_forall key))

theorem isCuspFun_of_tendsto : ∀ (D : D7) (V : HSp D) (N : ℕ) (ψ : ℕ → GA D V → ℂ) (f : GA D V → ℂ), (∀ n, Continuous (ψ n) ∧ (∀ γ ∈ GQ V, ∀ g, ψ n (γ * g) = ψ n g) ∧ IsCuspFun V (ψ n)) → Continuous f → (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) → Filter.Tendsto (fun n => GlobalTheory.Size.growthSize V N (ψ n - f)) Filter.atTop (nhds 0) → IsCuspFun V f := by
  intro D V N ψ f hψ hf hl ht
  have hint : ∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) →
      ∀ W, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W → ∀ μ : Measure (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W), μ.IsHaarMeasure →
      ∀ 𝓕, IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRat D.sp.cm V W) 𝓕 μ → ∀ g : GA D V,
        IntegrableOn (fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => φ (n.1 * g)) 𝓕 μ := by
    intro φ hc hl W hW μ hμ 𝓕 h𝓕 g
    rw [GlobalTheory.AutFunCompare.GQ_eq] at hl
    exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V W hW φ hc hl μ hμ 𝓕 h𝓕 g
  rw [GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm]
  intro W hW μ hμ 𝓕 h𝓕 g
  obtain ⟨h1, h2, -, h4⟩ := GlobalTheory.Size.quotHeight_laws V
  have hw := (hint (fun x => ((GlobalTheory.Grow.quotHeight V x ^ N : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (h4.pow N)) (fun γ hγ x => by rw [h2 γ hγ]) W hW μ hμ 𝓕 h𝓕 g).re
  refine integral_eq_zero_of_approx (μ := μ.restrict 𝓕) (u := fun k n => ψ k (n.1 * g)) (v := fun n => f (n.1 * g))
    (fun k => hint _ (hψ k).1 (hψ k).2.1 W hW μ hμ 𝓕 h𝓕 g) (hint _ hf hl W hW μ hμ 𝓕 h𝓕 g) hw
    (fun k => (GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm V _).1 (hψ k).2.2 W hW μ hμ 𝓕 h𝓕 g) fun ε hε => ?_
  obtain ⟨k, hk⟩ := (ht.eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 hε))).exists
  refine ⟨k, fun n => ?_⟩
  rw [GlobalTheory.Size.growthSize_eq_quot (fun γ hγ x => by
    rw [Pi.sub_apply, Pi.sub_apply, (hψ k).2.1 γ hγ, hl γ hγ])] at hk
  have := (ENNReal.ofReal_le_ofReal_iff hε.le).1 ((le_iSup _ (n.1 * g)).trans hk)
  exact (div_le_iff₀ (pow_pos (lt_of_lt_of_le one_pos (h1 _).1) N)).1 this

end GlobalTheory.CuspLimit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDiscreteSeriesConjugateReverseContragredient
section
open Formalism.MainNotions.S GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec

theorem isDS_conj_rev : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mn n → (H →L[ℂ] H)), IsDS ε lam σ → IsDS (fun a => ε a.rev) (fun a => -lam a.rev) (fun g => σ ((g.map (starRingEnd ℂ)).submatrix Fin.rev Fin.rev)) :=
  fun _ _ _ _ _ _ _ hσ => GlobalTheory.CoverModel.isDS_barRev (fun _ => rfl) hσ

end GlobalTheory.ArchRec
end

