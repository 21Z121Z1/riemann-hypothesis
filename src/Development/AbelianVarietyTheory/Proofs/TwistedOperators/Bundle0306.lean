import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0266
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0282
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0278
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0280
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIdealSmulAdelicPointRationalLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepLatIdeal

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem smul_mem_of_mem_smul (Λ : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) (a : E)
    (ha : ∀ m ∈ 𝔪, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = algebraMap (𝓞 E) E m * a) (x : Fin n → E) (hx : x ∈ 𝔪 • Λ) :
    a • x ∈ Λ := by
  refine Submodule.smul_induction_on (p := fun w => a • w ∈ Λ) hx (fun m hm y hy => ?_) (fun u v hu hv => ?_)
  · obtain ⟨c, hc⟩ := ha m hm
    have e : a • (m • y) = c • y := by
      rw [← algebraMap_smul E m y, ← algebraMap_smul E c y, smul_smul, hc, mul_comm]
    simp only [e]
    exact Λ.smul_mem c hy
  · simp only [smul_add]
    exact Λ.add_mem hu hv

theorem smul_mem_hatL (Λ : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) (a : E)
    (ha : ∀ m ∈ 𝔪, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = algebraMap (𝓞 E) E m * a)
    (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hz : z ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ)) :
    (a ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) • z ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  change z ∈ Submodule.span _ _ at hz
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, rfl⟩ := hw
    have hax := smul_mem_of_mem_smul Λ 𝔪 a ha x hx
    change _ ∈ Submodule.span _ _
    refine Submodule.subset_span ⟨a • x, hax, ?_⟩
    funext i
    show (a • x) i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) = (a ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * (x i ⊗ₜ[F] 1)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rfl
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [smul_add]; exact Submodule.add_mem _ hu hv
  | smul s u _ hu =>
    rw [Subring.smul_def, smul_smul, mul_comm, ← smul_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ s hu

theorem eq_zero_of_mem_hatL_bot (z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) (⊥ : Submodule (𝓞 E) (Fin n → E))) : z = 0 := by
  change z ∈ Submodule.span _ _ at hz
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, rfl⟩ := hw
    have hx0 : x = 0 := (Submodule.mem_bot _).1 hx
    subst hx0
    funext i
    show (0 : E) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) = 0
    exact TensorProduct.zero_tmul _ _
  | zero => rfl
  | add u v _ _ hu hv => rw [hu, hv, add_zero]
  | smul s u _ hu => rw [hu, smul_zero]

theorem nontrivial_af : Nontrivial (Formalism.L2.Herm.Af F) := by
  obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.mp (NumberField.RingOfIntegers.not_isField F)
  let v : HeightOneSpectrum (𝓞 F) := ⟨p, hp, hp0⟩
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h' := congrArg (fun b : Formalism.L2.Herm.Af F => b v) h
  simp at h'

theorem mem_smul_span (Λ : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (y : Fin n → E)
    (hy : g.1 *ᵥ (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ)) :
    y ∈ 𝔪 • Submodule.span (𝓞 E) {y : Fin n → E | g.1 *ᵥ (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) ∈
      Formalism.L2.Herm.hatL (F := F) Λ} := by
  by_cases h𝔪 : 𝔪 = ⊥
  · subst h𝔪
    have h0 : g.1 *ᵥ (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) = 0 :=
      eq_zero_of_mem_hatL_bot _ (by simpa [Submodule.bot_smul] using hy)
    have hv : (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) = 0 := by
      have := congrArg (fun w => (g⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).1 *ᵥ w) h0
      simpa [Matrix.mulVec_mulVec] using this
    haveI := nontrivial_af (F := F)
    have hinj : Function.Injective (Algebra.TensorProduct.includeLeft : E →ₐ[F] E ⊗[F] Formalism.L2.Herm.Af F) :=
      Algebra.TensorProduct.includeLeft_injective (algebraMap F (Formalism.L2.Herm.Af F)).injective
    have hy0 : y = 0 := by
      funext i
      apply hinj
      simpa using congrFun hv i
    subst hy0
    exact Submodule.zero_mem _
  · have hP : (𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by
      rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
    have h1 : (1 : E) ∈ ((𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) *
        (((𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) := by
      rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hP]
      exact FractionalIdeal.one_mem_one _
    have key : ∀ c ∈ ((𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E) *
        (((𝔪 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E),
        c • y ∈ 𝔪 • Submodule.span (𝓞 E) {y : Fin n → E | g.1 *ᵥ (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) ∈
          Formalism.L2.Herm.hatL (F := F) Λ} := by
      intro c hc
      refine Submodule.mul_induction_on (C := fun c => c • y ∈ 𝔪 • Submodule.span (𝓞 E)
        {y : Fin n → E | g.1 *ᵥ (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) ∈ Formalism.L2.Herm.hatL (F := F) Λ})
        hc (fun m hm a ha => ?_) (fun u v hu hv => ?_)
      · obtain ⟨m', hm', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hm
        have hint : ∀ t ∈ 𝔪, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = algebraMap (𝓞 E) E t * a := by
          intro t ht
          obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1
            ((FractionalIdeal.mem_inv_iff hP).1 ha _ (FractionalIdeal.mem_coeIdeal_of_mem _ ht))
          exact ⟨c, by rw [hc, mul_comm]⟩
        have hcol : (fun i => (a • y) i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) =
            (a ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) • (fun i => y i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) := by
          funext i
          show (a * y i) ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F) = (a ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * (y i ⊗ₜ[F] 1)
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        have haS : g.1 *ᵥ (fun i => (a • y) i ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
          rw [hcol, Matrix.mulVec_smul]
          exact smul_mem_hatL Λ 𝔪 a hint _ hy
        rw [mul_smul, algebraMap_smul]
        exact Submodule.smul_mem_smul hm' (Submodule.subset_span haS)
      · rw [add_smul]
        exact Submodule.add_mem _ hu hv
    simpa using key 1 h1

end General

theorem mem_smul_latAt : ∀ (D : D7) (V : HSp D) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → ∀ (x : GA D V) (y : Fin V.rank → D.host.E), (Lev.finE V x⁻¹).1 *ᵥ (fun i => y i ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (𝔪 • Λ) → y ∈ 𝔪 • latAt Λ x := by
  intro D V Λ 𝔪 _ x y hy
  unfold GlobalTheory.SepPer.latAt
  exact mem_smul_span Λ 𝔪 (Lev.finE V x⁻¹) y hy

end GlobalTheory.SepLatIdeal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelHeisenbergPhaseEqCexpRealPoints
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.PhaseReal

variable {D : D7}

theorem adj_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D A = Aᴴ := by
  ext i j
  rfl

theorem gram_ct (V : HSp D) : V.gramᴴ = V.gram :=
  Matrix.ext fun i j => GlobalTheory.DualPairCheck.gram_star V j i

theorem infPart_cA (z : AE D) :
    infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, ha, hb]

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace ((S.gram⁻¹).map (incA D) * (y.map (cA D))ᵀ * T.gram.map (incA D) * x) := by
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

theorem hO_iso (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hC : adj D C * V.gram * C' = 1) (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r) :
    hO V W (isoPart V W C κ) (isoPart V W C' (y.map (incA D))) =
      Matrix.trace ((adj D y * W.gram).map (incA D) * κ) := by
  have hz : (y * (adj D C' * V.gram))ᴴ = V.gram * C' * adj D y := by
    rw [conjTranspose_mul, conjTranspose_mul, gram_ct, adj_eq, adj_eq, conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have hu : isoPart V W C' (y.map (incA D)) = (y * (adj D C' * V.gram)).map (incA D) := by
    rw [Matrix.map_mul]
    rfl
  have hu' : ((isoPart V W C' (y.map (incA D))).map (cA D))ᵀ = (V.gram * C' * adj D y).map (incA D) := by
    rw [hu, ← hz]
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.conjTranspose_apply]
    exact GlobalTheory.DualPairCheck.cA_incA _
  have e1 : (V.gram⁻¹).map (incA D) * (V.gram * C' * adj D y).map (incA D) * W.gram.map (incA D) =
      C'.map (incA D) * (adj D y * W.gram).map (incA D) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul]
    congr 1
    rw [Matrix.mul_assoc V.gram, Matrix.nonsing_inv_mul_cancel_left _ _ (Formalism.L2.Theta.gram_det_ne V).isUnit,
      Matrix.mul_assoc]
  have e2 : (adj D C * V.gram).map (incA D) * C'.map (incA D) = 1 := by
    rw [← Matrix.map_mul, hC]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have e3 : isoPart V W C κ = κ * (adj D C * V.gram).map (incA D) := rfl
  rw [hO_eq_trace, hu', e1, e3, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, e2,
    Matrix.mul_one]

theorem pairQ_map (W : HSp D) {r : ℕ} (y : Matrix (Fin W.rank) (Fin r) D.host.E) :
    (pairQ W y).map (incA D) = incA D D.host.xi0 • (adj D y * W.gram).map (incA D) := by
  ext i j
  simp only [pairQ, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem symplO_iso (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hC : adj D C * V.gram * C' = 1) (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r) :
    symplO V W (isoPart V W C' (y.map (incA D))) (isoPart V W C κ) =
      -Algebra.trace (AF D.host.F) (AE D) (Matrix.trace ((pairQ W y).map (incA D) * κ)) := by
  unfold symplO
  rw [← GlobalTheory.FinTranslate.hO_herm, hO_iso V W C C' hC, pairQ_map, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    ← GlobalTheory.DualPairCheck.trace_cA, map_mul, GlobalTheory.DualPairCheck.cA_cA, GlobalTheory.DualPairCheck.cA_incA,
    GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg, neg_mul, map_neg]

theorem finPart_trace {m n : ℕ} (P : Matrix (Fin n) (Fin m) (AE D)) (κ : Mx D m n)
    (hκ : κ.map (finPart D) = 0) : finPart D (Matrix.trace (P * κ)) = 0 := by
  have h : ∀ i j, finPart D (κ i j) = 0 := fun i j => congrFun (congrFun hκ i) j
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul, h, mul_zero, Finset.sum_const_zero]

theorem trace_real {t : AE D} (h : finPart D t = 0) :
    Algebra.trace (AF D.host.F) (AE D) t =
      pairA D.host.F (fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) t)) 0 := by
  have h3 : GlobalTheory.FinTranslate.eInf D * Algebra.trace (AF D.host.F) (AE D) t =
      Algebra.trace (AF D.host.F) (AE D) t := by
    conv_rhs => rw [← GlobalTheory.FinTranslate.smul_eq_self_of_fin h, map_smul, smul_eq_mul]
  refine Prod.ext rfl ?_
  have := congrArg Prod.snd h3
  exact this.symm.trans (zero_mul _)

theorem theta_trace (θ : InfFam D) (hθ : IsInfFam θ) (ρ : D.what₂.Tau) (t : AE D) :
    θ ρ (fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) t) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      ((2 * (θ ρ (infPart D t)).re : ℝ) : ℂ) := by
  have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
  have hA : algebraMap (AF D.host.F) (AE D) (Algebra.trace (AF D.host.F) (AE D) t) = t + cA D t :=
    GlobalTheory.SelfDualLatticeCompare.trace_tensor (AF D.host.F) hcm t
  have hB := congrArg (infPart D) hA
  rw [map_add, infPart_cA] at hB
  have hC : infPart D (algebraMap (AF D.host.F) (AE D) (Algebra.trace (AF D.host.F) (AE D) t)) =
      fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) t) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  rw [← hC, hB, map_add, GlobalTheory.Mem.VolExists.infEmb_sigR hcm (hθ ρ), Complex.add_conj]

theorem theta_pair (θ : InfFam D) (hθ : IsInfFam θ) (ρ : D.what₂.Tau) {m n : ℕ}
    (P : Matrix (Fin n) (Fin m) D.host.E) (κ : Mx D m n) :
    θ ρ (infPart D (Matrix.trace (P.map (incA D) * κ))) =
      Matrix.trace (P.map (tauE D ρ) * compAt θ ρ κ) := by
  have h : ∀ e, θ ρ (infPart D (incA D e)) = tauE D ρ e := fun e => (hθ ρ).1 e
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply, compAt, h]

end GlobalTheory.PhaseReal

theorem GlobalTheory.PhaseReal.phase_eq : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E), adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r), κ.map (finPart D) = 0 → phase ψ V W C C' y κ = Complex.exp (2 * Real.pi * Complex.I * ((∑ τ, 2 * (Matrix.trace ((pairQ W y).map (tauE D τ) * compAt θ τ κ)).re : ℝ) : ℂ)) := by
  intro D V W r C C' hC ψ hψ θ hθ y κ hκ
  unfold phase
  rw [GlobalTheory.PhaseReal.symplO_iso V W C C' hC]
  set t := Matrix.trace ((pairQ W y).map (incA D) * κ) with ht
  have hfin : finPart D t = 0 := GlobalTheory.PhaseReal.finPart_trace _ κ hκ
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  set T := Algebra.trace (AF D.host.F) (AE D) t with hTdef
  have h1 : ψ (-T) = psiInf D.host.F ψ (-(fstA D.host.F T)) := by
    unfold psiInf
    congr 1
    rw [hT]
    refine Prod.ext rfl ?_
    exact neg_zero
  have h2 := hψ.2.2 θ hθ (-(fstA D.host.F T))
  have h3 : ∀ ρ, θ ρ ((-(fstA D.host.F T)) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      -((2 * (Matrix.trace ((pairQ W y).map (tauE D ρ) * compAt θ ρ κ)).re : ℝ) : ℂ) := by
    intro ρ
    rw [TensorProduct.neg_tmul, map_neg, hTdef, GlobalTheory.PhaseReal.theta_trace θ hθ ρ t, ht,
      GlobalTheory.PhaseReal.theta_pair θ hθ ρ]
  rw [h1, h2]
  congr 1
  simp only [h3, Finset.sum_neg_distrib]
  push_cast
  ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermHeisenbergIsotropicCharacter
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedTermTranslate

local infixl:70 " ⬝ " => HMul.hMul

variable {D : D7}

theorem symplOH_isoPart_isoPart (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (hC : IsIsoFrame V C)
    (b a : Mx D W.rank r) : symplOH V W (isoPart V W C b) (isoPart V W C a) = 0 := by
  set X : Mx D r V.rank := (adj D C * V.gram).map (incA D) with hXdef
  have hM : (adj D C * V.gram)ᴴ = V.gram * C := by
    rw [Matrix.conjTranspose_mul, GlobalTheory.MixModel.gram_conjTranspose]
    show V.gram * (Cᴴ)ᴴ = V.gram * C
    rw [Matrix.conjTranspose_conjTranspose]
  have hX0 : X ⬝ GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj X = 0 := by
    have e : GlobalTheory.MixModel.adj X = GlobalTheory.MixModel.rat (V.gram * C) := by
      rw [hXdef, ← hM]; rfl
    rw [e, hXdef]
    show GlobalTheory.MixModel.rat (adj D C * V.gram) ⬝ GlobalTheory.MixModel.rat V.gram⁻¹ ⬝ GlobalTheory.MixModel.rat (V.gram * C) = 0
    rw [← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul]
    have : adj D C * V.gram * V.gram⁻¹ * (V.gram * C) = adj D C * V.gram * C := by
      rw [Matrix.mul_assoc (adj D C * V.gram), ← Matrix.mul_assoc V.gram⁻¹,
        Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul]
    rw [this]
    exact (congrArg GlobalTheory.MixModel.rat hC.2.2).trans GlobalTheory.MixModel.rat_zero
  rw [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace]
  have e2 : isoPart V W C b = b ⬝ X := rfl
  have e3 : isoPart V W C a = a ⬝ X := rfl
  rw [e2, e3, GlobalTheory.MixModel.adj_mul]
  have e4 : GlobalTheory.MixModel.giA V ⬝ (GlobalTheory.MixModel.adj X ⬝ GlobalTheory.MixModel.adj a ⬝ (GlobalTheory.MixModel.gA W ⬝ (b ⬝ X)))
      = (GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj X ⬝ GlobalTheory.MixModel.adj a ⬝ GlobalTheory.MixModel.gA W ⬝ b) ⬝ X := by
    simp only [Matrix.mul_assoc]
  rw [e4, Matrix.trace_mul_comm]
  have e5 : X ⬝ (GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj X ⬝ GlobalTheory.MixModel.adj a ⬝ GlobalTheory.MixModel.gA W ⬝ b)
      = (X ⬝ GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj X) ⬝ (GlobalTheory.MixModel.adj a ⬝ GlobalTheory.MixModel.gA W ⬝ b) := by
    simp only [Matrix.mul_assoc]
  rw [e5, hX0, Matrix.zero_mul, Matrix.trace_zero, map_zero]

theorem symplO_eq_add (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add]
  norm_num

theorem heisO_heisO_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (G : WO S T → ℂ) (u v a : WO S T)
    (hav : symplOH S T a v = 0) :
    heisO ψ S T u (heisO ψ S T v G) a =
      ψ (symplO S T u v) * (ψ (symplOH S T (a + v) u) * G (a + v + u)) := by
  simp only [heisO]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_right_comm a u v]
  congr 2
  rw [GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_add_left, hav, symplO_eq_add,
    GlobalTheory.FinTranslate.symplOH_skew S T v u]
  ring

end GlobalTheory.MixedTermTranslate

namespace GlobalTheory.MixedTermTranslate

theorem term_heisO_isoPart : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r), term ψ V V' W C C' B μ 𝓨 (heisO ψ V W (isoPart V W C κ) G) y = phase ψ V W C C' y κ * term ψ V V' W C C' B μ 𝓨 G y := by
  intro D V V' W r C C' B hs ψ _ μ 𝓨 hμ G hG y κ
  have hμ' : IsCovolOne (GlobalTheory.MixModel.ratMx D W.rank r) μ 𝓨 := hμ
  have hmid : midPart V V' W B 0 = 0 := by
    show HMul.hMul (0 : Matrix (Fin W.rank) (Fin V'.rank) (AE D)) _ = 0
    exact Matrix.zero_mul _
  have iso := symplOH_isoPart_isoPart V W C hs.frame
  obtain ⟨u, hu⟩ : ∃ u, u = isoPart V W C' (Matrix.map y (incA D)) := ⟨_, rfl⟩
  have hterm : ∀ F : WO V W → ℂ, term ψ V V' W C C' B μ 𝓨 F y =
      ∫ s in 𝓨, heisO ψ V W u F (isoPart V W C s) ∂μ := by
    intro F
    show ∫ s in 𝓨, heisO ψ V W _ F (isoPart V W C s + midPart V V' W B 0) ∂μ = _
    rw [hmid, hu]
    simp only [add_zero]
  let Ψ : Mx D W.rank r → ℂ := fun s => ψ (symplOH V W (isoPart V W C s) u) * G (isoPart V W C s + u)
  have hper : ∀ γ ∈ GlobalTheory.MixModel.ratMx D W.rank r, ∀ s, Ψ (γ + s) = Ψ s := by
    rintro _ ⟨q₀, rfl⟩ s
    have e3 : (incA D).toAddMonoidHom.mapMatrix q₀ = q₀.map (incA D) := rfl
    simp only [Ψ]
    rw [e3, GlobalTheory.TwistEquiRat.isoPart_add, add_assoc (isoPart V W C (q₀.map (incA D))),
      ← GlobalTheory.TwistEquiRat.ratW_eq_isoPart V W C q₀, hG.quasi, GlobalTheory.TwistEquiRat.ratW_eq_isoPart V W C q₀,
      GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_add_right, iso, zero_add, AddChar.map_add_eq_mul]
    have h1 : ψ (symplOH V W (isoPart V W C (q₀.map (incA D))) u) *
        ψ (-(symplOH V W (isoPart V W C (q₀.map (incA D))) u)) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    linear_combination (ψ (symplOH V W (isoPart V W C s) u) * G (isoPart V W C s + u)) * h1
  have hph : phase ψ V W C C' y κ = ψ (symplO V W u (isoPart V W C κ)) := by rw [hu]; rfl
  have key : ∀ s, heisO ψ V W u (heisO ψ V W (isoPart V W C κ) G) (isoPart V W C s) =
      phase ψ V W C C' y κ * Ψ (s + κ) := by
    intro s
    rw [heisO_heisO_apply ψ V W G u _ _ (iso s κ), hph]
    show _ = _ * (ψ (symplOH V W (isoPart V W C (s + κ)) u) * G (isoPart V W C (s + κ) + u))
    rw [GlobalTheory.TwistEquiRat.isoPart_add]
  rw [hterm, hterm]
  simp only [key]
  rw [integral_const_mul, GlobalTheory.MixModel.covolOne_integral_add hμ' Ψ hper κ]
  rfl

end GlobalTheory.MixedTermTranslate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermLinearThetaFunctions
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedTerm

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem heisO_add_fun (S T : HSp D) (u : WO S T) (G H : WO S T → ℂ) :
    heisO ψ S T u (G + H) = heisO ψ S T u G + heisO ψ S T u H := by
  funext w
  simp only [heisO, Pi.add_apply, mul_add]

theorem heisO_smul_fun (S T : HSp D) (u : WO S T) (c : ℂ) (G : WO S T → ℂ) :
    heisO ψ S T u (c • G) = c • heisO ψ S T u G := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem continuous_isoPart (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    Continuous (isoPart V W C) := by
  unfold isoPart
  exact continuous_id.matrix_mul continuous_const

theorem integrableOn_heisO (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hψ : IsStdChar D ψ (-1)) {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (h : IsCovolOne (ratMx D W.rank r) μ 𝓨) {G : WO V W → ℂ} (hG : IsThetaFunO ψ V W G) (u a : WO V W) :
    IntegrableOn (fun z => heisO ψ V W u G (isoPart V W C z + a)) 𝓨 μ := by
  obtain ⟨-, -, hvol⟩ := h
  obtain ⟨c, hc⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hG
  have hcont : Continuous (fun z => heisO ψ V W u G (isoPart V W C z + a)) :=
    (GlobalTheory.HeisOrtho.continuous_heisO hψ.1 hG.cont u).comp ((continuous_isoPart V W C).add continuous_const)
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  have hfin : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.one_lt_top⟩
  refine Integrable.of_bound hcont.aestronglyMeasurable c (Filter.Eventually.of_forall fun z => ?_)
  rw [GlobalTheory.HeisOrtho.norm_heisO hψ.1]
  exact hc _

theorem term_linear : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ G H : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W H → term ψ V V' W C C' B μ 𝓨 (G + H) y = term ψ V V' W C C' B μ 𝓨 G y + term ψ V V' W C C' B μ 𝓨 H y) ∧ ∀ (c : ℂ) (G : WO V W → ℂ), IsThetaFunO ψ V W G → term ψ V V' W C C' B μ 𝓨 (c • G) y = c * term ψ V V' W C C' B μ 𝓨 G y := by
  intro D V V' W r C C' B ψ hψ μ 𝓨 h y
  have key : ∀ G, IsThetaFunO ψ V W G → IntegrableOn
      (fun z => heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) G (isoPart V W C z + midPart V V' W B 0)) 𝓨 μ :=
    fun G hG => integrableOn_heisO V W C hψ h hG _ _
  refine ⟨fun G H hG hH => ?_, fun c G hG => ?_⟩
  · simp only [term, res, heisO_add_fun, Pi.add_apply]
    exact integral_add (key G hG) (key H hH)
  · simp only [term, res, heisO_smul_fun, Pi.smul_apply, smul_eq_mul]
    first
      | exact integral_const_mul c _
      | exact integral_mul_left c _

end GlobalTheory.MixedTerm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrthogonalSummandProjectionMemLatticeOfSplitsStatement
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonalSummandProjection_mem_lattice_of_splits : ∀ {D : D7} {S A B : HSp D} (o : OrthDec S A B) {L : Lat S} {LA : Lat A} {LB : Lat B}, (∀ z : Fin B.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV B LB (· = v)) → z ∈ LB) → (∀ v, OrthAt o L LA LB v) → ∀ t ∈ L, o.qB *ᵥ t ∈ LB := by
  first | exact @GlobalTheory.FinPl.projB_mem_of_orthAt | exact GlobalTheory.FinPl.projB_mem_of_orthAt | (intros; apply GlobalTheory.FinPl.projB_mem_of_orthAt <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PositiveInducedModuleShiftStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_induced_module_shift : GlobalTheory.Published.LanglandsClassification → ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε) (h : 0 < I.a) (χ : Fin n → ℂ), (∀ (k : ℕ) v, IsKFin ε I.ρ v → ∃ N : ℕ, actU ε I.ρ ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) v = 0) → ∃ (I' : IndModule ε) (h' : 0 < I'.a), I'.j ⟨0, h'⟩ = 1 ∧ (I'.s ⟨0, h'⟩).re = (I.s ⟨0, h⟩).re ∧ (∀ (k : ℕ) v, IsKFin ε I'.ρ v → ∃ N : ℕ, actU ε I'.ρ ((etr (Egl n) (k + 1) - algebraMap ℂ _ (gelfVal χ (k + 1))) ^ N) v = 0) := by
  first | exact @GlobalTheory.RealInd.Stages.exists_first_step_one | exact GlobalTheory.RealInd.Stages.exists_first_step_one | (intros; apply GlobalTheory.RealInd.Stages.exists_first_step_one <;> assumption)
end

