import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0254
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0253
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiffQuotientBesselMapTendsto
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0255
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BallVolSuccSq
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.GaugeQuot.BallProd

theorem volume_ball_eq_ballVol {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] {d : ℕ}
    (hd : Module.finrank ℝ F = d) (r : ℝ) :
    (volume : Measure F) (Metric.ball 0 r) = ballVol d r := by
  subst hd
  unfold ballVol
  have h := (stdOrthonormalBasis ℝ F).measurePreserving_repr
  rw [← h.measure_preimage measurableSet_ball.nullMeasurableSet]
  congr 1
  ext x
  simp

theorem prod_region_eq_ballVol (P Q : ℕ) (r : ℝ) (hr : 0 < r) :
    ((volume : Measure (ℝ × Sp P Q)).prod
      (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2)))))
      {p | p.1.1 ^ 2 + ∑ i, ‖p.1.2 i‖ ^ 2 + ‖p.2‖ ^ 2 < r ^ 2} = ballVol ((P + Q + 1) ^ 2) r := by
  have h0 := GlobalTheory.volume_preserving_ofLp_complex (Fin P ⊕ Fin Q)
  have h1 := ((MeasurePreserving.id (volume : Measure ℝ)).prod h0).comp
    (WithLp.volume_preserving_ofLp ℝ (EuclideanSpace ℂ (Fin P ⊕ Fin Q)))
  have h2 := (h1.prod (MeasurePreserving.id
      (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2)))))).comp
    (WithLp.volume_preserving_ofLp (WithLp 2 (ℝ × EuclideanSpace ℂ (Fin P ⊕ Fin Q)))
      (EuclideanSpace ℝ (Fin ((P + Q) ^ 2))))
  have hm : MeasurableSet {p : (ℝ × Sp P Q) × EuclideanSpace ℝ (Fin ((P + Q) ^ 2)) |
      p.1.1 ^ 2 + ∑ i, ‖p.1.2 i‖ ^ 2 + ‖p.2‖ ^ 2 < r ^ 2} :=
    (isOpen_lt (by fun_prop) continuous_const).measurableSet
  rw [Measure.volume_eq_prod, ← h2.measure_preimage hm.nullMeasurableSet,
    ← volume_ball_eq_ballVol (F := WithLp 2 (WithLp 2 (ℝ × EuclideanSpace ℂ (Fin P ⊕ Fin Q)) ×
      EuclideanSpace ℝ (Fin ((P + Q) ^ 2))))]
  · congr 1
    ext x
    rw [mem_ball_zero_iff, ← sq_lt_sq₀ (norm_nonneg _) hr.le, WithLp.prod_norm_sq_eq_of_L2,
      WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq]
    simp
  · rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq, Module.finrank_prod,
      (WithLp.linearEquiv 2 ℝ _).finrank_eq, Module.finrank_prod,
      (WithLp.linearEquiv 2 ℝ (Fin P ⊕ Fin Q → ℂ)).finrank_eq, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
    ring

theorem ballVol_succ_sq (P Q : ℕ) (r : ℝ) (hr : 0 < r) :
    ballVol ((P + Q + 1) ^ 2) r = (2 : ℝ≥0∞) ^ (P + Q) *
      ((volume : Measure (ℝ × Sp P Q)).prod
        (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2)))))
        {p | tanSq p.1 + ‖p.2‖ ^ 2 < r ^ 2} := by
  have hs : (√2 : ℝ) ≠ 0 := by positivity
  have hfin : Module.finrank ℝ (Sp P Q) = 2 * (P + Q) := by
    rw [Module.finrank_pi_fintype]; simp [Complex.finrank_real_complex]; ring
  have h0 : MeasurePreserving (fun y : Sp P Q => (√2 : ℝ) • y) volume
      (((2 : ℝ≥0∞) ^ (P + Q))⁻¹ • volume) := by
    refine ⟨by fun_prop, ?_⟩
    rw [Measure.map_addHaar_smul _ hs, hfin, pow_mul, Real.sq_sqrt (by norm_num),
      abs_of_pos (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num)]
    simp
  have hne : ((2 : ℝ≥0∞) ^ (P + Q)) ≠ 0 := by simp
  have hnt : ((2 : ℝ≥0∞) ^ (P + Q)) ≠ ⊤ := by simp
  haveI : SFinite (((2 : ℝ≥0∞) ^ (P + Q))⁻¹ • (volume : Measure (Sp P Q))) := inferInstance
  have h1 := ((MeasurePreserving.id (volume : Measure ℝ)).prod h0).prod (MeasurePreserving.id
      (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2)))))
  have hm : MeasurableSet {p : (ℝ × Sp P Q) × EuclideanSpace ℝ (Fin ((P + Q) ^ 2)) |
      p.1.1 ^ 2 + ∑ i, ‖p.1.2 i‖ ^ 2 + ‖p.2‖ ^ 2 < r ^ 2} :=
    (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have h2 := h1.measure_preimage hm.nullMeasurableSet
  rw [Measure.prod_smul_right, Measure.prod_smul_left, Measure.smul_apply,
    ← Measure.volume_eq_prod, prod_region_eq_ballVol P Q r hr, smul_eq_mul] at h2
  have h3 : {p : (ℝ × Sp P Q) × EuclideanSpace ℝ (Fin ((P + Q) ^ 2)) |
      tanSq p.1 + ‖p.2‖ ^ 2 < r ^ 2} =
      Prod.map (Prod.map id fun y : Sp P Q => (√2 : ℝ) • y) id ⁻¹'
      {p | p.1.1 ^ 2 + ∑ i, ‖p.1.2 i‖ ^ 2 + ‖p.2‖ ^ 2 < r ^ 2} := by
    ext p
    simp [tanSq, norm_smul, mul_pow, Finset.mul_sum, mul_add]
  rw [h3, h2, ← mul_assoc, ENNReal.mul_inv_cancel hne hnt, one_mul]

end GlobalTheory.GaugeQuot.BallProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionalEquivariantUnipotentCharacterStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselFunctional_equivariant_unipotent_character : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, IsSPsiEquiv z (psiGen k r z c) π (Afun (psiGen k r z c) π μS σ u v ξ) := by
  first | exact @GlobalTheory.SgInf.Afun_isSPsiEquiv | exact GlobalTheory.SgInf.Afun_isSPsiEquiv | (intros; apply GlobalTheory.SgInf.Afun_isSPsiEquiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMapPairingBoundStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_map_pairing_bound : Hyps → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (R : Rep D.R.k D.R.rS) (h : ℝ) (l : R.H → W.Wp) (l' : R.H → W.Wq) (dd : ℝ), cdScaleTie D → GoodW D τ w w' θ W → R.IsDS (epsSH D.R) lam → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) R.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') R.σ W.π' l' → 0 < dd → (∀ v ∈ R.sm, l2SG W.νS (fun g => l (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → (∀ v ∈ R.sm, l2SG W.νS' (fun g => l' (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → ∃ A : LocS W, GoodS D lam A := by
  first | exact @GlobalTheory.DatumOfPeriods.exists_goodS | exact GlobalTheory.DatumOfPeriods.exists_goodS | (intros; apply GlobalTheory.DatumOfPeriods.exists_goodS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupIntegralEqInnerBesselFormStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselSubgroupIntegral_eq_inner_besselForm : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ v ∈ DD σ w, ∀ ξ : Wp, ∫ t, ⟪v, σ (Matrix.of t)⁻¹ v⟫_ℂ * ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ ∂μS = ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ := by
  first | exact @GlobalTheory.SgInf.SInt.sint_eq_inner_be | exact GlobalTheory.SgInf.SInt.sint_eq_inner_be | (intros; apply GlobalTheory.SgInf.SInt.sint_eq_inner_be <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockPerpEmbeddingOfDiagonalFrame
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

namespace GlobalTheory.PerpSort

theorem herm_comp {n P Q : ℕ} {ε : Fin n → Bool} {f : Fin P ⊕ Fin Q ≃ Fin n} (hf : Sorts ε f)
    (x y : Fin n → ℂ) : herm (x ∘ f) (y ∘ f) = star y ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) := by
  obtain ⟨h1, h2⟩ := hf
  rw [dotProduct, ← Equiv.sum_comp f, Fintype.sum_sum_type, herm]
  simp only [Function.comp_apply, Pi.star_apply, Formalism.REAL.Jm, mulVec_diagonal, h1, h2, if_true,
    Bool.false_eq_true, if_false, one_mul, neg_one_mul, mul_neg, Finset.sum_neg_distrib, ← sub_eq_add_neg]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem form_self {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = (GlobalTheory.GaussMean.qEps ε x : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Formalism.REAL.Jm, mulVec_diagonal, GlobalTheory.GaussMean.qEps]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  have hx : star (x i) * x i = ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast; ring
  rw [mul_left_comm, hx]
  split_ifs <;> push_cast <;> ring

theorem mat_symm {n P Q : ℕ} {ε : Fin n → Bool} {f : Fin P ⊕ Fin Q ≃ Fin n} (hf : Sorts ε f)
    (k : Formalism.REAL.UJ ε) : (hf.equiv.symm k).mat = (Formalism.MainNotions.S.uMat k).submatrix f f := by
  have h := hf.umat_equiv (hf.equiv.symm k)
  rw [ContinuousMulEquiv.apply_symm_apply] at h
  ext i j
  have e := congrFun (congrFun h (f i)) (f j)
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] at e
  exact e.symm

theorem act_symm {n P Q : ℕ} {ε : Fin n → Bool} {f : Fin P ⊕ Fin Q ≃ Fin n} (hf : Sorts ε f)
    (k : Formalism.REAL.UJ ε) (x : Fin n → ℂ) :
    act (hf.equiv.symm k) (x ∘ f) = (Formalism.MainNotions.S.uMat k *ᵥ x) ∘ f := by
  rw [act, mat_symm hf, Matrix.submatrix_mulVec_equiv, Function.comp_assoc, f.self_comp_symm,
    Function.comp_id]

private theorem of_fin_cases_mulVec {n : ℕ} (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ)
    (w : Fin (n + 1) → ℂ) :
    (Matrix.of fun i j => Fin.cases (motive := fun _ => ℂ) (x₀ i) (fun k => B i k) j) *ᵥ w =
      w 0 • x₀ + B *ᵥ fun k => w k.succ := by
  ext i
  simp only [mulVec, dotProduct, Fin.sum_univ_succ, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem exists_mulVec_eq {n : ℕ} (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool)
    (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ)
    (h0 : star x₀ ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x₀) ≠ 0) (h1 : star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0)
    (h2 : Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε') (y : Fin (n + 1) → ℂ)
    (hy : star x₀ ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0) : ∃ u, B *ᵥ u = y := by
  set J := Formalism.REAL.Jm ε
  set M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.of fun i j => Fin.cases (motive := fun _ => ℂ) (x₀ i) (fun k => B i k) j with hM
  have hMv : ∀ w, M *ᵥ w = w 0 • x₀ + B *ᵥ fun k : Fin n => w k.succ := fun w => of_fin_cases_mulVec x₀ B w
  have key : ∀ t : Fin n → ℂ, star x₀ ⬝ᵥ (J *ᵥ (B *ᵥ t)) = 0 := by
    intro t
    rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, h1, zero_dotProduct]
  have hval : ∀ w, star x₀ ⬝ᵥ (J *ᵥ (M *ᵥ w)) = w 0 * (star x₀ ⬝ᵥ (J *ᵥ x₀)) := by
    intro w
    rw [hMv, Matrix.mulVec_add, dotProduct_add, key, add_zero, Matrix.mulVec_smul,
      dotProduct_smul, smul_eq_mul]
  have hinj : Function.Injective M.mulVec := by
    intro a b hab
    have hz : M *ᵥ (a - b) = 0 := by
      rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr hab
    have hw0 : (a - b) 0 = 0 := by
      have e := hval (a - b)
      rw [hz, Matrix.mulVec_zero, dotProduct_zero] at e
      exact (mul_eq_zero.mp e.symm).resolve_right h0
    have hBt : B *ᵥ (fun k : Fin n => (a - b) k.succ) = 0 := by
      have e := hMv (a - b)
      rw [hz, hw0, zero_smul, zero_add] at e
      exact e.symm
    have ht : (fun k : Fin n => (a - b) k.succ) = 0 := by
      have hJ' : Formalism.REAL.Jm ε' *ᵥ (fun k : Fin n => (a - b) k.succ) = 0 := by
        rw [← h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBt, Matrix.mulVec_zero,
          Matrix.mulVec_zero]
      rw [← Matrix.one_mulVec (fun k : Fin n => (a - b) k.succ), ← Formalism.REAL.Jm_mul_self ε',
        ← Matrix.mulVec_mulVec, hJ', Matrix.mulVec_zero]
    rw [← sub_eq_zero]
    funext i
    refine Fin.cases hw0 (fun k => ?_) i
    exact congrFun ht k
  have hsurj : Function.Surjective M.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  obtain ⟨w, hw⟩ := hsurj y
  have hw0 : w 0 = 0 := by
    have e := hval w
    rw [hw, hy] at e
    exact (mul_eq_zero.mp e.symm).resolve_right h0
  refine ⟨fun k : Fin n => w k.succ, ?_⟩
  rw [← hw, hMv, hw0, zero_smul, zero_add]

theorem isPerpEmb_of_sorts : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (s : Bool) (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ) (j : Formalism.REAL.UJ ε' → Formalism.REAL.UJ ε), GlobalTheory.GaussMean.qEps ε x₀ = GlobalTheory.GaussMean.sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → (∀ g, Formalism.MainNotions.S.uMat (j g) *ᵥ x₀ = x₀ ∧ Formalism.MainNotions.S.uMat (j g) * B = B * Formalism.MainNotions.S.uMat g) → ∀ (P Q P' Q' : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin (n + 1)) (f' : Fin P' ⊕ Fin Q' ≃ Fin n) (hf : Sorts ε f) (hf' : Sorts ε' f'), IsPerpEmb (fun i => x₀ (f i)) (B.submatrix f f') (fun g => hf.equiv.symm (j (hf'.equiv g))) := by
  intro n ε ε' s x₀ B j hq h1 h2 hj P Q P' Q' f f' hf hf'
  change IsPerpEmb (x₀ ∘ f) _ _
  have hsub : ∀ u : Fin P' ⊕ Fin Q' → ℂ, B.submatrix f f' *ᵥ u = (B *ᵥ (u ∘ f'.symm)) ∘ f :=
    fun u => Matrix.submatrix_mulVec_equiv _ _ _ _
  have hc : star x₀ ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x₀) ≠ 0 := by
    rw [form_self, hq]
    cases s <;> simp [GlobalTheory.GaussMean.sgn]
  refine ⟨fun u v => ?_, fun y => ⟨fun h0 => ?_, ?_⟩, fun g => ?_⟩
  · have e := herm_comp hf' (u ∘ f'.symm) (v ∘ f'.symm)
    rw [Function.comp_assoc, f'.symm_comp_self, Function.comp_id, Function.comp_assoc,
      f'.symm_comp_self, Function.comp_id] at e
    rw [e, hsub, hsub, herm_comp hf, ← h2, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  · have e := herm_comp hf (y ∘ f.symm) x₀
    rw [Function.comp_assoc, f.symm_comp_self, Function.comp_id] at e
    rw [e] at h0
    obtain ⟨u, hu⟩ := exists_mulVec_eq ε ε' x₀ B hc h1 h2 _ h0
    refine ⟨u ∘ f', ?_⟩
    rw [hsub, Function.comp_assoc, f'.self_comp_symm, Function.comp_id, hu, Function.comp_assoc,
      f.symm_comp_self, Function.comp_id]
  · rintro ⟨u, rfl⟩
    rw [hsub, herm_comp hf, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, h1,
      zero_dotProduct]
  · obtain ⟨hfix, hcomm⟩ := hj (hf'.equiv g)
    refine ⟨?_, fun u => ?_⟩
    · show act (hf.equiv.symm (j (hf'.equiv g))) (x₀ ∘ f) = x₀ ∘ f
      rw [act_symm hf, hfix]
    · show act (hf.equiv.symm (j (hf'.equiv g))) _ = _
      have e := act_symm hf' (hf'.equiv g) (u ∘ f'.symm)
      rw [ContinuousMulEquiv.symm_apply_apply, Function.comp_assoc, f'.symm_comp_self,
        Function.comp_id] at e
      rw [hsub, hsub, act_symm hf, Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, e,
        Function.comp_assoc, f'.self_comp_symm, Function.comp_id]

end GlobalTheory.PerpSort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliTransportUnitaryConjStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_transport_unitary_conj : PI.UnitaryGroupMassFormula.CapelliEig.CapTransport := by
  first | exact @GlobalTheory.capelli_transport_conj | exact GlobalTheory.capelli_transport_conj | (intros; apply GlobalTheory.capelli_transport_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ComplexCoordinatesMeasurePreservingStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_coordinates_measure_preserving : ∀ (ι : Type) [Fintype ι] (n : ℕ), ∃ T : (ι → Fin n → ℂ) ≃ₜ+ (ι × Fin n × Bool → ℝ), MeasurePreserving T volume volume ∧ ∀ y v i, T y (v, i, true) = (y v i).re ∧ T y (v, i, false) = (y v i).im := by
  first | exact @GlobalTheory.ReImVolume.exists_reIm_measurePreserving | exact GlobalTheory.ReImVolume.exists_reIm_measurePreserving | (intros; apply GlobalTheory.ReImVolume.exists_reIm_measurePreserving <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DataConditionsOfGlobalAndRealRows
section
noncomputable section

namespace GlobalTheory.Diag.PG

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem data_of_rows (eps CD : ℝ) (he : 0 < eps) (he' : eps < 1 / 52) (hCD : 3 ≤ CD) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (Cg C0 : ℝ), Glob0 D x eps CD Cg → Nodes D x eps → ArithmeticConditionsOfDatum D →
      DuWin D C0 → StandingNumericalData D C0 := by
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.globalRankNumberBounds_size_comparisons eps CD he he' hCD 1 one_pos
  refine ⟨max x1 1, fun x hx D Cg C0 hG hN hA hW => ?_⟩
  have hxx1 : x1 ≤ x := le_trans (le_max_left _ _) hx
  have hxone : 1 ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨-, -, -, h12, -⟩ := hx1 x hxx1 _ _ _ _ _ hG.nums
  have hk : 5 ≤ D.R.k := by
    have := D.R.two_le_m
    have := D.R.m_add_three_le_k
    omega
  have hm2 := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl

  have hF : ∀ {n : ℕ} (g : Fin n → ℚ) (a b : ℕ) (ha : a < n) (hb : b < n), a = b →
      g ⟨a, ha⟩ = g ⟨b, hb⟩ := by
    intro n g a b ha hb h
    subst h
    rfl

  have huO : ∀ u τ (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ D.R.k),
      Formalism.MainNotions.S.uOne D u τ i = (((D.hcW u τ).u ⟨i - 1, by omega⟩ : ℚ) : ℝ) := by
    intro u τ i h1 h2
    unfold Formalism.MainNotions.S.uOne Formalism.MainNotions.S.uS
    rw [dif_pos ⟨h1, h2⟩]
  have hvO : ∀ τ (l : ℕ) (h1 : 1 ≤ l) (h2 : l ≤ D.R.k - 1),
      Formalism.MainNotions.S.vOne D τ l = (((D.hc τ).v ⟨l - 1, by omega⟩ : ℚ) : ℝ) := by
    intro τ l h1 h2
    unfold Formalism.MainNotions.S.vOne
    rw [dif_pos ⟨h1, h2⟩]
  have hbO : ∀ τ, Formalism.MainNotions.S.bOne D τ 1 = bFirst D τ := by
    intro τ
    unfold Formalism.MainNotions.S.bOne bFirst
    rw [dif_pos ⟨le_rfl, by have := D.R.two_le_m; omega⟩]
  have hu1 : ∀ u τ, Formalism.MainNotions.S.uOne D u τ 1 = uFirst D τ := by
    intro u τ
    rw [huO u τ 1 le_rfl (by omega)]
    unfold uFirst
    exact congrArg (fun q : ℚ => (q : ℝ))
      ((hF _ (1 - 1) 0 _ (by omega) (by norm_num)).trans (D.hcW_first u τ (by omega)))
  have huk : ∀ u τ, Formalism.MainNotions.S.uOne D u τ D.R.k = uLast D τ := by
    intro u τ
    rw [huO u τ D.R.k (by omega) le_rfl]
    unfold uLast
    exact congrArg (fun q : ℚ => (q : ℝ)) (D.hcW_last u τ (by omega))
  have hv1 : ∀ τ, Formalism.MainNotions.S.vOne D τ 1 = vFirst D τ := by
    intro τ
    rw [hvO τ 1 le_rfl (by omega)]
    unfold vFirst
    exact congrArg (fun q : ℚ => (q : ℝ)) (hF _ _ _ _ _ (by norm_num))
  have hvk : ∀ τ, Formalism.MainNotions.S.vOne D τ (D.R.k - 1) = vLast D τ := by
    intro τ
    rw [hvO τ (D.R.k - 1) (by omega) le_rfl]
    unfold vLast
    exact congrArg (fun q : ℚ => (q : ℝ)) (hF _ _ _ _ _ (by omega))
  have hDel : (0 : ℝ) < D.s.Del := by exact_mod_cast D.s.Del_pos
  have hkDel : (0 : ℝ) ≤ (D.R.k : ℝ) * D.s.Del := mul_nonneg (Nat.cast_nonneg _) hDel.le

  have hbx : 1 ≤ bx x eps := by
    unfold bx
    exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hg : ∀ i, 2 ≤ D.host.g i := by
    intro i
    have h := (hG.g_win i).1
    have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
    have h5 : (5 : ℝ) ≤ (D.R.k : ℝ) * bx x eps := by nlinarith
    have h2 : (2 : ℝ) ≤ ((D.R.k : ℝ) * bx x eps) ^ 8 :=
      calc (2 : ℝ) ≤ 5 := by norm_num
        _ ≤ (D.R.k : ℝ) * bx x eps := h5
        _ ≤ ((D.R.k : ℝ) * bx x eps) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
    exact_mod_cast h2.trans h
  unfold Formalism.MainNotions.S.StandingNumericalData
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hW, hA.2.1, hA.2.2.1, hA.2.2.2, ?_⟩
  ·
    intro τ l h1 h2
    rw [hvO τ l h1 h2]
    exact hG.cloud τ ⟨l - 1, by omega⟩
  ·
    intro u l h1 h2
    have key : ∀ τ, Formalism.MainNotions.S.uOne D u τ (l + 1) = Formalism.MainNotions.S.vOne D τ l - 1 / 2 -
        (if D.s.letter u ⟨l - 1, by omega⟩ then (D.s.Del : ℝ) else 0) := by
      intro τ
      rw [huO u τ (l + 1) (by omega) (by omega), hvO τ l h1 (by omega)]
      have e := D.s.u_letter u τ (l - 1) (by omega)
      rw [D.hcW_v u τ] at e
      have e' : (D.hcW u τ).u ⟨l + 1 - 1, by omega⟩ = (D.hcW u τ).u ⟨l - 1 + 1, by omega⟩ :=
        hF _ _ _ _ _ (by omega)
      rw [e', e]
      split_ifs <;> push_cast <;> ring
    by_cases hL : D.s.letter u ⟨l - 1, by omega⟩ = true
    · right
      intro τ
      rw [key τ, if_pos hL]
    · left
      intro τ
      rw [key τ, if_neg hL]
      ring
  ·
    intro u τ
    rw [hu1 u τ, hv1 τ]
    by_cases ht : Top D τ
    · have h1 := (hN.top τ ht).1
      have h2 := (hG.cloud τ ⟨0, by omega⟩).2
      have hvF : vFirst D τ = (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) := by
        unfold vFirst
        rfl
      rw [hvF]
      nlinarith
    · exact (hG.off τ ht).1
  ·
    intro u τ ht
    rw [hu1 u τ, hv1 τ]
    exact (hG.off τ ht).2.1
  ·
    intro u τ ht
    rw [huk u τ, hvk τ]
    exact (hG.off τ ht).2.2
  ·
    intro τ ht
    unfold Formalism.MainNotions.S.bTop
    rw [huk D.u₀ τ, hbO τ]
    obtain ⟨-, -, h3, h4⟩ := hN.top τ ht
    constructor <;> linarith
  ·
    intro u τ
    constructor
    · intro i hi
      have hl : Formalism.MainNotions.S.lamS D.R (D.hc τ) ⟨i, by omega⟩ = (((D.hcW u τ).v ⟨i, by omega⟩ : ℚ) : ℝ) := by
        unfold Formalism.MainNotions.S.lamS
        rw [dif_pos (show i < D.R.k - 1 by omega), D.hcW_v u τ]
      rw [hl]
      unfold Formalism.MainNotions.S.uS
      exact ⟨by exact_mod_cast (D.hcW u τ).u_gt_v ⟨i, by omega⟩,
        by exact_mod_cast (D.hcW u τ).v_gt_u ⟨i, by omega⟩⟩
    · intro h
      have hm : 0 < D.R.m := by
        have := D.R.two_le_m
        omega
      have hl : Formalism.MainNotions.S.lamS D.R (D.hc τ) ⟨D.R.k - 1, by omega⟩ =
          -(((D.hcW u τ).b ⟨0, hm⟩ : ℚ) : ℝ) := by
        unfold Formalism.MainNotions.S.lamS
        rw [dif_neg (show ¬ (D.R.k - 1 < D.R.k - 1) by omega),
          dif_pos (show D.R.k - 1 - (D.R.k - 1) < D.R.m by omega), D.hcW_b u τ]
        exact congrArg (fun q : ℚ => -(q : ℝ)) (hF _ _ _ _ _ (by simp))
      rw [hl]
      unfold Formalism.MainNotions.S.uS
      exact_mod_cast (D.hcW u τ).u_last_gt h hm
  ·
    intro u u' hne τ heq
    have hl : D.s.letter u ≠ D.s.letter u' := fun h => hne (D.s.letter_inj h)
    obtain ⟨⟨j, hj⟩, hjl⟩ := Function.ne_iff.mp hl
    have e := congrFun heq ⟨j + 1, by omega⟩
    simp only [Formalism.MainNotions.S.uS] at e
    have e' : (D.hcW u τ).u ⟨j + 1, by omega⟩ = (D.hcW u' τ).u ⟨j + 1, by omega⟩ := by
      exact_mod_cast e
    rw [D.s.u_letter u τ j hj, D.s.u_letter u' τ j hj, D.hcW_v, D.hcW_v] at e'
    have hQ := D.s.Del_pos
    cases h1 : D.s.letter u ⟨j, hj⟩ <;> cases h2 : D.s.letter u' ⟨j, hj⟩ <;>
      simp only [h1, h2] at e' hjl <;> simp at e' hjl <;> linarith
  ·
    intro u
    exact ⟨hA.1 u, Formalism.MainNotions.S.T_mod D u⟩
  ·
    intro u
    exact Formalism.MainNotions.S.ne_of_mod (hg 0) (hg 1) (Formalism.MainNotions.S.T_mod D u)

end GlobalTheory.Diag.PG

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiffQuotientBesselMapTendstoStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diffQuotient_besselMap_tendsto : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (z : Fin (2 * r + k + 1) → ℂ) (ψ : Mat k r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (l : H → Wp) (x : H) (X : Mat k r), IsURepOn (GG k r) σ → IsBesselMapSm z ψ σ π l → IsSmoothVec σ x → InLieHpk k r X → Filter.Tendsto (fun t : ℝ => l ((t : ℂ)⁻¹ • (σ (NormedSpace.exp ((t : ℂ) • X)) x - x))) (nhdsWithin 0 {0}ᶜ) (nhds (l (dsig σ X x))) ∧ ContinuousOn (fun g => l (σ g x)) (GG k r) ∧ ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ GG k r ∧ σ (NormedSpace.exp ((t : ℂ) • X)) x - x = ∫ u in (0 : ℝ)..t, σ (NormedSpace.exp ((u : ℂ) • X)) (dsig σ X x) := by
  first | exact @GlobalTheory.diffQuot_bessel | exact GlobalTheory.diffQuot_bessel | (intros; apply GlobalTheory.diffQuot_bessel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDatumOfTwoCongruentFramesStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_datum_of_two_congruent_frames : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (P : FPair H r) (t : Term V M r), H.IsTerm t → t.T = P.A.T → t.T' = P.B.T → Tri E P.A.f t.f → Tri E P.B.f t.f' → ∃ d : Datum P, IsTermOver P d t := by
  first | exact @GlobalTheory.LocOver.TermOver.exists_datum | exact GlobalTheory.LocOver.TermOver.exists_datum | (intros; apply GlobalTheory.LocOver.TermOver.exists_datum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralUnipotentLiftAntidiagonalStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_unipotent_lift_antidiagonal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (l : InfinitePlace E → ℝ), l ∈ skewLat (σ : E →+* E) (dInv E (2 * (r - a.val))) (s a ^ 2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inr (.inr (.inr a))) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inr (.inr (.inr a))) → degB r β ≤ degB r (.inr (.inr (.inr a))) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  first | exact @GlobalTheory.SnMass.VolN.exists_lift_antidiag | exact GlobalTheory.SnMass.VolN.exists_lift_antidiag | (intros; apply GlobalTheory.SnMass.VolN.exists_lift_antidiag <;> assumption)
end

