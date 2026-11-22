import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0362
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import GroundTheory.AutomorphicForms.Bundle0020
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0352
import GroundTheory.AutomorphicForms.AnisotropicHeight
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0358
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0010
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0066
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValZpowIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0320

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleLeviTransportStatement
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicInd_equiv_levi_transport : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W), Nonempty ((parInd e ρ).Equiv (parabolicInd k N β (ρ.comp φ.symm.toMonoidHom))) := by
  first | exact @GlobalTheory.CompanionTheory.ParIndBridge.parInd_equiv_parabolicInd | exact GlobalTheory.CompanionTheory.ParIndBridge.parInd_equiv_parabolicInd | (intros; apply GlobalTheory.CompanionTheory.ParIndBridge.parInd_equiv_parabolicInd <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIntersectionConjugateStatement
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_intersection_conjugate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ (e' : (Σ j, m' j) ≃ Fin N) (γ : Fin N → ℕ), (∀ x y, γ x < γ y ↔ blk e' x < blk e' y) → ∀ (φ' : Levi k m' ≃* levi k N γ), (∀ g, ((φ' g : levi k N γ) : GL (Fin N) k) = leviEmb k e' g) → ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W) (w : Equiv.Perm (Fin N)), ∃ (f : ∀ i, (Σ j, Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)) ≃ m i) (g : ∀ j, (Σ i, Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)) ≃ m' j), Nonempty (Representation.Equiv ((indRep (cellLeviSub k β γ w) (normInducing (ρ.comp φ.symm.toMonoidHom) γ w)).comp φ'.toMonoidHom) (cellFunctor f g ρ)) := by
  first | exact @GlobalTheory.CompanionTheory.GeomCell.cell_iso | exact GlobalTheory.CompanionTheory.GeomCell.cell_iso | (intros; apply GlobalTheory.CompanionTheory.GeomCell.cell_iso <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsEqLogIdeleModuleStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_abs_eq_log_idele_module : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (s : (Ad E)ˣ), logAbs (s : Ad E) = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E s : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.logAbs_eq_log_ideleModule | exact GlobalTheory.CompanionTheory.TorusCh.logAbs_eq_log_ideleModule | (intros; apply GlobalTheory.CompanionTheory.TorusCh.logAbs_eq_log_ideleModule <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowerMulJG
section
noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.BigCell

open PositivityTheory.Rg.Sw

variable {n : ℕ}

theorem JJ_inG : InG (JJ n) := by
  have hc : (JJ n)ᴴ = -JJ n := by
    unfold JJ
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg]
  show (JJ n)ᴴ * JJ n * JJ n = JJ n
  rw [hc, Matrix.mul_assoc, JJ_mul_JJ]
  simp

def JG : GR n :=
  ⟨⟨JJ n, -JJ n, by simp [JJ_mul_JJ], by simp [JJ_mul_JJ]⟩, JJ_inG⟩

theorem lower_mul_JG (y : GR n) :
    (mR (y * JG)).toBlocks₂₁ = -(mR y).toBlocks₂₂ := by
  have h : mR (y * JG) = mR y * JJ n := rfl
  rw [h, ← Matrix.fromBlocks_toBlocks (mR y)]
  unfold JJ
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  simp

theorem dense_bigCell₂₂ : ∀ n : ℕ, Dense {y : GR n | ((mR y).toBlocks₂₂).det ≠ 0} := by
  intro n
  have hset : {y : GR n | ((mR y).toBlocks₂₂).det ≠ 0} =
      (fun y => y * (JG (n := n))) ⁻¹' {y : GR n | ((mR y).toBlocks₂₁).det ≠ 0} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, lower_mul_JG, Matrix.det_neg]
    constructor
    · intro h
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) h
    · intro h h0
      exact h (by rw [h0, mul_zero])
  rw [hset]
  exact (dense_bigCell n).preimage (isOpenMap_mul_right _)

end GlobalTheory.CompanionTheory.BigCell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientIntegrableSquare
section
noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.GodementCoeff

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
  [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure]
  [ν.IsMulRightInvariant] {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

private theorem integrableOn_and_setIntegral_sq_le_of_isU (ρ : Γ → (B →L[ℂ] B)) (hρ : IsU ρ) (v : B)
    (hm : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (b : B) {s : Set Γ} (hs : MeasurableSet s)
    (hs' : ν s ≠ ⊤) :
    IntegrableOn (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) s ν ∧
      ∫ g in s, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 := by
  have hcont : Continuous fun g => ⟪b, ρ g v⟫_ℂ := continuous_const.inner (hρ.cont v)
  have hbd : ∀ g, ‖⟪b, ρ g v⟫_ℂ‖ ≤ ‖b‖ * ‖v‖ := fun g =>
    (norm_inner_le_norm _ _).trans (by rw [hρ.norm])
  have hc2 : IntegrableOn (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) s ν := by
    refine Measure.integrableOn_of_bounded (M := (‖b‖ * ‖v‖) ^ 2) hs'
      (hcont.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun g => ?_)
    rw [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbd g) 2
  set f : Γ → ℂ := s.indicator (fun g => starRingEnd ℂ ⟪b, ρ g v⟫_ℂ) with hfdef
  have hfm : Measurable f := ((Complex.continuous_conj.comp hcont).measurable).indicator hs
  have hfi : Integrable f ν := by
    refine (integrable_indicator_iff hs).mpr (Measure.integrableOn_of_bounded (M := ‖b‖ * ‖v‖) hs'
      (Complex.continuous_conj.comp hcont).aestronglyMeasurable (ae_of_all _ fun g => ?_))
    rw [Complex.norm_conj]
    exact hbd g
  have hfeq : (fun g => ‖f g‖ ^ 2) = s.indicator (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) := by
    funext g
    by_cases hg : g ∈ s <;> simp [hfdef, hg, norm_inner_symm]
  have hf2 : Integrable (fun g => ‖f g‖ ^ 2) ν := by
    rw [hfeq]
    exact (integrable_indicator_iff hs).mpr hc2
  have hG := GlobalTheory.CompanionTheory.Godement.norm_sq_integral_smul_le ν ρ hρ v hm f hfm hfi hf2
  rw [hfeq, integral_indicator hs] at hG
  have hint : Integrable (fun g => f g • ρ g v) ν :=
    hfi.smul_of_top_left (memLp_top_of_bound (hρ.cont v).aestronglyMeasurable ‖v‖
      (ae_of_all _ fun g => (hρ.norm g v).le))
  set I := ∫ g in s, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν with hIdef
  set w := ∫ g, f g • ρ g v ∂ν with hwdef
  have hinner : ⟪b, w⟫_ℂ = (I : ℂ) := by
    have h := (innerSL ℂ b).integral_comp_comm hint
    simp only [innerSL_apply_apply] at h
    rw [hwdef, ← h, hIdef, ← integral_indicator hs, ← integral_complex_ofReal]
    congr 1
    funext g
    by_cases hg : g ∈ s
    · rw [hfdef, Set.indicator_of_mem hg, Set.indicator_of_mem hg, inner_smul_right,
        Complex.conj_mul']
      push_cast
      rfl
    · simp [hfdef, hg]
  have hI0 : 0 ≤ I := setIntegral_nonneg hs fun _ _ => by positivity
  have hM0 : 0 ≤ ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
  have h1 : I ≤ ‖b‖ * ‖w‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) b w
    rwa [hinner, Complex.norm_real, Real.norm_of_nonneg hI0] at h
  refine ⟨hc2, ?_⟩
  rcases hI0.eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · have h2 : I * I ≤ I * ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) := by
      calc I * I ≤ (‖b‖ * ‖w‖) * (‖b‖ * ‖w‖) := mul_self_le_mul_self hI0 h1
        _ = ‖b‖ ^ 2 * ‖w‖ ^ 2 := by ring
        _ ≤ ‖b‖ ^ 2 * (I * ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) := by gcongr
        _ = I * ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) := by ring
    exact le_of_mul_le_mul_left h2 hpos

theorem sq_integrable_and_bound (ρ : Γ → (B →L[ℂ] B)) (hρ : IsU ρ) (v : B)
    (hm : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (b : B) :
    Integrable (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) ν ∧
      ∫ g, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 := by
  have hK : 0 ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 :=
    mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (sq_nonneg _)
  have hcont : Continuous fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 :=
    (continuous_const.inner (hρ.cont v)).norm.pow 2
  have key : ∀ s, MeasurableSet s → ν s ≠ ⊤ → ∫⁻ g in s, ‖‖⟪b, ρ g v⟫_ℂ‖ ^ 2‖ₑ ∂ν ≤
      ENNReal.ofReal ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) := by
    intro s hs hs'
    obtain ⟨hi, hle⟩ := integrableOn_and_setIntegral_sq_le_of_isU ν ρ hρ v hm b hs hs'
    rw [← ofReal_integral_norm_eq_lintegral_enorm hi]
    apply ENNReal.ofReal_le_ofReal
    simpa only [norm_pow, norm_norm] using hle
  have hInt : Integrable (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) ν :=
    integrable_of_forall_fin_meas_le _ ENNReal.ofReal_lt_top hcont.aestronglyMeasurable key
  refine ⟨hInt, ?_⟩
  have hle := lintegral_le_of_forall_fin_meas_le _ key
  rw [← ofReal_integral_norm_eq_lintegral_enorm hInt, ENNReal.ofReal_le_ofReal_iff hK] at hle
  simpa only [norm_pow, norm_norm] using hle

end GlobalTheory.CompanionTheory.GodementCoeff

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasureImageDoubleCoset
section
open MeasureTheory GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.DoubleCosetVolume

theorem measure_doubleCoset {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q) [μ.IsMulLeftInvariant] (B : Subgroup Q)
    (hB : IsOpen (B : Set Q)) (s : Q)
    (hfin : (B.map (MulAut.conj s).toMonoidHom).relIndex B ≠ 0) :
    μ {q : Q | ∃ x ∈ B, ∃ y ∈ B, q = x * s * y} =
      ((B.map (MulAut.conj s).toMonoidHom).relIndex B : ENNReal) * μ (B : Set Q) := by
  classical
  set C : Subgroup B := (B.map (MulAut.conj s).toMonoidHom).subgroupOf B with hC
  have hidx : C.index ≠ 0 := hfin
  have : C.FiniteIndex := ⟨hidx⟩
  have : Finite (B ⧸ C) := inferInstance
  letI : Fintype (B ⧸ C) := Fintype.ofFinite _
  have hmemC : ∀ w : B, w ∈ C ↔ ∃ b ∈ B, s * b * s⁻¹ = (w : Q) := by
    intro w
    rw [hC, Subgroup.mem_subgroupOf, Subgroup.mem_map]
    simp [MulAut.conj_apply]
  let r : B ⧸ C → Q := fun c => ((Quotient.out c : B) : Q) * s
  let T : B ⧸ C → Set Q := fun c => (fun h => (r c)⁻¹ * h) ⁻¹' (B : Set Q)
  have hcover : {q : Q | ∃ x ∈ B, ∃ y ∈ B, q = x * s * y} = ⋃ c, T c := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      refine ⟨QuotientGroup.mk (⟨x, hx⟩ : B), ?_⟩
      have h1 : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk (⟨x, hx⟩ : B) : B ⧸ C)) : B ⧸ C) =
          QuotientGroup.mk (⟨x, hx⟩ : B) := QuotientGroup.out_eq' _
      obtain ⟨b, hb, hbw⟩ := (hmemC _).1 (QuotientGroup.eq.1 h1)
      have h2 : ((Quotient.out (QuotientGroup.mk (⟨x, hx⟩ : B) : B ⧸ C) : B) : Q)⁻¹ * x =
          s * b * s⁻¹ := by
        rw [hbw]; simp
      show (r _)⁻¹ * (x * s * y) ∈ B
      have h3 : (r (QuotientGroup.mk (⟨x, hx⟩ : B)))⁻¹ * (x * s * y) = b * y := by
        show (((Quotient.out (QuotientGroup.mk (⟨x, hx⟩ : B) : B ⧸ C) : B) : Q) * s)⁻¹ *
          (x * s * y) = b * y
        rw [mul_inv_rev, mul_assoc s⁻¹, ← mul_assoc _ (x * s) y, ← mul_assoc _ x s, h2]
        group
      rw [h3]
      exact B.mul_mem hb hy
    · rintro ⟨c, hc⟩
      refine ⟨_, (Quotient.out c : B).2, _, hc, ?_⟩
      show q = r c * ((r c)⁻¹ * q)
      group
  have hdisj : Pairwise (Function.onFun Disjoint T) := by
    intro c c' hcc
    refine Set.disjoint_left.2 fun q hq hq' => hcc ?_
    have hq1 : (r c)⁻¹ * q ∈ B := hq
    have hq2 : (r c')⁻¹ * q ∈ B := hq'
    have hw : (Quotient.out c : B)⁻¹ * (Quotient.out c' : B) ∈ C := by
      refine (hmemC _).2 ⟨((r c)⁻¹ * q) * ((r c')⁻¹ * q)⁻¹, B.mul_mem hq1 (B.inv_mem hq2), ?_⟩
      show _ = ((Quotient.out c : B) : Q)⁻¹ * ((Quotient.out c' : B) : Q)
      show s * (((((Quotient.out c : B) : Q) * s)⁻¹ * q) *
        (((((Quotient.out c' : B) : Q) * s)⁻¹ * q))⁻¹) * s⁻¹ = _
      group
    have := QuotientGroup.eq.2 hw
    rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
    exact this
  have hopen : ∀ c, MeasurableSet (T c) := fun c =>
    (hB.preimage (continuous_const.mul continuous_id)).measurableSet
  have hT : ∀ c, μ (T c) = μ (B : Set Q) := fun c => measure_preimage_mul μ _ _
  rw [hcover, measure_iUnion hdisj hopen]
  simp only [hT, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 2
  show _ = C.index
  rw [Subgroup.index, Nat.card_eq_fintype_card]

theorem relIndex_map_mk {G : Type*} [Group G] (Z : Subgroup G) [Z.Normal] (H : Subgroup G) (t : G)
    (hZ : ∀ g ∈ H, ∀ h ∈ H, (t * h * t⁻¹)⁻¹ * g ∈ Z → ∃ h₂ ∈ H, t * h₂ * t⁻¹ = g) :
    ((H.map (QuotientGroup.mk' Z)).map (MulAut.conj (QuotientGroup.mk' Z t)).toMonoidHom).relIndex
        (H.map (QuotientGroup.mk' Z)) =
      (H.map (MulAut.conj t).toMonoidHom).relIndex H := by
  rw [← Subgroup.relIndex_comap, ← Subgroup.inf_relIndex_right,
    ← Subgroup.inf_relIndex_right (H.map (MulAut.conj t).toMonoidHom)]
  congr 1
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_comap, Subgroup.mem_map]
  refine and_congr_left fun hg => ?_
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, exists_exists_and_eq_and]
  constructor
  · rintro ⟨h, hh, he⟩
    have h1 : (QuotientGroup.mk' Z) (t * h * t⁻¹) = (QuotientGroup.mk' Z) g := by
      simpa using he
    exact hZ g hg h hh (QuotientGroup.eq.1 h1)
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, by simp⟩

theorem toNat_natCast_mul (j : ℕ) (x : ℤ) : ((j : ℤ) * x).toNat = j * x.toNat := by
  rcases le_total 0 x with h | h
  · lift x to ℕ using h
    rw [← Nat.cast_mul, Int.toNat_natCast, Int.toNat_natCast]
  · have h1 : (j : ℤ) * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    rw [Int.toNat_of_nonpos h1, Int.toNat_of_nonpos h, mul_zero]

end GlobalTheory.CompanionTheory.DoubleCosetVolume

namespace GlobalTheory.CompanionTheory.DoubleCosetVolume

open ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k]

theorem central_mem_cong {N : ℕ} {r : ValueGroupWithZero k} (hr : r < 1)
    (t : GL (Fin N) k) (d : Fin N → k) (hd : ∀ i, d i ≠ 0)
    (ht : (t : Matrix (Fin N) (Fin N) k) = Matrix.diagonal d)
    (g h z : GL (Fin N) k)
    (hg : ∀ i j, valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ r)
    (hh : ∀ i j, valuation k ((h : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ r)
    (hz : z ∈ Subgroup.center (GL (Fin N) k)) (hgz : g = t * h * t⁻¹ * z) :
    ∀ i j, valuation k ((z : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ r := by
  obtain ⟨c, hc⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hz
  have hzv : (z : Matrix (Fin N) (Fin N) k) = Matrix.scalar (Fin N) c := hc.symm
  have htinv : ((t⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = Matrix.diagonal fun i => (d i)⁻¹ := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [ht, Matrix.diagonal_mul_diagonal]
    simp [hd, Matrix.diagonal_one]
  intro i j
  by_cases hij : i = j
  · subst hij
    have h1 : (g : Matrix (Fin N) (Fin N) k) i i = (h : Matrix (Fin N) (Fin N) k) i i * c := by
      rw [hgz]
      simp only [Units.val_mul, hzv, htinv, ht, Matrix.scalar_apply, Matrix.mul_diagonal,
        Matrix.diagonal_mul]
      field_simp [hd i]
    have h2 : valuation k ((h : Matrix (Fin N) (Fin N) k) i i) = 1 := by
      have h3 := hh i i
      rw [Matrix.one_apply_eq] at h3
      have h4 := Valuation.map_one_add_of_lt (valuation k) (h3.trans_lt hr)
      rwa [add_sub_cancel] at h4
    have h5 := hg i i
    have h6 := hh i i
    rw [Matrix.one_apply_eq] at h5 h6 ⊢
    have h7 : (h : Matrix (Fin N) (Fin N) k) i i * (c - 1) =
        ((g : Matrix (Fin N) (Fin N) k) i i - 1) - ((h : Matrix (Fin N) (Fin N) k) i i - 1) := by
      rw [h1]; ring
    have h8 : valuation k (c - 1) ≤ r := by
      have h9 := Valuation.map_sub (valuation k) ((g : Matrix (Fin N) (Fin N) k) i i - 1)
        ((h : Matrix (Fin N) (Fin N) k) i i - 1)
      rw [← h7, map_mul, h2, one_mul] at h9
      exact h9.trans (max_le h5 h6)
    rw [hzv]
    simpa using h8
  · rw [hzv, Matrix.one_apply_ne hij]
    simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]

end GlobalTheory.CompanionTheory.DoubleCosetVolume

namespace GlobalTheory.CompanionTheory.DoubleCosetVolume

open ValuativeRel

theorem measure_image_doubleCoset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : k) (m : ℕ) (a : Fin N → ℤ), ϖ ≠ 0 → ValuativeRel.valuation k (ϖ) < 1 → (∀ x : k, ValuativeRel.valuation k (x) < 1 → ValuativeRel.valuation k (x) ≤ ValuativeRel.valuation k (ϖ)) → 1 ≤ m → Antitone a → ∀ D : GL (Fin N) k, (D : Matrix (Fin N) (Fin N) k) = Matrix.diagonal (fun i => ϖ ^ (a i)) → ∀ [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : MeasureTheory.Measure (AdGL k N)), μ.IsHaarMeasure → ∀ j : ℕ, μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g : GL (Fin N) k | ∃ x ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, ∃ y ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}, g = x * D ^ j * y}) = ((Nat.card (IsLocalRing.ResidueField (ValuativeRel.valuation k).integer) : ENNReal) ^ (j * (∑ i : Fin N, ∑ j : Fin N, if i < j then (a i - a j).toNat else 0))) * μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)}) := by
  intro k _ _ _ _ N ϖ m a hϖ0 hϖ1 hunif hm ha D hD _ _ μ hμ j
  have hϖm0 : ϖ ^ m ≠ 0 := pow_ne_zero _ hϖ0
  have hr : valuation k (ϖ ^ m) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le hϖ1 (by omega)
  obtain ⟨H, hH⟩ := GlobalTheory.CompanionTheory.PrincipalCongruence.exists_principalCongruence k N (ϖ ^ m) hϖm0 hr
  have hopen : IsOpen (H : Set (GL (Fin N) k)) := by
    rw [hH]
    exact (GlobalTheory.CompanionTheory.PrincipalCongruence.isOpen_isCompact_principal k N (ϖ ^ m) hϖm0 hr).1
  have hmem : ∀ g : GL (Fin N) k, g ∈ H ↔ ∀ i j, valuation k
      ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ valuation k (ϖ ^ m) := by
    intro g
    rw [← SetLike.mem_coe, hH]
    rfl
  rw [← hH]
  set t : GL (Fin N) k := D ^ j with ht
  have hDj : (t : Matrix (Fin N) (Fin N) k) = Matrix.diagonal (fun i => ϖ ^ ((j : ℤ) * a i)) := by
    rw [ht, Units.val_pow_eq_pow_val, hD, Matrix.diagonal_pow]
    congr 1
    funext i
    simp only [Pi.pow_apply]
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  have hanti : Antitone fun i => (j : ℤ) * a i := fun x y hxy =>
    mul_le_mul_of_nonneg_left (ha hxy) (by positivity)
  have hindex := GlobalTheory.CompanionTheory.CongIndex.index_main k N ϖ m (fun i => (j : ℤ) * a i) hϖ0 hϖ1 hunif hm hanti t hDj H hH
  have hsum : (∑ i : Fin N, ∑ l : Fin N, if i < l then ((j : ℤ) * a i - (j : ℤ) * a l).toNat else 0) =
      j * ∑ i : Fin N, ∑ l : Fin N, if i < l then (a i - a l).toNat else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs
    · rw [← mul_sub, toNat_natCast_mul]
    · simp
  simp only [hsum] at hindex
  have hq : 0 < Nat.card (IsLocalRing.ResidueField (valuation k).integer) := Nat.card_pos
  set Z : Subgroup (GL (Fin N) k) := Subgroup.center (GL (Fin N) k) with hZdef
  have hmerge : ∀ g ∈ H, ∀ h ∈ H, (t * h * t⁻¹)⁻¹ * g ∈ Z → ∃ h₂ ∈ H, t * h₂ * t⁻¹ = g := by
    intro g hg h hh hz
    have hzH : (t * h * t⁻¹)⁻¹ * g ∈ H := (hmem _).2 (central_mem_cong hr t _
      (fun i => zpow_ne_zero _ hϖ0) hDj g h _ ((hmem g).1 hg) ((hmem h).1 hh) hz (by group))
    refine ⟨h * ((t * h * t⁻¹)⁻¹ * g), H.mul_mem hh hzH, ?_⟩
    have hc := Subgroup.mem_center_iff.1 hz t⁻¹
    calc t * (h * ((t * h * t⁻¹)⁻¹ * g)) * t⁻¹
        = t * h * (((t * h * t⁻¹)⁻¹ * g) * t⁻¹) := by group
      _ = t * h * (t⁻¹ * ((t * h * t⁻¹)⁻¹ * g)) := by rw [hc]
      _ = g := by group
  have hI := relIndex_map_mk Z H t hmerge
  set B : Subgroup (AdGL k N) := H.map (QuotientGroup.mk' Z) with hB
  set s : AdGL k N := QuotientGroup.mk' Z t with hs
  have hBopen : IsOpen (B : Set (AdGL k N)) := by
    have := QuotientGroup.isOpenMap_coe (N := Z) _ hopen
    simpa [hB, Subgroup.coe_map] using this
  have hBcoe : (QuotientGroup.mk : GL (Fin N) k → AdGL k N) '' (H : Set (GL (Fin N) k)) = (B : Set (AdGL k N)) := by
    rw [hB, Subgroup.coe_map]; rfl
  have hdc : (QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
      {g : GL (Fin N) k | ∃ x ∈ (H : Set (GL (Fin N) k)), ∃ y ∈ (H : Set (GL (Fin N) k)), g = x * t * y} =
      {q : AdGL k N | ∃ x ∈ B, ∃ y ∈ B, q = x * s * y} := by
    ext q
    constructor
    · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      exact ⟨_, Subgroup.mem_map_of_mem _ hx, _, Subgroup.mem_map_of_mem _ hy, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨x * t * y, ⟨x, hx, y, hy, rfl⟩, rfl⟩
  rw [hBcoe, hdc, measure_doubleCoset μ B hBopen s (by rw [hI, hindex]; positivity), hI, hindex]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.DoubleCosetVolume
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasureImagePrincipalPosLtTop
section
open GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.PrincipalCongruence

theorem measure_image_principal_pos_lt_top :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N : ℕ) (ϖ : k) (m : ℕ), ϖ ≠ 0 → ValuativeRel.valuation k (ϖ) < 1 →
      (∀ x : k, ValuativeRel.valuation k (x) < 1 →
        ValuativeRel.valuation k (x) ≤ ValuativeRel.valuation k (ϖ)) → 1 ≤ m →
      ∀ [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : MeasureTheory.Measure (AdGL k N)),
        μ.IsHaarMeasure →
        0 < μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
          {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
            ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
              ValuativeRel.valuation k (ϖ ^ m)}) ∧
        μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
          {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
            ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
              ValuativeRel.valuation k (ϖ ^ m)}) < ⊤ := by
  intro k _ _ _ _ N ϖ m h0 h1 _ hm _ _ μ hμ
  have ht0 : ϖ ^ m ≠ 0 := pow_ne_zero m h0
  have ht1 : ValuativeRel.valuation k (ϖ ^ m) < 1 := by
    rw [map_pow]
    exact pow_lt_one' h1 (by omega)
  obtain ⟨hopen, hcomp⟩ := isOpen_isCompact_principal k N (ϖ ^ m) ht0 ht1
  have hone : (1 : GL (Fin N) k) ∈ {g : GL (Fin N) k | ∀ i j, ValuativeRel.valuation k
      ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤
        ValuativeRel.valuation k (ϖ ^ m)} := by
    intro i j
    simp
  refine ⟨?_, ?_⟩
  · have himg : IsOpenMap (QuotientGroup.mk : GL (Fin N) k → AdGL k N) :=
      QuotientGroup.isOpenMap_coe
    exact (himg _ hopen).measure_pos μ ⟨_, Set.mem_image_of_mem _ hone⟩
  · exact (hcomp.image QuotientGroup.continuous_mk).measure_lt_top

end GlobalTheory.CompanionTheory.PrincipalCongruence
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicDecompositionUpperHalfSpaceStatement
section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_decomposition_upper_half_space : ∀ (n : ℕ) (p : PositivityTheory.Rg.Sw.GR n), (PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ = 0 → ∃ (nb ma : PositivityTheory.Rg.Sw.GR n) (b a : Matrix (Fin n) (Fin n) ℂ), bᴴ = b ∧ IsUnit a.det ∧ PositivityTheory.Rg.Sw.mR nb = PositivityTheory.Rg.Sw.nU b ∧ PositivityTheory.Rg.Sw.mR ma = Matrix.fromBlocks a 0 0 (aᴴ)⁻¹ ∧ p = nb * ma ∧ ((PositivityTheory.Rg.Sw.mR p).toBlocks₁₁ * (Complex.I • 1) + (PositivityTheory.Rg.Sw.mR p).toBlocks₁₂) * ((PositivityTheory.Rg.Sw.mR p).toBlocks₂₁ * (Complex.I • 1) + (PositivityTheory.Rg.Sw.mR p).toBlocks₂₂)⁻¹ = b + Complex.I • (a * aᴴ) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelPoint.siegel_point | exact GlobalTheory.CompanionTheory.SiegelPoint.siegel_point | (intros; apply GlobalTheory.CompanionTheory.SiegelPoint.siegel_point <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParahoricUnipotentTimesKernelStatement
section
open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoric_unipotent_times_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ∀ g ∈ Gx k e,
    ∃ u ∈ unipRad k e ⊓ KO k (Fin n), ∃ h ∈ KOne k (Fin n), g = u * h := by
  first | exact @GlobalTheory.CompanionTheory.GxSplit.gx_split | exact GlobalTheory.CompanionTheory.GxSplit.gx_split | (intros; apply GlobalTheory.CompanionTheory.GxSplit.gx_split <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RangeIsotropicIffInvolutionMulZeroStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.range_isotropic_iff_involution_mul_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E) (π : Matrix (Fin n) (Fin n) E), LinearMap.range (Matrix.toLin' π) ≤ perpD (conjE E) d (LinearMap.range (Matrix.toLin' π)) ↔ sg d π * π = 0 := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.iso_range_iff_sg_mul | exact GlobalTheory.CompanionTheory.TorusCh.iso_range_iff_sg_mul | (intros; apply GlobalTheory.CompanionTheory.TorusCh.iso_range_iff_sg_mul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformGenerationOfVanishingStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_generation_of_vanishing : GradedNoeth → UniformVanishing → UniformGen := by
  first | exact @GlobalTheory.CompanionTheory.GE.uniformGen_of_gradedNoeth | exact GlobalTheory.CompanionTheory.GE.uniformGen_of_gradedNoeth | (intros; apply GlobalTheory.CompanionTheory.GE.uniformGen_of_gradedNoeth <;> assumption)
end

