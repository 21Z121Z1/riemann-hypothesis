import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0278
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0277
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixTranslationModulationIrreduc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0222
import ReciprocityTheory.Chebotarev.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleXSqAddOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerRepSchwartzPolynomialBound
section
open MeasureTheory GlobalTheory.RealWeil Filter Topology
open scoped SchwartzMap RealInnerProductSpace

noncomputable section

namespace GlobalTheory.RealWeil.SchrFamily

variable {l : Type} [Fintype l]

def pCLM (l : Type) [Fintype l] : (l ⊕ l → ℝ) →L[ℝ] EuclideanSpace ℝ l :=
  LinearMap.toContinuousLinearMap { toFun := pPart, map_add' := pPart_add, map_smul' := pPart_smul }

def qCLM (l : Type) [Fintype l] : (l ⊕ l → ℝ) →L[ℝ] EuclideanSpace ℝ l :=
  LinearMap.toContinuousLinearMap { toFun := qPart, map_add' := qPart_add, map_smul' := qPart_smul }

theorem rhoSch_eq (w : l ⊕ l → ℝ) (g : Sch l) :
    rhoSch w g = SchwartzMap.smulLeftCLM ℂ
      (fun y => GlobalTheory.Published.Metaplectic.eChar (innerSL ℝ (qPart w) y + ⟪pPart w, qPart w⟫ / 2))
      (SchwartzMap.compSubConstCLM ℂ (-pPart w) g) := by
  ext x
  rw [coe_rhoSch, SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.PhaseLipschitz.hasTemperateGrowth_phase _ _),
    SchwartzMap.compSubConstCLM_apply, smul_eq_mul, rhoFun, phase_eq_eChar, sub_neg_eq_add]
  simp

theorem seminorm_rhoSch_sub_le (p : Seminorm ℂ (Sch l)) (hp : Continuous p) :
    ∃ (q₁ q₂ q₃ : Seminorm ℂ (Sch l)) (M₁ M₂ M₃ : ℕ), ∀ (w : l ⊕ l → ℝ) (g : Sch l),
      p (rhoSch w g - g) ≤ (‖qPart w‖ + |⟪pPart w, qPart w⟫ / 2|) * (1 + ‖qPart w‖) ^ M₁ *
          (‖pPart w‖ * (1 + ‖pPart w‖) ^ M₃ * q₃ g + q₁ g) + ‖pPart w‖ * (1 + ‖pPart w‖) ^ M₂ * q₂ g := by
  obtain ⟨q₁, M₁, hq₁, hb₁⟩ := GlobalTheory.PhaseLipschitz.seminorm_smulLeft_eChar_sub_le (EuclideanSpace ℝ l) p hp
  obtain ⟨q₂, M₂, -, hb₂⟩ := GlobalTheory.SchwartzTranslateLip.translate_sub_le (EuclideanSpace ℝ l) p hp
  obtain ⟨q₃, M₃, -, hb₃⟩ := GlobalTheory.SchwartzTranslateLip.translate_sub_le (EuclideanSpace ℝ l) q₁ hq₁
  refine ⟨q₁, q₂, q₃, M₁, M₂, M₃, fun w g => ?_⟩
  set T := SchwartzMap.compSubConstCLM ℂ (-pPart w) g with hT
  have hL : ‖innerSL ℝ (qPart w)‖ = ‖qPart w‖ := innerSL_apply_norm _ _
  have h1 := map_add_le_add p (SchwartzMap.smulLeftCLM ℂ
    (fun y => GlobalTheory.Published.Metaplectic.eChar (innerSL ℝ (qPart w) y + ⟪pPart w, qPart w⟫ / 2)) T - T) (T - g)
  rw [sub_add_sub_cancel] at h1
  rw [rhoSch_eq]
  refine le_trans h1 (add_le_add ((hb₁ _ _ T).trans ?_) (hb₂ _ g))
  rw [hL]
  have h2 := map_add_le_add q₁ (T - g) g
  rw [sub_add_cancel] at h2
  have h3 := hb₃ (pPart w) g
  gcongr
  linarith

theorem tendsto_rhoSch_zero (g : Sch l) : Tendsto (fun u => rhoSch u g) (𝓝 0) (𝓝 g) := by
  rw [(schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).tendsto_nhds _ g]
  intro i ε hε
  obtain ⟨q₁, q₂, q₃, M₁, M₂, M₃, hb⟩ := seminorm_rhoSch_sub_le (schwartzSeminormFamily ℂ _ ℂ i)
    ((schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).continuous_seminorm i)
  have hpc : Tendsto (fun u : l ⊕ l → ℝ => pPart u) (𝓝 0) (𝓝 0) := by
    have := (pCLM l).continuous.tendsto 0
    rw [map_zero] at this
    exact this
  have hqc : Tendsto (fun u : l ⊕ l → ℝ => qPart u) (𝓝 0) (𝓝 0) := by
    have := (qCLM l).continuous.tendsto 0
    rw [map_zero] at this
    exact this
  have hpn : Tendsto (fun u : l ⊕ l → ℝ => ‖pPart u‖) (𝓝 0) (𝓝 0) := by simpa using hpc.norm
  have hqn : Tendsto (fun u : l ⊕ l → ℝ => ‖qPart u‖) (𝓝 0) (𝓝 0) := by simpa using hqc.norm
  have hk : Tendsto (fun u : l ⊕ l → ℝ => |⟪pPart u, qPart u⟫ / 2|) (𝓝 0) (𝓝 0) := by
    have := ((hpc.inner (𝕜 := ℝ) hqc).div_const 2).abs
    simpa using this
  have lim : Tendsto (fun u : l ⊕ l → ℝ => (‖qPart u‖ + |⟪pPart u, qPart u⟫ / 2|) * (1 + ‖qPart u‖) ^ M₁ *
          (‖pPart u‖ * (1 + ‖pPart u‖) ^ M₃ * q₃ g + q₁ g) + ‖pPart u‖ * (1 + ‖pPart u‖) ^ M₂ * q₂ g)
      (𝓝 0) (𝓝 0) := by
    have := (((hqn.add hk).mul ((hqn.const_add 1).pow M₁)).mul
      (((hpn.mul ((hpn.const_add 1).pow M₃)).mul_const (q₃ g)).add_const (q₁ g))).add
      ((hpn.mul ((hpn.const_add 1).pow M₂)).mul_const (q₂ g))
    simpa using this
  filter_upwards [lim.eventually (gt_mem_nhds hε)] with u hu
  exact (hb u g).trans_lt hu

theorem rhoSch_rhoSch (w₀ u : l ⊕ l → ℝ) (g : Sch l) :
    rhoSch w₀ (rhoSch u g) = Complex.exp (((Real.pi * sympl w₀ u : ℝ) : ℂ) * Complex.I) • rhoSch (w₀ + u) g := by
  ext x
  rw [coe_rhoSch, coe_rhoSch, rhoFun_rhoFun, SchwartzMap.smul_apply, coe_rhoSch]
  rfl

theorem continuous_rhoSch (g : Sch l) : Continuous fun w => rhoSch w g := by
  refine continuous_iff_continuousAt.2 fun w₀ => ?_
  set c : (l ⊕ l → ℝ) → ℂ := fun u => Complex.exp (((Real.pi * sympl w₀ u : ℝ) : ℂ) * Complex.I) with hcdef
  have hs : Continuous fun u : l ⊕ l → ℝ => sympl w₀ u := by
    have e : (fun u : l ⊕ l → ℝ => sympl w₀ u) =
        fun u => ⟪pPart w₀, qCLM l u⟫ - ⟪qPart w₀, pCLM l u⟫ := rfl
    rw [e]
    exact (continuous_const.inner (qCLM l).continuous).sub (continuous_const.inner (pCLM l).continuous)
  have hc : Continuous c := by
    rw [hcdef]
    fun_prop
  have h1 : Tendsto (fun u => (c u)⁻¹ • rhoSch w₀ (rhoSch u g)) (𝓝 0) (𝓝 ((c 0)⁻¹ • rhoSch w₀ g)) :=
    ((hc.tendsto 0).inv₀ (Complex.exp_ne_zero _)).smul
      (((rhoSch w₀).continuous.tendsto g).comp (tendsto_rhoSch_zero g))
  have hq0 : qPart (0 : l ⊕ l → ℝ) = 0 := rfl
  have hp0 : pPart (0 : l ⊕ l → ℝ) = 0 := rfl
  have hc0 : c 0 = 1 := by simp [hcdef, sympl, hq0, hp0]
  have e : ∀ u, (c u)⁻¹ • rhoSch w₀ (rhoSch u g) = rhoSch (w₀ + u) g := fun u => by
    rw [rhoSch_rhoSch, inv_smul_smul₀ (Complex.exp_ne_zero _)]
  simp only [e, hc0, inv_one, one_smul] at h1
  have h3 : Tendsto (fun w => w - w₀) (𝓝 w₀) (𝓝 0) := (continuous_sub_right w₀).tendsto' _ _ (sub_self _)
  refine (h1.comp h3).congr fun w => ?_
  simp

theorem seminorm_rhoSch_le (g : Sch l) (k m : ℕ) :
    ∃ (C : ℝ) (N : ℕ), ∀ w, SchwartzMap.seminorm ℂ k m (rhoSch w g) ≤ C * (1 + ‖w‖) ^ N := by
  obtain ⟨q₁, q₂, q₃, M₁, M₂, M₃, hb⟩ := seminorm_rhoSch_sub_le (SchwartzMap.seminorm ℂ k m)
    ((schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).continuous_seminorm (k, m))
  set p := SchwartzMap.seminorm ℂ k m (E := EuclideanSpace ℝ l) (F := ℂ) with hpdef
  set c := ‖pCLM l‖ + ‖qCLM l‖ with hcdef
  set N := 3 + M₁ + M₂ + M₃ with hN
  have hq1 : 0 ≤ q₁ g := apply_nonneg _ _
  have hq2 : 0 ≤ q₂ g := apply_nonneg _ _
  have hq3 : 0 ≤ q₃ g := apply_nonneg _ _
  have hp : 0 ≤ p g := apply_nonneg _ _
  refine ⟨(1 + c) ^ N * (2 * q₃ g + 2 * q₁ g + q₂ g + p g), N, fun w => ?_⟩
  have hc : 0 ≤ c := by positivity
  have hw := norm_nonneg w
  set X := (1 + c) * (1 + ‖w‖) with hX
  have hX1 : 1 ≤ X := by rw [hX]; nlinarith
  have hpw : ‖pPart w‖ ≤ ‖pCLM l‖ * ‖w‖ := (pCLM l).le_opNorm w
  have hqw : ‖qPart w‖ ≤ ‖qCLM l‖ * ‖w‖ := (qCLM l).le_opNorm w
  have hpn := norm_nonneg (pCLM l)
  have hqn := norm_nonneg (qCLM l)
  have ha : 1 + ‖pPart w‖ ≤ X := by rw [hX]; nlinarith
  have hb' : 1 + ‖qPart w‖ ≤ X := by rw [hX]; nlinarith
  have ha' : ‖pPart w‖ ≤ X := by linarith
  have hb'' : ‖qPart w‖ ≤ X := by linarith
  have hk : ‖qPart w‖ + |⟪pPart w, qPart w⟫ / 2| ≤ 2 * X ^ 2 := by
    have h1 : |⟪pPart w, qPart w⟫| ≤ ‖pPart w‖ * ‖qPart w‖ := abs_real_inner_le_norm _ _
    have h2 : ‖pPart w‖ * ‖qPart w‖ ≤ X * X := mul_le_mul ha' hb'' (norm_nonneg _) (by linarith)
    rw [abs_div, abs_two]
    nlinarith
  have hsub : p (rhoSch w g) ≤ p (rhoSch w g - g) + p g := by
    simpa using map_add_le_add p (rhoSch w g - g) g
  calc p (rhoSch w g) ≤ p (rhoSch w g - g) + p g := hsub
    _ ≤ (2 * X ^ 2) * X ^ M₁ * (X * X ^ M₃ * q₃ g + q₁ g) + X * X ^ M₂ * q₂ g + p g := by
        refine add_le_add ((hb w g).trans ?_) le_rfl
        gcongr
    _ = 2 * X ^ (3 + M₁ + M₃) * q₃ g + 2 * X ^ (2 + M₁) * q₁ g + X ^ (1 + M₂) * q₂ g + 1 * p g := by ring
    _ ≤ 2 * X ^ N * q₃ g + 2 * X ^ N * q₁ g + X ^ N * q₂ g + X ^ N * p g := by
        have e1 : X ^ (3 + M₁ + M₃) ≤ X ^ N := pow_le_pow_right₀ hX1 (by omega)
        have e2 : X ^ (2 + M₁) ≤ X ^ N := pow_le_pow_right₀ hX1 (by omega)
        have e3 : X ^ (1 + M₂) ≤ X ^ N := pow_le_pow_right₀ hX1 (by omega)
        have e4 : (1 : ℝ) ≤ X ^ N := one_le_pow₀ hX1
        have f1 := mul_le_mul_of_nonneg_right e1 hq3
        have f2 := mul_le_mul_of_nonneg_right e2 hq1
        have f3 := mul_le_mul_of_nonneg_right e3 hq2
        have f4 := mul_le_mul_of_nonneg_right e4 hp
        nlinarith
    _ = (1 + c) ^ N * (2 * q₃ g + 2 * q₁ g + q₂ g + p g) * (1 + ‖w‖) ^ N := by
        rw [hX, mul_pow]; ring

theorem exists_continuous_schwartz_rhoFun : ∀ (n : ℕ) (f : Sch (Fin n)), ∃ G : (Fin n ⊕ Fin n → ℝ) → Sch (Fin n),
    Continuous G ∧ (∀ w, ⇑(G w) = rhoFun w ⇑f) ∧
    ∀ k m : ℕ, ∃ (C : ℝ) (N : ℕ), ∀ w, SchwartzMap.seminorm ℂ k m (G w) ≤ C * (1 + ‖w‖) ^ N :=
  fun _ f => ⟨fun w => rhoSch w f, continuous_rhoSch f, fun w => coe_rhoSch w f, seminorm_rhoSch_le f⟩

end GlobalTheory.RealWeil.SchrFamily
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergPreservesSchwartzB
section
namespace SchrodingerSchwartzBruhat
section
open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.SchrSB

theorem eq_one_of_pow_two_pow_near {z : ℂ} (h : ∀ n : ℕ, ‖z ^ (2 ^ n) - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.PositiveFormRecursion.main
  | exact _root_.GlobalTheory.PositiveFormRecursion.main
  | (apply _root_.GlobalTheory.PositiveFormRecursion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PositiveFormRecursion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PositiveFormRecursion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PositiveFormRecursion.main ..)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLocallyConstant_addChar (ψ : AddChar k ℂ) (hψ : Continuous ψ) : IsLocallyConstant ψ := by
  have hb := IsValuativeTopology.hasBasis_nhds_zero' k
  have hU : ψ ⁻¹' Metric.ball 1 (1 / 2) ∈ nhds (0 : k) :=
    hψ.continuousAt.preimage_mem_nhds (by
      rw [AddChar.map_zero_eq_one]; exact Metric.ball_mem_nhds _ (by norm_num))
  obtain ⟨γ, hγ, hsub⟩ := hb.mem_iff.mp hU
  have hker : ∀ x, ValuativeRel.valuation k x < γ → ψ x = 1 := by
    intro x hx
    have h2 : ∀ n : ℕ, ValuativeRel.valuation k ((2 ^ n : ℕ) • x) < γ := by
      intro n
      induction n with
      | zero => simpa using hx
      | succ n ih =>
        have e : (2 ^ (n + 1) : ℕ) • x = (2 ^ n : ℕ) • x + (2 ^ n : ℕ) • x := by
          rw [pow_succ, mul_two, add_smul]
        rw [e]
        exact Valuation.map_add_lt _ ih ih
    apply eq_one_of_pow_two_pow_near
    intro n
    have h3 : ψ ((2 ^ n : ℕ) • x) ∈ Metric.ball (1 : ℂ) (1 / 2) := hsub (h2 n)
    rw [AddChar.map_nsmul_eq_pow, Metric.mem_ball, dist_eq_norm] at h3
    exact h3
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hn : {y : k | ValuativeRel.valuation k (y - x) < γ} ∈ nhds x := by
    have hc : ContinuousAt (fun y : k => y - x) x := by fun_prop
    exact hc.preimage_mem_nhds (by simpa using hb.mem_of_mem hγ)
  filter_upwards [hn] with y hy
  have e : ψ y = ψ (y - x) * ψ x := by
    rw [← AddChar.map_add_eq_mul]; simp
  rw [e, hker _ hy, one_mul]

theorem schr_mem_SB : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    ∀ {κ : Type} [Fintype κ] (w : (κ → k) × (κ → k)), ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), GlobalTheory.WeilM.schr ψ0 w φ ∈ GlobalTheory.WeilM.SB (κ → k) := by
  intro k _ _ _ _ _ ψ0 hψ κ _ w φ hφ
  obtain ⟨h1, h2⟩ : IsLocallyConstant φ ∧ HasCompactSupport φ := hφ
  have hl := isLocallyConstant_addChar ψ0 hψ
  have hcont : Continuous fun x : κ → k => x ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2) := by
    refine Continuous.add ?_ continuous_const
    exact continuous_id.dotProduct continuous_const
  have hs : HasCompactSupport fun x : κ → k => φ (x + w.1) :=
    h2.comp_homeomorph (Homeomorph.addRight w.1)
  have hf : IsLocallyConstant fun x : κ → k => φ (x + w.1) :=
    h1.comp_continuous (continuous_add_const w.1)
  refine ⟨?_, ?_⟩
  · exact (hl.comp_continuous hcont).mul hf
  · exact HasCompactSupport.mul_left hs

end GlobalTheory.CompanionTheory.SchrSB

end

end SchrodingerSchwartzBruhat
section

open MeasureTheory Matrix

theorem _root_.GlobalTheory.Adopt.schroedingerOperatorHeisenberg_preserves_schwartzBruhat : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    ∀ {κ : Type} [Fintype κ] (w : (κ → k) × (κ → k)), ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), GlobalTheory.WeilM.schr ψ0 w φ ∈ GlobalTheory.WeilM.SB (κ → k) := by
  first | exact @SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.schr_mem_SB | exact SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.schr_mem_SB | (intros; apply SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.schr_mem_SB <;> assumption)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatVectorIrreducibleTranslationsCharaStatement
section
open ValuativeRel Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_vector_irreducible_translations_characters : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    {κ : Type} [Fintype κ] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    (∀ x : k, (∀ y ∈ 𝒪[k], ψ0 (x * y) = 1) ↔ x ∈ 𝒪[k]) →
    ∀ W : Submodule ℂ ((κ → k) → ℂ), W ≤ GlobalTheory.WeilM.SB (κ → k) →
    (∀ φ ∈ W, ∀ v : κ → k, (fun x => φ (x + v)) ∈ W) →
    (∀ φ ∈ W, ∀ y : κ → k, (fun x => ψ0 (x ⬝ᵥ y) * φ x) ∈ W) →
    ∀ φ₀ ∈ W, φ₀ ≠ 0 → W = GlobalTheory.WeilM.SB (κ → k) := by
  first | exact @GlobalTheory.IrredSBVec.sb_irreducible_vec | exact GlobalTheory.IrredSBVec.sb_irreducible_vec | (intros; apply GlobalTheory.IrredSBVec.sb_irreducible_vec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzL2EuclideanIdentificationStatement
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_L2_euclidean_identification : ∀ (l : Type) [Fintype l] [DecidableEq l], ∃ (e : 𝓢(l → ℝ, ℂ) ≃L[ℂ] Sch l) (u : Lp ℂ 2 (volume : Measure (l → ℝ)) ≃ₗᵢ[ℂ] L2 l), (∀ φ (x : EuclideanSpace ℝ l), e φ x = φ x.ofLp) ∧ ∀ φ : 𝓢(l → ℝ, ℂ), u (φ.toLp 2) = (e φ).toLp 2 := by
  first | exact @GlobalTheory.EuclidTransport.exists_schwartz_L2_transport | exact GlobalTheory.EuclidTransport.exists_schwartz_L2_transport | (intros; apply GlobalTheory.EuclidTransport.exists_schwartz_L2_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionTensorPullbackRingHomBijectiveStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionTensorPullbackRingHom_bijective : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (U : T.affineOpens), Function.Bijective (GlobalTheory.HilbAff.theta A B g U) := by
  first | (exact @GlobalTheory.HilbAff.theta_bijective) | (exact GlobalTheory.HilbAff.theta_bijective) | (intros; apply GlobalTheory.HilbAff.theta_bijective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsIsFractionRingStalkImageOfGenericPointStatement
section
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_isFractionRing_stalk_imageOfGenericPoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y] [GlobalTheory.IsNormalScheme Z] (U : Z.Opens), IsAffineOpen U →
    (U : Set Z) ⊆ Set.range π → ∀ h : GlobalTheory.NormSheafDescent.genPt π ∈ U,
    IsDomain Γ(Z, U) ∧ (letI := GlobalTheory.NormSheafDescent.algAK π U h
      IsFractionRing Γ(Z, U) (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))) := by
  first | exact @GlobalTheory.NormSheafDescent.sections_isDomain_isFractionRing_stalk | exact GlobalTheory.NormSheafDescent.sections_isDomain_isFractionRing_stalk | (intros; apply GlobalTheory.NormSheafDescent.sections_isDomain_isFractionRing_stalk <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeminormSliceRLe
section
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff

noncomputable section
namespace GlobalTheory.SliceOpCont

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem norm_padL_le {κ κ' : Type} [Fintype κ] [Fintype κ'] (h : κ → V) :
    ‖(padL (κ' := κ') h : κ ⊕ κ' → V)‖ ≤ ‖h‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  cases i with
  | inl i => simpa [padL] using norm_le_pi_norm h i
  | inr j => simp [padL]

theorem sliceR_sub_eq {κ κ' : Type} [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ)
    (x x₀ : κ → V) :
    sliceR f x - sliceR f x₀
      = sliceR (SchwartzMap.compSubConstCLM ℂ (-(padL (κ' := κ') (x - x₀))) f - f) x₀ := by
  ext y
  have he : (Sum.elim x₀ y : κ ⊕ κ' → V) + padL (x - x₀) = Sum.elim x y := by
    funext i
    cases i with
    | inl i => simp [padL]
    | inr j => simp [padL]
  simp [SchwartzMap.compSubConstCLM_apply, he]

theorem seminorm_sliceR_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {κ κ' : Type} [Fintype κ] [Fintype κ'] (g : SchwartzMap (κ ⊕ κ' → V) ℂ) (x : κ → V) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (sliceR g x) ≤ SchwartzMap.seminorm ℂ k n g := by
  have := GlobalTheory.SliceWeight.pow_norm_mul_seminorm_sliceR_le V κ κ' g 0 k n x
  simpa using this

theorem continuous_sliceR (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {κ κ' : Type} [Fintype κ] [Fintype κ'] (f : SchwartzMap (κ ⊕ κ' → V) ℂ) :
    Continuous (fun x : κ → V => sliceR f x) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  refine ((schwartz_withSeminorms ℂ (κ' → V) ℂ).tendsto_nhds _ _).2 fun i ε hε => ?_
  obtain ⟨k, n⟩ := i
  set C : ℝ := 2 ^ k * ((Finset.Iic (k, n + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f
  have hcont : Continuous (fun x : κ → V => ‖x - x₀‖ * (1 + ‖x - x₀‖) ^ k * C) := by fun_prop
  have h0 : ‖x₀ - x₀‖ * (1 + ‖x₀ - x₀‖) ^ k * C = 0 := by simp
  have hev : ∀ᶠ x in nhds x₀, ‖x - x₀‖ * (1 + ‖x - x₀‖) ^ k * C < ε := by
    have := hcont.continuousAt (x := x₀)
    rw [ContinuousAt, h0] at this
    exact this (Iio_mem_nhds hε)
  filter_upwards [hev] with x hx
  refine lt_of_le_of_lt ?_ hx
  change SchwartzMap.seminorm ℂ k n (sliceR f x - sliceR f x₀) ≤ _
  rw [sliceR_sub_eq]
  refine (seminorm_sliceR_le V _ x₀ k n).trans ?_
  refine (GlobalTheory.SchwartzTranslateLip.seminorm_translate_sub_le k n k n le_rfl le_rfl _ f).trans ?_
  have hC : 0 ≤ C := by positivity
  have hp := norm_padL_le (κ' := κ') (x - x₀)
  gcongr

end GlobalTheory.SliceOpCont

open GlobalTheory.SliceOpCont in
theorem GlobalTheory.SliceOp.continuous_qOp (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (κ κ' κ₁' : Type) [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ) :
    Continuous (qOp P f) := by
  have hinl : Continuous (fun s : κ ⊕ κ₁' → V => s ∘ Sum.inl) := by fun_prop
  have hinr : Continuous (fun s : κ ⊕ κ₁' → V => s ∘ Sum.inr) := by fun_prop
  have hG : Continuous (fun s : κ ⊕ κ₁' → V =>
      SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ₁' → V) ℂ (P (sliceR f (s ∘ Sum.inl)))) :=
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ₁' → V) ℂ).continuous.comp
      (P.continuous.comp ((continuous_sliceR V f).comp hinl))
  have hq : qOp P f = fun s => (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ₁' → V) ℂ
      (P (sliceR f (s ∘ Sum.inl)))) (s ∘ Sum.inr) := by
    funext s; rfl
  rw [hq]
  exact continuous_eval.comp (hG.prodMk hinr)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepIntPolyRootModPrimeSqStatement
section
open scoped TensorProduct Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_large_prime_sq_dvd_eval_of_separable : ∀ f : ℤ[X], 0 < f.natDegree → (f.map (Int.castRingHom ℚ)).Separable → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ x : ℤ, ((p : ℤ) ^ 2) ∣ f.eval x := by
  first | exact @GlobalTheory.sep_int_poly_root_mod_prime_sq | exact GlobalTheory.sep_int_poly_root_mod_prime_sq | (intros; apply GlobalTheory.sep_int_poly_root_mod_prime_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelGaussianPairStandardGaussianStatement
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelGaussian_pair_standardGaussian : ∀ (l : Type) [Fintype l] [DecidableEq l] (τ : Matrix l l ℂ) (c : ℂ), GlobalTheory.IsSiegel τ → (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 * (1 - I • τ).det = c ^ 2 := by
  first | exact @GlobalTheory.siegelGauss_pair_standard | exact GlobalTheory.siegelGauss_pair_standard | (intros; apply GlobalTheory.siegelGauss_pair_standard <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecHomExtOfLocalizationAwaySpanEqTopStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specHom_ext_of_localizationAway_span_eq_top : ∀ (S : Type) [CommRing S] (ι : Type) (s : ι → S), Ideal.span (Set.range s) = ⊤ →
    ∀ (Y : Scheme.{0}) (a b : Sp S ⟶ Y),
    (∀ i, spMap (algebraMap S (Localization.Away (s i))) ≫ a = spMap (algebraMap S (Localization.Away (s i))) ≫ b) →
    a = b := by
  first | exact @GlobalTheory.SecGlue.hom_ext_of_span_eq_top | exact GlobalTheory.SecGlue.hom_ext_of_span_eq_top | (intros; apply GlobalTheory.SecGlue.hom_ext_of_span_eq_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemNsp
section
open GlobalTheory.WeilM Matrix

noncomputable section
namespace GlobalTheory.RankStrata

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Nsp (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν : kˣ →* ℂˣ) :
    Submodule ℂ (Matrix A D k → ℂ) :=
  Submodule.span ℂ {Z | ∃ g : GL A k, ∃ Ψ' ∈ SB (Matrix A D k), Z = GlobalTheory.SplitFlip.omB ν ν g 1 Ψ' - Ψ'}

variable {k}

theorem Nsp_le_SB (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν : kˣ →* ℂˣ) :
    Nsp k A D ν ≤ SB (Matrix A D k) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, Ψ', hΨ', rfl⟩
  exact Submodule.sub_mem _ (GlobalTheory.SplitFlip.omB_mem_SB ν ν g 1 hΨ') hΨ'

theorem sub_mem_Nsp {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν : kˣ →* ℂˣ)
    (g : GL A k) {Ψ : Matrix A D k → ℂ} (hΨ : Ψ ∈ SB (Matrix A D k)) :
    GlobalTheory.SplitFlip.omB ν ν g 1 Ψ - Ψ ∈ Nsp k A D ν :=
  Submodule.subset_span ⟨g, Ψ, hΨ, rfl⟩

end GlobalTheory.RankStrata
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableGaussianExtensionNormRpowStatement
section
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_gaussianExtension_norm_rpow : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (t : ℝ), 1 < t → Finite ((NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))ˣ ⧸ (Units.map (algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers (GlobalTheory.GaussExt.Ext F))).toMonoidHom).range) → Summable (fun c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) => |((Algebra.norm ℚ (GlobalTheory.GaussExt.gEmb F c.out.1) : ℚ) : ℝ)| ^ (-t)) := by
  first | exact @GlobalTheory.GaussSum.summable_gauss_norm | exact GlobalTheory.GaussSum.summable_gauss_norm | (intros; apply GlobalTheory.GaussSum.summable_gauss_norm <;> assumption)
end

