import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0060
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0041
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0059
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilPairLevelTrivialMapsLevelVectorStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0066
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0073
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0058
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0062
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0031
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0054
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0064
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0046
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0042
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0486
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0465
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0480
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0488
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.NormalFrameClauses
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesExistG2OfStandardLattices
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0061
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealSmulSplit

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReadOffFormsAutomorphicInverseMultiplier
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.AutRead

theorem lact_rmul {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (γ : GL (Fin r) E) (y b : Frame Ψ r) :
    lact γ (rmul y b) = rmul (lact γ y) b := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map ⇑(τ : E →+* ℂ) * (mat y τ * mat b τ) =
    (γ : Matrix (Fin r) (Fin r) E).map ⇑(τ : E →+* ℂ) * mat y τ * mat b τ
  rw [Matrix.mul_assoc]

theorem ip_smul_self {n g : ℕ} (t : ℂ) {v : TF n g} (hv : SW.IsSB v) :
    SW.ip (t • v) (t • v) = (t * conj t) * SW.ip v v := by
  have hc : SW.IsSB (fun x : Matrix (Fin n) (Fin g) ℚ => conj (v x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin n) (Fin g) v v hv hv).2.2.2.1
  have hP : SW.IsSB (v * fun x : Matrix (Fin n) (Fin g) ℚ => conj (v x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin n) (Fin g) v _ hv hc).2.2.1
  have e : (fun x : Matrix (Fin n) (Fin g) ℚ => (t • v) x * conj ((t • v) x)) = (t * conj t) • (v * fun x : Matrix (Fin n) (Fin g) ℚ => conj (v x)) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, map_mul]
    ring
  rw [SW.ip, SW.ip, e, (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin n) (Fin g) _ _ hP hP).2.2.2.2.2.1]
  rfl

end GlobalTheory.Ker.AutRead

namespace GlobalTheory.Ker.AutRead

theorem std_mem_Vset {D : D7} {S T : HSp D} (C : Ctx S T) (M : ℕ) (hM : 0 < M) :
    stdL D.host.E S.rank ∈ Vset D.host.E S.rank M := by
  have hs1 : IsMov (fmtC S 1) (stdL D.host.E S.rank) (stdL D.host.E S.rank) := by
    rw [Red.fmtC_one]; exact Red.isMov_one _
  exact (GlobalTheory.T.self_dual_lattices_at_level D S T C).1 M 1 _ hM (Red.trivAt_one _ _) (Red.stdL_fg _) hs1

theorem wG_phi_std {D : D7} {S T : HSp D} (C : Ctx S T) (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ)
    (hM : 0 < M) (hM𝔪 : (M : 𝓞 D.host.E) ∈ Lv.𝔪) (v₀ : Lt D.host.E T.rank → TF S.rank C.g)
    (hv : ∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L))
    (μ : GL (Fin T.rank) D.host.E → Lt D.host.E T.rank → ℂ)
    (hμ : ∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ k : Lv.J, Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) k → wG C.X C.bas C.idx γ (v₀ L) = (μ γ L * (Lv.lam k : ℂˣ)) • v₀ (mapL γ L))
    (γ : GL (Fin T.rank) D.host.E) (hγ : γ ∈ Lv.grp) (L : Lt D.host.E T.rank) (hL : L ∈ Lv.lats) :
    wG C.X C.bas C.idx γ (Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)) =
      μ γ L • Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank) := by
  obtain ⟨-, -, hgrp, hlat, -, -, -⟩ := GlobalTheory.T.level_structure_properties D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn
  obtain ⟨hun, k, hkJ, hred⟩ := (hgrp γ).1 hγ
  have hL' : mapL γ L ∈ Lv.lats := ((hlat L hL).2.2.2 γ hγ).1
  have e1 := hμ γ hγ L hL ⟨k, hkJ⟩ hred
  obtain ⟨-, -, hw3, -⟩ := GlobalTheory.T.weil_action_preserves_theta_and_inner_product D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even γ hun (v₀ L) (hv L hL).1
  have hip := (hw3 (v₀ L) (hv L hL).1).1
  rw [e1, ip_smul_self _ (hv _ hL').1, (hv _ hL').2.1, (hv L hL).2.1, mul_one, Complex.mul_conj] at hip
  have hn1 : ‖μ γ L * ((Lv.lam ⟨k, hkJ⟩ : ℂˣ) : ℂ)‖ = 1 := by
    have h2 : Complex.normSq (μ γ L * ((Lv.lam ⟨k, hkJ⟩ : ℂˣ) : ℂ)) = 1 := by exact_mod_cast hip
    rw [Complex.normSq_eq_norm_sq] at h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  rw [(GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv L hL _
    (std_mem_Vset C M hM)).2.2.2 γ hγ ⟨k, hkJ⟩ hred _ hn1 e1, mul_inv_cancel_right₀ (Units.ne_zero _)]

theorem th_phi_ne {D : D7} {S T : HSp D} (C : Ctx S T) (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ)
    (hM : 0 < M) (hM𝔪 : (M : 𝓞 D.host.E) ∈ Lv.𝔪) (v₀ : Lt D.host.E T.rank → TF S.rank C.g)
    (hv : ∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L))
    (B : C.Bas) (hB : C.IsB B) (L : Lt D.host.E T.rank) (hL : L ∈ Lv.lats) :
    C.Th (C.xB B) (Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)) ≠ 0 := by
  intro h0
  have hstd := std_mem_Vset C M hM
  have hx := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.1
  have hsb := (GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv L hL _
    hstd).1
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hx _ hsb
  have hsb0 := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin S.rank) (Fin C.g) _ _ hsb hsb).2.1 0
  have e : C.Th (C.xB B) ((0 : ℂ) • Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)) =
      C.Th (C.xB B) (Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)) := by
    rw [h2, zero_smul, h0]
  have hΦ0 : Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank) = 0 := by
    rw [(h1 _ hsb0).2 e.symm, zero_smul]
  have hip := (GlobalTheory.T.thetaTestFunction_norm_and_overlap_bound D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv L hL _
    hstd).1
  rw [hΦ0, SW.ip] at hip
  have ez : (fun x : Matrix (Fin S.rank) (Fin C.g) ℚ => (0 : TF S.rank C.g) x * conj ((0 : TF S.rank C.g) x)) =
      (0 : ℂ) • (0 : TF S.rank C.g) := by
    funext x; simp
  rw [ez, (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin S.rank) (Fin C.g) _ _ SW.isSB_zero SW.isSB_zero).2.2.2.2.2.1, zero_mul] at hip
  haveI : Finite (𝓞 D.host.E ⧸ Lv.𝔪) := Ideal.finiteQuotientOfFreeOfNeBot _ Lv.ne_bot
  have hpos : 0 < Nat.card Lv.J := Nat.card_pos
  exact (Nat.cast_ne_zero.2 hpos.ne') hip.symm

end GlobalTheory.Ker.AutRead

namespace GlobalTheory.Ker.AutRead

theorem read_off_automorphic : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g) (μ : GL (Fin T.rank) D.host.E → Lt D.host.E T.rank → ℂ), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → (∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ k : Lv.J, Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) k → wG C.X C.bas C.idx γ (v₀ L) = (μ γ L * (Lv.lam k : ℂˣ)) • v₀ (mapL γ L)) → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ F : Lt D.host.E T.rank → Frame C.X.Ψ T.rank → ℂ, (∀ L ∈ Lv.lats, DifferentiableOn ℂ (F L) C.X.dom) → (∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank, F L (rmul x b) = bchar (wtOf C.X C.hr c c' S.rank) b * F L x) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = z a * (ep 1 * cf (gL L)) * F L (C.xB (C.mvB a B))) → ∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, F (mapL γ L) (lact γ x) = (μ γ L)⁻¹ * F L x := by
  intro D S T C om hW Lv hn M hw hM hM𝔪 B hB f' hbase c c' z φ hz hφQ hK v₀ μ hv hμ ep cf hep gL hgL F hFhol hFb hFφ
    γ hγ L hL
  obtain ⟨hΛl, -, hgrp, hlat, -, -, -⟩ := GlobalTheory.T.level_structure_properties D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn
  obtain ⟨hun, k0, hkJ, hred⟩ := (hgrp γ).1 hγ
  have hL' : mapL γ L ∈ Lv.lats := ((hlat L hL).2.2.2 γ hγ).1
  have hJ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2
  have hmv := (hJ B hB).2.2.2.2.2
  obtain ⟨e, he⟩ := (GlobalTheory.T.rational_unitary_group_structure D S T C).1
  have hγA : IsRatOf T γ (e ⟨γ, hun⟩).1 := he ⟨γ, hun⟩
  have hγAQ : (e ⟨γ, hun⟩).1 ∈ GQ T := (e ⟨γ, hun⟩).2
  have hgrpT := (GlobalTheory.T.rational_unitary_group_structure D S T C).2.2.2 T
  have hcomm := hgrpT.2.2.2.1
  obtain ⟨a₀, ha₀, f, hf, hγAe⟩ := hgrpT.2.2.1 (e ⟨γ, hun⟩).1
  set γA := (e ⟨γ, hun⟩).1 with hγAdef
  obtain ⟨g1f, g1t, g1m⟩ := hgL L hL
  obtain ⟨g2f, g2t, g2m⟩ := hgL (mapL γ L) hL'
  have hk := GlobalTheory.T.rationalLevelPoint_finitePart_mem_levelGroup D S T C Lv γ ⟨k0, hkJ⟩ hred a₀ f (gL L) (gL (mapL γ L)) L ha₀ hf (hγAe ▸ hγA) g1f g2f g1t g2t
    hL.1.1 (hlat L hL).2.1 hL'.1.1 g1m g2m
  set k := (gL (mapL γ L))⁻¹ * f * gL L with hkdef

  have hstd := std_mem_Vset C M hM
  have hs1 : IsMov (fmtC S 1) (stdL D.host.E S.rank) (stdL D.host.E S.rank) := by
    rw [Red.fmtC_one]; exact Red.isMov_one _
  obtain ⟨hbase0, hu⟩ := (GlobalTheory.T.levelDatumVector_eq_theta_of_testFunction D S T C Lv hn M hw hM hM𝔪 B hB).2 v₀ hv
  obtain ⟨t, ht0, hft⟩ := (GlobalTheory.T.levelDatumVector_eq_theta_of_testFunction D S T C Lv hn M hw hM hM𝔪 B hB).1 f' hbase _ (hv _ hΛl)
  have hk0 : om (1, k) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) =
      C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank)) := by
    have h1 := (hK k ⟨k0, hkJ⟩ hk).1
    rw [hft, hu t, map_smul] at h1
    exact smul_right_injective _ ht0 h1

  have hsb : ∀ L₁ ∈ Lv.lats, SW.IsSB (Lv.phi C.bas hn v₀ L₁ (stdL D.host.E S.rank)) := fun L₁ hL₁ =>
    (GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv L₁ hL₁ _ hstd).1
  have hep1 : ∀ L₁ ∈ Lv.lats, ‖ep 1‖ = 1 ∧ ‖cf (gL L₁)‖ = 1 ∧ om (1, gL L₁)
      (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) =
      (ep 1 * cf (gL L₁)) • C.Th (C.xB B) (Lv.phi C.bas hn v₀ L₁ (stdL D.host.E S.rank)) := by
    intro L₁ hL₁
    obtain ⟨h1, h2, h3⟩ := hgL L₁ hL₁
    have := hep 1 _ (gL L₁) L₁ (one_mem _) (Red.trivAt_one _ _) (Red.stdL_fg _) hs1 h1 h2 hL₁.1.1 h3
    simpa only [Prod.mk_one_one] using this
  have key : ∀ a ∈ GinfC T, F (mapL γ L) (lact γ (C.xB (C.mvB a B))) = (μ γ L)⁻¹ * F L (C.xB (C.mvB a B)) := by
    intro a ha
    have hBa : C.IsB (C.mvB a B) := (hmv a).1
    have ha₀a : a₀ * a ∈ GinfC T := mul_mem ha₀ ha
    have hY : lact γ (C.xB (C.mvB a B)) = C.xB (C.mvB (a₀ * a) B) := by
      rw [← ((hJ _ hBa).2.2.2.2.2 γA).2.2.2.2.2 γ hγA, ← (hmv a).2.1 γA, hγAe, mul_assoc,
        ← (hcomm a ha).2.2 f hf, ← mul_assoc, (hmv f).2.1 (a₀ * a), (hmv f).2.2.1 hf]

    have hel : γA * (gL L * a) = gL (mapL γ L) * (a₀ * a) * k := by
      have c1 : a₀ * a * (gL (mapL γ L))⁻¹ = (gL (mapL γ L))⁻¹ * (a₀ * a) := (hcomm _ ha₀a).2.2 _ (inv_mem g2f)
      have c2 : a * f = f * a := (hcomm a ha).2.2 f hf
      have c3 : a * gL L = gL L * a := (hcomm a ha).2.2 _ g1f
      rw [hkdef, hγAe]
      calc a₀ * f * (gL L * a) = a₀ * (f * a) * gL L := by rw [← c3]; group
        _ = gL (mapL γ L) * (a₀ * a * (gL (mapL γ L))⁻¹) * f * gL L := by rw [c1, ← c2]; group
        _ = _ := by group
    have s1 : φ (gL L * a) = φ (gL (mapL γ L) * (a₀ * a)) := by
      rw [← hφQ γA hγAQ, hel, (hK k ⟨k0, hkJ⟩ hk).2]
    rw [hFφ L hL a ha, hFφ (mapL γ L) hL' _ ha₀a] at s1

    have hne : C.Th (C.xB (C.mvB (a₀ * a) B)) (Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank)) ≠ 0 :=
      th_phi_ne C Lv hn M hM hM𝔪 v₀ hv _ (hmv _).1 _ hL'
    have hx : C.xB (C.mvB a B) ∈ C.X.dom := (hJ _ hBa).2.1
    have hX1 : om (1, γA * a * gL L) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) =
        (ep 1 * cf (gL L) * z a * μ γ L) •
          C.Th (C.xB (C.mvB (a₀ * a) B)) (Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank)) := by
      have p : ((1, γA * a * gL L) : GA D S × GA D T) = (1, γA) * ((1, a) * (1, gL L)) := by
        simp only [Prod.mk_mul_mk, one_mul, mul_assoc]
      rw [p, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, (hep1 L hL).2.2, map_smul,
        hz a ha _ (hsb L hL), map_smul, map_smul, ((GlobalTheory.T.weilRep_rationalPoints_thetaFunctions_fock D S T C om hW).2 γ γA hγA _ (hsb L hL)).1 _ hx,
        wG_phi_std C Lv hn M hM hM𝔪 v₀ hv μ hμ γ hγ L hL, hY,
        (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ ((hJ _ (hmv _).1).2.1) _ (hsb _ hL')).2.1, smul_smul, smul_smul]
    have hX2 : om (1, γA * a * gL L) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) =
        (ep 1 * cf (gL (mapL γ L)) * z (a₀ * a)) •
          C.Th (C.xB (C.mvB (a₀ * a) B)) (Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank)) := by
      have c3 : a * gL L = gL L * a := (hcomm a ha).2.2 _ g1f
      have p : ((1, γA * a * gL L) : GA D S × GA D T) = (1, a₀ * a) * ((1, gL (mapL γ L)) * (1, k)) := by
        have eq : γA * a * gL L = a₀ * a * (gL (mapL γ L) * k) := by
          rw [mul_assoc γA, c3, hel, ← mul_assoc (a₀ * a), ← (hcomm _ ha₀a).2.2 _ g2f]
        rw [eq]
        simp only [Prod.mk_mul_mk, one_mul]
      rw [p, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hk0, (hep1 _ hL').2.2, map_smul,
        hz _ ha₀a _ (hsb _ hL'), smul_smul]
    have hsc : ep 1 * cf (gL L) * z a * μ γ L = ep 1 * cf (gL (mapL γ L)) * z (a₀ * a) :=
      smul_left_injective ℂ hne (hX1.symm.trans hX2)

    have hza : z a ≠ 0 := by
      intro h0
      have h1 := hz a ha _ (hsb L hL)
      rw [h0, zero_smul] at h1
      have h2 : om (1, a⁻¹) (om (1, a) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)))) =
          C.Th (C.xB B) (Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)) := by
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, inv_mul_cancel, Prod.mk_one_one, map_one,
          Module.End.one_apply]
      rw [h1, map_zero] at h2
      exact th_phi_ne C Lv hn M hM hM𝔪 v₀ hv B hB L hL h2.symm
    have hep0 : ep 1 ≠ 0 := fun h0 => by
      have := (hep1 L hL).1; rw [h0, norm_zero] at this; exact zero_ne_one this
    have hcf0 : cf (gL L) ≠ 0 := fun h0 => by
      have := (hep1 L hL).2.1; rw [h0, norm_zero] at this; exact zero_ne_one this
    have hμ0 : μ γ L ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hsc
      have hcf1 : cf (gL (mapL γ L)) ≠ 0 := fun h1 => by
        have := (hep1 _ hL').2.1; rw [h1, norm_zero] at this; exact zero_ne_one this
      have hz1 : z (a₀ * a) ≠ 0 := by
        intro h1
        have h3 := hz _ ha₀a _ (hsb _ hL')
        rw [h1, zero_smul] at h3
        have h2 : om (1, (a₀ * a)⁻¹) (om (1, a₀ * a) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank)))) =
            C.Th (C.xB B) (Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank)) := by
          rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, inv_mul_cancel, Prod.mk_one_one, map_one,
            Module.End.one_apply]
        rw [h3, map_zero] at h2
        exact th_phi_ne C Lv hn M hM hM𝔪 v₀ hv B hB _ hL' h2.symm
      exact mul_ne_zero (mul_ne_zero hep0 hcf1) hz1 hsc.symm
    rw [hY]
    have hinv : μ γ L * (μ γ L)⁻¹ = 1 := mul_inv_cancel₀ hμ0
    have hq : z a * ep 1 * cf (gL L) * μ γ L ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hza hep0) hcf0) hμ0
    apply mul_left_cancel₀ hq
    linear_combination (F (mapL γ L) (C.xB (C.mvB (a₀ * a) B))) * hsc - s1 -
      (z a * ep 1 * cf (gL L) * F L (C.xB (C.mvB a B))) * hinv
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := GlobalTheory.T.domain_frame_eq_real_translate_mul_borel D S T C B hB x hx
  have hxa : C.xB (C.mvB a B) ∈ C.X.dom := (hJ _ (hmv a).1).2.1
  have hya : lact γ (C.xB (C.mvB a B)) ∈ C.X.dom := by
    rw [← ((hJ _ (hmv a).1).2.2.2.2.2 γA).2.2.2.2.2 γ hγA, ← (hmv a).2.1 γA]
    exact (hJ _ (hmv _).1).2.1
  rw [lact_rmul, hFb _ hL' _ hya b hb, hFb L hL _ hxa b hb, key a ha]
  ring

end GlobalTheory.Ker.AutRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SkewSpaceLineOneParamFockDerivative
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

namespace GlobalTheory.LieLines

theorem line_deriv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X)
    (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ), IsInfFam θ →
    IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
    ∀ (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E X.rank)
      (hJ : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank))),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Ws,
      ∃ (h : ℝ → GA D X) (Y : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ τ, Y τ ∈ lieAt X τ) ∧
        (∀ t : ℝ, γ (Multiplicative.ofAdd t) = GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hJ (h t)) ∧
        ∀ f₀ : WO (sgn ε M) X → ℂ, IsVacF ψ θ (frSgn ε A) B f₀ → ∀ (P : PolF D X.rank M.rank) (z : WO (sgn ε M) X),
          HasDerivAt (fun t : ℝ => ω (1, h t) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) z)
            (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ (∑ τ, GlobalTheory.RealQuot.actT ε A B eS τ (Y τ) P) z) 0 := by
  classical
  intro D ψ θ ε M X A B χS χT ω eS eT hθ hω hexp Ws hJ γ hγ
  obtain ⟨L, hL⟩ : ∃ L : GlobalTheory.SmoothForms.LieN X, ∀ t : ℝ, γ (Multiplicative.ofAdd t) =
      GlobalTheory.TripleRead.toUX X (Equiv.refl (Fin X.rank)) hJ (GlobalTheory.SmoothForms.expInf θ X (t • L)) :=
    GlobalTheory.T.archLine_transposeGramUnitary_eq_exp D θ hθ X Ws hJ γ hγ
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ X
  refine ⟨fun t => GlobalTheory.SmoothForms.expInf θ X (t • L), fun τ => (L τ).1, fun τ => (L τ).2, hL, ?_⟩
  intro f₀ hf P z
  have hω' : IsWeilDatumO ψ (sgn ε M) X χS χT (WRep.toSgn ε ω) := hω
  have hψ := hω'.std
  have h1g : ∀ (g : GA D X), WRep.toSgn ε ω (1, g) = ω (1, g) := fun g => by
    simp [WRep.toSgn]
  have hlin : ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ (∑ τ, GlobalTheory.RealQuot.actT ε A B eS τ (L τ).1 P) =
      ∑ τ, ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ (GlobalTheory.RealQuot.actT ε A B eS τ (L τ).1 P) := map_sum _ _ _
  rcases isEmpty_or_nonempty D.what₂.Tau with hT | ⟨⟨τ₀⟩⟩
  · have e : ∀ t : ℝ, t • L = L := fun t => funext fun τ => (IsEmpty.false τ).elim
    simp only [e, hlin, Finset.univ_eq_empty, Finset.sum_empty, Pi.zero_apply]
    exact hasDerivAt_const _ _
  have hth : ∀ Q, IsThetaFunO ψ (sgn ε M) X (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ Q) :=
    (GlobalTheory.LieScalar.ptF_laws hθ hψ (frSgn ε A) B hf).1 τ₀
  let 𝒮 : Set (GA D X → ℂ) :=
    {φ | ∃ f z, IsThetaFunO ψ (sgn ε M) X f ∧ φ = fun g => WRep.toSgn ε ω (1, g) f z}
  have hc : ∀ φ ∈ 𝒮, Continuous φ := by
    rintro _ ⟨f, z, hf, rfl⟩
    exact (hω'.om_cont f hf z).comp (continuous_const.prodMk continuous_id)
  have hd : ∀ φ ∈ 𝒮, ∀ τ', ∀ Z ∈ lieAt X τ', ∃ φ' ∈ 𝒮, ∀ g,
      HasDerivAt (fun t : ℝ => φ (g * oneP θ X τ' Z t)) (φ' g) 0 := by
    rintro _ ⟨f, z, hf, rfl⟩ τ' Z hZ
    obtain ⟨G, hG', h⟩ := GlobalTheory.LieScalar.genT hθ hω' τ' Z hZ f hf
    refine ⟨_, ⟨G, z, hG', rfl⟩, fun g => ?_⟩
    have := h (MonoidHom.inr (GA D (sgn ε M)) (GA D X) g) z
    simpa only [MonoidHom.inr_apply, Prod.mk_mul_mk, mul_one] using this
  let φ : GA D X → ℂ := fun g => WRep.toSgn ε ω (1, g) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) z
  have hφ : φ ∈ 𝒮 := ⟨_, z, hth P, rfl⟩
  have h1 := GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ X 𝒮 hc hd φ hφ
  have h2 : GlobalTheory.SmoothForms.Sm (GlobalTheory.SmoothForms.expInf θ X) φ :=
    (GlobalTheory.SmoothForms.isSmoothInf_iff φ).1 ((GlobalTheory.SmoothForms.smooth_iff R φ).1 h1)
  have h3 := ((h2 1).differentiable (by simp) 0).hasFDerivAt
  have hline : ∀ V : GlobalTheory.SmoothForms.LieN X, HasDerivAt (fun t : ℝ => φ (GlobalTheory.SmoothForms.expInf θ X (t • V)))
      (fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0 V) 0 := by
    intro V
    have h4 : HasDerivAt (fun t : ℝ => t • V) V 0 := by
      have h := (hasDerivAt_id (0 : ℝ)).smul_const V
      rwa [one_smul] at h
    have h3' : HasFDerivAt (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y))
        (fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0) ((0 : ℝ) • V) := by
      rw [zero_smul]
      exact h3
    have h5 := HasFDerivAt.comp_hasDerivAt (0 : ℝ) h3' h4
    simpa only [Function.comp_def, one_mul] using h5
  have hτ : ∀ τ, fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0
      (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X) =
      ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ (GlobalTheory.RealQuot.actT ε A B eS τ (L τ).1 P) z := by
    intro τ
    have hl := (GlobalTheory.LieScalar.lieFockAll D (sgn ε M) X (frSgn ε A) B θ ψ χS χT (WRep.toSgn ε ω) f₀ τ (eS τ) (eT τ)
      hθ hω' (hexp τ).1 (hexp τ).2 hf).2 (L τ).1 (L τ).2 P z
    have e := (hline (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X)).unique
      (hl.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
        show φ _ = _
        simp only [φ]
        rw [GlobalTheory.SmoothForms.oneP_eq R τ (L τ) t]
        rfl))
    rw [e]
    rfl
  have hsum : ∑ τ, (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X) = L := Finset.univ_sum_single L
  have e1 : (fun t : ℝ => ω (1, GlobalTheory.SmoothForms.expInf θ X (t • L)) (ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ P) z) =
      fun t => φ (GlobalTheory.SmoothForms.expInf θ X (t • L)) := funext fun t => by simp only [φ, h1g]
  rw [e1, hlin, Finset.sum_apply]
  have e2 : fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0 L =
      ∑ τ, ptF (V := sgn ε M) ψ θ (frSgn ε A) B f₀ (GlobalTheory.RealQuot.actT ε A B eS τ (L τ).1 P) z := by
    have h7 := map_sum (fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0)
      (fun τ => (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X)) Finset.univ
    have h8 : fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0 L =
        fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0
          (∑ τ, (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X)) := by
      congr 1
      exact hsum.symm
    have h9 : fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0 L =
        ∑ τ, fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN X => φ (1 * GlobalTheory.SmoothForms.expInf θ X Y)) 0
          (Pi.single τ (L τ) : GlobalTheory.SmoothForms.LieN X) := by
      exact h8.trans h7
    rw [h9]
    exact Finset.sum_congr rfl fun τ _ => hτ τ
  have h6 := hline L
  rwa [e2] at h6

end GlobalTheory.LieLines

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SquareNuHeckeCharacterNotUnramifiedAtChosenPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri FieldCond)

namespace GlobalTheory.RowTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem squareNuHeckeCharacter_not_unramified_at_chosenPlace {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m) :
    ¬ (SqNum.nuH G t i j).UnrAt (G.pl.w G.pl.v0) := by
  intro hnu

  have hunder : (G.pl.w G.pl.v0).under (𝓞 D.host.F) = G.pl.v0 :=
    G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
  have hnotS1 : G.pl.v0 ∉ S1 D := G.ch.basePlace_not_mem_chiGridBadPlaces

  have hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q t →
      PP.under (𝓞 D.host.F) ≠ (G.pl.w G.pl.v0).under (𝓞 D.host.F) := by
    intro PP hPP
    rw [hunder]
    rcases hPP with hP | hP
    · intro heq
      apply hnotS1
      obtain ⟨k, hk⟩ := (hL.Pg PP).1 hP
      have hmem := GlobalTheory.LevelPlaces.mem_of_div L.C.P k PP hk
      have hF : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (PP.under (𝓞 D.host.F)).asIdeal := by
        simpa using hmem
      rw [← heq, S1_mem_OmF]
      fin_cases k
      · exact Or.inl hF
      · exact Or.inr (Or.inl hF)
    · exact G.pl.levelPlace_ne_basePlace t PP hP
  obtain ⟨hxi, hmu⟩ := (GlobalTheory.levCh_unramified_places D T L μ₀ hL t).2.2.2 _ hoff

  have hchi := (G.ch.lev0 (D.R.m - i) (by omega) (by omega) _ hunder).2
  apply hchi
  intro x hx
  have h := hnu x hx
  simp only [SqNum.nuH, div_eq_mul_inv, HChar.loc_mul, HChar.loc_inv, hmu j x hx, hxi x hx, one_mul] at h
  exact inv_eq_one.mp h

end GlobalTheory.RowTest

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncationFamilyPlaceAdditiveStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncation_family_place_additive : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ Q, IsPar Q → (∀ Tr, Continuous fun x => Yfam Φ (levelAll D.sp.cm.sig V.gram L a) x Tr Q) ∧ ∀ S, ∀ y ∈ atPts D.sp.cm.sig V.gram S, ∀ z ∈ awayPts D.sp.cm.sig V.gram S, ∀ Tr, Yfam Φ (levelAll D.sp.cm.sig V.gram L a) (y * z) Tr Q = (Yfam Φ (levelAll D.sp.cm.sig V.gram L a) y 0 Q - Yfam Φ (levelAll D.sp.cm.sig V.gram L a) 1 0 Q) + Yfam Φ (levelAll D.sp.cm.sig V.gram L a) z Tr Q := by
  first | exact @GlobalTheory.TruncKer.yfam_continuous_add | exact GlobalTheory.TruncKer.yfam_continuous_add | (intros; apply GlobalTheory.TruncKer.yfam_continuous_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VertexAtOfLevTransport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mi Formalism.IndefR.Seed.Frm IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VertexFromTransport

theorem vertexAt_of_levTransport : ∀ {D : D7} {T : Type} (L : LevCh D T), (∀ PP, PP ∈ L.Pg ↔ ∃ l, L.C.P.Div l PP) →
    ∀ i : Fin D.R.m, GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.Transport L.Pg (Wc D i) (Yc D 0) (L.βW i) (L.βY 0) →
    ∃ (eW : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W ((i : ℕ) + 1)).rank)
      (ι : GL (Fin (D.sp.W ((i : ℕ) + 1)).rank) (Formalism.IndefR.Lev.EAf D)),
      VertexAt ((i : ℕ) + 1) (betaYOf L.βY 0) (L.βW i) eW ι L.Pg := by
  intro D T L _ i ht
  have hr : (D.sp.Y 0).rank = (D.sp.W ((i : ℕ) + 1)).rank := by
    rw [D.sp.Y_rank 0 (Nat.zero_le _), D.sp.W_rank _ (by omega) (by omega)]
    simp [Ranks.rankY]
  exact GlobalTheory.NormalFramesLevels.vertexAt_of_transport L.Pg _ hr _ _
    (GlobalTheory.NormalFramesLevels.transport_betaYOf L.Pg (Wc D i) (L.βW i) L.βY ht)

end GlobalTheory.VertexFromTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionRealPointFockVectorsScalarColumnActionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilAction_realPoint_fockVectors_scalar_columnAction : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ B, C.IsB B → ∀ f, C.IsTh f → C.IsFock B f → ∀ h ∈ GinfC S, ∃ c : ℂ, c ≠ 0 ∧ ∀ Q Q' : MvPolynomial (FVar D T.rank S.rank) ℂ, C.toH Q' = Harm.colActHom (GlobalTheory.Ker.ColChange.colU C h) (C.toH Q) → om (h, 1) (C.fvec B f Q) = c • C.fvec B f Q' := by
  first | exact @GlobalTheory.Ker.RealColAct.om_real_fvec | exact GlobalTheory.Ker.RealColAct.om_real_fvec | (intros; apply GlobalTheory.Ker.RealColAct.om_real_fvec <;> assumption)
end

