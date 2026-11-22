import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0061
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0053
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0028
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0227
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0229
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelsAreCoverSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchurUnitaryIrreducibleScalar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinerContractionOnePlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0239

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRealScalarCharacterWeakWeil
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.RealChar

variable {D : D7} {S T : HSp D}

theorem realPt_zero (C : Ctx S T) : C.realPt 0 = 0 := by
  funext σ k a
  simp [Ctx.realPt, compAt]

theorem th_zero_eq (C : Ctx S T) {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {φ : TF S.rank C.g}
    (hφ : SW.IsSB φ) : C.Th x φ 0 = thR C.X C.bas C.idx φ x 0 := by
  have h0 : IsRealPt (0 : WO S T) := by
    ext i j
    simp
  rw [(GlobalTheory.Ker.ZakEx.isZak_Th D S T C x hx φ hφ).1.2 0 h0, realPt_zero]

theorem th_zero_eq_thP (C : Ctx S T) {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {φ : TF S.rank C.g}
    (hφ : SW.IsSB φ) : C.Th x φ 0 = thP C.X C.hr C.bas C.idx φ 1 x := by
  have h := (GlobalTheory.SW.one_mem_rowHighest_and_thP_smul_one D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank).2 1 φ x
  rw [one_smul, one_mul] at h
  rw [h, th_zero_eq C hx hφ, thR]
  have hz : zR C.X C.idx x (0 : WR C.X S.rank) = 0 := by
    funext k i
    simp [zR, hermC]
  rw [hz, GlobalTheory.Ker.RealScalar.gaussR_zero C x, one_mul, thA]
  simp
  exact Or.inl rfl

theorem continuous_th_mvB (C : Ctx S T) (B : C.Bas) (hB : C.IsB B) (φ : TF S.rank C.g) (hφ : SW.IsSB φ) :
    Continuous (fun a : GA D T => C.Th (C.xB (C.mvB a B)) φ 0) := by
  have hS := fun B (hB : C.IsB B) => (GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB
  have hdom : ∀ a : GA D T, C.xB (C.mvB a B) ∈ C.X.dom := fun a => (hS _ ((hS B hB).2.2.2.2.2 a).1).2.1
  have e : (fun a : GA D T => C.Th (C.xB (C.mvB a B)) φ 0) =
      (thP C.X C.hr C.bas C.idx φ 1) ∘ fun a => C.xB (C.mvB a B) := by
    funext a
    exact th_zero_eq_thP C (hdom a) hφ
  rw [e]
  have hP := (GlobalTheory.SW.theta_holomorphic_weight D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even (fun _ _ => 0)
    (fun _ _ => 0) φ hφ 1 (GlobalTheory.SW.one_mem_rowHighest_and_thP_smul_one D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank).1).1
  refine hP.continuousOn.comp_continuous ?_ hdom
  have hc : ∀ τ, Continuous fun a : GA D T => compAt C.θ τ (Formalism.L2.Theta.mt T a) := fun τ =>
    (GlobalTheory.RealWeil.continuous_compAt C.inf τ T.rank T.rank).comp (GlobalTheory.RealWeil.continuous_mt T).1
  refine continuous_pi fun σ => continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Ctx.xB, Ctx.mvB]
  exact Complex.continuous_conj.comp
    ((continuous_apply j).comp ((continuous_apply i).comp ((hc _).matrix_mul continuous_const)))

theorem exists_th_zero_ne (C : Ctx S T) (B : C.Bas) (hB : C.IsB B) (φ : TF S.rank C.g) (hφ : SW.IsSB φ)
    (h0 : φ ≠ 0) : ∃ φ' : TF S.rank C.g, SW.IsSB φ' ∧ C.Th (C.xB B) φ' 0 ≠ 0 := by
  have hx : C.xB B ∈ C.X.dom := ((GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB).2.1
  have R := GlobalTheory.Ker.thR_laws D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even _ hx φ hφ
  have hd := (GlobalTheory.Ker.zR_laws D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even _ hx).2.2.2.1
  obtain ⟨y, hy⟩ : ∃ y, thR C.X C.bas C.idx φ (C.xB B) (embR C.X y) ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hs : SW.IsSB ((0 : ℂ) • φ) := (isSB_algebra_haar_linear _ _ _ _ _ hφ hφ).2.1 0
    have e : thR C.X C.bas C.idx φ (C.xB B) = thR C.X C.bas C.idx ((0 : ℂ) • φ) (C.xB B) := by
      rw [R.2.2.2.2 0, zero_smul]
      exact hd.equalizer R.1.continuous continuous_const (funext hn)
    exact h0 (((R.2.2.2.1 _ hs).1 e).trans (zero_smul ℂ φ))
  have hs' := ((GlobalTheory.SW.heisG_laws D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even).2.2.2 y φ hφ).1
  refine ⟨_, hs', ?_⟩
  rw [th_zero_eq C hx hs', R.2.1 y 0, zero_add]
  exact mul_ne_zero (Complex.exp_ne_zero _) hy

end GlobalTheory.AdSpan.RealChar

namespace GlobalTheory.AdSpan.RealChar

theorem smul_cancel {α : Type} {F : α → ℂ} (hF : F ≠ 0) {c c' : ℂ} (h : c • F = c' • F) : c = c' := by
  obtain ⟨w, hw⟩ : ∃ w, F w ≠ 0 := by
    by_contra h'
    push_neg at h'
    exact hF (funext h')
  have := congrFun h w
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hw this

variable {D : D7} {S T : HSp D}

theorem th_ne (C : Ctx S T) {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {φ : TF S.rank C.g}
    (hφ : SW.IsSB φ) (h0 : φ ≠ 0) : C.Th x φ ≠ 0 := by
  intro h
  have L := GlobalTheory.Ker.Ctx.th_laws D S T C x hx φ hφ
  have hs : SW.IsSB ((0 : ℂ) • φ) := (isSB_algebra_haar_linear _ _ _ _ _ hφ hφ).2.1 0
  have e : C.Th x φ = C.Th x ((0 : ℂ) • φ) := by rw [L.2.1, h, smul_zero]
  exact h0 (((L.1 _ hs).2 e).trans (zero_smul ℂ φ))

theorem th_zero (C : Ctx S T) {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {φ : TF S.rank C.g}
    (hφ : SW.IsSB φ) (h0 : φ = 0) : C.Th x φ = 0 := by
  have L := GlobalTheory.Ker.Ctx.th_laws D S T C x hx φ hφ
  have e : φ = (0 : ℂ) • φ := by rw [h0, smul_zero]
  rw [e, L.2.1, zero_smul]

theorem kZero_ne (C : Ctx S T) {x₁ x₂ : Frame C.X.Ψ T.rank} (h₁ : x₁ ∈ C.X.dom) (h₂ : x₂ ∈ C.X.dom) :
    kZero C.X C.idx x₁ x₂ (0 : Fin S.rank → Fin C.g → ℂ) 0 ≠ 0 := by
  rw [GlobalTheory.AdTh.Overlap.kZero_zero]
  exact Finset.prod_ne_zero_iff.2 fun τ _ => inv_ne_zero (pow_ne_zero _ (mul_ne_zero
    (DblPoint.det_aLin_ne_zero h₁ h₂ τ) (DblPoint.det_aAnti_ne_zero h₁ h₂ τ)))

theorem realScal_character : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ContT C.ψ om → ∃ z : GA D T → ℂ, (∀ a ∈ GinfC T, ∀ a' ∈ GinfC T, z (a * a') = z a * z a') ∧ (∀ a ∈ GinfC T, ‖z a‖ = 1) ∧ ContinuousOn z (GinfC T : Set (GA D T)) ∧ ∀ B, C.IsB B → ∀ a ∈ GinfC T, RealScal C om B a (z a) := by
  intro D S T C om hom hcont
  obtain ⟨B₀, hB₀⟩ := (GlobalTheory.Ker.onBasis_frame_period D S T C).1
  have hS := fun B (hB : C.IsB B) => (GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB
  have hdom : ∀ B, C.IsB B → C.xB B ∈ C.X.dom := fun B hB => (hS B hB).2.1
  have hmvB : ∀ B, C.IsB B → ∀ g : GA D T, C.IsB (C.mvB g B) := fun B hB g => ((hS B hB).2.2.2.2.2 g).1
  have hex : ∀ B, C.IsB B → ∀ a ∈ GinfC T, ∃ c : ℂ, ‖c‖ = 1 ∧ RealScal C om B a c := fun B hB a ha =>
    GlobalTheory.Ker.RealScalar.om_real_Th D S T C om hom 1 (one_mem _) a ha B hB
  by_cases hne : ∃ φ : TF S.rank C.g, SW.IsSB φ ∧ φ ≠ 0
  swap
  · refine ⟨fun _ => 1, fun _ _ _ _ => (mul_one 1).symm, fun _ _ => norm_one, continuousOn_const,
      fun B hB a ha φ hφ => ?_⟩
    obtain ⟨c, -, hc⟩ := hex B hB a ha
    have h0 : φ = 0 := by
      by_contra h
      exact hne ⟨φ, hφ, h⟩
    rw [hc φ hφ, th_zero C (hdom _ (hmvB B hB a)) hφ h0, smul_zero, smul_zero]
  obtain ⟨φ₀, hφ₀, h0⟩ := hne
  let z : GA D T → ℂ := fun a => if h : a ∈ GinfC T then (hex B₀ hB₀ a h).choose else 1
  have hz : ∀ a (ha : a ∈ GinfC T), ‖z a‖ = 1 ∧ RealScal C om B₀ a (z a) := fun a ha => by
    simp only [z, dif_pos ha]
    exact (hex B₀ hB₀ a ha).choose_spec
  obtain ⟨⟨μ, 𝓕, hμ⟩, hip⟩ := GlobalTheory.Ker.ScalarProduct.ip_basic D S T C
  have hth : ∀ B, C.IsB B → ∀ φ : TF S.rank C.g, SW.IsSB φ → C.IsTh (C.Th (C.xB B) φ) :=
    fun B hB φ hφ => (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ (hdom B hB) φ hφ).1.1

  have hip2 : ∀ B B', C.IsB B → C.IsB B' → ∀ g : GA D T,
      ipO μ 𝓕 (C.Th (C.xB (C.mvB g B)) φ₀) (C.Th (C.xB (C.mvB g B')) φ₀) =
        ipO μ 𝓕 (C.Th (C.xB B) φ₀) (C.Th (C.xB B') φ₀) := fun B B' hB hB' g => by
    rw [GlobalTheory.AdTh.Overlap.ipO_Th C hμ (hdom _ (hmvB B hB g)) (hdom _ (hmvB B' hB' g)) hφ₀ hφ₀,
      GlobalTheory.AdTh.Overlap.ipO_Th C hμ (hdom _ hB) (hdom _ hB') hφ₀ hφ₀, GlobalTheory.AdTh.Overlap.kZero_mvB C hB g]
  have hdbl : dbl C.X C.bas C.idx φ₀ φ₀ 0 ≠ 0 := by
    intro hc
    have h1 := GlobalTheory.AdTh.Overlap.ipO_Th C hμ (hdom _ hB₀) (hdom _ hB₀) hφ₀ hφ₀
    rw [hc, zero_mul] at h1
    exact th_ne C (hdom _ hB₀) hφ₀ h0 ((hip μ 𝓕 hμ _ (hth B₀ hB₀ φ₀ hφ₀)).2.1 h1)
  have hipne : ∀ B B', C.IsB B → C.IsB B' →
      ipO μ 𝓕 (C.Th (C.xB B) φ₀) (C.Th (C.xB B') φ₀) ≠ 0 := fun B B' hB hB' => by
    rw [GlobalTheory.AdTh.Overlap.ipO_Th C hμ (hdom _ hB) (hdom _ hB') hφ₀ hφ₀]
    exact mul_ne_zero hdbl (kZero_ne C (hdom _ hB) (hdom _ hB'))

  have hind : ∀ B, C.IsB B → ∀ a (ha : a ∈ GinfC T), RealScal C om B a (z a) := by
    intro B hB a ha
    obtain ⟨c, -, hc⟩ := hex B hB a ha
    obtain ⟨hzn, hzs⟩ := hz a ha
    suffices e : c = z a by rw [← e]; exact hc
    have t1 := hth B hB φ₀ hφ₀
    have t2 := hth B₀ hB₀ φ₀ hφ₀
    have t1' := hth _ (hmvB B hB a) φ₀ hφ₀
    have t2' := hth _ (hmvB B₀ hB₀ a) φ₀ hφ₀
    have u := ((hip μ 𝓕 hμ _ t1).2.2.2 _ t2).2.2.2.2.2 om hom (1, a)
    have t3 : C.IsTh ((z a) • C.Th (C.xB (C.mvB a B₀)) φ₀) := hzs φ₀ hφ₀ ▸ hom.om_pres (1, a) _ t2
    rw [hc φ₀ hφ₀, hzs φ₀ hφ₀, ((hip μ 𝓕 hμ _ t1').2.2.2 _ t3).2.2.1,
      ((hip μ 𝓕 hμ _ t3).2.2.2 _ t1').2.1, ((hip μ 𝓕 hμ _ t2').2.2.2 _ t1').2.2.1, map_mul,
      ((hip μ 𝓕 hμ _ t1').2.2.2 _ t2').2.1, Complex.conj_conj, hip2 B B₀ hB hB₀ a] at u
    have K := hipne B B₀ hB hB₀
    have h1 : c * conj (z a) = 1 := mul_right_cancel₀ K (by linear_combination u)
    have h2 : z a * conj (z a) = 1 := by
      rw [Complex.mul_conj', hzn]; simp
    calc c = c * (z a * conj (z a)) := by rw [h2, mul_one]
      _ = (c * conj (z a)) * z a := by ring
      _ = z a := by rw [h1, one_mul]
  refine ⟨z, fun a ha a' ha' => ?_, fun a ha => (hz a ha).1, ?_, hind⟩
  ·
    have e1 := hind B₀ hB₀ (a * a') (mul_mem ha ha') φ₀ hφ₀
    have e2 := hind B₀ hB₀ a' ha' φ₀ hφ₀
    have e3 := hind _ (hmvB B₀ hB₀ a') a ha φ₀ hφ₀
    have hm : om (1, a * a') = om (1, a) * om (1, a') := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul]
    rw [hm, Module.End.mul_apply, e2, map_smul, e3, smul_smul,
      ← ((hS B₀ hB₀).2.2.2.2.2 a').2.1 a] at e1
    have := smul_cancel (th_ne C (hdom _ (hmvB B₀ hB₀ (a * a'))) hφ₀ h0) e1
    rw [← this, mul_comm]
  ·
    intro a₀ ha₀
    obtain ⟨φ, hφ, hφ0⟩ := exists_th_zero_ne C _ (hmvB B₀ hB₀ a₀) φ₀ hφ₀ h0
    have hN : Continuous fun a : GA D T => om (1, a) (C.Th (C.xB B₀) φ) 0 :=
      hcont _ (hth B₀ hB₀ φ hφ) 0
    have hD := continuous_th_mvB C B₀ hB₀ φ hφ
    have heq : ∀ a ∈ GinfC T, C.Th (C.xB (C.mvB a B₀)) φ 0 ≠ 0 →
        om (1, a) (C.Th (C.xB B₀) φ) 0 / C.Th (C.xB (C.mvB a B₀)) φ 0 = z a := fun a ha hne => by
      rw [hind B₀ hB₀ a ha φ hφ, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hne, mul_one]
    refine ContinuousWithinAt.congr_of_eventuallyEq
      ((hN.continuousAt.div hD.continuousAt hφ0).continuousWithinAt) ?_ (heq a₀ ha₀ hφ0).symm
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hD.continuousAt.eventually_ne hφ0)] with a ha hne
    exact (heq a ha hne).symm

end GlobalTheory.AdSpan.RealChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegerConjPrescribedResiduesPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_conj_prescribed_residues_places : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (b : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Formalism.L2.DIV.kP PP), ∃ c : 𝓞 D.host.E, ∀ PP ∈ P, Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar c) = b PP := by
  first | exact @GlobalTheory.SW.Lev.exists_bar_mk_eq_at_places | exact GlobalTheory.SW.Lev.exists_bar_mk_eq_at_places | (intros; apply GlobalTheory.SW.Lev.exists_bar_mk_eq_at_places <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKEquivariantGraphGoursatStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kEquivariant_graph_goursat : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S S' U : Submodule ℂ H), Formalism.MainNotions.S.IsKStableOn ε ρ S → Formalism.MainNotions.S.IsKStableOn ε ρ S' → Formalism.MainNotions.S.IsKStableOn ε ρ U → (∀ T : Submodule ℂ H, T ≤ S → Formalism.MainNotions.S.IsKStableOn ε ρ T → T = ⊥ ∨ T = S) → (∀ T : Submodule ℂ H, T ≤ S' → Formalism.MainNotions.S.IsKStableOn ε ρ T → T = ⊥ ∨ T = S') → S ⊓ S' = ⊥ → U ≤ S ⊔ S' → U ⊓ S = ⊥ → U ⊓ S' = ⊥ → U ≠ ⊥ → ∃ φ : H →ₗ[ℂ] H, (∀ k ∈ Formalism.REAL.Kset ε, ∀ u ∈ S, φ (ρ k u) = ρ k (φ u)) ∧ S.map φ = S' := by
  first | exact @GlobalTheory.KStableGraph.exists_kMap_onto | exact GlobalTheory.KStableGraph.exists_kMap_onto | (intros; apply GlobalTheory.KStableGraph.exists_kMap_onto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIsometryDiscreteSeriesModelDetCover
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.KFiniteTie

open GlobalTheory.CoverModel GlobalTheory.Chain.RealIt.LocalFromCover
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (toFrame)

section Semi

variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {cj : Bool} {U : H → H'}

theorem cjc_ofReal (cj : Bool) (r : ℝ) : cjc cj (r : ℂ) = r := by
  cases cj <;> simp [cjc]

theorem exists_real (hadd : ∀ x y, U (x + y) = U x + U y) (hs : ∀ (z : ℂ) x, U (z • x) = cjc cj z • U x)
    (hb : Function.Bijective U) (hn : ∀ x, ‖U x‖ = ‖x‖) : ∃ L : H ≃ₗᵢ[ℝ] H', ∀ x, L x = U x := by
  let L₀ : H →ₗᵢ[ℝ] H' :=
    { toFun := U
      map_add' := hadd
      map_smul' := fun r x => by
        rw [← Complex.coe_smul, hs, cjc_ofReal, Complex.coe_smul, RingHom.id_apply]
      norm_map' := hn }
  exact ⟨LinearIsometryEquiv.ofSurjective L₀ hb.2, fun _ => rfl⟩

theorem inner_map (hadd : ∀ x y, U (x + y) = U x + U y) (hs : ∀ (z : ℂ) x, U (z • x) = cjc cj z • U x)
    (hn : ∀ x, ‖U x‖ = ‖x‖) (w x : H) : ⟪U w, U x⟫_ℂ = cjc cj ⟪w, x⟫_ℂ := by
  have hre : ∀ w x : H, (⟪U w, U x⟫_ℂ).re = (⟪w, x⟫_ℂ).re := fun w x => by
    have h1 := re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (𝕜 := ℂ) (U w) (U x)
    have h2 := re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (𝕜 := ℂ) w x
    rw [← hadd, hn, hn, hn, ← h2] at h1
    exact h1
  have h1 := hre w x
  have h2 := hre w (Complex.I • x)
  rw [hs, inner_smul_right, inner_smul_right] at h2
  cases cj
  · apply Complex.ext <;> simp_all [cjc]
  · apply Complex.ext
    · simp only [cjc, if_true, Complex.conj_re]
      exact h1
    · simp only [cjc, if_true, Complex.conj_im] at h2 ⊢
      simpa using h2

end Semi

theorem isFormIso_phi {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) (br : Bool) :
    IsFormIso ε (phi br e) := by
  cases br
  · exact isFormIso_plainMat h
  · exact isFormIso_barMat h

theorem exists_kTie : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (p q : ℕ) (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ) (c : ℚ) (br cj : Bool) (e : Ix p q ≃ Fin V.rank) (m : ℤ) (U : M.H τ → R.U.H), IsParam lam → IsOrd (M.ε τ) (M.lam τ) lam c (sg br cj) e → (m : ℚ) = 2 * c → Comparison₂ R M τ br cj e m U → (∀ x v, U x = R.ι v → (IsHighestUnit (M.ε τ) (M.lam τ) (M.σ τ) x ↔ UnitHW R (blattner lam) v)) → ∃ u, KTie R M τ lam c br cj e u := by
  intro D V S M τ p q T R lam c br cj e m U hpar hord hm hT hhi
  have hφ := isFormIso_phi hord.1 br
  obtain ⟨L, hL⟩ := exists_real hT.add hT.smul hT.bij hT.norm
  have hr : ∀ v : kfin M τ, ∃ y, R.ι y = U v := by
    rintro ⟨v, hv⟩
    change U v ∈ LinearMap.range R.ι
    induction hv using Submodule.span_induction with
    | mem x hx => exact (hT.kfin x).1 hx
    | zero => rw [← hL, map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [hT.add]; exact add_mem hx hy
    | smul z x _ hx => rw [hT.smul]; exact Submodule.smul_mem _ _ hx
  choose u hu using hr
  have hmC : (m : ℂ) = 2 * (c : ℂ) := by exact_mod_cast hm
  have hgrp : ∀ (g : T.G) (x : M.H τ), U (M.σ τ (phi br e ((T.cov g : GL (Ix p q) ℂ) : Mat p q)) x) =
      ((T.sq g : ℂˣ) : ℂ) ^ m • R.U.π g (U x) := fun g x => by
    rw [hT.grp, smul_smul, ← zpow_add₀ (Units.ne_zero _), add_neg_cancel, zpow_zero, one_smul]
  refine ⟨u, hpar, hord, fun x y => R.ι_inj ?_, fun z x => R.ι_inj ?_, ⟨fun x y h => ?_, fun y => ?_⟩, ?_,
    fun Z hZ v v' => ?_, fun v => hhi _ _ (hu v).symm, fun m' hm' g v w => ?_⟩
  · rw [map_add, hu, hu, hu, Submodule.coe_add, hT.add]
  · rw [map_smul, hu, hu, Submodule.coe_smul, hT.smul]
  · exact Subtype.ext (hT.bij.1 (by rw [← hu, ← hu, h]))
  · obtain ⟨x, hx⟩ := hT.bij.2 (R.ι y)
    exact ⟨⟨x, Submodule.subset_span ((hT.kfin x).2 ⟨y, hx.symm⟩)⟩, R.ι_inj (by rw [hu]; exact hx)⟩
  · change (fun Z => toFrame M τ (phi br e Z)) '' _ = _
    rw [← toFrame_image M τ, ← Set.image_image (toFrame M τ) (phi br e)]
    congr 1
    ext Y
    obtain ⟨Z, rfl⟩ := hφ.bij.2 Y
    rw [hφ.bij.1.mem_set_image, ← hφ.mem_lie]
    rfl
  · have h1 := (hasDerivAt_sq_zpow T m hZ).fun_smul (R.der Z hZ (u v))
    have h2 : HasDerivAt (fun t : ℝ => L (M.rep τ (NormedSpace.exp (t • phiFr (M.fr τ) br e Z)) (v : M.H τ)))
        (R.ι (R.HK.act Z (u v) + ((c : ℂ) * Z.trace) • u v)) 0 := by
      convert h1 using 1
      · funext t
        have h3 := rep_exp M τ (phi br e Z) t
        rw [hL, show phiFr (M.fr τ) br e Z = toFrame M τ (phi br e Z) from rfl, h3, hφ.exp,
          ← T.expt_cov _ (GlobalTheory.RealPar.KStabLie.smul_mem_upq hZ t), hgrp, hu]
      · rw [hmC, show 2 * (c : ℂ) * (Z.trace / 2) = c * Z.trace by ring]
        simp [T.expt_zero]
    constructor
    · intro h
      have h3 := L.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
      refine R.ι_inj ?_
      rw [hu, ← hL]
      exact h3.unique h2
    · intro h
      rw [← h, hu, ← hL] at h2
      have h3 := L.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
      unfold VecDer
      convert h3 using 1
      · funext t; simp
      · simp
  · obtain rfl : m' = m := by exact_mod_cast hm'.trans hm.symm
    rw [← inner_map hT.add hT.smul hT.norm, hgrp, inner_smul_right, hu, hu]

end GlobalTheory.ArchRec.KFiniteTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNonzeroKFiniteStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_k_finite : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] [Nontrivial V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsURepOn (UJset ε) π → ∃ v, IsKFin ε π v ∧ v ≠ 0 := by
  first | exact @GlobalTheory.KFinExists.exists_kfin | exact GlobalTheory.KFinExists.exists_kfin | (intros; apply GlobalTheory.KFinExists.exists_kfin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinerContractionOnePlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.RealLine
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realIntertwiner_contraction_one_place : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) [DecidableEq D.what₂.Tau], IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.CompactFock ψ θ M M' ω f τ aS aT → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.LieFock ψ θ M M' ω f τ aS aT → IsItW θ M M' ω (ptOf ψ θ M M' f) It → ∀ (v : M'.Vec) (w : ∀ ρ, M.H ρ), ∃ A : PolF D W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ, SemiW M M' τ aS aT A ∧ ∀ φ y u, ⟪u, A φ y⟫_ℂ = ellT M (Function.update w τ u) (inclT M (It φ (PiTensorProduct.tprod ℂ (Function.update v τ y)))) := by
  first | exact @GlobalTheory.Chain.RealLine.Semi.exists_semiW | exact GlobalTheory.Chain.RealLine.Semi.exists_semiW | (intros; apply GlobalTheory.Chain.RealLine.Semi.exists_semiW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealPlaceThetaObjectsTheoremARPartsStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_provA_discreteSeries_archimedeanRallis : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∃ X : ProvA, (∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → HasParam (X.ds p q lam) lam) ∧ DiscreteSeriesBlattner X ∧ admQ5 X ∧ ArchimedeanRallisFirst X ∧ ArchimedeanRallisSecond X ∧ ArchimedeanRallisUpDownLine X ∧ ArchimedeanRallisFifth X := by
  first | exact @GlobalTheory.RealPlaceTheta.exists_record_theta | exact GlobalTheory.RealPlaceTheta.exists_record_theta | (intros; apply GlobalTheory.RealPlaceTheta.exists_record_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParameterSphericalUnramifiedUnitary
section
noncomputable section

namespace GlobalTheory.LFun.ExSatU

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun

theorem exists_hasSatU : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (ϖ : w.adicCompletion E) (σ : w.adicCompletion E →+* w.adicCompletion E) (q n : ℕ),
    IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V),
    ρ.IsIrreducible → IsAdmissible ρ → GlobalTheory.LGrp.IsSpherical ρ (KU σ n) → ∃ α, HasSatU ϖ q ρ α := by
  intro E _ _ w ϖ σ q n hU V _ _ ρ hi ha hs
  obtain ⟨ho, hc⟩ := GlobalTheory.T.isOpen_isCompact_unitaryIntegralPoints (w.adicCompletion E) ϖ σ q n hU
  exact GlobalTheory.LFun.SatCompare.exists_hasSatU hU ⟨ha.1, hi⟩ (ha.2 _ ho hc) hs

end GlobalTheory.LFun.ExSatU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignCompatibleNumberingDecreasingEnumeratiStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_signCompatible_numbering_decreasing_enumeration : ∀ (n p q : ℕ) (l₁ l₂ : List ℚ) (c : ℚ) (br cj : Bool) (ε : Fin n → Bool) (lamM : Fin n → ℝ), l₁.length = p → l₂.length = q → IsParam (ofBlocks l₁ l₂ : Ix p q → ℚ) → IsEnum (parOf br cj l₁ l₂ c) lamM ε → ∃ e : Ix p q ≃ Fin n, IsOrd ε lamM (ofBlocks l₁ l₂) c (sg br cj) e := by
  first | exact @GlobalTheory.ArchRec.EnumBlocks.exists_isOrd | exact GlobalTheory.ArchRec.EnumBlocks.exists_isOrd | (intros; apply GlobalTheory.ArchRec.EnumBlocks.exists_isOrd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitarySpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.SpanMod

variable {r s : ℕ}

theorem exists_unitary_span (r s : ℕ) (W U I : Type) [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup U]
    [InnerProductSpace ℂ U] (a : Mat r s →ₗ[ℂ] Module.End ℂ W) (b : Mat r s → Module.End ℂ U)
    (j : I → W →ₗ[ℂ] U) (ha : IsGK a) (hb : IsUAct b)
    (hj : ∀ i, ∀ Z ∈ upq r s, ∀ P, j i (a Z P) = b Z (j i P)) :
    ∃ (MM : UGKMod r s) (inc : MM.M.V →ₗ[ℂ] U), Function.Injective inc ∧
      LinearMap.range inc = Submodule.span ℂ {y | ∃ i P, y = j i P} ∧
      ∀ Z ∈ upq r s, ∀ y, inc (MM.M.act Z y) = b Z (inc y) := by
  first
  | exact @_root_.GlobalTheory.RealPartAdjointAction.main
  | exact _root_.GlobalTheory.RealPartAdjointAction.main
  | (apply _root_.GlobalTheory.RealPartAdjointAction.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RealPartAdjointAction.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RealPartAdjointAction.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RealPartAdjointAction.main ..)

end GlobalTheory.ArchRec.SpanMod
end

