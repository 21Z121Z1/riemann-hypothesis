import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0048
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0049
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0036
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicCuspFormAutomorphicBoundedSquareIntegrable
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Topology

namespace GlobalTheory.AdelicCusp

theorem adel_muPin_automorphic {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    {V : HSp D} {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r} {Kf : Subgroup (GA D V)}
    {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hd : DictIsUnif V dict Kf th hr) (hloc : GlobalTheory.DictLocTest.LocClause V dict) {mu : GA D V → ℂ}
    (hmu : MuUnit V dict mu) (hmc : Continuous mu) {c : Comp → ℂ} (hc : CUnit c) (s : ℂ)
    (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X) (hPc : ∀ k, ContinuousOn (P k) (X k).dom)
    (hΓ : ∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (lact γ x) = P k x) (hfin : supE X la P ≠ ⊤)
    (φ : GA D V → ℂ) (hφ : ∀ g, φ g = s * (c (dict g).1 * mu g * P (dict g).1 (dict g).2)) :
    (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) ∧ (∀ k ∈ Kf, ∀ g, φ (g * k) = mu k * φ g) ∧ Continuous φ ∧
      (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) ∧ MemLp (onQ V φ) 2 (muQ1 V) := by
  obtain ⟨hQ, hK, -, hdom, -, -⟩ := hd
  obtain ⟨hmul, hnorm, hQ1, hunit⟩ := hmu

  have key : ∀ g g' : GA D V, ∀ γ' ∈ (X (dict g).1).Γ, dict g' = ⟨(dict g).1, lact γ' (dict g).2⟩ →
      c (dict g').1 * P (dict g').1 (dict g').2 = c (dict g).1 * P (dict g).1 (dict g).2 := by
    intro g g' γ' hγ' he
    rw [he]
    show c (dict g).1 * P (dict g).1 (lact γ' (dict g).2) = _
    rw [hΓ _ γ' hγ' _ (hdom g)]
  have hφ' : ∀ g, φ g = s * mu g * (c (dict g).1 * P (dict g).1 (dict g).2) := fun g => by
    rw [hφ]; ring
  have hL : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g := by
    intro γ hγ g
    obtain ⟨γ', hγ', he⟩ := hQ γ hγ g
    rw [hφ', hφ', key g _ γ' hγ' he, hmul, hQ1 γ hγ, one_mul]
  have hR : ∀ k ∈ Kf, ∀ g, φ (g * k) = mu k * φ g := by
    intro k hk g
    obtain ⟨γ', hγ', he⟩ := hK k hk g
    rw [hφ', hφ', key g _ γ' hγ' he, hmul]
    ring

  have hC : Continuous φ := by
    rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨N, hN, k, x, hxc, hx⟩ := hloc g₀
    have hloc' : ∀ g ∈ N, c (dict g).1 * P (dict g).1 (dict g).2 = c k * P k (x g) := by
      intro g hg
      obtain ⟨hxd, γ, hγ, he⟩ := hx g hg
      rw [he]
      show c k * P k (lact γ (x g)) = _
      rw [hΓ k γ hγ (x g) hxd]
    have hcont : ContinuousOn (fun g => s * mu g * (c k * P k (x g))) N :=
      (continuousOn_const.mul hmc.continuousOn).mul
        (continuousOn_const.mul ((hPc k).comp hxc fun g hg => (hx g hg).1))
    have heq : (fun g => s * mu g * (c k * P k (x g))) =ᶠ[𝓝 g₀] φ := by
      filter_upwards [hN] with g hg
      rw [hφ', hloc' g hg]
    exact (hcont.continuousAt hN).congr heq

  have hB : ∀ g, ‖φ g‖ ≤ ‖s‖ * (supE X la P).toReal := by
    intro g
    have hw : (X (dict g).1).pnorm (la (dict g).1) (P (dict g).1) (dict g).2 = ‖P (dict g).1 (dict g).2‖ := by
      unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
      simp [hunit g]
    have hle : ENNReal.ofReal ((X (dict g).1).pnorm (la (dict g).1) (P (dict g).1) (dict g).2) ≤ supE X la P := by
      unfold Formalism.L2.Pj.supE
      exact le_iSup_of_le ⟨(dict g).1, ⟨(dict g).2, hdom g⟩⟩ le_rfl
    have hP : ‖P (dict g).1 (dict g).2‖ ≤ (supE X la P).toReal := by
      rw [← hw]
      exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp hle
    rw [hφ, norm_mul, norm_mul, norm_mul, hc (dict g).1, hnorm g, one_mul, one_mul]
    exact mul_le_mul_of_nonneg_left hP (norm_nonneg s)
  refine ⟨hL, hR, hC, ⟨_, hB⟩, ?_⟩

  have hinv : ∀ g, onQ V φ (autMk V g) = φ g := by
    intro g
    show φ (Quotient.out (autMk V g)) = φ g
    have h1 := Quotient.exact (Quotient.out_eq (autMk V g))
    have h2 : g * (Quotient.out (autMk V g))⁻¹ ∈ GQ V := QuotientGroup.rightRel_apply.mp h1
    have h3 := hL _ h2 (Quotient.out (autMk V g))
    rw [inv_mul_cancel_right] at h3
    exact h3.symm
  have hmeas : Measurable (onQ V φ) := by
    have : BorelSpace (GA D V) := ⟨rfl⟩
    rw [measurable_from_quotient]
    have : onQ V φ ∘ Quotient.mk'' = φ := funext hinv
    rw [this]
    exact hC.measurable
  refine MemLp.of_bound hmeas.aestronglyMeasurable (‖s‖ * (supE X la P).toReal)
    (Filter.Eventually.of_forall fun q => ?_)
  show ‖φ (Quotient.out q)‖ ≤ _
  exact hB _

set_option maxHeartbeats 1000000 in

theorem phiJ_automorphic : ∀ (D : D7) (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hD : Dom a n), ∀ f ∈ T.cuspA j a n, (∀ γ ∈ GQ (T.V j σ), ∀ g, T.phiJ j σ a f (γ * g) = T.phiJ j σ a f g) ∧ (∀ k ∈ T.Kf j σ, ∀ g, T.phiJ j σ a f (g * k) = T.mu j σ k * T.phiJ j σ a f g) ∧ Continuous (T.phiJ j σ a f) ∧ (∃ C : ℝ, ∀ g, ‖T.phiJ j σ a f g‖ ≤ C) ∧ MemLp (onQ (T.V j σ) (T.phiJ j σ a f)) 2 (muQ1 (T.V j σ)) := by
  intro D T h j hj σ hσ a n hD f hf
  obtain ⟨th, hr, hth, hd⟩ := h.dictU j hj σ hσ
  have hU := h.unf j hj σ hσ
  have hLK := h.levelK j hj σ hσ
  have hK : T.Kf j σ ≤ GfC (T.V j σ) := fun k hk => ((hLK k).mp hk).1
  have hpos : 0 < D.host.g 0 * D.host.g 1 := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hN : ∀ g₀ : GA D (T.V j σ), {g : GA D (T.V j σ) | ∃ k ∈ T.Kf j σ, ∃ h ∈ GinfC (T.V j σ), g = g₀ * k * h} ∈ 𝓝 g₀ :=
    fun g₀ => LevelOpen.level_mem_nhds D (T.V j σ) (D.host.g 0 * D.host.g 1) (T.Kf j σ) hpos hLK g₀
  have hloc := GlobalTheory.DictLocTest.locClause_of_unif_places hd hK hN (fun k τ => ⟨τ.1, hth k τ⟩)
  have hmem : rdU (T.U j σ) f ∈ holSub (T.U j σ).X (laU (T.U j σ) a n) := by
    have h1 := (Submodule.mem_inf.mp hf).2
    rw [Submodule.mem_iInf] at h1
    have h2 := h1 σ
    rw [Submodule.mem_iInf] at h2
    exact h2 hσ

  have hΓ : ∀ P ∈ holSub (T.U j σ).X (laU (T.U j σ) a n), ∀ k, ∀ γ ∈ ((T.U j σ).X k).Γ,
      ∀ x ∈ ((T.U j σ).X k).dom, P k (lact γ x) = P k x := by
    intro P hP
    unfold Formalism.L2.Pj.holSub at hP
    induction hP using Submodule.span_induction with
    | mem Q hQ =>
      intro k γ hγ x hx
      have hQ' : IsHolCusp (T.U j σ).X (laU (T.U j σ) a n) Q := hQ
      unfold Formalism.L2.Pj.IsHolCusp at hQ'
      obtain ⟨⟨⟨-, -, hsec⟩, -⟩, -⟩ := hQ' k
      rw [hsec γ hγ x hx, h.chiTriv j hj σ hσ a n hD k γ hγ, one_mul]
    | zero => intro k γ hγ x hx; rfl
    | add Q R _ _ hQ hR =>
      intro k γ hγ x hx
      simp only [Pi.add_apply, hQ k γ hγ x hx, hR k γ hγ x hx]
    | smul t Q _ hQ =>
      intro k γ hγ x hx
      simp only [Pi.smul_apply, hQ k γ hγ x hx]
  refine adel_muPin_automorphic (hd := hd) (hloc := hloc) (hmu := h.muUnit j hj σ hσ)
    (hmc := h.muCont j hj σ hσ) (hc := h.cUnit j hj σ hσ) (s := (lieFac (T.Q.Dw j) (xiR D) a : ℂ))
    (la := laU (T.U j σ) a n) (P := rdU (T.U j σ) f) (hPc := fun k => rdC_continuousOn hU hD ⟨f, hf⟩ k)
    (hΓ := hΓ _ hmem) (hfin := supE_cusp_ne_top hσ hf) (φ := T.phiJ j σ a f) (hφ := ?_)
  intro g
  simp only [Formalism.L2.Pj.CoreJ.phiJ, Pi.smul_apply, smul_eq_mul, Formalism.L2.Pj.adel_muPin]

end GlobalTheory.AdelicCusp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledGaussianKernelDiagonalTranslationInvarianStatement
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledGaussianKernel_diagonal_translation_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, ∀ a b w : WR X n, cexp (π * I * (EFR X w (a - b) : ℝ)) * (gaussR X bas idx x₁ (zR X idx x₁ (w + a)) * conj (gaussR X bas idx x₂ (zR X idx x₂ (w + b))) * kZero X idx x₁ x₂ (zR X idx x₁ (w + a)) (fun k i => conj (zR X idx x₂ (w + b) k i))) = gaussR X bas idx x₁ (zR X idx x₁ a) * conj (gaussR X bas idx x₂ (zR X idx x₂ b)) * kZero X idx x₁ x₂ (zR X idx x₁ a) (fun k i => conj (zR X idx x₂ b k i)) := by
  first | exact @GlobalTheory.Ker.Diag.kernel_diag | exact GlobalTheory.Ker.Diag.kernel_diag | (intros; apply GlobalTheory.Ker.Diag.kernel_diag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabCompact

theorem exists_compact_of_entries {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0)
    (C : Set (R ⊗[F] E)) (hC : IsCompact C) :
    ∃ K : Set (HA R σ J), IsCompact K ∧ ∀ h : HA R σ J, (∀ i j, (HA.mat R σ J h).1 i j ∈ C) → h ∈ K := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) R
  haveI : T2Space (R ⊗[F] E) := e.isEmbedding.t2Space
  have hc : IsClosed (HR R σ J : Set (GL (Fin M) (R ⊗[F] E))) := by
    have hv : Continuous fun g : GL (Fin M) (R ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
      Units.continuous_val
    exact isClosed_eq (((hv.matrix_map (GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ)).matrix_transpose.matrix_mul
      continuous_const).matrix_mul hv) continuous_const
  let S : Set (Matrix (Fin M) (Fin M) (R ⊗[F] E)) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC
  let f : Matrix (Fin M) (Fin M) (R ⊗[F] E) → (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    fun A => MulOpposite.op (JR (F := F) R J⁻¹ * (Formalism.UG.cT (sigR R σ) A * JR (F := F) R J))
  have hf : Continuous f := MulOpposite.continuous_op.comp (continuous_const.matrix_mul
    ((continuous_id.matrix_map (GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ)).matrix_transpose.matrix_mul
      continuous_const))
  have hemb := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin M) (Fin M) (R ⊗[F] E))).comp
    hc.isClosedEmbedding_subtypeVal
  refine ⟨_, hemb.isCompact_preimage (hS.prod (hS.image hf)), fun h hh => ?_⟩
  have hm : (HA.mat R σ J h).1 ∈ S := fun i _ j _ => hh i j
  refine ⟨hm, (HA.mat R σ J h).1, hm, ?_⟩
  have hu : Formalism.UG.cT (sigR R σ) (HA.mat R σ J h).1 * JR (F := F) R J * (HA.mat R σ J h).1 = JR (F := F) R J := h.2
  have h1 : JR (F := F) R J⁻¹ * JR (F := F) R J = 1 := by
    unfold JR
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hJ), Matrix.map_one _ (map_zero _) (map_one _)]
  change MulOpposite.op _ = MulOpposite.op ((HA.mat R σ J h)⁻¹).1
  congr 1
  refine (Units.inv_eq_of_mul_eq_one_left ?_).symm
  rw [Matrix.mul_assoc, hu, h1]

theorem exists_compact_latHat (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {M : ℕ} (L : Submodule (𝓞 E) (Fin M → E)) (hL : L.FG) :
    ∃ C : Set (Fin M → Af F ⊗[F] E), IsCompact C ∧ ∀ y ∈ latHat F E (L : Set (Fin M → E)), y ∈ C := by
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Af F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Af F) _
  haveI : ContinuousSMul (Af F) (Af F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  have hZ : (L.restrictScalars ℤ).FG := hL.restrictScalars
  obtain ⟨m, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hZ
  let g : (Fin m → Af F) → Fin M → Af F ⊗[F] E := fun c i => ∑ k, c k ⊗ₜ[F] x k i
  have hg : Continuous g := by
    refine continuous_pi fun i => continuous_finset_sum _ fun k _ => ?_
    have : (fun c : Fin m → Af F => c k ⊗ₜ[F] x k i) = fun c => c k • ((1 : Af F) ⊗ₜ[F] x k i) := by
      funext c
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    have hk : Continuous fun c : Fin m → Af F => c k := continuous_apply k
    have ho : Continuous fun _ : Fin m → Af F => (1 : Af F) ⊗ₜ[F] x k i := continuous_const
    exact hk.smul ho
  have hI : IsCompact (intAf F) := GlobalTheory.AdeleCocompact.isCompact_integral F
  refine ⟨g '' Set.pi Set.univ fun _ => intAf F, (isCompact_univ_pi fun _ => hI).image hg, fun y hy => ?_⟩
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, v, hv, rfl⟩ := hy
    have hv' : v ∈ Submodule.span ℤ (Set.range x) := by rw [hx]; exact hv
    obtain ⟨n, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hv'
    refine ⟨fun k => n k • a, fun k _ w => ?_, ?_⟩
    · rw [map_zsmul]
      exact zsmul_mem (ha w) _
    · funext i
      simp only [g, Finset.sum_apply, Pi.smul_apply, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
  | zero =>
    refine ⟨0, fun k _ w => ?_, ?_⟩
    · rw [Pi.zero_apply, map_zero]
      exact zero_mem _
    · funext i
      simp [g]
  | add y z _ _ hy hz =>
    obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨d, hd, rfl⟩ := hz
    refine ⟨c + d, fun k _ w => ?_, ?_⟩
    · rw [Pi.add_apply, map_add]
      exact add_mem (hc k trivial w) (hd k trivial w)
    · funext i
      simp only [g, Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
  | neg y _ hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    refine ⟨-c, fun k _ w => ?_, ?_⟩
    · rw [Pi.neg_apply, map_neg]
      exact neg_mem (hc k trivial w)
    · funext i
      simp only [g, Pi.neg_apply, TensorProduct.neg_tmul, Finset.sum_neg_distrib]

theorem exists_compact_entries (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {M : ℕ} (L : Submodule (𝓞 E) (Fin M → E)) (hL : L.FG)
    (hsp : Submodule.span E (L : Set (Fin M → E)) = ⊤) :
    ∃ C : Set (Af F ⊗[F] E), IsCompact C ∧ ∀ A : Matrix (Fin M) (Fin M) (Af F ⊗[F] E),
      (∀ y ∈ latHat F E (L : Set (Fin M → E)), A.mulVec y ∈ latHat F E (L : Set (Fin M → E))) →
      ∀ i j, A i j ∈ C := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  obtain ⟨C, hC, hLC⟩ := exists_compact_latHat F E L hL
  choose d hd hdL using fun j => GlobalTheory.AdLat.OpenLat.exists_denom L hsp (Pi.single j 1)
  refine ⟨⋃ p : Fin M × Fin M, (fun y : Fin M → Af F ⊗[F] E =>
      y p.1 * ((1 : Af F) ⊗ₜ[F] ((d p.2 : E)⁻¹))) '' C,
    isCompact_iUnion fun p => hC.image ((continuous_apply p.1).mul continuous_const), fun A hA i j => ?_⟩
  have h1 : (1 : Af F) ∈ intAf F := fun w => by rw [map_one]; exact one_mem _
  have hy : (fun k => (1 : Af F) ⊗ₜ[F] (d j • (Pi.single j 1 : Fin M → E)) k) ∈
      latHat F E (L : Set (Fin M → E)) := AddSubgroup.subset_closure ⟨1, h1, _, hdL j, rfl⟩
  refine Set.mem_iUnion.2 ⟨(i, j), _, hLC _ (hA _ hy), ?_⟩
  have hd0 : (d j : E) ≠ 0 := Nat.cast_ne_zero.2 (hd j).ne'
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp), mul_assoc,
    Algebra.TensorProduct.tmul_mul_tmul]
  simp only [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, mul_inv_cancel₀ hd0]
  rw [← Algebra.TensorProduct.one_def, mul_one]

theorem det_gram_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) :
    S.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have hy : S.frame.equivFun.symm v = 0 := by
    apply S.nondeg.2
    intro x
    have hi : ∀ i, S.hT (S.frame i) (S.frame.equivFun.symm v) = 0 := by
      intro i
      have := congrFun h0 i
      rw [Module.Basis.equivFun_symm_apply, map_sum]
      simpa [Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram, mul_comm] using this
    rw [← S.frame.sum_repr x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hi, smul_zero]
  exact S.frame.equivFun.symm.map_eq_zero_iff.1 hy

theorem exists_compact_adele (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (R : ℝ) (C : Set (Af D.host.F ⊗[D.host.F] D.host.E)) (hC : IsCompact C) :
    ∃ K : Set (AE D), IsCompact K ∧ ∀ z : AE D, finPart D z ∈ C → (∀ ρ, ‖θ ρ (infPart D z)‖ ≤ R) → z ∈ K := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) _
  obtain ⟨s, hs⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  let j : Af D.host.F ⊗[D.host.F] D.host.E → AE D := fun w => e.symm (0, w)
  have hj : Continuous j := hc.comp (continuous_const.prodMk continuous_id)
  have hj1 : ∀ w, infPart D (j w) = 0 := fun w =>
    (he (e.symm (0, w))).1.symm.trans (by rw [e.apply_symm_apply])
  have hj2 : ∀ w, finPart D (j w) = w := fun w =>
    (he (e.symm (0, w))).2.symm.trans (by rw [e.apply_symm_apply])
  have hB : IsCompact (Set.pi Set.univ fun _ : D.what₂.Tau => Metric.closedBall (0 : ℂ) R) :=
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine ⟨_, (hB.prod hC).image ((hs.cont.comp continuous_fst).add (hj.comp continuous_snd)), fun z hz hR => ?_⟩
  refine ⟨(fun ρ => θ ρ (infPart D z), finPart D z), ⟨fun ρ _ => mem_closedBall_zero_iff.2 (hR ρ), hz⟩, ?_⟩
  refine sub_eq_zero.1 (hs.ext _ ?_ fun τ => ?_)
  · change finPart D (s (fun ρ => θ ρ (infPart D z)) + j (finPart D z) - z) = 0
    rw [RingHom.map_sub, RingHom.map_add, hs.fin, hj2, zero_add, sub_self]
  · change θ τ (infPart D (s (fun ρ => θ ρ (infPart D z)) + j (finPart D z) - z)) = 0
    rw [RingHom.map_sub, RingHom.map_add, hj1, add_zero, RingHom.map_sub, hs.comp, sub_self]

theorem exists_compact_stab : ∀ (D : D7) (V : HSp D) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ R : ℝ, ∃ K : Set (GA D V), IsCompact K ∧ ∀ h : GA D V, (∀ y, y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ (finMat D.sp.cm.sig V.gram h).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V)) → (∀ ρ i j, ‖infMat D.sp.cm.sig V.gram (θ ρ) h i j‖ ≤ R) → h ∈ K := by
  intro D V θ hθ R
  let f := V.frame.equivFun.toLinearMap
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := V.L0.map (f.restrictScalars (𝓞 D.host.E))
  have hL : (L : Set (Fin V.rank → D.host.E)) = L0c D V := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ∑ i, V.frame.equivFun x i • V.frame i ∈ V.L0
      rwa [V.frame.sum_equivFun]
    · intro hv
      refine ⟨V.frame.equivFun.symm v, ?_, V.frame.equivFun.apply_symm_apply v⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact hv
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective v
    have hx : x ∈ Submodule.span D.host.E (V.L0 : Set V.V) := by
      rw [V.standardTuple_isLattice.span_eq_top]; trivial
    have := Submodule.mem_map_of_mem (f := f) hx
    rw [Submodule.map_span] at this
    exact this
  obtain ⟨C, hC, hCe⟩ := exists_compact_entries D.host.F D.host.E L (V.standardTuple_isLattice.fg.map _) hsp
  rw [hL] at hCe
  obtain ⟨C', hC', hCe'⟩ := exists_compact_adele D θ hθ R C hC
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨K, hK, hKe⟩ := exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram (det_gram_ne_zero V) C' hC'
  exact ⟨K, hK, fun h h1 h2 => hKe h fun i j =>
    hCe' _ (hCe _ (fun y hy => (h1 y).1 hy) i j) fun ρ => h2 ρ i j⟩

end GlobalTheory.StabCompact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteAdelicLatticeTransportLawsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicLatticeTransport_laws : ∀ (D : D7) (k : ℕ) (L : Lt D.host.E k), (L.FG ∧ Submodule.span D.host.E (L : Set (Fin k → D.host.E)) = ⊤) → (∀ v, toAf v ∈ hatV L ↔ v ∈ L) ∧ IsMov 1 L L ∧ (∀ ga : GL (Fin k) D.host.E, IsMov ((ga : Matrix (Fin k) (Fin k) D.host.E).map fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x) L (mapL ga L)) ∧ ∀ m m' : Matrix (Fin k) (Fin k) (AfE D), m * m' = 1 → (∃ L' : Lt D.host.E k, (L'.FG ∧ Submodule.span D.host.E (L' : Set (Fin k → D.host.E)) = ⊤) ∧ IsMov m L L') ∧ ∀ L' : Lt D.host.E k, L'.FG → IsMov m L L' → Submodule.span D.host.E (L' : Set (Fin k → D.host.E)) = ⊤ ∧ IsMov m' L' L ∧ (∀ L'' : Lt D.host.E k, L''.FG → IsMov m L L'' → L'' = L') ∧ (∀ m₂ (L'' : Lt D.host.E k), IsMov m₂ L' L'' → IsMov (m₂ * m) L L'') ∧ ∀ 𝔞 𝔟 : Ideal (𝓞 D.host.E), 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → IsMov m (𝔞 • L) (𝔞 • L') ∧ IsMov m (idq 𝔞 𝔟 L) (idq 𝔞 𝔟 L') ∧ (idq 𝔞 𝔟 L).FG ∧ Submodule.span D.host.E (idq 𝔞 𝔟 L : Set (Fin k → D.host.E)) = ⊤ := by
  first | exact @GlobalTheory.Ker.isMov_laws | exact GlobalTheory.Ker.isMov_laws | (intros; apply GlobalTheory.Ker.isMov_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GaussRMulFactor
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker.RealHeis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)

theorem hx_add_left (z z' w : Fin g → ℂ) :
    hx X bas idx x (z + z') w = hx X bas idx x z w + hx X bas idx x z' w := by
  simp only [GlobalTheory.Dict.hx, mulVec_add, add_dotProduct]

theorem hx_add_right (z w w' : Fin g → ℂ) :
    hx X bas idx x z (w + w') = hx X bas idx x z w + hx X bas idx x z w' := by
  simp only [GlobalTheory.Dict.hx, mulVec_add, star_add, dotProduct_add]

theorem hx_smul_left (c : ℂ) (z w : Fin g → ℂ) :
    hx X bas idx x (c • z) w = c * hx X bas idx x z w := by
  simp only [GlobalTheory.Dict.hx, mulVec_smul, smul_dotProduct, smul_eq_mul]

theorem contDiff_gaussR : ContDiff ℝ (⊤ : ℕ∞) (gaussR X bas idx x : (Fin n → Fin g → ℂ) → ℂ) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => star z) := Complex.conjCLE.contDiff
  have h1 : ∀ (k : Fin n) (i : Fin g), ContDiff ℝ (⊤ : ℕ∞)
      fun z : Fin n → Fin g → ℂ => (hMat X bas idx x *ᵥ z k) i := by
    intro k i
    simp only [mulVec, dotProduct]
    fun_prop
  have h2 : ∀ k : Fin n, ContDiff ℝ (⊤ : ℕ∞)
      fun z : Fin n → Fin g → ℂ => hx X bas idx x (z k) (z k) := by
    intro k
    change ContDiff ℝ _ fun z : Fin n → Fin g → ℂ => ∑ i, (hMat X bas idx x *ᵥ z k) i *
      ∑ j, imInv X bas idx x i j * star ((hMat X bas idx x *ᵥ z k) j)
    exact ContDiff.sum fun i _ => (h1 k i).mul
      (ContDiff.sum fun j _ => contDiff_const.mul (hc.comp (h1 k j)))
  exact (contDiff_const.mul (ContDiff.sum fun k _ => h2 k)).neg.cexp

theorem gaussR_mul_factor (hsym : ∀ z w, hx X bas idx x w z = conj (hx X bas idx x z w))
    (z a : Fin n → Fin g → ℂ) :
    gaussR X bas idx x z * cexp (-(π * ∑ k, hx X bas idx x (z k + (1 / 2 : ℂ) • a k) (a k))) =
      cexp (-(π * I * ((∑ k, hx X bas idx x (z k) (a k)).im : ℝ))) * gaussR X bas idx x (z + a) := by
  have h1 : ∑ k, hx X bas idx x (a k) (z k) = conj (∑ k, hx X bas idx x (z k) (a k)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hsym _ _
  simp only [gaussR, ← Complex.exp_add, Pi.add_apply, hx_add_left, hx_add_right, hx_smul_left,
    Finset.sum_add_distrib, ← Finset.mul_sum, h1]
  congr 1
  generalize ∑ k, hx X bas idx x (z k) (a k) = S
  have h2 := Complex.sub_conj S
  push_cast at h2
  linear_combination (-(π : ℂ) / 2) * h2

end GlobalTheory.Ker.RealHeis

namespace GlobalTheory.Ker

theorem thR_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, ∀ φ : TF n g, IsSB φ → ContDiff ℝ (⊤ : ℕ∞) (thR X bas idx φ x : WR X n → ℂ) ∧ (∀ (y : Matrix (Fin n) (Fin r) E) (v : WR X n), thR X bas idx (heisG X bas y φ) x v = cexp (-(π * I * (EFR X v (embR X y) : ℝ))) * thR X bas idx φ x (v + embR X y)) ∧ (∀ γ : GL (Fin r) E, IsUn X γ → ∀ v : WR X n, thR X bas idx (wG X bas idx γ φ) (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) = thR X bas idx φ x v) ∧ (∀ ψ, IsSB ψ → (thR X bas idx φ x = (thR X bas idx ψ x : WR X n → ℂ) → φ = ψ) ∧ thR X bas idx (φ + ψ) x = (thR X bas idx φ x + thR X bas idx ψ x : WR X n → ℂ)) ∧ ∀ a : ℂ, thR X bas idx (a • φ) x = (a • thR X bas idx φ x : WR X n → ℂ) := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn x hxd φ hφ
  obtain ⟨⟨L, hL⟩, him, -, -, hinv⟩ := GlobalTheory.T.realPeriodMap_homeomorph_riemannForm_density E r X g q0 hr bas idx n hs hn x hxd
  obtain ⟨hsym, -, -, -, -, -, -, hga⟩ := GlobalTheory.Dict.hx_laws E r X g bas idx n hs hn x hxd
  have hLf : zR X idx x = (L : WR X n → Fin n → Fin g → ℂ) := funext fun v => (hL v).symm
  refine ⟨?_, fun y v => ?_, fun γ hγ v => ?_, fun ψ hψ => ⟨fun h => ?_, ?_⟩, fun a => ?_⟩
  · have h1 : ContDiff ℝ (⊤ : ℕ∞) (thA X bas idx φ x) :=
      (AnalyticOnNhd.contDiff (𝕜 := ℂ) (SCV.analyticOnNhd_of_differentiable
        (ThetaHol.differentiable_thA idx hs hφ hxd) _)).restrict_scalars ℝ
    have h2 := ((RealHeis.contDiff_gaussR X bas idx x).mul h1).comp L.contDiff
    rw [← hLf] at h2
    exact h2
  · have h1 := ((heisG_laws E r X g bas idx n hs hn).2.2.2 y φ hφ).2.2.2.2 x hxd (zR X idx x v)
    have h2 : zR X idx x (v + embR X y) = zR X idx x v + zR X idx x (embR X y) := by
      rw [hLf, map_add]
    have h3 := RealHeis.gaussR_mul_factor X bas idx x hsym (zR X idx x v) (zR X idx x (embR X y))
    rw [him] at h3
    rw [thR, thR, h1, h2, ← _root_.mul_assoc, ← _root_.mul_assoc, ← h3]
    rfl
  · rw [thR, thR, hinv γ hγ v, (wG_laws E r X g bas idx n hs hn γ hγ φ hφ).2.1 x hxd]
    simp only [gaussR, (hga γ hγ).2.2.2]
  · have hone : IsUn X (1 : GL (Fin r) E) := fun u w => by simp
    refine ((wG_laws E r X g bas idx n hs hn 1 hone φ hφ).2.2.1 ψ hψ).2.2 x hxd ?_
    funext z
    obtain ⟨v, rfl⟩ := L.surjective z
    have h1 := congrFun h v
    rw [thR, thR, ← hL] at h1
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) h1
  · funext v
    simp only [thR, UnAct.thA_add idx hs hxd hφ hψ, Pi.add_apply, mul_add]
  · funext v
    simp only [thR, UnAct.thA_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]

end GlobalTheory.Ker
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealPointsClassicalModelRealVectorSpaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPoints_classicalModel_realVectorSpace : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∃ R : WR C.X S.rank →+ WO S T, Continuous R ∧ Continuous C.realPt ∧ (∀ w w', C.realPt (w + w') = C.realPt w + C.realPt w') ∧ (∀ v, IsRealPt (R v) ∧ C.realPt (R v) = v) ∧ (∀ w, IsRealPt w → R (C.realPt w) = w) ∧ (∀ w, IsFinPt (w - R (C.realPt w))) ∧ (∀ u, IsFinPt u → C.realPt u = 0) ∧ (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ), lineAt C.θ τ z t = R (t • (Pi.single (C.m.e τ) (fun k a => conj (z a k)) : WR C.X S.rank))) ∧ ∀ (h : GA D S) (g : GA D T) (w : WO S T), (IsRealPt w → IsRealPt (actO S T h g w)) ∧ (IsFinPt w → IsFinPt (actO S T h g w)) ∧ ∀ τ, compAt C.θ τ (actO S T h g w) = compAt C.θ τ (mt T g) * compAt C.θ τ w * compAt C.θ τ (mt S h⁻¹) := by
  first | exact @GlobalTheory.KerReal.real_points | exact GlobalTheory.KerReal.real_points | (intros; apply GlobalTheory.KerReal.real_points <;> assumption)
end

