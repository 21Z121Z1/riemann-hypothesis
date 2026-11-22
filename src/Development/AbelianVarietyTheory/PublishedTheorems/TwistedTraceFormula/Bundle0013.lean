import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapInfFinEquivEqProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompOfIsTraceClass
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SiegelWeilAnisotropicUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MulMemRiemannRochSpaceAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0052

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.Cusp GlobalTheory.AutMult GlobalTheory.DiscreteSum GlobalTheory.Orb GlobalTheory.AdelicU GlobalTheory.SplitWeil
open scoped Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

namespace Published

def CuspTraceClass : Prop :=
  ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    ∀ f ∈ CcGA V, IsTraceClass (RcuspOp V μ f)

def CuspDiscreteDecomposition : Prop :=
  ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], IsDiscreteSum (Rcusp V μ)

end Published

namespace CuspSpectrum

section General

theorem isDiscreteSum_of_repOp {G K : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {ρ : G →* (K →L[ℂ] K)} (hρ : IsUnitaryRep ρ)
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (h : ∀ v ≠ 0, ∃ f : G → ℂ, Continuous f ∧ HasCompactSupport f ∧
      IsCompactOperator (repOp ρ μ f) ∧ repOp ρ μ f v ≠ 0) : IsDiscreteSum ρ :=
  EnoughCompact.isDiscreteSum hρ fun v hv =>
    let ⟨_, h1, h2, h3, h4⟩ := h v hv
    ⟨_, h3, fun S hS x => (DFunLike.congr_fun (hρ.comp_repOp hρ h1 h2 S hS.2) x).symm, h4⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem exists_isCompact_isOpen {N : Set (GFin σ J)} (hN : N ∈ 𝓝 1) :
    ∃ U : Set (GFin σ J), IsOpen U ∧ IsCompact U ∧ 1 ∈ U ∧ U ⊆ N := by
  have := GlobalTheory.Doubling.totallyDisconnectedSpace_GFin σ J
  obtain ⟨K, hK, hKN, hc⟩ := local_compact_nhds hN
  obtain ⟨U, hU, h1, hUK⟩ := loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 hK
  exact ⟨U, hU.2, hc.of_isClosed_subset hU.1 hUK, h1, hUK.trans hKN⟩

theorem exists_bump_ccAd (h : IsCMExt F E σ) {N : Set (GAd σ J)} (hN : N ∈ 𝓝 1) :
    ∃ φ : GAd σ J → ℝ, (fun g => (φ g : ℂ)) ∈ CcAd σ J ∧ 0 ≤ φ ∧ φ 1 = 1 ∧ Function.support φ ⊆ N := by
  classical
  have h1 : (infFinEquiv σ J).symm ⁻¹' N ∈ 𝓝 ((1, 1) : GInf σ J × GFin σ J) :=
    (map_continuous (infFinEquiv σ J).symm).continuousAt.preimage_mem_nhds
      ((map_one (infFinEquiv σ J).symm).symm ▸ hN :)
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1 h1
  obtain ⟨a, ha, a1, a0, hs⟩ := exists_bump (SmoothFactor.isEmbedding_infMat J h).isInducing hA
  obtain ⟨U, ho, hc, hU, hUB⟩ := exists_isCompact_isOpen hB
  refine ⟨fun g => a (projInf σ J g) * U.indicator 1 (projFin σ J g), ?_,
    fun g => mul_nonneg (a0 _).1 (indicator_nonneg (fun _ _ => zero_le_one) _), by simp [a1, hU], fun g hg => ?_⟩
  · convert infFin_mem_ccAd ((SmoothFactor.ccInf_eq σ J).ge ha) (indicator_mem_SB ho hc) using 1
    funext g
    by_cases hg : projFin σ J g ∈ U <;> simp [infFin, hg]
  · rw [← (infFinEquiv σ J).symm_apply_apply g]
    exact hAB ⟨hs (subset_tsupport _ (left_ne_zero_of_mul hg)),
      hUB (mem_of_indicator_ne_zero (right_ne_zero_of_mul hg))⟩

theorem mem_span_conv (hDM : Published.DixmierMalliavinFactorisation) (h : IsCMExt F E σ) (μ : Measure (GAd σ J))
    [μ.IsHaarMeasure] : CcAd σ J ≤ Submodule.span ℂ {f | ∃ g ∈ CcAd σ J, ∃ g' ∈ CcAd σ J, f = conv μ g g'} := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  obtain ⟨μa, μf, _, _, e⟩ := exists_map_infFinEquiv_eq_prod μ
  obtain ⟨m, g, g', hg, rfl⟩ := SmoothFactor.exists_sum_conv_ccInf J hDM h μa univ_mem ha
  obtain ⟨K, hK, hKb⟩ := exists_biinvariant hb
  obtain ⟨U, ho, hc, hU, hUK⟩ := exists_isCompact_isOpen (hK.mem_nhds K.one_mem)
  have h0 : (μf.real U : ℂ) ≠ 0 := by
    exact_mod_cast ENNReal.toReal_ne_zero.2 ⟨(ho.measure_pos _ ⟨1, hU⟩).ne', hc.measure_ne_top⟩
  have h1 : conv μf (U.indicator 1) b = (μf.real U : ℂ) • b := by
    funext y
    have : ∀ x, U.indicator (1 : GFin σ J → ℂ) x * b (x⁻¹ * y) = U.indicator (fun _ => b y) x := fun x => by
      by_cases hx : x ∈ U
      · simp [hx, (hKb _ (K.inv_mem (hUK hx)) y).1]
      · simp [hx]
    rw [conv, integral_congr_ae (.of_forall this), integral_indicator_const _ ho.measurableSet]
    simp
  have h2 : infFin σ J (∑ i, conv μa (g i) (g' i)) b =
      ∑ i, (μf.real U : ℂ)⁻¹ • conv μ (infFin σ J (g i) (U.indicator 1)) (infFin σ J (g' i) b) := by
    funext x
    simp [conv_infFin e, h1, infFin, Finset.sum_mul, mul_left_comm _ (μf.real U : ℂ), h0]
  rw [h2]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨_, infFin_mem_ccAd (hg i).1 (indicator_mem_SB ho hc), _, infFin_mem_ccAd (hg i).2.1 hb, rfl⟩)

end General

variable {D : D7} {V : HSp D} {μ : Measure (GA D V)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem isRepOp_RcuspOp {f : GA D V → ℂ} (hf : f ∈ CcGA V) : IsRepOp (Rcusp V μ) μ f (RcuspOp V μ f) :=
  (isUnitaryRep_Rcusp V μ).isRepOp (continuous_of_mem_ccAd hf).1 (continuous_of_mem_ccAd hf).2

theorem exists_RcuspOp_ne_zero {v : L2cusp V μ} (hv : v ≠ 0) : ∃ f ∈ CcGA V, RcuspOp V μ f v ≠ 0 := by
  obtain ⟨N, hN, h⟩ := exists_nhds_repOp_ne_zero μ (isUnitaryRep_Rcusp V μ) hv
  obtain ⟨φ, hφ, h0, h1, hs⟩ := exists_bump_ccAd (isCMExt_host D) hN
  have hc := continuous_of_mem_ccAd hφ
  exact ⟨_, hφ, h φ (Complex.continuous_re.comp hc.1) (hc.2.comp_left (g := Complex.re) rfl) h0
    (h1 ▸ one_ne_zero) hs⟩

theorem isDiscreteSum_of_compact (h : ∀ f ∈ CcGA V, IsCompactOperator (RcuspOp V μ f)) : IsDiscreteSum (Rcusp V μ) := by
  refine isDiscreteSum_of_repOp (isUnitaryRep_Rcusp V μ) μ fun v hv => ?_
  obtain ⟨f, hf, h0⟩ := exists_RcuspOp_ne_zero hv
  exact ⟨f, (continuous_of_mem_ccAd hf).1, (continuous_of_mem_ccAd hf).2, h f hf, h0⟩

theorem isTraceClass_of_isHilbertSchmidt (hDM : Published.DixmierMalliavinFactorisation)
    (h : ∀ f ∈ CcGA V, IsHilbertSchmidt (RcuspOp V μ f)) {f : GA D V → ℂ} (hf : f ∈ CcGA V) :
    IsTraceClass (RcuspOp V μ f) := by
  have hu := isUnitaryRep_Rcusp V μ
  suffices f ∈ CcGA V ∧ IsTraceClass (RcuspOp V μ f) from this.2
  refine Submodule.span_induction (p := fun f _ => f ∈ CcGA V ∧ IsTraceClass (RcuspOp V μ f)) ?_ ?_ ?_ ?_
    (mem_span_conv hDM (isCMExt_host D) μ hf)
  · rintro _ ⟨g, hg, g', hg', rfl⟩
    have c := continuous_of_mem_ccAd hg
    have c' := continuous_of_mem_ccAd hg'
    refine ⟨conv_mem_ccAd μ hg hg', ?_⟩
    rw [show RcuspOp V μ (conv μ g g') = _ from (hu.repOp_convolution (μ := μ) c.1 c.2 c'.1 c'.2).repOp_eq]
    exact (h g hg).isTraceClass_comp (h g' hg')
  · refine ⟨zero_mem _, ?_⟩
    rw [RcuspOp, IsRepOp.repOp_eq (T := 0) fun v => by simp]
    exact isTraceClass_zero
  · rintro g g' - - ⟨hg, t⟩ ⟨hg', t'⟩
    have c := continuous_of_mem_ccAd hg
    have c' := continuous_of_mem_ccAd hg'
    exact ⟨add_mem hg hg', by rw [RcuspOp, hu.repOp_add c.1 c.2 c'.1 c'.2]; exact t.add t'⟩
  · rintro a g - ⟨hg, t⟩
    have c := continuous_of_mem_ccAd hg
    exact ⟨Submodule.smul_mem _ a hg, by rw [RcuspOp, hu.repOp_smul c.1 c.2 a]; exact t.smul a⟩

theorem L2cusp_le_L2disc (h : IsDiscreteSum (Rcusp V μ)) : L2cusp V μ ≤ L2discG V μ := fun F hF => by
  have hW := isSubrep_L2cusp V μ
  refine (h.disc_eq_top.ge.trans (disc_le (U := (L2discG V μ).comap (L2cusp V μ).subtype)
    ((isSubrep_disc (π := RG V μ)).1.preimage continuous_subtype_val) fun X hX => ?_) : ⊤ ≤ _)
    (Submodule.mem_top (x := ⟨F, hF⟩))
  refine Submodule.map_le_iff_le_comap.1 (IsIrredSubrep.le_disc ⟨hW.isSubrep_rep_iff.1 hX.1,
    fun e => hX.2.1 (Submodule.map_injective_of_injective (Submodule.injective_subtype _) (e.trans (Submodule.map_bot _).symm)), fun U hU hs => ?_⟩)
  have e : (U.comap (L2cusp V μ).subtype).map (L2cusp V μ).subtype = U :=
    Submodule.map_comap_eq_self (hU.trans (LinearMap.map_le_range))
  rcases hX.2.2 (U.comap (L2cusp V μ).subtype) ((Submodule.comap_mono hU).trans
    (Submodule.comap_map_eq_of_injective (Submodule.injective_subtype _) X).le)
    (hW.isSubrep_rep_iff.2 (e.symm ▸ hs)) with h0 | h0
  · exact .inl (by rw [← e, h0, Submodule.map_bot])
  · exact .inr (by rw [← e, h0])

theorem multIn_L2cusp_lt (h : IsDiscreteSum (Rcusp V μ)) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {π : GA D V →* (H →L[ℂ] H)} (hπ : IsIrrUnitary π) : multIn π (RG V μ) (L2cusp V μ) < Cardinal.aleph0 :=
  multIn_rep (π := π) (isSubrep_L2cusp V μ) ▸ h.2 ⟨H, π, hπ⟩

theorem traceIsDiagonal (hP : Published.CuspTraceClass) {f : GA D V → ℂ} (hf : f ∈ CcGA V)
    (h : IndefiniteRowSideFullHecke.TraceKernelDecomposition.MapsIntoCusp V μ (starFn f)) :
    IndefiniteRowSideFullHecke.TraceKernelDecomposition.TraceIsDiagonal (ν := autMeasure V μ) (RopG V μ f) (kernelQ (GQ V) f) :=
  have c := continuous_of_mem_ccAd hf
  TraceDiagonal.traceIsDiagonal_Rop c.1 c.2 (by
    change IsTraceClass (RopG V μ f)
    rw [TraceDiagonal.RopG_eq_comp c.1 c.2 h]
    exact (hP D V μ f hf).comp_comp _ _)

end CuspSpectrum

theorem Published.cuspDiscreteDecomposition_of_traceClass (h : Published.CuspTraceClass) : Published.CuspDiscreteDecomposition :=
  fun D V μ _ _ => CuspSpectrum.isDiscreteSum_of_compact fun f hf =>
    isCompactOperator_of_isHilbertSchmidt (h D V μ f hf).isHilbertSchmidt

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IntegrableOfIsAniso
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero GlobalTheory.ThetaMean

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaMean.Model

variable {D : D7}

theorem isAniso_posSpace (m : ℕ) : IsAniso (D := D) (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral m) :=
  GlobalTheory.BesselConvDefinite.isAniso_of_isDefinite _ (Examples₂.posSpace_sigOK _ _) fun _ => .inl rfl

theorem zero_vec (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (K : Subgroup (GA D S)) : IsThetaFunO ψ S T 0 ∧ IsKFinVec ω K 0 := by
  refine ⟨⟨fun _ _ => by simp, ⟨⊤, isOpen_univ, fun u _ _ => funext fun w => by simp [heisO]⟩, continuous_const,
    fun _ _ _ _ _ => contDiff_const⟩, ?_⟩
  have : Submodule.span ℂ {f : WO S T → ℂ | ∃ k ∈ K, f = ω (k, 1) 0} = ⊥ :=
    Submodule.span_eq_bot.2 (by rintro _ ⟨k, -, rfl⟩; exact map_zero _)
  rw [IsKFinVec, this]
  infer_instance

theorem hypotheses_inhabited (H : GlobalTheory.Published.WeilRepresentationUnitaryPair) (D : D7) (n m : ℕ) :
    ∃ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle)
      (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (a : GL (Fin A.rank) (AE D))
      (μ : Measure (WO A B)) (𝓨 : Set (WO A B)) (ν : Measure (GA D B)),
      A.rank = n ∧ B.rank = m ∧ IsAniso B ∧ IsWeilDatumO ψ (dblSp A) B 1 χB ω ∧ IsMaj A a ∧
        IsCovolOne (ratL B A) μ 𝓨 ∧ ν.IsHaarMeasure := by
  obtain ⟨ψ, hψ⟩ := GlobalTheory.StdAdelicChar.exists_isStdChar D
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  let A : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral n
  let B : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral m
  have h1 : IsHeckeChar D (η ^ m) := ⟨by
    have : ((η ^ m : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => η x ^ m := by funext x; simp
    rw [this]; exact hη.1.1.pow m, fun x => by rw [MonoidHom.pow_apply, hη.1.2 x, one_pow]⟩
  have hr := hη.2.2.1
  have h2 : ResEta D (η ^ m) B.rank := ⟨hr.1, fun e he a => by rw [MonoidHom.pow_apply, hr.2 e he a, pow_one]; rfl⟩
  have h3 : ResEta D 1 (dblSp A).rank := ⟨hr.1, fun e he a => by
    have h4 := he.2.2.1 (idF D a)
    have h5 : Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) (idF D a) = a ^ 2 := Units.ext (by
      change Algebra.norm (AF D.host.F) (algebraMap (AF D.host.F) (AE D) a.1) = _
      have := t2Space_adeleRing' (F := D.host.F)
      have : Nontrivial (AF D.host.F) :=
        (NumberField.AdeleRing.algebraMap_injective (NumberField.RingOfIntegers D.host.F) D.host.F).nontrivial
      rw [Algebra.norm_algebraMap, Module.finrank_baseChange, D.sp.cm.deg2, Units.val_pow_eq_pow_val])
    rw [h5, map_pow] at h4
    change (1 : Circle) = e a ^ (n + n)
    rw [← two_mul, pow_mul, h4, one_pow]⟩
  obtain ⟨ω, hω⟩ := H D ψ (dblSp A) B 1 (η ^ m) hψ ⟨continuous_const, fun _ => rfl⟩ h1 h3 h2
  obtain ⟨a, ha⟩ := exists_isMaj A
  obtain ⟨μ, 𝓨, hμ⟩ := exists_isCovolOne D B.rank A.rank
  exact ⟨ψ, A, B, _, ω, a, μ, 𝓨, Measure.haar, rfl, rfl, isAniso_posSpace m, hω, ha, hμ, inferInstance⟩

theorem integrable_of_isAniso {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χ χ' : (AE D)ˣ →* Circle}
    {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hω : IsWeilDatumO ψ S T χ χ' ω) (hT : IsAniso T)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (ν : Measure (GA D T)) [ν.IsHaarMeasure] (g : GA D S) :
    Integrable (AutomorphicL2Unitary.descend (GQ T) fun h => thetaKO ω g h f) (autMeasure T ν) :=
  integrable_theta hω hf (GlobalTheory.Mem.AnisoQuotient.exists_compact D T hT) g

theorem average_const_aut (T : HSp D) (ν : Measure (GA D T)) [ν.IsHaarMeasure] (c : ℂ) :
    ⨍ _, c ∂autMeasure T ν = c := average_const _ c

theorem conclusion_zero (A B : HSp D) (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ))
    (a : GL (Fin A.rank) (AE D)) (μ : Measure (WO A B)) (𝓨 : Set (WO A B)) (ν : Measure (GA D B)) :
    Eis.EisValueAt A (flat A a (swSec A B ω μ 𝓨 0) (sZero A B)) (sZero A B)
      ((if A.rank < B.rank then 1 else 2 : ℂ) • thetaMean ω ν 0) := by
  have h1 : flat A a (swSec A B ω μ 𝓨 0) (sZero A B) = fun _ _ => 0 := by
    funext s g
    refine (flatH_apply _ _ _ _).trans ?_
    simp [swSec, evZero]
  have h2 : thetaMean ω ν 0 = 0 := by
    funext g
    simp [thetaMean, thetaKO, AutomorphicL2Unitary.descend]
  rw [h1, h2, smul_zero]
  refine ⟨fun s _ => ⟨fun _ _ _ => rfl, fun g => ?_⟩, fun g => ?_⟩
  · simp [Eis.EisConv, Eis.CosetConv, Eis.term, summable_zero]
  · have : Eis.eisSer A (fun _ _ => (0 : ℂ)) g = fun _ => 0 := by
      funext s
      simp [Eis.eisSer, Eis.eis, Eis.cosetSum, Eis.term]
    rw [this]
    exact GlobalTheory.Cont.holValueAt_const 0 _

end GlobalTheory.ThetaMean.Model

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Chamber GlobalTheory.AdelicU GlobalTheory.TruncKer GlobalTheory.Orb
open scoped ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chamber

example {k : ℕ} (𝔞 : Submodule ℝ (A0 k)) (Q : Finset (SV k)) :
    (volume : Measure (aMQ 𝔞 Q)) = (stdOrthonormalBasis ℝ (aMQ 𝔞 Q)).toBasis.addHaar := rfl

def ExpFamilyIntegral : Prop :=
  ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ X, IsOrth 𝔞 X → IsGMFam 𝔞 (expFam X) ∧ ∀ Q ∈ parF 𝔞 ∅,
    (Integrable (fun H : aMQ 𝔞 Q => gamM 𝔞 Q X H) ∧
      ∀ l, cM 𝔞 Q (expFam X) l = eL l (X Q) * ∫ H : aMQ 𝔞 Q, eL l H * gamM 𝔞 Q X H) ∧
    (Integrable (fun H : aMQ (aP Q) ∅ => gamP Q ∅ (X Q) H) ∧
      ∀ l, cP Q ∅ (expFam X) l = ∫ H : aMQ (aP Q) ∅, eL l H * gamP Q ∅ (X Q) H)

def FamilySmooth : Prop :=
  ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ c, IsGMFam 𝔞 c → ∀ Q ∈ parF 𝔞 ∅,
    (ContDiff ℝ ∞ (cM 𝔞 Q c) ∧ Set.EqOn (cM 𝔞 Q c) (sumM 𝔞 Q c) (generic k)) ∧
    ∀ R ⊆ Q, ContDiff ℝ ∞ (cP Q R c) ∧ Set.EqOn (cP Q R c) (sumP Q R c) (generic k)

def FamilyProduct : Prop :=
  ∀ (k : ℕ) (𝔞 : Submodule ℝ (A0 k)), IsLevi 𝔞 → ∀ c d, IsGMFam 𝔞 c → IsGMFam 𝔞 d → ∀ R ∈ parF 𝔞 ∅, ∀ l,
    cM 𝔞 R (c * d) l = ∑ Q ∈ parF 𝔞 R, cM 𝔞 Q c l * cP Q R d l

end GlobalTheory.Chamber

namespace GlobalTheory.TruncKer

variable {D : D7} {V : HSp D} (Φ : WittFrame V) (K : Subgroup (GA D V)) (μ : Measure (GA D V))

def OrthogonalY : Prop :=
  ∀ x T, IsOrth ⊤ (Yfam Φ K x T) ∧
    ∀ π ε w, Φ.IsWeylRep D.sp.cm π ε w → Yfam Φ K x T (weylPar π ε) = Ys Φ K π ε w x T

def KernelConvergence : Prop :=
  ∀ f ∈ CcGA V, ∃ c : ℝ, ∀ T, Regular c T →
    (∀ 𝔬, IsSSClass 𝔬 → Integrable (descend (GQ V) (kT Φ K 𝔬 f T)) (autMeasure V μ)) ∧
    {𝔬 | IsSSClass 𝔬 ∧ ∫ q, ‖descend (GQ V) (kT Φ K 𝔬 f T) q‖ ∂autMeasure V μ ≠ 0}.Finite

def WeightedOrbital : Prop :=
  ∀ f ∈ CcGA V, ∀ γ : GF V, IsRegSS γ.1.1 → ∀ P, IsMinLevi Φ γ P →
    ∀ (dt : Measure (cent (rat V γ))) [dt.IsHaarMeasure], ∃ c : ℝ, ∀ T, Regular c T →
      Integrable (descend (cent (rat V γ)) fun x => (weight Φ K (aP P) T x : ℂ) * conjFn (rat V γ) f x)
        (quotMeas (cent (rat V γ)) dt μ) ∧
      ∫ q, descend (GQ V) (kT Φ K {δ | IsConj γ δ} f T) q ∂autMeasure V μ =
        volA Φ K (aP P) (cent (rat V γ)) dt *
          wOrbInt (cent (rat V γ)) dt μ (rat V γ) (fun x => weight Φ K (aP P) T x) f

end GlobalTheory.TruncKer

namespace GlobalTheory.Published

def LabesseWaldspurger : Prop :=
  (ExpFamilyIntegral ∧ FamilySmooth ∧ FamilyProduct) ∧
  ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a →
    OrthogonalY Φ (levelAll D.sp.cm.sig V.gram L a) ∧
    ∀ (μ : Measure (GA D V)) [μ.IsHaarMeasure],
      KernelConvergence Φ (levelAll D.sp.cm.sig V.gram L a) μ ∧ WeightedOrbital Φ (levelAll D.sp.cm.sig V.gram L a) μ

example (D : D7) : wittIndex (CuspDecay.Model.plane D) = 1 ∧
    ∃ (Φ : WittFrame (CuspDecay.Model.plane D)) (L : _) (a : _), Φ.IsGood D.sp.cm L a :=
  ⟨wittIndex_plane D, exists_isGood _⟩

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SphericalSectionOfMemCompact
section
noncomputable section

open scoped NNReal
open MeasureTheory Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSW.Model

section Field

variable (E : Type) [Field E] [CharZero E] [StarRing E]

theorem four_gram (e e' : Matrix (Fin 4) (Fin 1) E) (i : Matrix (Fin 4) (Fin 2) E) (he : e = !![0; 0; 1; 1])
    (he' : e' = !![0; 0; 1 / 2; -(1 / 2)]) (hi : i = !![1, 0; 0, 1; 0, 0; 0, 0]) :
    eᴴ * sgnM E ![false, true, false, true] * e = 0 ∧ e'ᴴ * sgnM E ![false, true, false, true] * e' = 0 ∧
    e'ᴴ * sgnM E ![false, true, false, true] * e = 1 ∧ iᴴ * sgnM E ![false, true, false, true] * i = sgnM E ![false, true] ∧
    iᴴ * sgnM E ![false, true, false, true] * e = 0 ∧ iᴴ * sgnM E ![false, true, false, true] * e' = 0 := by
  subst he he' hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext a b <;> rw [Matrix.mul_apply] <;>
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply] <;> fin_cases a <;> fin_cases b <;>
    simp [Fin.sum_univ_four, Examples₂.sgn] <;> norm_num

theorem two_gram (e e' : Matrix (Fin 2) (Fin 1) E) (he : e = !![1; 1]) (he' : e' = !![1 / 2; -(1 / 2)]) :
    eᴴ * sgnM E ![false, true] * e = 0 ∧ e'ᴴ * sgnM E ![false, true] * e' = 0 ∧
    e'ᴴ * sgnM E ![false, true] * e = 1 := by
  subst he he'
  refine ⟨col_gram E _ _ _ _ ?_, col_gram E _ _ _ _ ?_, col_gram E _ _ _ _ ?_⟩ <;> simp [Fin.sum_univ_two, Examples₂.sgn]
  norm_num

end Field

def hypFour (D : D7) : HypDec (diagSp D 4 ![false, true, false, true] 2 2) (diagSp D 2 ![false, true] 1 1) 1 where
  e := (!![0; 0; 1; 1] : Matrix (Fin 4) (Fin 1) D.host.E)
  e' := (!![0; 0; 1 / 2; -(1 / 2)] : Matrix (Fin 4) (Fin 1) D.host.E)
  i₀ := (!![1, 0; 0, 1; 0, 0; 0, 0] : Matrix (Fin 4) (Fin 2) D.host.E)
  ee := gram_check _ _ _ (four_gram D.host.E _ _ _ rfl rfl rfl).1
  e'e' := gram_check _ _ _ (four_gram D.host.E _ _ _ rfl rfl rfl).2.1
  e'e := gram_check _ _ _ (four_gram D.host.E _ _ _ rfl rfl rfl).2.2.1
  iso := (gram_check _ _ _ (four_gram D.host.E _ _ _ rfl rfl rfl).2.2.2.1).trans (diagSp_gram 2 _ 1 1).symm
  i₀e := gram_check _ _ _ (four_gram D.host.E _ _ _ rfl rfl rfl).2.2.2.2.1
  i₀e' := gram_check _ _ _ (four_gram D.host.E _ _ _ rfl rfl rfl).2.2.2.2.2
  rank_add := rfl

def hypTwo (D : D7) : HypDec (diagSp D 2 ![false, true] 1 1) (diagSp D 0 ![] 0 0) 1 where
  e := (!![1; 1] : Matrix (Fin 2) (Fin 1) D.host.E)
  e' := (!![1 / 2; -(1 / 2)] : Matrix (Fin 2) (Fin 1) D.host.E)
  i₀ := 0
  ee := gram_check _ _ _ (two_gram D.host.E _ _ rfl rfl).1
  e'e' := gram_check _ _ _ (two_gram D.host.E _ _ rfl rfl).2.1
  e'e := gram_check _ _ _ (two_gram D.host.E _ _ rfl rfl).2.2
  iso := by funext i; exact i.elim0
  i₀e := by funext i; exact i.elim0
  i₀e' := by funext i; exact i.elim0
  rank_add := rfl

theorem isAniso_zero (D : D7) : IsAniso (diagSp D 0 ![] 0 0) := fun _ _ h =>
  h.2.1.ne_zero ⟨0, h.1⟩ (funext fun i => i.elim0)

theorem not_isAniso {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (hr : 0 < r) : ¬ IsAniso T := fun h => by
  refine h r d.e ⟨hr, ?_, d.ee⟩
  have h1 := d.e'e
  refine (Matrix.mulVec_injective_iff (M := d.e)).1 fun x y hxy => ?_
  have h2 := congrArg ((d.e'ᴴ * T.gram) *ᵥ ·) hxy
  simpa only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using h2

theorem exists_isMaj {D : D7} (V : HSp D) : ∃ a, IsMaj V a :=
  let ⟨a, _, h⟩ := @AdelicU.Frames.exists_isLatticeFrame_isMajorantFrame _ _ _ _ _ _ _ _ _ (AdelicU.isCMExt_host D) _ (isHermND_gram V) _
    (isLattice_frameLat_host V)
  ⟨a, h⟩

theorem exists_haar_Kmax {D : D7} (T : HSp D) (b : GL (Fin T.rank) (AE D)) :
    ∃ ν : Measure (Kmax T b), ν.IsHaarMeasure ∧ IsProbabilityMeasure ν := by
  haveI : CompactSpace (Kmax T b) :=
    isCompact_iff_compactSpace.1 (isCompact_levelAll (AdelicU.isCMExt_host D) _ _ _)
  exact ⟨Measure.haarMeasure ⊤, inferInstance, ⟨Measure.haarMeasure_self⟩⟩

theorem hypotheses_isotropic (D : D7) : ∃ (ψ : AddChar (AF D.host.F) ℂ) (V T T' T₀ : HSp D) (t r' : ℕ)
    (_ : HypDec T T' t) (_ : HypDec T' T₀ r'), IsStdChar D ψ (-1) ∧
    T.rank + T'.rank = 2 * V.rank ∧ T'.rank < T.rank ∧ 0 < T'.rank ∧ IsAniso T₀ ∧ 0 < r' ∧ ¬ IsAniso T' ∧
    (∃ a, IsMaj V a) ∧ (∃ b', IsMaj T' b') ∧ (∃ θ : InfFam D, IsInfFam θ) ∧
    (∃ μ₀ 𝓕₀, IsCovolOne (ratL T V) μ₀ 𝓕₀) ∧ (∃ μ₁ 𝓕₁, IsCovolOne (ratMx D t (dblSp V).rank) μ₁ 𝓕₁) ∧
    (∃ m : Measure (GA D T'), m.IsHaarMeasure) ∧
    ∃ b, IsMaj T b ∧ ∃ ν : Measure (Kmax T b), ν.IsHaarMeasure ∧ IsProbabilityMeasure ν := by
  obtain ⟨hθ, ψ, hψ⟩ := Ker.exists_infFam_and_stdChar D
  obtain ⟨b, hb⟩ := exists_isMaj (diagSp D 4 ![false, true, false, true] 2 2)
  exact ⟨ψ, diagSp D 3 ![false, false, false] 3 0, _, _, _, 1, 1, hypFour D, hypTwo D, hψ, rfl, (by decide : 2 < 4),
    (by decide : 0 < 2), isAniso_zero D, Nat.one_pos, not_isAniso (hypTwo D) Nat.one_pos, exists_isMaj _, exists_isMaj _, hθ,
    exists_isCovolOne D _ _, exists_isCovolOne D _ _, ⟨Measure.haar, inferInstance⟩, b, hb, exists_haar_Kmax _ b⟩

example (D : D7) : rhoH (diagSp D 2 ![false, true] 1 1) 1 = 1 / 2 := by
  show ((2 : ℕ) - (1 : ℕ) : ℝ) / 2 = 1 / 2
  norm_num

theorem sphericalSection_of_mem_compact {D : D7} {T T₀ : HSp D} {r : ℕ} {d : HypDec T T₀ r} {b : GL (Fin T.rank) (AE D)}
    (h : HasIw d (Kmax T b)) (s : ℂ) {k : GA D T} (hk : k ∈ Kmax T b) : sphericalSection d b s k = 1 := by
  rw [sphericalSection, h.isIwasawa.iwAbs_of_mem hk]; simp [npow]

theorem sphericalSection_neg_rho {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (b : GL (Fin T.rank) (AE D)) :
    sphericalSection d b (-(rhoH T r : ℂ)) = 1 := by
  funext h; simp [sphericalSection, npow]

theorem IsRegElt.unique {D : D7} {S T T₀ : HSp D} {r : ℕ} {ψ : AddChar (AF D.host.F) ℂ}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {θ : InfFam D} {τ : D.what₂.Tau} {d : HypDec T T₀ r}
    {b : GL (Fin T.rank) (AE D)} (hI : HasIw d (Kmax T b)) {zG zG' zH : MvPolynomial ℕ ℂ} {P P' : Polynomial ℂ}
    (h : IsRegElt ψ om θ τ d b zG zH P) (h' : IsRegElt ψ om θ τ d b zG' zH P') : P = P' :=
  Polynomial.funext fun s => by
    have := congrFun ((h.2.2.1 s).symm.trans (h'.2.2.1 s)) 1
    simpa only [Pi.smul_apply, sphericalSection_of_mem_compact hI s (one_mem _), smul_eq_mul, mul_one] using this

end GlobalTheory.RegSW.Model

end
end

