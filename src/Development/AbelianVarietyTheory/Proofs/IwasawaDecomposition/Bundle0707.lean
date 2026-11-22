import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0602
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0688
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0575
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0687
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0305
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheafA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0275
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0690
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0691
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0674

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingCurry
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

noncomputable section

namespace GlobalTheory.FlagFibre

theorem measurePreserving_curry (ι κ : Type) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℂ) volume volume := by
  have h : (volume : Measure (ι × κ → ℂ)) =
      (volume : Measure (ι → κ → ℂ)).map (MeasurableEquiv.curry ι κ ℂ).symm := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]
    have e : (MeasurableEquiv.curry ι κ ℂ).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
      ext f; simp [MeasurableEquiv.coe_curry_symm, Function.uncurry]
    rw [e, volume_pi, Measure.pi_pi]
    simp_rw [volume_pi, Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  refine ⟨(MeasurableEquiv.curry ι κ ℂ).measurable, ?_⟩
  rw [h, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
  simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r j : ℕ} (X : Data E r) (hj : j ≤ r) {Tau : Type}
  [Fintype Tau] (κ : Tau ≃ X.Ψ)

theorem mem_OmF_of_proj (hp : X.p0 = r - j) {z : V (nd X)} (hz : proj X hj κ z ∈ DomFlat Tau j (r - j)) :
    z ∈ OmF X (x0F X) := by
  intro τ
  obtain ⟨t, rfl⟩ := κ.surjective τ
  refine ⟨?_, fun i => ?_⟩
  · have e : mat (cpt X (x0F X) z) (κ t) = mat (x0F X) (κ t) * uni (coords X κ z t) := rfl
    rw [e, det_mul, det_uni, mul_one]
    exact det_x0F X _
  · rw [dmin_cpt X κ z t i, hp]
    refine GlobalTheory.T.leading_minor_signs_over_bounded_flag_domain r j (r - j) (idx hj) (isBlockOrderedSumEquiv_trueIndex hj) _ (reindex_sgn hj) _ ?_ i
    have h := hz t
    have e : unflat (proj X hj κ z) t = toMat (base (idx hj) (coords X κ z t)) := by
      ext a b; exact proj_eq X hj κ z t (a, b)
    rwa [e] at h

theorem inter_OmF (hp : X.p0 = r - j) {S : Set (Tau × Fin j × Fin (r - j) → ℂ)} (hD : S ⊆ DomFlat Tau j (r - j)) :
    proj X hj κ ⁻¹' S ∩ OmF X (x0F X) = proj X hj κ ⁻¹' S :=
  Set.inter_eq_left.2 fun _ hz => mem_OmF_of_proj X hj κ hp (hD hz)

theorem densF_eq (z : V (nd X)) :
    densF X (x0F X) z = ∏ t, dens (sgnMat r X.p0) (coords X κ z t) := by
  rw [densF, ← κ.prod_comp]
  exact Finset.prod_congr rfl fun t _ => Finset.prod_congr rfl fun i _ => by rw [dmin_cpt X κ z t]

theorem muF_preimage (hp : X.p0 = r - j) {S : Set (Tau × Fin j × Fin (r - j) → ℂ)} (hS : MeasurableSet S)
    (hD : S ⊆ DomFlat Tau j (r - j)) :
    muF X (x0F X) (proj X hj κ ⁻¹' S) =
      ENNReal.ofReal ((flagConst j * flagConst (r - j))⁻¹ ^ Fintype.card Tau) * muD Tau j (r - j) S := by
  have hS' := measurable_proj X hj κ hS
  set c := MeasurableEquiv.curry Tau (Fin j × Fin (r - j)) ℂ with hc
  set φ : (Tau → Fin j × Fin (r - j) → ℂ) → ℝ≥0∞ := (c.symm ⁻¹' S).indicator 1 with hφ
  have hφm : Measurable φ := measurable_one.indicator (c.symm.measurable hS)
  have hDm : Measurable fun y => ENNReal.ofReal (dens (sgnMat r (r - j)) y) := (measurable_dens _).ennreal_ofReal
  have key := GlobalTheory.T.lintegral_pi_fibre_measurePreserving Tau _ _ _ (glue (idx hj)) (base (idx hj)) _ φ (GlobalTheory.T.measurePreserving_glueLowerUnitriangularBlocks _ _ _ _ (isBlockOrderedSumEquiv_trueIndex hj))
    (measurable_base _) (base_glue (isBlockOrderedSumEquiv_trueIndex hj)) hDm hφm
  have hm : Measurable fun y : Tau → Low r → ℂ => φ (fun t => base (idx hj) (y t)) *
      ∏ t, ENNReal.ofReal (dens (sgnMat r (r - j)) (y t)) :=
    (hφm.comp (measurable_pi_lambda _ fun t => (measurable_base _).comp (measurable_pi_apply t))).mul
      (Finset.measurable_prod _ fun t _ => hDm.comp (measurable_pi_apply t))
  rw [← (GlobalTheory.T.measurePreserving_flagFibreChartCoordinates E r X Tau κ).lintegral_comp hm,
    ← (measurePreserving_curry Tau (Fin j × Fin (r - j))).lintegral_comp_emb c.measurableEmbedding] at key
  rw [muF, muD, withDensity_apply _ hS', withDensity_apply _ hS, Measure.restrict_restrict hS',
    Measure.restrict_restrict hS, Set.inter_eq_left.2 hD,
    inter_OmF X hj κ hp hD, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_indicator hS', ← lintegral_indicator hS]
  refine Eq.trans (lintegral_congr fun z => ?_) (key.trans (lintegral_congr fun v => ?_))
  · have e : c.symm (fun t => base (idx hj) (coords X κ z t)) = proj X hj κ z :=
      funext fun s => (proj_eq X hj κ z s.1 s.2).symm
    by_cases h : proj X hj κ z ∈ S
    · rw [Set.indicator_of_mem (show z ∈ proj X hj κ ⁻¹' S from h), hφ,
        Set.indicator_of_mem (by rwa [Set.mem_preimage, e]), Pi.one_apply, one_mul, densF_eq X κ, hp,
        ENNReal.ofReal_prod_of_nonneg fun _ _ => dens_nonneg _ _]
    · rw [Set.indicator_of_notMem (show z ∉ proj X hj κ ⁻¹' S from h), hφ,
        Set.indicator_of_notMem (by rwa [Set.mem_preimage, e]), zero_mul]
  · by_cases h : v ∈ S
    · rw [Set.indicator_of_mem h, hφ, Set.indicator_of_mem (show c v ∈ c.symm ⁻¹' S from h), Pi.one_apply, one_mul]
      have hc0 : 0 < flagConst j * flagConst (r - j) := mul_pos (flagConst_pos _) (flagConst_pos _)
      have hv : ∀ t, toMat (c v t) ∈ hcDom j (r - j) := hD h
      have hpos : ∀ t, 0 ≤ (hQ (toMat (c v t))).det.re ^ (-((j + (r - j) : ℕ) : ℤ)) := fun t =>
        zpow_nonneg (Complex.pos_iff.1 (PosDef.det_pos (hv t))).1.le _
      rw [Finset.prod_congr rfl fun t _ => GlobalTheory.T.lintegral_flagDensity_fibre_boundedDomain r j (r - j) (idx hj) (isBlockOrderedSumEquiv_trueIndex hj) (sgnMat r (r - j))
        (reindex_sgn hj) (c v t) (hv t), ← ENNReal.ofReal_prod_of_nonneg fun t _ => div_nonneg (hpos t) hc0.le,
        ← ENNReal.ofReal_mul (by positivity), Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
        div_eq_inv_mul, inv_pow]
      rfl
    · rw [Set.indicator_of_notMem h, hφ, Set.indicator_of_notMem (show c v ∉ c.symm ⁻¹' S from h), zero_mul]

theorem covol_eq_muD : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r)
    (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ F, IsFD (gammaU X hj κ) F →
    muD Tau j (r - j) F < ⊤ ∧
      covol X = grassConst j (r - j) ^ Fintype.card Tau * (muD Tau j (r - j) F).toReal := by
  intro E _ _ _ r j X hj Tau _ κ hp F hF
  obtain ⟨F', hm, hsub, h0, hfs⟩ := GlobalTheory.T.isFundamentalSet_chart_preimage_fundamentalDomain E r j X hj Tau κ hp (GlobalTheory.T.domain_point_stabilizer_trivial E r j X hj Tau κ hp)
    (fun N hN hD h => by rw [muF_preimage X hj κ hp hN hD, h, mul_zero]) F hF
  have hD := hsub.trans hF.2.1
  rw [inter_OmF X hj κ hp hD] at hfs
  obtain ⟨h1, h2⟩ := covol_eq X (isOrth_x0F X) hfs
  have e : muD Tau j (r - j) F' = muD Tau j (r - j) F := (measure_eq_measure_of_null_diff hsub h0)
  have hc0 : 0 < flagConst j * flagConst (r - j) := mul_pos (flagConst_pos _) (flagConst_pos _)
  rw [muF_preimage X hj κ hp hm hD, e] at h1 h2
  refine ⟨?_, ?_⟩
  · refine lt_top_iff_ne_top.2 fun h => h1.ne ?_
    rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
  · have e1 : flagConst r = grassConst j (r - j) * (flagConst j * flagConst (r - j)) := by
      rw [← mul_assoc, ← flagConst_add, Nat.add_sub_cancel' hj]
    have e2 : X.Ψ.card = Fintype.card Tau := by rw [Fintype.card_congr κ, Fintype.card_coe]
    rw [h2, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), e1, e2, mul_pow, inv_pow]
    field_simp

end GlobalTheory.FlagFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemStalkIdealOfCodimOne
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.PrincipalHartogs

theorem mem_span_singleton_of_forall_height_le_one {B : Type} [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] [IsNoetherianRing B] (f s : B)
    (h : ∀ q : Ideal B, q.IsPrime → q.height ≤ 1 → ∃ u, u ∉ q ∧ u * s ∈ Ideal.span {f}) :
    s ∈ Ideal.span {f} := by
  by_cases hf : f = 0
  · subst hf
    obtain ⟨u, hu, hus⟩ := h ⊥ Ideal.isPrime_bot (by simp)
    rw [Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at hus ⊢
    rcases mul_eq_zero.mp hus with h0 | h0
    · exact absurd (h0 ▸ Submodule.zero_mem ⊥) hu
    · exact h0
  let K := FractionRing B
  have hfK : algebraMap B K f ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr hf
  let d : Ideal B := (Ideal.span {f}).colon {s}
  have hd : ∀ a, a ∈ d ↔ a * s ∈ Ideal.span {f} := fun a => by
    simp only [d, Submodule.mem_colon_singleton, smul_eq_mul]
  by_cases hd1 : d = ⊤
  · simpa using (hd 1).1 (hd1 ▸ Submodule.mem_top)
  exfalso
  obtain ⟨Q, hQ, hdQ⟩ := Ideal.exists_le_maximal d hd1
  have hreg : ∀ a c : B, algebraMap B K a * (algebraMap B K s / algebraMap B K f) = algebraMap B K c →
      a ∈ d := fun a c e => by
    rw [hd, Ideal.mem_span_singleton]
    refine ⟨c, ?_⟩
    rw [← mul_div_assoc, div_eq_iff hfK, ← map_mul, ← map_mul] at e
    rw [mul_comm f c]
    exact IsFractionRing.injective B K e
  obtain ⟨p, hp, -, h1, hpf⟩ := NormalPole.exists_height_one (K := K)
    (algebraMap B K s / algebraMap B K f) Q (fun a c e => hdQ (hreg a c e))
  obtain ⟨u, hu, hus⟩ := h p hp h1.le
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hus
  refine hu (hpf u c ?_)
  rw [← mul_div_assoc, div_eq_iff hfK, ← map_mul, ← map_mul, hc]

end GlobalTheory.PrincipalHartogs

namespace GlobalTheory.PrincipalHartogs

theorem mem_stalkId_of_forall_ringKrullDim_le_one : ∀ (V : Scheme.{0}) (I : V.IdealSheafData), (∀ v : V, IsDomain (V.presheaf.stalk v) ∧ IsIntegrallyClosed (V.presheaf.stalk v) ∧ IsNoetherianRing (V.presheaf.stalk v)) → (∀ v : V, (FinalTheorems.stalkId I v).IsPrincipal) → ∀ s : Γ(V, ⊤), (∀ v : V, ringKrullDim (V.presheaf.stalk v) ≤ 1 → (V.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v) → ∀ v : V, (V.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v := by
  intro V I hB hPr s hs v
  obtain ⟨hd, hic, hn⟩ := hB v
  obtain ⟨f, hf0⟩ := (hPr v).principal
  have hf : FinalTheorems.stalkId I v = Ideal.span {f} := hf0
  obtain ⟨U, hU, hv, -⟩ := exists_isAffineOpen_mem_and_subset (x := v) (U := ⊤) trivial
  letI : Algebra Γ(V, U) (V.presheaf.stalk v) := V.presheaf.algebra_section_stalk ⟨v, hv⟩
  haveI hlocv := hU.isLocalization_stalk ⟨v, hv⟩
  set t : Γ(V, U) := V.presheaf.map (homOfLE le_top).op s with ht
  have hgerm : ∀ (y : V) (hy : y ∈ U), (V.presheaf.germ ⊤ y trivial).hom s =
      (V.presheaf.germ U y hy).hom t := fun y hy => by
    rw [ht, ← CommRingCat.comp_apply, V.presheaf.germ_res]
  have key : ∀ q : Ideal (V.presheaf.stalk v), q.IsPrime → q.height ≤ 1 →
      ∃ u, u ∉ q ∧ u * (V.presheaf.germ ⊤ v trivial).hom s ∈ Ideal.span {f} := by
    intro q hq hq1
    let P : Ideal Γ(V, U) := q.comap (algebraMap Γ(V, U) (V.presheaf.stalk v))
    haveI hPp : P.IsPrime := Ideal.comap_isPrime _ q
    let Pt : PrimeSpectrum Γ(V, U) := ⟨P, hPp⟩
    have hyU : hU.fromSpec Pt ∈ U := by
      have : hU.fromSpec Pt ∈ Set.range hU.fromSpec := ⟨Pt, rfl⟩
      rwa [hU.range_fromSpec] at this
    let yU : U := ⟨hU.fromSpec Pt, hyU⟩
    have hPt : hU.primeIdealOf yU = Pt :=
      hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf yU)
    letI : Algebra Γ(V, U) (V.presheaf.stalk yU.1) := V.presheaf.algebra_section_stalk yU
    have hlocy := hU.isLocalization_stalk yU
    rw [hPt] at hlocy
    have hdim : ringKrullDim (V.presheaf.stalk yU.1) ≤ 1 := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (V.presheaf.stalk yU.1)]
      have := IsLocalization.height_comap (hU.primeIdealOf ⟨v, hv⟩).asIdeal.primeCompl q
      change (P.height : WithBot ℕ∞) ≤ 1
      rw [show P = Ideal.under Γ(V, U) q from rfl, this]
      exact_mod_cast hq1
    have hy := hs yU.1 hdim
    rw [hgerm yU.1 hyU, ds_stalkId_eq_map I ⟨U, hU⟩ yU.1 hyU] at hy
    change algebraMap Γ(V, U) (V.presheaf.stalk yU.1) t ∈
      Ideal.map (algebraMap Γ(V, U) (V.presheaf.stalk yU.1)) (I.ideal ⟨U, hU⟩) at hy
    obtain ⟨⟨a, w⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff P.primeCompl _).mp hy
    rw [← map_mul] at e
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := P.primeCompl) e
    refine ⟨algebraMap Γ(V, U) (V.presheaf.stalk v) (c * w), ?_, ?_⟩
    · exact (P.primeCompl.mul_mem c.2 w.2 : (c : Γ(V, U)) * w ∉ P)
    · rw [← hf, ds_stalkId_eq_map I ⟨U, hU⟩ v hv, hgerm v hv]
      change algebraMap Γ(V, U) (V.presheaf.stalk v) (c * w) * algebraMap Γ(V, U) _ t ∈
        Ideal.map (algebraMap Γ(V, U) (V.presheaf.stalk v)) (I.ideal ⟨U, hU⟩)
      rw [← map_mul, show (c : Γ(V, U)) * w * t = c * (t * w) by ring, hc]
      exact Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ _ a.2)
  rw [hf]
  exact mem_span_singleton_of_forall_height_le_one f _ key

end GlobalTheory.PrincipalHartogs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundBlocksOfBlockDiagonal
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.GoodMetric

theorem pow_le_logTwo_mul_pow {L : ℝ} {N N' k : ℕ} (hN' : N = 0 → N' = 0) (hL : N = 0 ∨ Real.log 2 ≤ L)
    (hk : k ≤ N') : L ^ k ≤ (Real.log 2)⁻¹ ^ N' * L ^ N' := by
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hD : 1 ≤ (Real.log 2)⁻¹ ^ N' := one_le_pow₀ (one_le_inv₀ h2 |>.2 h2'.le)
  rcases hL with hN | hL
  · have : N' = 0 := hN' hN
    subst this
    have : k = 0 := by omega
    subst this
    simp
  · have hL0 : 0 < L := h2.trans_le hL
    rcases le_or_gt 1 L with h1 | h1
    · calc L ^ k ≤ L ^ N' := pow_le_pow_right₀ h1 hk
        _ = 1 * L ^ N' := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hD (by positivity)
    · calc L ^ k ≤ 1 := pow_le_one₀ hL0.le h1.le
        _ ≤ (L * (Real.log 2)⁻¹) ^ N' := one_le_pow₀ (by rw [← div_eq_mul_inv, one_le_div h2]; exact hL)
        _ = _ := by rw [mul_pow, mul_comm]

theorem sum_abs_log_eq_zero_or_ge {n : ℕ} (S : Finset (Fin n)) (v : ReciprocityTheory.L2DbarEstimates.V n)
    (hS : ∀ a ∈ S, ‖v a‖ < 1 / 2) :
    ∑ a ∈ S, |Real.log ‖v a‖| = 0 ∨ Real.log 2 ≤ ∑ a ∈ S, |Real.log ‖v a‖| := by
  by_cases h : ∀ a ∈ S, |Real.log ‖v a‖| = 0
  · exact Or.inl (Finset.sum_eq_zero h)
  · push_neg at h
    obtain ⟨a, ha, hne⟩ := h
    right
    have hv : ‖v a‖ ≠ 0 := fun h0 => hne (by rw [h0]; simp)
    have hpos : 0 < ‖v a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    have hlt : Real.log ‖v a‖ < Real.log (1 / 2) := Real.log_lt_log hpos (hS a ha)
    have hl : Real.log 2 ≤ |Real.log ‖v a‖| := by
      rw [one_div, Real.log_inv] at hlt
      rw [abs_of_neg (by linarith [Real.log_pos one_lt_two])]
      linarith
    exact hl.trans (Finset.single_le_sum (f := fun a => |Real.log ‖v a‖|) (fun _ _ => abs_nonneg _) ha)

end GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric

theorem goodBound_of_blockDiagonal' : ∀ (n : ℕ) (S : Finset (Fin n)) (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (G : ∀ τ : ι, ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin (m τ)) (Fin (m τ)) ℂ) (c : ℝ) (N : ℕ), ∃ (c' : ℝ) (N' : ℕ), ∀ v : ReciprocityTheory.L2DbarEstimates.V n, (∀ a ∈ S, ‖v a‖ < 1 / 2) → (Matrix.blockDiagonal' fun τ => G τ v).det ≠ 0 → (∀ p q, ContDiffAt ℝ 2 (fun u => (Matrix.blockDiagonal' fun τ => G τ u) p q) v) → GlobalTheory.GoodMetric.GoodBound S c N (fun u => Matrix.blockDiagonal' fun τ => G τ u) v → ∀ τ, GlobalTheory.GoodMetric.GoodBound S c' N' (G τ) v := by
  intro n S ι _ _ m G c N
  set K := ∑ τ, m τ
  set N' := N * (K + 1)
  set F : ℝ := ∏ τ, ((m τ).factorial : ℝ)
  set D : ℝ := (Real.log 2)⁻¹ ^ N'
  refine ⟨F * (max 1 c) ^ (K + 1) * D, N', ?_⟩
  intro v hS hdet hC hG τ
  set L := ∑ a ∈ S, |Real.log ‖v a‖| with hLdef
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hdp : 0 < ‖(Matrix.blockDiagonal' fun τ => G τ v).det‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hdet)
  have hcY : 0 < c * L ^ N := hdp.trans_le hG.det
  have hY : 0 < L ^ N := by
    rcases (pow_nonneg hL0 N).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hcY; exact absurd hcY (lt_irrefl 0)
  have hc : 0 < c := pos_of_mul_pos_left hcY hY.le
  have hLN : N = 0 ∨ Real.log 2 ≤ L := by
    rcases sum_abs_log_eq_zero_or_ge S v hS with h | h
    · left
      by_contra hN
      rw [← hLdef] at h
      rw [h, zero_pow hN] at hY
      exact lt_irrefl 0 hY
    · exact Or.inr h
  have hN' : N = 0 → N' = 0 := fun h => by simp [N', h]
  have key : ∀ k ≤ N', L ^ k ≤ D * L ^ N' := fun k hk => pow_le_logTwo_mul_pow hN' hLN hk
  have hF : 1 ≤ F := by
    have : F = ((∏ τ, (m τ).factorial : ℕ) : ℝ) := by simp [F]
    rw [this]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _)
  have hD : 1 ≤ D := one_le_pow₀ ((one_le_inv₀ (Real.log_pos one_lt_two)).2
    (by have := Real.log_two_lt_d9; linarith))
  have hM1 : 1 ≤ max 1 c := le_max_left _ _
  have hcF : c ≤ F * (max 1 c) ^ (K + 1) :=
    calc c ≤ max 1 c := le_max_right _ _
      _ ≤ (max 1 c) ^ (K + 1) := le_self_pow₀ hM1 (by omega)
      _ = 1 * (max 1 c) ^ (K + 1) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hF (by positivity)
  have hcc' : c ≤ F * (max 1 c) ^ (K + 1) * D :=
    hcF.trans (le_mul_of_one_le_right (by positivity) hD)

  have hent : ∀ τ' (i j : Fin (m τ')), ‖G τ' v i j‖ ≤ c * L ^ N := fun τ' i j => by
    have := hG.entry ⟨τ', i⟩ ⟨τ', j⟩
    simpa [Matrix.blockDiagonal'_apply_eq] using this
  have hprod : (Matrix.blockDiagonal' fun τ => G τ v).det = ∏ τ', (G τ' v).det :=
    GlobalTheory.Div.BlockChangeDet.det_blockDiagonal'_eq_prod _
  have hunit : ∀ τ', IsUnit (G τ' v).det := fun τ' => by
    rw [hprod] at hdet
    exact (Finset.prod_ne_zero_iff.1 hdet τ' (Finset.mem_univ _)).isUnit
  have hCτ : ∀ τ', GlobalTheory.HermFrame.MContDiffAt 2 (G τ') v := fun τ' i j => by
    have := hC ⟨τ', i⟩ ⟨τ', j⟩
    simpa [Matrix.blockDiagonal'_apply_eq] using this
  have hconn : ∀ ξ, GlobalTheory.HermFrame.conn (fun u => Matrix.blockDiagonal' fun τ => G τ u) v ξ =
      Matrix.blockDiagonal' fun τ => GlobalTheory.HermFrame.conn (G τ) v ξ := fun ξ =>
    GlobalTheory.HermFrame.conn_blockDiagonal' hunit ξ
  have hcurv : ∀ ξ η, GlobalTheory.HermFrame.curv (fun u => Matrix.blockDiagonal' fun τ => G τ u) v ξ η =
      Matrix.blockDiagonal' fun τ => GlobalTheory.HermFrame.curv (G τ) v ξ η := fun ξ η =>
    GlobalTheory.HermFrame.curv_blockDiagonal' hCτ hunit ξ η
  have hdel : ∀ ξ η, GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.conn
      (fun u => Matrix.blockDiagonal' fun τ => G τ u) u ξ) v η =
      Matrix.blockDiagonal' fun τ => GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.conn (G τ) u ξ) v η := by
    intro ξ η
    have he : (fun u => GlobalTheory.HermFrame.conn (fun u => Matrix.blockDiagonal' fun τ => G τ u) u ξ) =ᶠ[𝓝 v]
        fun u => Matrix.blockDiagonal' fun τ => GlobalTheory.HermFrame.conn (G τ) u ξ :=
      (Filter.eventually_all.2 fun i => (hCτ i).eventually_isUnit (hunit i)).mono
        fun x hx => GlobalTheory.HermFrame.conn_blockDiagonal' hx ξ
    rw [GlobalTheory.HermFrame.mdel_congr he, GlobalTheory.HermFrame.mdel_blockDiagonal']

  set e := c * L ^ N
  set M := max 1 e
  have hM : 1 ≤ M := le_max_left _ _
  have hdetle : ∀ τ', ‖(G τ' v).det‖ ≤ ((m τ').factorial : ℝ) * M ^ m τ' := fun τ' => by
    have := Matrix.det_le (abv := NormedField.toAbsoluteValue ℂ) (A := G τ' v) (x := M)
      fun i j => (hent τ' i j).trans (le_max_right _ _)
    calc ‖(G τ' v).det‖ = (NormedField.toAbsoluteValue ℂ) (G τ' v).det := rfl
      _ ≤ _ := this
      _ = _ := by simp [Fintype.card_fin, nsmul_eq_mul]
  set P := ∏ τ' ∈ Finset.univ.erase τ, ‖(G τ' v).det‖
  have hnorm : ‖(Matrix.blockDiagonal' fun τ => G τ v).det‖ = ‖(G τ v).det‖ * P := by
    rw [hprod, norm_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
  have hP0 : 0 < P := Finset.prod_pos fun τ' _ => norm_pos_iff.2 (hunit τ').ne_zero
  have hinv : ‖(G τ v).det‖⁻¹ = ‖(Matrix.blockDiagonal' fun τ => G τ v).det‖⁻¹ * P := by
    rw [hnorm, mul_inv, mul_assoc, inv_mul_cancel₀ hP0.ne', mul_one]
  have hPle : P ≤ F * M ^ K := by
    have h1 : P ≤ ∏ τ' ∈ Finset.univ.erase τ, ((m τ').factorial : ℝ) * M ^ m τ' :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun τ' _ => hdetle τ'
    have h2 : ∏ τ' ∈ Finset.univ.erase τ, ((m τ').factorial : ℝ) * M ^ m τ' ≤
        ∏ τ', ((m τ').factorial : ℝ) * M ^ m τ' := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
      refine le_mul_of_one_le_left (Finset.prod_nonneg fun _ _ => by positivity) ?_
      exact one_le_mul_of_one_le_of_one_le
        (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)) (one_le_pow₀ hM)
    have h3 : ∏ τ', ((m τ').factorial : ℝ) * M ^ m τ' = F * M ^ K := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    linarith
  have hMle : M ≤ max 1 c * max 1 (L ^ N) :=
    max_le (one_le_mul_of_one_le_of_one_le hM1 (le_max_left _ _))
      (mul_le_mul (le_max_right _ _) (le_max_right _ _) hY.le (by positivity))
  have hMY : (max 1 (L ^ N)) ^ (K + 1) ≤ D * L ^ N' := by
    rcases le_total 1 (L ^ N) with h | h
    · rw [max_eq_right h, ← pow_mul]; exact key _ le_rfl
    · rw [max_eq_left h, one_pow]; simpa using key 0 (Nat.zero_le _)
  refine ⟨fun i j => ?_, ?_, fun a i j => ?_, fun a b i j => ?_, fun a b i j => ?_⟩
  · calc ‖G τ v i j‖ ≤ c * L ^ N := hent τ i j
      _ ≤ c * (D * L ^ N') := mul_le_mul_of_nonneg_left (key N (by simp [N']; exact Nat.le_mul_of_pos_right _ (by omega))) hc.le
      _ = c * D * L ^ N' := by ring
      _ ≤ F * (max 1 c) ^ (K + 1) * D * L ^ N' :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcF (by positivity)) (by positivity)
  · rw [hinv]
    calc ‖(Matrix.blockDiagonal' fun τ => G τ v).det‖⁻¹ * P ≤ e * (F * M ^ K) :=
          mul_le_mul hG.det hPle hP0.le hcY.le
      _ ≤ M * (F * M ^ K) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ = F * M ^ (K + 1) := by ring
      _ ≤ F * (max 1 c * max 1 (L ^ N)) ^ (K + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hMle _) (by positivity)
      _ = F * (max 1 c) ^ (K + 1) * (max 1 (L ^ N)) ^ (K + 1) := by ring
      _ ≤ F * (max 1 c) ^ (K + 1) * (D * L ^ N') := mul_le_mul_of_nonneg_left hMY (by positivity)
      _ = _ := by ring
  · have := hG.form a ⟨τ, i⟩ ⟨τ, j⟩
    rw [hconn, Matrix.blockDiagonal'_apply_eq] at this
    exact this.trans hcc'
  · have := hG.dbar a b ⟨τ, i⟩ ⟨τ, j⟩
    rw [hcurv, Matrix.blockDiagonal'_apply_eq] at this
    exact this.trans hcc'
  · have := hG.del a b ⟨τ, i⟩ ⟨τ, j⟩
    rw [hdel, hdel, Matrix.sub_apply, Matrix.blockDiagonal'_apply_eq, Matrix.blockDiagonal'_apply_eq,
      ← Matrix.sub_apply] at this
    exact this.trans hcc'

end GlobalTheory.GoodMetric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFamilyChartHolomorphicStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_family_chart_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (d g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (ch : AlgChart (genStr Z) σ d) (i : Fin Fu.n) (B : Set (ReciprocityTheory.L2DbarEstimates.V d)) (P : ReciprocityTheory.L2DbarEstimates.V d → ((Fu.Di i).La →+ (Fin g → ℂ))), IsOpen B → B ⊆ ch.e.target → (∀ b ∈ B, IsPeriod (Fu.Di i) ty (P b)) → (∀ v, DifferentiableOn ℂ (fun b => P b v) B) → (∀ b ∈ B, ∀ y : FrPt Xo c (CAt σ), ch.e.symm b = cxPt Z y → Fu.u i (P b) = y.x) → Mono (genι Z) → ∀ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (F : EigFrame Z φ (LogKS.chart V ≫ genι Z)), LogKS.chart V ≫ genStr Z = spMap φ → ∃ z : ReciprocityTheory.L2DbarEstimates.V d → ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ), (∀ τ k, DifferentiableOn ℂ (fun b => z b τ k) {b ∈ B | ch.e.symm b ∈ ptsIn (genStr Z) σ V.1 ∧ ¬ LiesIn (ch.e.symm b) (genBd Z)}) ∧ ∀ b ∈ B, ∀ (hy : ch.e.symm b ∈ ptsIn (genStr Z) σ V.1) (f : EigFrame Z σ ((ch.e.symm b).1 ≫ genι Z)), F.IsMap (evHom hy) f → ∀ q : FrPt Xo c (CAt σ), cxPt Z q = ch.e.symm b → (∀ τ k, ∃ w : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left, w ≫ Z.m0.toSABMap.φ = q.u τ k ∧ w ≫ Z.m.φ = f.v τ k) → ∀ τ k, IsDerivAt0 (fun w => (Fu.ex i (P b) w).left) (z b τ k) (q.u τ k) := by
  first | exact @GlobalTheory.ShFam.ExpCoord.exists_expCoord | exact GlobalTheory.ShFam.ExpCoord.exists_expCoord | (intros; apply GlobalTheory.ShFam.ExpCoord.exists_expCoord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMatrixPolynomialGrowthPuncturedPolydiscStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodMatrix_polynomialGrowth_puncturedPolydisc : ∀ (n a d : ℕ) (τ : (Fin n → ℂ) → Fin d → Fin d → ℂ) (c : Fin d → Fin d → ℂ), DifferentiableOn ℂ τ (logDom n a) → (∀ s ∈ logDom n a, ∀ v : Fin d → ℝ, v ≠ 0 → 0 < (∑ i, ∑ j, (v i : ℂ) * τ s i j * (v j : ℂ)).im) → (∀ s ∈ logDom n a, ∀ i j, τ s i j - τ s j i = c i j) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖τ s‖ ≤ C * (1 + ‖s‖) ^ k := by
  first | exact @GlobalTheory.period_matrix_polynomial_growth | exact GlobalTheory.period_matrix_polynomial_growth | (intros; apply GlobalTheory.period_matrix_polynomial_growth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
section
noncomputable section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LieBase

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open Classical in

def pointPoly (H : Host E) (Dw : Datum H) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ :=
  ∏ τ : GlobalTheory.AllWt.Psi H, (C ((-1 : ℝ) ^ Dw.mult τ.1) * X (τ.1, Dw.mult τ.1)) ^ (Dw.p + Dw.q - Dw.mult τ.1)

end GlobalTheory.LieBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarisedAbelianPartIsoOfBundleSquareIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedAbelianPart_iso_of_bundleSquare_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) → ∃ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen ∧ wL.IsGen ∧ IsMonHom Φ.hom ∧ ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL') := by
  first | exact @GlobalTheory.unif_sq_polarised_iso | exact GlobalTheory.unif_sq_polarised_iso | (intros; apply GlobalTheory.unif_sq_polarised_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pre_model_chart_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Pre Y i₀) (L : FinLB (Y Z.i).X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd (Y Z.i).t L M) (ι : Fin Z.m → Fin L.n) (ρ : ∀ a, Γ((Y Z.i).X, L.U (ι a)) →+* Γ(Z.X, (Z.U a).1)) (g : ∀ en : En Dw.mult, Z.X ⟶ PSpace (Z.i.c.V W) (plN M en.1)), Comparison₂ Z L aff crd ι ρ g → ∀ (n : ℕ) (u : Fin n → Let Dw.mult) (kk : Fin n) (h₀ : Down (u ∘ Fin.castLE kk.2.le)) (h₁ : Down (u ∘ Fin.castLE (Nat.succ_le_of_lt kk.2))) (L' : FinLB Z.X) (ix : Fin L'.n → Fin L.n) (q₀ : Fin L'.n → Fin (plN M kk + 1)) (q₁ : Fin L'.n → Fin (plN M (kk + 1) + 1)) (r : ∀ (a : Fin Z.m) (i : Fin L'.n), Γ(Z.X, (Z.U a).1 ⊓ L'.U i)ˣ), IsLine Z L aff crd g ⟨kk, _, h₀⟩ ⟨kk + 1, _, h₁⟩ L' ix q₀ q₁ r → ∀ (k : Type) [Field k] a a' i (φ : Γ(Z.X, (Z.U a).1) →+* k) (φ' : Γ(Z.X, (Z.U a').1) →+* k) (cf : Fin (Dw.mult (u kk).1) → k), spMap φ ≫ Z.chart a = spMap φ' ≫ Z.chart a' → ⊤ ≤ (spMap φ ≫ Z.chart a) ⁻¹ᵁ L'.U i → (∀ m, (u kk).2 < m → cf m = 0) → IsCombAtG (Y Z.i).t (spMap φ ≫ Z.chart a ≫ Z.π) ((Z.fr a).bc φ (u kk).1) cf ((Z.fr a').bc φ' (u kk).1 (u kk).2) → valF (spMap φ ≫ Z.chart a) _ (r a i).val = valF (spMap φ ≫ Z.chart a) _ (r a' i).val * cf (u kk).2 := by
  first | exact @GlobalTheory.FlagEmb.LChart.gen_change | exact GlobalTheory.FlagEmb.LChart.gen_change | (intros; apply GlobalTheory.FlagEmb.LChart.gen_change <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimitiveBalancedFormEqOfSameRayStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveBalancedForm_eq_of_same_ray : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X]
    (β β' : balForms bar X) (p r : ℕ), IsPrim bar β → IsPrim bar β' → 0 < p → 0 < r → p • β = r • β' → β = β' := by
  first | exact @GlobalTheory.PolFan.isPrim_ray_eq | exact GlobalTheory.PolFan.isPrim_ray_eq | (intros; apply GlobalTheory.PolFan.isPrim_ray_eq <;> assumption)
end

