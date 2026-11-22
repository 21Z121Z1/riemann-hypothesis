import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2419
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1957
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.ExistsFundSetOrth
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2430
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonLevelCoverPullbackProbability
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevPullNorm

theorem sum_mul_fibre {ι κ : Type} [Fintype ι] [Fintype κ] (π : ι → κ) (w : ι → ℕ) (N : ℕ) (I : κ → ℝ≥0∞)
    (h : ∀ k, ∑ᶠ i : {i // π i = k}, w i.1 = N) : ∑ i, (w i : ℝ≥0∞) * I (π i) = N * ∑ k, I k := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ π, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := h k
  rw [finsum_eq_sum_of_fintype] at hk
  rw [← hk, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_subtype _ (p := fun i => π i = k) (by simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [i.2]

theorem goodEmb_comp_eF (D : D7) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (d : DeltaDat Xo c 0) (σ₂ : d.c₂.F →+* ℂ) :
    GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) ↔ GoodEmb d.c₂ σ₂ := by
  unfold GoodEmb
  rfl

theorem frame_tr {E : Type} [Field E] {r : ℕ} {A B : Finset (E →+* ℂ)} (h : A = B) (x : Frame A r) (ρ : E →+* ℂ)
    (h₁ : ρ ∈ B) (h₂ : ρ ∈ A) : (h ▸ x : Frame B r) ⟨ρ, h₁⟩ = x ⟨ρ, h₂⟩ := by
  subst h; rfl

theorem relab_eF (D : D7) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (d : DeltaDat Xo c 0) (τ : d.c₂.F →+* ℂ) :
    relab c (τ.comp (d.eF : c.F →+* d.c₂.F)) = relab d.c₂ τ := by
  funext ρ
  ext a
  rfl

theorem goodOf_eF (D : D7) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (d : DeltaDat Xo c 0) (σ₂ : d.c₂.F →+* ℂ) :
    goodOf c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) = (goodOf d.c₂ σ₂).comp (d.eF : c.F →+* d.c₂.F) := by
  unfold goodOf
  by_cases h : GoodEmb d.c₂ σ₂
  · rw [if_pos ((goodEmb_comp_eF D d σ₂).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((goodEmb_comp_eF D d σ₂).1 h')), if_neg h]
    rfl

theorem pnorm_lact_transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (hΨ : X'.Ψ = X.Ψ) (δ : GL (Fin r) E) (la : Wt X.Ψ r) (la' : Wt X'.Ψ r) (P : Frame X.Ψ r → ℂ) (P' : Frame X'.Ψ r → ℂ) (t : ℂ) (n : ℕ), X'.Gm = X.Gm → X'.p0 = X.p0 → (∀ v w, herm X.Gm ((δ : Matrix (Fin r) (Fin r) E).mulVec v) ((δ : Matrix (Fin r) (Fin r) E).mulVec w) = herm X.Gm v w) → (∀ (τ : E →+* ℂ) (h : τ ∈ X'.Ψ) (i : Fin r), la' ⟨τ, h⟩ i = la ⟨τ, hΨ ▸ h⟩ i) → ‖t‖ = 1 → (∀ x ∉ X'.dom, P' x = 0) → (∀ x ∉ X.dom, P x = 0) → (∀ x ∈ X'.dom, P' x = t ^ n * P (lact δ (hΨ ▸ x))) → ∀ y : Frame X'.Ψ r, X'.pnorm la' P' y = X.pnorm la P (lact δ (hΨ ▸ y)) := by
  intro E _ _ _ r X X' hΨ δ la la' P P' t n hG hp hu hla ht h0' h0 hrel y
  cases X'
  cases hΨ
  cases hG
  cases hp
  have hla' : la' = la := funext fun τ => funext fun i => hla τ.1 τ.2 i
  subst hla'
  have hun : GlobalTheory.SW.IsUn X δ := hu
  have hd : ∀ (z : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)), dmin X.Gm (lact δ z) τ i = dmin X.Gm z τ i :=
    fun z τ i => GlobalTheory.Dict.Extend.dmin_lact hun z τ i
  have hdom : ∀ z : Frame X.Ψ r, lact δ z ∈ X.dom → z ∈ X.dom := by
    intro z hz τ
    refine ⟨fun h => (hz τ).1 ?_, fun i => by rw [← hd z τ i]; exact (hz τ).2 i⟩
    show ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat z τ).det = 0
    rw [Matrix.det_mul, h, mul_zero]
  show _ = X.pnorm _ P (lact δ y)
  unfold Data.pnorm
  by_cases hy : y ∈ X.dom
  · rw [hrel y hy, norm_mul, norm_pow, ht, one_pow, one_mul]
    refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => ?_)
    rw [hd, hd]
  · have hy' : lact δ y ∉ X.dom := fun h => hy (hdom y h)
    rw [h0' y hy, h0 _ hy', norm_zero, zero_mul, zero_mul]

theorem petE_sq_mul_vol : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (G : WTZ D.host.E) (f : Rul Xo c), f ∈ cuspW Xo c U G → ∀ (x0 : ∀ k, Frame ((U σ).X k).Ψ D.R.r) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))), (∀ k, IsOrth ((U σ).X k) (x0 k) ∧ IsFundSet ((U σ).X k) (x0 k) (FF k)) → (∑ k, muF ((U σ).X k) (x0 k) (FF k)) ≠ 0 ∧ (∑ k, muF ((U σ).X k) (x0 k) (FF k)) ≠ ⊤ ∧ petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) (modelWt (U σ) G) (rdU (U σ) f) ^ 2 * ∑ k, muF ((U σ).X k) (x0 k) (FF k) = ∑ k, ∫⁻ z in FF k, ENNReal.ofReal (((U σ).X k).pnorm (modelWt (U σ) G k) (rdU (U σ) f k) (cpt ((U σ).X k) (x0 k) z) ^ 2) ∂(muF ((U σ).X k) (x0 k)) := by
  intro D j H Dw l Xo c U dict hL σ hσ G f hf x0 FF hx
  have hsf : ∀ k, ((U σ).X k).IsSec (modelWt (U σ) G k) (rdU (U σ) f k) := fun k =>
    GlobalTheory.PeterssonCompare.isSec_of_mem_holSub _ _ ((mem_cuspW.1 hf).2 σ hσ) k
  obtain ⟨h0, hT, hI⟩ := GlobalTheory.T.adelicProbability_eq_normalised_fundamentalSets D j H Dw l Xo c U dict hL σ hσ x0 FF hx
  refine ⟨h0, hT, ?_⟩
  have := hI (fun k y => ENNReal.ofReal (((U σ).X k).pnorm (modelWt (U σ) G k) (rdU (U σ) f k) y ^ 2))
    (fun k => ENNReal.measurable_ofReal.comp ((GlobalTheory.PeterssonCompare.measurable_pnorm _ _
      (hsf k).1.continuousOn (fun y hy => dif_neg hy)).pow_const 2))
    (fun k γ hγ y hy => by simp only [GlobalTheory.PeterssonCompare.pnorm_lact _ (hsf k) hγ hy])
    (fun k b hb y hy => by simp only [FrameDegreeData.pnorm_rmul _ _ _ (hsf k).2.1 y hy b hb])
  rw [← this]
  congr 1
  unfold petE
  have e : eLpNorm (fun q => ptN (modelWt (U σ) G) (rdU (U σ) f) (dict σ (Quotient.out q))) 2 (muQ1 (D.sp.W j)) ^ 2 =
      ∫⁻ q, ‖ptN (modelWt (U σ) G) (rdU (U σ) f) (dict σ (Quotient.out q))‖ₑ ^ 2 ∂(muQ1 (D.sp.W j)) := by
    have := eLpNorm_nnreal_pow_eq_lintegral (p := 2) (μ := muQ1 (D.sp.W j))
      (f := fun q => ptN (modelWt (U σ) G) (rdU (U σ) f) (dict σ (Quotient.out q))) two_ne_zero
    simpa using this
  rw [e]
  refine lintegral_congr fun q => ?_
  have hnn : 0 ≤ ptN (modelWt (U σ) G) (rdU (U σ) f) (dict σ (Quotient.out q)) := by
    unfold ptN Data.pnorm
    positivity
  rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg hnn, ← ENNReal.ofReal_pow hnn]
  rfl

set_option maxHeartbeats 1600000 in

theorem petE_pull_good : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → Even n → ∀ (f g : _), f ∈ cuspW Xo c U (wtZ a n) → g ∈ cuspW d.Xo₂ d.c₂ U₂ (wtZ a n) → Pull d f g → ∀ τ : d.c₂.F →+* ℂ, GoodEmb d.c₂ τ →
    petE (D.sp.W j) (dict₂ τ) (muQ1 (D.sp.W j)) (modelWt (U₂ τ) (wtZ a n)) (rdU (U₂ τ) g) =
    petE (D.sp.W j) (dict (τ.comp (d.eF : c.F →+* d.c₂.F))) (muQ1 (D.sp.W j)) (modelWt (U (τ.comp (d.eF : c.F →+* d.c₂.F))) (wtZ a n)) (rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f) := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd a n ha hn f g hf hg hp τ hτ
  have hσ : GoodEmb c (τ.comp (d.eF : c.F →+* d.c₂.F)) := (goodEmb_comp_eF D d τ).2 hτ
  obtain ⟨π, δ, N, hN, hcomp, hfib, t, ht1, hrel⟩ := GlobalTheory.T.levelCover_complexModels_components_isometries_degree D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd τ hτ
  have hex : ∀ (X : Data D.host.E D.R.r), ∃ x0, IsOrth X x0 ∧ ∃ FF, IsFundSet X x0 FF := fun X => by
    choose P _ hG using X.signature
    exact ⟨fun τ => P τ, fun τ => hG τ, GlobalTheory.MetricWeightTest.exists_fundSet_orth X (fun τ => hG τ)⟩
  choose x0 hx0 FF hFF using fun k => hex ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k)
  choose x0₂ hx0₂ FF₂ hFF₂ using fun k => hex ((U₂ τ).X k)
  obtain ⟨hS0, hST, h1⟩ := petE_sq_mul_vol D j H Dw l Xo c U dict hL (τ.comp (d.eF : c.F →+* d.c₂.F)) hσ (wtZ a n) f hf x0 FF (fun k => ⟨hx0 k, hFF k⟩)
  obtain ⟨hS0₂, hST₂, h2⟩ := petE_sq_mul_vol D j H Dw d.l₂ d.Xo₂ d.c₂ U₂ dict₂ hL₂ τ hτ (wtZ a n) g hg x0₂ FF₂
    (fun k => ⟨hx0₂ k, hFF₂ k⟩)
  have hΨ : ∀ k₂, ((U₂ τ).X k₂).Ψ = ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Ψ := fun k₂ => Finset.ext fun ρ =>
    (((hL₂.unf τ hτ).2.1 k₂).2 ρ).trans (((hL.unf (τ.comp (d.eF : c.F →+* d.c₂.F)) hσ).2.1 (π k₂)).2 ρ).symm
  have hp0 : ∀ k₂, ((U₂ τ).X k₂).p0 = ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).p0 := fun k₂ =>
    ((hL₂.unf τ hτ).2.1 k₂).1.trans ((hL.unf (τ.comp (d.eF : c.F →+* d.c₂.F)) hσ).2.1 (π k₂)).1.symm
  have hsf : ∀ k, ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k).IsSec (modelWt (U (τ.comp (d.eF : c.F →+* d.c₂.F))) (wtZ a n) k) (rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f k) := fun k =>
    GlobalTheory.PeterssonCompare.isSec_of_mem_holSub _ _ ((mem_cuspW.1 hf).2 (τ.comp (d.eF : c.F →+* d.c₂.F)) hσ) k
  have h0f : ∀ k, ∀ x ∉ ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k).dom, rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f k x = 0 := fun k x hx => dif_neg hx
  have h0g : ∀ k, ∀ x ∉ ((U₂ τ).X k).dom, rdU (U₂ τ) g k x = 0 := fun k x hx => dif_neg hx
  have hsecf : f ∈ sec Xo c a n := by
    have := cuspW_le_secZ (wtZ a n) hf
    rwa [GlobalTheory.AllWt.exZ_wtZ, secZ_nat] at this
  have hsecg : g ∈ sec d.Xo₂ d.c₂ a n := by
    have := cuspW_le_secZ (wtZ a n) hg
    rwa [GlobalTheory.AllWt.exZ_wtZ, secZ_nat] at this
  have hmeas : ∀ k, Measurable fun x => ENNReal.ofReal
      (((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k).pnorm (modelWt (U (τ.comp (d.eF : c.F →+* d.c₂.F))) (wtZ a n) k) (rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f k) x ^ 2) := fun k =>
    ENNReal.measurable_ofReal.comp
      ((GlobalTheory.PeterssonCompare.measurable_pnorm _ _ (hsf k).1.continuousOn (h0f k)).pow_const 2)
  have hcint : ∀ k₂, ∫⁻ z in FF₂ k₂, ENNReal.ofReal (((U₂ τ).X k₂).pnorm (modelWt (U₂ τ) (wtZ a n) k₂)
        (rdU (U₂ τ) g k₂) (cpt ((U₂ τ).X k₂) (x0₂ k₂) z) ^ 2) ∂(muF ((U₂ τ).X k₂) (x0₂ k₂)) =
      ((((U₂ τ).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ : ℝ≥0∞) *
        ∫⁻ z in FF (π k₂), ENNReal.ofReal (((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).pnorm (modelWt (U (τ.comp (d.eF : c.F →+* d.c₂.F))) (wtZ a n) (π k₂))
        (rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f (π k₂)) (cpt ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)) (x0 (π k₂)) z) ^ 2) ∂(muF ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)) (x0 (π k₂))) ∧
      muF ((U₂ τ).X k₂) (x0₂ k₂) (FF₂ k₂) =
      ((((U₂ τ).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ : ℝ≥0∞) *
        muF ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)) (x0 (π k₂)) (FF (π k₂)) := by
    intro k₂
    have hGm := (hcomp k₂).1
    have hu := (hcomp k₂).2.1
    have hle := (hcomp k₂).2.2.1
    have hidx := (hcomp k₂).2.2.2
    have hu' : ∀ v w, herm ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v)
        ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm v w := by
      rw [← hGm]; exact hu
    have hP := pnorm_lact_transport D.host.E D.R.r ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)) ((U₂ τ).X k₂) (hΨ k₂) (δ k₂) (modelWt (U (τ.comp (d.eF : c.F →+* d.c₂.F))) (wtZ a n) (π k₂))
        (modelWt (U₂ τ) (wtZ a n) k₂) (rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f (π k₂)) (rdU (U₂ τ) g k₂) (t k₂) n hGm (hp0 k₂) hu'
        (fun ρ h i => by simp only [modelWt, hp0 k₂, relab_eF])
        (ht1 k₂) (h0g k₂) (h0f (π k₂)) (fun x hx => by
          refine hrel a n ha f hsecf g hsecg hp k₂ x _ hx (fun ρ h₂ h₁ => ?_) hn
          show (δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map ρ * mat (hΨ k₂ ▸ x) ⟨ρ, h₁⟩ = _
          congr 1
          unfold mat
          rw [frame_tr (hΨ k₂) x ρ h₁ h₂])
    refine ⟨?_, ?_⟩
    · simp_rw [hP]
      exact GlobalTheory.T.lintegral_fundamentalSet_conj_finiteIndex_subgroup D.host.E D.R.r ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)) ((U₂ τ).X k₂) (hΨ k₂) (δ k₂) (x0 (π k₂)) (x0₂ k₂)
        (FF (π k₂)) (FF₂ k₂) _ hGm (hp0 k₂) hu' hle hidx (hx0 _) (hx0₂ _) (hFF _) (hFF₂ _) (hmeas _)
        (fun γ hγ x hx => by simp only [GlobalTheory.PeterssonCompare.pnorm_lact _ (hsf _) hγ hx])
        (fun b hb x hx => by simp only [FrameDegreeData.pnorm_rmul _ _ _ (hsf _).2.1 x hx b hb])
    · have := GlobalTheory.T.lintegral_fundamentalSet_conj_finiteIndex_subgroup D.host.E D.R.r ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)) ((U₂ τ).X k₂) (hΨ k₂) (δ k₂) (x0 (π k₂)) (x0₂ k₂)
        (FF (π k₂)) (FF₂ k₂) (fun _ => 1) hGm (hp0 k₂) hu' hle hidx (hx0 _) (hx0₂ _) (hFF _) (hFF₂ _)
        measurable_const (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
      simpa only [setLIntegral_one] using this
  set w : (U₂ τ).Comp → ℕ := fun k₂ =>
    (((U₂ τ).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ with hw
  have hfib' : ∀ k, ∑ᶠ i : {i // π i = k}, w i.1 = N := fun k => by
    rw [← hfib k]
    exact finsum_congr fun i => by simp only [hw, i.2]
  have hA := sum_mul_fibre π w N (fun k => ∫⁻ z in FF k, ENNReal.ofReal (((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k).pnorm (modelWt (U (τ.comp (d.eF : c.F →+* d.c₂.F))) (wtZ a n) k)
        (rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f k) (cpt ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k) (x0 k) z) ^ 2) ∂(muF ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k) (x0 k))) hfib'
  have hB := sum_mul_fibre π w N (fun k => muF ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k) (x0 k) (FF k)) hfib'
  simp only [hw] at hA hB
  have e1 := h2
  simp only [fun k₂ => (hcint k₂).1, fun k₂ => (hcint k₂).2] at e1
  rw [hA, hB, ← h1] at e1
  have hNS0 : (N : ℝ≥0∞) * ∑ k, muF ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k) (x0 k) (FF k) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hN.ne') hS0
  have hNST : (N : ℝ≥0∞) * ∑ k, muF ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k) (x0 k) (FF k) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) hST
  have e2 : petE (D.sp.W j) (dict₂ τ) (muQ1 (D.sp.W j)) (modelWt (U₂ τ) (wtZ a n)) (rdU (U₂ τ) g) ^ 2 =
      petE (D.sp.W j) (dict (τ.comp (d.eF : c.F →+* d.c₂.F))) (muQ1 (D.sp.W j)) (modelWt (U (τ.comp (d.eF : c.F →+* d.c₂.F))) (wtZ a n)) (rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f) ^ 2 := by
    rw [← ENNReal.mul_left_inj hNS0 hNST, e1]
    ring
  have e3 : ∀ x y : ℝ≥0∞, x ^ 2 = y ^ 2 → x = y := fun x y h => by
    have h' : x ^ (2:ℝ) = y ^ (2:ℝ) := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, ENNReal.rpow_natCast]; exact h
    exact ENNReal.rpow_left_injective two_ne_zero h'
  exact e3 _ _ e2

theorem levPull_normW : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → Even n → ∀ (f : cuspW Xo c U (wtZ a n)) (g : cuspW d.Xo₂ d.c₂ U₂ (wtZ a n)), Pull d (f : Rul Xo c) (g : Rul d.Xo₂ d.c₂) → ∀ σ₂ : d.c₂.F →+* ℂ, normW U₂ (xiR D) (fun _ => D.sp.W j) dict₂ (wtZ a n) σ₂ g = normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) (σ₂.comp (d.eF : c.F →+* d.c₂.F)) f := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd a n ha hn f g hp σ₂
  simp only [normW, petW, petAt]
  rw [goodOf_eF D d σ₂, petE_pull_good D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd a n ha hn _ _ f.2 g.2 hp _
    (goodEmb_goodOf _ _)]

end GlobalTheory.LevPullNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardClassEqZeroOfZeroDenseOpenAndSectionOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem bijective_appLE_ι {Z : Scheme.{0}} (O W : Z.Opens) (hW : W ≤ O) (W' : O.toScheme.Opens)
    (h : W' = O.ι ⁻¹ᵁ W) : Function.Bijective (O.ι.appLE W W' h.le) := by
  subst h
  have : IsIso (O.ι.app W) := Scheme.Hom.isIso_app _ _ (by simpa using hW)
  rw [← Scheme.Hom.app_eq_appLE]
  exact ConcreteCategory.bijective_of_isIso _

theorem eq_zero_of_pull_eq_zero : ∀ (T Z : Scheme.{0}) [IsIntegral T] [IsLocallyNoetherian T], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → ∀ (U : T.Opens), (U : Set T).Nonempty → ∀ (p : Z ⟶ T) (O : Z.Opens) (e : T ⟶ O.toScheme), Smooth (O.ι ≫ p) → GeometricallyIntegral (O.ι ≫ p) → e ≫ O.ι ≫ p = 𝟙 _ → O ⊔ p ⁻¹ᵁ U = ⊤ → ∀ c : Pic Z, GlobalTheory.CechPic.pull O.ι c = 0 → GlobalTheory.CechPic.pull (p ⁻¹ᵁ U).ι c = 0 → c = 0 := by
  intro T Z _ _ hT U hU p O e hs hg he hcov
  refine GlobalTheory.T.cechPicard_eq_zero_of_twoOpen_cover_units_split Z O (p ⁻¹ᵁ U) hcov fun F => ?_
  have h1 : (O.ι ≫ p) ⁻¹ᵁ U = O.ι ⁻¹ᵁ (O ⊓ p ⁻¹ᵁ U) := by
    rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq, Scheme.Hom.comp_preimage]
  have h2 : (⊤ : O.toScheme.Opens) = O.ι ⁻¹ᵁ O := by simp
  have b1 := bijective_appLE_ι O (O ⊓ p ⁻¹ᵁ U) inf_le_left _ h1
  have b2 := bijective_appLE_ι O O le_rfl _ h2
  obtain ⟨G, w, hGw⟩ := GlobalTheory.T.unit_above_dense_open_eq_global_mul_pullback T O hT U hU (O.ι ≫ p) e hs hg he
    (Units.map (O.ι.appLE (O ⊓ p ⁻¹ᵁ U) _ h1.le).hom.toMonoidHom F)
  let ε := RingEquiv.ofBijective (O.ι.appLE O ⊤ h2.le).hom b2
  refine ⟨Units.map ε.symm.toMonoidHom G, pullU p U w, ?_⟩
  apply Units.ext
  apply b1.1
  have hv := congrArg Units.val hGw
  have hG : (O.ι.appLE O ⊤ h2.le).hom (ε.symm G) = G := ε.apply_symm_apply _
  change (O.ι.appLE (O ⊓ p ⁻¹ᵁ U) _ h1.le).hom F =
    O.toScheme.presheaf.map (homOfLE le_top).op (G : Γ(O, ⊤)) * (O.ι ≫ p).app U (w : Γ(T, U)) at hv
  change (O.ι.appLE (O ⊓ p ⁻¹ᵁ U) _ h1.le).hom F = (O.ι.appLE (O ⊓ p ⁻¹ᵁ U) _ h1.le).hom
    (Z.presheaf.map (homOfLE inf_le_left).op (ε.symm G) *
      Z.presheaf.map (homOfLE inf_le_right).op (p.app U (w : Γ(T, U))))
  rw [hv, map_mul, ← hG]
  congr 1
  · rw [hG]
    conv_lhs => rw [← hG]
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  · rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.appLE_comp_appLE]

end GlobalTheory.PicGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardClassLocallyTrivialOfTrivialSmoothNormalCo
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocalTriv

theorem hartogs_chart : ∀ (Y : Scheme.{0}) (V : Y.Opens) (hV : IsAffineOpen V), IsLocallyNoetherian (Sp Γ(Y, V)) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y → ∀ U : (Sp Γ(Y, V)).Opens, (∀ p : Sp Γ(Y, V), ringKrullDim (Y.presheaf.stalk (hV.fromSpec p)) ≤ 1 → p ∈ U) → Function.Bijective ((Sp Γ(Y, V)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom := by
  intro Y V hV hLN hY U hU
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp Γ(Y, V)) := fun p => by
    let e := (asIso (hV.fromSpec.stalkMap p)).commRingCatIsoToRingEquiv
    obtain ⟨h1, h2⟩ := hY (hV.fromSpec p)
    haveI := h1
    haveI := h2
    haveI : IsDomain ((Sp Γ(Y, V)).presheaf.stalk p) := MulEquiv.isDomain _ e.symm.toMulEquiv
    exact ⟨inferInstance, IsIntegrallyClosed.of_equiv e⟩
  have hb := ((GlobalTheory.extension_over_codim_two (Sp Γ(Y, V)) hN).1 U fun p hp => hU p (by
    let e := (asIso (hV.fromSpec.stalkMap p)).commRingCatIsoToRingEquiv
    exact (ringKrullDim_eq_of_ringEquiv e).trans_le hp)).1 ⊤
  have key : ∀ (V' : (Sp Γ(Y, V)).Opens) (_ : V' = U) (h' : V' ≤ ⊤),
      Function.Bijective (resG (Sp Γ(Y, V)) h') →
        Function.Bijective ((Sp Γ(Y, V)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom := by
    rintro _ rfl _ h
    exact h
  exact key _ (top_inf_eq U) _ hb

theorem factor_locus : ∀ (X T : Scheme.{0}) (W : X.Opens) (c : Pic W.toScheme) (j : T ⟶ X) [IsOpenImmersion j] (V : (j ⁻¹ᵁ W).toScheme.Opens), IsLocus (GlobalTheory.CechPic.pull (j ∣_ W) c) V → ∀ N : X.Opens, (∀ w ∈ N ⊓ W, ∃ z ∈ V, j ((j ⁻¹ᵁ W).ι z) = w) → GlobalTheory.CechPic.pull (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) c = 0 := by
  intro X T W c j _ V hV N hN
  have hz : ∀ z : (N ⊓ W).toScheme, ∃ z' ∈ V, (j ∣_ W) z' = X.homOfLE (inf_le_right : N ⊓ W ≤ W) z := by
    intro z
    obtain ⟨z', hz'V, hz'⟩ := hN ((N ⊓ W).ι z) z.2
    refine ⟨z', hz'V, W.ι.isOpenEmbedding.injective ?_⟩
    have e1 : W.ι ((j ∣_ W) z') = j ((j ⁻¹ᵁ W).ι z') :=
      congrArg (fun f => f.base z') (morphismRestrict_ι j W)
    have e2 : W.ι (X.homOfLE (inf_le_right : N ⊓ W ≤ W) z) = (N ⊓ W).ι z :=
      congrArg (fun f => f.base z) (X.homOfLE_ι (inf_le_right : N ⊓ W ≤ W))
    exact e1.trans (hz'.trans e2.symm)
  let k := IsOpenImmersion.lift (j ∣_ W) (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) (by
    rintro _ ⟨z, rfl⟩
    obtain ⟨z', -, h⟩ := hz z
    exact ⟨z', h⟩)
  have hk : k ≫ (j ∣_ W) = X.homOfLE (inf_le_right : N ⊓ W ≤ W) := IsOpenImmersion.lift_fac _ _ _
  rw [← hk, pull_comp]
  refine GlobalTheory.T.nonvanishingLocus_pullback_and_vanish_into_locus.2 _ _ k _ V hV fun z => ?_
  obtain ⟨z', hz'V, h⟩ := hz z
  have hkz : k z = z' := (j ∣_ W).isOpenEmbedding.injective (by
    have e : (j ∣_ W) (k z) = X.homOfLE (inf_le_right : N ⊓ W ≤ W) z := congrArg (fun f => f.base z) hk
    exact e.trans h.symm)
  rw [hkz]
  exact hz'V

theorem locally_trivial : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian X] (q : Y ⟶ X) [Smooth q] [Surjective q], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y → ∀ W : X.Opens, (∀ z : Y, ringKrullDim ((Y).presheaf.stalk z) ≤ 1 → z ∈ q ⁻¹ᵁ W) → ∀ c : Pic W.toScheme, GlobalTheory.CechPic.pull (q ∣_ W) c = 0 → ∀ x : X, ∃ N : X.Opens, x ∈ N ∧ GlobalTheory.CechPic.pull (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) c = 0 := by
  intro X Y _ q _ _ hY W hW c hc x
  obtain ⟨y, rfl⟩ := q.surjective x
  obtain ⟨N0, hN0, hx0, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show q y ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨N1, hN1, hy1, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (show y ∈ q ⁻¹ᵁ N0 from hx0)
  have hA0 : IsAffineOpen N0 := hN0
  have hA1 : IsAffineOpen N1 := hN1
  have hB : IsNoetherianRing Γ(X, N0) := IsLocallyNoetherian.component_noetherian ⟨N0, hN0⟩
  let g : Γ(X, N0) →+* Γ(Y, N1) := (q.appLE N0 N1 hle).hom
  have hg : g.Flat := HasRingHomProperty.appLE @Flat q inferInstance ⟨N0, hN0⟩ ⟨N1, hN1⟩ hle
  have hsq : spMap g ≫ hA0.fromSpec = hA1.fromSpec ≫ q := IsAffineOpen.SpecMap_appLE_fromSpec q hA0 hA1 hle
  have hpt : ∀ p, hA0.fromSpec (spMap g p) = q (hA1.fromSpec p) := fun p => by
    have := congrArg (fun f => f.base p) hsq
    simpa using this
  have hLN : IsLocallyNoetherian (Sp Γ(Y, N1)) := LocallyOfFiniteType.isLocallyNoetherian (hA1.fromSpec ≫ q)
  let W0 : (Sp Γ(X, N0)).Opens := hA0.fromSpec ⁻¹ᵁ W
  have hbij := hartogs_chart Y N1 hA1 hLN hY (spMap g ⁻¹ᵁ W0) fun p hp => by
    show hA0.fromSpec (spMap g p) ∈ W
    rw [hpt]
    exact hW _ hp
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  let M := L.pull (hA0.fromSpec ∣_ W)
  have hM : M.IsLB := pull_isLB hL _
  have hk : spMap g ⁻¹ᵁ W0 ≤ hA1.fromSpec ⁻¹ᵁ (q ⁻¹ᵁ W) := fun p hp => by
    show q (hA1.fromSpec p) ∈ W
    rw [← hpt]
    exact hp
  have hcomp : (spMap g ∣_ W0) ≫ (hA0.fromSpec ∣_ W) = hA1.fromSpec.resLE (q ⁻¹ᵁ W) _ hk ≫ (q ∣_ W) := by
    rw [← cancel_mono W.ι]
    simp only [Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc]
    exact (morphismRestrict_ι_assoc (spMap g) W0 hA0.fromSpec).trans (congrArg _ hsq)
  have htriv : Triv (M.pull (spMap g ∣_ W0)) := by
    have h0 : cls _ (pull_isLB hM (spMap g ∣_ W0)) = 0 := by
      rw [cls_pull hM, cls_pull hL, ← pull_comp, hcomp, pull_comp, hc, map_zero]
    exact (cls_eq_zero_iff _).1 h0
  obtain ⟨y1, rfl⟩ : y ∈ Set.range hA1.fromSpec := hA1.range_fromSpec ▸ hy1
  obtain ⟨s, D, hyD, hD⟩ := GlobalTheory.T.exists_nowhereZero_section_near_of_flat_trivial Γ(X, N0) Γ(Y, N1) g hg W0 hbij M hM htriv y1
  let N : X.Opens := ⟨q '' (hA1.fromSpec '' D), q.isOpenMap _ (hA1.fromSpec.isOpenEmbedding.isOpenMap _ D.isOpen)⟩
  refine ⟨N, ⟨_, ⟨y1, hyD, rfl⟩, rfl⟩, ?_⟩
  refine factor_locus X _ W _ hA0.fromSpec (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s) ⟨M, hM, s, cls_pull hL _ hM, rfl⟩ N ?_
  rintro w ⟨⟨_, ⟨d, hd, rfl⟩, rfl⟩, hwW⟩
  have hdW : d ∈ spMap g ⁻¹ᵁ W0 := by
    show hA0.fromSpec (spMap g d) ∈ W
    rw [hpt]
    exact hwW
  refine ⟨(spMap g ∣_ W0) ⟨d, hdW⟩, hD ⟨d, hdW⟩ hd, ?_⟩
  have e : W0.ι ((spMap g ∣_ W0) ⟨d, hdW⟩) = spMap g d :=
    congrArg (fun f => f.base ⟨d, hdW⟩) (morphismRestrict_ι (spMap g) W0)
  exact (congrArg hA0.fromSpec.base e).trans (hpt d)

end GlobalTheory.LocalTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedChartsAffineOfSpectraStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pinched_charts_affine_of_spectra : (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (C' D E : Type) [CommRing C'] [CommRing D] [CommRing E] (φ : R' →+* C') (δ : R ⧸ c →+* D) (π : C' →+* E) (ψ : D →+* E), φ.Smooth → δ.IsStandardSmoothOfRelativeDimension g → IsPushout (CommRingCat.ofHom (φ.comp (algebraMap R R'))) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom π) (CommRingCat.ofHom (ψ.comp δ)) → IsPushout (CommRingCat.ofHom (δ.comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom (algebraMap R R')) (CommRingCat.ofHom ψ) (CommRingCat.ofHom (π.comp φ)) → ∀ y : Sp E, GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) (spMap φ) (spMap δ) (spMap π) (spMap ψ) (spMap π y)) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (B' C Y : Scheme.{0}) (b' : B' ⟶ Sp R') (e : C ⟶ Sp (R ⧸ c)) (i : Y ⟶ B') (q : Y ⟶ C), IsAffine B' → IsAffine C → Smooth b' → e.appTop.hom.IsStandardSmoothOfRelativeDimension g → IsPullback i (q ≫ e) (b' ≫ spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) → IsPullback q (i ≫ b') (e ≫ spMap (Ideal.Quotient.mk c)) (spMap (algebraMap R R')) → ∀ y : Y, GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) b' e i q (i y) := by
  first | exact @GlobalTheory.Pinch.Aff.pinched_affine_of_spec | exact GlobalTheory.Pinch.Aff.pinched_affine_of_spec | (intros; apply GlobalTheory.Pinch.Aff.pinched_affine_of_spec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedChartsRestrictMatchingOpensStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pinched_charts_restrict_matching_opens : ∀ (g : ℕ) (S S' Z B' C Y : Scheme.{0}) (s' : S' ⟶ S) (z : Z ⟶ S) (b' : B' ⟶ S') (e : C ⟶ Z) (i : Y ⟶ B') (q : Y ⟶ C), IsPullback i (q ≫ e) (b' ≫ s') z → IsPullback q (i ≫ b') (e ≫ z) s' → ∀ (V' : B'.Opens) (V : C.Opens), i ⁻¹ᵁ V' = q ⁻¹ᵁ V → ∃ (q₀ : (i ⁻¹ᵁ V').toScheme ⟶ V.toScheme), IsPullback (i ∣_ V') (q₀ ≫ V.ι ≫ e) ((V'.ι ≫ b') ≫ s') z ∧ IsPullback q₀ ((i ∣_ V') ≫ V'.ι ≫ b') ((V.ι ≫ e) ≫ z) s' ∧ ∀ x : V'.toScheme, GlobalTheory.Pinch.Pinched g s' z (V'.ι ≫ b') (V.ι ≫ e) (i ∣_ V') q₀ x → GlobalTheory.Pinch.Pinched g s' z b' e i q (V'.ι x) := by
  first | exact @GlobalTheory.Pinch.restrict_pinched | exact GlobalTheory.Pinch.restrict_pinched | (intros; apply GlobalTheory.Pinch.restrict_pinched <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedFunctionsGlueAffineFlatBaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pinched_functions_glue_affine_flat_baseChange : ∀ (S : Scheme.{0}) (E X X' Z Z' : Over S) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), Flat E.hom → i' ≫ p = p' ≫ i → IsPullback i'.left p'.left p.left i.left → IsAffineHom p.left → IsClosedImmersion i.left → GlobalTheory.PinchLift.Glues p.left i.left i'.left p'.left → ∀ (V : X.left.Opens) (W : (E ⊗ X).left.Opens), IsAffineOpen V → IsAffineOpen W → W ≤ (snd E X).left ⁻¹ᵁ V → ∀ (a : Γ((E ⊗ X').left, (E ◁ p).left ⁻¹ᵁ W)) (b : Γ((E ⊗ Z).left, (E ◁ i).left ⁻¹ᵁ W)), ((E ◁ i').left.appLE ((E ◁ p).left ⁻¹ᵁ W) ((E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W)) inf_le_left).hom a = ((E ◁ p').left.appLE ((E ◁ i).left ⁻¹ᵁ W) ((E ◁ i').left ⁻¹ᵁ ((E ◁ p).left ⁻¹ᵁ W) ⊓ (E ◁ p').left ⁻¹ᵁ ((E ◁ i).left ⁻¹ᵁ W)) inf_le_right).hom b → ∃! s : Γ((E ⊗ X).left, W), ((E ◁ p).left.app W).hom s = a ∧ ((E ◁ i).left.app W).hom s = b := by
  first | exact @GlobalTheory.PinchLift.FlatBC.glues_affine_of_flat_baseChange | exact GlobalTheory.PinchLift.FlatBC.glues_affine_of_flat_baseChange | (intros; apply GlobalTheory.PinchLift.FlatBC.glues_affine_of_flat_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointOnModelPullbackCompatibleStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.point_on_model_pullback_compatible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype)
    (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
    (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ →
    ∀ (X : LieG P.Gt) (u0 : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left), ITie P π X u0 →
    ∃ w : Sp (DualNumber ℂ_[p]) ⟶ Y.oF.t.G.left,
      w ≫ Y.m.φ = spMap (dualMap (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ u0 ∧
      w ≫ Y.oF.t.G.hom = spMap (algebraMap ℂ_[p] (DualNumber ℂ_[p])) ≫ yy ∧
      spMap (TrivSqZeroExt.fstHom ℂ_[p] ℂ_[p] ℂ_[p]).toRingHom ≫ w = (1 : Over.mk yy ⟶ Y.oF.t.G).left ∧
      LieTie P ψ X w := by
  first | exact @GlobalTheory.FlatModel.LiftW.liftW | exact GlobalTheory.FlatModel.LiftW.liftW | (intros; apply GlobalTheory.FlatModel.LiftW.liftW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolAVDimEqOfGrpPullbackField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem polAV_g_eq_of_isGrpPullback : ∀ (K : Type) [Field K] (T : Scheme.{0}) (P : PolAV T) (P₀ : PolAV (Sp K)) (f : Sp K ⟶ T) (a : P₀.A.left ⟶ P.A.left), IsGrpPullback P₀.A P.A f a → P₀.g = P.g := by
  intro K _ T P P₀ f a h
  have h2 : SmoothOfRelativeDimension P.g P₀.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
  exact ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ P₀.smoothDim h2 (eSec P₀.A (default : PrimeSpectrum K))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialTopSelfIntersectionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_top_self_intersection : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (κ : Type) [Field κ] (Z : Scheme.{0}) [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ Z) → ∀ (ι : Type) [Fintype ι] (D : ℕ), Fintype.card ι = D → topologicalKrullDim Z ≤ D → ∀ (i : Z ⟶ X) (N : ι → HermLB p), pol (fun n : ι → ℤ => (topSelfIntersection κ ((comb N n).B.pull i) D : ℝ)) = D.factorial * (interNum κ (structureModule Z) (fun a => (N a).B.pull i) : ℝ) := by
  first | exact @GlobalTheory.FibreProj.pol_topSelf_comb_pull | exact GlobalTheory.FibreProj.pol_topSelf_comb_pull | (intros; apply GlobalTheory.FibreProj.pol_topSelf_comb_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerOfInducedBundleGeneratedStatement
section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.power_of_induced_bundle_generated : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (q : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L q cf → Y.ample A.D → ∃ m : ℕ, 1 ≤ m ∧ GlobalTheory.IsGenerated ((L.pow m).B.pull M.j) := by
  first | exact @GlobalTheory.TrueGeo.InducedGen.exists_isGenerated_pow | exact GlobalTheory.TrueGeo.InducedGen.exists_isGenerated_pow | (intros; apply GlobalTheory.TrueGeo.InducedGen.exists_isGenerated_pow <;> assumption)
end

