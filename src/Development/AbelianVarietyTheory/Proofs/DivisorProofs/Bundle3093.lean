import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0774
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0798
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3031
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2986
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0095
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2572
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgIdemBinv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2617
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTensorPosDefFormPositive
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisChangeTorsion
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.HtGen.DlogClose

theorem dlog_sub_norm_lt_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (p : ℕ) [Fact p.Prime] (x : Sp ↥(intO ℂ_[p]) ⟶ X) (g g' : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)) (e' : Fin g' → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)), IsTanBasis t x e → IsTanBasis t x e' → ∀ (c : TorsChar t x (p ^ 2)) (h : Fin g → ↥(intO ℂ_[p])) (h' : Fin g' → ↥(intO ℂ_[p])), DlogIs t p 2 c e h → DlogIs t p 2 c e' h' → ∀ (a : Fin g → ℂ_[p]) (a' : Fin g' → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left), IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) a w → IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e' i) a' w → w ∈ latHT t p (spMap (intO ℂ_[p]).subtype ≫ x) → ‖∑ i, (h i : ℂ_[p]) * a i - ∑ i, (h' i : ℂ_[p]) * a' i‖ < 1 := by
  intro E _ _ _ H X _ t hX p hp x g g' e e' he he' c h h' hD hD' a a' w hw hw' hL
  have hn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  obtain ⟨x', hx', vO, hv, hs⟩ := GlobalTheory.ShFam.Pad.HTBound.htBound E H X t p ℂ_[p] hn x
    (fun x' hx' => GlobalTheory.LineNorm.WedgeMax.ext_intO hX x x' hx') w hL p (by
      rw [hn, ← Real.rpow_neg_one]
      refine Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg ?_)
      rw [div_le_one (by linarith)]
      linarith)
  obtain rfl := GlobalTheory.LineNorm.WedgeMax.ext_intO hX x x' hx'
  obtain ⟨b, hbv, hb⟩ := GlobalTheory.HTLevel.coords he hw _ hv hs
  obtain ⟨b', hbv', hb'⟩ := GlobalTheory.HTLevel.coords he' hw' _ hv hs
  obtain ⟨u, hu⟩ := GlobalTheory.HTLevel.red_ex (Ideal.span {(p : ↥(intO ℂ_[p])) ^ 2}) hv
  have h1 := hD b vO hbv u hu
  have h2 := hD' b' vO hbv' u hu
  rw [h1, Ideal.Quotient.eq] at h2
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h2
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have h3 : ∑ i, (h i : ℂ_[p]) * a i - ∑ i, (h' i : ℂ_[p]) * a' i = (r : ℂ_[p]) * p := by
    apply mul_left_cancel₀ hp0
    have := congrArg (intO ℂ_[p]).subtype hr
    simp only [map_mul, map_pow, map_natCast, map_sum, map_sub, Subring.subtype_apply, hb, hb'] at this
    have e1 : ∑ i, (h i : ℂ_[p]) * ((p : ℂ_[p]) * a i) = (p : ℂ_[p]) * ∑ i, (h i : ℂ_[p]) * a i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i, (h' i : ℂ_[p]) * ((p : ℂ_[p]) * a' i) = (p : ℂ_[p]) * ∑ i, (h' i : ℂ_[p]) * a' i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2] at this
    linear_combination (-1 : ℂ_[p]) * this
  rw [h3, norm_mul, hn]
  have hr1 : ‖(r : ℂ_[p])‖ ≤ 1 := r.2
  have hpi : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  calc ‖(r : ℂ_[p])‖ * (p : ℝ)⁻¹ ≤ 1 * (p : ℝ)⁻¹ := by gcongr
    _ < 1 := by rw [_root_.one_mul]; exact hpi

end GlobalTheory.HtGen.DlogClose
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTorsionChars
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj

namespace GlobalTheory.HTLevelSq

theorem mem_latHT_iff_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (p : ℕ) [Fact p.Prime] (x : Sp ↥(intO ℂ_[p]) ⟶ X) (g : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO ℂ_[p])) ⟶ t.G.left)), IsTanBasis t x e → ∀ (N : ℕ) (c : Fin N → TorsChar t x (p ^ 2)) (h : Fin N → Fin g → ↥(intO ℂ_[p])), (∀ c' : TorsChar t x (p ^ 2), ∃ j, Agree c' (c j)) → (∀ j, DlogIs t p 2 (c j) e (h j)) → ∀ (a : Fin g → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left), IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) a w → (w ∈ latHT t p (spMap (intO ℂ_[p]).subtype ≫ x) ↔ ∀ j, ‖∑ i, (h j i : ℂ_[p]) * a i‖ ≤ 1) ∧ (w ∈ latHT t p (spMap (intO ℂ_[p]).subtype ≫ x) → ∀ i, ‖(p : ℂ_[p]) * a i‖ ≤ 1) := by
  intro E _ _ _ H X _ t hX p hp x g e he N c h hAll hdl
  have hn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := PadicComplexHost.norm_p p
  have hx : ∀ x' : Sp ↥(intO ℂ_[p]) ⟶ X,
      spMap (intO ℂ_[p]).subtype ≫ x' = spMap (intO ℂ_[p]).subtype ≫ x → x' = x :=
    fun x' h' => GlobalTheory.LineNorm.WedgeMax.ext_intO hX x x' h'
  have hc1 : ∀ c₁ : TorsChar t x (p ^ 1), ∃ j, DlogIs t p 1 c₁ e (h j) := fun c₁ => by
    obtain ⟨c', hc'⟩ := GlobalTheory.T.torsionChar_extends_divisible_level E H X t ℂ_[p] x (p ^ 1) (p ^ 2) (pow_ne_zero _ hp.out.ne_zero)
      (pow_dvd_pow _ (by norm_num)) c₁
    obtain ⟨j, hj⟩ := hAll c'
    exact ⟨j, GlobalTheory.HTLevel.dlog_down (by norm_num) c' c₁ hc' he.1 (GlobalTheory.HTMap.dlog_congr he.1 hj (hdl j))⟩
  have hj1 : ∀ j, ∃ c₁ : TorsChar t x (p ^ 1), DlogIs t p 1 c₁ e (h j) := fun j =>
    ⟨GlobalTheory.HTLevel.res (pow_dvd_pow p (by norm_num : 1 ≤ 2)) (c j),
      GlobalTheory.HTLevel.dlog_down (by norm_num : 1 ≤ 2) (c j) (GlobalTheory.HTLevel.res (pow_dvd_pow p (by norm_num : 1 ≤ 2)) (c j))
        (fun _ _ _ _ _ _ => rfl) he.1 (hdl j)⟩
  have L1 := fun a w hw => GlobalTheory.HTLevel.mem_latHT_iff GlobalTheory.ShFam.Pad.HTBound.htBound E H X t p ℂ_[p] hn x hx g e he N h
    hc1 hj1 a w hw
  have heC := fun i => GlobalTheory.FactorDepth.isTanAtG_map t (intO ℂ_[p]).subtype (he.1 i)
  have step : ∀ (a : Fin g → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left),
      IsCombAtG t (spMap (intO ℂ_[p]).subtype ≫ x) (fun i => spMap (dualMap (intO ℂ_[p]).subtype) ≫ e i) a w →
      (∀ j, ‖∑ i, (h j i : ℂ_[p]) * a i‖ ≤ 1) → (∀ i, ‖(p : ℂ_[p]) ^ 2 * a i‖ ≤ 1) →
      w ∈ latHT t p (spMap (intO ℂ_[p]).subtype ≫ x) := by
    intro a w hw h1 h2
    let b : Fin g → ↥(intO ℂ_[p]) := fun i => ⟨(p : ℂ_[p]) ^ 2 * a i, h2 i⟩
    obtain ⟨vO, hv, hbv⟩ := Guard.exists_comb he.1 b
    refine ⟨x, rfl, 2, vO, hv, ?_, fun k c₀ w' hw' => ?_⟩
    · exact Guard.comb_unique heC (GlobalTheory.LatDRFree.comb_map t (intO ℂ_[p]).subtype hbv) (Guard.comb_smul heC hw _)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : Subsingleton (↥(intO ℂ_[p]) ⧸ Ideal.span {(p : ↥(intO ℂ_[p])) ^ 0}) := by
        rw [Ideal.Quotient.subsingleton_iff, pow_zero, Ideal.span_singleton_one]
      rw [Subsingleton.elim (TrivSqZeroExt.snd _) 0]
      exact Ideal.zero_mem _
    obtain ⟨j, D, hD, hδ⟩ : ∃ j, ∃ D : Fin g → ↥(intO ℂ_[p]), DlogIs t p k c₀ e D ∧
        ∀ i, D i - h j i ∈ Ideal.span {(p : ↥(intO ℂ_[p])) ^ 2} := by
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · obtain rfl : k = 1 := by omega
        obtain ⟨j, hj⟩ := hc1 c₀
        exact ⟨j, h j, hj, fun i => by simp⟩
      · obtain ⟨⟨D, hD⟩, -⟩ := GlobalTheory.T.exists_dlog_unique_modulo_p E H X t _ x p k c₀ g e he.1
        obtain ⟨j, hj⟩ := hAll (GlobalTheory.HTLevel.res (pow_dvd_pow p hk2) c₀)
        exact ⟨j, D, hD, (GlobalTheory.T.exists_dlog_unique_modulo_p E H X t _ x p 2 _ g e he.1).2 D (h j)
          (GlobalTheory.HTLevel.dlog_down hk2 c₀ (GlobalTheory.HTLevel.res (pow_dvd_pow p hk2) c₀) (fun _ _ _ _ _ _ => rfl) he.1 hD) (GlobalTheory.HTMap.dlog_congr he.1 hj (hdl j))⟩
    choose δ hδ using fun i => Ideal.mem_span_singleton'.1 (hδ i)
    let s : ↥(intO ℂ_[p]) := ⟨∑ i, (h j i : ℂ_[p]) * a i, h1 j⟩
    have h3 : ∑ i, D i * b i = (s + ∑ i, δ i * b i) * (p : ↥(intO ℂ_[p])) ^ 2 := by
      apply (intO ℂ_[p]).subtype_injective
      simp only [map_mul, map_pow, map_natCast, map_sum, map_add, Subring.subtype_apply, s, b]
      rw [← Finset.sum_add_distrib, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := congrArg (intO ℂ_[p]).subtype (hδ i)
      simp only [map_mul, map_pow, map_natCast, map_sub, Subring.subtype_apply] at this
      linear_combination (-(p : ℂ_[p]) ^ 2 * a i) * this
    rw [hD b vO hbv w' hw', h3, map_mul, map_pow, map_natCast]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  intro a w hw
  refine ⟨⟨fun hL => ((L1 a w hw).1 hL).1, fun hd => ?_⟩, fun hL => ((L1 a w hw).1 hL).2⟩
  by_cases hbig : ∀ i, ‖(p : ℂ_[p]) ^ 2 * a i‖ ≤ 1
  · exact step a w hw hd hbig
  exfalso
  push_neg at hbig
  obtain ⟨i₀, hi₀⟩ := hbig
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖a i‖) ⟨i₀, Finset.mem_univ _⟩
  have hai : 1 < ‖(p : ℂ_[p]) ^ 2 * a i‖ := by
    refine lt_of_lt_of_le hi₀ ?_
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hi i₀ (Finset.mem_univ _)) (norm_nonneg _)
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have ha0 : a i ≠ 0 := fun h0 => by rw [h0, mul_zero, norm_zero] at hai; linarith
  have hl1 : ‖((p : ℂ_[p]) ^ 2 * a i)⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hai.le
  have hlw := Guard.comb_smul heC hw ((p : ℂ_[p]) ^ 2 * a i)⁻¹
  have hd' : ∀ j, ‖∑ k, (h j k : ℂ_[p]) * (((p : ℂ_[p]) ^ 2 * a i)⁻¹ * a k)‖ ≤ 1 := fun j => by
    have e2 : ∑ k, (h j k : ℂ_[p]) * (((p : ℂ_[p]) ^ 2 * a i)⁻¹ * a k) =
        ((p : ℂ_[p]) ^ 2 * a i)⁻¹ * ∑ k, (h j k : ℂ_[p]) * a k := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [e2, norm_mul]
    exact mul_le_one₀ hl1 (norm_nonneg _) (hd j)
  have hb' : ∀ k, ‖(p : ℂ_[p]) ^ 2 * (((p : ℂ_[p]) ^ 2 * a i)⁻¹ * a k)‖ ≤ 1 := fun k => by
    have e3 : (p : ℂ_[p]) ^ 2 * (((p : ℂ_[p]) ^ 2 * a i)⁻¹ * a k) = a k / a i := by field_simp
    rw [e3, norm_div]
    exact div_le_one_of_le₀ (hi k (Finset.mem_univ _)) (norm_nonneg _)
  have hmem := step _ _ hlw hd' hb'
  have h4 := ((L1 _ _ hlw).1 hmem).2 i
  have e1 : (p : ℂ_[p]) * (((p : ℂ_[p]) ^ 2 * a i)⁻¹ * a i) = (p : ℂ_[p])⁻¹ := by field_simp
  rw [e1, norm_inv, hn, inv_inv] at h4
  have : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  linarith

end GlobalTheory.HTLevelSq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleMapCokerCardEqKerTorsionCardStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateModuleMap_coker_card_eq_kerTorsion_card : ∀ (l : ℕ) [Fact l.Prime] (M N : Type) [CommGroup M] [CommGroup N] (φ : M →* N), (∀ x : M, ∃ y, y ^ l = x) → Function.Surjective φ → Finite φ.ker → Function.Injective (Tate.map l φ) ∧ Nat.card (Tate l N ⧸ LinearMap.range (Tate.map l φ)) = Nat.card {x : M // φ x = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1} := by
  first | exact @GlobalTheory.tate_map_coker_card | exact GlobalTheory.tate_map_coker_card | (intros; apply GlobalTheory.tate_map_coker_card <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalBaseDataPullbackAlongMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum
noncomputable section

namespace GlobalTheory.PullFrom

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap]

theorem good_exists {X Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (z : Z) : ∃ J, Good L z J := by
  obtain ⟨J, hJ, -⟩ := exists_good L hL z (K := Empty) Empty.elim Empty.elim (fun a => a.elim) (fun k => k.elim)
  exact ⟨J, hJ⟩

private theorem sq_ext_lemma {S Z : Scheme.{0}} {G : Over S} {f g : Z ⟶ (G2 G).left}
    (h₁ : f ≫ (fst G G).left = g ≫ (fst G G).left) (h₂ : f ≫ (snd G G).left = g ≫ (snd G G).left) : f = g :=
  Over.tensorObj_ext _ _ h₁ h₂

theorem pullData_of_dataFrom : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)) (Q' : Data V) (e' : Q'.X ≃+ (Fin T.r → ℤ)), (∀ i, θ (s i) ≠ 0) → DataFrom T iw s ε n Q e → DataFrom T (θ.comp iw) (fun i => θ (s i)) ε n Q' e' → PullData Q θ Q' (e'.trans e.symm) := by
  intro o W _ _ _ T R V _ _ _ _ θ iw I _ s ε n Q e Q' e' hs hQ hQ'
  obtain ⟨β₀, β₀₂, w₀, hpb₀, hsq₀, hw₀, hc₀, hτ₀⟩ := hQ
  obtain ⟨β₁, β₁₂, w₁, hpb₁, hsq₁, hw₁, hc₁, hτ₁⟩ := hQ'
  have hcomp : spMap θ ≫ spMap iw = spMap (θ.comp iw) := (spMap_comp_ring iw θ).symm

  obtain ⟨β, β₂, hpb, hsq, hβ, hβ₂⟩ := GlobalTheory.T.exists_cancel_grpPullback_with_squares (Sp V) (Sp R) (Sp W) Q'.B Q.B T.B (spMap θ) (spMap iw)
    β₁ β₀ β₁₂ β₀₂ (hcomp ▸ hpb₁) hpb₀ hsq₁ hsq₀

  obtain ⟨w, hw, hrel⟩ := GlobalTheory.T.mumfordBundleIso_cancel_values_mul (Sp V) (Sp R) (Sp W) Q'.B Q.B T.B Q'.M.L Q.M.L T.M.L Q'.M.isLB Q.M.isLB
    T.M.isLB β₂ β₀₂ β₁₂ hβ₂ w₀ hw₀ w₁ hw₁

  have hcc : ∀ a, (Q'.c a).left ≫ β = spMap θ ≫ (Q.c ((e'.trans e.symm) a)).left := by
    intro a
    apply hpb₀.1.hom_ext
    · simp only [Category.assoc, hβ, hc₁, hc₀, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
      rw [← hcomp, Category.assoc]
    · simp only [Category.assoc, hpb.1.w]
      simp

  have hsqT : ∀ a b : Q.X, (lift (Q.c a) (Q.c b)).left ≫ β₀₂ =
      spMap iw ≫ (lift (T.c₀ ((n : ℤ) • e a)) (T.c₀ ((n : ℤ) • e b))).left := by
    intro a b
    apply sq_ext_lemma
    · rw [Category.assoc, hsq₀.1, ← Category.assoc, ← Over.comp_left, lift_fst, hc₀, Category.assoc,
        ← Over.comp_left, lift_fst]
    · rw [Category.assoc, hsq₀.2, ← Category.assoc, ← Over.comp_left, lift_snd, hc₀, Category.assoc,
        ← Over.comp_left, lift_snd]
  refine ⟨β, β₂, w, hpb, hsq, hw, hcc, ?_⟩
  intro a b
  set a₀ := (e'.trans e.symm) a with ha₀def
  set b₀ := (e'.trans e.symm) b with hb₀def
  have ha₀ : e a₀ = e' a := by simp [a₀]
  have hb₀ : e b₀ = e' b := by simp [b₀]

  have hsqQ : (lift (toUnit (TK V) ≫ Q'.c a) (toUnit (TK V) ≫ Q'.c b)).left ≫ β₂ =
      ((TK V).hom ≫ spMap θ) ≫ (lift (Q.c a₀) (Q.c b₀)).left := by
    have h₁ : (lift (Q.c a₀) (Q.c b₀)).left ≫ (fst Q.B Q.B).left = (Q.c a₀).left := by
      rw [← Over.comp_left, lift_fst]
    have h₂ : (lift (Q.c a₀) (Q.c b₀)).left ≫ (snd Q.B Q.B).left = (Q.c b₀).left := by
      rw [← Over.comp_left, lift_snd]
    apply sq_ext_lemma
    · rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.comp_left, Category.assoc,
        hcc, Category.assoc, Category.assoc, h₁]
      rfl
    · rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc,
        hcc, Category.assoc, Category.assoc, h₂]
      rfl
  obtain ⟨k₀, hk₀, hv₀⟩ := hτ₀ a₀ b₀
  obtain ⟨k₁, hk₁, hv₁⟩ := hτ₁ a b
  obtain ⟨x, y, hy, hxy, hxy'⟩ :=
    GlobalTheory.LaurentFrac.exists_frac R V θ s (fun i => (n : ℤ) * ε i (e' a) (e' b)) hs

  obtain ⟨u, hu, hvu⟩ := GlobalTheory.T.exists_generator_transport_mumfordBundleIso (Sp R) (Sp W) Q.B T.B Q.M.L T.M.L Q.M.isLB T.M.isLB β₀₂ w₀ hw₀
    (𝟙_ (Over (Sp R))) (𝟙_ (Over (Sp W))) (Q.c a₀) (Q.c b₀) (T.c₀ ((n : ℤ) • e a₀))
    (T.c₀ ((n : ℤ) • e b₀)) (spMap iw) (hsqT a₀ b₀) (T.τ₀ _ _) (T.τ₀_gen _ _)
  refine ⟨u, x, y, k₀, k₁, hu, hy, ?_, ?_, ?_, ?_⟩
  · rw [hk₀, ha₀, hb₀]
    exact hxy
  · rw [hk₁]
    exact hxy'
  · intro z J hJ
    obtain ⟨J₀, hJ₀⟩ := good_exists T.M.isLB z
    have hl : (toUnit (TK R)).left ≫ (lift (Q.c a₀) (Q.c b₀)).left =
        (lift (toUnit (TK R) ≫ Q.c a₀) (toUnit (TK R) ≫ Q.c b₀)).left := by
      rw [← Over.comp_left, comp_lift]
    rw [hv₀ z J₀ J hJ₀ hJ, hvu _ _ z J₀ J hJ₀ hJ, hl]
    rfl
  · intro z J J' hJ hJ'
    obtain ⟨J₀, hJ₀⟩ := good_exists T.M.isLB z
    rw [ha₀, hb₀] at hvu
    rw [hv₁ z J₀ J' hJ₀ hJ', hrel _ _ z J' J J₀ hJ' hJ hJ₀, hvu _ ((TK V).hom ≫ spMap θ) z J₀ J hJ₀ hJ, hsqQ,
      Category.assoc ((TK V).hom) (spMap θ) (spMap iw), hcomp, _root_.mul_assoc]

end GlobalTheory.PullFrom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalFlagUniversalStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautological_flag_universal : ∀ (ι : Type) [Fintype ι] (N : ℕ) (fl : ∀ _ : ι, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback (GlobalTheory.FlagZ.flStr ι N)).obj (GlobalTheory.FlagZ.Taut.stdE N)) N), GlobalTheory.FlagZ.Taut.IsTaut ι N fl →
  ∀ (T : Scheme.{0}) (g : T ⟶ Sp ℤ) (fl' : ∀ _ : ι, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback g).obj (GlobalTheory.FlagZ.Taut.stdE N)) N),
    ∃ g' : T ⟶ GlobalTheory.FlagZ.Fl ι N, ∃ w : g' ≫ GlobalTheory.FlagZ.flStr ι N = g, ∀ a i,
      ∃ e : (Scheme.Modules.pullback g').obj ((fl a).F i) ≅ (fl' a).F i,
        e.hom ≫ (fl' a).ι i = (Scheme.Modules.pullback g').map ((fl a).ι i) ≫
          (Scheme.Modules.pullbackComp g' (GlobalTheory.FlagZ.flStr ι N)).hom.app (GlobalTheory.FlagZ.Taut.stdE N) ≫
            (Scheme.Modules.pullbackCongr w).hom.app (GlobalTheory.FlagZ.Taut.stdE N) := by
  first | exact @GlobalTheory.FlagZ.exists_classifying | exact GlobalTheory.FlagZ.exists_classifying | (intros; apply GlobalTheory.FlagZ.exists_classifying <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalLatticeIdentificationEqId
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem lattice_iso_eq_of_tautPts : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (ψ : InvFun ℤ) (m N n : ℕ) (ε : (Fin m ⊕ Fin N) → LinearMap.BilinForm ℤ (Fin T.r → ℤ)), 3 ≤ n → IsCone id ψ (fun k => ε (.inl k)) → (∀ x, x ≠ 0 → ∃ k, 0 < ε (.inl k) x x) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D₁ D₂ : DegPre V) (ω₁ : W →+* V) (s₁ : (Fin m ⊕ Fin N) → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (ω₂ : W →+* V) (s₂ : (Fin m ⊕ Fin N) → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → (∀ k, s₁ (.inl k) ∈ maximalIdeal V ∧ s₁ (.inl k) ≠ 0) → (∀ k, IsUnit (s₁ (.inr k))) → (∀ k, s₂ (.inl k) ∈ maximalIdeal V ∧ s₂ (.inl k) ≠ 0) → (∀ k, IsUnit (s₂ (.inr k))) → Match D₁ D₂ b φ F → (∀ a : Fin T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → ∀ y, e₂ (φ y) = e₁ y := by
  intro o W _ _ _ T ψ m N n ε hn hcone hdef V _ _ _ D₁ D₂ ω₁ s₁ e₁ β₁ ββ₁ w₁ ω₂ s₂ e₂ β₂ ββ₂ w₂ b φ F _ _ hτ₁ hτ₂ hF₁ hF₂
    hs₁ hu₁ hs₂ hu₂ hM hpts
  let ga : (Fin T.r → ℤ) ≃ₗ[ℤ] (Fin T.r → ℤ) := ((e₁.symm.trans φ).trans e₂).toIntLinearEquiv
  have hga : ∀ a, ga a = e₂ (φ (e₁.symm a)) := fun _ => rfl

  have hcong : ∀ a, GlobalTheory.Poinc.CongMod n (ga a) a := by
    intro a
    obtain ⟨p₁, p₂, hy₁, -, hy₂, -, p', hp', -, z, hz, -⟩ := hpts a
    have h : e₂ p₂.y = e₂ (φ p₁.y) + n • e₂ z := by rw [hz, map_add, hp', map_nsmul]
    rw [hy₂, hy₁, AddEquiv.apply_symm_apply] at h
    refine ⟨-(e₂ z), ?_⟩
    rw [smul_neg, eq_add_neg_iff_add_eq, hga]
    exact h.symm

  have hpu := GlobalTheory.T.tautologicalBase_matching_monomials_ratio_unit T ε n V D₁ D₂ ω₁ s₁ e₁ β₁ ββ₁ w₁ ω₂ s₂ e₂ β₂ ββ₂ w₂ b φ F hτ₁ hτ₂ hF₁ hF₂ hM
  have hab : ∀ a b, ∃ u : Vˣ, ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (ga a) (ga b)) =
      algebraMap V (FractionRing V) u * ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i a b) := by
    intro a b
    obtain ⟨u, hu⟩ := hpu (e₁.symm a) (e₁.symm b)
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at hu
    exact ⟨u, hu⟩
  obtain ⟨c₁, c₂, hc₁, hc₂, hsum⟩ := GlobalTheory.T.monomials_differ_by_units_positive_boundaryCombination V T.r m N n (by omega) ε s₁ s₂ ga hs₁ hu₁ hs₂ hu₂ hab
  have hS := GlobalTheory.T.smoothCone_sum_generators_eq_of_common_interiorPoint ψ (Fin T.r → ℤ) m m (fun k => ε (.inl k)) (fun k => pull ga.toLinearMap (ε (.inl k))) hcone
    (hcone.pull_equiv ga) c₁ c₂ hc₁ hc₂ hsum

  have he : ∀ x y, (∑ k, ε (.inl k)) (ga x) (ga y) = (∑ k, ε (.inl k)) x y := by
    intro x y
    have h := LinearMap.congr_fun₂ hS x y
    simp only [LinearMap.sum_apply, pull_apply, LinearEquiv.coe_coe] at h ⊢
    exact h.symm
  have hpos : ∀ x, x ≠ 0 → 0 < (∑ k, ε (.inl k)) x x := by
    intro x hx
    obtain ⟨k, hk⟩ := hdef x hx
    simp only [LinearMap.sum_apply]
    exact Finset.sum_pos' (fun i _ => hcone.nonneg i x) ⟨k, Finset.mem_univ _, hk⟩
  have hrefl := GlobalTheory.Poinc.eq_refl_of_isometry_congMod (Fin T.r → ℤ) (∑ k, ε (.inl k)) hpos ga he n hn hcong
  intro y
  have h := DFunLike.congr_fun hrefl (e₁ y)
  rw [hga, AddEquiv.symm_apply_apply, LinearEquiv.refl_apply] at h
  exact h

end GlobalTheory.TInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalSubbundleRankStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tautological_subbundle_rank : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (i : Fin (N + 1)), VB.IsVB (F ι N τ i) i ∧ VB.IsSubbundle (incl ι N τ i) := by
  first | exact @GlobalTheory.FlagZ.Univ.isVB_F_and_isSubbundle_incl | exact GlobalTheory.FlagZ.Univ.isVB_F_and_isSubbundle_incl | (intros; apply GlobalTheory.FlagZ.Univ.isVB_F_and_isSubbundle_incl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoIntegralLogAddInv
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem tendsto_integral_log_add_inv : ∀ (T : Type) [MeasurableSpace T] (μ : Measure T) [IsFiniteMeasure μ] (w : T → ℝ) (C : ℝ), Measurable w → (∀ x, 0 ≤ w x ∧ w x ≤ C) → (∀ᵐ x ∂μ, 0 < w x) → Integrable (fun x => Real.log (w x) / 2) μ → Tendsto (fun n : ℕ => ∫ x, Real.log (w x + 1 / ((n : ℝ) + 1)) ∂μ) atTop (𝓝 (2 * ∫ x, Real.log (w x) / 2 ∂μ)) := by
  intro T _ μ _ w C hw hwC hpos hint
  have hint' : Integrable (fun x => Real.log (w x)) μ := by
    refine (hint.const_mul 2).congr (Eventually.of_forall fun x => ?_)
    simp only; ring
  have hlim : 2 * ∫ x, Real.log (w x) / 2 ∂μ = ∫ x, Real.log (w x) ∂μ := by
    rw [← integral_const_mul]; congr 1; ext x; ring
  rw [hlim]
  refine tendsto_integral_of_dominated_convergence (fun x => |Real.log (w x)| + |Real.log (C + 1)|) ?_ ?_ ?_ ?_
  · intro n
    exact (Real.measurable_log.comp (hw.add_const _)).aestronglyMeasurable
  · exact hint'.abs.add (integrable_const _)
  · intro n
    filter_upwards [hpos] with x hx
    have hd : 0 < 1 / ((n:ℝ) + 1) := by positivity
    have hd1 : 1 / ((n:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    have h1 : Real.log (w x) ≤ Real.log (w x + 1 / ((n:ℝ)+1)) := Real.log_le_log hx (by linarith)
    have h2 : Real.log (w x + 1 / ((n:ℝ)+1)) ≤ Real.log (C + 1) :=
      Real.log_le_log (by linarith) (by linarith [(hwC x).2])
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [neg_abs_le (Real.log (w x)), abs_nonneg (Real.log (C+1))]
    · linarith [le_abs_self (Real.log (C+1)), abs_nonneg (Real.log (w x))]
  · filter_upwards [hpos] with x hx
    have h : Tendsto (fun n : ℕ => w x + 1 / ((n:ℝ) + 1)) atTop (𝓝 (w x + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h
    exact (Real.continuousAt_log hx.ne').tendsto.comp h

end GlobalTheory.Mix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataMumfordSideGeneratorValuesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorData_mumfordSide_generator_values : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D' W) (A : Matrix (Fin r) (Fin r) ℤ) (f : D'.P.A ⟶ D'.P.A), f = GlobalTheory.TensAct.matAct T A → W = (W + W.transpose) * A → ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun p : Fin 4 × ((Fin r × Fin r) × Fin 4) => (![(padd D'.P.A (𝟙 _) f).left, 𝟙 D'.P.A.left, f.left, (toUnit D'.P.A ≫ η[D'.P.A]).left] : Fin 4 → (D'.P.A.left ⟶ D'.P.A.left)) p.1 ≫ tensφ T.pr p.2) (fun p => (![1, -2, -1, 2] : Fin 4 → ℤ) p.1 * tensε W p.2)), t.IsGen ∧ ∀ (y : D'.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → val t (D'.xK y) z J = ∏ a : Fin 4, (∏ i, ∏ j, val (D.toPre.tau (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) a) i) (T.xe ((![y + GlobalTheory.TensAct.latAct T A y, y, GlobalTheory.TensAct.latAct T A y, 0] : Fin 4 → D'.X) a) j)) (𝟙 _) z J ^ W i j) ^ (-(![1, -2, -1, 2] : Fin 4 → ℤ) a) := by
  first | exact @GlobalTheory.MumSide.mside | exact GlobalTheory.MumSide.mside | (intros; apply GlobalTheory.MumSide.mside <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPeriodsBalancedIntegralMatricesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorData_periods_balanced_integralMatrices : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R))
    {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef →
    ∀ (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (hl : IsLimit (Fan.mk D'.toPre.P.A pr)) (xe : D'.toPre.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))),
    (∀ i, IsMonHom (pr i)) → (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) → w.IsGen →
    (∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' →
      val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) →
    letI := PowLim.mod xe (symUnitOf W h)
    ∀ a : TensO (symUnitOf W h), D'.toPre.TauBal (PowLim.act pr hl (TensO.mat _ a)) (PowLim.act pr hl (TensO.mat _ (star a)))
      (fun y => a • y) (fun y => star a • y) := by
  first | exact @GlobalTheory.Mum.PolTens.tauBal_polTens | exact GlobalTheory.Mum.PolTens.tauBal_polTens | (intros; apply GlobalTheory.Mum.PolTens.tauBal_polTens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiScalarEqUnitMulProdPeriodsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorData_psiScalar_eq_unit_mul_prod_periods : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : GlobalTheory.PolDeg.Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)) (xe : D'.X ≃+ (Fin r → Q.X)) (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → ∀ (k : Q.X → Q.X → (FractionRing R)ˣ), (∀ a b, Q.TauCoord a b (k a b)) → ∀ (ga' : ∀ χ : D'.X, LB.Gen (LB.LinComb D'.P.L (K := PUnit) (fun _ => (D'.c χ).left) (fun _ => -1))) (a' : D'.X → (FractionRing R)ˣ), GlobalTheory.UU.PsiScal D' ga' a' → ∀ y : D'.X, ∃ u ∈ unitsK R, a' y = u * ∏ i, ∏ j, k (xe y i) (xe y j) ^ W i j := by
  first | exact @GlobalTheory.Mum.TensPol.scalar_tens | exact GlobalTheory.Mum.TensPol.scalar_tens | (intros; apply GlobalTheory.Mum.TensPol.scalar_tens <;> assumption)
end

