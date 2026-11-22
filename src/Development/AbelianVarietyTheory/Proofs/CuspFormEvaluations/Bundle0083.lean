import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0074
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0078
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0081
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0003
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0011
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0096
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0031
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0030
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpOfPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0016
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0011
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTiePf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0019
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.EvalSinglePointId
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0004
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0032
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0023
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFactsOfThetaDataOnModels
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem GlobalTheory.Shares.exists_anFacts_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (N : ℕ) (ka wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (CR c : ℝ), addL wF wL Tn = ka → Nonempty (ArchAt h j w wF Tn (WeightFamilies.c1 D CR Tn c j)) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → MggOnto h j CR Tn c ka → TieMaxCuspSt h j CR Tn c ka → ∃ (R : Rdg (recPlusN h j hj n)) (t : Idx D j N → ℂ) (δ : ℕ) (xs : Fin δ → R.Y), R.Generic t ∧ AnFacts R w t ka wF Tn (WeightFamilies.MggK n.base CR Tn c j ka) xs := by
  intro D T h j hj n N ka wL wF w Tn CR c hka hA hOn hM hTie
  subst hka
  obtain ⟨A⟩ := hA
  obtain ⟨R, e, hR⟩ := GlobalTheory.T.exists_base_embedding_reading_forms D T h j hj n
  obtain ⟨t, ht, ⟨Fl⟩⟩ := GlobalTheory.T.exists_algIndependent_coeffs_flatDatum D T h j hj N wL wF w Tn _ A
  classical
  let ι : Type := Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ
  have : Fintype ι := inferInstance
  let en : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let xs : Fin (Fintype.card ι) → R.Y := fun q =>
    e.symm ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩
  have hxs : ∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩ :=
    fun q => e.apply_symm_apply _
  have h1 := GlobalTheory.T.points_interpolation_genericSections D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs hOn
  refine ⟨R, t, _, xs, ?_, h1.1, h1.2,
    GlobalTheory.T.cuspForm_vanishing_at_points_mul_pow_mem_span D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs hOn,
    GlobalTheory.T.leadingProducts_independent_modulo_deepProducts D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs,
    GlobalTheory.T.archimedean_flat_decomposition_indexing D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs,
    GlobalTheory.T.finrank_lower_bound_cuspForm_vanishing_low_coeff D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs CR c rfl hM,
    GlobalTheory.T.cuspForm_vanishing_low_coeff_mem_leading_add_deep_span D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs hOn CR c rfl ?_⟩
  · intro Q hQ
    have hσ : R.σ = T.σ₀ := RingHom.ext hR.1
    rw [hσ]
    exact ht Q hQ
  · exact fun F hF => (hTie F).1 hF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConjugateSectionValuesSemilinearStatement
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateSection_values_semilinear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, galRul h f ∈ sec Xo c a n ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), evR Xo c (galRul h f) y = (evR Xo c f (twPt h y)).val) ∧ (∀ (t : c.F) (f g : Rul Xo c), galRul h (t • f + g) = ta t • galRul h f + galRul h g) ∧ ∀ (c₀ : Coeff l) (hle : c₀.F ≤ c.F), (∀ x : c₀.F, ta (incF c₀ c hle x) = incF c₀ c hle x) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (as : Fin m → c.F) (fs : Fin m → Rul Xo c₀), ∀ f ∈ sec Xo c a n, IsBC hle f as fs → IsBC hle (galRul h f) (fun i => ta (as i)) fs := by
  first | exact @GlobalTheory.GalTw.galRul_sec_val_semilinear | exact GlobalTheory.GalTw.galRul_sec_val_semilinear | (intros; apply GlobalTheory.GalTw.galRul_sec_val_semilinear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspReadingsLinearIndependent
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory

theorem cusp_readings_linearIndependent : ReciprocityTheory.ChartRestriction.G.PullbackSections.AlgInjAtSt := by
  unfold ReciprocityTheory.ChartRestriction.G.PullbackSections.AlgInjAtSt
  intro D T h j hj ka σ hσ m f hf
  have hlin := hf.map' (T.C j ka).subtype (T.C j ka).ker_subtype
  have hmem : ∀ i, (f i : T.R j) ∈ sec (T.Q.Xo j) T.Q.c (wtA ka) ka.n := fun i =>
    Formalism.L2.Pj.cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) (wtA ka) ka.n (f i).2
  have hU := h.unf j hj σ hσ
  have hB : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have key := (GlobalTheory.reading_linearIndependent_and_injective hB _ _ _ _ (T.Q.Xo j) T.Q.c σ _
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) ((Formalism.L2.PjFree.isUnf_ofPj (T.U j σ)).2 hU)
    (wtA ka) ka.n).1 m (fun i => (f i : T.R j)) hmem hlin
  simp only [Formalism.L2.PjFree.rdU_ofPj] at key
  exact key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartFree

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB Formalism.MainNotions.ModuliIntegralCharts.H1
open scoped ComplexConjugate
open Matrix

theorem embeddings_differ_on_integer {E : Type} [Field E] [NumberField E] (τ τ' : E →+* ℂ) (h : τ ≠ τ') :
    ∃ a : 𝓞 E, τ (a : E) ≠ τ' (a : E) := by
  by_contra hall
  push Not at hall
  apply h
  ext x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  simp only [map_div₀]
  rw [show (algebraMap (𝓞 E) E a) = (a : E) from rfl, show (algebraMap (𝓞 E) E b) = (b : E) from rfl,
    hall a, hall b]

theorem balanced_pairs_conjugate {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S] {d : ℕ} (A : 𝓞 E → Matrix (Fin d) (Fin d) S)
    (uvec : Lt1 Dw → Fin d → S)
    (heig : ∀ (a : 𝓞 E) (ℓ : Lt1 Dw) (i : Fin d), ∑ j, A a i j * uvec ℓ j = algebraMap c.F S (embK c ℓ.1 a) * uvec ℓ i)
    (M : Fin d → Fin d → S) (hbal : ∀ a, (A a).transpose * Matrix.of M = Matrix.of M * A (H.bar a))
    (ℓ ℓ' : Lt1 Dw) (hne : ∑ i, ∑ j, M i j * uvec ℓ i * uvec ℓ' j ≠ 0) :
    ℓ'.1 = ComplexEmbedding.conjugate ℓ.1 := by
  by_contra hc
  have hσ : ℓ.1 ≠ ComplexEmbedding.conjugate ℓ'.1 := by
    intro h
    apply hc
    rw [h]
    show ℓ'.1 = star (star ℓ'.1)
    rw [star_star]
  obtain ⟨a, ha⟩ := embeddings_differ_on_integer _ _ hσ
  have hmv : ∀ (b : 𝓞 E) (ℓ₀ : Lt1 Dw), A b *ᵥ uvec ℓ₀ = algebraMap c.F S (embK c ℓ₀.1 b) • uvec ℓ₀ := by
    intro b ℓ₀
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    exact heig b ℓ₀ i
  set B := uvec ℓ ⬝ᵥ (Matrix.of M *ᵥ uvec ℓ') with hB
  have hBe : B = ∑ i, ∑ j, M i j * uvec ℓ i * uvec ℓ' j := by
    rw [hB]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h1 := congrArg (fun N : Matrix (Fin d) (Fin d) S => uvec ℓ ⬝ᵥ (N *ᵥ uvec ℓ')) (hbal a)
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hmv,
    hmv, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    smul_eq_mul, ← hB] at h1
  have key : (algebraMap c.F S (embK c ℓ.1 a) - algebraMap c.F S (embK c ℓ'.1 (H.bar a))) * B = 0 := by
    rw [sub_mul, h1, sub_self]
  have hu : IsUnit (algebraMap c.F S (embK c ℓ.1 a) - algebraMap c.F S (embK c ℓ'.1 (H.bar a))) := by
    rw [← map_sub]
    refine IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)
    intro h0
    apply ha
    have h2 := congrArg (fun x : c.F => (x : ℂ)) (sub_eq_zero.1 h0)
    simp only [embK_coe] at h2
    rw [h2, H.bar_eq, IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
  exact hne (hBe ▸ (hu.mul_right_eq_zero).1 key)

theorem twist_on_eigenDirections (hFix : FrTruncFixSt) (hLE : LinEigSt) : FrTruncFixBSt := by
  intro E _ _ _ H Dw l Xo c _ hs S _ _ _ y C
  obtain ⟨e', hfr, hrig, cc, hT, h0, hsym, hbal, hu⟩ := hFix E H Dw l Xo c hs S y C
  exact ⟨e', hfr, hrig, cc, hT, h0, hsym, fun m ℓ ℓ' hne => balanced_pairs_conjugate c (fun a => dLin (C.B.A.act a)) C.uvec
    (fun a ℓ i => hLE E H Dw l Xo c S y C a ℓ i) (cc m) (hbal m) ℓ ℓ' hne, hu⟩

theorem eigenDirections : LinEigSt := GlobalTheory.EigDir.linEig_holds

theorem chartIndep_of_globalFns (hGlob : ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt) : ChartIndepSt2 :=
  have hAct := expActOf_of eigenDirections
  chartIndep2_verb
    (chartIndepTrunc_of (expChartOf_of hAct) (ExpGauge.expGaugeOf_of hAct) tie_holds ExpUniqChart.expUniqTan
      (gaugeUniq_of_global hGlob) (killAddVal_of fun _ _ _ _ H => psiCover_holds H))
    (twist_on_eigenDirections (frTruncFix_of frRatio_holds) eigenDirections) germFix_holds (harmInv_of hAct)

theorem chartIndep : ChartIndepSt2 :=
  chartIndep_of_globalFns GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end GlobalTheory.ChartFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinearStatement
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ruleBaseChange_section_values_semilinear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F), (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, rulBC hle f ∈ sec Xo c' a n ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S), evR Xo c' (rulBC hle f) y = evR Xo c f (y.res hle h)) ∧ (∀ (t : c.F) (f g : Rul Xo c), rulBC hle (t • f + g) = incF c c' hle t • rulBC hle f + rulBC hle g) := by
  first | exact @GlobalTheory.FieldBC.rulBC_sec_val_linear | exact GlobalTheory.FieldBC.rulBC_sec_val_linear | (intros; apply GlobalTheory.FieldBC.rulBC_sec_val_linear <;> assumption)
end

