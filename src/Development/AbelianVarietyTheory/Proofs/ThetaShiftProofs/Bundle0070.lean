import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridgeAlt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0022
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmValueLineLengthConjEqStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0047
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0054
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0068

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmArcDatumFamilyFunctionalBoundedLinearOnCuspFor
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM.RunNum

theorem sum_extendByZero_fin_eq_sum_of_eq {p m : ℕ} (f : Fin p → ℕ) (h : m = p) : ∑ i : Fin m, ext0 f i = ∑ i, f i := by
  subst h
  exact Finset.sum_congr rfl fun i _ => by simp [ext0]

theorem conj_rt_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (τ : E →+* ℂ)
    (h : τ (H.rt : E) = H.rt0) : conjEmb τ (H.rt : E) ≠ H.rt0 := by
  intro h'
  have h1 : starRingEnd ℂ H.rt0 = H.rt0 := by
    have h0 : starRingEnd ℂ (τ (H.rt : E)) = H.rt0 := h'
    rwa [h] at h0
  have h2 : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h1
  have h3 := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp [pow_two, h2] at h3
  nlinarith [mul_self_nonneg H.rt0.re]

theorem absA_wtA {D : D7} (T : Core D) (j : ℕ) (hD : IsDatW D j (T.Q.Dw j)) (hH : T.Q.PinHost)
    (w : WeightFamilies.Wt D j) :
    absA (T.Q.Dw j) (wtA w) = ∑ t, ((∑ i, w.aP t i) + ∑ i, w.aM t i) := by
  classical
  simp only [absA, wtA]
  rw [Finset.sum_congr rfl fun σ _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Finset.sum_add_distrib]
  have ht := hH.2.2.2 t
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [Finset.sum_eq_single (DV.tauEmb D t)]
    · simp only [if_true]
      exact sum_extendByZero_fin_eq_sum_of_eq _ (by rw [← hD.1]; simp [Datum.mult, ht])
    · intro b _ hb; simp [hb]
    · simp
  · rw [Finset.sum_eq_single (conjEmb (DV.tauEmb D t))]
    · simp only [if_true]
      exact sum_extendByZero_fin_eq_sum_of_eq _ (by rw [← hD.2.1]; simp [Datum.mult, conj_rt_ne _ _ ht])
    · intro b _ hb; simp [hb]
    · simp

theorem absA_add_le_size {D : D7} (T : Core D) (hp : T.Q.Pins) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) :
    (absA (T.Q.Dw j) (wtA w) : ℝ) + (D.R.f : ℝ) * D.R.r * w.n ≤ w.size := by
  rw [absA_wtA T j (hp.2.2.2 j hj) hp.1 w]
  unfold WeightFamilies.Wt.size
  push_cast
  have h1 : (1 : ℝ) ≤ max ((D.R.sigW j).2 : ℝ) 1 := le_max_right _ _
  have h2 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * w.n := by positivity
  nlinarith

theorem pnorm_le_sup {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type} [Fintype Comp]
    (X : Comp → Data E r) (la) {P : FDSec X} (hP : P ∈ holSub X la) (p : FPt X) :
    (X p.1).pnorm (la p.1) (P p.1) p.2 ≤ Formalism.L2.Pj.supN X la P := by
  unfold Formalism.L2.Pj.supN
  rw [← ENNReal.ofReal_le_iff_le_toReal (supE_ne_top _ _ hP)]
  exact le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)) p

theorem one_le_LaAt (D : D7) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) : 1 ≤ LaAt D j ka CR Tt cc :=
  le_max_left _ _

theorem archimedeanTerm_nonneg (E : Type) [Field E] [NumberField E] {r : ℕ} (hr : 1 ≤ r) {La : ℝ} (hLa : 1 ≤ La) (c₁ : ℝ) :
    0 ≤ archP E r La c₁ := by
  unfold archP
  have h1 : 0 ≤ Real.log (max 1 c₁) := Real.log_nonneg (le_max_left _ _)
  have h2 : 0 ≤ Real.log La := Real.log_nonneg hLa
  have h3 : 0 ≤ Real.log (rdE E) := by
    refine Real.log_nonneg (Real.one_le_rpow ?_ (by positivity))
    unfold dE
    exact_mod_cast Int.one_le_abs (discr_ne_zero E)
  have h4 : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
  linarith

theorem arch_good (hK : Known) {D : D7} {T : Core D} (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ)
    (hG : GlobalTheory.RunIn.GamAt T) (hj : InR D j) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁]
    (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁) (hd : Std d)
    (s : CMIn d.a d.e d.th d.jj (nAt D j ka CR Tt cc) (LaAt D j ka CR Tt cc) (WeightFamilies.c1 D CR Tt cc j))
    (em : K₁ →+* ℂ) (hem : GoodEmb T.Q.c (em.comp (algebraMap T.Q.c.F K₁))) (F : (recB h).Cusp j ka) :
    ‖em (cfOf d.yF d.μ d.jj F.1)‖ * (s.valLine d.μ ka.n).n em ≤
      (recB h).supN j ka (em.comp (algebraMap T.Q.c.F K₁)) F * Real.exp (CarchAt D j ka CR Tt cc) := by
  obtain ⟨-, -, -, -, -, hf, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨-, hr, -⟩ := hnum j hj
  have hFc : F.1 ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA ka) ka.n := cutR_le T.C j ka F.2
  have hS : (recB h).supN j ka (em.comp (algebraMap T.Q.c.F K₁)) F =
      supC (T.Q.Xo j) T.Q.c (T.U j) (xiR D) (em.comp (algebraMap T.Q.c.F K₁)) (wtA ka) ka.n F.1 := by
    change cutN T.C T.Ns j ka _ F = _
    unfold cutN Core.Ns
    rw [if_pos hj, goodOf, if_pos hem]
  have h0 := (recB h).supN_nonneg j ka (em.comp (algebraMap T.Q.c.F K₁)) F
  have hb := GlobalTheory.T.norm_cmArcCoefficientFunctional_le hK _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d _ _ _ s em D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j _)) (xiR D) ((recB h).supN j ka (em.comp (algebraMap T.Q.c.F K₁)) F)
    (wtA ka) ka.n hd (one_le_LaAt D j ka CR Tt cc) hem (h.unf j hj _ hem) (h.xiAbs j hj _ hem) (dom_wtA ka)
    (GlobalTheory.TransvPrinc.transvIn_of_hasPrinc _ _ _ _ _ _ _ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j _)) _ _ (hG j hj _ hem)
      (h.chiTriv j hj _ hem _ _ (dom_wtA ka)))
    F.1 (cusp_le_sec _ _ _ _ _ hFc) h0 (by
      intro k y hy
      rw [hS]
      exact mul_le_mul_of_nonneg_left
        (pnorm_le_sup _ _ (((mem_cusp _ _ _ _ _ _).1 hFc).2 _ hem) ⟨k, ⟨y, hy⟩⟩) (lieFac_pos _ _ _).le)
  refine hb.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) h0)
  unfold CarchAt
  have h1 := absA_add_le_size T h.pins j hj ka
  have h2 : (fdeg D.host.E : ℝ) = D.R.f := by
    unfold fdeg
    rw [hf, Nat.mul_div_cancel_left _ two_pos]
  have h3 : (D.R.f : ℝ) * ka.n ≤ (D.R.f : ℝ) * D.R.r * ka.n := by
    have : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr
    have h4 : (0 : ℝ) ≤ (D.R.f : ℝ) * ka.n := by positivity
    nlinarith
  rw [h2]
  have h5 := archimedeanTerm_nonneg D.host.E hr (one_le_LaAt D j ka CR Tt cc) (WeightFamilies.c1 D CR Tt cc j)
  exact add_le_add_right (mul_le_mul_of_nonneg_left (by linarith) h5) _

theorem arch_all (hK : Known) {D : D7} {T : Core D} (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ)
    (hG : GlobalTheory.RunIn.GamAt T) (hj : InR D j) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁]
    (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁) (hd : Std d)
    (s : CMIn d.a d.e d.th d.jj (nAt D j ka CR Tt cc) (LaAt D j ka CR Tt cc) (WeightFamilies.c1 D CR Tt cc j))
    (em : K₁ →+* ℂ) (F : (recB h).Cusp j ka) :
    ‖em (cfOf d.yF d.μ d.jj F.1)‖ * (s.valLine d.μ ka.n).n em ≤
      (recB h).supN j ka (em.comp (algebraMap T.Q.c.F K₁)) F * Real.exp (CarchAt D j ka CR Tt cc) := by
  by_cases hem : GoodEmb T.Q.c (em.comp (algebraMap T.Q.c.F K₁))
  · exact arch_good hK h j ka CR Tt cc hG hj K₁ d hd s em hem F
  · have hg := goodEmb_goodOf T.Q.c (em.comp (algebraMap T.Q.c.F K₁))
    rw [goodOf, if_neg hem] at hg
    have h1 := arch_good hK h j ka CR Tt cc hG hj K₁ d hd s ((starRingEnd ℂ).comp em) hg F
    rw [GlobalTheory.T.cmValueLine_length_conj_eq hK _ _ _ _ _ K₁ _ _ _ _ _ _ _ s d.μ ka.n em, RingHom.comp_assoc, recB_supN_conj] at h1
    simpa using h1

end GlobalTheory.ArcCM.RunNum

namespace GlobalTheory.ArcCM

open RunNum

theorem numGood_of_famQ : Known → ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (large₂ : SizeData₂ D), GlobalTheory.RunIn.GamAt T → InR D j → j < D.R.m → ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁), FamQ T j ka CR Tt cc K₁ d → ∃ φ : (recB h).Cusp j ka →ₗ[T.Q.c.F] K₁, (∀ F, φ F = cfOf d.yF d.μ d.jj F.1) ∧ @NumGood T.Q.c.F ((recB h).Cusp j ka) _ _ ((recB h).acgC j ka) ((recB h).modC j ka) {F | F ∈ (recB h).Mlat j ka} (fun σ F => (recB h).supN j ka σ F) (beOf D.host.E (nAt D j ka CR Tt cc) (absA (T.Q.Dw j) (wtA ka))) (CarchAt D j ka CR Tt cc) (BdegAt large₂ j ka CR Tt cc) K₁ _ _ _ φ := by
  intro hK D T h j ka CR Tt cc large₂ hG hj _ K₁ _ _ _ d ⟨hd, ⟨s⟩⟩
  obtain ⟨hgood, -, -, -, -, hf, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨hpq, hr, -⟩ := hnum j hj
  have hle : cutR T.C j ka ≤ sec (T.Q.Xo j) T.Q.c (wtA ka) ka.n :=
    (cutR_le T.C j ka).trans (cusp_le_sec _ _ _ _ _)
  obtain ⟨⟨ψ, hψ⟩, hdeg⟩ := cfOf_linear_and_degree hK _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d (wtA ka) ka.n
  have hLa := one_le_LaAt D j ka CR Tt cc
  have hc : 0 ≤ pDeg large₂.logOm + (1 / 2) * Real.log (LaAt D j ka CR Tt cc) := by
    have := Real.log_nonneg hLa
    unfold pDeg
    positivity
  have hφ : ∀ F : (recB h).Cusp j ka, (ψ.comp (Submodule.inclusion hle)) F = cfOf d.yF d.μ d.jj F.1 :=
    fun F => hψ _
  refine ⟨ψ.comp (Submodule.inclusion hle), hφ, ?_⟩
  by_cases hμ : ∑ v, d.μ v = absA (T.Q.Dw j) (wtA ka)
  · obtain ⟨hN, hNd⟩ := valLine_ndeg_le hK _ _ _ _ _ K₁ _ _ _ _ _ _ _ s large₂.logOm d.μ ka.n hLa
      (lamDegSt_logOm₂ hK D T large₂ h.pins)
    refine ⟨s.valLine d.μ ka.n, hN, hNd.trans ?_, GlobalTheory.T.cmValueLine_length_conj_eq hK _ _ _ _ _ K₁ _ _ _ _ _ _ _ s _ _, ?_, ?_⟩
    · unfold BdegAt
      refine mul_le_mul_of_nonneg_left ?_ hc
      rw [hμ, hf, hpq, Nat.mul_div_cancel_left _ two_pos]
      push_cast
      exact absA_add_le_size T h.pins j hj ka
    · intro la w hw F hF hne
      rw [hφ] at hne ⊢
      exact GlobalTheory.T.cmArcDatum_functional_finite_integrality_bound hK _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d _ _ _ s
        (modelsAt_of_good_level hK _ _ _ _ _ _ (hpq ▸ hr) hgood) hd hLa la w hw (wtA ka) ka.n F.1
        ⟨hle F.2, fun v hv => hF la v hv⟩ hne
    · intro em F _ hne
      have hpos : 0 < (recB h).supN j ka (em.comp (algebraMap T.Q.c.F K₁)) F := by
        refine lt_of_le_of_ne ((recB h).supN_nonneg j ka _ F) fun h0 => hne ?_
        rw [((recB h).supN_eq_zero j ka _ F).1 h0.symm]
        exact map_zero _
      have h1 := arch_all hK h j ka CR Tt cc hG hj K₁ d hd s em F
      rw [hφ] at hne ⊢
      have h2 : 0 < ‖em (cfOf d.yF d.μ d.jj F.1)‖ := norm_pos_iff.2 ((map_ne_zero em).2 hne)
      have h3 := Real.log_le_log (mul_pos h2 (hN.2 em)) h1
      rwa [Real.log_mul h2.ne' (hN.2 em).ne', Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp] at h3
  · have hz : ∀ F : (recB h).Cusp j ka, ¬ (ψ.comp (Submodule.inclusion hle)) F ≠ 0 := fun F hne =>
      hμ (hdeg F.1 (hle F.2) (hφ F ▸ hne))
    refine ⟨MLine.one, ⟨one_ne_zero, fun _ => one_pos⟩, ?_, fun _ => rfl, fun _ _ _ F _ hne => (hz F hne).elim,
      fun _ F _ hne => (hz F hne).elim⟩
    have : (MLine.one : MLine K₁).ndeg = 0 := by simp [MLine.ndeg, MLine.deg, MLine.one]
    rw [this]
    exact mul_nonneg hc (zero_le_one.trans ka.one_le_size)

end GlobalTheory.ArcCM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExtendEmbedding
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM

theorem exists_extend_embedding {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K] [Algebra F K]
    (σ : F →+* ℂ) : ∃ em : K →+* ℂ, em.comp (algebraMap F K) = σ := by
  letI : Algebra F ℂ := σ.toAlgebra
  haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  let f : K →ₐ[F] ℂ := IsAlgClosed.lift
  exact ⟨f.toRingHom, RingHom.ext fun x => f.commutes x⟩

theorem killQ_of_gamAt : Known → ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), GlobalTheory.RunIn.GamAt T → InR D j → j < D.R.m → KillQ h j ka CR Tt cc := by
  intro hK D T h j ka CR Tt cc hG hj hm K₁ _ _ _ d hd F hF
  have key : ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ →
      (∀ k, rdU (T.U j σ) F.1 k ∈ ((T.U j σ).X k).SSgt (laU (T.U j σ) (wtA ka) ka.n k) (WeightFamilies.c1 D CR Tt cc j)) →
      cfOf d.yF d.μ d.jj F.1 = 0 := by
    intro σ hσ hr
    obtain ⟨em, rfl⟩ := exists_extend_embedding (K := K₁) σ
    have hc : F.1 ∈ T.C j ka := cutR_le T.C j ka F.2
    exact GlobalTheory.T.cmArcFunctional_vanishes_low_fourierJacobi hK _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d _ _ _ em _
      (Formalism.L2.PjFree.Unf.ofPj (T.U j _)) (wtA ka) ka.n hd hσ (h.unf j hj _ hσ) (dom_wtA ka)
      (GlobalTheory.TransvPrinc.transvIn_of_hasPrinc _ _ _ _ (T.Q.Xo j) T.Q.c _ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j _)) (wtA ka) ka.n
        (hG j hj _ hσ) (h.chiTriv j hj _ hσ _ _ (dom_wtA ka))) F.1 hc.1 hr
  exact key T.σ₀ T.good_σ₀ ((GlobalTheory.T.mem_forms_low_coeffs_vanish_iff_fourierJacobi D T h j ka CR Tt cc hj hm F).2.1 hF)

end GlobalTheory.ArcCM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFamilyMemberFunctionalNeZero
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcDetect

theorem exists_place (p : ℕ) (hp : p.Prime) : ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits := by
  have hne : (Ideal.span {(p : (⊥ : Subring ℂ))}) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    obtain ⟨n, hn⟩ := Subring.mem_bot.1 v.2
    have h1 : ((p : ℤ) * n : ℤ) = 1 := by
      have := congrArg Subtype.val hv
      simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one] at this
      rw [← hn] at this
      exact_mod_cast this
    have := Int.isUnit_iff_natAbs_eq.1 (IsUnit.of_mul_eq_one _ h1)
    simp at this
    exact hp.one_lt.ne' this
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
  exact ⟨W, hW ⟨p, Ideal.mem_span_singleton_self _, by simp⟩⟩

theorem iSup_sub_iInf_le {r : ℕ} (hr : 0 < r) (x : Fin r → ℝ) (A B : ℝ) (h1 : ∀ i, x i ≤ A) (h2 : ∀ i, -B ≤ x i) :
    (⨆ i, x i) - ⨅ i, x i ≤ A + B := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have := ciSup_le h1
  have := le_ciInf h2
  linarith

section Weight

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sum_cm {r : ℕ} (X : Data E r) (g : (E →+* ℂ) → ℕ) :
    ∑ τ : X.Ψ, (g τ.1 + g (conjEmb τ.1)) = ∑ τ, g τ := by
  classical
  rw [← Finset.sum_add_sum_compl X.Ψ g]
  have hc : X.Ψᶜ = X.Ψ.image NumberField.ComplexEmbedding.conjugate := by
    ext σ
    simp only [Finset.mem_compl, Finset.mem_image]
    constructor
    · intro h
      exact ⟨NumberField.ComplexEmbedding.conjugate σ, (X.cmType _).2 (by simpa using h), by simp⟩
    · rintro ⟨τ, hτ, rfl⟩
      exact (X.cmType τ).1 hτ
  rw [hc, Finset.sum_image (fun a _ b _ h => by simpa using congrArg NumberField.ComplexEmbedding.conjugate h),
    ← Finset.sum_add_distrib]
  exact Finset.sum_coe_sort X.Ψ (fun τ => g τ + g (ComplexEmbedding.conjugate τ))

theorem card_cm {r : ℕ} (X : Data E r) : Fintype.card X.Ψ = fdeg E := by
  have h := sum_cm X (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
  unfold fdeg
  rw [← NumberField.Embeddings.card E ℂ]
  omega

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem laU_dominant {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (h : Dom a n)
    (k : U.Comp) : (U.X k).IsDominant (laU U a n k) := by
  intro τ
  refine ⟨fun i j hij hj => ?_, fun i j hi hij => ?_, fun i j hi hj => ?_⟩
  · have hij' : (i : ℕ) ≤ j := hij
    have := h.1 (Function.invFun (relab c σ) (conjEmb τ.1))
      (show (U.X k).p0 - 1 - (j : ℕ) ≤ (U.X k).p0 - 1 - (i : ℕ) by omega)
    unfold laU
    rw [if_neg (by omega), if_neg (by omega)]
    dsimp only at this
    omega
  · have hij' : (i : ℕ) ≤ j := hij
    have := h.1 (Function.invFun (relab c σ) τ.1)
      (show (i : ℕ) - (U.X k).p0 ≤ (j : ℕ) - (U.X k).p0 by omega)
    unfold laU
    rw [if_pos (by omega), if_pos (by omega)]
    dsimp only at this
    omega
  · unfold laU
    rw [if_neg (by omega), if_pos (by omega)]
    omega

theorem invFun_relab (τ : E →+* ℂ) : Function.invFun (relab c c.F.val.toRingHom) τ = τ := by
  have h : ∀ τ : E →+* ℂ, relab c c.F.val.toRingHom τ = τ := fun τ => RingHom.ext fun _ => rfl
  have h2 : relab c c.F.val.toRingHom (Function.invFun (relab c c.F.val.toRingHom) τ) = τ :=
    Function.invFun_eq ⟨τ, h τ⟩
  rwa [h] at h2

theorem sum_spread_le {r : ℕ} (hr : 0 < r) (U : Unf Xo c c.F.val.toRingHom r) (hU : IsUnf U)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (k : U.Comp) :
    ∑ τ, (U.X k).spread (laU U a n k) τ ≤ (absA Dw a : ℝ) + (fdeg E : ℝ) * n := by
  obtain ⟨hrk, hk, -⟩ := hU
  obtain ⟨hp, hΨ⟩ := hk k
  let B : (E →+* ℂ) → ℕ := fun τ => ∑ i : Fin (Dw.mult τ), a (τ, (i : ℕ))
  have hB : ∀ τ i, i < Dw.mult τ → a (τ, i) ≤ B τ := fun τ i hi =>
    Finset.single_le_sum (f := fun i : Fin (Dw.mult τ) => a (τ, (i : ℕ))) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ ⟨i, hi⟩)
  have h1 : ∀ τ : (U.X k).Ψ, (U.X k).spread (laU U a n k) τ ≤ ((B τ.1 + B (conjEmb τ.1) : ℕ) : ℝ) + n := by
    intro τ
    have m1 : Dw.mult τ.1 = Dw.p := if_pos ((hΨ _).1 τ.2)
    have m2 : Dw.mult (conjEmb τ.1) = Dw.q :=
      if_neg fun h => ((U.X k).cmType τ.1).1 τ.2 ((hΨ _).2 h)
    have hn : ((n / 2 : ℕ) : ℝ) + ((n / 2 : ℕ) : ℝ) ≤ n := by
      have : n / 2 + n / 2 ≤ n := by omega
      exact_mod_cast this
    have key : ∀ i, -((B (conjEmb τ.1) : ℤ) + ((n / 2 : ℕ) : ℤ)) ≤ laU U a n k τ i ∧
        laU U a n k τ i ≤ (B τ.1 : ℤ) + ((n / 2 : ℕ) : ℤ) := by
      intro i
      have hi := i.2
      unfold laU
      rw [invFun_relab, invFun_relab]
      split_ifs with h
      · have a1 := hB τ.1 ((i : ℕ) - (U.X k).p0) (by omega)
        constructor <;> omega
      · have a2 := hB (conjEmb τ.1) ((U.X k).p0 - 1 - (i : ℕ)) (by omega)
        constructor <;> omega
    refine (iSup_sub_iInf_le hr _ ((B τ.1 : ℝ) + ((n / 2 : ℕ) : ℝ))
      ((B (conjEmb τ.1) : ℝ) + ((n / 2 : ℕ) : ℝ)) (fun i => ?_) (fun i => ?_)).trans ?_
    · have h1 := (Int.cast_le (R := ℝ)).2 (key i).2
      rwa [Int.cast_add, Int.cast_natCast, Int.cast_natCast] at h1
    · exact_mod_cast (key i).1
    · rw [Nat.cast_add]; linarith
  refine (Finset.sum_le_sum fun τ _ => h1 τ).trans ?_
  rw [Finset.sum_add_distrib, ← Nat.cast_sum, sum_cm (U.X k) B, Finset.sum_const, Finset.card_univ, card_cm,
    nsmul_eq_mul]
  rfl

theorem exists_split {r : ℕ} (X₀ : Data E r) (X : DataX E r) (hX : X.toData = X₀) (la : Wt X₀.Ψ r)
    (P : Frame X₀.Ψ r → ℂ) (c₁ w : ℝ) (q g : ℕ) (hq : X₀.p0 = q) (hg : X.g = g)
    (hdom : X₀.IsDominant la) (hc : 0 < c₁) (hw : 1 ≤ w) (hspr : (∑ τ, X₀.spread la τ) ≤ w) (hr : (r : ℝ) ≤ w)
    (hχ : ∀ gm ∈ X₀.Γ, X₀.χ la gm = 1) (hP : P ∈ X₀.SS la) (hP' : P ∉ X₀.SSgt la c₁) :
    ∃ (ξ : Fin r → E) (ν : X₀.Ψ → ℝ) (x : Frame X₀.Ψ r) (lam : Fin (r - 2) → Fin r → E),
      X₀.IsIso ξ ∧ ∑ τ, ν τ ≤ c₁ ∧ x ∈ X₀.dom ∧ SplitData X ξ (LaQ E r q g X.NA X.NC c₁ w) (hX ▸ x) lam ∧
      (∀ m ∈ X₀.Λp ξ, ∃ e : E, e • ξ ∈ X₀.Λ ∧
        ((nQ E r g X.NA X.NC c₁ w : ℕ) : ℂ) • X₀.aproj x ξ (X₀.embV m) = X₀.embV (e • ξ)) ∧
      X₀.fj la ξ ν P x ≠ 0 := by
  subst hX hq hg
  obtain ⟨ξ, ν, hξ, hν, -, -, h⟩ := GlobalTheory.FJDetect.exists_fj_ne_zero_at_split_point' X la P c₁ w hdom hc hw hspr hr
    (fun gm hgm _ => hχ gm hgm) hP hP'
  obtain ⟨x, hx, lam, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h (nQ E r X.g X.NA X.NC c₁ w) (by
    unfold nQ
    push_cast
    exact (Nat.le_ceil _).trans (le_add_of_nonneg_right zero_le_one))
  refine ⟨ξ, ν, x, lam, hξ, hν, hx, ⟨h1, h2, h3, h4, h5, fun j τ => (h6 j τ).trans ?_⟩, h7, h8⟩
  refine pow_le_pow_left₀ ?_ (le_max_right _ _) 2
  have hw0 : 0 < w := by linarith
  unfold d6La ReciprocityTheory.MultiplicativeHeights.approxR d5mu d6rh dE
  positivity

end Weight

theorem detect_of_tie (hK : Known) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {K₁ : Type} [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) {n' : ℕ} {La c₁ : ℝ}
    (s : CMIn d.a d.e d.th d.jj n' La c₁) (em : K₁ →+* ℂ) [Algebra (FractionRing ℂ) ℂ]
    [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (hσ : em.comp (algebraMap c.F K₁) = σ) {r : ℕ}
    (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r)
    (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    Std d → GoodEmb c σ → IsUnf U → GlobalTheory.FrameNorm.HasPrinc U l.M → Dom a' n →
    (∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (laU U a' n k) gm = 1) → (U.X k).IsIso ξ' → x ∈ (U.X k).dom →
    Comparison₂ Uw d.a em s.ξ k ξ' x → ∀ F ∈ sec Xo c a' n, (∀ k', (U.X k').IsBddSec (laU U a' n k') (rdU U F k')) →
    (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 s.ν₀).re) (rdU U F k) x ≠ 0 →
    ∃ mo : ArcLt Dw →₀ ℕ, cfOf d.yF mo d.jj F ≠ 0 := by
  subst hσ
  exact GlobalTheory.T.exists_coeff_ne_zero_of_fourierJacobi_arcDatum hK E H Dw l Xo c K₁ d n' La c₁ s em r U Uw k ξ' x a' n

theorem exists_fam_cfOf_ne_zero : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r) (k : U.Comp) (Xx : DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ w : ℝ), ModelsAt Xo c → IsUnf U → l.A = 1 → 3 ≤ r → GlobalTheory.FrameNorm.HasPrinc U l.M → Dom a' n → (∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (laU U a' n k) gm = 1) → 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → Xx.g = l.M → 0 < c₁ → ((absA Dw a' : ℝ) + (fdeg E : ℝ) * n + r ≤ w) → ∀ F ∈ sec Xo c a' n, (∀ k', rdU U F k' ∈ (U.X k').SS (laU U a' n k')) → rdU U F k ∉ (U.X k).SSgt (laU U a' n k) c₁ → ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra c.F K₁) (d : ArcDatum Xo c K₁), Fam (nQ E r l.M Xx.NA Xx.NC c₁ w) (LaQ E r Dw.q l.M Xx.NA Xx.NC c₁ w) c₁ d ∧ cfOf d.yF d.μ d.jj F ≠ 0 := by
  intro hK E _ _ _ H Dw l Xo c r U k Xx hX 𝔄 a' n c₁ w hM hU hA hr hP hD hχ h𝔄 hΛ hg hc hw F hF hS hS'
  letI : Algebra (FractionRing ℂ) ℂ := FractionRing.liftAlgebra ℂ ℂ
  haveI : IsScalarTower ℂ (FractionRing ℂ) ℂ := FractionRing.isScalarTower_liftAlgebra ℂ ℂ
  have hr3 : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have h0 : (0 : ℝ) ≤ (absA Dw a' : ℝ) + (fdeg E : ℝ) * n := by positivity
  obtain ⟨ξ, ν, x, lam, hξ, hν, hx, hsp, htor, hfj⟩ := exists_split (U.X k) Xx hX (laU U a' n k) (rdU U F k) c₁ w
    Dw.q l.M (hU.2.1 k).1 hg (laU_dominant U hD k) hc (by linarith)
    ((sum_spread_le (by omega) U hU a' n k).trans (by linarith)) (by linarith) (hχ k) (hS k) hS'
  obtain ⟨ν₀, hν1, hν2, hν3, hν4⟩ := GlobalTheory.FjFreq.freq_real_nonneg_integral E r (U.X k) _ _ (hS k).1 ξ hξ ν x hx hfj
  obtain rfl : ν = fun τ => (τ.1 ν₀).re := funext hν2
  rw [GlobalTheory.sum_re_cmType_eq_half_trace] at hν
  obtain ⟨Uw⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c _ r U hU
  have htv := GlobalTheory.TransvPrinc.transvIn_of_hasPrinc E H Dw l Xo c _ r U a' n hP hχ k
  obtain ⟨K₁, _, _, _, em, a, e, th, jj, s, hem, hs, htie⟩ := GlobalTheory.T.exists_cmArcData_at_splitIsotropicPoint hK E H Dw l Xo c r U Uw k ξ x Xx hX 𝔄
    _ _ c₁ lam (nQ E r l.M Xx.NA Xx.NC c₁ w) ν₀ hU hA hr hξ hx h𝔄 hΛ hsp le_rfl (Nat.succ_pos _) htor hν1 hν3
    (fun s h1 h2 => hν4 s h1 (htv ξ hξ s h1 h2)) hν
  obtain ⟨Wp, hWp⟩ := exists_place 2 Nat.prime_two
  obtain ⟨Y, hY, hYp⟩ := hM 2 Wp Nat.prime_two hWp
  obtain ⟨χ, W, -, hd⟩ := GlobalTheory.ArcDatumExists.exists_arcDatum hK.laws hK.laws2 E H Dw l Xo c K₁ Wp Y hY a
  obtain ⟨d, d1, d2, d3, d4, d5, -, d7, d8, d9⟩ := hd e
    (GlobalTheory.T.cmLetters_isLieBasis_along_arc hK E H Dw l Xo c K₁ a e th jj _ _ c₁ s _ _ Y χ W) th s.th_nz.ne_zero 0 jj
  obtain ⟨Wp', Y', a₁, χ', W', e', yF, th', i12, i3, mu, jj'⟩ := d
  dsimp only at d1 d2 d3 d4 d5 d7
  subst d1 d3 d7
  cases d2
  cases d4
  cases d5
  obtain ⟨mo, hmo⟩ := detect_of_tie hK ⟨Wp', Y', a₁, χ', W', e', yF, th', i12, i3, mu, jj'⟩ s em _ hem U Uw k ξ x a' n
    ⟨d8, d9, hYp⟩ rfl hU hP hD hχ hξ hx htie F hF (fun k' => (hS k').1) (by rw [hs]; exact hfj)
  exact ⟨K₁, _, _, _, ⟨Wp', Y', a₁, χ', W', e', yF, th', i12, i3, mo, jj'⟩, ⟨⟨d8, d9, hYp⟩, ⟨s⟩⟩, hmo⟩

end GlobalTheory.ArcDetect
end

