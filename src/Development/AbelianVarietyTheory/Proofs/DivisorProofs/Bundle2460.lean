import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0044
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1522
import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0067
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0041
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0361
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0751
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0030
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2299
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2359
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2437

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionWeightJetBound
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.ThetaCuspOn.theta_cuspOn_value : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂), ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), letI := p.T.Q.H.starRing; ∀ (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∀ f ∈ thGen Y.d.Xo₂ Y.d.c₂ nab (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i)), ∀ (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → ∃ f' ∈ AllWt.cuspOn Y.U Z (Formalism.L2.Pj.wtZ (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i))), evI y' f' = evI y' f := by
  intro hP hD hS hF
  have hG := GlobalTheory.LiftGaps.lift_gaps hS
  unfold Covers Lifts at hG ⊢
  refine Formalism.MainNotions.Closed.imp hG ?_
  rintro eps Fm CH - ⟨C3, hC3, x3, h3⟩
  refine ⟨C3, hC3, x3, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hp1, hgap⟩ := h3 x hx hle ι p hp i hi Y hY
  intro Z TF la hla
  letI := p.T.Q.H.starRing
  intro nab hnab f hf y T io y' g hfac
  have hU := hY.1.unf

  obtain ⟨hanti, hgp⟩ := hgap la hla
  have hb : ∀ τ j, |(la τ j : ℝ)| ≤ ∑ τ', ∑ j', |(la τ' j' : ℝ)| := fun τ j =>
    (Finset.single_le_sum (f := fun j' => |(la τ j' : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun τ' => ∑ j', |(la τ' j' : ℝ)|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ τ))
  have hev : Even (GlobalTheory.RefSum.nCol (dat p i)) := by
    obtain ⟨k, hk⟩ := GlobalTheory.RefSum.eight_dvd_nCol (Dw := dat p i)
    exact ⟨4 * k, by omega⟩
  have hw := GlobalTheory.RefSum.thA_dominant_lastPos_degree _ _ (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)) _ hp1 hev hanti hgp hb
  have hr : 1 ≤ (Fm.D x ι).R.r := by
    have := (Fm.D x ι).R.two_le_m
    have := (Fm.D x ι).R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hcusp := (GlobalTheory.thetaRules_exist_and_cusp _ _ _ _ Y.d.Xo₂ Y.d.c₂ _ Y.U hr hU nab hnab).2 _ _ hw.1 hw.2.2.1 f hf
  obtain ⟨g', hg'e, -⟩ := GlobalTheory.CompRestr.exists_cuspOn_restrict _ _ _ _ Y.d.Xo₂ Y.d.c₂ _ Y.U hU Z _ ⟨f, hcusp⟩
  refine ⟨g', g'.2, ?_⟩
  letI := io.toAlgebra
  have hfac' : TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z := hfac
  have hL : GlobalTheory.AllWt.LiesOn Z y'.1 := by
    refine (ptY_le_iff TF.X Z y'.1).1 ?_
    rw [hfac']
    first
      | (rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top])
      | (intro s _; exact (((Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y) s).2 : _))
      | (intro s _; simp)
  exact hg'e T.Fr y'.1 hL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstLengthFlatSectionEqFrameNormComplexEmbeddin
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

noncomputable section

namespace GlobalTheory.PtDegArch

theorem good_case (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (hL : Laws U x) (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (hy : LiesOn Z y) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)) (hh : F.IsHerm h) (u : Fin (Dw.mult τ.1) → Fin F.P₀.g → K) (u' : Fin (Dw.mult (conjEmb τ.1)) → Fin F.P₀.g → K) (hu : GlobalTheory.PtDeg.FrameCoord y m1 m2 F τ.1 u) (hu' : GlobalTheory.PtDeg.FrameCoord y m1 m2 F (conjEmb τ.1) u') (σ : K →+* ℂ) (hσ : GoodEmb c (σ.comp (algebraMap c.F K))) :
    s.cInf (σ.comp (algebraMap c.F K)) = ‖σ (evR Xo c s.sig y)‖ * Real.sqrt (h.gram σ u).det.re / Real.sqrt (h.gram σ u').det.re := by
  set σ₀ := σ.comp (algebraMap c.F K) with hσ₀
  let φ : K →ₐ[c.F] CAt σ₀ := { σ with commutes' := fun a => rfl }
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c K (CAt σ₀) φ y
  obtain ⟨k, w, t, ho, hb⟩ := GlobalTheory.LamT.exists_ortho_frBor E H Dw l Xo c σ₀ r (U σ₀) (hL.unf σ₀ hσ) z
  have hon : (⟨k, w.1⟩ : Σ k, Frame ((U σ₀).X k).Ψ r) ∈ framesOn (U σ₀) Z :=
    ⟨w.2, liesOn_frBor hb (liesOn_frMap hz hy)⟩
  have hgood : goodOf c σ₀ = σ₀ := if_pos hσ
  have hinf := s.norm_inf σ₀
  rw [hgood] at hinf
  have h1 : homN (U σ₀) x (wtOf Dw (flatWt Dw τ) 0) s.sig ⟨k, w.1⟩ = s.cInf σ₀ := by
    have : homN (U σ₀) x (wtOf Dw (flatWt Dw τ) 0) s.sig ⟨k, w.1⟩ ∈
        homN (U σ₀) x (wtOf Dw (flatWt Dw τ) 0) s.sig '' framesOn (U σ₀) Z := ⟨_, hon, rfl⟩
    rw [hinf] at this
    exact this
  rw [GlobalTheory.CompHS.homN_eq_homFac] at h1
  have h2 := GlobalTheory.evR_frBor_of_mem_secZ GlobalTheory.lawsFieldsSeparately.2.1 Xo c _ s.sig_mem (CAt σ₀) t _ _ hb
  have h3 := GlobalTheory.FrameEval.evR_frMap_of_isReduced E H Dw l Xo c s.sig s.sig_mem.1 φ y z hz
  have h4 := GlobalTheory.T.normFactor_flatLine_eq_gram_orthonormal_frame E H Dw l Xo c r U x hL τ K y B t₀ m1 m2 F h hh u u' hu hu' σ hσ φ (fun _ => rfl) z hz k w t ho hb
  rw [← h1, h4]
  have h5 : ‖σ (evR Xo c s.sig y)‖ = ‖GlobalTheory.CompHS.diagChar (exOf Dw (flatWt Dw τ) 0) t‖ * ‖toC (evR Xo c s.sig ((U σ₀).un k w))‖ := by
    rw [← norm_mul]
    show ‖toC (φ (evR Xo c s.sig y))‖ = _
    rw [← h3, h2]
    rfl
  rw [h5]
  ring

theorem cInf_eq_frame_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (u : Fin (Dw.mult τ.1) → Fin F.P₀.g → K) (u' : Fin (Dw.mult (conjEmb τ.1)) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F τ.1 u → GlobalTheory.PtDeg.FrameCoord y m1 m2 F (conjEmb τ.1) u' → ∀ σ : K →+* ℂ, s.cInf (σ.comp (algebraMap c.F K)) = ‖σ (evR Xo c s.sig y)‖ * Real.sqrt (h.gram σ u).det.re / Real.sqrt (h.gram σ u').det.re := by
  intro E _ _ _ H Dw l Xo c r U x hL Z τ s K _ _ _ y hy B t₀ m1 m2 F h hh u u' hu hu' σ
  by_cases hσ : GoodEmb c (σ.comp (algebraMap c.F K))
  · exact good_case E H Dw l Xo c r U x hL Z τ s K y hy B t₀ m1 m2 F h hh u u' hu hu' σ hσ
  · set σ' := (starRingEnd ℂ).comp σ
    have e0 : σ'.comp (algebraMap c.F K) = (starRingEnd ℂ).comp (σ.comp (algebraMap c.F K)) := RingHom.comp_assoc _ _ _
    have hσ' : GoodEmb c (σ'.comp (algebraMap c.F K)) := by
      have := goodEmb_goodOf c (σ.comp (algebraMap c.F K))
      rw [goodOf, if_neg hσ] at this
      rw [e0]; exact this
    have hg := good_case E H Dw l Xo c r U x hL Z τ s K y hy B t₀ m1 m2 F h hh u u' hu hu' σ' hσ'
    have hc : s.cInf (σ'.comp (algebraMap c.F K)) = s.cInf (σ.comp (algebraMap c.F K)) := by
      have i1 := s.norm_inf (σ.comp (algebraMap c.F K))
      have i2 := s.norm_inf (σ'.comp (algebraMap c.F K))
      rw [e0, goodOf_conj, i1] at i2
      exact (Set.singleton_eq_singleton_iff.1 i2).symm
    have hgr : ∀ {n : ℕ} (v : Fin n → Fin F.P₀.g → K), (h.gram σ' v).det.re = (h.gram σ v).det.re := fun v => by
      have : h.gram σ' v = (h.gram σ v).map (starRingEnd ℂ) := by
        ext i j
        simp only [ReciprocityTheory.GeometryOfNumbersTheory.HermFam.gram, Matrix.of_apply, Matrix.map_apply]
        exact GlobalTheory.T.lieAlgebraMetric_conjEmbedding_eq_conj K B.pol F h hh σ (v i) (v j)
      rw [this]
      change ((starRingEnd ℂ).mapMatrix (h.gram σ v)).det.re = _
      rw [← RingHom.map_det, Complex.conj_re]
    rw [← hc, hg, hgr, hgr]
    simp only [σ', RingHom.comp_apply, Complex.norm_conj]

end GlobalTheory.PtDegArch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractionLieDerivativeDivPowerCompatFiltration
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.CtrFil

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

theorem ctr_algebraMap' (v : Derivation R B B) (b : B) : ctr v (algebraMap B (DR R B) b) = 0 :=
  CliffordAlgebra.contractLeft_algebraMap _ _ b

theorem ctr_ι' (v : Derivation R B B) (ω : Ω[B⁄R]) :
    ctr v (ι1 ω) = algebraMap B (DR R B) (v.liftKaehlerDifferential ω) :=
  CliffordAlgebra.contractLeft_ι _ _ ω

theorem ctr_mul' (v : Derivation R B B) (x y : DR R B) :
    ctr v (x * y) = ctr v x * y + sgn x * ctr v y := by
  induction x using indDR generalizing y with
  | h b =>
    rw [← Algebra.smul_def, map_smul, ctr_algebraMap', zero_mul, zero_add, AlgHom.commutes, Algebra.smul_def]
  | hd b =>
    rw [ctr_ι', sgn_ι]
    rw [show ctr v (ι1 (D R B b) * y) = _ from CliffordAlgebra.contractLeft_ι_mul _ _ _]
    rw [Algebra.smul_def, neg_mul, sub_eq_add_neg]
    rfl
  | hm x z hx hz =>
    rw [mul_assoc, hx, hz, hx, map_mul]
    simp only [mul_add, add_mul, mul_assoc]
    abel
  | ha x z hx hz =>
    rw [add_mul, map_add, hx, hz, map_add, map_add, add_mul, add_mul]
    abel

theorem ctr_mem_of_span (v : Derivation R B B) {S : Set (DR R B)} {T : Ideal (DR R B)}
    (hST : Ideal.span S ≤ T) (hS : ∀ s ∈ S, ctr v s ∈ T) : ∀ x ∈ Ideal.span S, ctr v x ∈ T := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x hx ih =>
    rw [smul_eq_mul, ctr_mul']
    exact add_mem (Ideal.mul_mem_left _ _ (hST hx))
      (Ideal.mul_mem_left _ _ ih)

end GlobalTheory.CtrFil

namespace GlobalTheory.CtrFil

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {J : Ideal B} (δ : DividedPowers J)
  (v : Derivation R B B)

theorem lie_apply' (x : DR R B) : lie v x = dDR R B (ctr v x) + ctr v (dDR R B x) := rfl

theorem ctr_mem_rel (hv : ∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) {x : DR R B}
    (hx : x ∈ rel R δ) : ctr v x ∈ rel R δ := by
  refine ctr_mem_of_span v le_rfl ?_ x hx
  rintro _ ⟨n, a, ha, rfl⟩
  rw [ctr_ι', map_sub, map_smul, Derivation.liftKaehlerDifferential_comp_D,
    Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul, hv n a ha, sub_self, map_zero]
  exact zero_mem _

theorem lie_mem_rel (hv : ∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) {x : DR R B}
    (hx : x ∈ rel R δ) : lie v x ∈ rel R δ := by
  rw [lie_apply']
  exact add_mem (dDR_mem_rel R δ (ctr_mem_rel δ v hv hx)) (ctr_mem_rel δ v hv (dDR_mem_rel R δ hx))

theorem fil_succ_le' (n : ℕ) : fil δ (n + 1) ≤ fil δ n :=
  Ideal.span_mono fun _ ⟨l, h1, h2, h3⟩ ↦ ⟨l, h1, by omega, h3⟩

theorem filDR_succ_le' (n : ℕ) : filDR R δ (n + 1) ≤ filDR R δ n :=
  sup_le_sup_right (Ideal.span_mono (Set.image_mono (fil_succ_le' δ n))) _

theorem rel_le_filDR' (n : ℕ) : rel R δ ≤ filDR R δ n := le_sup_right

theorem span_le_filDR' (n : ℕ) : Ideal.span (algebraMap B (DR R B) '' fil δ n) ≤ filDR R δ n := le_sup_left

theorem ctr_mem_filDR (hv : ∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) (n : ℕ) {x : DR R B}
    (hx : x ∈ filDR R δ n) : ctr v x ∈ filDR R δ n := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  refine add_mem (ctr_mem_of_span v (span_le_filDR' δ n) ?_ y hy) (rel_le_filDR' δ n (ctr_mem_rel δ v hv hz))
  rintro _ ⟨b, _, rfl⟩
  rw [ctr_algebraMap']
  exact zero_mem _

theorem ι_mem_filDR (n : ℕ) {ω : Ω[B⁄R]} (hω : ω ∈ fil δ n • (⊤ : Submodule B Ω[B⁄R]) ⊔ N1 R δ) :
    ι1 ω ∈ filDR R δ n := by
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hω
  rw [map_add]
  refine add_mem ?_ (rel_le_filDR' δ n hw)
  refine span_le_filDR' δ n ?_
  refine Submodule.smul_induction_on hu (fun c hc ω _ ↦ ?_) (fun x y hx hy ↦ ?_)
  · rw [map_smul, Algebra.smul_def, Algebra.commutes]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨c, hc, rfl⟩)
  · rw [map_add]; exact add_mem hx hy

theorem dDR_mem_filDR (hv : ∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) (n : ℕ) {x : DR R B}
    (hx : x ∈ filDR R δ (n + 1)) : dDR R B x ∈ filDR R δ n := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  refine add_mem ?_ (rel_le_filDR' δ n (dDR_mem_rel R δ hz))
  clear hx
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, rfl⟩ := hy
    rw [dDR_algebraMap]
    refine ι_mem_filDR δ n (GlobalTheory.T.derivation_dividedPowerFiltration_succ_le R B Ω[B⁄R] J δ (D R B) (N1 R δ) ?_ n b hb)
    intro m a ha
    exact Ideal.subset_span ⟨m, a, ha, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x hx ih =>
    rw [smul_eq_mul, dDR_mul]
    refine add_mem (Ideal.mul_mem_left _ _ ih) (Ideal.mul_mem_left _ _ ?_)
    exact filDR_succ_le' δ n (span_le_filDR' δ (n + 1) hx)

theorem lie_mem_filDR (hv : ∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) (n : ℕ) {x : DR R B}
    (hx : x ∈ filDR R δ (n + 1)) : lie v x ∈ filDR R δ n := by
  rw [lie_apply']
  exact add_mem (dDR_mem_filDR δ v hv n (ctr_mem_filDR δ v hv (n + 1) hx))
    (ctr_mem_filDR δ v hv n (dDR_mem_filDR δ v hv n hx))

end GlobalTheory.CtrFil

open GlobalTheory.CtrFil in

theorem GlobalTheory.PDForm.ctr_lie_rel_filDR : (∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B)
    (δ : DividedPowers J) (v : Derivation R B B), (∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) →
    ∀ x ∈ rel R δ, ctr v x ∈ rel R δ ∧ lie v x ∈ rel R δ) ∧ ∀ (R B : Type) [CommRing R] [CommRing B]
    [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (v : Derivation R B B),
    (∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) → ∀ n, (∀ x ∈ filDR R δ n, ctr v x ∈ filDR R δ n) ∧
    (∀ x ∈ filDR R δ (n + 1), dDR R B x ∈ filDR R δ n) ∧ ∀ x ∈ filDR R δ (n + 1), lie v x ∈ filDR R δ n :=
  ⟨fun _ _ _ _ _ _ δ v hv _ hx ↦ ⟨ctr_mem_rel δ v hv hx, lie_mem_rel δ v hv hx⟩,
    fun _ _ _ _ _ _ δ v hv n ↦ ⟨fun _ hx ↦ ctr_mem_filDR δ v hv n hx, fun _ hx ↦ dDR_mem_filDR δ v hv n hx,
      fun _ hx ↦ lie_mem_filDR δ v hv n hx⟩⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateDividesOnNonzeroLocusSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.ThetaDiv

theorem resG_top_injective {X : Scheme.{0}} {W : X.Opens} (hW : ⊤ ≤ W) :
    Function.Injective (resG X (le_top : W ≤ ⊤)) := by
  obtain rfl : W = ⊤ := top_le_iff.1 hW
  intro x y h
  have e : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (Opposite.op (⊤ : X.Opens)) := rfl
  simpa only [resG, e, CategoryTheory.Functor.map_id, CommRingCat.hom_id, RingHom.id_apply] using h

theorem div_of_mem_nonzeroLocus : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : ZH.RatModel o Ω) (δ : LB M.Z) {I : Type} (t : I → δ.Sec) (th : I → Ω), δ.IsLB → ZM.SecCoord δ t M.pt th → ∀ (a : I) (z : M.Z), z ∈ nonzeroLocus (t a) → M.Div th a z := by
  intro o Ω _ _ _ M δ I t th _ hsc a z hz
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  have hDU : M.Z.basicOpen ((t a).f k) ≤ δ.U k := M.Z.basicOpen_le _
  have hD : ((M.Z.basicOpen ((t a).f k) : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hk⟩
  have hptD := M.top_le_preimage_pt hD
  have hptU : ⊤ ≤ M.pt ⁻¹ᵁ δ.U k := fun x hx => hDU (hptD hx)
  obtain ⟨τ, -, hτ⟩ := hsc
  let j : PUnit → δ.ι := fun _ => k
  have hj : (δ.pull M.pt).U j ≤ M.pt ⁻¹ᵁ δ.U (j PUnit.unit) := LB.wchart_le δ _ j PUnit.unit
  have hW : ⊤ ≤ (δ.pull M.pt).U j := fun x _ => Set.mem_iInter.2 fun _ => hptU (x := x) trivial
  have inj := resG_top_injective hW
  let e := Scheme.ΓSpecIso (CommRingCat.of Ω)
  have hc : ∀ b, resG (Sp Ω) (le_top : (δ.pull M.pt).U j ≤ ⊤) ((M.pt.appLE (δ.U k) ⊤ hptU).hom ((t b).f k)) =
      resG (Sp Ω) le_top (e.inv.hom (th b)) * (τ.s j).val := by
    intro b
    rw [← hτ b j hj]
    show (M.pt.appLE _ ⊤ hptU ≫ (Sp Ω).presheaf.map (homOfLE le_top).op).hom _ = _
    rw [Scheme.Hom.appLE_map]
  have hv : ∀ b, valF M.pt (δ.U k) ((t b).f k) = e.hom.hom ((M.pt.appLE (δ.U k) ⊤ hptU).hom ((t b).f k)) :=
    fun b => dif_pos hptU
  have hei : ∀ x : Ω, e.hom.hom (e.inv.hom x) = x := fun x => by
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  have key : ∀ b, valF M.pt (δ.U k) ((t b).f k) * th a = valF M.pt (δ.U k) ((t a).f k) * th b := by
    intro b
    have h1 : (M.pt.appLE (δ.U k) ⊤ hptU).hom ((t b).f k) * e.inv.hom (th a) =
        (M.pt.appLE (δ.U k) ⊤ hptU).hom ((t a).f k) * e.inv.hom (th b) := by
      apply inj
      rw [map_mul, map_mul, hc b, hc a]
      ring
    have h2 := congrArg e.hom.hom h1
    rwa [map_mul, map_mul, hei, hei, ← hv, ← hv] at h2
  have hua : valF M.pt (δ.U k) ((t a).f k) ≠ 0 :=
    ((GlobalTheory.Points.le_preimage_basicOpen_iff M.pt hptU ((t a).f k)).1 hptD).ne_zero
  have hth : th a ≠ 0 := by
    intro h0
    apply hua
    rw [hv]
    have h1 := hc a
    rw [h0, map_zero, map_zero, zero_mul] at h1
    rw [inj (h1.trans (map_zero _).symm), map_zero]
  refine ⟨hth, fun b => ?_⟩
  have hu : IsUnit (resG M.Z hDU ((t a).f k)) :=
    RingedSpace.isUnit_res_basicOpen M.Z.toLocallyRingedSpace.toRingedSpace ((t a).f k)
  have hval : valF M.pt _ (resG M.Z hDU ((t b).f k) * ((hu.unit⁻¹ : (Γ(M.Z, M.Z.basicOpen ((t a).f k)))ˣ) : Γ(M.Z, M.Z.basicOpen ((t a).f k)))) = th b / th a := by
    rw [← ZH.RatModel.res_apply M _ hD, map_mul, map_units_inv, IsUnit.unit_spec, ZH.RatModel.res_resG,
      ZH.RatModel.res_resG, ZH.RatModel.res_apply, ZH.RatModel.res_apply]
    field_simp
    linear_combination key b
  exact hval ▸ ZH.RatModel.valF_mem_O hk _

end GlobalTheory.ThetaDiv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleCotangentValueBaseChangeNatura
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem val_sub_pull {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {Y Y' : Scheme.{0}}
    {t : Y ⟶ Sp R} {t' : Y' ⟶ Sp R'} {φ : Y' ⟶ Y} (m : IsMor (dp0 R) t (dp0 R') t' σ φ)
    (E : SqExt R) (E' : SqExt R') (ρ : E.C →+* E'.C) (ρ₀ : E.B →+* E'.B)
    (hρ : ∀ r, ρ (algebraMap R E.C r) = algebraMap R' E'.C (σ r))
    (hρ₀ : ∀ r, ρ₀ (algebraMap R E.B r) = algebraMap R' E'.B (σ r))
    (hπ : ∀ c, ρ₀ (E.π c) = E'.π (ρ c)) (hi : ∀ b, ρ (E.i b) = E'.i (ρ₀ b))
    {T₀ : Thick (dp0 R) t} {T₀' : Thick (dp0 R') t'} (a : T₀ ⟶ m.obj T₀')
    (z : Sp E.C ⟶ Y) (hz : z ≫ t = spMap (algebraMap R E.C))
    (z' : Sp E'.C ⟶ Y') (hz' : z' ≫ t' = spMap (algebraMap R' E'.C))
    (τ : T₀ ⟶ Thick.triv E.C z hz) (τ' : T₀' ⟶ Thick.triv E'.C z' hz')
    (h : ∀ c, ρ (τ.φ c) = τ'.φ (a.φ c)) (f : Z1 (O (dp0 R) t)) :
    ∃ b : E'.B, E'.val z' hz' (m.coef.pullbackOneCocycle f) - ev (m.coef.pullbackOneCocycle f) τ' =
      ρ (E.val z hz f - ev f τ) + τ'.φ (ev f a) - E'.i b := by
  have e : spMap ρ ≫ z = z' ≫ φ := by
    let u : T₀.B₀ →+* E.C := τ.φ₀
    let u' : T₀'.B₀ →+* E'.C := τ'.φ₀
    let a₀ : T₀.B₀ →+* T₀'.B₀ := a.φ₀
    have h1 : spMap u ≫ T₀.x = z := τ.pt
    have h2 : spMap u' ≫ T₀'.x = z' := τ'.pt
    have h3 : spMap a₀ ≫ T₀.x = T₀'.x ≫ φ := a.pt
    rw [← h1, ← h2, Category.assoc, ← h3, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 2
    refine RingHom.ext fun c ↦ ?_
    obtain ⟨c, rfl⟩ := T₀.surj c
    exact (congrArg ρ (τ.comm c)).trans ((h c).trans
      ((τ'.comm (a.φ c)).symm.trans (congrArg τ'.φ₀ (a.comm c).symm)))
  have e₀ : spMap ρ₀ ≫ spMap (E.π : E.C →+* E.B) ≫ z = (spMap (E'.π : E'.C →+* E'.B) ≫ z') ≫ φ := by
    rw [Category.assoc, ← e, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 2
    exact RingHom.ext hπ
  let Φ : E.thick _ (E.red_w hz) ⟶ m.obj (E'.thick _ (E'.red_w hz')) :=
    { φ := { ρ with commutes' := hρ }
      φ₀ := ρ₀
      comm := hπ
      dp := isDPMorphism_sqDP E.sq E'.sq _ fun c hc ↦ by
        have hc' : E.π c = 0 := hc
        change E'.π (ρ c) = 0
        rw [← hπ, hc', map_zero]
      pt := e₀ }
  let b : Thick.triv E.B _ (E.red_w hz) ⟶ m.obj (Thick.triv E'.B _ (E'.red_w hz')) :=
    Thick.trivHom { ρ₀ with commutes' := hρ₀ } e₀
  have k1 := ev_sq f b (m.functor.map (E'.secHom (E'.red_w hz') E'.i E'.π_i))
    (E.secHom (E.red_w hz) E.i E.π_i) Φ fun c ↦ (hi c).symm
  have k2 := ev_sq f a (m.functor.map (τ' ≫ E'.idHom hz')) (τ ≫ E.idHom hz) Φ fun c ↦ (h c).symm
  have k3 := ev_comp f τ (E.idHom hz)
  have k4 := ev_comp (m.coef.pullbackOneCocycle f) τ' (E'.idHom hz')
  have key : ∀ (A B C : E.C) (x y u v w k l : E'.C) (N : E.C), x + y = ρ A + w → l + k = ρ N + w → N = C + B →
      k = v + u → y - u - v = ρ (A - B - C) + l - x := fun A B C x y u v w k l N h1 h2 h3 h4 ↦ by
    subst h3 h4
    rw [map_add] at h2
    rw [map_sub, map_sub]
    linear_combination h1 - h2
  exact ⟨ev f b, key _ _ _ _ _ _ _ _ _ _ _ k1 k2 k3 k4⟩

attribute [local instance] cotOp cotCentral cotTower

def cotRingHom {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {D D' : Type} [CommRing D] [Bialgebra R D]
    [CommRing D'] [Bialgebra R' D'] (s : SemiBialgHom σ D D') :
    TrivSqZeroExt R (Cot R D) →+* TrivSqZeroExt R' (Cot R' D') where
  toFun c := TrivSqZeroExt.inl (σ c.fst) + TrivSqZeroExt.inr (s.cot c.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [map_smulₛₗ]

theorem cotVal_pull : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X : Over (Sp R)) (X' : Over (Sp R')) (φ : X'.left ⟶ X.left) (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R') (X'.hom ≫ 𝟙 _) σ φ) (D D' : Type) [CommRing D] [Bialgebra R D] [CommRing D'] [Bialgebra R' D'] (s : SemiBialgHom σ D D') (y : Pt X D) (y' : Pt X' D') (a : trivAt y ⟶ m.obj (trivAt y')) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))), (∀ r, a.φ r = s r) → cotVal (m.coef.pullbackOneCocycle f) y' = s.cot (cotVal f y) + dUnit R' (show D' from ev f a) := by
  intro R R' _ _ σ X X' φ m D D' _ _ _ _ s y y' a f ha
  have hf : ∀ c, (cotRingHom s c).fst = σ c.fst := fun c ↦ add_zero _
  have hs : ∀ c, (cotRingHom s c).snd = s.cot c.snd := fun c ↦ zero_add _
  have pf : ∀ c : D, TrivSqZeroExt.fst (cotPt R D c) = Coalgebra.counit c := fun c ↦ add_zero _
  have ps : ∀ c : D, TrivSqZeroExt.snd (cotPt R D c) = dUnit R c := fun c ↦ zero_add _
  have pf' : ∀ c : D', TrivSqZeroExt.fst (cotPt R' D' c) = Coalgebra.counit c := fun c ↦ add_zero _
  have ps' : ∀ c : D', TrivSqZeroExt.snd (cotPt R' D' c) = dUnit R' c := fun c ↦ zero_add _
  obtain ⟨b, hb⟩ := val_sub_pull m (cotExt R D) (cotExt R' D') (cotRingHom s) σ
    (fun r ↦ TrivSqZeroExt.ext (hf _) ((hs _).trans (map_zero _))) (fun _ ↦ rfl) (fun c ↦ (hf c).symm)
    (fun r ↦ TrivSqZeroExt.ext (hf _) ((hs _).trans (map_zero _))) a
    (spOver (cotPt R D) ≫ y).left (Pt.w _) (spOver (cotPt R' D') ≫ y').left (Pt.w _)
    (trivMap (cotPt R D) y) (trivMap (cotPt R' D') y') (fun c ↦ by
      change cotRingHom s (cotPt R D c) = cotPt R' D' (a.φ c)
      rw [ha]
      ext
      · rw [hf, pf, pf', s.counit_map]
      · rw [hs, ps, ps', s.cot_d]) f
  refine (congrArg (cotSnd R' D') hb).trans ?_
  rw [map_sub, map_add]
  refine (sub_zero _).trans ?_
  exact congrArg₂ (· + ·) (hs _) (ps' _)

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DataLink
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

namespace GlobalTheory.MassLink

theorem data_link : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m), letI : IsCMField D.host.E := D.host.isCMField_hostE; ∃ (G : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin D.R.r → D.host.E)) (Ψ : Finset (D.host.E →+* ℂ)) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ D.R.r) (p0 : Ψ → ℕ) (J : Type) (s : J → Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) (h : J → Theta.GA D (Wc D i)), (2 ≤ D.R.r ∧ GlobalTheory.UCls.Unr D.host.E ∧ GlobalTheory.UCls.SelfDualLat G Λ ∧ (∀ τ : D.host.E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) ∧ (∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin D.R.r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ)) ∧ GlobalTheory.SUVol.IsSReps G (Λ : Set (Fin D.R.r → D.host.E)) 1 s ∧ ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f) ∧ (G = Matrix.transpose ((HSpace.gram (Wc D i)).submatrix (Fin.cast (rank_Wc i).symm) (Fin.cast (rank_Wc i).symm)) ∧ (∃ eΨ : D.what₂.Tau ≃ Ψ, ∀ ρ, ((eΨ ρ : Ψ) : D.host.E →+* ℂ) = TH.tauE D ρ) ∧ (∀ j, h j ∈ Theta.GfC (Wc D i)) ∧ (∀ (j j' : J) (g : Theta.GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E), g ∈ Theta.GQ (Wc D i) → Theta.matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → Formalism.IndefR.Lev.finE (Wc D i) ((h j')⁻¹ * g * h j) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) → IsIntegral ℤ (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).det ∧ ((γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).det = 1 → j = j')) ∧ (∀ (j : J) (g : Theta.GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E) (γr : GL (Fin D.R.r) D.host.E), g ∈ Theta.GQ (Wc D i) → Theta.matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ → (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).submatrix (Fin.cast (rank_Wc i).symm) (Fin.cast (rank_Wc i).symm) = (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) → (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).det = 1 → Formalism.IndefR.Lev.finE (Wc D i) ((h j)⁻¹ * g * h j) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) → γr ∈ GlobalTheory.SUVol.ratStab G (Λ : Set (Fin D.R.r → D.host.E)) (s j))) := by
  intro D Tu Cl t0 hCl i
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨hcm, eΨ, heΨ⟩ := GlobalTheory.T.cm_type_from_conjugate_complement D
  obtain ⟨x, p0, hx⟩ := GlobalTheory.T.gram_matrix_of_mass_frame_diagonal D i
  obtain ⟨J, s, hs⟩ := GlobalTheory.T.special_unitary_representatives_exist D Tu Cl t0 hCl i
  refine ⟨gm D i, lat Cl i, psi D, x, p0, J, s, fun j => lift D i (s j),
    ⟨(GlobalTheory.T.two_le_hermitianRank_and_hostDegree_eq D).1, GlobalTheory.T.unramified_class_of_cm_host D, GlobalTheory.T.self_dual_lattice_of_level_class D Tu Cl t0 hCl i, hcm, hx, hs, (GlobalTheory.T.two_le_hermitianRank_and_hostDegree_eq D).2⟩, rfl,
    ⟨eΨ, heΨ⟩, fun j => (GlobalTheory.T.special_unitary_lift_in_theta_group D i (s j) (hs.1 j)).1, GlobalTheory.T.special_unitary_representatives_theta_compatible D Tu Cl t0 hCl i J s hs,
    fun j g γ γr hg hm hr hd hk => GlobalTheory.T.special_unitary_rational_matrix_compatible D Tu Cl t0 hCl i (s j) (hs.1 j) g γ γr hg hm hr hd hk⟩

end GlobalTheory.MassLink
end

