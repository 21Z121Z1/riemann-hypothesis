import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0044
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateAny
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0175
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0178
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2199
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2567
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2800
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2824
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2242
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2007
import Formalism.LocalRingCardinality.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2756
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2980
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2964
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2730
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2952
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3027
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0018
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReflectionSumJetNumber
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.JetsCharZero

theorem num_le (dF R N r g0 g1 cst : ℝ) (hR : 0 ≤ R) (hN : 0 ≤ N) (hr : 0 ≤ r) (hg0 : 0 < g0) (hle : g0 ≤ g1)
    (h : R * N ^ 3 * (r * N / 4 + 2 * dF ^ 2) / g0 ≤ cst) : dF ^ 2 * (R * N ^ 3) / g1 ≤ cst := by
  have hX : 0 ≤ R * N ^ 3 := by positivity
  refine le_trans ?_ h
  calc dF ^ 2 * (R * N ^ 3) / g1 ≤ dF ^ 2 * (R * N ^ 3) / g0 := div_le_div_of_nonneg_left (by positivity) hg0 hle
    _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hg0.le
        have : dF ^ 2 ≤ r * N / 4 + 2 * dF ^ 2 := by nlinarith [sq_nonneg dF, mul_nonneg hr hN]
        nlinarith [mul_le_mul_of_nonneg_left this hX]

theorem exists_thRule_value_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (IsLocalRing.maximalIdeal T.V) C.I.G), P.TorsionIso → CharZero (IsLocalRing.ResidueField T.V) → ∀ (φ : ℝ), GlobalTheory.SlopeRec.HasPhi y φ → ∀ (α : 𝓞 E) (q : ℕ), α * star α = ((q : ℕ) : 𝓞 E) → q ∣ l.M → l.Mb ≤ Ideal.span {star α} → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∑ f : Lt1 Dw, 2 * rk f ≤ n → 1 ≤ n → ∀ (N cst : ℝ), ((Module.finrank ℚ E * Dw.q : ℕ) : ℝ) ≤ N → 4 * DF Dw a + 4 ≤ q → (DF Dw a : ℝ) * (2 * Real.sqrt N) < q → (DF Dw a : ℝ) ^ 2 * ((|(discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) / (2 * Module.finrank ℚ E) * N ^ 3) / q ≤ cst → ∃ f ∈ thGen Xo c nab a n, evI y f ≠ 0 ∧ (vV T.V (evI y f) : ℝ) ≤ cst * φ := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab T io y C hTr P hP hch φ hφ α q hα hq hMb a n hanti hs hn N cst hρN h4 hM0 hcst
  obtain ⟨P₁, hP₁, hB⟩ := GlobalTheory.T.exists_harmonicPoly_localInvariant_nonpos_char0 E H Dw l Xo c a n hanti hs
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  obtain ⟨⟨Q, hQ⟩, -⟩ := GlobalTheory.PowData.exists_powData E H Dw l Xo c T io y C P ϖ hϖ
  obtain ⟨ρ, hρ, hSB⟩ := GlobalTheory.ShortPhi.exists_shortBasis E H Dw l Xo c T io y φ hφ C P ϖ hϖ Q hQ
  set R : ℝ := |(discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E) / (2 * Module.finrank ℚ E) with hR
  have hR0 : 0 ≤ R := by positivity
  have hρN' : (ρ : ℝ) ≤ N := le_trans (by exact_mod_cast hρ) hρN
  have hρ0 : (0 : ℝ) ≤ ρ := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N := hρ0.trans hρN'
  have hM0' : (DF Dw a : ℝ) * (2 * Real.sqrt ρ) < q := lt_of_le_of_lt (by gcongr) hM0
  have hup := GlobalTheory.T.iInf_thetaRule_le_localValue_charZero E H Dw l Xo c nab hnab T io y C hTr P hP hch ϖ hϖ Q hQ ρ _ _ hSB α q hα hq hMb a n 1 hn one_pos h4
    hM0' P₁ hP₁
  have hloc := hB T io y C hch 1 l.M one_pos
  have hφ0 := hφ.nonneg
  have hq0 : (0 : ℝ) < q := by
    have h : 0 < q := by omega
    exact_mod_cast h
  set B : ℝ := (DF Dw a : ℝ) ^ 2 * (R * (ρ : ℝ) ^ 3 * φ) / q / ((1 : ℕ) : ℝ) with hBdef
  have hBle : B ≤ cst * φ := by
    rw [hBdef, Nat.cast_one, div_one]
    calc (DF Dw a : ℝ) ^ 2 * (R * (ρ : ℝ) ^ 3 * φ) / q ≤ (DF Dw a : ℝ) ^ 2 * (R * N ^ 3 * φ) / q := by gcongr
      _ = (DF Dw a : ℝ) ^ 2 * (R * N ^ 3) / q * φ := by ring
      _ ≤ cst * φ := by gcongr
  have hinf : (⨅ (f : Rul Xo c) (_ : ∃ x : Fin n → Dw.La, IsThRule Xo c nab x P₁ f), nval T.V 1 (evI y f)) ≤
      ((B : ℝ) : EReal) := by
    refine hup.trans ?_
    calc _ ≤ (0 : EReal) + ((B : ℝ) : EReal) := add_le_add hloc le_rfl
      _ = _ := zero_add _
  by_contra hne
  push_neg at hne
  have hlow : (((⌊B⌋ + 1 : ℤ) : ℝ) : EReal) ≤
      ⨅ (f : Rul Xo c) (_ : ∃ x : Fin n → Dw.La, IsThRule Xo c nab x P₁ f), nval T.V 1 (evI y f) := by
    refine le_iInf₂ fun f ⟨x, hx⟩ => ?_
    have hf : f ∈ thGen Xo c nab a n := ⟨x, P₁, hP₁, hx⟩
    by_cases h0 : evI y f = 0
    · rw [h0, nval_zero]; exact le_top
    have h1 := hne f hf h0
    rw [nval_of_ne h0, Nat.cast_one, div_one, EReal.coe_le_coe_iff]
    have h2 : B < (vV T.V (evI y f) : ℝ) := lt_of_le_of_lt hBle h1
    have h3 : ⌊B⌋ < vV T.V (evI y f) := Int.floor_lt.2 h2
    exact_mod_cast h3
  have h5 := EReal.coe_le_coe_iff.1 (hlow.trans hinf)
  push_cast at h5
  linarith [Int.lt_floor_add_one B]

theorem exists_thRule_value_le_cover : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), ∀ cst : ℝ, GlobalTheory.RefSum.JetNum (Fm.D x ι) (DF (dat p i) (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)))) cst → letI := p.T.Q.H.starRing; ∀ (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∀ (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (C : IntegralChartA3 Y.d.Xo₂ Y.d.c₂ T io y') (P : PELUnif (IsLocalRing.maximalIdeal T.V) C.I.G) (φT : ℝ), CharZero (IsLocalRing.ResidueField T.V) → Formalism.MainNotions.ModuliIntegralCharts.H1.FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → P.TorsionIso → GlobalTheory.SlopeRec.HasPhi y' φT → ∃ f ∈ thGen Y.d.Xo₂ Y.d.c₂ nab (GlobalTheory.RefSum.thA (dat p i) la (GlobalTheory.RefSum.nCol (dat p i))) (GlobalTheory.RefSum.nCol (dat p i)), evI y' f ≠ 0 ∧ (vV T.V (evI y' f) : ℝ) ≤ cst * φT := by
  intro h1 h2 h3 h4
  have hA := GlobalTheory.T.host_field_degree_divisibility h1 h2 h3 h4
  have hG := GlobalTheory.LiftGaps.lift_gaps h3
  unfold Covers Lifts Formalism.MainNotions.Closed at hA hG ⊢
  obtain ⟨ε1, hε1, hA⟩ := hA
  obtain ⟨ε2, hε2, hG⟩ := hG
  refine ⟨min ε1 ε2, lt_min hε1 hε2, fun eps he hle => ?_⟩
  obtain ⟨K1, hK1⟩ := hA eps he (hle.trans (min_le_left _ _))
  obtain ⟨K2, hK2⟩ := hG eps he (hle.trans (min_le_right _ _))
  refine ⟨⟨max K1.pre K2.pre, fun l => max (K1.t l) (K2.t l), fun l => max (K1.mid l) (K2.mid l),
    fun l => max (K1.last l) (K2.last l)⟩, fun Fm CH hF hL => ?_⟩
  have hL1 : Fm.Large K1 CH := ⟨fun c hc => (le_max_left _ _).trans (hL.1 c hc), trivial,
    fun c hc => (le_max_left _ _).trans (hL.2.2.1 c hc), fun c hc => (le_max_left _ _).trans (hL.2.2.2 c hc)⟩
  have hL2 : Fm.Large K2 CH := ⟨fun c hc => (le_max_right _ _).trans (hL.1 c hc), trivial,
    fun c hc => (le_max_right _ _).trans (hL.2.2.1 c hc), fun c hc => (le_max_right _ _).trans (hL.2.2.2 c hc)⟩
  obtain ⟨C1, hC1, hE1⟩ := hK1 Fm CH hF hL1
  obtain ⟨C2, -, hE2⟩ := hK2 Fm CH hF hL2
  refine ⟨C1, hC1, ?_⟩
  obtain ⟨x1, hx1⟩ := hE1.and hE2
  refine ⟨x1, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hAi, hGi⟩ := hx1 x hx hle ι p hp
  obtain ⟨α, hα, hdvd, hMb, hρq⟩ := hAi i hi Y hY
  obtain ⟨hp1, hgap⟩ := hGi i hi Y hY
  intro la hla cst hJ nab hnab T io y' C P φT hch hTr hP hφ
  obtain ⟨hanti, hgp⟩ := hgap la hla
  have hbd : ∀ (τ : AllWt.Psi p.T.Q.H) (k : Fin ((dat p i).p + (dat p i).q)),
      |((la τ k : ℤ) : ℝ)| ≤ ∑ τ' : AllWt.Psi p.T.Q.H, ∑ k' : Fin ((dat p i).p + (dat p i).q), |((la τ' k' : ℤ) : ℝ)| :=
    fun τ k => (Finset.single_le_sum (f := fun k' => |((la τ k' : ℤ) : ℝ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ k)).trans (Finset.single_le_sum (f := fun τ' => ∑ k' : Fin ((dat p i).p + (dat p i).q),
        |((la τ' k' : ℤ) : ℝ)|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ τ))
  have hEven : Even (GlobalTheory.RefSum.nCol (dat p i)) := by
    unfold GlobalTheory.RefSum.nCol
    exact ⟨4 * ((∑ f : Lt1 (dat p i), 2 * rk f) / 8 + Fintype.card (Lt1 (dat p i)) + 1), by ring⟩
  have hn1 : 1 ≤ GlobalTheory.RefSum.nCol (dat p i) := by unfold GlobalTheory.RefSum.nCol; omega
  obtain ⟨hDom, -⟩ := GlobalTheory.RefSum.thA_dominant_lastPos_degree _ _ (dat p i) la (GlobalTheory.RefSum.nCol (dat p i)) _ hp1 hEven
    hanti hgp hbd
  have hg0 : 2 ≤ (Fm.D x ι).host.g 0 := ((Fm.D x ι).host.g_prime 0).two_le
  have hg1 : 2 ≤ (Fm.D x ι).host.g 1 := ((Fm.D x ι).host.g_prime 1).two_le
  obtain ⟨j1, j2, j3⟩ := hJ 0
  have hle0 : (Fm.D x ι).host.g 0 ≤ (Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 := Nat.le_mul_of_pos_right _ (by omega)
  have hle0' : ((Fm.D x ι).host.g 0 : ℝ) ≤ (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) := by exact_mod_cast hle0
  have hg0' : (0 : ℝ) < (Fm.D x ι).host.g 0 := by exact_mod_cast (show 0 < (Fm.D x ι).host.g 0 by omega)
  have hN0 : (0 : ℝ) ≤ 2 * ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.m := by positivity
  have hR0 : 0 ≤ GlobalTheory.PtTie.rr0 (Fm.D x ι) := by unfold GlobalTheory.PtTie.rr0; positivity
  exact exists_thRule_value_le _ _ _ _ Y.d.Xo₂ Y.d.c₂ nab hnab T io y' C hTr P hP hch φT hφ α _ hα hdvd hMb _ _ hDom.1
    GlobalTheory.RefSum.sum_le_nCol hn1 (2 * ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.m) cst (by exact_mod_cast hρq) (j1.trans hle0)
    (lt_of_lt_of_le j2 hle0') (num_le _ _ _ _ _ _ _ hR0 hN0 (Nat.cast_nonneg _) hg0' hle0' j3)

end GlobalTheory.JetsCharZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentationInputsAllParts
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind

namespace GlobalTheory.Fc.Ind

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem atAll_fourRows : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ (𝒜 : FamClass) (σ : RawSel Part 𝒜),
      AtAll PFire 𝒜 σ ∧ AtAll PRB 𝒜 σ ∧ AtAll PThR 𝒜 σ ∧ AtAll PFrames 𝒜 σ := by
  intro hDS hHC hRD hCW 𝒜 σ
  have hF : AtAll PFire 𝒜 σ := fun Fm hc x hx i =>
    GlobalTheory.T.indefinite_scale_theta_equality hDS hHC hRD hCW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B
  refine ⟨hF, fun Fm hc x hx i => ?_, fun Fm hc x hx i => ?_, fun Fm hc x hx i => ?_⟩
  · exact GlobalTheory.T.indefinite_scale_theta_bound_right hRD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B (Fm.parT x hx i).nV_ge (hF Fm hc x hx i).1
  · exact GlobalTheory.T.indefinite_scale_theta_identity _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B.Q (σ Fm hc x hx i).Rr (hF Fm hc x hx i).1
  · exact GlobalTheory.T.indefinite_scale_theta_sum _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B.Q (σ Fm hc x hx i).pins

end GlobalTheory.Fc.Ind

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeEqOneOfComp
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt GlobalTheory.VB GlobalTheory.GenSmoothCover

namespace GlobalTheory.GenRes

theorem bijective_residueFieldMap {A B : Scheme.{0}} (f : A ⟶ B) [SurjectiveOnStalks f] (x : A) :
    Function.Bijective (f.residueFieldMap x).hom := by
  refine ⟨RingHom.injective _, fun a => ?_⟩
  obtain ⟨b, rfl⟩ := A.residue_surjective x a
  obtain ⟨c, rfl⟩ := f.stalkMap_surjective x b
  exact ⟨B.residue _ c, congr($(Scheme.residue_residueFieldMap f x).hom c)⟩

theorem residueDegree_eq_one_of_comp {A B C : Scheme.{0}} (g : A ⟶ B) (c : B ⟶ C) (a : A)
    (h : Function.Bijective ((g ≫ c).residueFieldMap a).hom) : c.residueDegree (g a) = 1 := by
  rw [Scheme.residueFieldMap_comp] at h
  have hs : Function.Surjective (c.residueFieldMap (g a)).hom := fun y => by
    obtain ⟨x, hx⟩ := h.2 ((g.residueFieldMap a).hom y)
    exact ⟨x, (g.residueFieldMap a).hom.injective hx⟩
  have hb : Function.Bijective (c.residueFieldMap (g a)).hom := ⟨RingHom.injective _, hs⟩
  letI := (c.residueFieldMap (g a)).hom.toAlgebra
  unfold Scheme.Hom.residueDegree
  exact (LinearEquiv.finrank_eq (AlgEquiv.ofBijective (Algebra.ofId _ _) hb).toLinearEquiv).symm.trans
    (Module.finrank_self _)

theorem exists_birational_genSmooth : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp k) (d : ℕ), IsArithVar p d → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (ρ : Y ⟶ X),
      IsArithVar (ρ ≫ p) d ∧ GenSmooth (ρ ≫ p) d ∧ ρ (genericPoint Y) = genericPoint X ∧
        ρ.residueDegree (genericPoint Y) = 1 := by
  intro hP k _ X _ p D h
  have := h.isDomain
  have := h.finite
  have := h.charZero_base
  have := h.isNoetherianRing
  let K := FractionRing k
  have G := IsPullback.of_hasPullback p (spMap (algebraMap k K))
  set f := pullback.fst p (spMap (algebraMap k K))
  set q := pullback.snd p (spMap (algebraMap k K))
  obtain ⟨_, hd, hf⟩ := genericFibre h G
  have hq : IsProjOver q := ProjSpace.isProjOver_of_isPullback_spMap _ G h.isProjOver
  obtain ⟨W, s, U, _, hsm, hW, hU, hiso⟩ := WeakRes.weak_resolution hP K _ q D hq hd
  have : IsProper q := CommonModel.isProper_of_isProjOver hq
  have : IsProper (s ≫ q) := CommonModel.isProper_of_isProjOver hW
  have hdW : topologicalKrullDim W = D :=
    (OpenDim.topologicalKrullDim_eq_of_isIso_restrict K _ W q (s ≫ q) s inferInstance inferInstance rfl U hU hiso).trans hd
  obtain ⟨Y, ρ, _, j, hj, hY, H, _, _⟩ := exists_closure h.isProjOver (s ≫ f) (s ≫ q)
    (by rw [Category.assoc, Category.assoc, G.w]) hW
  have : IsProper (ρ ≫ p) := CommonModel.isProper_of_isProjOver hY
  have : IsFinite (spMap (Int.castRingHom k)) := (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 h.finite)
  have H' := H.paste_vert (isPullback_rat k K)
  have : Flat (j ≫ (ρ ≫ p) ≫ spMap (Int.castRingHom k)) := flat_of_over_fractionField (K := ℚ) _ _ H'.w.symm
  have hfl : Flat ((ρ ≫ p) ≫ spMap (Int.castRingHom k)) := flat_of_schemeDominant_of_isDedekindDomain j _
  have hA : IsArithVar (ρ ≫ p) D :=
    ⟨h.isDomain, h.finite, ‹_›, hY, hfl, IntModel.topologicalKrullDim_eq_succ Int.not_isField H' hdW⟩
  obtain ⟨_, -, hjη⟩ := genericFibre hA H
  obtain ⟨x, hx⟩ := hU
  have : Nonempty (s ⁻¹ᵁ U : W.Opens).toScheme := ⟨inv (s ∣_ U) ⟨x, hx⟩⟩
  have : IsIntegral (s ⁻¹ᵁ U : W.Opens).toScheme := isIntegral_of_isOpenImmersion (s ⁻¹ᵁ U).ι
  have e : ((s ⁻¹ᵁ U).ι ≫ j) ≫ ρ = (s ∣_ U ≫ U.ι) ≫ f := by
    rw [Category.assoc, hj, morphismRestrict_ι, Category.assoc]
  have eη : ((s ⁻¹ᵁ U).ι ≫ j) (genericPoint _) = genericPoint Y := by
    rw [Scheme.Hom.comp_apply, genericPoint_eq_of_isOpenImmersion, hjη]
  have := IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)
  have : IsPreimmersion f := MorphismProperty.of_isPullback G.flip this
  refine ⟨Y, ‹_›, ρ, hA, fun σ => ?_, ?_, ?_⟩
  · have : LocallyOfFinitePresentation (ρ ≫ p) := inferInstance
    exact ⟨⟨AlgChart (ρ ≫ p) σ D, id, ModelCharts.exists_chart H (RegGenSmooth.injective_of_charZero σ)⟩⟩
  · rw [← eη, ← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, genericPoint_eq_of_isOpenImmersion, hf]
  · have : SurjectiveOnStalks (((s ⁻¹ᵁ U).ι ≫ j) ≫ ρ) := by rw [e]; infer_instance
    rw [← eη]
    exact residueDegree_eq_one_of_comp _ ρ _ (bijective_residueFieldMap _ _)

end GlobalTheory.GenRes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldLinearIndependentClosedFibreGenericPStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueField_linearIndependent_closedFibre_genericPoints : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → ∀ (n : ℕ) (u : Fin n → H.left.functionField), (∀ i, GlobalTheory.Cartier.RegAt y (u i)) → (∀ c : Fin n → T, GlobalTheory.Cartier.ZeroAt y (∑ i, GlobalTheory.Desc.cst H.hom (c i) * u i) → ∀ i, c i ∈ maximalIdeal T) → ∀ d : Fin n → D, GlobalTheory.Cartier.ZeroAt y' (∑ i, GlobalTheory.Desc.cst H'.hom (d i) * θ (u i)) → ∀ i, d i ∈ maximalIdeal D := by
  first | exact @GlobalTheory.Desc.ResInj.residue_linearIndependent | exact GlobalTheory.Desc.ResInj.residue_linearIndependent | (intros; apply GlobalTheory.Desc.ResInj.residue_linearIndependent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingBoundOfDeepGood
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.RingStep

set_option maxHeartbeats 1000000 in

theorem ring_of (_hP : Hypotheses2) (hG : Gram) (hD : DeepGood) : Ring := by
  have hH := GlobalTheory.CovTop.Sizes.hostN 4
  refine Closed.imp ((hG.and hD).and hH) fun Fm CH _ h => ?_
  obtain ⟨⟨⟨C1, -, h1⟩, ⟨C2, -, h2⟩⟩, ⟨A, -, h3⟩⟩ := h
  refine ⟨0, le_rfl, ?_⟩
  obtain ⟨x0, hx⟩ := (h1.and h2).and h3
  refine ⟨x0, fun x hx' hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨g1, g2⟩, g3⟩ := hx x hx' hle ι p hp
  have gram := g1 i
  have deep := g2 i hi Y hY
  have host := g3 i
  have hB := GlobalTheory.T.cuspFormLattice_slope_sq_goodCover_le_core _ p.T ((i : ℕ) + 1) Y _ _ (wtA (p.κ i)) (p.κ i).n (typeK p.fw p.F.lv2 i) p.fw.laws
    ⟨Nat.succ_pos _, i.2⟩ hY.1 (dom_wtA _) (fun f hf => hf.1) gram.2.2.2 deep.1
  have hrd := (log_rd_le_fieldSz Y.d.c₂.F).trans hY.1.size
  obtain ⟨⟨-, hL10, hLx, -⟩, -, -, -, -, -, -, -, -, hpp, ⟨hA1, hPPx, -⟩, hroom, -⟩ := host
  have hb : 391 * zBase (Fm.L x ι) ^ 2 ≤ (Fm.L x ι).sc.b := by
    have hm1 := (Fm.D x ι).R.two_le_m
    have hm2 := (Fm.D x ι).R.m_add_three_le_k
    have hf : (1 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast (by have := (Fm.D x ι).R.toFrame.ord_pos; show 1 ≤ 2 * (Fm.D x ι).R.toFrame.ord; omega : 1 ≤ (Fm.D x ι).R.f)
    have hr : (1 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ (Fm.D x ι).R.r)
    have hZ : 1 ≤ zBase (Fm.L x ι) := by
      unfold zBase
      have : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := by nlinarith
      nlinarith
    have hX : (Fm.L x ι).sc.x ≤ (Fm.L x ι).sc.x ^ A := by
      calc (Fm.L x ι).sc.x = (Fm.L x ι).sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (Fm.L x ι).sc.x ^ A := Real.rpow_le_rpow_of_exponent_le (by linarith) hA1
    have hX4 : ((Fm.L x ι).sc.x ^ A) ^ (4 : ℝ) = ((Fm.L x ι).sc.x ^ A) ^ (4 : ℕ) := by
      exact_mod_cast Real.rpow_natCast ((Fm.L x ι).sc.x ^ A) 4
    have hZ2 : zBase (Fm.L x ι) ^ 2 ≤ zBase (Fm.L x ι) ^ 12 := pow_le_pow_right₀ hZ (by norm_num)
    have h1 : zBase (Fm.L x ι) ^ 2 ≤ (Fm.L x ι).sc.x ^ A := hZ2.trans (hpp.trans hPPx)
    generalize (Fm.L x ι).sc.x ^ A = X at *
    have hX10 : (10 : ℝ) ≤ X := (hL10.trans hLx).trans hX
    have h3 : (100 : ℝ) ≤ X * X := by nlinarith
    have h4 : (1000 : ℝ) ≤ X * X * X := by nlinarith
    have h2 : 391 * X ≤ X ^ 4 := by nlinarith
    rw [hX4] at hroom
    linarith
  show slope_sq _ (latDeep p i Y) - 2 * (Fm.L x ι).sc.b ≤ muCore p i
  have h2r : 2 * (Real.log |(discr Y.d.c₂.F : ℝ)| / Module.finrank ℚ Y.d.c₂.F) ≤ 2 * (Fm.L x ι).sc.b := by linarith
  exact le_trans (sub_le_sub_left h2r _) hB

end GlobalTheory.CovTop.RingStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorTensorPowerCorrespondsFormalSumStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosatiGenerator_tensorPower_corresponds_formalSum : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W) (A A' : Matrix (Fin r) (Fin r) ℤ) (u' : LB.Gen (LB.LinComb D'.P.L (rosatiφ D'.P.A (GlobalTheory.TensAct.matAct T A) (GlobalTheory.TensAct.matAct T A')) rosatiε)), u'.IsGen → LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ u' (zero2 D'.P.A)) (LB.oneGen D'.P.L) → ∀ (Ξ : LB.Gen (LB.LinComb D.P.L (fun v : (GlobalTheory.TensBal.sig W A A').support => (GlobalTheory.TensBal.vecHom T v.1).left) (fun v => GlobalTheory.TensBal.sig W A A' v.1))), Ξ.IsGen → (∀ (z : (𝟙_ (Over (Spec (CommRingCat.of R)))).left) (J : ((𝟙_ (Over (Spec (CommRingCat.of R)))).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → val Ξ (zero2 D'.P.A) z J = 1) → ∀ (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι) (J' : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → ∀ y y' : D'.X, (∏ a, GlobalTheory.TensBal.isoV T.w z J J' (D'.pt2 y y' ≫ rosatiφ D'.P.A (GlobalTheory.TensAct.matAct T A) (GlobalTheory.TensAct.matAct T A') a) ^ rosatiε a) * val u' (D'.pt2 y y') z J' = val Ξ (D'.pt2 y y') z J := by
  first | exact @GlobalTheory.TensRos.ros_sig | exact GlobalTheory.TensRos.ros_sig | (intros; apply GlobalTheory.TensRos.ros_sig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiValuesTensorDataMatrixAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section
namespace GlobalTheory.Mum.TensRos

theorem main_alg {F : Type} [Field F] (a1 a2 P1 P2 s1 s2 A Bv C Dd E' G one : F) (hA : A ≠ 0) (hB : Bv ≠ 0)
    (hE : E' ≠ 0) (hG : G ≠ 0) (hD : Dd ≠ 0)
    (h1 : a2 * (A * Bv * C) = a1 * (Dd * E' * G)) (h2 : a2 * P1 = P2) (h3 : s1 * A * Bv = P1 * Dd * one)
    (h4 : s2 * E' * G = P2 * C * one) : s2 = s1 * a1 := by
  have hK : A * Bv * E' * G * Dd ≠ 0 := by positivity
  apply mul_right_cancel₀ hK
  linear_combination (A*Bv*Dd)*h4 - (a1*E'*G*Dd)*h3 - (A*Bv*Dd*C*one)*h2 + (P1*one*Dd)*h1

theorem rosGt_values : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ (x : 𝓞 E) (ρ' : N'.A → N'.A → F), (letI := H.starRing; GlobalTheory.Relabel.RosV ν' o.onB x ρ') → ∀ (v' w' : N'.Gt) (vs : Fin r → N.Gt), GtRel T ν ν' v' vs → GtRel T ν ν' w' (fun i => ∏ j, vs j ^ ρ x i j) → (letI := H.starRing; ∀ χ, (w'.s χ : F) = v'.s (ν'.eX.symm (star x • ν'.eX χ)) * ρ' (N'.c χ) v'.b) := by
  intro R _ _ _ hB D D' r W T F _ _ _ N N' ν ν' E _ _ _ H ρ hρ _ o hact x ρ' hρ' v' w' vs hv hw
  letI := H.starRing
  obtain ⟨ρ'', hT, hmove⟩ := GlobalTheory.T.rosatiValue_tensorData_transport_lambdaBundle R hB D D' W T F N N' ν ν' (𝓞 E) o.onB x ρ' hρ'
  obtain ⟨-, hbij, -, -, -, hwv0, -, -⟩ := GlobalTheory.T.tensorData_values_facts R hB D D' W T F N N' ν ν'
  rw [GtRel, gtRelV_iff] at hv hw
  intro χ
  have hb : w'.b = GlobalTheory.Relabel.actV ν' o.onB x v'.b := by
    apply hbij.1
    funext j
    rw [hw.1 j, cmp_actV T ν ν' o ρ hact x v'.b j, ← NumD.projB_apply, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow, NumD.projB_apply, hv.1 k]
  have h1 := hmove (N'.c χ) v'.b
  rw [c_actV ν' o] at h1
  have h2 := GlobalTheory.T.rosatiGenerator_components_torusExtension R hB D D' W T F N N' ν ν' E H ρ hρ o hact x ρ'' hT χ v'.b vs hv.1
  have h3 := hv.2 (ν'.eX.symm (star x • ν'.eX χ))
  have h4 := hw.2 χ
  rw [hb] at h4
  exact main_alg _ _ _ _ _ _ _ _ _ _ _ _ _ (hwv0 _) (hwv0 _) (hwv0 _) (hwv0 _) (hwv0 _) h1 h2 h3 h4

end GlobalTheory.Mum.TensRos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowRepresentationBasePosition
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem row_hRB_univ : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ (Q : V4.Slot) (Lk : LkT Bundle), R1.RankBoundAtBundlePoints Q Lk := by
  intro hDS hHC hRD hCW Q Lk
  refine Row.of_sel fun 𝒜 σ _ _ Fm hc x hx i => ?_
  exact GlobalTheory.T.indefinite_scale_theta_bound_right hRD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B (Fm.parT x hx i).nV_ge
    (GlobalTheory.T.indefinite_scale_theta_equality hDS hHC hRD hCW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (σ Fm hc x hx i).B).1

end GlobalTheory.Fc.R1

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitContinuousStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_orbit_continuous : GlobalTheory.ThK.KP → GlobalTheory.ThK.SoCont := by
  first | exact @GlobalTheory.ThKSoCont.soCont | exact GlobalTheory.ThKSoCont.soCont | (intros; apply GlobalTheory.ThKSoCont.soCont <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueGenericPointIntegralSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_value_generic_point_integral_section : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U) (x : TFK (R := R) (FractionRing R) ⟶ A.A) (e : FrAt x) (h : 𝟙_ (Over (Sp R)) ⟶ G) (l : FractionRing R) (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))), IntTerm.Ext U x h → (∀ (z : (TF (R := R) (FractionRing R)).left) (JA : ((TF (R := R) (FractionRing R)).left ⟶ A.A.left) → A.L.ι) (JG : ((TF (R := R) (FractionRing R)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → (Geo.Tor.gw (Y := (TF (R := R) (FractionRing R)).left) w₀ (x.left ≫ U.gen.inv.left) z (JG (toUnit (TF (R := R) (FractionRing R)) ≫ h).left) (fun _ => JA x.left)).val * (val (Z := (TF (R := R) (FractionRing R)).left) e (𝟙 _) z JA).val = GlobalTheory.UT.cst (FractionRing R) z l * (val f (toUnit (TF (R := R) (FractionRing R))).left z JG).val) → ∀ (k : ℕ) (s : SecA A (FractionRing R) k) (σ' : U.SecGF (FractionRing R) k), GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) (FractionRing R)) ((Over.pullback (jK R)).obj G)).left k (snd (TFK (R := R) (FractionRing R)) A.A).left (U.genF (FractionRing R)).left s (UnifPre.gFK (G := G) (FractionRing R)) (𝟙 _) σ' → ∀ (n : ℕ) (c : Fin n → FractionRing R) (σ : Fin n → H0 U.LG.L k), GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) (FractionRing R)) (fun _ => (k : ℤ)) σ' (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) (FractionRing R)) (fun i => scal (fst (TFK (R := R) (FractionRing R)) ((Over.pullback (jK R)).obj G)).left (c i)) → ∀ xs : Fin n → R, (∀ (i : Fin n) (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι), Good U.LG.L z J → sval (σ i) (r ≫ h.left) z J = Geo.Tor.cst r z (xs i) * (val f r z J ^ k).val) → ∀ v : FractionRing R, ValAt s x e v → v * l ^ k = ∑ i, c i * algebraMap R (FractionRing R) (xs i) := by
  first | exact @GlobalTheory.Poinc.IntEval.value_at_section | exact GlobalTheory.Poinc.IntEval.value_at_section | (intros; apply GlobalTheory.Poinc.IntEval.value_at_section <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueIntegralPointCongruentTermSumStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_value_integral_point_congruent_term_sum : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (h : 𝟙_ (Over (Sp R)) ⟶ G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U h g → ∀ (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))) (t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, g.b.left] (DegPre.lineε 1))) (e k : ℕ), GlobalTheory.Poinc.IntEval.TRel U h g.b f t e → ∀ (σ : H0 U.LG.L k) (fs : ∀ α : D.toPre.X, D.toPre.SecB k α), U.ExpandsAt e k σ fs → ∀ x : R, (∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι), Good U.LG.L z J → sval σ (r ≫ h.left) z J = Geo.Tor.cst r z x * (val f r z J ^ k).val) → ∀ a : D.toPre.X → R, (∀ (α : D.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good D.toPre.P.L z J → sval (fs α) (r ≫ g.b.left) z J * (val (g.s α) r z J).val * (val t r z J ^ k).val = Geo.Tor.cst r z (a α) * (val (L := D.toPre.P.L) D.toPre.rig r z J ^ k).val) → ∃ S : Finset D.toPre.X, ∀ T : Finset D.toPre.X, S ⊆ T → x - ∑ α ∈ T, a α ∈ I ^ (e + 1) := by
  first | exact @GlobalTheory.Poinc.IntEval.value_sub_sum_mem_hRed | exact GlobalTheory.Poinc.IntEval.value_sub_sum_mem_hRed | (intros; apply GlobalTheory.Poinc.IntEval.value_sub_sum_mem_hRed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawLeftRestrictionGlobalStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.places_bound_tuple : GlobalTheory.BigOn.Exp.TupLe.PlacesSt := by
  first | exact @GlobalTheory.BigOn.Exp.TupLe.placesSt | exact GlobalTheory.BigOn.Exp.TupLe.placesSt | (intros; apply GlobalTheory.BigOn.Exp.TupLe.placesSt <;> assumption)
end

