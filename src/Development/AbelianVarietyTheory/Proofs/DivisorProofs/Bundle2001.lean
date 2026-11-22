import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundOfCoreLaws
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1969
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1987
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1840
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0007
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0008
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ImportsBis
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0004
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogSupNormLowerBoundPrincipalLevel
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory

theorem transv_of_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Xx : DataX E r) (Y : Data E r)
    (hX : Xx.toData = Y) (la : Wt Y.Ψ r) (M : ℝ) (hχ : ∀ γ ∈ Y.Γ, Y.χ la γ = 1)
    (htr : ∀ v ∈ Xx.L', herm Xx.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ Xx.Γ, ∀ τ : Xx.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = Xx.flowMat v τ ((M : ℂ) * τ.1 b)) :
    ∀ v ∈ Xx.L', herm Y.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ Y.Γ, Y.χ la γ = 1 ∧
        ∀ τ : Y.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = Y.flowMat v τ ((M : ℂ) * τ.1 b) := by
  subst hX
  intro v hv hvv b hb hbi
  obtain ⟨γ, hγ, hγ'⟩ := htr v hv hvv b hb hbi
  exact ⟨γ, hγ, hχ γ hγ, hγ'⟩

theorem lamSup_of_laws : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ F ∈ cusp Xo c U a n, (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → F ≠ 0 → -lamSup D.host.E D.R.r Dw.q D.host.d l.M (GlobalTheory.CM.logOm D.host.E χ).re ((absA Dw a : ℕ) : ℝ) ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) ≤ (∑ σ : c.F →+* ℂ, Real.log (supC Xo c U (xiR D) (goodOf c σ) a n F)) / (Module.finrank ℚ c.F : ℝ) := by
  classical
  intro D j H Dw l Xo c U dict h _ χ hχ a n ha F hF hval hF0
  have hσ₀ : GoodEmb c c.F.val.toRingHom := rfl
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r
    omega
  have hU := h.unf c.F.val.toRingHom hσ₀
  have hpq : Dw.p + Dw.q = D.R.r := hU.1.symm
  have hSD : SupDef Xo c U :=
    (Formalism.L2.PjFree.supDef_ofPj U).1 (GlobalTheory.supNorm_definite_on_cusp D.host.E H Dw l Xo c D.R.r
      (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj (U σ)).2 (h.unf σ hσ)))
  set σ₀ := c.F.val.toRingHom with hσdef
  have hhol : rdU (U σ₀) F ∈ holSub (U σ₀).X (laU (U σ₀) a n) := ((mem_cusp _ _ _ _ _ F).1 hF).2 σ₀ hσ₀
  have hSS := Formalism.L2.Pj.abelian₂.holSub_SS siegelSpaceAlgebra_holds (U σ₀).X (laU (U σ₀) a n) hhol
  have hfin : supE (U σ₀).X (laU (U σ₀) a n) (rdU (U σ₀) F) ≠ ⊤ := supE_cusp_ne_top hσ₀ hF
  have hpos : 0 < supN (U σ₀).X (laU (U σ₀) a n) (rdU (U σ₀) F) := by
    rcases (ENNReal.toReal_nonneg : 0 ≤ (supE (U σ₀).X (laU (U σ₀) a n) (rdU (U σ₀) F)).toReal).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (hSD a n ha σ₀ hσ₀ F hF heq.symm) hF0
  obtain ⟨k, z0, hz0, hlt⟩ := Formalism.L2.Pj.abelian₂.half_max (U σ₀).X (laU (U σ₀) a n) (rdU (U σ₀) F) hpos hfin
  have hhalf : ∀ x ∈ ((U σ₀).X k).dom, ((U σ₀).X k).pnorm (laU (U σ₀) a n k) (rdU (U σ₀) F k) x ≤
      2 * ((U σ₀).X k).pnorm (laU (U σ₀) a n k) (rdU (U σ₀) F k) z0 :=
    fun x hx => (Formalism.L2.Pj.abelian₂.pnorm_le_supN _ _ _ hfin k x hx).trans hlt.le
  have hposz : 0 < ((U σ₀).X k).pnorm (laU (U σ₀) a n k) (rdU (U σ₀) F k) z0 := by linarith
  obtain ⟨Xx, hX, hXg, hΛ, -, M, hM, hMk, htr⟩ := GlobalTheory.T.exists_selfDual_data_transvection_principal_level D j H Dw l Xo c U dict h σ₀ hσ₀ k
  have hsp := GlobalTheory.T.sum_weightSpread_le_exponentNorm_add D j H Dw l Xo c U dict h σ₀ hσ₀ a n k
  set s : ℝ := ((absA Dw a : ℕ) : ℝ) with hs
  set t : ℝ := ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) with ht
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  have ht0 : 0 ≤ t := Nat.cast_nonneg _
  have hw : (∑ τ, ((U σ₀).X k).spread (laU (U σ₀) a n k) τ) ≤ s + t + 1 := by linarith
  have hw1 : (1 : ℝ) ≤ s + t + 1 := by linarith
  obtain ⟨x, lam, hx, hLB, hPx⟩ := Formalism.L2.Pj.abelian₂.cm_frame_of_eq Xx ((U σ₀).X k) hX _ _ z0 M (s + t + 1) (hSS k) hM
    hw hw1 hr (transv_of_eq Xx _ hX _ M (h.chiTriv σ₀ hσ₀ a n ha k) htr) hz0 hhalf hposz
  have hp0 : Xx.p0 = Dw.q := (congrArg Data.p0 hX).trans (hU.2.1 k).1
  have heps : epStar M (fdeg D.host.E) (s + t + 1) Xx.k0 = epsLev D.host.E D.host.d l.M (s + t + 1) := by
    unfold epsLev epStar
    congr 2
    rw [← hMk]
    ring
  have hLa : frameBasisRadius D.R.r Xx.p0 (fdeg D.host.E) (dE D.host.E) (Real.sqrt (epStar M (fdeg D.host.E) (s + t + 1) Xx.k0))
      (3 * frameRadius (s + t + 1) D.R.r / 5) = cmLen D.host.E D.R.r Dw.q D.host.d l.M (s + t + 1) := by
    unfold cmLen
    rw [hp0, heps]
  rw [hLa] at hLB
  have hf1 : 1 ≤ fdeg D.host.E := by
    have h2 := finrank_eq_two_mul_half_degree (E := D.host.E)
    have h3 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    have h4 : Module.finrank ℚ D.host.E = 2 * fdeg D.host.E := by exact_mod_cast h2
    omega
  have hd1 := GlobalTheory.WtSizes.one_le_dE D
  have hlog : Real.log (M * Xx.k0) ≤ 19 * |Real.log (M * Xx.k0)| + 3 + Real.log (dE D.host.E) := by
    have := Real.log_nonneg hd1
    have := le_abs_self (Real.log (M * Xx.k0))
    have := abs_nonneg (Real.log (M * Xx.k0))
    linarith
  obtain ⟨C0, hC0, hroom⟩ := GlobalTheory.T.exists_constant_cmEvaluation_fits_room
  have hLa1 : 1 ≤ cmLen D.host.E D.R.r Dw.q D.host.d l.M (s + t + 1) := by
    rw [← hLa]
    exact (hroom (fdeg D.host.E) D.R.r Xx.p0 (dE D.host.E) |Real.log (M * Xx.k0)| 0 M Xx.k0 (s + t + 1) hf1 hr
      Xx.p0_le hd1 (abs_nonneg _) hM Xx.minWeight_pos hw1 hlog).1
  have hSpos : ∀ σ, 0 < supC Xo c U (xiR D) (goodOf c σ) a n F := fun σ => by
    unfold supC
    refine mul_pos (lieFac_pos _ _ _) (lt_of_le_of_ne (supN_nonneg _ _ _) fun h0 => hF0 ?_)
    exact hSD a n ha _ (Formalism.L2.Pj.goodEmb_goodOf (c := c) σ) F hF h0.symm
  have h5 := GlobalTheory.T.meanLogSupNorm_lowerBound_cmFrame_nonvanishing D.host.E H Dw l Xo c D.R.r U (xiR D) h.unf h.xiAbs (by omega) χ hχ a n ha F hF hval hSpos
    k ⟨x, hx⟩ Xx hX D.host.AA (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D) hΛ _ lam hLa1 hLB hPx
  refine le_trans ?_ h5
  have et : ((Module.finrank ℚ D.host.E / 2 * D.R.r : ℕ) : ℝ) * n = t := by
    rw [ht]
    simp only [fdeg, Nat.cast_mul]
  rw [et]
  unfold lamSup
  apply le_of_eq
  simp only [absA] at hs
  rw [← hs]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAlgebraMapLtOneIffValuationLtOne
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.Frames GlobalTheory.HTLat
open scoped NNReal

namespace GlobalTheory.CompHt

theorem norm_algebraMap_lt_one_iff_valuation_lt_one : ∀ (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (ℓ : ℕ) [Fact ℓ.Prime]
    [Algebra K ℂ_[ℓ]], (ℓ : 𝓞 K) ∈ la.asIdeal → ∀ (T : CDVR) (io : K →+* T.Fr) (e : ℕ), OverLa la T.V io e →
    ∀ (k : T.Fr →+* ℂ_[ℓ]), (∀ b, k (io b) = algebraMap K ℂ_[ℓ] b) →
      (∀ x : T.Fr, val_vw la ℓ (Valued.v : Valuation ℂ_[ℓ] ℝ≥0) (k x) = nval T.V e x) →
      ∀ b : K, ‖algebraMap K ℂ_[ℓ] b‖ < 1 ↔ la.valuation K b < 1 := by
  intro K _ _ la ℓ _ _ hℓ T io e ho k hk hm b
  have hnv : ∀ x : ℂ_[ℓ], ‖x‖ = ((Valued.v x : ℝ≥0) : ℝ) := fun x => by
    rw [PadicComplex.norm_eq_norm, Valuation.norm_def, PadicComplex.RankOne.hom_eq_embedding,
      Valuation.embedding_restrict]
  by_cases hb : b = 0
  · subst hb; simp

  have hpos : ∀ x : K, x ≠ 0 → (0 < vLa la x ↔ la.valuation K x < 1) := fun x hx => by
    have h0 : la.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    have := WithZero.log_lt_log h0 (one_ne_zero)
    rw [WithZero.log_one] at this
    simp only [vLa]
    constructor
    · intro h; exact this.1 (by omega)
    · intro h; have := this.2 h; omega
  have hℓK : (ℓ : K) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have hcpos : (0 : ℝ) < vLa la (ℓ : K) := by
    have h1 : la.valuation K (ℓ : K) < 1 := by
      have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) la (ℓ : 𝓞 K)).2 hℓ
      simpa using this
    exact_mod_cast (hpos _ hℓK).2 h1
  have ha : algebraMap K ℂ_[ℓ] b ≠ 0 := (map_ne_zero _).2 hb
  have hio : io b ≠ 0 := (map_ne_zero _).2 hb
  have h := hm (io b)
  rw [hk, val_vw_of_ne la ℓ _ ha, nval_of_ne hio, ho.2 b] at h
  have he : (e : ℝ) ≠ 0 := by exact_mod_cast ho.1.ne'
  have h' : (vLa la (ℓ : K) : ℝ) * (Real.log ((Valued.v : Valuation ℂ_[ℓ] ℝ≥0) (algebraMap K ℂ_[ℓ] b) : ℝ) /
      Real.log ((Valued.v : Valuation ℂ_[ℓ] ℝ≥0) (ℓ : ℂ_[ℓ]) : ℝ)) = vLa la b := by
    rw [EReal.coe_eq_coe_iff] at h
    rw [h]; push_cast; field_simp
  have hL : Real.log ((Valued.v : Valuation ℂ_[ℓ] ℝ≥0) (ℓ : ℂ_[ℓ]) : ℝ) < 0 := by
    rw [PadicComplex.valuation_p]
    have : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
    push_cast
    exact Real.log_neg (by positivity) (by rw [one_div]; exact inv_lt_one_of_one_lt₀ this)
  have hva : (0 : ℝ) < ((Valued.v : Valuation ℂ_[ℓ] ℝ≥0) (algebraMap K ℂ_[ℓ] b) : ℝ) := by
    have : (Valued.v : Valuation ℂ_[ℓ] ℝ≥0) (algebraMap K ℂ_[ℓ] b) ≠ 0 := (Valuation.ne_zero_iff _).2 ha
    exact_mod_cast pos_iff_ne_zero.2 this
  rw [hnv, ← hpos b hb, ← Int.cast_pos (R := ℝ), ← h', mul_pos_iff_of_pos_left hcpos,
    ← Real.log_neg_iff hva]
  constructor
  · intro hA; exact div_pos_of_neg_of_neg hA hL
  · intro hq
    by_contra hA; push_neg at hA
    exact absurd hq (not_lt.2 (div_nonpos_of_nonneg_of_nonpos hA hL.le))

end GlobalTheory.CompHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormRawThetaSeriesIndexBoundLeSqrt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.RawThetaSup

open GlobalTheory.Dict.ShortPoint

theorem norm_rawThetaSeries_index_bound_le_sqrt {κ t : ℂ} {m z Q : ℕ} {J B : ℝ} {j : ℕ} (hJ : J = j) (hj : 0 < j) (hz : z = m * j)
    (hC : 0 ≤ 1 * (B / Real.sqrt J)) (h : ‖((Q : ℂ))⁻¹ * (κ * t)‖ ≤ 1 * (B / Real.sqrt J)) :
    ‖(1 : ℂ)⁻¹ * (m : ℂ)⁻¹ * (Q : ℂ)⁻¹ * (z : ℂ) * κ * t‖ ≤ Real.sqrt J * B := by
  have hJ0 : 0 < J := by rw [hJ]; exact_mod_cast hj
  have hs : 0 < Real.sqrt J := Real.sqrt_pos.2 hJ0
  have hb : ‖((Real.sqrt J : ℝ) : ℂ)‖ ^ 2 = J := by
    rw [Complex.norm_real, Real.norm_of_nonneg hs.le, Real.sq_sqrt hJ0.le]
  have h1 := norm_index_cancellation_le_bound hJ hj hz hb hC h
  have e : (1 : ℂ)⁻¹ * (m : ℂ)⁻¹ * (Q : ℂ)⁻¹ * (z : ℂ) * κ * t =
      ((Real.sqrt J : ℝ) : ℂ) * (((Real.sqrt J : ℝ) : ℂ)⁻¹ * (m : ℂ)⁻¹ * (Q : ℂ)⁻¹ * (z : ℂ) * κ * t) := by
    have : ((Real.sqrt J : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    field_simp
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le]
  exact mul_le_mul_of_nonneg_left (h1.trans_eq (_root_.one_mul B)) hs.le

theorem thLaValAt_evR {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {n : ℕ} {Λ : GenLat E n} {N : ℕ} (hU : Λ.Unimod) (hT : Λ.TrivAt l.M) (hO : Λ.LevOK N l.M)
    {a : (E →+* ℂ) × ℕ → ℕ} {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmL c Λ a)
    (w : (Fin n → LevQ Dw l) → c.F) {f : Rul Xo c} (hf : f ∈ sec Xo c a n)
    (h : ∀ (p : TRing c.F) (y : FrPt Xo c p.R), thLaValAt Xo c nab w Λ N P y (f p y))
    (S : Type) [CommRing S] [_root_.IsReduced S] [Algebra c.F S] (y : FrPt Xo c S) :
    thLaValAt Xo c nab w Λ N P y (evR Xo c f y) := by
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨hval, hnat⟩ := GlobalTheory.shortThetaValue_existsUnique_natural hL GlobalTheory.chartIndependence_unconditional E H Dw l Xo c
    nab hnab n Λ N hU hT hO a P hP.1 w 1
  obtain ⟨v, hv, -⟩ := hval S y
  obtain ⟨p, φ, y0, hy0⟩ := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw l Xo c S y
  have e1 := GlobalTheory.CoverDescent.evR_of_test (GlobalTheory.Frames.algebraic_laws hL.secBaseChange E H Dw l Xo c).2.2.1 f hf.1
    p φ y0 y hy0
  have e2 := hnat p.R S φ y0 y hy0 _ v (h p y0) hv
  rw [e1, e2]
  exact hv

set_option maxHeartbeats 1000000 in

theorem norm_evR_le (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r)
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) (hr1 : 1 ≤ r) (t : ℝ) (ht : 0 < t)
    (hct : ∀ k τ, (U.X k).c τ = t) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hDom : Dom a n) [StarRing (𝓞 E)]
    (nab : NabV Xo c) (hnab : IsNab Xo c nab) (Λ : GenLat E n) (N : ℕ) (w : (Fin n → LevQ Dw l) → c.F)
    (hw1 : ∀ q, ‖σ (w q)‖ ≤ 1) (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c) (hΛu : Λ.Unimod) (hΛt : Λ.TrivAt l.M)
    (hΛl : Λ.LevOK N l.M) (hP : P ∈ harmL c Λ a) (hf : f ∈ sec Xo c a n)
    (hraw : ∀ (p : TRing c.F) (y : FrPt Xo c p.R), thLaValAt Xo c nab w Λ N P y (f p y))
    (k : U.Comp) (x : (U.X k).dom) (hxo : (U.X k).IsOrtho x.1) (lam : ℝ) (hlam : 0 < lam)
    (hlam2 : lam ^ 2 ≤ (U.X k).firstMinimumSq x.1) :
    ‖Formalism.L2.PjFree.toC (evR Xo c f (U.un k x))‖ ≤
      Real.sqrt (((Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℝ) ^ r) *
      ((∑ m ∈ P.support, ‖σ (P.coeff m)‖) * (Real.pi * Real.exp 1 * t * (Formalism.L2.Pj.DF Dw a : ℕ)) ^ (((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) / 2) * Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * (fdeg E * r : ℕ) * n) * (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^ (fdeg E * r * n)) := by
  have hci := GlobalTheory.chartIndependence_unconditional
  have hr : r = Dw.p + Dw.q := hU.1
  have hn : Even n := hDom.2
  letI A₁ : Algebra c.F ℂ := σ.toAlgebra
  have huf : IsUnitFr (U.X k) x.1 := fun τ i => by
    unfold dmin lminor
    rw [hxo τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
    refine Finset.prod_eq_one fun a _ => ?_
    simp only [Function.comp, FD.sgn]
    split_ifs <;> simp
  obtain ⟨W, Dc, A, θ, v, κ, he, hg, hw, hL, hmk, hA, hrd, hth, hmean, hvac, hprod⟩ :=
    GlobalTheory.T.exists_analyticData_unitFrame_framedPoint E H Dw l Xo c σ r U hσ hU hr1 a n hDom k x huf
  obtain ⟨-, -, hlen, -, -⟩ := hx_ortho E r (U.X k) W.g Dc.bas Dc.idx Dc.sympl x.1 x.2 hxo
  have hv0 := thLaValAt_evR nab hnab hΛu hΛt hΛl hP w hf hraw ℂ (unC U k x)
  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨-, hV, hVd, hstd⟩ := GenLatCmp.genLat_vset E n Λ.La
  have hΛ : Λ.La ∈ Vset E n l.M := hV _ N hM hΛu hΛt hΛl
  have hΛ1 : Λ.La ∈ Vset E n 1 := hVd 1 _ (one_dvd _) hΛ
  obtain ⟨Y, hY⟩ := (GlobalTheory.T.dual_half_level_marking_exists_and_match E H Dw l r (U.X k) (U.X k).Λ (W.mark k) _ hL hmk
    (Complex.isPrimitiveRoot_exp _ hM.ne')).2.2.2.2 n N hΛl.1.pos
  have hval := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hci E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e x.1 (U.X k).Λ (unC U k x) A
    Dc.sympl x.2 hL Dw.p n Dc.hr Dc.eL hr hn (he ▸ Dc.dir_eq) nab hnab θ v κ hrd hvac hprod (W.mark k) hmk hA
    Λ.La hΛ N hΛl Y hY a P hP.1 w 1 _ hv0
  have hhom : (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P)).IsHomogeneous (Formalism.L2.Pj.DF Dw a) :=
    (((GlobalTheory.T.exists_integralHarmonic_ne_zero_and_isHomogeneous E H Dw l c a n).2 P hP.1).map σ).rename_isHomogeneous
  have hcore := fun y => GlobalTheory.T.jet_translate_projected_vacuum_le E r (U.X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hn H.w0 hw _ hL Λ.La hΛ1
    v hvac x.1 x.2 hxo t ht (hct k) θ κ hth hmean hprod lam hlam (fun u hu hu0 => hlam2.trans (hlen u hu hu0)) y _ _
    hhom
  obtain ⟨R, -, -, hR, hR0, -⟩ := VacMean.vac_proj_mean E r (U.X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hn
    H.w0 hw _ hL Λ.La hΛ1 v hvac
  rw [hR] at hR0
  have hJ : (0 : ℝ) < Real.sqrt ((((stdL E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup) : ℝ) ^ r) :=
    Real.sqrt_pos.2 (by exact_mod_cast hR0)
  have hsb : IsSB (projA (U.X k) Dc.bas (H.w0 : E) (tens Λ.La (U.X k).Λ) v) := by
    obtain ⟨⟨v', hv'⟩, -, h, -⟩ := TensVac.vacua E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hn _
      H.w0.isIntegral_coe hw _ hL 1 Λ.La hΛ1
    rw [h v hvac.1 v' hv']
    exact isSB_smul _ hv'.1
  rw [sum_coeff_rename] at hcore
  have hc2 := fun y => (le_div_iff₀ hJ).2 (hcore y)
  have hB0 := (norm_nonneg _).trans (hc2 0)
  have hmeanle := norm_mean_le Dc.hr Dc.idx Dc.sympl x.2 (fun q => algebraMap c.F ℂ (w q))
    (fun q => heisG (U.X k) Dc.bas (Y q) (projA (U.X k) Dc.bas (H.w0 : E) (tens Λ.La (U.X k).Λ) v))
    (fun q => ((heisG_laws E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hn).2.2.2 (Y q) _ hsb).1) _ κ zero_le_one hB0
    hw1 (fun q => hc2 (Y q))
  have hfin := norm_rawThetaSeries_index_bound_le_sqrt (Nat.cast_pow _ r).symm hR0 (zCard_eq Λ hstd hΛl r) (mul_nonneg zero_le_one hB0) hmeanle
  have hev' : Formalism.L2.PjFree.toC (evR Xo c f (U.un k x)) = evR Xo c f (unC U k x) := rfl
  rw [hev', hval, ← hg, index_Ln Λ hstd]
  simp only [map_mul, map_inv₀, map_natCast, map_one]
  exact hfin

end GlobalTheory.RawThetaSup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSumChoiceBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.norm_sum_choice_bound : ∃ C1 : ℝ, 0 < C1 ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ (ch : Choice R) (CF : ℝ), ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.NormSum.Inp D →
      DictAt ch → ∀ (S : Finset ℕ) (δ : ℕ → ℝ), GlobalTheory.NormSum.Letters D S δ →
      ∀ (t : T) (p : Pair T), DefPair D.R.m p → ∀ (k : ℕ) (d : FinDatum ch.G t p), 0 < k → IsCosetDatum k d → d.z = 1 →
      d.P = locPl ch.G t → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ch.S.Z.IsRatAt d x y →
      ∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → Away ch.G t w →
      ∀ (a : ℝ) (v : VV ℂ (wt ch.G p.small)), InLat _ w a (latAt ch.S.toGridChoice p.small x) v →
        InLat _ w (a + (vw w ((l : ℕ) : D.what₂.LL) : ℝ) * C1 *
            GlobalTheory.SumSize.TopInt.kerLoss ch.G δ C1 large₂.sc.b p.small p.big l (padicValNat l k))
          (latAt ch.S.toGridChoice p.big y) (ch.S.Z.kkMap 1 d x y v) := by
  refine ⟨1, one_pos, ?_⟩
  intro D large₂ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch CF _ _ _ _ hI hDict S δ hL t p hp k d hk hd hz hP x y hR w l hl hw hA a v hv
  have hn := DefPair.nodes hp
  obtain ⟨k', hk', hd', hle, hsp⟩ := UpperTheory.WildA.depth large₂ hS.size d hP w l hl hw hA k hk hd
  obtain ⟨r, U, hU, e, hx⟩ := UpperTheory.WildA.toStd ch.S.toGridChoice p.small hn.1 l hl x
  obtain ⟨r', U', hU', e', hy⟩ := UpperTheory.WildA.toStd ch.S.toGridChoice p.big hn.2 l hl y
  have hmv := UpperTheory.WildA.move ch.S.Z hS.core.lev t p hp d x r y r' U U' hU hU'
  have hR' : ch.S.Z.IsRatAt d (r * x) (r' * y) := by
    intro i j
    have := UpperTheory.WildA.ratMove D _ _ _ _ _ _ hmv (fun i j => by
      have := hR i j
      rwa [Normal.kkIn, LinearMap.toMatrix_apply] at this) i j
    rwa [Normal.kkIn, LinearMap.toMatrix_apply]
  have h1 := UpperTheory.WildA.kerStd D large₂ Γ Pl0 T A Ks R F hS ch hI hDict S δ hL t p hp k' d hk' hd' hz hP _ _ hR' w l hl hw hsp hx hy
    large₂.sc.b
  have h2 := (UpperTheory.WildA.latMove D _ w a _ U v).2 hv
  rw [← e] at h2
  have h3 := UpperTheory.WildA.matLat D _ _ w l hl hw _ _ hx hy _ _ h1 a _ h2
  have h4 := LinearMap.congr_fun hmv v
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h4
  rw [h4, e'] at h3
  refine GlobalTheory.SumSize.TopInt.inLat_mono ((UpperTheory.WildA.latMove D _ w _ _ U' _).1 h3) ?_
  rw [mul_one]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (GlobalTheory.SumSize.TopInt.kerLoss_mono _ _ _ _ _ _ _ hle)
    (by exact_mod_cast GlobalTheory.SumSize.TopInt.vw_natCast_nonneg w l))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicAdelicSchwartzFiniteCosetDecomposition
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem GlobalTheory.WeilCont.schA_periodic_finite_cosets : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    IsCompact (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    ∀ K : Set (κ → FiniteAdeleRing (𝓞 F) F), IsCompact K →
    ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (y : Fin m → κ → FiniteAdeleRing (𝓞 F) F),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ Ψ ∈ GlobalTheory.WeilM.schA F κ, (∀ x ∈ L, ∀ z, Ψ (z + GlobalTheory.WeilCont.adeleJoin F 0 x) = Ψ z) →
        (∀ z, Ψ z ≠ 0 → (fun i => (z i).2) ∈ K) →
        ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, Ψ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i) := by
  intro F _ _ κ _ L hLo hLc K hK
  have hcont : ∀ k : κ → FiniteAdeleRing (𝓞 F) F, Continuous fun w : κ → FiniteAdeleRing (𝓞 F) F => w - k :=
    fun k => continuous_id.sub continuous_const
  have hmk : ∀ a b : κ → FiniteAdeleRing (𝓞 F) F,
      (QuotientAddGroup.mk a : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L) = QuotientAddGroup.mk b ↔ a - b ∈ L := by
    intro a b
    rw [QuotientAddGroup.eq, ← neg_mem_iff, neg_add, neg_neg, ← sub_eq_add_neg]
  have hfin : (QuotientAddGroup.mk '' K : Set ((κ → FiniteAdeleRing (𝓞 F) F) ⧸ L)).Finite := by
    obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover (fun k => {w | w - k ∈ L})
      (fun k _ => (hLo.preimage (hcont k)).mem_nhds (by simp))
    refine (t.finite_toSet.image QuotientAddGroup.mk).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨k, hk, hwk⟩ := Set.mem_iUnion₂.mp (hcov hw)
    exact ⟨k, hk, ((hmk w k).2 hwk).symm⟩
  obtain ⟨m, e, he, hS⟩ : ∃ (m : ℕ) (e : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L), Function.Injective e ∧
      ∀ q, q ∈ (QuotientAddGroup.mk '' K : Set ((κ → FiniteAdeleRing (𝓞 F) F) ⧸ L)) ↔ ∃ i, e i = q := by
    refine ⟨hfin.toFinset.card, fun i => (hfin.toFinset.equivFin.symm i).1,
      Subtype.val_injective.comp hfin.toFinset.equivFin.symm.injective, fun q => ⟨fun hq => ?_, ?_⟩⟩
    · exact ⟨hfin.toFinset.equivFin ⟨q, hfin.mem_toFinset.2 hq⟩, by simp⟩
    · rintro ⟨i, rfl⟩
      exact hfin.mem_toFinset.1 (hfin.toFinset.equivFin.symm i).2
  choose y hy using fun i => QuotientAddGroup.mk_surjective (e i)
  refine ⟨m, fun i w => if (QuotientAddGroup.mk w : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L) = e i then 1 else 0, y,
    fun i => ?_, fun i j => ?_, ?_⟩
  · refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ⟨{w | w - x ∈ L}, hLo.preimage (hcont x), by simp,
      fun x' hx' => ?_⟩, HasCompactSupport.intro' (K := {w | w - y i ∈ L})
      ((Homeomorph.subRight (y i)).isCompact_preimage.2 hLc)
      ((AddSubgroup.isClosed_of_isOpen L hLo).preimage (hcont (y i))) fun w hw => ?_⟩
    · dsimp only
      rw [(hmk x' x).2 hx']
    · dsimp only
      rw [if_neg]
      intro h
      exact hw ((hmk w (y i)).1 (h.trans (hy i).symm))
  · dsimp only
    rw [hy j]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg (fun h' => h (he h').symm), if_neg h]
  · intro Ψ hΨ hper hsupp
    choose f hf using fun i => GlobalTheory.WeilCont.exists_slice F hΨ (y i)
    refine ⟨f, funext fun z => ?_⟩
    obtain ⟨x, w, rfl⟩ : ∃ x w, z = GlobalTheory.WeilCont.adeleJoin F x w :=
      ⟨fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1, fun i => (z i).2,
        funext fun i => Prod.ext (by simp only [GlobalTheory.WeilCont.adeleJoin, RingEquiv.symm_apply_apply]) rfl⟩
    simp only [Finset.sum_apply, GlobalTheory.WeilCont.pureA_adeleJoin, ← hf]
    by_cases hw : (QuotientAddGroup.mk w : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L) ∈ QuotientAddGroup.mk '' K
    · obtain ⟨i0, hi0⟩ := (hS _).1 hw
      rw [Finset.sum_eq_single i0]
      · rw [if_pos hi0.symm, mul_one, hf]
        have hL : w - y i0 ∈ L := (hmk w (y i0)).1 (hi0.symm.trans (hy i0).symm)
        rw [← hper _ hL (GlobalTheory.WeilCont.adeleJoin F x (y i0))]
        congr 1
        funext i
        simp only [GlobalTheory.WeilCont.adeleJoin, Pi.add_apply, Pi.sub_apply, Pi.zero_apply, map_zero]
        exact Prod.ext (add_zero _).symm (add_sub_cancel _ _).symm
      · intro j _ hj
        rw [if_neg (fun h => hj (he (h.symm.trans hi0.symm))), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have h0 : Ψ (GlobalTheory.WeilCont.adeleJoin F x w) = 0 := by
        by_contra h
        exact hw ⟨w, hsupp _ h, rfl⟩
      rw [h0]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rw [if_neg, mul_zero]
      intro h
      exact hw (h ▸ (hS _).2 ⟨i, rfl⟩)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceBelowExists
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.Frames GlobalTheory.HTLat
open scoped NNReal

namespace GlobalTheory

theorem placeBelow_exists {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
    (c : Coeff l) (σ : E →+* ℂ) (la : HeightOneSpectrum (𝓞 c.F)) : ∃ w : HeightOneSpectrum (𝓞 E),
      ∀ a : 𝓞 E, a ∈ w.asIdeal ↔ la.valuation c.F (embK c σ a) < 1 := by
  set f : 𝓞 E →+* 𝓞 c.F := RingOfIntegers.mapRingHom (embF c σ) with hf
  have hemb : ∀ a : 𝓞 E, embK c σ a = algebraMap (𝓞 c.F) c.F (f a) := fun _ => rfl
  obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot la.ne_bot
  have hZ : Ideal.comap (algebraMap ℤ (𝓞 c.F)) la.asIdeal ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hx0 hxI (Algebra.IsIntegral.isIntegral x)
  obtain ⟨n, hnI, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZ
  haveI : la.asIdeal.IsPrime := la.isPrime
  refine ⟨⟨la.asIdeal.comap f, Ideal.comap_isPrime f la.asIdeal, ?_⟩, fun a => ?_⟩
  · intro hbot
    have hmem : ((n : ℤ) : 𝓞 E) ∈ la.asIdeal.comap f := by
      rw [Ideal.mem_comap, map_intCast]
      simpa using hnI
    rw [hbot, Ideal.mem_bot] at hmem
    exact hn0 (by exact_mod_cast hmem)
  · show f a ∈ la.asIdeal ↔ _
    rw [hemb, HeightOneSpectrum.valuation_lt_one_iff_mem]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompaStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomialFockSpace_stable_archimedeanMaximalCompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (Y : Spc F E n) (W : Spc F E d) (M : Model σ Y W) (om : Rep σ Y W) (χ₁ χ₂ : Chr F E),
    B.IsGood σ → M.IsGood B.ψ → M.IsWeil B.ψ χ₁ χ₂ om → ∀ k ∈ KInf σ W B.emb,
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) (⇑f) (⇑f₁) → f₁ ∈ M.Pol B.ψ B.emb := by
  first | exact @GlobalTheory.KInfPol.pol_stable_kInf | exact GlobalTheory.KInfPol.pol_stable_kInf | (intros; apply GlobalTheory.KInfPol.pol_stable_kInf <;> assumption)
end

