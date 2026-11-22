import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0040
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RigFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0048
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0013
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0062
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0015
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0016
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0018
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.AppellHumbertMeanSquareEqOfProportionalSectionsStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appellHumbertMeanSquare_eq_of_proportional_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P P' : (F.Di k).La →+ (Fin g → ℂ)) (h₀ : Matrix (Fin g) (Fin g) ℂ) (x x' : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (a : ℂ) (m m' : ℝ), IsPeriod (F.Di k) ty P → IsPeriod (F.Di k) ty P' → (∀ v, P v = h₀ *ᵥ P' v) → x = F.u k P → x' = x → SecBC (RingHom.id ℂ) a x x' s s' → AHMean F k P x s m → AHMean F k P' x' s' m' → m' = ‖a‖ ^ 2 * m := by
  first | exact @GlobalTheory.FrameNorm.ahMean_eq_of_secBC | exact GlobalTheory.FrameNorm.ahMean_eq_of_secBC | (intros; apply GlobalTheory.FrameNorm.ahMean_eq_of_secBC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.BirationalOfFormRatiosFullTrdeg
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Reg

theorem birSt_of_ratios_trdeg :
    ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c), ∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF), ((∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ k₀, evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j) ≠ 0 ∧ Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F (Set.range fun k => evC hG Z ((G.w k : (recB h.toLawsCore).Cusp j wL) : T.R j) / evC hG Z ((G.w k₀ : (recB h.toLawsCore).Cusp j wL) : T.R j))) = WeightFamilies.dimY D j) → BIRSt h j hj hG G) ∧ (BigAt h j hj hG G → BIRSt h j hj hG G) := by
  intro D T h j hj hG ka wL wF G
  have htr := (GlobalTheory.FlagDim.fnFG_fnTrdeg_record D T.Q h.pins.2.2.2 j hj).2
  have hint := GlobalTheory.Reg.intFormSt_holds D T h j hj hG wL _ G.w
  exact ⟨fun hB => birSt_of h j hj hG htr G hB hint,
    fun hBig => birSt_of_big h j hj hG htr G hBig hint⟩

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsEvenSecEvRNeZero
section
set_option autoImplicit false

noncomputable section

open NumberField Topology ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.EtaForm

namespace GlobalTheory.Reg

theorem exists_even_sec_evR_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)), ∃ n : ℕ, 0 < n ∧ Even n ∧ ∃ f ∈ sec Xo c 0 n, evR Xo c f y ≠ 0 := by
  intro E _ _ _ H Dw l Xo c σ y
  have hR : Odd 3 := by decide
  have h1 : 1 < 3 := by decide
  obtain ⟨hfG, hfL, -⟩ := GlobalTheory.EtaCard.card_levGrp_and_span E H Dw 3 h1
  letI hFin : Fintype (LatMod Dw 3) := Fintype.ofFinite _
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  have hT : AllTest Xo c := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw l Xo c
  obtain ⟨cf, -, hne⟩ := GlobalTheory.EtaForm.exists_small_coeff_etaValAt_ne_zero GlobalTheory.firstFiveLaws.1 E H Dw l Xo c 3 hR h1
    2 0 (CAt σ) 1 (fun _ => y)
  obtain ⟨⟨f, hrule, -⟩, hsec⟩ := GlobalTheory.EtaForm.isEtaRule_existsUnique_mem_sec GlobalTheory.firstFiveLaws.1 E H Dw l Xo c 3 hR
    (Fin 2 → LatMod Dw 3) 2 (fun j => (cf j : ℤ)) (shiftFam 3 0)
  refine ⟨2 * Nat.card (LevGrp Dw (3 ^ 4)), Nat.mul_pos two_pos Nat.card_pos, even_two_mul _, f, hsec f hrule, ?_⟩
  exact hne 0 _ (GlobalTheory.EtaForm.etaValAt_evR_of_fromTest E H Dw l Xo c 3 hR _ _ _ _ f hrule (CAt σ) y (hT _ _)).1

end GlobalTheory.Reg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.NotGoodConj
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.FrameNorm.Existence

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem not_good_conj (σ : c.F →+* ℂ) (h : Formalism.L2.PjFree.GoodEmb c σ) :
    ¬ Formalism.L2.PjFree.GoodEmb c ((starRingEnd ℂ).comp σ) := by
  intro h'
  have h1 : (starRingEnd ℂ) H.rt0 = H.rt0 := by
    have e : (starRingEnd ℂ) ((σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ) = H.rt0 := h'
    unfold Formalism.L2.PjFree.GoodEmb at h
    rwa [h] at e
  have h2 : H.rt0.im = 0 := Complex.conj_eq_iff_im.mp h1
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  simp only [sq, Complex.mul_re, Complex.neg_re, Complex.natCast_re] at hre
  rw [h2] at hre
  nlinarith [mul_self_nonneg H.rt0.re]

theorem good_conj (σ : c.F →+* ℂ) (h : ¬ Formalism.L2.PjFree.GoodEmb c σ) :
    Formalism.L2.PjFree.GoodEmb c ((starRingEnd ℂ).comp σ) := by
  have := Formalism.L2.PjFree.goodEmb_goodOf c σ
  unfold Formalism.L2.PjFree.goodOf at this
  rwa [if_neg h] at this

theorem cabs_mul {K : Type} [Field K] {σ : K →+* ℂ} (a b : CAt σ) : cabs (a * b) = cabs a * cabs b :=
  norm_mul (show ℂ from a) (show ℂ from b)

theorem cabs_one {K : Type} [Field K] {σ : K →+* ℂ} : cabs (1 : CAt σ) = 1 :=
  norm_one (α := ℂ)

theorem cabs_unit_pos {K : Type} [Field K] {σ : K →+* ℂ} (a : (CAt σ)ˣ) : 0 < cabs (a : CAt σ) := by
  have h : cabs (a : CAt σ) * cabs ((a⁻¹ : (CAt σ)ˣ) : CAt σ) = 1 := by
    rw [← cabs_mul, Units.mul_inv, cabs_one]
  have h0 : 0 ≤ cabs (a : CAt σ) := norm_nonneg _
  refine lt_of_le_of_ne h0 fun e => ?_
  rw [← e, zero_mul] at h
  exact zero_ne_one h

theorem baseNorm_pos {x : ℝ} (hx : 0 < x) (i : Ix Dw) : 0 < baseNorm Dw x i := by
  cases i with
  | none => exact one_pos
  | some j => exact Real.sqrt_pos.mpr (by have := Real.pi_pos; positivity)

theorem cabs_eq {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) {k k'} (x : (U.X k).dom) (x' : (U.X k').dom) (t t' : Ix Dw → (CAt σ)ˣ)
    (y : FrPt Xo c (CAt σ)) (hx : IsUnitFr (U.X k) x.1) (hx' : IsUnitFr (U.X k') x'.1)
    (h : FrBor t (U.un k x) y) (h' : FrBor t' (U.un k' x') y) (i : Ix Dw) :
    cabs (t i : CAt σ) = cabs (t' i : CAt σ) := by
  have hi : FrBor t'⁻¹ y (U.un k' x') :=
    (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k' x') y y).2.2.2 t' h'
  have hc : FrBor (t'⁻¹ * t) (U.un k x) (U.un k' x') :=
    (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) (U.un k x) y (U.un k' x')).2.2.1 t t'⁻¹ h hi
  have h1 : cabs ((t'⁻¹ * t) i : CAt σ) = 1 := by
    cases i with
    | none => exact GlobalTheory.T.unitFrames_generatorRatio_modulus_one E H Dw l Xo c σ r U hσ hU k k' x x' _ hx hx' hc
    | some j => exact GlobalTheory.T.cabs_frBor_eq_one_of_unitFr E H Dw l Xo c σ r U hσ hU k k' x x' _ hx hx' hc j
  have e : (t i : CAt σ) = (t' i : CAt σ) * ((t'⁻¹ * t) i : CAt σ) := by
    rw [← Units.val_mul, Pi.mul_apply, Pi.inv_apply, mul_inv_cancel_left]
  rw [e, cabs_mul, h1, mul_one]

theorem exists_good {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) {xR : ℝ} (hx : 0 < xR) :
    ∃ G : FrPt Xo c (CAt σ) → Ix Dw → ℝ, (∀ y i, 0 < G y i) ∧
      ∀ k (z : (U.X k).dom), IsUnitFr (U.X k) z.1 → ∀ (t : Ix Dw → (CAt σ)ˣ) (y : FrPt Xo c (CAt σ)),
        FrBor t (U.un k z) y → ∀ i, G y i = cabs (t i : CAt σ) * baseNorm Dw xR i := by
  choose k x t hu hb using (GlobalTheory.T.exists_unit_gram_frame_borel_change E H Dw l Xo c σ r U hσ hU).2
  refine ⟨fun y i => cabs (t y i : CAt σ) * baseNorm Dw xR i,
    fun y i => mul_pos (cabs_unit_pos _) (baseNorm_pos hx i), ?_⟩
  intro k' z hz t' y hy i
  show _ * _ = _
  rw [cabs_eq U hσ hU (x y) z (t y) t' y (hu y) hz (hb y) hy i]

theorem transport {P : (c.F →+* ℂ) → Prop} (G : ∀ σ : c.F →+* ℂ, P σ → FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    {σ τ : c.F →+* ℂ} (e : τ = σ) (hσ : P σ) (hτ : P τ) (φ : CAt σ →ₐ[c.F] CAt τ)
    (hφ : ∀ z : CAt σ, (show ℂ from φ z) = (show ℂ from z)) (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt τ))
    (h : FrMap φ y y') : G τ hτ y' = G σ hσ y := by
  subst e
  have h1 : φ = AlgHom.id c.F (CAt τ) := AlgHom.ext hφ
  subst h1
  have u := GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ (AlgHom.id c.F (CAt τ)) y
  rw [u.1 _ _ h u.2.1]

theorem exists_pinned : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ xR : ℝ, 0 < xR → ∃ fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ, FnPin U xR fn ∧ FnNe Xo c fn := by
  classical
  intro E _ _ _ H Dw l Xo c r U hU xR hx
  choose G hpos hpin using fun (σ : c.F →+* ℂ) (hσ : Formalism.L2.PjFree.GoodEmb c σ) =>
    exists_good (U σ) hσ (hU σ hσ) hx
  choose bc hbc using fun (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) =>
    GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ (conjAlg σ) y
  refine ⟨fun σ y => if h : Formalism.L2.PjFree.GoodEmb c σ then G σ h y else G _ (good_conj σ h) (bc σ y), ⟨?_, ?_⟩, ?_⟩
  · intro σ hσ k z hz t y hy i
    simp only [dif_pos hσ]
    rw [abs_of_pos (hpos σ hσ y i)]
    exact hpin σ hσ k z hz t y hy i
  · intro σ y y' hy i
    by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
    · have hn := not_good_conj σ hσ
      simp only [dif_pos hσ, dif_neg hn]
      have hm : FrMap ((conjAlg ((starRingEnd ℂ).comp σ)).comp (conjAlg σ)) y (bc _ y') :=
        frMap_trans (Xo := Xo) (c := c) _ _ _ _ _ y y' _ hy (hbc _ y')
      have e : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp σ) = σ :=
        RingHom.ext fun a => Complex.conj_conj (σ a)
      rw [transport G e hσ (good_conj _ hn) _ (fun z => Complex.conj_conj (show ℂ from z)) y _ hm]
    · have hg := good_conj σ hσ
      simp only [dif_pos hg, dif_neg hσ]
      rw [(GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ (conjAlg σ) y).1 _ _ hy (hbc σ y)]
  · intro σ y i
    by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
    · simp only [dif_pos hσ]
      exact (hpos σ hσ y i).ne'
    · simp only [dif_neg hσ]
      exact (hpos _ _ _ i).ne'

end GlobalTheory.FrameNorm.Existence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormBddAboveISupEqCuspFormSupNorm
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.FrameNorm.SupNorm

theorem bdd_and_iSup_eq {α β : Type} (g : α → ℝ) (h : β → ℝ) (C : ℝ) (hC : 0 ≤ C) (hh : ∀ b, 0 ≤ h b)
    (h1 : ∀ a, ∃ b, g a = C * h b) (h2 : ∀ b, ∃ a, g a = C * h b)
    (hfin : (⨆ b, ENNReal.ofReal (h b)) ≠ ⊤) :
    BddAbove (Set.range g) ∧ (⨆ a, g a) = C * (⨆ b, ENNReal.ofReal (h b)).toReal := by
  have hle : ∀ b, h b ≤ (⨆ b, ENNReal.ofReal (h b)).toReal := fun b =>
    (ENNReal.ofReal_le_iff_le_toReal hfin).1 (le_iSup (fun b => ENNReal.ofReal (h b)) b)
  have hr : Set.range g = Set.range fun b => C * h b := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := h1 a
      exact ⟨b, hb.symm⟩
    · rintro ⟨b, rfl⟩
      exact h2 b
  refine ⟨⟨C * (⨆ b, ENNReal.ofReal (h b)).toReal, ?_⟩, ?_⟩
  · rw [hr]
    rintro _ ⟨b, rfl⟩
    exact mul_le_mul_of_nonneg_left (hle b) hC
  · rw [ENNReal.toReal_iSup (fun b => ENNReal.ofReal_ne_top), Real.mul_iSup_of_nonneg hC]
    unfold iSup
    rw [hr]
    simp only [ENNReal.toReal_ofReal (hh _)]

theorem supBdd_and_supR_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ a n, Dom a n → ∀ f ∈ Formalism.L2.PjFree.cusp Xo c U a n, SupBdd Xo c fn a n f ∧ ∀ σ, supR Xo c fn σ a n f = Formalism.L2.PjFree.supC Xo c U xR (Formalism.L2.PjFree.goodOf c σ) a n f := by
  intro E _ _ _ H Dw l Xo c r U hU xR fn hx hfn a n hd f hf
  obtain ⟨-, htie, hconj⟩ := GlobalTheory.T.pointwise_norm_section_eq_flagDomain_norm E H Dw l Xo c r U hU xR fn hx hfn
  have hs : f ∈ sec Xo c a n := Formalism.L2.PjFree.cusp_le_sec Xo c U a n hf
  have hB : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  let N : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → ℝ := fun σ =>
    ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f
  have hgood : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ →
      BddAbove (Set.range (N σ)) ∧ (⨆ y, N σ y) = Formalism.L2.PjFree.supC Xo c U xR σ a n f := by
    intro σ hσ
    refine bdd_and_iSup_eq (N σ)
      (fun p : Formalism.L2.PjFree.FPt (U σ).X =>
        ((U σ).X p.1).pnorm (Formalism.L2.PjFree.laU (U σ) a n p.1) (Formalism.L2.PjFree.rdU (U σ) f p.1) p.2)
      (Formalism.L2.PjFree.lieFac Dw xR a) (Formalism.L2.PjFree.lieFac_pos Dw xR a).le
      (fun p => mul_nonneg (norm_nonneg _) (Formalism.L2.PjFree.pnorm_fac_nonneg _ _ _)) (fun y => ?_) (fun p => ?_)
      (Formalism.L2.PjFree.supE_cusp_ne_top hσ hf)
    · obtain ⟨k, x, t, ht⟩ := (hU σ hσ).2.2.1 y
      exact ⟨⟨k, x⟩, htie σ hσ k x t y ht a n hd f hs⟩
    · exact ⟨(U σ).un p.1 p.2, htie σ hσ p.1 p.2 1 _
        ((GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)).1 _) a n hd f hs⟩
  have hsub : ∀ σ τ : c.F →+* ℂ, τ = (starRingEnd ℂ).comp σ → Set.range (N σ) ⊆ Set.range (N τ) := by
    rintro σ τ rfl _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c _ _ (conjAlg σ) y
    exact ⟨z, hconj σ y z hz a n f hs⟩
  have hr : ∀ σ : c.F →+* ℂ, Set.range (N σ) = Set.range (N (Formalism.L2.PjFree.goodOf c σ)) := by
    intro σ
    by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
    · have e : Formalism.L2.PjFree.goodOf c σ = σ := if_pos hσ
      exact (hsub _ _ rfl).trans (hsub _ _ (by rw [e]; ext x; simp)) |>.antisymm
        ((hsub _ _ rfl).trans (hsub _ _ (by rw [e]; ext x; simp)))
    · have e : Formalism.L2.PjFree.goodOf c σ = (starRingEnd ℂ).comp σ := if_neg hσ
      exact (hsub _ _ e).antisymm (hsub _ _ (by rw [e]; ext x; simp))
  refine ⟨fun σ => ?_, fun σ => ?_⟩
  · show BddAbove (Set.range (N σ))
    rw [hr σ]
    exact (hgood _ (Formalism.L2.PjFree.goodEmb_goodOf c σ)).1
  · show sSup (Set.range (N σ)) = _
    rw [hr σ]
    exact (hgood _ (Formalism.L2.PjFree.goodEmb_goodOf c σ)).2

end GlobalTheory.FrameNorm.SupNorm
end

