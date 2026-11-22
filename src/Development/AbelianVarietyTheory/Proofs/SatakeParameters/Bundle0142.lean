import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0136
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0131
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0134
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalThetaPairExistence
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesTrivial
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0041
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0129
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KapGEqCharInf
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

theorem embT_mem_qbar (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral x).map (TaylorLogMetric.embT D τ).toRatAlgHom

theorem lamC_qbar {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (q : TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (algebraMap TaylorLogMetric.Qbar ℂ q) = lam q := by
  unfold TaylorLogMetric.lamC
  rw [dif_pos (show algebraMap TaylorLogMetric.Qbar ℂ q ∈ TaylorLogMetric.Qbar from q.2)]
  rfl

theorem kapG_eq_char_inf : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E pos lam ρ → ∀ (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) (a : D.host.E), a * D.host.conj a = 1 → (∀ v, (gamAt X j c γ v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det = ρ v a) → letI := wittFractionAlgebraCp p; letI := algKfC E; kapG X ℂ_[p] j c γ = E.iK (algebraMap X.G.O X.G.Kf (((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O)) * TaylorLogMetric.lamC lam (∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v), TaylorLogMetric.embT D (pos ⟨v, s⟩) a ^ X.w v (j + 1) s) * (p : ℂ_[p]) ^ (-(∑ v : X.Pl, X.vm v (j + 1) * ordP (X.G.P.W v) p (ρ v a))) := by
  intro D p _ X E pos lam ρ hLP j c γ a ha hdet
  letI := wittFractionAlgebraCp p
  letI := algKfC E
  have hp : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_mul] at ha
    exact zero_ne_one ha
  have hconj : D.host.conj a = a⁻¹ := eq_inv_of_mul_eq_one_right ha

  have hcA : cA X ℂ_[p] j (gamAt X j c γ) =
      TaylorLogMetric.lamC lam (∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v), TaylorLogMetric.embT D (pos ⟨v, s⟩) a ^ X.w v (j + 1) s) := by
    let q : ∀ v : X.Pl, Fin (X.G.P.n' v) → TaylorLogMetric.Qbar := fun v s => ⟨TaylorLogMetric.embT D (pos ⟨v, s⟩) a, embT_mem_qbar D _ a⟩
    have h1 : (∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v), TaylorLogMetric.embT D (pos ⟨v, s⟩) a ^ X.w v (j + 1) s) =
        algebraMap TaylorLogMetric.Qbar ℂ (∏ v : X.Pl, ∏ s : Fin (X.G.P.n' v), q v s ^ X.w v (j + 1) s) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [map_prod]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [map_zpow₀]
      rfl
    rw [h1, lamC_qbar, map_prod]
    unfold cA
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_zpow₀, hdet v]
    have h2 : lam (q v s) = twG X E v s (ρ v (if IsOddPos s then D.host.conj a else a)) := by
      rw [← hLP v s a, ← lamC_qbar lam (q v s)]
      rfl
    rw [h2, twG_eq_tw]
    by_cases hs : IsOddPos s
    · rw [if_pos hs, if_pos hs, hconj, map_inv₀, map_inv₀, inv_zpow', neg_one_mul]
    · rw [if_neg hs, if_neg hs, one_mul]
  have hP : (∏ v : X.Pl, (p : ℂ_[p]) ^ (-(X.vm v (j + 1) * ordP (X.G.P.W v) p
      (gamAt X j c γ v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det))) =
      (p : ℂ_[p]) ^ (-(∑ v : X.Pl, X.vm v (j + 1) * ordP (X.G.P.W v) p (ρ v a))) := by
    simp_rw [hdet]
    rw [← Finset.sum_neg_distrib]
    induction (Finset.univ : Finset X.Pl) using Finset.cons_induction with
    | empty => simp
    | cons b s hb ih => rw [Finset.sum_cons, Finset.prod_cons, zpow_add₀ hp, ih]
  unfold kapG
  rw [hcA, hP]
  rfl

end GlobalTheory.TwV.Xc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst

theorem StLat.not_frac (l : ℕ) [Fact l.Prime] (Co : Core l) (ϖ : Per.Fl l)
    (hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l)) (u : Per.BdRp l) (hu : IsLogP (beta ϖ) u) (x y : Per.Bcris l)
    (hx : Co.ι x ≠ 0) : Co.ι y ≠ Co.ι x * algebraMap (Per.BdRp l) (Per.BdR l) u := by
  intro h
  obtain ⟨hdom, hdvr, hmax, hmaxθ, -, hfilt, hfr⟩ := BdRDVR.core_dvr l Co
  have hker := GlobalTheory.T.kerP_eq_span_beta_of_untilt_eq l ϖ hϖ
  have hfil := GlobalTheory.T.filP_eq_span_betaD_pow_of_kerP_eq_span_beta l Co ϖ hker
  have hinjD : Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := IsFractionRing.injective _ _
  have hβ0 : betaD ϖ ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field (Per.BdRp l)
    rw [hmax, ← pow_one (Co.j Co.t), ← hfilt 1, hfil 1, h0, pow_one, Ideal.span_singleton_eq_bot]
  have hsep : ∀ z : Per.BdRp l, (∀ n : ℕ, betaD ϖ ^ n ∣ z) → z = 0 := by
    intro z hz
    have hne : Ideal.span {betaD ϖ} ≠ ⊤ := by
      rw [← pow_one (betaD ϖ), ← hfil 1, hfilt 1, pow_one, ← hmax]
      exact (IsLocalRing.maximalIdeal.isMaximal (Per.BdRp l)).ne_top
    have h1 : z ∈ ⨅ n : ℕ, Ideal.span {betaD ϖ} ^ n := by
      refine (Submodule.mem_iInf _).2 fun n => ?_
      rw [Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton.2 (hz n)
    rwa [Ideal.iInf_pow_eq_bot_of_isDomain _ hne, Ideal.mem_bot] at h1
  obtain ⟨r, ax, hax⟩ := bcris_eq_acris_localization_periodT_alt l Co x
  obtain ⟨r', ay, hay⟩ := bcris_eq_acris_localization_periodT_alt l Co y
  set tt := algebraMap (Per.Acris l) (Per.Bcris l) Co.t with htt
  have e1 : algebraMap (Per.Acris l) (Per.Bcris l) (ax * Co.t ^ r') = x * tt ^ (r + r') := by
    rw [map_mul, map_pow, ← hax, pow_add]; ring
  have e2 : algebraMap (Per.Acris l) (Per.Bcris l) (ay * Co.t ^ r) = y * tt ^ (r + r') := by
    rw [map_mul, map_pow, ← hay, pow_add]; ring
  have e3 : Co.j (ay * Co.t ^ r) = Co.j (ax * Co.t ^ r') * u := by
    apply hinjD
    rw [map_mul (algebraMap (Per.BdRp l) (Per.BdR l)), ← Co.ι_j, ← Co.ι_j, e1, e2, map_mul Co.ι, map_mul Co.ι, h]
    ring
  have hA := GlobalTheory.T.acris_mem_betaAdicClosure_ainfAdjoinBeta l Co.j Co.j_cris ϖ (GlobalTheory.T.divPowerEnvelope_mem_ainfAdjoinBeta l ϖ hϖ) hfil
  have hz := GlobalTheory.T.eq_zero_of_mem_clos_of_pow_mul_mul_mem_clos l (Fact.out : l.Prime) (isUnit_l_BdRp l) (betaD ϖ) hβ0 hsep (Sg ϖ)
    (GlobalTheory.T.ainfAdjoinBetaImage_div_beta_pow l ϖ hϖ hker hfil) (GlobalTheory.T.betaImageDeRhamPlus_dvd_of_lAdic_residues l ϖ hker hfil) u
    (GlobalTheory.T.log_period_congruence_bdr l ϖ hker hfil u hu) (Co.j (ax * Co.t ^ r')) 0 (hA _) (by
      rw [pow_zero, one_mul, ← e3]; exact hA _)
  have hz2 : Co.ι (x * tt ^ (r + r')) = 0 := by
    rw [← e1, Co.ι_j, hz, map_zero]
  have htne : Co.ι tt ≠ 0 := by
    rw [htt, Co.ι_j]
    intro h0
    have h3 : Co.j Co.t = 0 := hinjD (h0.trans (map_zero _).symm)
    apply IsDiscreteValuationRing.not_a_field (Per.BdRp l)
    rw [hmax, h3, Ideal.span_singleton_eq_bot]
  haveI : IsDomain (Per.BdR l) := IsFractionRing.isDomain (Per.BdRp l)
  rw [map_mul, map_pow] at hz2
  exact mul_ne_zero hx (pow_ne_zero _ htne) hz2

theorem StLat.kummer_not_frac : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (b b' : P.R.B), b ≠ 0 →
  ¬ ∀ g ∈ GK K, b * P.actQ g b' - P.actQ g b * b' = b * P.actQ g b * ((kummer P g : ℚ_[l]) • P.tB) := by
  intro l _ P AI T K b b' hb h
  haveI : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T (botExt l)
  obtain ⟨x, y, hx, hxy⟩ := GlobalTheory.T.exists_kummerFracCoboundary_full_galois l P K b b' hb h
  obtain ⟨Co, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨ϖ, hr⟩ := exists_tilt (lRoot l) (lRoot_succ l) l (lRoot_zero l)
  have hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l) := Subtype.ext (by
    have := hr 0
    rw [lRoot_zero, map_natCast] at this
    exact this.trans (SubringClass.coe_natCast _ _).symm)
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_logOnePlus_kerTheta_deRhamPlus l (beta ϖ) (by
    rw [GlobalTheory.T.kerP_eq_span_beta_of_untilt_eq l ϖ hϖ]; exact Ideal.mem_span_singleton_self _)
  have hg := GlobalTheory.T.galois_logTeichmullerRatio_eq_add_kummer l P Co hC.ζ ϖ hr hϖ u hu
  letI : Field P.R.BdR := (GlobalTheory.RegularRing.isField_of_tied T).toField
  set U := T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) u) with hUdef
  have hct : ∀ g : GQ l, T.eD (P.ιB ((kummer P g : ℚ_[l]) • P.tB)) =
      algebraMap (Per.BdRp l) (Per.BdR l)
        (Co.j (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (kummer P g)) * Co.t)) := by
    intro g
    rw [hC.ι, Algebra.smul_def, map_mul, T.zB, hC.t, ← Co.ι_j]
    simp only [Core.tB, GlobalTheory.RingIface.zB_alg, map_mul]
  have hU : ∀ g : GQ l, P.actQdR g U = U + P.ιB ((kummer P g : ℚ_[l]) • P.tB) := by
    intro g
    apply T.eD.injective
    rw [T.actD, hUdef, RingEquiv.apply_symm_apply, map_add, RingEquiv.apply_symm_apply, hct]
    rw [show Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) u) =
      algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g u) from
        GlobalTheory.RingIface.sigD_alg l g u, hg, map_add]
  have hcomm : ∀ (g : GQ l) (z : P.R.B), P.ιB (P.actQ g z) = P.actQdR g (P.ιB z) := by
    intro g z
    have := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ z
    rwa [P.PD_ι, P.PD_actB, P.PD_ι, P.PD_actdR] at this
  have hX : P.ιB x ≠ 0 := fun h0 => hx ((P.PD (botExt l)).ι_inj (by rw [P.PD_ι, h0, map_zero]))
  have hgX : ∀ g : GQ l, P.actQdR g (P.ιB x) ≠ 0 := fun g h0 =>
    hX ((P.actQdR g).injective (h0.trans (map_zero _).symm))
  have hW : ∀ g : GQ l, P.actQdR g (P.ιB y * (P.ιB x)⁻¹ - U) = P.ιB y * (P.ιB x)⁻¹ - U := by
    intro g
    have h1 := congrArg P.ιB (hxy g)
    simp only [map_sub, map_mul, hcomm] at h1
    rw [map_sub, map_mul, map_inv₀, hU]
    have hx1 := mul_inv_cancel₀ hX
    have hx2 := mul_inv_cancel₀ (hgX g)
    linear_combination ((P.ιB x)⁻¹ * (P.actQdR g (P.ιB x))⁻¹) * h1
      - (P.actQdR g (P.ιB y) * (P.actQdR g (P.ιB x))⁻¹) * hx1 + (P.ιB y * (P.ιB x)⁻¹) * hx2
      + (P.ιB ((kummer P g : ℚ_[l]) • P.tB) * P.actQdR g (P.ιB x) * (P.actQdR g (P.ιB x))⁻¹) * hx1
      + P.ιB ((kummer P g : ℚ_[l]) • P.tB) * hx2
  obtain ⟨c, hc⟩ := (P.PD (botExt l)).invdR (P.ιB y * (P.ιB x)⁻¹ - U) fun g => by
    rw [P.PD_actdR]; exact hW g
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 c.2
  have hca : algebraMap ↥(botExt l).1 P.R.BdR c = algebraMap ℚ_[l] P.R.BdR a := by
    have e : c = algebraMap ℚ_[l] ↥(botExt l).1 a := Subtype.ext ha.symm
    rw [e, ← IsScalarTower.algebraMap_apply]
  rw [hca] at hc
  have hY : P.ιB (y - a • x) = P.ιB x * U := by
    rw [map_sub, map_smul, Algebra.smul_def]
    have hx1 := mul_inv_cancel₀ hX
    linear_combination (-P.ιB x) * hc - P.ιB y * hx1
  apply StLat.not_frac l Co ϖ hϖ u hu (T.eB x) (T.eB (y - a • x))
  · rw [← hC.ι]
    exact fun h0 => hX (T.eD.injective (h0.trans (map_zero _).symm))
  · rw [← hC.ι, ← hC.ι, hY, map_mul, hUdef, RingEquiv.apply_symm_apply]

theorem stRegular : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    IsDomain (Bst P) ∧
    (∀ (K : FinExt l) (b b' : Bst P), b ≠ 0 →
      (∀ g : ↥(GK K), b * actSt P (g : GQ l) b' = actSt P (g : GQ l) b * b') →
      ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ b' = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c * b) ∧
    (∀ (K : FinExt l) (b : Bst P), b ≠ 0 →
      (∀ g : ↥(GK K), ∃ x : ℚ_[l], actSt P (g : GQ l) b = algebraMap ℚ_[l] (Bst P) x * b) → IsUnit b) := by
  intro l _ P AI ⟨T⟩
  haveI : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T (botExt l)
  obtain ⟨Co, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  have hinj : Co.TensorInj := GlobalTheory.Published.FontaineBcris_holds.tensorInj Co
  have hreg : Co.Regular := GlobalTheory.Published.FontaineBcris_holds.regular Co
  refine ⟨inferInstance, fun K b b' hb h => ?_, fun K b hb h => ?_⟩
  · haveI : CharZero P.R.B := by
      have := (algebraMap ℚ_[l] P.R.B).injective
      exact charZero_of_injective_algebraMap this
    have hA : ∀ (g : GQ l) (p : Bst P), actSt P g p = (p.map ((P.actQ g).toRingEquiv : P.R.B →+* P.R.B)).comp (X + C ((kummer P g : ℚ_[l]) • P.tB)) :=
      fun g p => stHom_apply P (P.actQ g) _ p
    obtain ⟨d, d', hd, e, hf⟩ := GlobalTheory.T.twistedShift_fixed_ratio_const_domain (fun g : ↥(GK K) => (P.actQ (g : GQ l)).toRingEquiv)
      (fun g => (kummer P (g : GQ l) : ℚ_[l]) • P.tB)
      (fun d d' hd hh => StLat.kummer_not_frac l P AI T K d d' hd fun g hg => hh ⟨g, hg⟩) b' b hb (fun g => by
        rw [← hA, ← hA]; exact h g)
    obtain ⟨c, hc⟩ := GlobalTheory.RegularRing.fracInv hC hinj K d d' hd fun g => by
      rw [P.PD_actB, P.PD_actB]; exact hf g
    refine ⟨⟨c, c.2.2⟩, c.2.1, ?_⟩
    have hd' : (C d : Bst P) ≠ 0 := C_ne_zero.2 hd
    apply mul_left_cancel₀ hd'
    have hK0 : algebraMap ↥(K0 K) P.R.B c = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨c, c.2.2⟩ := rfl
    rw [e, hc, Polynomial.algebraMap_apply, C_mul, hK0]
    ring
  · have hK : ∀ b : P.R.B, ¬ ∀ g ∈ GK K, P.actQ g b - b = (kummer P g : ℚ_[l]) • P.tB :=
      GlobalTheory.Pst.NoLog.kummer_not_coboundary l P AI T K
    exact GlobalTheory.T.isUnit_of_stable_line' l P K hK (GlobalTheory.RegularRing.lineUnit hC hreg K) b hb h

end GlobalTheory.Pst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeModelVacuumTranslateClassesIndependent
section
namespace GlobalTheory.Hk3

theorem locVac_span_classes_indep : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, GlobalTheory.Hk3.LocVac ρ s →
    iSupIndep (fun c : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n =>
      Submodule.span ℂ {w : M | ∃ x : Matrix (Fin n') (Fin n) L,
        (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ GlobalTheory.Hk3.HoweDuality.intMat L n' n) = c ∧ w = ρ x s}) := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hvac
  classical
  obtain ⟨hU, -, hSint, hTint, hS, hT, hδ, -, hpsi_ne, hρ0, hρ, -, -, -⟩ := hP
  have hσ := hU.1
  have hA : ∀ x y : Matrix (Fin n') (Fin n) L, σ (locH σ δ JS JT x y) = - locH σ δ JS JT y x :=
    locH_conj σ hσ δ hδ.2 JS JT hS hT
  have hψinv : ∀ a, ψ a * ψ (-a) = 1 := fun a => by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have hΛ : intMatSub (L := L) n n' = HoweDuality.intMat L n' n := AddSubgroup.ext fun _ => Iff.rfl
  have hshift : ∀ t, LocVac ρ t → ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ (x + u) t = ψ (-((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2)) • ρ x t := by
    intro t ht x u hu
    have h1 : ρ x t = ψ ((locH σ δ JS JT x u + σ (locH σ δ JS JT x u)) / 2) • ρ (x + u) t := by
      have := congrArg (fun f => f t) (hρ x u)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
      rwa [ht u hu] at this
    rw [h1, smul_smul, mul_comm, hψinv, one_smul]
  have heig : ∀ t, LocVac ρ t → ∀ x u, u ∈ intMatSub (L := L) n n' →
      ρ u (ρ x t) = ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) • ρ x t := by
    intro t ht x u hu
    have := congrArg (fun f => f t) (hρ u x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, add_comm u x, hshift t ht x u hu, smul_smul, ← AddChar.map_add_eq_mul]
    congr 2
    rw [hA u x, hA x u]; ring
  have hdist : ∀ x y : Matrix (Fin n') (Fin n) L, (∀ u ∈ intMatSub (L := L) n n',
      ψ (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) = ψ (locH σ δ JS JT u y + σ (locH σ δ JS JT u y))) →
      x - y ∈ intMatSub (L := L) n n' := by
    intro x y hxy
    refine intMat_of_psi hU hδ.1 hSint hTint ψ hpsi_ne (x - y) (fun u hu => ?_)
    have e : locH σ δ JS JT u (x - y) + σ (locH σ δ JS JT u (x - y)) =
        (locH σ δ JS JT u x + σ (locH σ δ JS JT u x)) + -(locH σ δ JS JT u y + σ (locH σ δ JS JT u y)) := by
      rw [locH_sub_right, map_sub]; ring
    rw [e, AddChar.map_add_eq_mul, hxy u hu, hψinv]
  set Λ := HoweDuality.intMat L n' n with hΛdef

  have hle : (fun c : Matrix (Fin n') (Fin n) L ⧸ Λ =>
      Submodule.span ℂ {w : M | ∃ x : Matrix (Fin n') (Fin n) L,
        (QuotientAddGroup.mk x : Matrix (Fin n') (Fin n) L ⧸ Λ) = c ∧ w = ρ x s}) ≤
      fun c => Submodule.span ℂ {ρ c.out s} := by
    intro c
    refine Submodule.span_le.mpr ?_
    rintro w ⟨x, hx, rfl⟩
    have hm : -c.out + x ∈ intMatSub (L := L) n n' := by
      rw [hΛ]
      exact QuotientAddGroup.eq.mp (by rw [QuotientAddGroup.out_eq', hx])
    have := hshift s hvac c.out _ hm
    rw [add_neg_cancel_left] at this
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  refine iSupIndep.mono ?_ hle
  by_cases hs : s = 0
  · have hb : (fun c : Matrix (Fin n') (Fin n) L ⧸ Λ => Submodule.span ℂ {ρ c.out s}) = fun _ => ⊥ := by
      funext c; rw [hs, map_zero, Submodule.span_singleton_eq_bot]
    rw [hb, iSupIndep_def]
    intro i
    exact disjoint_bot_left
  have hnz : ∀ x, ρ x s ≠ 0 := by
    intro x h0
    have := congrArg (fun f => f s) (hρ (-x) x)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, h0, map_zero, neg_add_cancel, hρ0,
      Module.End.one_apply] at this
    have hne : ψ ((locH σ δ JS JT (-x) x + σ (locH σ δ JS JT (-x) x)) / 2) ≠ 0 := by
      intro h; have := hψinv ((locH σ δ JS JT (-x) x + σ (locH σ δ JS JT (-x) x)) / 2); rw [h, zero_mul] at this
      exact zero_ne_one this
    exact hs ((smul_eq_zero.mp this.symm).resolve_left hne)
  refine LinearIndependent.iSupIndep_span_singleton ?_
  rw [linearIndependent_iff']
  intro I C hC y hy
  have hind := eig_indep (fun u : intMatSub (L := L) n n' => ρ (u : Matrix (Fin n') (Fin n) L))
    (fun (y : Matrix (Fin n') (Fin n) L ⧸ Λ) (u : intMatSub (L := L) n n') =>
      ψ (locH σ δ JS JT (u : Matrix (Fin n') (Fin n) L) y.out + σ (locH σ δ JS JT (u : Matrix (Fin n') (Fin n) L) y.out)))
    (fun y => ρ y.out s) (fun y u => heig s hvac y.out u u.2) I
    (by
      intro y _ y' _ hyy
      by_contra hcon
      push_neg at hcon
      apply hyy
      have hm := hdist y.out y'.out (fun u hu => hcon ⟨u, hu⟩)
      rw [hΛ] at hm
      rw [← QuotientAddGroup.out_eq' y, ← QuotientAddGroup.out_eq' y', QuotientAddGroup.eq_iff_sub_mem]
      exact hm)
    C hC
  exact (smul_eq_zero.mp (hind y hy)).resolve_right (hnz _)

end GlobalTheory.Hk3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LenSmulTup
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

namespace GlobalTheory.TwV.Xc

theorem len_smul_tup : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (j : ℕ) (c : X.Lv.comp j) (γ : (X.Lv.lev j c).Γ) (L : (X.Pj j).Tup), (X.Pj j).IsLatTup L → ∀ v, len X v j ((X.Lv.lev j c).smul γ L) = len X v j L - ordP (X.G.P.W v) p (gamAt X j c γ v : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)).det := by
  intro p _ X j c γ L hL v
  exact Formalism.L2.G.Pend.len_smul X j c γ L hL v

end GlobalTheory.TwV.Xc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalCharDetEqOneOfCongrOneModPowStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localChar_det_eq_one_of_congr_one_mod_pow : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (i : ℕ) (P : rowSG Pr sel mu) (n : ℕ) (k : Sp X.E n ≃ₗ[X.E] Sp X.E n),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E n) l))) →
    muAt Ch sel mu cst i P ((LinearEquiv.det k : X.Eˣ) : X.E) = 1 := by
  first | exact @GlobalTheory.AwayMat.muAt_det_congr_one | exact GlobalTheory.AwayMat.muAt_det_congr_one | (intros; apply GlobalTheory.AwayMat.muAt_det_congr_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalThetaPairExistenceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locPair_vacuum_relation_independent : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ c : Matrix (Fin n') (Fin n) L →₀ ℂ, ∀ s, s ≠ 0 → LocVac ρ s → (c.sum fun x z => z • ρ x s) = 0 → ∀ s', LocVac ρ s' → (c.sum fun x z => z • ρ x s') = 0 := by
  first | exact @GlobalTheory.Hk3.locVac_rel_indep | exact GlobalTheory.Hk3.locVac_rel_indep | (intros; apply GlobalTheory.Hk3.locVac_rel_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixLatticeIndexIntegralTranslationInvarianceStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixLatticeIndex_integral_translation_invariance : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (a b : ℕ) (x : Matrix (Fin a) (Fin b) L),
    (∀ u ∈ GlobalTheory.Hk3.HoweDuality.intMat L a b, GlobalTheory.Hk3.HoweDuality.latIdx (x + u) = GlobalTheory.Hk3.HoweDuality.latIdx x) ∧
    ∀ h : GL (Fin a) L, h ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) →
      GlobalTheory.Hk3.HoweDuality.latIdx ((h : Matrix (Fin a) (Fin a) L) * x) = GlobalTheory.Hk3.HoweDuality.latIdx x := by
  first | exact @GlobalTheory.Hk3.HoweDuality.latIdx_invariance | exact GlobalTheory.Hk3.HoweDuality.latIdx_invariance | (intros; apply GlobalTheory.Hk3.HoweDuality.latIdx_invariance <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLat
section
noncomputable section

namespace GlobalTheory.VolAt

open Formalism.MainNotions.G Matrix

def homLat (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k k' : ℕ}
    (A : Submodule W (Fin k → Qq)) (B : Submodule W (Fin k' → Qq)) : Submodule W (Matrix (Fin k') (Fin k) Qq) where
  carrier := {x | ∀ z ∈ A, x *ᵥ z ∈ B}
  zero_mem' := fun z _ => by rw [Matrix.zero_mulVec]; exact B.zero_mem
  add_mem' := fun hx hy z hz => by rw [Matrix.add_mulVec]; exact B.add_mem (hx z hz) (hy z hz)
  smul_mem' := fun c x hx z hz => by
    rw [Matrix.smul_mulVec]
    exact B.smul_mem c (hx z hz)

theorem mem_homLat (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k k' : ℕ}
    (A : Submodule W (Fin k → Qq)) (B : Submodule W (Fin k' → Qq)) (x : Matrix (Fin k') (Fin k) Qq) :
    x ∈ homLat W A B ↔ ∀ z ∈ A, x *ᵥ z ∈ B := Iff.rfl

end GlobalTheory.VolAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChartStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_homLattice_iff_integralMatrix_splitChart : ∀ {D : D7} (e : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D e → Chart e v π → ∀ (S T : HSp D) (βS : GL (Fin S.rank) (Fv D.host.F v)) (βT : GL (Fin T.rank) (Fv D.host.F v)), Frame S e π βS → Frame T e π βT → ∃ c : Fv D.host.F v, c ≠ 0 ∧ ∀ u : WO S T, IsHalf e u → (u ∈ latO S T (L0c D S) (L0c D T) (fun _ => True) ↔ IntM (Ov D v) (c • ((βT⁻¹).1 * Matrix.map u π * βS.1))) := by
  first | exact @GlobalTheory.SplitHomLattice.mem_latO_iff_intM | exact GlobalTheory.SplitHomLattice.mem_latO_iff_intM | (intros; apply GlobalTheory.SplitHomLattice.mem_latO_iff_intM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralFiniteAdelesTensorIffLocalOrdersStatement
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_integralFiniteAdelesTensor_iff_localOrders : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (z : Af F ⊗[F] E), z ∈ intA F E ↔ ∀ v : HeightOneSpectrum (𝓞 F), evF E v z ∈ ordAt E v := by
  first | exact @GlobalTheory.PlaceComp.IntLocal.mem_intA_iff | exact GlobalTheory.PlaceComp.IntLocal.mem_intA_iff | (intros; apply GlobalTheory.PlaceComp.IntLocal.mem_intA_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemPlacesOverOfNeAlt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.InertialTypes

theorem not_mem_placesOver_of_ne {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ placesOver E p) : w ∉ placesOver E q := by
  intro hw'
  have hc : IsCoprime (p : 𝓞 E) (q : 𝓞 E) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left a hw) (w.asIdeal.mul_mem_left b hw')

theorem main : ∀ (D : D7) (T : WDTie D.nd D.naut) (S : Reading T), TameSplitAll D.host.E → BlockSplitAll D.host.E → Laws S → SuppLaws S → ChiIne D.nd D.naut → (∀ i w hw, (w ∈ D.nd.Q i ∨ (w ∈ D.nd.S i ∧ ∀ k, w ∉ placesOver D.host.E (D.host.g k))) → TypeTame S i w hw) → (∀ i w hw, (w ∈ D.nd.S i ∨ w ∈ D.nd.Q i) → TypeBlock S i w hw) → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D := by
  intro D T S hTS hBS hL hS hchi hT hB
  refine ⟨fun i P w hSQ hc => ?_, fun i P w hwS _ _ hm => ?_, (GlobalTheory.RowLaws.main _ _ _ _ _ T).2.2⟩
  · have hw := D.nd.SQ_split i w hSQ
    refine GlobalTheory.TameType.inertialType_of_tame _ _ _ _ _ T S i w hw hTS hL (hT i w hw ?_)
      (hchi i w (D.nd.SQ_l i w hSQ)) P
    by_cases hQ : w ∈ D.nd.Q i
    · exact Or.inl hQ
    · refine Or.inr ⟨hSQ.resolve_right hQ, fun k => ?_⟩
      rcases (hc.resolve_left hQ).2 with h | ⟨-, h⟩
      · exact not_mem_placesOver_of_ne D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 h
      · exact not_mem_placesOver_of_ne D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 h
  · have hw := D.nd.SQ_split i w (Or.inl hwS)
    exact GlobalTheory.SplitRead.BlockParam.split_param _ _ _ _ _ T S i w hw hBS hL hS (hB i w hw (Or.inl hwS))
      (hchi i w (D.nd.SQ_l i w (Or.inl hwS))) P hm

end GlobalTheory.InertialTypes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitBoundStandardSeriesInertPlacesStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitBound_standardSeries_inertPlaces : ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (Ee : OrbitPlaces.Ent D), OrbitPlaces.Shape D L X Ee → (∀ u, ∀ i < D.R.m, ∀ t ∈ D.host.TT, Ee.row u i (false, t) 0 - Ee.row u i (false, t) 1 ≤ 2 * L.sc.a) → 5 ≤ K.dl1 → 4 ≤ K.dl2 → BeFam D Ee.ep Ee.be → (Ee.sg = fun _ _ => -1) → OrbitPlaces.OrbitBoundWithoutOperator Ee X K := by
  first | exact @GlobalTheory.OrbitBoundStdRec.orbit_bound_rec | exact GlobalTheory.OrbitBoundStdRec.orbit_bound_rec | (intros; apply GlobalTheory.OrbitBoundStdRec.orbit_bound_rec <;> assumption)
end

