import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0408
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0149
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0106
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0247
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0432
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0481
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0418
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0359
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0421
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0310
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0334
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0395
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0030
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0055
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.CountT
import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WeightConstT
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0473
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0416
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0419
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0468
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0287
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0479
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0362
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0399

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeBoundAtTermsOfLocalData
section
noncomputable section
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints GlobalTheory.TypeAsm

namespace GlobalTheory.TypeAsm.AmpTerms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem prod_sqrt {ι : Type} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∏ i, Real.sqrt (f i) = Real.sqrt (∏ i, f i) := by
  have h0 : 0 ≤ ∏ i, Real.sqrt (f i) := Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _
  have h2 : (∏ i, Real.sqrt (f i)) ^ 2 = ∏ i, f i := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => Real.sq_sqrt (hf i)
  rw [← h2, Real.sqrt_sq h0]

theorem prod_bound {ι : Type} [Fintype ι] (x d g : ι → ℝ) (A PB : ℝ) (hA : 0 ≤ A)
    (hx : ∀ i, 0 ≤ x i) (h : ∀ i, x i ≤ Real.sqrt (d i) * (A / 1 * g i)) (hg : ∏ i, g i ≤ PB) :
    ∏ i, x i ≤ (∏ i, Real.sqrt (d i)) * (A ^ Fintype.card ι * PB) := by
  calc ∏ i, x i ≤ ∏ i, (Real.sqrt (d i) * (A / 1 * g i)) :=
        Finset.prod_le_prod (fun i _ => hx i) (fun i _ => h i)
    _ = (∏ i, Real.sqrt (d i)) * (A ^ Fintype.card ι * ∏ i, g i) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, div_one]
    _ ≤ (∏ i, Real.sqrt (d i)) * (A ^ Fintype.card ι * PB) := by
        apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left hg (pow_nonneg hA _)

theorem chain {a V L w vol Pr om vk sd A0f PB G : ℝ} (ha : 0 ≤ a) (hV : 1 ≤ V * L) (hL : 0 ≤ L) (hw : 0 ≤ w)
    (hPr0 : 0 ≤ Pr) (hom : 0 ≤ om) (hvk : 0 ≤ vk)
    (hfact : a * V ≤ w * (vol * Pr)) (hvol : vol ≤ om * (vk * L)) (hPr : Pr ≤ sd * (A0f * PB))
    (hG : vk * L * L * A0f * PB ≤ G) (hsd : 0 ≤ sd) : a ≤ w * sd * G * om := by
  have s1 : a ≤ a * V * L := by nlinarith
  have s2 : a * V * L ≤ w * (vol * Pr) * L := mul_le_mul_of_nonneg_right hfact hL
  have s3 : vol * Pr ≤ om * (vk * L) * Pr := mul_le_mul_of_nonneg_right hvol hPr0
  have s4 : om * (vk * L) * Pr ≤ om * (vk * L) * (sd * (A0f * PB)) :=
    mul_le_mul_of_nonneg_left hPr (by positivity)
  have s5 : w * (vol * Pr) * L ≤ w * (om * (vk * L) * (sd * (A0f * PB))) * L := by
    apply mul_le_mul_of_nonneg_right _ hL
    exact mul_le_mul_of_nonneg_left (s3.trans s4) hw
  have s6 : w * (om * (vk * L) * (sd * (A0f * PB))) * L = w * sd * om * (vk * L * L * A0f * PB) := by ring
  have s7 : w * sd * om * (vk * L * L * A0f * PB) ≤ w * sd * om * G :=
    mul_le_mul_of_nonneg_left hG (by positivity)
  nlinarith

theorem sizes {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cw cT CT C0 : ℝ}
    (hH : Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0) (hC' : 40 ≤ C') (hCl : 1 ≤ Cl) :
    D.R.m = 2 * D.R.rS + 2 ∧ 1 ≤ D.host.v ∧ 2 * D.host.v ≤ large₂.sc.b ∧ 1 ≤ D.R.f ∧
      40 * D.R.rS ^ 4 ≤ D.R.k ∧ 5 * D.R.rS ≤ D.R.k ∧ (∀ w, 0 < Tr D w) := by
  obtain ⟨⟨-, hCk, hmf, -, -, -, -, -, -, -, hrd, -, -, -, -, -, -, -, hv, -, -, -, hT, -, hCl0⟩, -, -⟩ := hH.1
  have hm : D.R.m = 2 * D.R.rS + 2 := D.R.rS_two.symm
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hrdv : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
  have hb : large₂.sc.b = Real.exp large₂.sc.L := rfl
  have hf : 1 ≤ D.R.f := by
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have h2v : 2 * D.host.v ≤ large₂.sc.b := by
    rw [← hrdv, hb]
    have hpos : 0 < D.host.rdE := by rw [hrdv]; linarith
    have hrd' : Real.log D.host.rdE ≤ large₂.sc.L :=
      hrd.trans (div_le_self (by linarith) hCl)
    exact (Real.log_le_iff_le_exp hpos).1 hrd'
  have hk40 : 40 * D.R.rS ^ 4 ≤ D.R.k := by
    have hmr : (D.R.rS : ℝ) ≤ D.R.m := by rw [hm]; push_cast; linarith
    have hm1 : (1 : ℝ) ≤ D.R.m := by rw [hm]; push_cast; linarith
    have hr0 : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
    have h4 : (D.R.rS : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 5 := by
      calc (D.R.rS : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 4 := pow_le_pow_left₀ hr0 hmr 4
        _ ≤ (D.R.m : ℝ) ^ 5 := pow_le_pow_right₀ hm1 (by norm_num)
    have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
    have hm5 : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := by positivity
    have hx : (D.R.m : ℝ) ^ 5 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
      have h1 : (D.R.m : ℝ) ^ 5 ≤ (D.R.m : ℝ) ^ 5 * D.R.f := le_mul_of_one_le_right hm5 hf1
      exact h1.trans (le_mul_of_one_le_right (by positivity) hL.le)
    have hreal : ((40 * D.R.rS ^ 4 : ℕ) : ℝ) ≤ D.R.k := by
      push_cast
      calc 40 * (D.R.rS : ℝ) ^ 4 ≤ 40 * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by linarith
        _ ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by
          apply mul_le_mul_of_nonneg_right hC'; positivity
        _ = C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by ring
        _ ≤ D.R.k := hCk
    exact_mod_cast hreal
  refine ⟨hm, hv, h2v, hf, hk40, ?_, fun w => ?_⟩
  · have : D.R.rS ≤ D.R.rS ^ 4 := by
      rcases Nat.eq_zero_or_pos D.R.rS with h | h
      · rw [h]; norm_num
      · exact Nat.le_self_pow (by norm_num) _
    omega
  · have hb0 : 0 < large₂.sc.b := Real.exp_pos _
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) (hT w).1

theorem amplitudeBound_of_localData_of_tailBound : GlobalTheory.TypeAsm.LocDatC → GlobalTheory.TypeAsm.TailP → GlobalTheory.TypeAsm.AmpP := by
  intro hLoc hTailP Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨CH, hCH, hT⟩ := hTailP Cg cb Cw cT CT C0 hcb hcT
  refine ⟨CH, hCH, fun Cs hCs => ?_⟩
  obtain ⟨C₁, hC₁, hProd⟩ := GlobalTheory.T.localBound_productOverPlaces_label Cs hCs
  obtain ⟨Ca, hCa⟩ := GlobalTheory.amplitude_arithmetic CH hCH
  refine ⟨max Ca 0, le_max_right _ _, fun C hC => ?_⟩
  have hC0 : 0 ≤ C := (le_max_right _ _).trans hC
  have hCaC : Ca ≤ C := (le_max_left _ _).trans hC
  obtain ⟨C'₁, Cl₁, hT1⟩ := hT C₁
  obtain ⟨Clg, hGap⟩ := GlobalTheory.T.gapC_holds
  refine ⟨max C'₁ 40, max (max Cl₁ Clg) 1, fun C' Cl hC' hCl => ?_⟩
  intro D large₂ X Y u hTies hH hConc
  have hCl1 : 1 ≤ Cl := (le_max_right _ _).trans hCl
  obtain ⟨hm, hv, h2v, hf, hk40, hk5, hTr⟩ :=
    GlobalTheory.TypeAsm.AmpTerms.sizes hH ((le_max_right _ _).trans hC') hCl1
  have hStd : Std D large₂ := ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hH⟩
  have hCM : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := hH.2.2.2.2.2.2.2
  have hgap := hGap C' Cl Cg cb Cw cT CT C0 D large₂ ((le_max_right _ _).trans ((le_max_left _ _).trans hCl)) hH
  obtain ⟨Ch, hBs, hGood⟩ := hLoc D X ⟨u⟩ hgap hTies.dsig_tie
  have hTail := hT1 C' Cl ((le_max_left _ _).trans hC') ((le_max_left _ _).trans ((le_max_left _ _).trans hCl))
    D large₂ hTies hH hConc.2.2.2.2.2.2.2
  obtain ⟨hcovTop, hcov1⟩ := GlobalTheory.T.integralUnipotent_covolume_finite_bounded D large₂ X Y u Ch hStd
  have hb2 : 2 ≤ large₂.sc.b := by linarith
  intro t ht
  have hj1 : 1 ≤ jT t := Formalism.L2.SG.KappaOffDiagonal.JPosC_holds Cg cb Cw cT CT C0 C' Cl D large₂ X Y u hH hConc t ht
  have hjr : jT t ≤ D.R.rS := Nat.sub_le _ _
  obtain ⟨De, P, hP, hDel, hDeOK, hprod⟩ := hProd D large₂ X Y u Ch CH hStd hCH hk40 hk5 t ht hjr hj1
  set c : ℝ := Formalism.L2.SG.TermOp.wt t * Real.sqrt (dpiC X u) * k2a large₂ CH Cs C (jT t) (labT t) with hc
  have hc0 : 0 ≤ c := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (amplitude_label_nonneg large₂ hC0 _ _)
  have hinf := (GlobalTheory.DegAsm.WeightInf.main _ _ (HV D) hCM D.R.rS).2 (F0 X u) (Ft t) (dI D) t.lam
  have hex : ∃ N, GlobalTheory.DegAsm.Adapt (F0 X u) (Ft t) (dI D) N := by
    obtain ⟨N, hN, -⟩ := GlobalTheory.T.exists_adaptedNormalForm_relevantTerm D large₂ X Y u hStd t ht
    exact ⟨N, hN⟩
  have key : ∀ N : GlobalTheory.DegCnt.NF (HV D) D.R.rS, GlobalTheory.DegAsm.Adapt (F0 X u) (Ft t) (dI D) N →
      ‖(Y.tO u u).vec t‖ ≤ c * N.om t.lam := by
    intro N hN
    have hNj : N.j = jT t := (GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label D large₂ X Y u hStd t N hN).1
    obtain ⟨β, n₁, g, n₂, hfr⟩ := GlobalTheory.T.adaptedNormalForm_gives_real_normal_form D large₂ X Y u Ch hStd t N hN
    obtain ⟨K, hK⟩ := GlobalTheory.T.strict_fundamentalSet_integralStabilizer_exists D X Y u t
    set μ : D.what₂.Tau → Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) := fun τ =>
      (ENNReal.ofReal 1 • GlobalTheory.Amp.lebR0 D.R.k D.R.rS N.j β).map (Formalism.QuantumDeterminants.conjM (n₂ τ)⁻¹) with hμ
    have hμN : ∀ τ, GlobalTheory.Amp.IsNormalFormStabilizerMeasure D.R.k D.R.rS N.j_le (zB X (Ch.Qi τ) u τ) (zB X (Ch.Qi τ) u τ)
        (gamT Ch t τ)⁻¹ 1 (μ τ) := by
      intro τ
      obtain ⟨h1, h2, h3, hfo⟩ := hfr τ
      obtain ⟨-, hz, hz', hTz, ⟨cc, hnorm⟩, -⟩ := hfo
      exact ⟨hz, hz', hTz, n₁ τ, h1, n₂ τ, h2, g τ, β, cc, hnorm, h3, rfl⟩
    have hvol := GlobalTheory.T.integralStabiliser_covolume_le_indexWeight D large₂ X Y u Ch hStd t N hN μ K hμN hK
    have htr : ∀ (a b : ℕ) (e : a = b) (ha : a ≤ D.R.rS) (hb : b ≤ D.R.rS) (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
        (γ : GlobalTheory.SgInf.Mat D.R.k D.R.rS) (s : ℝ) (μ' : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)),
        GlobalTheory.Amp.IsNormalFormStabilizerMeasure D.R.k D.R.rS ha z z' γ s μ' → GlobalTheory.Amp.IsNormalFormStabilizerMeasure D.R.k D.R.rS hb z z' γ s μ' := by
      rintro a b rfl _ _ _ _ _ _ _ h; exact h
    have hμJ : ∀ τ, GlobalTheory.Amp.IsNormalFormStabilizerMeasure D.R.k D.R.rS hjr (zB X (Ch.Qi τ) u τ) (zB X (Ch.Qi τ) u τ)
        (gamT Ch t τ)⁻¹ 1 (μ τ) := fun τ => htr _ _ hNj _ _ _ _ _ _ _ (hμN τ)
    have hq : ∀ τ, _ := fun τ => GlobalTheory.DegVol.StabQuot.exists_sigmaFinite_quot D.R.k D.R.rS (jT t) hjr
      (zB X (Ch.Qi τ) u τ) (zB X (Ch.Qi τ) u τ) (gamT Ch t τ) (muGB X (Ch.Q τ) (Ch.Qi τ) τ) (μ τ)
      ((hGood.2 u τ).1.2.2.2.2.2.2.1) (hμJ τ) (((GlobalTheory.T.realPointGramMinorsAgree_proof D X Y u Ch τ).2 t).1)
    choose hσμ hHaarμ hNR ν hσν hνnull hνq using hq
    have hfact := GlobalTheory.T.termAmplitude_le_covolume_localAmplitudes D X Y u Ch hBs hGood hcovTop t ht.2 μ ν K
      (fun τ => ⟨hσμ τ, hHaarμ τ, hσν τ, hνnull τ, hνq τ⟩) hK
    have hr1 : 1 ≤ D.R.rS := hj1.trans hjr
    have hjk : jT t + 2 ≤ D.R.k := by
      have : D.R.rS ≤ D.R.rS ^ 4 := Nat.le_self_pow (by norm_num) _
      omega
    have hqq : 16 * D.R.rS ^ 3 + 4 * D.R.rS + 2 ≤ C₁ * D.R.k * D.R.rS := by
      have a1 : D.R.rS ^ 3 ≤ D.R.rS ^ 5 := Nat.pow_le_pow_right hr1 (by norm_num)
      have a2 : D.R.rS ≤ D.R.rS ^ 5 := Nat.le_self_pow (by norm_num) _
      have a3 : 1 ≤ D.R.rS ^ 5 := Nat.one_le_pow _ _ hr1
      have a4 : 40 * D.R.rS ^ 4 * D.R.rS ≤ D.R.k * D.R.rS := Nat.mul_le_mul_right _ hk40
      have a5 : D.R.k * D.R.rS ≤ C₁ * (D.R.k * D.R.rS) := Nat.le_mul_of_pos_left _ hC₁
      have a6 : 40 * D.R.rS ^ 4 * D.R.rS = 40 * D.R.rS ^ 5 := by ring
      rw [mul_assoc]
      omega
    have hH1 : 1 ≤ H1C large₂ CH := by
      unfold H1C
      exact Real.one_le_rpow (by linarith) (by positivity)
    have hloc := fun τ => GlobalTheory.T.amplitude_hsNorm_le_degreeBound_realPlace D τ u u 1 (locW Ch u u τ) _ (locS hBs u u τ) (by linarith) one_pos (hTr u)
      (hTr u) (hGood.2 u τ).1 (hGood.2 u τ).2 (jT t) hjr (C₁ * D.R.k * D.R.rS) (gamT Ch t τ) 1 (H1C large₂ CH) (De τ) _
      (ν τ) hj1 hjk hqq one_pos hH1 (hTail τ u _ (hGood.2 u τ).1 _ (hGood.2 u τ).2).1
      (hTail τ u _ (hGood.2 u τ).1 _ (hGood.2 u τ).2).2 (hDeOK τ) (hNR τ) (hνq τ)
    have hom0 : 0 ≤ N.om t.lam := hinf.1.trans (hinf.2.1 N hN)
    have hL0 : 0 ≤ lossV D := by unfold lossV; have := hv; positivity
    have hvol' : (Measure.pi μ (trI Ch '' K)).toReal ≤
        N.om t.lam * (D.host.v ^ (D.R.k * (D.R.rS - jT t) * D.R.f) * lossV D) := by
      rw [← hNj]
      exact ENNReal.toReal_le_of_le_ofReal (by have := hv; positivity) hvol
    have hcard : Fintype.card D.what₂.Tau = D.R.f := D.what₂.card_Tau
    have hsd : ∏ τ, Real.sqrt (Module.finrank ℂ (Formalism.L2.SG.LocWSOf.locW Ch u u τ).Wp : ℝ) =
        Real.sqrt (dpiC X u) := by
      rw [prod_sqrt _ (fun τ => Nat.cast_nonneg _)]
      unfold dpiC
      rw [Formalism.L2.SG.Pf.AmpWin.finrank_tau]
      rfl
    have hA0 : (0 : ℝ) ≤ (2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1 *
        2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1)) := by have := hv; positivity
    have hPr := prod_bound _ _ _ _ _ hA0 (fun τ => Real.sqrt_nonneg _) hloc hprod
    rw [hsd, hcard] at hPr
    have hG := hCa C hCaC D.R.k D.R.rS D.R.m D.R.f (jT t) large₂.sc.b D.host.v (k2Del D (jT t) (labT t))
      (k2S D (H1C large₂ CH) (jT t) (labT t)) Cs P hm hj1 hjr (by omega) hf hb2 hv h2v hP hDel (one_le_sigma_product _ _ _)
    have hfinal := chain (norm_nonneg _) hcov1 hL0 (Real.sqrt_nonneg _)
      (Finset.prod_nonneg fun τ _ => Real.sqrt_nonneg _) hom0 (by have := hv; positivity) hfact hvol' hPr hG
      (Real.sqrt_nonneg _)
    refine hfinal.trans (le_of_eq ?_)
    rw [hc]
    unfold k2a H1C
    rfl
  have hfin := hinf.2.2 _ c hc0 hex key
  show ‖(Y.tO u u).vec t‖ ≤ Formalism.L2.SG.TermOp.wt t * Real.sqrt (dpiC X u) * (omT t * k2a large₂ CH Cs C (jT t) (labT t))
  have e : Formalism.L2.SG.TermOp.wt t * Real.sqrt (dpiC X u) * (omT t * k2a large₂ CH Cs C (jT t) (labT t)) =
      c * GlobalTheory.DegAsm.omI (F0 X u) (Ft t) (dI D) t.lam := by
    rw [hc]; unfold omT; ring
  rw [e]; exact hfin

end GlobalTheory.TypeAsm.AmpTerms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountParameterConditionsOfSizeHypothesesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.countParameterConditions_of_sizeHypotheses : ∀ (D : D7) (L : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) (n0 : ℕ) (A C cb7 : ℝ), 0 ≤ C → 0 < cb7 → 2 * Cg ≤ A → (n0 : ℝ) ≤ D.R.k → 2 ≤ Cl → 2 * C ≤ Cl → Real.log L.sc.L ≤ cb7 * D.R.k → ArithmeticConditionsOfDatum D → StandingHypotheses D L C' Cl Cg cb Cu cT CT → AdmissibleBoundsFromSource.CountTheoremHypotheses D L n0 A C cb7 ∧ 4 * D.R.r < D.host.g 1 := by
  first | exact @GlobalTheory.countClauses_of_sizeHyp | exact GlobalTheory.countClauses_of_sizeHyp | (intros; apply GlobalTheory.countClauses_of_sizeHyp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGroupSumFactorsRowWeightAmplitudeProof
section
noncomputable section

open scoped Classical Pointwise
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.FamDefs Formalism.MainNotions.S.LocNG GlobalTheory.HL GlobalTheory.LocOver GlobalTheory.SnFam

namespace GlobalTheory.FamilyNormRational

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem toPts_inj' {K : Type} [Zero K] {i : ℕ} (p q : Point K (i + 1)) (h : toPts p = toPts q) : p = q := by
  have hb : p.1.map Prod.snd = q.1.map Prod.snd := congrArg (fun x => x.1.blocks) h
  have hl : p.1.length = q.1.length := by simpa using congrArg List.length hb
  have hv : ∀ k (hk : k < p.1.length) (hk' : k < q.1.length), (p.1[k]).1 = (q.1[k]).1 := by
    intro k hk hk'
    have key := congrArg (fun x : (Σ c : Composition (i + 1), (Fin c.length → K)) =>
      if hk : k < x.1.length then x.2 ⟨k, hk⟩ else 0) h
    have e1 : k < (toPts p).1.length := by simpa [toPts, Composition.length] using hk
    have e2 : k < (toPts q).1.length := by simpa [toPts, Composition.length] using hk'
    simp only [dif_pos e1, dif_pos e2] at key
    simpa [toPts] using key
  apply Subtype.ext
  apply List.ext_getElem hl
  intro k hk hk'
  have hs := congrArg (fun l => l[k]?) hb
  simp only [List.getElem?_map, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk', Option.map_some,
    Option.some.injEq] at hs
  exact Prod.ext (hv k hk hk') hs

theorem one_mem_nRat {D : D7} {T : D.host.E} (F : LFlag (VS D) D.R.rS T) : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NRat F :=
  ⟨one_mem _, fun j x _ => by simp, fun x _ => by simp⟩

theorem squaredGroupSum_classDoubleCoset_eq_rowWeight : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k →
    ConcTie X Y → ∀ ν, Formalism.L2.SG.RealObj.NuQPin X u u' ν → ∀ s : X.B.I.Ginf → NNReal, (∀ γ, 0 < s γ) →
    (∀ w : Point D.host.E (D.R.rS + 1), (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) →
      (s (Formalism.L2.SG.RealObj.gamW X u u' w) : ℝ) = (((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹)) →
    ∀ (K : Type) (S : Prop → Prop) (TS : Set (TauC Y u u')) (cls : TauC Y u u' → K), FamQ Y u u' S TS cls →
    ∀ γ : PN.Pts D.host.E D.R.rS, HasPt Y u u' TS γ →
    ∀ Fm : LocFam (zOf Y) K (NuC D), FamTie TS cls (nmlOf Y u u') γ Fm →
    ∀ (c : K) (n : NuC D), a2F Y u u' TS cls (sc s ν) c γ n = a2W Fm.toL (ampQ S Fm.toL) c n := by
  intro D X Y u u' hSt hk hCT ν hνP s hs0 hsw K S TS cls hFQ γ hγ Fm hFT c n
  obtain ⟨w, F00, F'0, F'1, hw, -, -, -, hZ, hbase, hOm, hgood, -, -, -, -, hdat, -, -⟩ := hFT
  have hdc := hdat c n
  have hL : Fm.toL.dat c n = Fm.dat c n := rfl
  show ‖grpF Y u u' TS cls c γ n‖ ^ 2 / J2of Y u u' (sc s ν) γ = a2W Fm.toL (ampQ S Fm.toL) c n
  unfold a2W
  rw [hL]
  rcases hd : Fm.dat c n with _ | d
  · rw [hd] at hdc
    have h0 : grpF Y u u' TS cls c γ n = 0 := by
      unfold grpF
      have h0 : ∀ t, (TS ∩ {t | cls t = c ∧ ptPN t = γ ∧ nmlOf Y u u' t = n}).indicator (Y.tO u u').vec t = 0 := by
        intro t; apply Set.indicator_of_notMem; rintro ⟨h1, h2, h3, h4⟩; exact hdc ⟨t, h1, h2, h3, h4⟩
      simp [h0]
    simp [h0]
  · rw [hd] at hdc
    obtain ⟨⟨t0, ht0, hc0, hp0, hn0⟩, hall⟩ := hdc
    obtain ⟨hOv, hrw⟩ := hall t0 ht0 hc0 hp0 hn0
    obtain ⟨hTS, hCR, hRow⟩ := hFQ
    obtain ⟨t1, ht1, hv1, hp1⟩ := hγ
    have hGTS : ∀ t ∈ TS, t.G ≠ 0 := by
      intro t ht h0
      rw [hTS] at ht
      apply ht.1
      show Formalism.L2.SG.TermOp.Gt t = 0
      unfold Formalism.L2.SG.TermOp.Gt
      rw [if_pos h0]
    have hG1 := hGTS t1 ht1
    have hG0 := hGTS t0 ht0
    have hrel1 : t1.relevant := (GlobalTheory.T.nonGeneric_family_classes_determine_rows D X Y u u' hCT).2.2 t1 hv1
    obtain ⟨w1, hw1, hat1, -⟩ := GlobalTheory.T.terms_at_point_of_relevant_term_relevant_finite D X Y u u' t1 hG1 hrel1
    have hw1w : w1 = w := toPts_inj' _ _ (hw1.trans (hp1.trans hw.symm))
    subst hw1w
    have hatOf : ∀ t : TauC Y u u', ptPN t = γ → t.relevant ∧ t.toTerm.atPt w1 ∧ Formalism.L2.SG.PairVal.ptOf t.toTerm = w1 := by
      intro t ht
      obtain ⟨hr, hg, hcell⟩ := hat1 t (ht.trans hp1.symm)
      refine ⟨hr, ⟨(Quot.out t.toTerm.cls).1, ⟨(Quot.out t.toTerm.cls).2, Quot.out_eq _⟩, hg, hcell⟩, ?_⟩
      exact toPts_inj' _ _ (ht.trans hw.symm)
    obtain ⟨hrel0, hat0, hpt0⟩ := hatOf t0 hp0
    obtain ⟨-, hat1', hpt1⟩ := hatOf t1 hp1
    have hAtB : ∀ p, AtBase (zOf Y) p F00 F'0 (Tu D u) (Tu D u') (Fm.FP p) := fun p =>
      ⟨(hbase p).1, (hbase p).2.1, (hbase p).2.2.1, (hbase p).2.2.2⟩
    have hGv : Gval F00 F'0 ≠ 0 := by
      obtain ⟨-, hg0, hcell0⟩ := hat1 t0 (hp0.trans hp1.symm)
      have hcell00 : IsInCell (ZhatOM (ZhatL F00 F'0)) w1 :=
        ⟨1, 1, fun i j => ⟨fun h => Matrix.one_apply_ne (ne_of_lt h), fun h => h ▸ Matrix.one_apply_eq i⟩,
          fun i j => ⟨fun h => Matrix.one_apply_ne (ne_of_gt h), fun h => h ▸ Matrix.one_apply_eq i⟩,
          by rw [hZ, Matrix.one_mul, Matrix.mul_one]⟩
      have e1 := Formalism.L2.SG.WConst.gPoint_eq_gval F00 F'0 w1 hcell00
      have e2 := Formalism.L2.SG.WConst.gPoint_eq_gval (T := Tu D u) (T' := Tu D u') (lf D (X.Fu u)) (Quot.out t0.toTerm.cls).1
        w1 hcell0
      rw [← e1, e2]
      exact hg0
    have hBase : ∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (Fm.FP p) ∧
        (Fm.FP p).RelG (LocNG.theta (Y.M p)) := fun p =>
      ⟨hAtB p, (GlobalTheory.T.localisedBaseFrames_relevantPair D (zOf Y) u u' w1 F00 F'0 hZ hGv p).2 _ (hAtB p)⟩
    obtain ⟨G, ⟨cc⟩⟩ := GlobalTheory.T.exists_global_coordinates_rational_flagPair D X Y u u' hSt w1 F00 F'0 Fm.FP hZ hGv hBase
    obtain ⟨ρ, U, U', hmv⟩ := GlobalTheory.T.term_moves_to_baseFrames_up_to_unitriangular D X Y u u' hSt w1 F00 F'0 Fm.FP hZ hGv hBase t0 hat0
    have hcore := GlobalTheory.T.row_doubleCoset_sum_norm_sq_bound D X Y u u' hSt hk w1 F00 F'0 Fm.FP hZ hGv hBase G cc ν hνP t0 ρ U U' hmv hrel0 hpt0 S
    have hamp := GlobalTheory.T.globalAmplitude_eq_localAmplitudes D X Y u u' hSt hk w1 F00 F'0 Fm.FP hZ hGv hBase G cc t0 ρ U U' hmv Fm.R Fm.P Fm.Om
      (fun p => (d p).1) hgood hOm (fun p => hOv p.1 p.2) S
    have hset : (TS ∩ {t | cls t = c ∧ ptPN t = γ ∧ nmlOf Y u u' t = n}) =
        {t : TauC Y u u' | (Y.tO u u').rowOf t = (Y.tO u u').rowOf t0 ∧ nmlOf Y u u' t = nmlOf Y u u' t0 ∧
          S (¬ t.generic)} := by
      ext t
      constructor
      · rintro ⟨htS, hct, -, hnt⟩
        refine ⟨hRow t htS t0 ht0 (hct.trans hc0.symm), hnt.trans hn0.symm, ?_⟩
        have h2 := htS
        rw [hTS] at h2
        exact h2.2
      · rintro ⟨hr, hnm, hS⟩
        obtain ⟨nn, mm, hnn, hmm, hlin⟩ := (GlobalTheory.T.doubleCoset_eq_iff_isometry_unipotent_translate D X Y u u' hSt t0 t).1 hnm
        obtain ⟨-, hGeq, hpteq, -, -⟩ := GlobalTheory.T.flagTerm_invariants_const_on_rationalDoubleCoset D X Y u u' hSt t0 t nn mm hrel0 hG0 ⟨hnn, hmm, hlin⟩
        have htS : t ∈ TS := by
          rw [hTS]
          refine ⟨?_, hS⟩
          show Formalism.L2.SG.TermOp.Gt t ≠ 0
          unfold Formalism.L2.SG.TermOp.Gt
          rw [if_neg (hGeq ▸ hG0)]
          exact one_ne_zero
        refine ⟨htS, ((hCR t htS t0 ht0 hnm).2 hr).trans hc0, ?_, hnm.trans hn0⟩
        show toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm) = γ
        rw [hpteq]
        exact hp0
    have hrep : ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w1 g :=
      (GlobalTheory.T.orbital_integrals_terms_one_doubleCoset D X Y u u' hSt ν hνP t0 hrel0 hG0 w1 hpt0.symm).1
    have hJ : J2of Y u u' (sc s ν) γ = (s (Formalism.L2.SG.RealObj.gamW X u u' w1) : ℝ) ^ 2 *
        ‖Formalism.L2.SG.PackageTie.hsEmb (Jw Y u u' ν w1)‖ ^ 2 := by
      unfold J2of
      have hex : ∃ w' : Point D.host.E (D.R.rS + 1), toPts w' = γ ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w' g :=
        ⟨w1, hw, hrep⟩
      rw [dif_pos hex]
      have hcw : hex.choose = w1 := toPts_inj' _ _ (hex.choose_spec.1.trans hw.symm)
      rw [hcw, Jw_sc, map_smul, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hJne : ‖Formalism.L2.SG.PackageTie.hsEmb (Jw Y u u' ν w1)‖ ≠ 0 := by
      intro h0
      obtain ⟨ρ1, U1, U1', hmv1⟩ := GlobalTheory.T.term_moves_to_baseFrames_up_to_unitriangular D X Y u u' hSt w1 F00 F'0 Fm.FP hZ hGv hBase t1 hat1'
      obtain ⟨T, hT, hamp1⟩ := GlobalTheory.T.rowTerm_amplitude_eq_mass_mul_phase D X Y u u' hSt hk w1 F00 F'0 Fm.FP hZ hGv hBase G cc ν hνP t1 ρ1 U1 U1'
        hmv1 hrel1 hpt1
      have he := hamp1 t1 1 1 rfl ⟨one_mem_nRat _, one_mem_nRat _, by simp⟩
      have hT0 : Formalism.L2.SG.PackageTie.hsEmb T = 0 := norm_eq_zero.1 (hT.trans h0)
      apply hv1
      show Formalism.L2.SG.TermOp.vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t1 = 0
      unfold Formalism.L2.SG.TermOp.vec
      rw [he, map_smul, hT0, smul_zero, smul_zero]
      ext q
      simp
    have hgi := hsw w1 hrep
    have hspos : (0 : ℝ) < s (Formalism.L2.SG.RealObj.gamW X u u' w1) := by exact_mod_cast hs0 _
    have hampeq : ‖G.amp (G.datOf (cc.lat ρ t0.lam)) (fun Γ => S (¬ G.Gen (G.datOf (cc.lat ρ t0.lam)) Γ))‖ =
        ‖ampQ S Fm.toL d‖ := by
      rw [hamp]; unfold ampQ
      congr 1
      refine Finset.sum_congr rfl (fun A _ => Finset.prod_congr rfl (fun p _ => ?_))
      split_ifs <;> first | rfl | (exfalso; tauto)
    have hgrp : grpF Y u u' TS cls c γ n = ∑' t : TauC Y u u', {t : TauC Y u u' | (Y.tO u u').rowOf t =
        (Y.tO u u').rowOf t0 ∧ nmlOf Y u u' t = nmlOf Y u u' t0 ∧ S (¬ t.generic)}.indicator (Y.tO u u').vec t := by
      unfold grpF; rw [hset]
    rw [hgrp, hcore, hJ, hampeq]
    show _ = Fm.rw c * ‖ampQ S Fm.toL d‖ ^ 2
    rw [hrw, ← hgi]
    have hJp : 0 < ‖Formalism.L2.SG.PackageTie.hsEmb (Jw Y u u' ν w1)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hJne)
    field_simp

theorem familyGroupSumFactorsRowWeightAmplitude : GlobalTheory.SnFam.FamilyGroupSumFactorsWeightAmplitude := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, le_rfl, 0, 0, fun C' Cl _ _ D large₂ X Y u u' hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν => ?_⟩
  have hk := four_rank_add_seven_le_k hc
  obtain ⟨-, hSt, hCT⟩ := hc
  obtain ⟨s, hs1, hs0, hsle, hsw⟩ := GlobalTheory.T.exists_scale_normalised_localReading D X u u'
  refine ⟨s, hs1, hs0, fun γ => ?_, fun K S TS cls hFQ γ hγ Fm hFT c n =>
    squaredGroupSum_classDoubleCoset_eq_rowWeight D X Y u u' hSt hk hCT ν hν.2 s hs0 hsw K S TS cls hFQ γ hγ Fm hFT c n⟩
  have h1 : (s γ : ℝ) ≤ 1 := by exact_mod_cast hsle γ
  have h0 : (0 : ℝ) ≤ s γ := (s γ).2
  simp only [zero_mul, Real.rpow_zero]
  nlinarith

end GlobalTheory.FamilyNormRational
end
end

