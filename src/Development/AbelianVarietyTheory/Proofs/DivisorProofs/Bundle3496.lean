import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedThetaIntegralValue
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularisingTranslateCombination
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0662
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3474
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3436
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3427
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3423
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3428
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2599
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2709
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3479
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3462

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarSmul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ThetaRegularizationComparison

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem standing {large₂ : SizeData₂ D} (hR : GlobalTheory.SqTop.Rec large₂) (hx : 11 ≤ D.host.splitBound) {μ₀ : T} (hL : L.Is μ₀)
    (G : GridData L sc) (t : T) : SquareStanding G t := by
  classical
  have hcc : D.host.ccK = ⊤ := hR.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨P, -, -⟩, -⟩ := hR.size
  have lev : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := fun p hp hpp => by
    have h := P.level_split p hp
    exact (Nat.Prime.coprime_iff_not_dvd hpp).2 (not_dvd_of_splitK hpp h)
  refine ⟨hx, fun w hw => ?_⟩
  have e1 : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) = ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) := by
    rw [hcc, Ideal.absNorm_top, mul_one]
  rw [e1]
  rcases Finset.mem_union.1 hw with hw | hw
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨p, hpv, hcop⟩ : ∃ p : ℕ, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∧ Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := by
      rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | hv1
      · refine ⟨q0 D, G.pl.basePlace_over_qZero, ?_⟩
        have hs := (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1
        have hM : Nat.Coprime (Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D) (q0 D) := by
          rw [Nat.Coprime, Nat.gcd_rec, hs, Nat.gcd_one_left]
        have hdv : D.host.QS * D.host.q * D.host.d ∣ Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D := by
          unfold LevelStarExponents.condE
          exact Dvd.dvd.mul_left dvd_rfl _
        exact (hM.coprime_dvd_left hdv).symm
      · rcases (S1_mem_OmF D).1 hv1 with h | h | h | h
        · exact ⟨_, h, lev _ (D.host.g_level 0) (D.host.g_prime 0)⟩
        · exact ⟨_, h, lev _ (D.host.g_level 1) (D.host.g_prime 1)⟩
        · exact ⟨_, h, lev _ D.host.pde_level.1 D.host.pde_prime⟩
        · exact ⟨_, h, lev _ D.host.pde_level.2 D.host.pde'_prime⟩
    have hpw : ((p : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal := by
      rw [← G.pl.under_w hv, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at hpv
      exact hpv
    exact GlobalTheory.SquareConv.natCast_not_mem (G.pl.w v).isPrime.ne_top hcop hpw
  · intro hmem
    apply (hL.Q_off t w hw).1
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem

theorem exists_haar_smul (V : HSp D) (ν ν' : Measure (GA D V)) (h : ν.IsHaarMeasure) (h' : ν'.IsHaarMeasure) :
    ∃ s : NNReal, s ≠ 0 ∧ ν' = s • ν := by
  obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  exact ⟨Measure.haarScalarFactor ν' ν, (Measure.haarScalarFactor_pos_of_isHaarMeasure ν' ν).ne',
    Measure.isMulLeftInvariant_eq_smul ν' ν⟩

theorem integral_change (V : HSp D) {ν ν' : Measure (GA D V)} {𝓕 𝓕' : Set (GA D V)} (h : GlobalTheory.SquareComm.IsHaarFD V ν 𝓕)
    (h' : GlobalTheory.SquareComm.IsHaarFD V ν' 𝓕') {s : NNReal} (hs : ν' = s • ν) (f : GA D V → ℂ)
    (hf : ∀ γ ∈ GQ V, ∀ u, f (γ * u) = f u) :
    (IntegrableOn f 𝓕 ν → IntegrableOn f 𝓕' ν') ∧ ∫ u in 𝓕', f u ∂ν' = ((s : ℝ) : ℂ) * ∫ u in 𝓕, f u ∂ν := by
  obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have := h'.1
  have h2 : IsFundamentalDomain (GQ V) 𝓕 ν' := h.2.mono (by rw [hs]; exact Measure.smul_absolutelyContinuous)
  have hinv : ∀ (γ : GQ V) (g : GA D V), f (γ • g) = f g := fun γ g => hf γ γ.2 g
  refine ⟨fun hi => (h2.integrableOn_iff h'.2 hinv).1 ?_, ?_⟩
  · rw [hs, IntegrableOn, Measure.restrict_smul]
    exact Integrable.smul_measure_nnreal hi
  · rw [h'.2.setIntegral_eq h2 hinv, hs, Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def,
      Complex.real_smul]

open GlobalTheory.FinPl GlobalTheory.SmallKerInv in

theorem kerSmall_inv {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ Θ')
    (hΘ : IsMatched B t ρ i j Θ Θ') (g g₁) :
    ∃ (Λ : GlobalTheory.FinPl.Lat (G.V (.grid i j))) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    Λ.FG ∧ Submodule.span D.host.E (Λ : Set (Fin (G.V (.grid i j)).rank → D.host.E)) = ⊤ ∧
    ∀ κ, GlobalTheory.FinPl.InK (G.V (.grid i j)) Λ (fun v => v ∉ S) κ → ∀ u, kerSmall W Θ' g g₁ (u * κ) = kerSmall W Θ' g g₁ u := by
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, he, ⟨φ₁, φ₂, h1, -⟩, -⟩, -, rfl⟩ := hΘ
  have hm := W.om_is (.mu t i j) ⟨i.2.le, j.2⟩
  have hc := W.om_is (.chi (i : ℕ) j) ⟨i.2, j.2.le⟩
  have s0 := (node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).sd
  have s1 := (node_isV G hL (X := .grid (i : ℕ) ((j : ℕ) + 1)) ⟨i.2.le, j.2⟩).sd
  have s2 := (node_isV G hL (X := .grid ((i : ℕ) + 1) (j : ℕ)) ⟨i.2, j.2.le⟩).sd
  set good : Pl D → Prop := fun v => Tame D v ∧
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrS (.mu t i j)) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrT (.mu t i j)) v ∧
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrS (.chi (i : ℕ) j)) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.chrT (.chi (i : ℕ) j)) v
    with hgood
  have hev : ∀ᶠ v : Pl D in Filter.cofinite, good v := by
    filter_upwards [GlobalTheory.FinPl.eventually_extUnram_two_notMem D,
      GlobalTheory.FinPl.ShapeSecond.ae_charUnramAt _ hm.hecS.1, GlobalTheory.FinPl.ShapeSecond.ae_charUnramAt _ hm.hecT.1,
      GlobalTheory.FinPl.ShapeSecond.ae_charUnramAt _ hc.hecS.1, GlobalTheory.FinPl.ShapeSecond.ae_charUnramAt _ hc.hecT.1]
      with v h0 h1 h2 h3 h4
    exact ⟨⟨h0.1, Or.inl h0.2⟩, h1, h2, h3, h4⟩
  have hfin : {v | ¬ good v}.Finite := Filter.eventually_cofinite.1 hev
  classical
  refine ⟨G.Λ (.grid i j), hfin.toFinset ∪ (locPl G t).image (fun PP => PP.under (𝓞 D.host.F)),
    s0.1.fg, s0.1.span_eq_top, ?_⟩
  intro κ hκ u
  have hgd : ∀ v, v ∉ hfin.toFinset ∪ (locPl G t).image (fun PP => PP.under (𝓞 D.host.F)) → good v := by
    intro v hv
    by_contra h
    exact hv (Finset.mem_union_left _ (hfin.mem_toFinset.2 h))
  have hoff : ∀ PP ∈ locPl G t,
      ¬ (PP.under (𝓞 D.host.F) ∉ hfin.toFinset ∪ (locPl G t).image (fun PP => PP.under (𝓞 D.host.F))) :=
    fun PP hPP h => h (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hPP))
  unfold kerSmall
  refine Finsupp.sum_congr fun d hd => ?_
  obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  obtain ⟨d', hd', hd''⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hP)
  have hdd := Finsupp.support_single_subset hd''
  rw [Finset.mem_singleton] at hdd
  subst hdd
  obtain ⟨⟨hsb1, hth1⟩, ⟨hsb2, hth2⟩⟩ := h1 d' hd'
  have hv1 := ρ.vT_is t i j i.2.le j.2
  have hv2 := ρ.vX_is i j i.2 j.2.le
  congr 1
  congr 1
  · show thetaKO (W.om (.mu t i j)) (u * κ) g _ = thetaKO (W.om (.mu t i j)) u g _
    unfold thetaKO
    have e1 : ((u * κ, g) : GA D (G.pS (.mu t i j)) × GA D (G.pT (.mu t i j))) = (u, g) * (κ, 1) := by simp
    rw [e1, map_mul, Module.End.mul_apply]
    refine congrArg (fun x => W.om (.mu t i j) (u, g) x 0) ?_
    exact om_fock_fix _ _ _ _ _ _ _ hm W.θ_is _ _ _
      (fun v hv => ⟨s0, s1, (hgd v hv).1, (hgd v hv).2.1, (hgd v hv).2.2.1⟩) e _ he hoff _ _ _
      hv1.2.theta hv1.2.lat hth1 _ _ _ _ _ κ 1 hκ (inK_one _ _ _)
  · show thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) (u * κ) _ = thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) u _
    unfold thetaKO
    have e2 : ((negGA _ g₁, u * κ) : GA D (G.pS (.chi (i : ℕ) j)) × GA D (G.pT (.chi (i : ℕ) j))) =
        (negGA _ g₁, u) * (1, κ) := by simp
    rw [e2, map_mul, Module.End.mul_apply]
    refine congrArg (fun x => W.om (.chi (i : ℕ) j) (negGA _ g₁, u) x 0) ?_
    exact om_fock_fix _ _ _ _ _ _ _ hc W.θ_is _ _ _
      (fun v hv => ⟨isSelfDualC_neg s2, s0, (hgd v hv).1, (hgd v hv).2.2.2.1, (hgd v hv).2.2.2.2⟩) e _ he hoff _ _ _
      hv2.2.theta hv2.2.lat hth2 _ _ _ _ _ 1 κ (inK_one _ _ _) hκ

theorem exists_reg_at (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hst : SquareStanding G t) (M : Vol G) (hM : M.Is t) (Θ Θ')
    (hΘ : IsMatched B t ρ i j Θ Θ') (g g₁) (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∃ v ∉ P, ∃ w : GA D (G.V (.grid i j)) →₀ ℂ, zdeg w ≠ 0 ∧
      IntegrableOn (translates w (kerSmall W Θ' g g₁)) (M.fd _) (M.ν _) ∧
      ∀ b ∈ w.support, b ∈ Set.range (GlobalTheory.AdelicU.emb D.sp.cm.sig (G.V (.grid i j)).gram v) := by
  obtain ⟨e, Bs, Γ', X, om, om', h, hTr, hv, hvP⟩ := GlobalTheory.RegAt.squareTriple_avoid hL W t i j hst P M hM
  obtain ⟨z, Φ, a, C₀, hz, hΦ, hid, hsupp⟩ :=
    GlobalTheory.RegAt.translates_kerSmall_le_theta_at hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ' X om om' h hTr hv
  have dec := (hK.1 D.host.F D.host.E D.sp.cm.sig Bs _ _ Γ' X om om' hTr).1
  obtain ⟨C, k, hC⟩ := (dec.2 Φ hΦ).1 0
  have hbd : ∀ u, ‖translates z (kerSmall W Θ' g g₁) u‖ ≤
      |C₀| * |C| * (2 * GlobalTheory.Grow.quotHeight _ g * GlobalTheory.Grow.height _ g₁) ^ k := by
    intro u
    obtain ⟨γ, hγ, hle⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight _ g
    have e1 : translates z (kerSmall W Θ' g g₁) u = translates z (kerSmall W Θ' (γ * g) g₁) u := by
      simp only [translates, GlobalTheory.ZConvLeft.kerSmall_rat_left hL W B ρ t i j Θ Θ' hΘ g₁ γ hγ]
    rw [e1]
    have h1 := hC (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))
    rw [pow_zero, mul_one] at h1
    have h2 := GlobalTheory.BlockHeight.ht_blkU_le _ _ e h.JWW (γ * g) g₁
    have h3 : (0 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) := NNReal.coe_nonneg _
    have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) ≤
        2 * GlobalTheory.Grow.quotHeight _ g * GlobalTheory.Grow.height _ g₁ :=
      h2.trans (mul_le_mul_of_nonneg_right hle (GlobalTheory.Grow.height_pos _ _).le)
    calc _ ≤ C₀ * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))‖ := hid _ _
      _ ≤ |C₀| * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self C₀) (norm_nonneg _)
      _ ≤ |C₀| * (|C| * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h3 k)))
            (abs_nonneg C₀)
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h4 k) (mul_nonneg (abs_nonneg C₀) (abs_nonneg C))
  have hWl := (hM.vtx (.grid i j) ⟨i.2.le, j.2.le⟩).haar_fund
  haveI : IsFiniteMeasure ((M.ν (.grid i j)).restrict (M.fd (.grid i j))) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hWl.1 hWl.2).ne
  have hcont := GlobalTheory.SmallRoute.continuous_translates_kerSmall hL W B ρ t i j Θ Θ' hΘ g₁ z
  exact ⟨Bs.v₁, hvP, z, hz, Integrable.of_bound ((hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable) _
    (.of_forall hbd), hsupp⟩

open GlobalTheory.SmallConst in

theorem reg_const (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hst : SquareStanding G t) (M : Vol G) (hM : M.Is t) (Θ Θ')
    (hΘ : IsMatched B t ρ i j Θ Θ') (g g₁) :
    ∃ J : ℂ, ∀ z, IntegrableOn (translates z (kerSmall W Θ' g g₁)) (M.fd _) (M.ν _) →
      ∫ u in M.fd _, translates z (kerSmall W Θ' g g₁) u ∂M.ν _ = zdeg z * J := by
  classical
  have k2 := exists_reg_at hK hL W B ρ t i j hst M hM Θ Θ' hΘ g g₁
  obtain ⟨Λ, S, hfg, hsp, hright⟩ := kerSmall_inv hL W B ρ t i j Θ Θ' hΘ g g₁
  choose b' Pb hPb hKb using fun b => GlobalTheory.T.exists_finiteSupport_mul_latticeStabilizer (G.V (.grid i j)) Λ hfg hsp S b
  have hinv := kerSmall_rat_mid W B ρ t i j Θ Θ' hΘ g g₁
  set f := kerSmall W Θ' g g₁ with hf
  have kb : ∀ b u, f (u * b' b) = f (u * b) := fun b u => by
    have := hright _ (hKb b) (u * b' b)
    rw [← this, mul_assoc, mul_inv_cancel_left]
  have hfd := (hM.vtx (.grid i j) ⟨i.2.le, j.2.le⟩).haar_fund
  haveI := hfd.1
  have key := zdeg_mul_integral_comm (G.V (.grid i j)) (M.ν _) (M.fd _) hfd.2 f hinv
  obtain ⟨v₀, -, w₀, hw₀, hi₀, hs₀⟩ := k2 ∅
  refine ⟨(∫ u in M.fd _, translates w₀ f u ∂M.ν _) / zdeg w₀, fun z hz => ?_⟩
  have hz'f : translates (z.mapDomain b') f = translates z f := by
    funext u
    simp only [translates]
    rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
    exact Finsupp.sum_congr fun b _ => by rw [kb]
  have hz'd : zdeg (z.mapDomain b') = zdeg z := by
    simp only [zdeg]
    rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
  obtain ⟨v, hv, w, hw, hi, hs⟩ := k2 (insert v₀ (z.support.biUnion Pb))
  have hv0 : v ≠ v₀ := fun h => hv (h ▸ Finset.mem_insert_self _ _)
  have c1 : ∀ x ∈ w.support, ∀ y ∈ (z.mapDomain b').support, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', rfl⟩ := hs x hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hy)
    exact GlobalTheory.AdelicU.commute_emb _ _ x' (hPb b v fun h => hv (Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨b, hb, h⟩)))
  have c2 : ∀ x ∈ w.support, ∀ y ∈ w₀.support, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', rfl⟩ := hs x hx
    obtain ⟨y', rfl⟩ := hs₀ y hy
    exact GlobalTheory.AdelicU.commute_emb _ _ x' (GlobalTheory.AdelicU.proj_emb_ne _ _ hv0 y')
  have e1 := key w _ c1 hi (by rw [hz'f]; exact hz)
  have e2 := key w w₀ c2 hi hi₀
  rw [hz'f, hz'd] at e1
  rw [mul_div_assoc', eq_div_iff hw₀]
  apply mul_left_cancel₀ hw
  linear_combination zdeg w₀ * e1 - zdeg z * e2

end GlobalTheory.ThetaRegularizationComparison

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectOfPeriodStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harrisTaylor_object_of_period : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (D' : PLat D.O D.inv) t Q, 0 < N → N.Coprime p → b.IsType σ ρ → D.Cls N D' t → IsPeriod D' ρ Q → ∃ (o : Obj b N (spMap σ)) (h : _) (hL : _) (e : _), UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e := by
  first | (exact @GlobalTheory.UPel.HT.exists_obj_unifAt_of_period) | (exact GlobalTheory.UPel.HT.exists_obj_unifAt_of_period) | (intros; apply GlobalTheory.UPel.HT.exists_obj_unifAt_of_period <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorPeriodDefectZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatMod

namespace GlobalTheory.HeatMod

theorem opMod {R : Type} [CommRing R] (G : Over (Sp R)) {n : ℕ} (dd : Fin n → Fld G.left)
    (Θ M : Matrix (Fin n) (Fin n) R) (u c₁ c₂ : Fin n → R) (d : Fld G.left) {W : G.left.Opens} (p p' : Γ(G.left, W))
    (k : ℕ) (O : G.left.Opens) (f : Γ(G.left, O)) :
    op G dd (Θ + M) (u - c₁) (fun O f => d O f - combF G.hom dd c₂ O f) p p' k O f =
      op G dd Θ u d p p' k O f - 2 * (k : Γ(G.left, O)) * combF G.hom dd c₂ O f - quadF G.hom dd M O f -
        2 * combF G.hom dd c₁ O f := by
  have hc : ∀ a b : R, constFn G.hom O (a + b) = constFn G.hom O a + constFn G.hom O b := fun a b => by
    simp [constFn]
  have hs : ∀ a b : R, constFn G.hom O (a - b) = constFn G.hom O a - constFn G.hom O b := fun a b => by
    simp [constFn]
  simp only [op, combF, quadF, Matrix.add_apply, Pi.sub_apply, hc, hs, add_mul, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring

theorem rsT_resG_constFn {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {U V : Z.Opens} (hV : V ≤ U)
    (x : R) : rsT (resG Z (le_top : U ≤ ⊤) (constFn s ⊤ x)) V = constFn s V x := by
  rw [← GlobalTheory.KS.rsT_of_le (le_top : U ≤ ⊤), GlobalTheory.KS.rsT_rsT le_top hV, GlobalTheory.KS.rsT_constFn _ le_top]

theorem defect_cancel {R X : Type} [CommRing R] [AddCommGroup X] (w : X → X →+ R) (π π' : X → R) (half : R)
    (h2 : 2 * half = 1) (hw1 : ∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) (hw2 : ∀ mu mu', w mu mu' = w mu' mu)
    (hπ' : ∀ mu mu', π' (mu + mu') = π' mu + π' mu') (hπ : ∀ mu mu', π (mu + mu') = π mu + π mu' + w mu' mu)
    (k : ℕ) (mu α : X) :
    0 = 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu +
      (-(2 * (k : R) * (π (α + k • mu) - half * w (α + k • mu) (α + k • mu))) - w (α + k • mu) (α + k • mu) -
        2 * π' (α + k • mu)) -
      (-(2 * (k : R) * (π α - half * w α α)) - w α α - 2 * π' α) := by
  have wsm : ∀ (m : ℕ) (x y : X), w (m • x) y = (m : R) * w x y := by
    intro m x y
    induction m with
    | zero =>
      simp only [zero_smul, Nat.cast_zero, zero_mul]
      have := hw1 0 0 y
      simp only [add_zero] at this
      linear_combination -this
    | succ m ih => rw [succ_nsmul, hw1, ih]; push_cast; ring
  have psm : ∀ (m : ℕ) (x : X), π' (m • x) = (m : R) * π' x := by
    intro m x
    induction m with
    | zero =>
      simp only [zero_smul, Nat.cast_zero, zero_mul]
      have := hπ' 0 0
      simp only [add_zero] at this
      linear_combination -this
    | succ m ih => rw [succ_nsmul, hπ', ih]; push_cast; ring
  have qsm : ∀ (m : ℕ) (x : X), π (m • x) = (m : R) * π x + half * ((m : R) ^ 2 - m) * w x x := by
    intro m x
    induction m with
    | zero =>
      have := hπ 0 0
      simp only [add_zero, map_zero, AddMonoidHom.zero_apply] at this
      simp only [zero_smul, Nat.cast_zero]
      linear_combination -this
    | succ m ih =>
      rw [succ_nsmul, hπ, ih, map_nsmul, nsmul_eq_mul]
      push_cast
      linear_combination (-(m : R) * w x x) * h2
  simp only [hπ, hπ', hw1, map_add, wsm, map_nsmul, psm, qsm, nsmul_eq_mul, hw2 α mu]
  linear_combination (-((k : R) ^ 2 * w mu mu + 2 * (k : R) ^ 2 * w mu α)) * h2

theorem exists_heat_defect_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (w : Dd.toPre.X → Dd.toPre.X →+ R) (π π' : Dd.toPre.X → R), IsBasic Y h → HasDefect Y h (fun (k : ℕ) mu α => 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) → (∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) → (∀ mu mu', w mu mu' = w mu' mu) → (∀ mu mu', π' (mu + mu') = π' mu + π' mu') → (∀ mu mu', π (mu + mu') = π mu + π mu' + w mu' mu) → ∃ h' : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h' ∧ HasDefect Y h' (fun _ _ _ => 0) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv D h w π π' hB hD hw1 hw2 hπ' hπ
  let ℓ₁ : Dd.toPre.X →+ R := AddMonoidHom.mk' π' hπ'
  let half : R := algebraMap ℚ R (1 / 2)
  have h2 : (2 : R) * half = 1 := by
    simp only [half]
    rw [← map_ofNat (algebraMap ℚ R) 2, ← map_mul]
    norm_num
  let ℓ₂ : Dd.toPre.X →+ R := AddMonoidHom.mk' (fun x => π x - half * w x x) (fun a b => by
    simp only [hπ, hw1, map_add]
    rw [hw2 b a]
    linear_combination (-(w a b)) * h2)
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.exists_torus_invariantField_const_coeffs R Dd O oa Y n v dd hv ℓ₁
  obtain ⟨c₂, hc₂⟩ := GlobalTheory.T.exists_torus_invariantField_const_coeffs R Dd O oa Y n v dd hv ℓ₂
  obtain ⟨M, hMs, hMa, hMg⟩ := GlobalTheory.T.exists_symmetric_second_order_operator_of_character_form R Dd O oa Y n v dd hv w hw1 hw2
  obtain ⟨⟨a1, a2, a3⟩, kc, wt₂, pb₂⟩ := hc₂
  let h' : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D :=
    { Θ := h.Θ + M
      symm := by rw [Matrix.transpose_add, h.symm, hMs]
      u := h.u - c₁
      J := h.J
      W := h.W
      j := h.j
      d := fun i O f => h.d i O f - combF Y.H.hom dd c₂ O f
      p := h.p
      p' := h.p'
      cover := h.cover
      le := h.le
      lift := fun i => by
        obtain ⟨⟨f1, f2, f3⟩, fc⟩ := h.lift i
        refine ⟨⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' hh hW f => ?_⟩, fun W hW r => ?_⟩
        · dsimp only; rw [f1 W hW, a1 W le_top]; ring
        · dsimp only; rw [f2 W hW, a2 W le_top]; ring
        · dsimp only; rw [f3 W W' hh hW, a3 W W' hh le_top, map_sub]
        · dsimp only; rw [fc W hW, kc, sub_zero]
      glue := fun k i i' O hO f => by
        have hle : O ≤ Y.q.left ⁻¹ᵁ (Dd.toPre.P.L.U (h.j i) ⊓ Dd.toPre.P.L.U (h.j i')) := fun x hx =>
          ⟨h.le i (hO hx).1, h.le i' (hO hx).2⟩
        rw [opMod, opMod, h.glue k i i' O hO f, pb₂ _ _ O k f hle, hMg _ _ O k f hle, hc₁.2.2.2 _ _ O k f hle]
        ring }

  have wsm : ∀ (m : ℕ) (x y : Dd.toPre.X), w (m • x) y = (m : R) * w x y := by
    intro m x y
    induction m with
    | zero => simp only [zero_smul, Nat.cast_zero, zero_mul]; have := hw1 0 0 y; simp only [add_zero] at this; linear_combination -this
    | succ m ih => rw [succ_nsmul, hw1, ih]; push_cast; ring
  let e : ℕ → Dd.toPre.X → R := fun k α => -(2 * (k : R) * ℓ₂ α) - w α α - 2 * ℓ₁ α
  have key : ∀ k α σ σ', TActs Y h' k α σ σ' →
      TActs Y h k α σ (σ' - constFn Dd.toPre.P.A.hom ⊤ (e k α) • σ) := by
    rintro k α σ σ' ⟨τ, τ', hτ, hτ', hA⟩
    refine ⟨τ, τ' - constFn Y.H.hom ⊤ (e k α) • τ, hτ, GlobalTheory.T.isRaynaudFourierTerm_sub_smul R Dd.toPre O oa Y k α σ σ' τ τ' (e k α) hτ hτ',
      fun i => ?_⟩
    have hA' := hA i
    obtain ⟨V, hV⟩ := (hB i).1
    have hwt := GlobalTheory.T.raynaudFourierTerm_chartRestriction_isWeight R Dd.toPre O oa Y k α σ τ hτ (h.j i) (h.W i) ⟨V, hV⟩ (h.le i)
    change rsT (τ'.f fun _ => h.j i) (h.W i) = op Y.H dd (h.Θ + M) (h.u - c₁)
      (fun O f => h.d i O f - combF Y.H.hom dd c₂ O f) (h.p i) (h.p' i) k (h.W i)
      (rsT (τ.f fun _ => h.j i) (h.W i)) at hA'
    rw [opMod, wt₂ α _ ⟨V, hV⟩ _ hwt, hMa α _ ⟨V, hV⟩ _ hwt, hc₁.2.2.1 α _ ⟨V, hV⟩ _ hwt] at hA'
    have hle' : h.W i ≤ LB.wchart Dd.toPre.P.L (K := Fin 1) (fun _ => Y.q.left) (fun _ => h.j i) := fun x hx =>
      Set.mem_iInter.2 fun _ => h.le i hx
    have hce : constFn Y.H.hom (h.W i) (e k α) = -(2 * (k : Γ(Y.H.left, h.W i)) * constFn Y.H.hom (h.W i) (ℓ₂ α)) -
        constFn Y.H.hom (h.W i) (w α α) - 2 * constFn Y.H.hom (h.W i) (ℓ₁ α) := by
      have hcf : ∀ a, constFn Y.H.hom (h.W i) a = ((Y.H.hom.appLE ⊤ (h.W i) (fun _ _ => trivial)).hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) a := fun _ => rfl
      simp only [hcf, e, map_sub, map_neg, map_mul, map_natCast, map_ofNat]
    change rsT ((τ'.f fun _ => h.j i) - resG Y.H.left le_top (constFn Y.H.hom ⊤ (e k α)) * τ.f fun _ => h.j i) (h.W i) = _
    rw [GlobalTheory.KS.rsT_sub, GlobalTheory.KS.rsT_mul, rsT_resG_constFn, hA', hce]
    · ring
    · exact hle'
  refine ⟨h', fun i => ?_, ?_⟩
  · obtain ⟨b1, b2, b3, b4⟩ := hB i
    refine ⟨b1, b2, b3, fun α V hV f hf => ?_⟩
    show IsWt Y α _ (h.d i _ f - combF Y.H.hom dd c₂ _ f)
    rw [wt₂ α _ ⟨V, rfl⟩ f hf]
    exact GlobalTheory.T.isRaynaudTorusWeightFunction_sub_const_mul R Dd.toPre O oa Y α _ _ f (ℓ₂ α) (b4 α V hV f hf) hf
  · intro k mu α σ σ' σ₁ σ₁' hk hS hT1 hT2
    have H := hD k mu α σ _ σ₁ _ hk hS (key _ _ _ _ hT1) (key _ _ _ _ hT2)
    have H2 := GlobalTheory.T.thetaShiftFunctionalEq_sub_constFn_smul R Dd.toPre k mu α σ σ' σ₁ σ₁' _ _ _ hS H
    convert H2 using 1
    exact defect_cancel w π π' half h2 hw1 hw2 hπ' hπ k mu α

end GlobalTheory.HeatMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegCompOfFirstTop
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegCompTop

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

theorem exists_isPullDeg_comp_of_preimage {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''}
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D'')
    (hW : specOf i ⁻¹ᵁ p.W = ⊤) :
    ∃ r : IsPullDeg (j.comp i) D D'', proj r = proj q ≫ proj p ∧ ∀ x, r.xe x = p.xe (q.xe x) := by
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  obtain ⟨ψ', hv⟩ := PullDegCancelTop.exists_psiOn_pull p
  obtain ⟨g, hg'⟩ : ∃ g : (TK R'').left ⟶ (specOf i ⁻¹ᵁ p.W).toScheme,
      g ≫ (specOf i ⁻¹ᵁ p.W).ι = jK R'' ≫ specOf j :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro y -
      rw [Scheme.Opens.range_ι, hW]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  have hg : (g ≫ (specOf i ∣_ p.W)) ≫ p.W.ι = jK R'' ≫ specOf (j.comp i) := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hg', Category.assoc]
    exact congrArg (jK R'' ≫ ·) sc
  obtain ⟨r, hr₁, hr₂, -⟩ := PullDegCompData.exists_isPullDeg_of_valW D D'' p.psiW (g ≫ (specOf i ∣_ p.W)) hg gp w
    (T.pgen_comp D'.P.isLB g₁ g₂) hr (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have v₁ := hv (q.xe x) _ g z J J' hJ hJ'
      have v₂ := PsiEvenPull.psi_pull q x (𝟙 _) z hJ' hJ''
      have ag : val (ψ'.psi (q.xe x)) g z J' = val (q.psiW.psi (q.xe x)) (𝟙 _ ≫ q.g) z J' :=
        ArcSpecialise.psiOn_agree ψ' q.psiW _ _ _ (by rw [hg', Category.id_comp, q.g_comm]) hJ'
      have hx : D''.xK x ≫ proj q = g ≫ (specOf i ⁻¹ᵁ p.W).ι ≫ (D'.c (q.xe x)).left := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = _
        rw [Category.assoc, q.c_pr, ← Category.assoc g, hg', Category.assoc]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      change _ = (om q.w z J' J'' (𝟙 _ ≫ D''.xK x))⁻¹ * _ at v₂
      rw [ag, v₂, Category.id_comp, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r, hr₁, hr₂⟩

theorem exists_isPullDeg_comp_top : ∀ {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D''), p.W = ⊤ → ∃ r : IsPullDeg (j.comp i) D D'', r.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (j.comp i)) = (q.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf j)) ≫ p.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) ∧ ∀ x, r.xe x = p.xe (q.xe x) := by
  intro R R' R'' _ _ _ _ _ _ i j D D' D'' p q e
  exact exists_isPullDeg_comp_of_preimage p q (by rw [e]; rfl)

end GlobalTheory.PullDegCompTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinSymplecticTransferStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zarhinSymplecticTransfer : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ), GlobalTheory.ZarhinFam.KappaOK h M d κ := by
  first | (exact @GlobalTheory.ZarhinFam.exists_kappaOK) | (exact GlobalTheory.ZarhinFam.exists_kappaOK) | (intros; apply GlobalTheory.ZarhinFam.exists_kappaOK  <;> assumption)
end

