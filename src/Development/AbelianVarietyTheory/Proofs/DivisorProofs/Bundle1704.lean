import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
import Formalism.PairingDivisors.StatementH
import Formalism.PairingDivisors.PairingDivisorProofs.Height
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1675
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0913
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0912
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0063
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0053

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodularAndLintegralUnfoldOfLattice
section
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

namespace GlobalTheory.ResLine.RightUnfold

theorem isMulRightInvariant_of_lattice {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (Λ : Subgroup G)
    [Countable Λ] (𝓑 : Set G) (h𝓑 : IsFundamentalDomain Λ 𝓑 ν) (hfin : ν 𝓑 ≠ ⊤) :
    ν.IsMulRightInvariant := by
  refine ⟨fun x => ?_⟩
  haveI : (ν.map (· * x)).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right ν x
  have hc := Measure.isMulLeftInvariant_eq_smul (ν.map (· * x)) ν
  set c := Measure.haarScalarFactor (ν.map (· * x)) ν
  have h𝓑' : IsFundamentalDomain Λ ((· * x) ⁻¹' 𝓑) ν := by
    refine h𝓑.preimage_of_equiv (quasiMeasurePreserving_mul_right ν x) (e := id)
      Function.bijective_id ?_
    intro g y
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hm : ν ((· * x) ⁻¹' 𝓑) = ν 𝓑 := h𝓑'.measure_eq h𝓑
  have h0 : ν 𝓑 ≠ 0 := h𝓑.measure_ne_zero (NeZero.ne ν)
  have hmap : (ν.map (· * x)) 𝓑 = ν ((· * x) ⁻¹' 𝓑) :=
    MeasurableEquiv.map_apply (MeasurableEquiv.mulRight x) 𝓑
  have h1 : (c : ENNReal) * ν 𝓑 = 1 * ν 𝓑 := by
    calc (c : ENNReal) * ν 𝓑 = (c • ν) 𝓑 := by simp [Measure.smul_apply]
      _ = (ν.map (· * x)) 𝓑 := by rw [hc]
      _ = 1 * ν 𝓑 := by rw [one_mul]; exact hmap.trans hm
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj h0 hfin).1 h1
    exact_mod_cast this
  rw [hc, hc1, one_smul]

theorem isInvInvariant_of_right {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.IsInvInvariant := by
  constructor
  let c : ENNReal := Measure.haarScalarFactor μ.inv μ
  have hc : μ.inv = c • μ := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have h1 : Measure.map Inv.inv (Measure.map Inv.inv μ) = c ^ 2 • μ := by
    rw [← Measure.inv_def μ, hc, Measure.map_smul, ← Measure.inv_def μ, hc, smul_smul, pow_two]
  have μeq : μ = c ^ 2 • μ := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at h1
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id] using h1
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have h2 : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [μeq]
    simp
  have h3 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
          K.isCompact.measure_lt_top.ne).1 h2
  have h4 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h3
  rw [hc, h4, one_smul]

theorem unimodular_and_unfold : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) (Λ : Subgroup G) [Countable Λ] (𝓑 : Set G), ν.IsHaarMeasure → IsFundamentalDomain Λ 𝓑 ν → ν 𝓑 ≠ ⊤ → ν.IsMulRightInvariant ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂ν = ∫⁻ b in 𝓑, ∑' γ : Λ, f (b⁻¹ * γ) ∂ν := by
  intro G _ _ _ _ _ _ _ _ ν Λ _ 𝓑 hν h𝓑 hfin
  haveI hR := isMulRightInvariant_of_lattice ν Λ 𝓑 h𝓑 hfin
  haveI := isInvInvariant_of_right ν
  refine ⟨hR, fun f hf => ?_⟩
  rw [← lintegral_inv_eq_self f, h𝓑.lintegral_eq_tsum' (fun x => f x⁻¹), lintegral_tsum]
  · refine tsum_congr fun γ => ?_
    refine lintegral_congr fun b => ?_
    simp [Subgroup.smul_def]
  · intro γ
    exact (hf.comp (measurable_inv.mul_const _)).aemeasurable

end GlobalTheory.ResLine.RightUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedEtaCharacterKillsFiniteIdeleNorm
section
noncomputable section

namespace GlobalTheory.EtaTildeNorm

section SlopeTestRemainingChoices

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory.Mem.Chr.IdlFact GlobalTheory.Mem.Chr.KDVal
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.Mem.Col2.SplitChar

theorem map_finPartI_locF {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra F L] (χ : HChar L)
    (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : χ.1 (finPartI L (locF F v k)) = χ.resFin v k := by
  unfold HChar.resFin
  rw [MonoidHom.finsetProd_apply]
  unfold locF
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun Q _ => congrArg χ.1 (GlobalTheory.Mem.KerDet.finPartI_localIdele Q _)

theorem eq_one (D : D7) (χ : HChar D.host.E) (hχ : IsEtaT D.host χ) (x : (AE D)ˣ) :
    χ.1 (finIdl D (x * sgU D x)) = 1 := by
  classical
  obtain ⟨c, hc, hcm, hu, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  have ec : c.toRingEquiv = D.host.conj.toRingEquiv := RingEquiv.ext hc
  set a : Ideles D.host.E := finIdl D (x * sgU D x) with ha_def
  have ha : a ∈ balanced (L := D.host.E) D.host.F := norm_balanced x
  let T : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
    (finite_valAt_ne_one a).toFinset.image fun w => w.under (𝓞 D.host.F)
  let m : HeightOneSpectrum (𝓞 D.host.F) → ℤ := fun v =>
    if h : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v then -WithZero.log (valAt h.choose a) else 0
  let b : Ideles D.host.E := ∏ v ∈ T, locF (L := D.host.E) D.host.F v (unif v) ^ m v
  have hm : ∀ w : HeightOneSpectrum (𝓞 D.host.E), m (w.under (𝓞 D.host.F)) = -WithZero.log (valAt w a) := fun w => by
    have hex : ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := ⟨w, rfl⟩
    simp only [m]
    rw [dif_pos hex, ha w hex.choose hex.choose_spec]
  have hval : ∀ w, valAt w b = valAt w a := fun w => by
    have h1 : ∀ v, v ≠ w.under (𝓞 D.host.F) → valAt w (locF (L := D.host.E) D.host.F v (unif v) ^ m v) = 1 :=
      fun v hv => by rw [map_zpow, valAt_locF, if_neg hv.symm, one_zpow]
    simp only [b]
    rw [map_prod]
    by_cases hw : w.under (𝓞 D.host.F) ∈ T
    · rw [Finset.prod_eq_single_of_mem _ hw (fun v _ hv => h1 v hv), map_zpow, valAt_locF, if_pos rfl, hu,
        ordF_unif_self, ← WithZero.exp_zsmul, hm]
      simp only [smul_eq_mul, mul_neg, neg_neg, mul_one]
      exact WithZero.exp_log (valAt_ne_zero w a)
    · rw [Finset.prod_eq_one (fun v hv => h1 v (fun e => hw (e ▸ hv)))]
      by_contra hne
      exact hw (Finset.mem_image_of_mem _ (by simpa using fun e => hne e.symm))
  have hu' : b⁻¹ * a ∈ unitIdl D.host.E := fun w => by
    rw [← valAt_apply, map_mul, map_inv, hval]
    exact inv_mul_cancel₀ (valAt_ne_zero w a)

  have h1 : χ.1 (finPartI D.host.E (b⁻¹ * a)) = 1 :=
    GlobalTheory.Mem.LocTriv.eq_one_of_local _ χ.1 χ.2.1 _ (finPartI_mem_unitIdl.2 hu') (fun _ => rfl) fun v y hy =>
      hχ.unr v y (by
        unfold IsUnitAt
        rw [hy]
        exact hu' v)

  have h2 : χ.1 (finPartI D.host.E b) = 1 := by
    simp only [b]
    rw [map_prod, map_prod]
    refine Finset.prod_eq_one fun v hv => ?_
    rw [map_zpow, map_zpow, map_finPartI_locF, hχ.res.1 v, etaFin]
    split_ifs with hcard
    · rw [ordF_unif_self, zpow_one]
      obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hv
      rw [hm]
      obtain ⟨w', hw', -⟩ := existsUnique_conjPl D.host.conj.toRingEquiv w
      have hund : w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) :=
        (under_eq_iff_conjPl c hcm.rank hcm.ne w w').2 (Or.inr (by rw [ec]; exact hw'))
      have hmem : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) →
          Q ∈ aboveF (L := D.host.E) D.host.F (w.under (𝓞 D.host.F)) := fun Q hQ => by
        simp [aboveF, hQ]
      have hww : w' = w := Finset.card_le_one.1 hcard.le _ (hmem w' hund) _ (hmem w rfl)
      subst hww
      have e1 : valAt w' a = vl D w' (x : AE D) * vl D w' (x : AE D) := by
        change vl D w' ((x : AE D) * sgA D x) = _
        rw [map_mul, vl_sgA hw' x]
      have h0 : vl D w' (x : AE D) ≠ 0 := by
        intro h
        have := valAt_ne_zero w' a
        rw [e1, h, zero_mul] at this
        exact this rfl
      rw [e1, WithZero.log_mul h0 h0]
      exact Even.neg_one_zpow (Even.add_self _).neg
    · exact one_zpow _
  have e : a = b * (b⁻¹ * a) := (mul_inv_cancel_left b a).symm
  have e2 : finPartI D.host.E a = a := by rw [ha_def]; exact finPartI_finIdl D _
  rw [← e2, e, map_mul, map_mul, h1, h2, one_mul]

end SlopeTestRemainingChoices

end GlobalTheory.EtaTildeNorm

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

theorem GlobalTheory.EtaTildeNorm.map_finIdl_norm : ∀ (D : D7) (χ : HChar D.host.E), Formalism.L2.Host.IsEtaT D.host χ →
    ∀ x : (AE D)ˣ, χ.1 (finIdl D (x * sgU D x)) = 1 :=
  fun D χ hχ x => GlobalTheory.EtaTildeNorm.eq_one D χ hχ x
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationMinpolyCoeffZeroGeOfPowMulIntegral
section
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.FunObj.SqNum.LowVal

theorem coeff_zero_mul_pow_mem {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {β : ℂ} {p : K[X]}
    (h : IsMinPol σ β p) {c : ℕ} (hc0 : (c : K) ≠ 0) (hc : IsIntegral ℤ ((c : ℂ) * β)) :
    ∃ a : 𝓞 K, p.coeff 0 * (c : K) ^ p.natDegree = (a : K) := by
  letI : Algebra K ℂ := σ.toAlgebra
  letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  haveI : IsScalarTower (𝓞 K) K ℂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ℤ (𝓞 K) ℂ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hβ : IsIntegral K β := ⟨p, h.1, h.2.2⟩
  have es : (c : K) • β = (c : ℂ) * β := by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_natCast]
  have hγ : IsIntegral (𝓞 K) ((c : K) • β) := by
    rw [es]; exact hc.tower_top
  have e1 := IsIntegrallyClosed.minpoly_smul (R := K) hc0 hβ
  have e2 := minpoly.isIntegrallyClosed_eq_field_fractions' K hγ
  rw [← h.eq_minpoly] at e1
  refine ⟨(minpoly (𝓞 K) ((c : K) • β)).coeff 0, ?_⟩
  rw [RingOfIntegers.coe_eq_algebraMap, ← coeff_map, ← e2, e1, coeff_scaleRoots, Nat.sub_zero]

theorem natCast_not_mem {K : Type} [Field K] [NumberField K] {w : Formalism.PairingDivisionLocalBalance.Pl K} {l n : ℕ} (hn : n.Coprime l)
    (hw : (l : 𝓞 K) ∈ w.asIdeal) : (n : 𝓞 K) ∉ w.asIdeal := by
  intro h
  obtain ⟨x, y, e⟩ := (Nat.isCoprime_iff_coprime.2 hn).map (Int.castRingHom (𝓞 K))
  refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← e]
  exact add_mem (Ideal.mul_mem_left _ _ (by simpa using h)) (Ideal.mul_mem_left _ _ (by simpa using hw))

theorem vw_coeff_zero_ge : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (β : ℂ) (p : K[X]) (l N : ℕ),
    GlobalTheory.FunObj.SqNum.IsMinPol σ β p → l.Prime → GlobalTheory.CMVal.IntAt l ((l : ℂ) ^ (N : ℤ) * β) →
    ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, (l : 𝓞 K) ∈ w.asIdeal → -(((N * p.natDegree : ℕ) : ℤ) * vw w (l : K)) ≤ vw w (p.coeff 0) := by
  intro K _ _ _ σ β p l N h hl ⟨n, hn, hi⟩ w hw
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hl.one_lt.ne' (Nat.coprime_zero_left l |>.1 hn)
  have hc : IsIntegral ℤ (((n * l ^ N : ℕ) : ℂ) * β) := by
    convert hi using 1
    push_cast
    rw [zpow_natCast]
    ring
  have hl0 : (l : K) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hn0' : (n : K) ≠ 0 := by exact_mod_cast hn0
  have hc0 : ((n * l ^ N : ℕ) : K) ≠ 0 := by
    push_cast
    exact mul_ne_zero hn0' (pow_ne_zero _ hl0)
  obtain ⟨a, ha⟩ := coeff_zero_mul_pow_mem h hc0 hc
  have h1 : 0 ≤ vw w (p.coeff 0 * ((n * l ^ N : ℕ) : K) ^ p.natDegree) := by
    rw [ha]; exact Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w a
  have hvn : vw w (n : K) = 0 := by
    have := Formalism.DivisionValues.ReductionFirst.vw_unit w (n : 𝓞 K) (natCast_not_mem hn hw)
    simpa using this
  have hvl := Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w l
  by_cases hp0 : p.coeff 0 = 0
  · rw [hp0, Formalism.DivisionValues.ValuationRepresentative.vw_zero]
    have : (0 : ℤ) ≤ ((N * p.natDegree : ℕ) : ℤ) := Int.natCast_nonneg _
    nlinarith
  · rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hp0 (pow_ne_zero _ hc0), Formalism.PairingDivisionLocalBalance.vw_pow w _ hc0] at h1
    push_cast at h1
    rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hn0' (pow_ne_zero _ hl0), Formalism.PairingDivisionLocalBalance.vw_pow w _ hl0, hvn] at h1
    push_cast
    nlinarith

end GlobalTheory.FunObj.SqNum.LowVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingLocusClosedSubschemeStatement
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vanishing_locus_closed_subscheme : ∀ (Y : Scheme.{0}) (G Q : Y.Modules) (u : G ⟶ Q), G.IsQuasicoherent → IsVB Q 1 → ∃ (Z : Scheme.{0}) (j : Z ⟶ Y), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (h : T ⟶ Y), (Scheme.Modules.pullback h).map u = 0 ↔ ∃ h' : T ⟶ Z, h' ≫ j = h := by
  first | exact @GlobalTheory.ZeroLocus.exists_closed_zeroLocus | exact GlobalTheory.ZeroLocus.exists_closed_zeroLocus | (intros; apply GlobalTheory.ZeroLocus.exists_closed_zeroLocus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIntegralLocalToFiniteStatement
section
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_integral_local_to_finite : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), WeilIntegralLocal P → WeilIntegralFinite P := by
  first | exact @GlobalTheory.WeilIntegral.weilIntegralFinite_of_local | exact GlobalTheory.WeilIntegral.weilIntegralFinite_of_local | (intros; apply GlobalTheory.WeilIntegral.weilIntegralFinite_of_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingIntegralStatement
section
open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_pairing_integral : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), HasCubeFn P.A → HasTrivialisingOpen P → TranslatesInto P → CubeValuesIntegral P → WeilIntegralLocal P := by
  first | exact @GlobalTheory.WeilIntegral.Local.weilIntegralLocal_of_cubes | exact GlobalTheory.WeilIntegral.Local.weilIntegralLocal_of_cubes | (intros; apply GlobalTheory.WeilIntegral.Local.weilIntegralLocal_of_cubes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationRealMovesFrameDetChar
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealMove

theorem muVal_mul {D : D7} {V : HSp D} {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : Formalism.L2.Pj.MuVal V χ mu)
    (g g' : GA D V) : mu (g * g') = mu g * mu g' := by
  obtain ⟨x, hx⟩ := h.1 g
  obtain ⟨x', hx'⟩ := h.1 g'
  have hxx : IsDetRoot V (g * g') (x * x') := by
    unfold IsDetRoot at *
    rw [map_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, map_mul]
    rw [mul_mul_mul_comm, ← hx, ← hx']
  rw [h.2 _ _ hxx, h.2 _ _ hx, h.2 _ _ hx', map_mul, Circle.coe_mul]

theorem frMove_mul {D : D7} (θ : InfFam D) (W : HSp D) (X : Data D.host.E W.rank) (hX : IsMod W rfl X)
    (u v : GA D W) (x : Frame X.Ψ W.rank) :
    frMove θ W rfl X (u * v) x = frMove θ W rfl X u (frMove θ W rfl X v x) := by
  funext τ
  have hτ : ∃ ρ, τ.1 = tauE D ρ := (hX.psi τ.1).1 τ.2
  have e : realM θ (Formalism.L2.Theta.mt W (u * v)) τ.1 =
      realM θ (Formalism.L2.Theta.mt W u) τ.1 * realM θ (Formalism.L2.Theta.mt W v) τ.1 := by
    unfold realM
    rw [dif_pos hτ, dif_pos hτ, dif_pos hτ, GlobalTheory.UnitaryChar.compAt_mt_mul]
  show (Matrix.reindex (finCongr rfl) (finCongr rfl) (realM θ (Formalism.L2.Theta.mt W (u * v)) τ.1) * mat x τ :
      Matrix (Fin W.rank) (Fin W.rank) ℂ) =
    Matrix.reindex (finCongr rfl) (finCongr rfl) (realM θ (Formalism.L2.Theta.mt W u) τ.1) *
      (Matrix.reindex (finCongr rfl) (finCongr rfl) (realM θ (Formalism.L2.Theta.mt W v) τ.1) * mat x τ)
  rw [e, ← Matrix.mul_assoc]
  simp

theorem om_real_reads : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r), IsONFr X x → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ u ∈ GinfC W, Reads θ V W hr X bas idx (om (1, u) f) (mu u • φ) (frMove θ W hr X u x) := by
  intro D ψ θ V W χV χW om hP mu hmu r g hr X bas idx hX hS x hx f φ hf hR
  subst hr
  have hstd := hP.weil.std
  obtain ⟨X', m, hq', hq, bas', idx', hs, -, -, -, -, -, -, hfr⟩ :=
    GlobalTheory.T.orthonormal_frame_reading_eq_conjugate_datum_theta D ψ θ V W g X bas idx hstd hP.inf hP.even hP.std hX hS
  set C : GlobalTheory.Ker.Ctx V W := ⟨ψ, hstd, θ, hP.inf, X', m, g, X.p0, hq', bas', idx', hs, hP.even⟩ with hC
  obtain ⟨⟨B, hB⟩, hBx⟩ := hfr x hx
  obtain ⟨hIsB, hinv, -, -, -, -, -, hmv, hTh⟩ := hBx B hB
  have hfe : f = C.Th (C.xB B) φ := (hTh f φ hR.1).1 ⟨hf, hR⟩
  have hON : ∀ u, IsONFr X (frMove θ W rfl X u x) := fun u => (hmv u).1
  have hpres : ∀ u : GA D W, IsThetaFunO ψ V W (om (1, u) f) := fun u => hP.weil.om_pres _ _ hf
  have hc : ∀ u : GA D W, ∃ c : ℂ, u ∈ GinfC W → ‖c‖ = 1 ∧
      Reads θ V W rfl X bas idx (om (1, u) f) (c • φ) (frMove θ W rfl X u x) := by
    intro u
    by_cases hu : u ∈ GinfC W
    swap
    · exact ⟨1, fun h => absurd h hu⟩
    obtain ⟨c, hc1, hc⟩ := GlobalTheory.Ker.RealScalar.om_real_Th D V W C om (GlobalTheory.Ker.isWeak_of_datum hP.weil) 1 (one_mem _)
      u hu B hIsB
    refine ⟨c, fun _ => ⟨hc1, ?_⟩⟩
    have h1 := hc φ hR.1
    rw [← hfe] at h1
    obtain ⟨-, -, -, -, -, -, -, -, hTh'⟩ := (hfr _ (hON u)).2 _ (hmv u).2
    have h2 := ((hTh' (C.Th (C.xB (C.mvB u B)) φ) φ hR.1).2 rfl).2
    have h3 := (GlobalTheory.T.thetaReading_linear_injective_at_orthonormal_frame D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS _ (hON u)
      _ _ _ _ h2 h2).1 c 0
    rw [zero_smul, zero_smul, add_zero, add_zero] at h3
    rw [h1]
    exact h3
  choose c hc using hc
  by_cases hφ : φ = 0
  · intro u hu
    have := (hc u hu).2
    rw [hφ, smul_zero] at this ⊢
    exact this
  obtain ⟨G, hG⟩ := GlobalTheory.T.inner_thetaFunctions_reading_testFunction_frames D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS
  obtain ⟨K, hK0, hK⟩ := (hG x x hx hx).2.2 φ hR.1 hφ
  obtain ⟨μ, 𝓕, hμ⟩ := (GlobalTheory.Ker.ScalarProduct.ip_basic D V W C).1
  have hmul : ∀ u ∈ GinfC W, ∀ v ∈ GinfC W, c (u * v) = c u * c v := by
    intro u hu v hv
    have h1 := hK _ _ (hON (u * v)) (hON u) _ _ _ _ (hpres _) (hpres _) (hc _ (mul_mem hu hv)).2 (hc u hu).2 μ 𝓕 hμ
    have hR1 : Reads θ V W rfl X bas idx f ((1 : ℂ) • φ) x := by rwa [one_smul]
    have h2 := hK _ _ (hON v) hx _ _ _ _ (hpres _) hf (hc v hv).2 hR1 μ 𝓕 hμ
    have h3 := GlobalTheory.WeilInner.om_inner D ψ V W χV χW om hP.weil μ 𝓕 hμ (1, u) _ _ (hpres v) hf
    have h4 : om (1, u * v) f = om (1, u) (om (1, v) f) := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    rw [h4, h3, h2, frMove_mul θ W X hX, (hG _ _ (hON v) hx).2.1 u, map_one, mul_one] at h1
    have h5 : c v = c (u * v) * conj (c u) :=
      mul_right_cancel₀ (mul_ne_zero hK0 (hG _ _ (hON v) hx).1) h1
    have h6 : c u * conj (c u) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, (hc u hu).1]; simp
    rw [h5]
    linear_combination (-c (u * v)) * h6
  have hmu0 : ∀ u, mu u ≠ 0 := fun u h => by
    have := hmu.norm u
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hcart := (GlobalTheory.FrameCplx.cplx_of_frame D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS x _
    hx hinv).1
  have hone := GlobalTheory.UnitaryChar.char_eq_one D θ W hP.inf _ hcart (fun u => c u / mu u)
    (fun u hu v hv => by
      show c (u * v) / mu (u * v) = c u / mu u * (c v / mu v)
      rw [hmul u hu v hv, muVal_mul hmu, mul_div_mul_comm])
    (fun k hk hks => by
      have h1 := GlobalTheory.T.weilDatum_compact_vacuum_reads_det_character D ψ θ V W χV χW om hP mu hmu W.rank g rfl X bas idx hX hS x _ hx hinv f φ hf hR k hk hks
      have h2 := (GlobalTheory.T.thetaReading_linear_injective_at_orthonormal_frame D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS _ (hON k)
        _ _ _ _ (hc k hk).2 h1).2.1 rfl
      have h3 : c k = mu k := smul_left_injective ℂ hφ h2
      show c k / mu k = 1
      rw [h3, div_self (hmu0 k)])
  intro u hu
  have h : c u = mu u := (div_eq_one_iff_eq (hmu0 u)).1 (hone u hu)
  rw [← h]
  exact (hc u hu).2

end GlobalTheory.RealMove
end

