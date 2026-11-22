import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0030
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0043
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0024
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0046
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0044

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralPowerLineScaling
section
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem lintegral_sq_add_sq_rpow_neg :
    ∀ s : ℝ, 1 / 2 < s → ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ a : ℝ, 0 < a → ∀ m : ℝ,
    ∫⁻ d : ℝ, ENNReal.ofReal ((a ^ 2 + (d - m) ^ 2) ^ (-s)) = C * ENNReal.ofReal (a ^ (1 - 2 * s)) := by
  intro s hs
  have hint : Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-s)) := by
    have h0 := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * s)
      (by simp; linarith)
    have e : -(2 * s) / 2 = -s := by ring
    simpa [Real.norm_eq_abs, sq_abs, e] using h0
  refine ⟨∫⁻ t, ENNReal.ofReal ((1 + t ^ 2) ^ (-s)), hint.lintegral_lt_top.ne, ?_⟩
  intro a ha m
  have hF : Measurable fun d : ℝ => ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s)) := by fun_prop
  rw [lintegral_sub_right_eq_self (fun d : ℝ => ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))) m]
  have hpt : ∀ t : ℝ, ENNReal.ofReal ((a ^ 2 + (a * t) ^ 2) ^ (-s)) =
      ENNReal.ofReal (a ^ ((2 : ℕ) * -s : ℝ)) * ENNReal.ofReal ((1 + t ^ 2) ^ (-s)) := by
    intro t
    rw [← ENNReal.ofReal_mul (by positivity), show a ^ 2 + (a * t) ^ 2 = a ^ 2 * (1 + t ^ 2) by ring,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast a 2,
      ← Real.rpow_mul ha.le]
  have hpow : a ^ (1 - 2 * s) = a * a ^ ((2 : ℕ) * -s : ℝ) := by
    rw [show (1 - 2 * s) = 1 + ((2 : ℕ) * -s : ℝ) by push_cast; ring, Real.rpow_add ha,
      Real.rpow_one]
  calc ∫⁻ d, ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))
      = ∫⁻ d, ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))
          ∂(ENNReal.ofReal |a| • Measure.map (a * ·) volume) := by
        rw [Real.smul_map_volume_mul_left ha.ne']
    _ = ENNReal.ofReal |a| * ∫⁻ t, ENNReal.ofReal ((a ^ 2 + (a * t) ^ 2) ^ (-s)) := by
        rw [lintegral_smul_measure, lintegral_map hF (measurable_const_mul a), smul_eq_mul]
    _ = ENNReal.ofReal a * (ENNReal.ofReal (a ^ ((2 : ℕ) * -s : ℝ)) *
          ∫⁻ t, ENNReal.ofReal ((1 + t ^ 2) ^ (-s))) := by
        rw [abs_of_pos ha]
        simp_rw [hpt]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul ha.le, ← hpow, mul_comm]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFiniteAlgebraJacobsonRadical
section
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LocalFinite

theorem map_maximalIdeal_le_jacobson_and_pow_le :
    ∀ (O R : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Module.Finite O R],
      Ideal.map (algebraMap O R) (IsLocalRing.maximalIdeal O) ≤ (⊥ : Ideal R).jacobson ∧
        ∃ N : ℕ, (⊥ : Ideal R).jacobson ^ N ≤
          Ideal.map (algebraMap O R) (IsLocalRing.maximalIdeal O) := by
  intro O R _ _ _ _ _
  haveI : Algebra.IsIntegral O R := Algebra.IsIntegral.of_finite O R
  set m := IsLocalRing.maximalIdeal O with hm
  set I : Ideal R := Ideal.map (algebraMap O R) m with hI
  refine ⟨?_, ?_⟩
  · refine le_sInf ?_
    rintro M ⟨-, hM⟩
    refine Ideal.map_le_iff_le_comap.mpr ?_
    haveI : (Ideal.comap (algebraMap O R) M).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    exact (IsLocalRing.eq_maximalIdeal this).ge
  · have hle : m ≤ Ideal.comap (algebraMap O R) I := Ideal.le_comap_map
    let f : (O ⧸ m) →+* (R ⧸ I) := Ideal.quotientMap I (algebraMap O R) hle
    letI : Field (O ⧸ m) := Ideal.Quotient.field m
    letI : Algebra (O ⧸ m) (R ⧸ I) := f.toAlgebra
    have hcomp : (f.comp (Ideal.Quotient.mk m)).Finite := by
      have h1 : (algebraMap O R).Finite := RingHom.finite_algebraMap.mpr inferInstance
      have h2 : (Ideal.Quotient.mk I).Finite :=
        RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective
      have h3 : f.comp (Ideal.Quotient.mk m) = (Ideal.Quotient.mk I).comp (algebraMap O R) := by
        ext x; simp [f]
      rw [h3]
      exact h2.comp h1
    have hf : f.Finite := RingHom.Finite.of_comp_finite hcomp
    haveI : Module.Finite (O ⧸ m) (R ⧸ I) := hf
    haveI : IsArtinianRing (R ⧸ I) := IsArtinianRing.of_finite (O ⧸ m) (R ⧸ I)
    obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R ⧸ I)
    refine ⟨N, ?_⟩
    have hmap : Ideal.map (Ideal.Quotient.mk I) (⊥ : Ideal R).jacobson ≤
        (⊥ : Ideal (R ⧸ I)).jacobson := by
      refine le_sInf ?_
      rintro P ⟨-, hP⟩
      refine Ideal.map_le_iff_le_comap.mpr ?_
      haveI : (Ideal.comap (Ideal.Quotient.mk I) P).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      exact sInf_le ⟨bot_le, this⟩
    have hz : Ideal.map (Ideal.Quotient.mk I) ((⊥ : Ideal R).jacobson ^ N) = ⊥ := by
      rw [Ideal.map_pow]
      exact le_bot_iff.mp ((Ideal.pow_right_mono hmap N).trans hN.le)
    intro x hx
    have : Ideal.Quotient.mk I x = 0 := by
      have := Ideal.mem_map_of_mem (Ideal.Quotient.mk I) hx
      rw [hz] at this
      simpa using this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this

end GlobalTheory.CompanionTheory.LocalFinite
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalizationPreservesClosednessStatement
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_preserves_closedness : ∀ {S : Type} [CommRing S] (ϖ : S), (Val ϖ → Loc S ∧ Loc (Localization.Away ϖ)) ∧ (Aic S → Aic (Localization.Away ϖ)) := by
  first | exact @GlobalTheory.CompanionTheory.LocAic.main | exact GlobalTheory.CompanionTheory.LocAic.main | (intros; apply GlobalTheory.CompanionTheory.LocAic.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeetOverHypersurfaceOfGerm
section
namespace GlobalTheory.CompanionTheory.ComplexSets

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter

theorem exists_hypersurface_of_monic_relation {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {w : σ → ℂ} {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (hirr : GermIrreducibleAt Y w) {φ : (σ → ℂ) → ℂ}
    (hφ : AnalyticAt ℂ φ w) (hnv : ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → φ z = 0) :
    ∀ (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (a j) (A w)) →
      (∀ᶠ z in 𝓝 w, z ∈ Y → φ z ^ N + ∑ j, a j (A z) * φ z ^ (j : ℕ) = 0) →
      ∃ e : (Fin d → ℂ) → ℂ, AnalyticAt ℂ e (A w) ∧ (¬ ∀ᶠ y in 𝓝 (A w), e y = 0) ∧
        ∀ᶠ z in 𝓝 w, z ∈ Y → φ z = 0 → e (A z) = 0 := by
  intro N
  induction N with
  | zero =>
    intro a _ hrel
    exfalso
    have := hrel.self_of_nhds hirr.1
    simp at this
  | succ n ih =>
    intro a ha hrel
    by_cases h0 : ∀ᶠ y in 𝓝 (A w), a 0 y = 0
    · have h0' : ∀ᶠ z in 𝓝 w, a 0 (A z) = 0 := (A.continuous.tendsto w).eventually h0
      have hQ : AnalyticAt ℂ (fun z => φ z ^ n + ∑ j : Fin n, a j.succ (A z) * φ z ^ (j : ℕ)) w := by
        refine (hφ.pow n).add ?_
        refine Finset.analyticAt_fun_sum _ fun j _ => ?_
        have hc : AnalyticAt ℂ (fun z => a j.succ (A z)) w :=
          AnalyticAt.comp' (ha j.succ) (A.analyticAt w)
        exact hc.mul (hφ.pow _)
      have hprod : ∀ᶠ z in 𝓝 w, z ∈ Y →
          φ z * (φ z ^ n + ∑ j : Fin n, a j.succ (A z) * φ z ^ (j : ℕ)) = 0 := by
        filter_upwards [hrel, h0'] with z hz hz0 hzY
        have h := hz hzY
        rw [Fin.sum_univ_succ] at h
        simp only [Fin.val_zero, pow_zero, mul_one, hz0, zero_add, Fin.val_succ] at h
        rw [← h, mul_add, Finset.mul_sum, pow_succ']
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rcases hirr.2 φ _ hφ hQ hprod with h | h
      · exact absurd h hnv
      · exact ih (fun j => a j.succ) (fun j => ha j.succ) h
    · refine ⟨a 0, ha 0, h0, ?_⟩
      filter_upwards [hrel] with z hz hzY hφ0
      have h := hz hzY
      rw [Fin.sum_univ_succ] at h
      simpa [hφ0] using h

theorem irreducibleGermMeetOverHypersurface_of_finiteFibreGermIntegral
    (H : FiniteFibreGermIntegral.Statement) : IrreducibleGermMeetOverHypersurface.Statement := by
  intro σ _ Y Z w d A hY hirr hfib hZ hnot
  obtain ⟨N₀, k, f, hN₀, hwN₀, hf, hZN⟩ := hZ
  have hex : ∃ m, ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → f m z = 0 := by
    by_contra hcon
    push_neg at hcon
    apply hnot
    filter_upwards [eventually_all.2 hcon, hN₀.mem_nhds hwN₀] with z hz hzN hzY
    have hmem : z ∈ {z | z ∈ N₀ ∧ ∀ i, f i z = 0} := ⟨hzN, fun i => hz i hzY⟩
    rw [← hZN] at hmem
    exact hmem.1
  obtain ⟨m, hm⟩ := hex
  have hφ : AnalyticAt ℂ (f m) w := hf m w hwN₀
  obtain ⟨N, a, ha, hrel⟩ := H σ Y w d A hY hfib (f m) hφ
  obtain ⟨e, he, hne, hz⟩ := exists_hypersurface_of_monic_relation A hirr hφ hm N a ha hrel
  refine ⟨e, he, hne, ?_⟩
  filter_upwards [hz, hN₀.mem_nhds hwN₀] with z hz' hzN hzY hzZ
  have hmem : z ∈ Z ∩ N₀ := ⟨hzZ, hzN⟩
  rw [hZN] at hmem
  exact hz' hzY (hmem.2 m)

end GlobalTheory.CompanionTheory.ComplexSets
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIdempotentComplementIffStatement
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_idempotent_complement_iff : ∀ {S : Type} [CommRing S] (P : Ideal S), P.IsPrime → ∀ x : S, x ∈ compI P ↔ ∃ e, IsIdempotentElem e ∧ e ∉ P ∧ e * x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff | exact GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff | (intros; apply GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialCoefficientComparisonStatement
section
open Finset GlobalTheory.CompanionTheory.CoefId
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomial_coefficient_comparison : ∀ {n : ℕ} {ι κ : Type} (I : Finset ι) (J : Finset κ) (f : ι → ℂ) (g : κ → ℂ) (e : ι → Fin n → ℤ) (e' : κ → Fin n → ℤ), (∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → Function.Injective (fun a => z a ^ 2) → ∑ i ∈ I, f i * mon (e i) z = ∑ j ∈ J, g j * mon (e' j) z) → ∀ m : Fin n → ℤ, ∑ i ∈ I.filter (fun i => e i = m), f i = ∑ j ∈ J.filter (fun j => e' j = m), g j := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.laurent_indep_torus | exact GlobalTheory.CompanionTheory.CoefId.laurent_indep_torus | (intros; apply GlobalTheory.CompanionTheory.CoefId.laurent_indep_torus <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqZeroOfCPowMemSpan
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem mul_eq_zero_of_C_pow_mem_span (K : Type) [CommRing K]
    (hred : ∀ (x : K) (n : ℕ), x ^ n = 0 → x = 0) (f g a : K) (n : ℕ)
    (h : (Polynomial.C a) ^ n ∈
      Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) : g * a = 0 := by
  let L := Localization.Away g
  let u : L := IsLocalization.Away.invSelf g
  have hu : algebraMap K L g * u = 1 := IsLocalization.Away.mul_invSelf g
  let φ : Polynomial K →+* L := Polynomial.eval₂RingHom (algebraMap K L) (u * algebraMap K L f)
  have h0 : φ (Polynomial.C f - Polynomial.X * Polynomial.C g) = 0 := by
    have e1 : φ (Polynomial.C f) = algebraMap K L f := by simp [φ]
    have e2 : φ Polynomial.X = u * algebraMap K L f := by simp [φ]
    have e3 : φ (Polynomial.C g) = algebraMap K L g := by simp [φ]
    rw [map_sub, map_mul, e1, e2, e3]
    linear_combination (-(algebraMap K L f)) * hu
  have h1 : φ ((Polynomial.C a) ^ n) = 0 := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
    rw [← hc, map_mul, h0, mul_zero]
  have h2 : algebraMap K L (a ^ n) = 0 := by
    have e : φ ((Polynomial.C a) ^ n) = algebraMap K L (a ^ n) := by simp [φ]
    rw [← e, h1]
  obtain ⟨⟨m, hm⟩, e⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) L _).1 h2
  obtain ⟨M, rfl⟩ := hm
  have e' : g ^ M * a ^ n = 0 := e
  apply hred _ (M + n)
  calc (g * a) ^ (M + n) = g ^ n * a ^ M * (g ^ M * a ^ n) := by ring
    _ = 0 := by rw [e', mul_zero]

theorem b_inj : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (K₁ : Type) [CommRing K₁]
    (K₂ : Type) [CommRing K₂] (f g : K) (i₁ : Polynomial K →+* K₁) (i₂ : Polynomial K →+* K₂)
    (r : ℕ → K) (N : ℕ), Pf p K → IsRt p r → r 0 ^ N ∈ Ideal.span {f, g} →
    PQ p i₁ (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) →
    PQ p i₂ (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) →
    ∀ a : K, i₁ (Polynomial.C a) = 0 → i₂ (Polynomial.C a) = 0 → ∀ k, r k * a = 0 := by
  intro p _ K _ K₁ _ K₂ _ f g i₁ i₂ r N hK hr hN h₁ h₂ a ha₁ ha₂
  obtain ⟨-, hred, -, -, hroots⟩ := pf_facts p K hK
  obtain ⟨k₁, hk₁⟩ := (h₁.ker _).1 ha₁
  obtain ⟨k₂, hk₂⟩ := (h₂.ker _).1 ha₂
  have hg : g * a = 0 := mul_eq_zero_of_C_pow_mem_span K hred f g a _ hk₁
  have hf : f * a = 0 := mul_eq_zero_of_C_pow_mem_span K hred g f a _ hk₂
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hN
  have h0 : r 0 ^ N * a = 0 := by
    rw [← huv]
    linear_combination u * hf + v * hg
  exact (hroots r hr).2.2 N a h0

end GlobalTheory.CompanionTheory.PerfectRing
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityFinitePlacesStatement
section
open Matrix PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicativity_finite_places : MulF := by
  first | exact @GlobalTheory.CompanionTheory.WedgeMinor.mulF | exact GlobalTheory.CompanionTheory.WedgeMinor.mulF | (intros; apply GlobalTheory.CompanionTheory.WedgeMinor.mulF <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityInfinitePlacesStatement
section
open Matrix PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicativity_infinite_places : DetMono → MulI := by
  first | exact @GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono | exact GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono | (intros; apply GlobalTheory.CompanionTheory.GramWedge.mulI_of_detMono <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatCardDualEq
section
namespace GlobalTheory.CompanionTheory.ZModDual

theorem nat_card_dual_eq : ∀ (n : ℕ) [NeZero n] (N : Type) [AddCommGroup N] [Module (ZMod n) N] [Finite N],
    Nat.card (Module.Dual (ZMod n) N) = Nat.card N := by
  intro n _ N _ _ _
  exact GlobalTheory.ZModDual.card_dual_eq n N

end GlobalTheory.CompanionTheory.ZModDual
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewtonPolygonSlopeExistenceStatement
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newton_polygon_slope_existence : ∀ {S : Type} [CommRing S] (ϖ : S), Dich ϖ → Roots ϖ → ∀ (q : ℕ → S) (d M : ℕ), 0 < d → q d = 1 → q 0 ∣ ϖ ^ M → ∃ c : S, (∀ i, 1 ≤ i → i ≤ d → q 0 ∣ q i * c ^ i) ∧ ∃ i, 1 ≤ i ∧ i ≤ d ∧ q i * c ^ i ∣ q 0 := by
  first | exact @GlobalTheory.CompanionTheory.NewtonSlope.first_slope | exact GlobalTheory.CompanionTheory.NewtonSlope.first_slope | (intros; apply GlobalTheory.CompanionTheory.NewtonSlope.first_slope <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NoetherNormalizationHomogeneousStatement
section
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noether_normalization_homogeneous : ∀ (K : Type) [Field K] [Infinite K] (N : ℕ) (I : Ideal (MvPolynomial (Fin (N + 1)) K)), I ≠ ⊤ → (∀ f ∈ I, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ I) → ∃ (e m : ℕ) (y : Fin m → MvPolynomial (Fin (N + 1)) K), 0 < e ∧ (∀ i, (y i).IsHomogeneous e) ∧ AlgebraicIndependent K (fun i => Ideal.Quotient.mk I (y i)) ∧ Module.Finite (Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (y i))) (MvPolynomial (Fin (N + 1)) K ⧸ I) := by
  first | exact @GlobalTheory.CompanionTheory.ConeNoether.main | exact GlobalTheory.CompanionTheory.ConeNoether.main | (intros; apply GlobalTheory.CompanionTheory.ConeNoether.main <;> assumption)
end

