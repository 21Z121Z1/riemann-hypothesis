import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0667
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0663
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0664
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0666
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0675
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartHasPeriodLinearIntegral
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem lift_topNil {p : ℕ} [Fact p.Prime] {O B Q : Type} [CommRing O] [CommRing B] [CommRing Q]
    [Algebra B Q] {θ : B →+* O} (hF : IsFrame p Q θ) {G : PDivGroup p O} {d : ℕ} (c : Chart G d)
    (t : G.Tate) (n : ℕ) (z : Fin d → B) (hz : ∀ i, θ (z i) = t.pt n (c.x n i)) :
    ∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N := by
  intro i
  obtain ⟨N, a, ha⟩ := c.nil n i
  obtain ⟨a', ha'⟩ := hF.surj (t.pt n a)
  have hw : θ (z i ^ N - p * a') = 0 := by
    rw [map_sub, map_pow, hz, map_mul, map_natCast, ha', ← map_pow, ha, map_mul, map_natCast, sub_self]
  obtain ⟨w, -, hw'⟩ := hF.pd _ hw
  refine ⟨N * p, ?_⟩
  have h1 : (p : B) * a' ∣ (z i ^ N) ^ p - (z i ^ N - p * a') ^ p := by
    have := sub_dvd_pow_sub_pow (z i ^ N) (z i ^ N - p * a') p
    simpa using this
  rw [pow_mul]
  have h2 : (p : B) ∣ (z i ^ N) ^ p - (z i ^ N - p * a') ^ p := dvd_trans (dvd_mul_right _ _) h1
  have h3 : (p : B) ∣ (z i ^ N - p * a') ^ p := hw' ▸ dvd_mul_right _ _
  have := dvd_add h2 h3
  simpa using this

end GlobalTheory.QLog

namespace GlobalTheory.QLog

theorem val_integral {p : ℕ} {σ B Q : Type} [Fintype σ] [DecidableEq σ] [CommRing B] [CommRing Q]
    [Algebra B Q] (z : σ → B) (s : MvPowerSeries σ B) (q : Q)
    (h : HasVal p z (map (algebraMap B Q) s) q) : ∃ b : B, q = algebraMap B Q b := by
  obtain ⟨N, hN⟩ := h 0
  obtain ⟨b, hb⟩ := hN N le_rfl
  have hE : (MvPolynomial.eval fun i => algebraMap B Q (z i))
      (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => N) (map (algebraMap B Q) s)) =
      algebraMap B Q (MvPolynomial.eval z (trunc' B (Finsupp.equivFunOnFinite.symm fun _ => N) s)) := by
    rw [trunc'_map, MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
      MvPolynomial.eval₂_comp_left]
    rfl
  refine ⟨MvPolynomial.eval z (trunc' B (Finsupp.equivFunOnFinite.symm fun _ => N) s) + b, ?_⟩
  rw [hE, pow_zero, one_mul, sub_eq_iff_eq_add'] at hb
  rw [hb, map_add]

end GlobalTheory.QLog

namespace GlobalTheory.QLog

theorem hasPeriod_add_smul {p : ℕ} [Fact p.Prime] {O B Q : Type} [CommRing O] [CommRing B]
    [CommRing Q] [Algebra B Q] {θ : B →+* O} (hF : IsFrame p Q θ) {G : PDivGroup p O} {d : ℕ}
    (c : Chart G d) (t : G.Tate) {f g : MvPowerSeries (Fin d) Q} {y y' : B} (b : B)
    (hf : c.HasPeriod θ t f y) (hg : c.HasPeriod θ t g y') :
    c.HasPeriod θ t (f + algebraMap B Q b • g) (y + b * y') := by
  rw [c.hasPeriod_iff hF] at hf hg ⊢
  intro n z hz
  obtain ⟨q, hq, b1, hb1⟩ := hf n z hz
  obtain ⟨r, hr, b2, hb2⟩ := hg n z hz
  have h1 := (GlobalTheory.QLog.ValLin.hasVal_add_smul_map p B O Q θ hF (Fin d) z g g r r hr).2.1 (algebraMap B Q b)
  have h2 := (GlobalTheory.QLog.ValLin.hasVal_add_smul_map p B O Q θ hF (Fin d) z _ _ q _ hq).1 h1
  refine ⟨_, h2, b1 + b * b2, ?_⟩
  have e : (p : Q) ^ n * (q + algebraMap B Q b * r) =
      (p : Q) ^ n * q + algebraMap B Q b * ((p : Q) ^ n * r) := by ring
  rw [e, hb1, hb2, ← map_mul, ← map_add]
  congr 1
  ring

theorem hasPeriod_integral {p : ℕ} [Fact p.Prime] {O B Q : Type} [CommRing O] [CommRing B]
    [CommRing Q] [Algebra B Q] {θ : B →+* O} (hF : IsFrame p Q θ) {G : PDivGroup p O} {d : ℕ}
    (c : Chart G d) (t : G.Tate) (s : MvPowerSeries (Fin d) B) :
    c.HasPeriod θ t (map (algebraMap B Q) s) 0 := by
  rw [c.hasPeriod_iff hF]
  intro n z hz
  have hD : DIn (⊤ : Ideal B) (map (algebraMap B Q) s) := fun α i =>
    ⟨(α i : B) * coeff α s, trivial, by rw [coeff_map, map_mul, map_natCast]⟩
  obtain ⟨q, hq, -⟩ := GlobalTheory.QLog.existsUnique_hasVal_of_dIn p B O Q θ hF (Fin d) z (lift_topNil hF c t n z hz) _ hD
  obtain ⟨e, he⟩ := val_integral z s q hq
  exact ⟨q, hq, e, by rw [he, zero_add, map_mul, map_pow, map_natCast]⟩

open MvPowerSeries in
private lemma exists_pow_dvd_of_theta_eq_of_isFrame {p : ℕ} {B O Q : Type} [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] {θ : B →+* O} (hθ : _root_.GlobalTheory.QLog.IsFrame p Q θ)
    {z : B} {a : O} (hza : θ z = a) {N : ℕ} (ha : (p : O) ∣ a ^ N) :
    ∃ M, (p : B) ∣ z ^ M := by
  obtain ⟨w, hw⟩ := ha
  obtain ⟨b, hb⟩ := hθ.surj w
  obtain ⟨y, -, hy⟩ := hθ.pd (z ^ N - p * b)
    (by simp [hza, hb, hw])
  refine ⟨N * p, ?_⟩
  have h1 : (p : B) ∣ (z ^ N) ^ p - (z ^ N - p * b) ^ p :=
    (dvd_mul_right (p : B) b).trans (by simpa using sub_dvd_pow_sub_pow (z ^ N) (z ^ N - p * b) p)
  have h2 : (z ^ N) ^ p = ((z ^ N) ^ p - (z ^ N - p * b) ^ p) + p * y := by rw [← hy]; ring
  rw [pow_mul, h2]
  exact dvd_add h1 (dvd_mul_right _ _)

open MvPowerSeries in
private lemma eval_algebraMap_trunc'_map_eq_algebraMap_eval {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]
    {d : ℕ} (s : MvPowerSeries (Fin d) B) (z : Fin d → B) (N : ℕ) :
    MvPolynomial.eval (fun i ↦ algebraMap B Q (z i))
        (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ ↦ N) (map (algebraMap B Q) s)) =
      algebraMap B Q (MvPolynomial.eval z (trunc' B (Finsupp.equivFunOnFinite.symm fun _ ↦ N) s)) := by
  rw [MvPowerSeries.trunc'_map, MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_comp_left, RingHom.comp_id]
  rfl

open MvPowerSeries in

theorem _root_.GlobalTheory.QLog.hasPeriod_linear : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : _root_.GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), ∀ F : _root_.GlobalTheory.QLog.BFrame ε, ∀ (G : _root_.GlobalTheory.PDivGroup p O) (d : ℕ) (c : _root_.GlobalTheory.QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), _root_.GlobalTheory.QLog.IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (f g : MvPowerSeries (Fin d) F.Q) (t : G.Tate) (y y' b : F.B), c.HasPeriod F.θ t f y → c.HasPeriod F.θ t g y' → c.HasPeriod F.θ t (f + algebraMap F.B F.Q b • g) (y + b * y') ∧ (∀ s : MvPowerSeries (Fin d) F.B, constantCoeff s = 0 → c.HasPeriod F.θ t (map (algebraMap F.B F.Q) s) 0) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F G d c μ' _ _ f g t y y' b hf hg
  have hF := F.frame
  rw [c.hasPeriod_iff hF] at hf hg
  refine ⟨?_, ?_⟩
  · rw [c.hasPeriod_iff hF]
    intro n z hz
    obtain ⟨q, hq, b₁, hb₁⟩ := hf n z hz
    obtain ⟨r, hr, b₂, hb₂⟩ := hg n z hz
    have hbr := (_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p _ O _ F.θ hF (Fin d) z g f
      r q hr).2.1 (algebraMap _ _ b)
    refine ⟨q + algebraMap _ _ b * r,
      (_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p _ O _ F.θ hF (Fin d) z f _ q _
        hq).1 hbr, b₁ + b * b₂, ?_⟩
    simp only [map_add, map_mul, map_pow, map_natCast] at hb₁ hb₂ ⊢
    linear_combination hb₁ + algebraMap _ _ b * hb₂
  · intro s _
    rw [c.hasPeriod_iff hF]
    intro n z hz
    have hz' : ∀ i, ∃ M, (p : F.B) ∣ z i ^ M := fun i => by
      obtain ⟨N, hN⟩ := c.nil n i
      refine exists_pow_dvd_of_theta_eq_of_isFrame hF (hz i) (N := N) ?_
      simpa [map_pow, map_natCast] using map_dvd (t.pt n) hN
    have hd : _root_.GlobalTheory.QLog.DIn (⊤ : Ideal F.B)
        (map (algebraMap F.B F.Q) s) := by
      intro α i
      exact ⟨(α i : F.B) * coeff α s, Submodule.mem_top, by simp⟩
    obtain ⟨q, hq, -⟩ := _root_.GlobalTheory.QLog.existsUnique_hasVal_of_dIn p _ O _
      F.θ hF (Fin d) z hz' _ hd
    have hq' := hq
    unfold _root_.GlobalTheory.QLog.HasVal at hq'
    obtain ⟨N, hN⟩ := hq' 0
    obtain ⟨e, he⟩ := hN N le_rfl
    refine ⟨q, hq, MvPolynomial.eval z
      (trunc' F.B (Finsupp.equivFunOnFinite.symm fun _ ↦ N) s) + e, ?_⟩
    rw [eval_algebraMap_trunc'_map_eq_algebraMap_eval, pow_zero, one_mul] at he
    have hq2 : q = algebraMap _ F.Q (MvPolynomial.eval z
        (trunc' F.B (Finsupp.equivFunOnFinite.symm fun _ ↦ N) s) + e) := by
      rw [map_add, ← he]
      ring
    rw [hq2, zero_add, map_mul, map_pow, map_natCast]

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundarySwapSubRulesStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupLawCoboundary_swap_sub_rules : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (c c' : MvPowerSeries (Fin d ⊕ Fin d) R) (f f' : MvPowerSeries (Fin d) R), cob2 μ (c - c') = cob2 μ c - cob2 μ c' ∧ swap (c - c') = swap c - swap c' ∧ cob1 μ (f - f') = cob1 μ f - cob1 μ f' := by
  first | exact @GlobalTheory.CobLin.sub_rules | exact GlobalTheory.CobLin.sub_rules | (intros; apply GlobalTheory.CobLin.sub_rules <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOneFractionStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cob2_cob1_eq_zero_of_isLaw : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLaw μ → ∀ g : MvPowerSeries (Fin d) Q, cob2 (up Q μ) (cob1 (up Q μ) g) = 0 := by
  first | exact @GlobalTheory.formalGroupLawCoboundaryTwo_coboundaryOne_fractions | exact GlobalTheory.formalGroupLawCoboundaryTwo_coboundaryOne_fractions | (intros; apply GlobalTheory.formalGroupLawCoboundaryTwo_coboundaryOne_fractions <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawPointsCommMonoidSubstHomStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupLaw_points_commMonoid_subst_hom : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ (τ : Type) [Finite τ] (u v w : Fin d → MvPowerSeries τ R), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i, constantCoeff (w i) = 0) → (∀ i, constantCoeff (op μ u v i) = 0) ∧ op μ (op μ u v) w = op μ u (op μ v w) ∧ op μ u v = op μ v u ∧ op μ u (fun _ => 0) = u ∧ ∀ (τ' : Type) (a : τ → MvPowerSeries τ' R), (∀ t, constantCoeff (a t) = 0) → ∀ i, subst a (op μ u v i) = op μ (fun j => subst a (u j)) (fun j => subst a (v j)) i := by
  first | exact @GlobalTheory.Katz.LawMonoid.mon | exact GlobalTheory.Katz.LawMonoid.mon | (intros; apply GlobalTheory.Katz.LawMonoid.mon <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalLogCoeffMemOfSubOneMemDp
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
  GlobalTheory.FormalCalc

namespace GlobalTheory.DPLog

theorem finsum_mem_addSubmonoid {M ι : Type*} [AddCommMonoid M] (S : AddSubmonoid M)
    {f : ι → M} (hf : ∀ i, f i ∈ S) : ∑ᶠ i, f i ∈ S := by
  classical
  by_cases h : (Function.support f).Finite
  · rw [finsum_eq_sum f h]; exact S.sum_mem fun i _ => hf i
  · rw [finsum_of_infinite_support h]; exact S.zero_mem

theorem formalLog_in_of_sub_one_mem : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B]
    [CommRing Q] [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ →
    ∀ J : Ideal B, (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (σ : Type) (h : MvPowerSeries σ B),
    constantCoeff h = 1 → (∀ α, coeff α (h - 1) ∈ J) →
    In J (formalLog (map (algebraMap B Q) h)) := by
  intro p _ B O Q _ _ _ _ _ θ hF J hJ σ h h1 hJh
  let S : AddSubmonoid Q := J.toAddSubmonoid.map (algebraMap B Q).toAddMonoidHom
  have hS : ∀ q, q ∈ S ↔ ∃ b ∈ J, q = algebraMap B Q b := fun q =>
    AddSubmonoid.mem_map.trans
      ⟨fun ⟨b, hb, e⟩ => ⟨b, hb, e.symm⟩, fun ⟨b, hb, e⟩ => ⟨b, hb, e.symm⟩⟩
  have hww : map (algebraMap B Q) h - 1 = map (algebraMap B Q) (h - 1) := by
    rw [map_sub, map_one]
  have hsub : PowerSeries.HasSubst (map (algebraMap B Q) h - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp [h1])
  intro α
  refine (hS _).1 ?_
  rw [formalLog, PowerSeries.coeff_subst hsub]
  refine finsum_mem_addSubmonoid S fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [S.zero_mem]
  obtain ⟨y, hy, hwy⟩ :=
    DPSeries.pow_eq_factorial_mul p B O Q θ hF J hJ σ (h - 1) hJh d hd
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  refine (hS _).2 ⟨((-1 : B) ^ (k + 2) * (k.factorial : B)) * coeff α y,
    J.mul_mem_left _ (hy α), ?_⟩
  rw [hww, ← map_pow, hwy, coeff_map, ← map_natCast (C (σ := σ) (R := B)), coeff_C_mul,
    PowerSeries.coeff_log, if_neg (Nat.succ_ne_zero k), smul_eq_mul]
  have e : algebraMap ℚ Q ((k + 1 : ℕ) : ℚ)⁻¹ * ((k + 1 : ℕ) : Q) = 1 := by
    rw [← map_natCast (algebraMap ℚ Q), ← map_mul, inv_mul_cancel₀ (by positivity), map_one]
  rw [div_eq_mul_inv, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_neg, map_neg,
    map_one, map_one, map_natCast, map_natCast, Nat.factorial_succ, Nat.cast_mul]
  linear_combination ((-1 : Q) ^ (k + 2) * (k.factorial : Q) * algebraMap B Q (coeff α y)) * e

end GlobalTheory.DPLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameWeightLeviStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviAt_log_nsq_ratio_eq_leviAt_ph : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E : La) (U : Set Y) (β J : ι → Y → ℂ), IsOpen U → A.IsFrameOn (A.kap + E) U β → A.IsFrameOn A.kap U J → ∀ x ∈ U, ∀ i, x ∈ (A.chart i).source → ContDiffAt ℝ ∞ ((fun y => -Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap J y)) ∘ (A.chart i).symm) (A.chart i x) ∧ ∀ f : Y → ℝ, ContDiffAt ℝ ∞ (f ∘ (A.chart i).symm) (A.chart i x) → ∀ ξ : Fin n → ℂ, A.leviAt i (fun y => (-Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap J y)) + f y) x ξ = A.leviAt i (fun y => A.ph E i y + f y) x ξ := by
  first | exact @GlobalTheory.frameWeight_levi | exact GlobalTheory.frameWeight_levi | (intros; apply GlobalTheory.frameWeight_levi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobXiEigenvectorEqOfFrameImageEq
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WinLift

theorem eigen_eq_of_frame_eq : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ x y : Ainf p O, WittVector.frobenius x = WittVector.frobenius (xi ε) * x → WittVector.frobenius y = WittVector.frobenius (xi ε) * y → F.a x = F.a y → x = y := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F x y hx hy hxy
  have hsub : WittVector.frobenius (x - y) = WittVector.frobenius (xi ε) * (x - y) := by
    rw [map_sub, hx, hy, mul_sub]
  obtain ⟨c, hc, -⟩ := GlobalTheory.PDivLat.existsUnique_padic_of_eigen p C v O hv ε hε (x - y) hsub
  have h0 : F.a (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  rw [← hc, map_mul, ← F.p_τ] at h0
  have h1 : F.τ * F.a (ofPadic p O c) = 0 := by
    apply tf F
    rw [← h0]; ring
  have h2 : Sandwich.mu ε ∣ ofPadic p O c := (F.τ_mul _).1 h1
  have h3 : WittVector.fontaineTheta O p (ofPadic p O c) = 0 := by
    obtain ⟨w, hw⟩ := h2
    rw [hw, map_mul, theta_mu hv hε, zero_mul]
  have hc0 : c = 0 := by
    by_contra hne
    have hs := PadicInt.unitCoeff_spec hne
    rw [hs, map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast] at h3
    have hp : (p : O) ≠ 0 := by
      intro h
      have := congrArg (algebraMap O C) h
      rw [map_natCast, map_zero] at this
      exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) this
    have hu : IsUnit (WittVector.fontaineTheta O p (ofPadic p O (PadicInt.unitCoeff hne : ℤ_[p]))) :=
      ((PadicInt.unitCoeff hne).isUnit.map (ofPadic p O)).map _
    rcases mul_eq_zero.1 h3 with h | h
    · exact hu.ne_zero h
    · exact hp (pow_eq_zero_iff'.1 h).1
  rw [← sub_eq_zero, ← hc, hc0, map_zero, zero_mul]

end GlobalTheory.WinLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusCongruenceCombinationOverIntegers
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.SmallSecond.ToO

theorem frob_eq_expand {Q τ : Type} [CommRing Q] (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q)
    (f : MvPowerSeries τ Q) : frob p s f = expand p hp (map s f) := by
  rw [frob, expand, substAlgHom_apply]

theorem coeff_frob_smul {Q τ : Type} [CommRing Q] (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q)
    (f : MvPowerSeries τ Q) (β : τ →₀ ℕ) : coeff (p • β) (frob p s f) = s (coeff β f) := by
  rw [frob_eq_expand p hp, coeff_expand_smul, coeff_map]

theorem coeff_frob_of_not_dvd {Q τ : Type} [CommRing Q] (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q)
    (f : MvPowerSeries τ Q) {α : τ →₀ ℕ} {i : τ} (h : ¬ p ∣ α i) : coeff α (frob p s f) = 0 := by
  rw [frob_eq_expand p hp]
  exact coeff_expand_of_not_dvd p hp _ h

theorem formalGroupLawCoboundaryOne_sub {Q : Type} [CommRing Q] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) Q}
    (h : ∀ i, constantCoeff (μ i) = 0) (f g : MvPowerSeries (Fin d) Q) :
    cob1 μ (f - g) = cob1 μ f - cob1 μ g := by
  have := formalCoboundary_add h (f - g) g
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

theorem formalGroupLawCoboundaryOne_finset_sum {Q : Type} [CommRing Q] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) Q}
    (h : ∀ i, constantCoeff (μ i) = 0) {ι : Type} (S : Finset ι) (f : ι → MvPowerSeries (Fin d) Q) :
    cob1 μ (∑ i ∈ S, f i) = ∑ i ∈ S, cob1 μ (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have := formalCoboundary_smul h 0 0
    simpa using this
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, formalCoboundary_add h, ih]

end GlobalTheory.SmallSecond.ToO

open GlobalTheory.SmallSecond.ToO in

theorem GlobalTheory.SmallSecond.frob_congr_to_O : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (F : BFrame ε) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), (∀ i, QL μ' ⊤ (e i)) → ∀ (W : Fin d ⊕ Fin k → F.B) (b : Fin k → F.B), (∀ l, ¬IsUnit (F.θ (W l))) → In (⊤ : Ideal F.B) (frob p F.s (comb (Sum.elim (fun _ => 0) b) e) - comb W e) → In (Ideal.span {(p : F.B)}) (cob1 (up F.Q μ') (frob p F.s (comb (Sum.elim (fun _ => 0) b) e)) - frob p F.s (cob1 (up F.Q μ') (comb (Sum.elim (fun _ => 0) b) e))) → ∃ (F₁ : MvPowerSeries (Fin d ⊕ Fin d) F.B) (t : MvPowerSeries (Fin d) O), map (algebraMap F.B F.Q) F₁ = cob1 (up F.Q μ') (comb (Sum.elim (fun _ => 0) b) e) ∧ (∀ i, ¬IsUnit (lin t i)) ∧ (∀ β : Fin d ⊕ Fin d →₀ ℕ, ¬IsUnit (coeff (p • β) (cob1 μ t) - F.θ (coeff β F₁) ^ p)) ∧ ∀ α : Fin d ⊕ Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α (cob1 μ t)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε F d μ μ' hlift hmap k e he W b hW hT hC
  classical
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : IsLocalRing O := ValuationRing.isLocalRing O
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set m := IsLocalRing.maximalIdeal O with hm
  have memm : ∀ x : O, x ∈ m ↔ ¬IsUnit x := fun x => by
    rw [hm, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hpm : (p : O) ∈ m := (memm _).2 Fact.out
  have hθp : ∀ x : F.B, F.θ ((p : F.B) * x) ∈ m := fun x => by
    rw [map_mul, map_natCast]; exact m.mul_mem_right _ hpm
  have hWm : ∀ l, F.θ (W l) ∈ m := fun l => (memm _).2 (hW l)
  have hμQ : ∀ i, constantCoeff (up F.Q μ' i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hlift.const, map_zero]
  have hcomb : ∀ c : Fin d ⊕ Fin k → F.B, cob1 (up F.Q μ') (comb c e) =
      ∑ l, algebraMap F.B F.Q (c l) • cob1 (up F.Q μ') (e l) := by
    intro c
    unfold comb
    rw [formalGroupLawCoboundaryOne_finset_sum hμQ]
    exact Finset.sum_congr rfl fun l _ => formalCoboundary_smul hμQ _ _
  choose g _ hg using fun l => (he l).2.2
  choose c1 _ hc1 using fun l => (he l).2.1
  have hSm : ∀ α, F.θ (∑ l, W l * g l α) ∈ m := fun α => by
    rw [map_sum]
    exact m.sum_mem fun l _ => by rw [map_mul]; exact m.mul_mem_right _ (hWm l)
  have hF : In (⊤ : Ideal F.B) (cob1 (up F.Q μ') (comb (Sum.elim (fun _ => (0 : F.B)) b) e)) := by
    intro α
    refine ⟨∑ l, Sum.elim (fun _ => (0 : F.B)) b l * g l α, trivial, ?_⟩
    rw [hcomb, map_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [MvPowerSeries.coeff_smul, hg, map_mul]
  obtain ⟨F₁, hF₁⟩ := In.top_iff.1 hF
  obtain ⟨T, hTT⟩ := In.top_iff.1 hT
  have hcobT : ∀ α, coeff α (cob1 μ (map F.θ T)) = F.θ (coeff α (cob1 μ' T)) := by
    intro α
    have hμeq : μ = fun i => map F.θ (μ' i) := funext fun i => (hmap i).symm
    rw [hμeq, ← map_formalGroupLawCoboundaryOne_eq F.θ μ' hlift.const T, coeff_map]
  have hup : map (algebraMap F.B F.Q) (cob1 μ' T) =
      cob1 (up F.Q μ') (frob p F.s (comb (Sum.elim (fun _ => (0 : F.B)) b) e)) -
        ∑ l, algebraMap F.B F.Q (W l) • cob1 (up F.Q μ') (e l) := by
    rw [map_formalGroupLawCoboundaryOne_eq (algebraMap F.B F.Q) μ' hlift.const T]
    change cob1 (up F.Q μ') (map (algebraMap F.B F.Q) T) = _
    rw [hTT, formalGroupLawCoboundaryOne_sub hμQ, hcomb]
  choose r hr hrC using hC
  have hgen : ∀ α, algebraMap F.B F.Q (coeff α (cob1 μ' T)) =
      coeff α (frob p F.s (map (algebraMap F.B F.Q) F₁)) + algebraMap F.B F.Q (r α) -
        algebraMap F.B F.Q (∑ l, W l * g l α) := by
    intro α
    have h1 := congrArg (coeff α) hup
    rw [coeff_map] at h1
    rw [h1, ← hrC α, map_sub, map_sub, hF₁, map_sum, map_sum]
    have h2 : ∑ l, coeff α (algebraMap F.B F.Q (W l) • cob1 (up F.Q μ') (e l)) =
        ∑ l, algebraMap F.B F.Q (W l * g l α) :=
      Finset.sum_congr rfl fun l _ => by rw [MvPowerSeries.coeff_smul, hg, map_mul]
    rw [h2]; ring
  refine ⟨F₁, map F.θ T, hF₁, fun i => (memm _).1 ?_, fun β => (memm _).1 ?_,
    fun α ⟨i, hi⟩ => (memm _).1 ?_⟩
  · have key : coeff (Finsupp.single i 1) T = -∑ l, W l * c1 l i := by
      apply F.frame.inj
      have h1 := congrArg (coeff (Finsupp.single i 1)) hTT
      rw [coeff_map] at h1
      have hnd : ¬ p ∣ (Finsupp.single i 1 : Fin d →₀ ℕ) i := by
        rw [Finsupp.single_eq_same]; exact (Fact.out : p.Prime).not_dvd_one
      rw [h1, map_sub, coeff_frob_of_not_dvd p hp0 _ _ hnd, zero_sub, map_neg, map_sum]
      unfold comb
      rw [map_sum]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      have := hc1 l i
      simp only [lin] at this
      rw [MvPowerSeries.coeff_smul, this, map_mul]
    unfold lin
    rw [coeff_map, key, map_neg, map_sum]
    exact m.neg_mem (m.sum_mem fun l _ => by rw [map_mul]; exact m.mul_mem_right _ (hWm l))
  · have h1 := hgen (p • β)
    rw [coeff_frob_smul p hp0, coeff_map, F.s_alg, ← map_add, ← map_sub] at h1
    rw [hcobT, F.frame.inj h1]
    obtain ⟨y, hy⟩ := F.σ_pow (coeff β F₁)
    obtain ⟨r', hr'⟩ := Ideal.mem_span_singleton.1 (hr (p • β))
    have e1 : F.θ (F.σ (coeff β F₁) + r (p • β) - ∑ l, W l * g l (p • β)) - F.θ (coeff β F₁) ^ p =
        F.θ (F.σ (coeff β F₁) - coeff β F₁ ^ p) + F.θ (r (p • β)) -
          F.θ (∑ l, W l * g l (p • β)) := by
      simp only [map_sub, map_add, map_pow]; ring
    rw [e1, hy, hr']
    exact m.sub_mem (m.add_mem (hθp y) (hθp r')) (hSm _)
  · have h1 := hgen α
    rw [coeff_frob_of_not_dvd p hp0 _ _ hi, zero_add, ← map_sub] at h1
    rw [hcobT, F.frame.inj h1, map_sub]
    obtain ⟨r', hr'⟩ := Ideal.mem_span_singleton.1 (hr α)
    rw [hr']
    exact m.sub_mem (hθp r') (hSm _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusLiftSolvesModFrobXiMu
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

theorem GlobalTheory.WinLift.frob_lift_dvd : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) (F0 : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)), IsUnit V → (∀ i m, Sandwich.mu ε ∣ (F0.map WittVector.frobenius - blk d k (p : Ainf p O) 1 * V.transpose * F0) i m) → (∀ i m, WittVector.fontaineTheta O p (F0 (Sum.inl i) m) = 0) → ∀ i m, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ (V.transpose⁻¹ * blk d k 1 (WittVector.frobenius (xi ε)) * F0.map WittVector.frobenius) i m - WittVector.frobenius (xi ε) * F0 i m := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h V F0 hV hF hθ i m
  set ξ' : Ainf p O := WittVector.frobenius (xi ε) with hξ'
  set μ : Ainf p O := Sandwich.mu ε with hμ
  set G : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O) := V.transpose * F0 with hG
  set E : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O) :=
    blk d k 1 ξ' * F0.map WittVector.frobenius - ξ' • G with hEdef
  have hVt : IsUnit V.transpose.det := by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det V).1 hV
  have key : V.transpose⁻¹ * blk d k 1 ξ' * F0.map WittVector.frobenius - ξ' • F0 =
      V.transpose⁻¹ * E := by
    rw [hEdef, hG, Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc (V.transpose⁻¹),
      Matrix.nonsing_inv_mul _ hVt, Matrix.one_mul]
  have hEe : ∀ j n, E j n = Sum.elim (fun _ => (1 : Ainf p O)) (fun _ => ξ') j *
      WittVector.frobenius (F0 j n) - ξ' * G j n := by
    intro j n
    simp [hEdef, blk, Matrix.diagonal_mul]
  have hyp : ∀ j n, μ ∣ WittVector.frobenius (F0 j n) -
      Sum.elim (fun _ => (p : Ainf p O)) (fun _ => 1) j * G j n := by
    intro j n
    have := hF j n
    rw [Matrix.mul_assoc, ← hG] at this
    simpa [blk, Matrix.diagonal_mul] using this
  have hE : ∀ j n, ξ' * μ ∣ E j n := by
    intro j n
    rw [hEe]
    rcases j with j | j
    · obtain ⟨w, hw⟩ := (Ideal.mem_span_singleton').1
        (show F0 (Sum.inl j) n ∈ Ideal.span {xi ε} by
          rw [← AinfXi.ker_theta hv ε (root_prim hε)]; exact hθ j n)
      have h1 : μ ∣ ξ' * (WittVector.frobenius w - G (Sum.inl j) n) := by
        have := dvd_sub (hyp (Sum.inl j) n) ((mu_dvd_frob_xi_sub ε).mul_right (G (Sum.inl j) n))
        convert this using 1
        simp only [Sum.elim_inl]
        rw [← hw, map_mul, ← hξ']
        ring
      have h2 := mul_dvd_mul_left ξ' (mu_dvd_of_xi_mul F _ h1)
      convert h2 using 1
      simp only [Sum.elim_inl]
      rw [← hw, map_mul, ← hξ']
      ring
    · have := mul_dvd_mul_left ξ' (hyp (Sum.inr j) n)
      convert this using 1
      simp only [Sum.elim_inr]
      ring
  have e := congrFun (congrFun key i) m
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at e
  rw [e, Matrix.mul_apply]
  exact Finset.dvd_sum fun j _ => (hE j m).mul_left _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusLinearCombinationZeroLeftAinfFrameStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_linearCombination_zero_left_ainfFrame : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (F : BFrame ε) (d k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B), (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → ∀ b : Fin k → F.B, In (⊤ : Ideal F.B) (frob p F.s (comb (Sum.elim (fun _ => 0) b) e) - comb (U.mulVec (fun j => F.σ ((Sum.elim (fun _ => 0) b : Fin d ⊕ Fin k → F.B) j))) e) := by
  first | exact @GlobalTheory.frob_comb_zero_left | exact GlobalTheory.frob_comb_zero_left | (intros; apply GlobalTheory.frob_comb_zero_left <;> assumption)
end

