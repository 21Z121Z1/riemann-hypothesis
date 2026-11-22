import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0681
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0683
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0669
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0653
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0682
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0663
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0668
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDevissageStepIndependentStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_devissage_step_independent : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (C : Type) [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ Θ : Q →+* C, (∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b)) → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q), (∀ i, QL μ ⊤ (e i)) → IsBasis (fun i => map θ (μ i)) (fun i => map Θ (e i)) → ∀ N' N : Ideal B, IsStep p θ N' N → ∀ (b : ι → B) (s : MvPowerSeries (Fin d) Q), (∀ i, b i ∈ N) → In N s → QL μ N' (comb b e - s) → (∀ i, b i ∈ N') ∧ In N' s := by
  first | exact @GlobalTheory.step_independent | exact GlobalTheory.step_independent | (intros; apply GlobalTheory.step_independent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPullbackTeichmullerLift
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.KatzPull

open GlobalTheory.Katz

theorem lift_X (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] {σ : Type} (s : σ) :
    Katz.lift p (X s : MvPowerSeries σ k) = X s := by
  classical
  ext α
  rw [coeff_lift, coeff_X, coeff_X]
  split_ifs
  · rw [map_one, map_one]
  · rw [WittVector.teichmuller_zero, map_zero]

theorem lin_subst {R : Type} [CommRing R] {d e : ℕ} (a : Fin e → MvPowerSeries (Fin d) R)
    (ha : ∀ j, constantCoeff (a j) = 0) (f : MvPowerSeries (Fin e) R) :
    lin (subst a f) = pullLin a (lin f) := by
  classical
  have ha' := hasSubst_of_constantCoeff_zero ha
  have hcard : ∀ α : Fin e →₀ ℕ, Multiset.card (Finsupp.toMultiset α) = α.degree := fun α => by
    rw [Finsupp.card_toMultiset, Finsupp.degree]; rfl
  have inj : Function.Injective (Finsupp.toMultiset : (Fin e →₀ ℕ) → Multiset (Fin e)) :=
    fun x y hxy => by simpa using congrArg Multiset.toFinsupp hxy
  set f1 : MvPowerSeries (Fin e) R := C (constantCoeff f) + ∑ j, C (lin f j) * X j with hf1
  have hf2 : ∀ α : Fin e →₀ ℕ, α.degree < 2 → coeff α (f - f1) = 0 := by
    intro α hα
    rcases (show α.degree = 0 ∨ α.degree = 1 by omega) with h | h
    · have h0 : α = 0 := by
        apply inj
        rw [map_zero, ← Multiset.card_eq_zero, hcard, h]
      subst h0
      simp [hf1, coeff_X]
    · obtain ⟨j, hj⟩ := Multiset.card_eq_one.1 ((hcard α).trans h)
      have h1 : α = Finsupp.single j 1 := by
        apply inj
        rw [hj, Finsupp.toMultiset_single, one_smul]
      subst h1
      simp [hf1, coeff_X, coeff_C, lin, Finsupp.single_eq_single_iff]
  funext i
  have key := (GlobalTheory.T.coeff_subst_leading_of_agree_degree_one R (Fin e) (Fin d) a a 2 (f - f1) ha ha (fun _ _ _ => rfl) hf2
    (Finsupp.single i 1)).1 (by rw [Finsupp.degree_single]; norm_num)
  rw [subst_sub ha', map_sub, sub_eq_zero] at key
  unfold lin pullLin
  rw [key, hf1, subst_add ha', subst_C, map_add, coeff_C, if_neg (Finsupp.single_ne_zero.2 one_ne_zero),
    zero_add, ← coe_substAlgHom ha', map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, coe_substAlgHom ha', subst_C, subst_X ha', coeff_C_mul]
  rfl

theorem quasiLog_pull : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d e : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k) (hμ : IsLaw μ) (hν : IsLaw ν) (φ : Fin e → MvPowerSeries (Fin d) k), IsHom μ ν φ → ∀ f ∈ quasiLog p hν, subst (fun j => Katz.lift p (φ j)) f ∈ quasiLog p hμ ∧ (∀ c, Red p (cob1 (fun j => Katz.lift p (ν j)) f) c → Red p (cob1 (fun i => Katz.lift p (μ i)) (subst (fun j => Katz.lift p (φ j)) f)) (pull2 φ c)) ∧ ∀ w, RedV p (lin f) w → RedV p (lin (subst (fun j => Katz.lift p (φ j)) f)) (pullLin φ w) := by
  intro p _ k _ _ _ d e μ ν hμ hν φ hφ f hf
  obtain ⟨hf1, hf2⟩ := hf
  have hΦ0 : ∀ j, constantCoeff (Katz.lift p (φ j)) = 0 := fun j => constantCoeff_lift p (hφ.const j)
  have hΦs : HasSubst (fun j => Katz.lift p (φ j)) := hasSubst_of_constantCoeff_zero hΦ0
  have hLμ0 : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0 := fun i => constantCoeff_lift p (hμ.const i)
  have hLμs : HasSubst (fun i => Katz.lift p (μ i)) := hasSubst_of_constantCoeff_zero hLμ0
  have hLν0 : ∀ i, constantCoeff (Katz.lift p (ν i)) = 0 := fun i => constantCoeff_lift p (hν.const i)
  have hXl0 : ∀ i : Fin d, constantCoeff (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k)) = 0 :=
    fun _ => constantCoeff_X _
  have hXr0 : ∀ i : Fin d, constantCoeff (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k)) = 0 :=
    fun _ => constantCoeff_X _
  have hXls := hasSubst_of_constantCoeff_zero hXl0
  have hXrs := hasSubst_of_constantCoeff_zero hXr0
  have RR := fun σ => GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k σ
  have hRedΦ : ∀ j, Red p (Katz.lift p (φ j)) (φ j) := fun j => (RR _).2.2.1 (φ j)
  have redX : ∀ {σ : Type} (s : σ), Red p (X s : MvPowerSeries σ (Fr p k)) (X s) := fun s => by
    simpa [lift_X] using (RR _).2.2.1 (X s : MvPowerSeries _ k)
  have hIL := GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin d) (Fin d ⊕ Fin d) (fun i => X (Sum.inl i)) (fun i => X (Sum.inl i))
    hXl0 (fun i => redX _)
  have hIR := GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin d) (Fin d ⊕ Fin d) (fun i => X (Sum.inr i)) (fun i => X (Sum.inr i))
    hXr0 (fun i => redX _)

  set U : Fin e ⊕ Fin e → MvPowerSeries (Fin d ⊕ Fin d) (Fr p k) :=
    Sum.elim (fun j => inL (Katz.lift p (φ j))) (fun j => inR (Katz.lift p (φ j))) with hU
  set U' : Fin e ⊕ Fin e → MvPowerSeries (Fin d ⊕ Fin d) k :=
    Sum.elim (fun j => inL (φ j)) (fun j => inR (φ j)) with hU'
  have hinL0 : ∀ j, constantCoeff (inL (Katz.lift p (φ j))) = 0 := fun j =>
    constantCoeff_subst_eq_zero hXls hXl0 (hΦ0 j)
  have hinR0 : ∀ j, constantCoeff (inR (Katz.lift p (φ j))) = 0 := fun j =>
    constantCoeff_subst_eq_zero hXrs hXr0 (hΦ0 j)
  have hU0 : ∀ s, constantCoeff (U s) = 0 := by
    rintro (j | j)
    · exact hinL0 j
    · exact hinR0 j
  have hRedU : ∀ s, Red p (U s) (U' s) := by
    rintro (j | j)
    · exact hIL.1 _ _ (hRedΦ j)
    · exact hIR.1 _ _ (hRedΦ j)
  have hIU := GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin e ⊕ Fin e) (Fin d ⊕ Fin d) U U' hU0 hRedU
  have C6 := GlobalTheory.T.powerSeriesEvalTwoGroups_rules (Fr p k) e (Fin d ⊕ Fin d) (Fin d ⊕ Fin d)
    (fun j => inL (Katz.lift p (φ j))) (fun j => inR (Katz.lift p (φ j))) hinL0 hinR0

  set A : Fin e → MvPowerSeries (Fin d ⊕ Fin d) (Fr p k) :=
    fun j => subst (fun i => Katz.lift p (μ i)) (Katz.lift p (φ j)) with hA
  set B : Fin e → MvPowerSeries (Fin d ⊕ Fin d) (Fr p k) :=
    fun j => subst U (Katz.lift p (ν j)) with hB
  have hA0 : ∀ j, constantCoeff (A j) = 0 := fun j => constantCoeff_subst_eq_zero hLμs hLμ0 (hΦ0 j)
  have hB0 : ∀ j, constantCoeff (B j) = 0 := fun j =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hU0) hU0 (hLν0 j)
  have hRA : ∀ j, Red p (A j) (subst μ (φ j)) := fun j =>
    (GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin d) (Fin d ⊕ Fin d) _ μ hLμ0 (fun i => (RR _).2.2.1 (μ i))).1 _ _ (hRedΦ j)
  have hRB : ∀ j, Red p (B j) (subst μ (φ j)) := fun j => by
    rw [hφ.hom j]
    exact hIU.1 _ _ ((RR _).2.2.1 (ν j))
  have hD := GlobalTheory.T.subst_sub_subst_integral_of_integral_differential p k (Fin e) (Fin d ⊕ Fin d) A B (fun j => subst μ (φ j)) f hA0 hB0 hRA hRB hf1

  have hid : cob1 (fun i => Katz.lift p (μ i)) (subst (fun j => Katz.lift p (φ j)) f) =
      (subst A f - subst B f) + subst U (cob1 (fun j => Katz.lift p (ν j)) f) := by
    have e1 : subst U (cob1 (fun j => Katz.lift p (ν j)) f) =
        subst B f - subst (fun j => inL (Katz.lift p (φ j))) f - subst (fun j => inR (Katz.lift p (φ j))) f := by
      change at2 (cob1 (fun j => Katz.lift p (ν j)) f) _ _ = _
      unfold cob1
      rw [(C6.2.2.1 _ _).2, (C6.2.2.1 _ _).2, C6.1, C6.2.1, C6.2.2.2.2.2.1 e _ hLν0]
      rfl
    rw [e1]
    unfold cob1 inL inR
    rw [subst_comp_subst_apply hΦs hLμs, subst_comp_subst_apply hΦs hXls,
      subst_comp_subst_apply hΦs hXrs]
    abel
  have part2 : ∀ c, Red p (cob1 (fun j => Katz.lift p (ν j)) f) c →
      Red p (cob1 (fun i => Katz.lift p (μ i)) (subst (fun j => Katz.lift p (φ j)) f)) (pull2 φ c) := by
    intro c hc
    rw [hid]
    have h1 := ((RR _).2.2.2.2.2.1 _).1 hD
    have h2 := hIU.1 _ _ hc
    have := ((RR _).2.2.2.1 _ _ _ _ h1 h2).1
    rwa [zero_add] at this
  refine ⟨⟨GlobalTheory.T.subst_mem_integralDifferentialSubmodule p k (Fin e) (Fin d) _ f hΦ0
      (fun j => ((RR _).1 _).2 ⟨φ j, hRedΦ j⟩) hf1, ?_⟩, part2, ?_⟩
  · obtain ⟨c, hc⟩ := ((RR _).1 _).1 hf2
    exact ((RR _).1 _).2 ⟨_, part2 c hc⟩
  · intro w hw i
    rw [lin_subst _ hΦ0]
    choose a ha ha' using hw
    refine ⟨∑ j, a j * WittVector.teichmuller p (lin (φ j) i), ?_, ?_⟩
    · simp only [pullLin, map_sum, map_mul, ha]
      rfl
    · simp only [pullLin, map_sum, map_mul, ha', WittVector.teichmuller_coeff_zero]
      rfl

end GlobalTheory.KatzPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientJetsFderivDetNeZeroStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_jets_fderiv_det_ne_zero : ∀ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ (p : V n) (w0 : V n → ℂ) (w : Fin n → V n → ℂ), DifferentiableAt ℂ w0 p → (∀ j, DifferentiableAt ℂ (w j) p) → ‖w0 p - 1‖ ≤ ε → ‖fderiv ℂ (fun v => w0 v - 1) p‖ ≤ ε → (∀ j, ‖w j p‖ ≤ ε) → (∀ j, ‖fderiv ℂ (fun v : V n => w j v - (v j - p j)) p‖ ≤ ε) → w0 p ≠ 0 ∧ (fderiv ℂ (fun v : V n => (WithLp.toLp 2 (fun j => w j v / w0 v) : V n)) p).det ≠ 0 := by
  first | exact @GlobalTheory.quot_jets_det_ne_zero | exact GlobalTheory.quot_jets_det_ne_zero | (intros; apply GlobalTheory.quot_jets_det_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionCommutesFormalGroupLawCoboundariesStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), (∀ i, constantCoeff (μ i) = 0) → (∀ g c, Red p g c → Red p (cob2 (fun i => Katz.lift p (μ i)) g) (cob2 μ c) ∧ Red p (swap g) (swap c)) ∧ (∀ b b', Red p b b' → Red p (cob1 (fun i => Katz.lift p (μ i)) b) (cob1 μ b') ∧ RedV p (lin b) (lin b')) ∧ (∀ i, Red p (op (fun i => Katz.lift p (μ i)) x1 (op (fun i => Katz.lift p (μ i)) x2 x3) i) (op μ x1 (op μ x2 x3) i) ∧ Red p (op (fun i => Katz.lift p (μ i)) (op (fun i => Katz.lift p (μ i)) x1 x2) x3 i) (op μ (op μ x1 x2) x3 i)) ∧ ∀ (c : WittVector p k) g, g ∈ intBy p k (Fin d ⊕ Fin d) c → cob2 (fun i => Katz.lift p (μ i)) g ∈ intBy p k _ c ∧ swap g ∈ intBy p k _ c := by
  first | exact @GlobalTheory.Katz.red_coboundaries | exact GlobalTheory.Katz.red_coboundaries | (intros; apply GlobalTheory.Katz.red_coboundaries <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionQuotientHolomorphicMeasurable
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
theorem _root_.GlobalTheory.OTY.TwEst.quot_holo_measurable : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La]
    (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La), ∀ (la : La) (U Ω : Set Y) (β h : ι → Y → ℂ), IsOpen U → IsOpen Ω →
    A.IsFrameOn la U β → A.IsSecOn la Ω h → (∀ i y, y ∉ Ω → h i y = 0) →
    (∀ i, DifferentiableOn ℂ (_root_.GlobalTheory.OTY.TwEst.quot A h β ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω))) ∧
    Measurable (_root_.GlobalTheory.OTY.TwEst.ext0 U (fun y : U => _root_.GlobalTheory.OTY.TwEst.quot A h β y)) ∧
    ∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * _root_.GlobalTheory.OTY.TwEst.quot A h β y := by
  intro n Y _ _ _ _ _ ι La _ A la U Ω β h hU hΩ hβ hh h0
  classical
  obtain ⟨⟨hβhol, hβcoc⟩, hβne⟩ := hβ
  obtain ⟨hhhol, hhcoc⟩ := hh
  have hq : ∀ y, _root_.GlobalTheory.OTY.TwEst.quot A h β y = h (A.pick y) y / β (A.pick y) y := fun y => by
    unfold _root_.GlobalTheory.OTY.TwEst.quot; rfl
  have hβi : ∀ i, ∀ y ∈ (A.chart i).source, y ∈ U → β i y ≠ 0 := by
    intro i y hy hyU hzero
    apply hβne y hyU
    rw [hβcoc (A.pick y) i y hyU (A.mem_pick y) hy, hzero, mul_zero]
  have hqe : ∀ i, ∀ y ∈ (A.chart i).source, y ∈ U →
      _root_.GlobalTheory.OTY.TwEst.quot A h β y = h i y / β i y := by
    intro i y hy hyU
    rw [hq]
    by_cases hyΩ : y ∈ Ω
    · rw [hhcoc (A.pick y) i y hyΩ (A.mem_pick y) hy, hβcoc (A.pick y) i y hyU (A.mem_pick y) hy,
        mul_div_mul_left _ _ (A.g_ne la _ _ y (A.mem_pick y) hy)]
    · rw [h0 _ _ hyΩ, h0 _ _ hyΩ, zero_div, zero_div]
  have hdiff : ∀ i, DifferentiableOn ℂ (_root_.GlobalTheory.OTY.TwEst.quot A h β ∘ (A.chart i).symm)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω)) := by
    intro i
    set S := (A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω) with hS
    have h1 : DifferentiableOn ℂ (h i ∘ (A.chart i).symm) S :=
      (hhhol i).mono fun v hv => ⟨hv.1, hv.2.2⟩
    have h2 : DifferentiableOn ℂ (β i ∘ (A.chart i).symm) S :=
      (hβhol i).mono fun v hv => ⟨hv.1, hv.2.1⟩
    have h3 : ∀ v ∈ S, (β i ∘ (A.chart i).symm) v ≠ 0 := fun v hv =>
      hβi i _ ((A.chart i).map_target hv.1) hv.2.1
    have hd : DifferentiableOn ℂ
        (fun v => (h i ∘ (A.chart i).symm) v * ((β i ∘ (A.chart i).symm) v)⁻¹) S :=
      h1.mul (h2.inv h3)
    refine hd.congr fun v hv => ?_
    simp only [Function.comp_apply, ← div_eq_mul_inv]
    exact hqe i _ ((A.chart i).map_target hv.1) hv.2.1
  refine ⟨hdiff, ?_, fun y hy => ?_⟩
  · have hopen : IsOpen (U ∩ Ω) := hU.inter hΩ
    have hcont : ContinuousOn (_root_.GlobalTheory.OTY.TwEst.quot A h β) (U ∩ Ω) := by
      intro y hy
      set i := A.pick y
      have hys : y ∈ (A.chart i).source := A.mem_pick y
      have hset : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω)) :=
        (A.chart i).isOpen_inter_preimage_symm hopen
      have hmem : A.chart i y ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω) :=
        ⟨(A.chart i).map_source hys, by
          simp only [Set.mem_preimage, (A.chart i).left_inv hys]; exact hy⟩
      have hca : ContinuousAt (_root_.GlobalTheory.OTY.TwEst.quot A h β ∘ (A.chart i).symm) (A.chart i y) :=
        ((hdiff i).continuousOn).continuousAt (hset.mem_nhds hmem)
      have hcomp : ContinuousAt ((_root_.GlobalTheory.OTY.TwEst.quot A h β ∘ (A.chart i).symm) ∘ A.chart i) y :=
        hca.comp ((A.chart i).continuousAt hys)
      refine (hcomp.congr ?_).continuousWithinAt
      filter_upwards [(A.chart i).open_source.mem_nhds hys] with w hw
      simp [(A.chart i).left_inv hw]
    have heq : _root_.GlobalTheory.OTY.TwEst.ext0 U (fun y : U => _root_.GlobalTheory.OTY.TwEst.quot A h β y) =
        (U ∩ Ω).piecewise (_root_.GlobalTheory.OTY.TwEst.quot A h β) 0 := by
      funext y
      unfold _root_.GlobalTheory.OTY.TwEst.ext0
      by_cases hyU : y ∈ U
      · by_cases hyΩ : y ∈ Ω
        · simp [hyU, hyΩ, Set.piecewise]
        · simp [hyU, hyΩ, Set.piecewise, hq, h0 _ _ hyΩ]
      · simp [hyU, Set.piecewise]
    rw [heq]
    exact hcont.measurable_piecewise continuousOn_const hopen.measurableSet
  · rw [hq, mul_div_cancel₀ _ (hβne y hy)]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearHomConnectedFactorThroughPart
section
open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

open TensorProduct Coalgebra Bialgebra WithConv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem PDivGroup.semiHom_app_eq_conn_part :
    ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
    [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' G'₀ G'₁ : PDivGroup p k') (C : PDivGroup p k)
    (i₀ : G'₀ ⟶ G') (q₀ : G' ⟶ G'₀) (i₁ : G'₁ ⟶ G') (q₁ : G' ⟶ G'₁), G'₁.IsEt → C.IsConn →
    q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G' → ∀ (x : SemiHom σ G' C) (n : ℕ) (a : C.A n),
      q₀.app n (i₀.app n (x.app n a)) = x.app n a := by
  intro p _ k k' _ _ _ _ _ _ σ G' G'₀ G'₁ C i₀ q₀ i₁ q₁ hEt hConn hsplit x n a
  have h1 : ∀ c : C.A n,
      i₁.app n (x.app n c) = algebraMap k' (G'₁.A n) (σ (counit (R := k) c)) := by
    intro c
    haveI := hEt n
    have hmem : c - algebraMap k (C.A n) (counit (R := k) c) ∈ augIdeal k (C.A n) := by
      rw [mem_augIdeal_iff', map_sub, ← Bialgebra.counitAlgHom_apply (R := k),
        ← Bialgebra.counitAlgHom_apply (R := k), AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply, sub_self]
    have h := (((hConn n _ hmem).map (x.app n).toRingHom).map (i₁.app n)).eq_zero
    change i₁.app n (x.app n (c - _)) = 0 at h
    rw [map_sub, SemiBialgHom.map_algebraMap, map_sub, AlgHomClass.commutes, sub_eq_zero] at h
    exact h
  have hP₁ : ∀ c : C.A n, (q₁ ≫ i₁).app n (x.app n c) =
      algebraMap k' (G'.A n) (σ (counit (R := k) c)) := by
    intro c
    rw [comp_app, BialgHom.comp_apply, h1, AlgHomClass.commutes]
  have hid : ∀ b : G'.A n, ((q₀ ≫ i₀).conv n * (q₁ ≫ i₁).conv n).ofConv b = b := by
    intro b
    have h := congrArg (fun f : G' ⟶ G' => f.app n b) hsplit
    exact h
  have key : ∀ c : C.A n ⊗[k] C.A n,
      Algebra.TensorProduct.lift ((q₀ ≫ i₀).app n : G'.A n →ₐ[k'] G'.A n)
        ((q₁ ≫ i₁).app n : G'.A n →ₐ[k'] G'.A n) (fun _ _ => .all _ _) ((x.app n).two c) =
      (q₀ ≫ i₀).app n (x.app n (TensorProduct.rid k (C.A n)
        (LinearMap.lTensor (C.A n) (counit (R := k)) c))) := by
    intro c
    induction c with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | tmul b c =>
      rw [TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, LinearMap.lTensor_tmul,
        TensorProduct.rid_tmul, SemiBialgHom.lin_apply, SemiBialgHom.lin_apply]
      change _ * (q₁ ≫ i₁).app n (x.app n c) = _
      rw [hP₁, (x.app n).smul_map, map_smul, Algebra.smul_def, mul_comm]
      rfl
  have e : (toPts ((q₀ ≫ i₀).conv n * (q₁ ≫ i₁).conv n)).ofConv (x.app n a) = x.app n a :=
    hid (x.app n a)
  rw [map_mul, AlgHom.convMul_apply, toPts_ofConv, toPts_ofConv, ← (x.app n).two_comul] at e
  have e2 := key (comul (R := k) a)
  rw [Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul] at e2
  exact e2.symm.trans e

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearHomEtaleFactorThroughPart
section
open CategoryTheory GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

open TensorProduct Coalgebra Bialgebra WithConv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDivGroup

theorem app_app_eq_algebraMap_counit_of_isConn_of_isEt {p : ℕ} [Fact p.Prime] {k k' : Type}
    [Field k] [CharP k p] [PerfectRing k p] [Field k'] {σ : k →+* k'} {G' G'₀ : PDivGroup p k'}
    {C : PDivGroup p k} (i₀ : G'₀ ⟶ G') (hG : G'₀.IsConn) (hC : C.IsEt) (x : SemiHom σ G' C)
    (n : ℕ) (a : C.A n) :
    i₀.app n (x.app n a) = algebraMap k' (G'₀.A n) (σ (counit (R := k) a)) := by
  have hmem : a - algebraMap k (C.A n) (counit (R := k) a) ∈ augIdeal k (C.A n) := by
    rw [mem_augIdeal_iff', map_sub, ← Bialgebra.counitAlgHom_apply (R := k),
      ← Bialgebra.counitAlgHom_apply (R := k), AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  suffices h : i₀.app n ((x.app n).toRingHom (a - algebraMap k (C.A n) (counit (R := k) a))) = 0 by
    rw [map_sub, map_sub, sub_eq_zero] at h
    refine h.trans ?_
    change i₀.app n ((x.app n) (algebraMap k (C.A n) (counit (R := k) a))) = _
    rw [(x.app n).map_algebraMap, AlgHomClass.commutes]
  haveI := hC n
  haveI : IsNoetherianRing (G'₀.A n) := isNoetherian_of_tower k' inferInstance
  obtain ⟨N, hN⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical
    (IsNoetherian.noetherian (augIdeal k' (G'₀.A n)))).2 fun y hy => mem_nilradical.2 (hG n y hy)
  obtain ⟨b, hb, hab⟩ := exists_augIdeal_pow_eq (A := C.A n) N _ hmem
  have hfb : i₀.app n ((x.app n).toRingHom b) ∈ augIdeal k' (G'₀.A n) := by
    rw [mem_augIdeal_iff', CoalgHomClass.counit_comp_apply]
    change counit (R := k') ((x.app n) b) = 0
    rw [(x.app n).counit_map, (mem_augIdeal_iff' b).1 hb, map_zero]
  have hle : N ≤ p ^ N := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have h1 := Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hfb (p ^ N))
  rw [hN] at h1
  rw [hab, map_pow, map_pow]
  exact (Submodule.mem_bot _).1 h1

theorem add_app_eq_lift_comul {p : ℕ} {k : Type} [CommRing k] {G H : PDivGroup p k}
    (f g : G ⟶ H) (n : ℕ) (c : H.A n) :
    Hom.app (f + g) n c = Algebra.TensorProduct.lift (f.app n : H.A n →ₐ[k] G.A n)
      (g.app n : H.A n →ₐ[k] G.A n) (fun _ _ => .all _ _) (comul c) := by
  have h := DFunLike.congr_fun (congrArg ofConv (map_mul toPts (f.conv n) (g.conv n))) c
  rw [AlgHom.convMul_apply] at h
  exact h

end GlobalTheory.PDivGroup

theorem GlobalTheory.PDivGroup.semiHom_factor_of_isConn_of_isEt :
    ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [PerfectRing k p]
    [Field k'] [CharP k' p] [PerfectRing k' p] (σ : k →+* k') (G' G'₀ G'₁ : PDivGroup p k') (C : PDivGroup p k)
    (i₀ : G'₀ ⟶ G') (q₀ : G' ⟶ G'₀) (i₁ : G'₁ ⟶ G') (q₁ : G' ⟶ G'₁), G'₀.IsConn → C.IsEt →
    q₀ ≫ i₀ + q₁ ≫ i₁ = 𝟙 G' → ∀ (x : SemiHom σ G' C) (n : ℕ) (a : C.A n),
      q₁.app n (i₁.app n (x.app n a)) = x.app n a := by
  intro p _ k k' _ _ _ _ _ _ σ G' G'₀ G'₁ C i₀ q₀ i₁ q₁ hG hC hs x n a
  have key : ∀ t : C.A n ⊗[k] C.A n,
      Algebra.TensorProduct.lift ((q₀ ≫ i₀).app n : G'.A n →ₐ[k'] G'.A n)
        ((q₁ ≫ i₁).app n : G'.A n →ₐ[k'] G'.A n) (fun _ _ => .all _ _) ((x.app n).two t) =
      (q₁ ≫ i₁).app n (x.app n (TensorProduct.lid k _ (LinearMap.rTensor _ counit t))) := by
    intro t
    induction t with
    | zero => simp
    | add u v hu hv =>
      rw [map_add, map_add, hu, hv, map_add, map_add, ← map_add, ← map_add]
    | tmul a₁ a₂ =>
      rw [TensorProduct.map_tmul, SemiBialgHom.lin_apply, SemiBialgHom.lin_apply,
        Algebra.TensorProduct.lift_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
      change q₀.app n (i₀.app n (x.app n a₁)) * _ = _
      rw [app_app_eq_algebraMap_counit_of_isConn_of_isEt i₀ hG hC x n a₁, AlgHomClass.commutes,
        ← Algebra.smul_def, (x.app n).smul_map]
      change _ = ((q₁ ≫ i₁).app n : G'.A n →ₐ[k'] G'.A n) (σ (counit a₁) • x.app n a₂)
      rw [map_smul]
  have h1 : x.app n a = Hom.app (q₀ ≫ i₀ + q₁ ≫ i₁) n (x.app n a) := by rw [hs]; rfl
  rw [add_app_eq_lift_comul, ← SemiBialgHom.two_comul, key, Coalgebra.rTensor_counit_comul,
    TensorProduct.lid_tmul, one_smul] at h1
  exact h1.symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearLiftBijectiveLocalizationStatement
section
open GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinear_lift_bijective_localization : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (f : R) [IsLocalization.Away f R'] {M M' : Type 1} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] (ρ : M →ₛₗ[algebraMap R R'] M'), Function.Bijective (GlobalTheory.DeRham.liftSemi ρ) → (∀ m' : M', ∃ (n : ℕ) (x : M), algebraMap R R' f ^ n • m' = ρ x) ∧ ∀ x : M, ρ x = 0 → ∃ n : ℕ, f ^ n • x = 0 := by
  first | exact @GlobalTheory.DeRham.localisation_of_liftSemi_bijective | exact GlobalTheory.DeRham.localisation_of_liftSemi_bijective | (intros; apply GlobalTheory.DeRham.localisation_of_liftSemi_bijective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShEqvTwStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eqv_spMap_tw_of_isUnit : ∀ (q : ℕ) (i : ℤ) (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B), SH A → SH B → IsUnit (q : A) → Eqv _ (spMap φ) (tw q i) := by
  first | (exact @GlobalTheory.EtC.sh_eqv_tw) | (exact GlobalTheory.EtC.sh_eqv_tw) | (intros; apply GlobalTheory.EtC.sh_eqv_tw  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelKlingenDeligneRibetOfBoth
section
namespace GlobalTheory

theorem siegelKlingenDeligneRibet_of_both :
    GlobalTheory.Published.SiegelKlingen → GlobalTheory.Published.DeligneRibet → GlobalTheory.Published.SiegelKlingenDeligneRibet :=
  fun a b => ⟨a, b⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallExtensionElementMulZeroClassEqZeroStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallExtension_element_mul_zeroClass_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ y : HO1 s, TMul h₀.w t 0 y → y = 0 := by
  first | exact @GlobalTheory.AbCoh.tMul_zero_eq_zero | exact GlobalTheory.AbCoh.tMul_zero_eq_zero | (intros; apply GlobalTheory.AbCoh.tMul_zero_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothBumpChartBallHalfOneStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_bump_chart_ball_halfOne : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (i : ι) (p : V n) (ρ : ℝ), 0 < ρ → closedBall p ρ ⊆ (A.chart i).target → ∃ χ : Y → ℝ, A.SmoothFn χ ∧ tsupport χ ⊆ (A.chart i).source ∩ A.chart i ⁻¹' ball p ρ ∧ ∀ y ∈ (A.chart i).source, A.chart i y ∈ ball p (ρ / 2) → χ y = 1 := by
  first | exact @GlobalTheory.smooth_bump_chart_ball | exact GlobalTheory.smooth_bump_chart_ball | (intros; apply GlobalTheory.smooth_bump_chart_ball <;> assumption)
end

