import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0642
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0234
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0703
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxB
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0708
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0690
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0707
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0694
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0441
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0392
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0696
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMoritaLatticeQuotientTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.EtLevMorita

theorem isLocalRing_quot_pow {A : Type} [CommRing A] (m : Ideal A) [hm : m.IsMaximal] (k : ℕ)
    (hk : k ≠ 0) : IsLocalRing (A ⧸ m ^ k) := by
  have hne : m ^ k ≠ ⊤ := fun h => hm.ne_top (top_le_iff.1 (h ▸ Ideal.pow_le_self hk))
  haveI : Nontrivial (A ⧸ m ^ k) := Ideal.Quotient.nontrivial_iff.2 hne
  obtain ⟨M0, hM0⟩ := Ideal.exists_maximal (A ⧸ m ^ k)
  have key : ∀ M : Ideal (A ⧸ m ^ k), M.IsMaximal → M.comap (Ideal.Quotient.mk (m ^ k)) = m := by
    intro M hM
    have h1 : (M.comap (Ideal.Quotient.mk (m ^ k))).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    have h2 : m ^ k ≤ M.comap (Ideal.Quotient.mk (m ^ k)) := by
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
      exact M.zero_mem
    have h3 : m ≤ M.comap (Ideal.Quotient.mk (m ^ k)) := h1.isPrime.le_of_pow_le h2
    exact (hm.eq_of_le h1.ne_top h3).symm
  exact IsLocalRing.of_unique_max_ideal ⟨M0, hM0, fun M hM =>
    Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
      ((key M hM).trans (key M0 hM0).symm)⟩

section Act

variable {O : Type} [Ring O] {G : Type} [CommGroup G] (act : O → G → G)
  (hmul : ∀ b g h, act b (g * h) = act b g * act b h) (hone : ∀ g, act 1 g = g)
  (hcomp : ∀ b c g, act (b * c) g = act b (act c g)) (hadd : ∀ b c g, act (b + c) g = act b g * act c g)

include hmul in
theorem act_one_eq (b : O) : act b 1 = 1 := by
  have h := hmul b 1 1
  rw [_root_.mul_one] at h
  exact left_eq_mul.1 h

include hadd in
theorem act_zero_eq (g : G) : act 0 g = 1 := by
  have h := hadd 0 0 g
  rw [add_zero] at h
  exact left_eq_mul.1 h

def actModule : Module O (Additive G) where
  smul b x := Additive.ofMul (act b x.toMul)
  one_smul x := by show Additive.ofMul (act 1 x.toMul) = x; rw [hone]; rfl
  mul_smul b c x := congrArg Additive.ofMul (hcomp b c x.toMul)
  smul_zero b := congrArg Additive.ofMul (act_one_eq act hmul b)
  smul_add b x y := congrArg Additive.ofMul (hmul b x.toMul y.toMul)
  add_smul b c x := congrArg Additive.ofMul (hadd b c x.toMul)
  zero_smul x := congrArg Additive.ofMul (act_zero_eq act hadd x.toMul)

end Act

end GlobalTheory.EtLevMorita

open GlobalTheory.EtLevMorita in

theorem GlobalTheory.EtLevMorita.exists_lev : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (w0 : Ideal (𝓞 D.F)) (r : ℕ), w0.IsMaximal → (p : 𝓞 D.F) ∈ w0 →
  ∀ (G : Type) [CommGroup G] (act : D.O → G → G), (∀ b g h, act b (g * h) = act b g * act b h) → (∀ g, act 1 g = g) →
  (∀ b c g, act (b * c) g = act b (act c g)) → (∀ b c g, act (b + c) g = act b g * act c g) →
  ∀ f : (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) → G, (∀ a a', f (a + a') = f a * f a') →
  (∀ (c : 𝓞 D.F) a, f (Ideal.Quotient.mk (w0 ^ r) c • a) = act (algebraMap (𝓞 D.F) D.O c) (f a)) → Function.Injective f →
  (∀ g, (∀ c ∈ w0 ^ r, act (algebraMap (𝓞 D.F) D.O c) g = 1) → ∃ a, f a = g) →
  ∃ l : D.La → G, (∀ x y, l (x + y) = l x * l y) ∧ (∀ (b : D.O) x, l (b • x) = act b (l x)) ∧
    (∀ x, l x = 1 ↔ x ∈ wSub D w0 r) ∧ ∀ g, (∀ c ∈ w0 ^ r, act (algebraMap (𝓞 D.F) D.O c) g = 1) → ∃ y, l y = g := by
  intro p _ D w0 r hw hp G _ act hmul hone hcomp hadd f hfadd hfsm hfinj hfonto
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨fun _ => 1, fun _ _ => (_root_.mul_one 1).symm, fun b _ => (act_one_eq act hmul b).symm,
      fun x => ?_, fun g hg => ⟨0, ?_⟩⟩
    · simp only [true_iff]
      have hx : x = algebraMap (𝓞 D.F) D.O 1 • x := by simp
      rw [hx]
      exact Submodule.subset_span ⟨1, by simp, x, rfl⟩
    · have h1 := hg 1 (by simp)
      rw [map_one, hone] at h1
      exact h1.symm
  · haveI := isLocalRing_quot_pow w0 r hr.ne'
    letI : Module D.O (Additive G) := actModule act hmul hone hcomp hadd
    letI : Module (𝓞 D.F) (Additive G) := Module.compHom (Additive G) (algebraMap (𝓞 D.F) D.O)
    haveI : IsScalarTower (𝓞 D.F) D.O (Additive G) := ⟨fun c b x => by
      show (c • b) • x = algebraMap (𝓞 D.F) D.O c • (b • x)
      rw [Algebra.smul_def, mul_smul]⟩
    letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
    haveI : IsScalarTower (𝓞 D.F) D.O D.La := ⟨fun c b x => by
      show (c • b) • x = algebraMap (𝓞 D.F) D.O c • (b • x)
      rw [Algebra.smul_def, mul_smul]⟩
    have hsm : ∀ (b : D.O) (x : Additive G), b • x = Additive.ofMul (act b x.toMul) := fun _ _ => rfl
    let T : Submodule D.O (Additive G) :=
      { carrier := {x | ∀ c ∈ w0 ^ r, act (algebraMap (𝓞 D.F) D.O c) x.toMul = 1}
        add_mem' := fun {x y} hx hy c hc => by
          show act _ (x.toMul * y.toMul) = 1
          rw [hmul, hx c hc, hy c hc, _root_.mul_one]
        zero_mem' := fun c _ => act_one_eq act hmul _
        smul_mem' := fun b x hx c hc => by
          show act _ (act b x.toMul) = 1
          rw [← hcomp, Algebra.commutes, hcomp, hx c hc, act_one_eq act hmul] }
    have hf0 : f 0 = 1 := by
      have h := hfadd 0 0
      rw [add_zero] at h
      exact left_eq_mul.1 h
    have hfT : ∀ a, Additive.ofMul (f a) ∈ T := fun a c hc => by
      show act _ (f a) = 1
      rw [← hfsm, Ideal.Quotient.eq_zero_iff_mem.2 hc, zero_smul, hf0]
    let fl : (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) →ₗ[𝓞 D.F] T :=
      { toFun := fun a => ⟨Additive.ofMul (f a), hfT a⟩
        map_add' := fun a a' => Subtype.ext (by
          show Additive.ofMul (f (a + a')) = Additive.ofMul (f a) + Additive.ofMul (f a')
          rw [hfadd]; rfl)
        map_smul' := fun c a => Subtype.ext (by
          show Additive.ofMul (f (c • a)) = algebraMap (𝓞 D.F) D.O c • Additive.ofMul (f a)
          rw [← algebraMap_smul (𝓞 D.F ⧸ w0 ^ r) c a, Ideal.Quotient.algebraMap_eq, hfsm]
          rfl) }
    have hfl : Function.Bijective fl := by
      refine ⟨fun a a' h => hfinj (congrArg (fun t : T => (t : Additive G).toMul) h), fun t => ?_⟩
      obtain ⟨a, ha⟩ := hfonto (t : Additive G).toMul t.2
      exact ⟨a, Subtype.ext (by show Additive.ofMul (f a) = _; rw [ha]; rfl)⟩
    let eT : T ≃ₗ[𝓞 D.F] (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) := (LinearEquiv.ofBijective fl hfl).symm
    obtain ⟨g, hgs, hgsm, hgker⟩ := GlobalTheory.T.level_quotient_module_surjection p D w0 r hw
    let gl : D.La →ₗ[𝓞 D.F] (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) :=
      { toFun := g
        map_add' := g.map_add
        map_smul' := fun c x => by
          show g (algebraMap (𝓞 D.F) D.O c • x) = c • g x
          rw [hgsm, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul] }
    have hker : LinearMap.ker gl = (wSub D w0 r).restrictScalars (𝓞 D.F) := by
      ext x
      rw [LinearMap.mem_ker, Submodule.restrictScalars_mem]
      exact hgker x
    let eL : (D.La ⧸ wSub D w0 r) ≃ₗ[𝓞 D.F] (Fin (D.m * D.n) → 𝓞 D.F ⧸ w0 ^ r) :=
      (Submodule.Quotient.restrictScalarsEquiv (𝓞 D.F) (wSub D w0 r)).symm ≪≫ₗ
        Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ gl.quotKerEquivOfSurjective hgs
    obtain ⟨φ, hφs, hφk⟩ := GlobalTheory.T.order_surjects_matrix_algebra_mod_prime_power p D w0 r hw hp
    obtain ⟨e⟩ := GlobalTheory.T.morita_nonempty_equiv_of_local_quotient_matrix (𝓞 D.F) (w0 ^ r) inferInstance D.m D.n D.m_pos D.O φ hφs hφk
      (D.La ⧸ wSub D w0 r) T eL eT
    refine ⟨fun x => ((e (Submodule.Quotient.mk x) : T) : Additive G).toMul, fun x y => ?_, fun b x => ?_,
      fun x => ?_, fun g hg => ?_⟩
    · simp only [Submodule.Quotient.mk_add, map_add, Submodule.coe_add, toMul_add]
    · simp only [Submodule.Quotient.mk_smul, map_smul, Submodule.coe_smul, hsm, toMul_ofMul]
    · rw [toMul_eq_one, ZeroMemClass.coe_eq_zero, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]
    · obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (e.symm ⟨Additive.ofMul g, hg⟩)
      refine ⟨y, ?_⟩
      simp only [hy, LinearEquiv.apply_symm_apply, toMul_ofMul]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeakSectionSmallDbarEnergy
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem peak_isSecOn {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (la : La) (i : ι) (W : Set Y) (hW : W ⊆ (A.chart i).source)
    (u : V n → ℂ) (hu : Differentiable ℂ u) :
    A.IsSecOn la W (fun j y => A.g la j i y * u (A.chart i y)) := by
  refine ⟨fun j => ?_, fun j l y hy hj hl => ?_⟩
  · have hsub : (A.chart j).target ∩ (A.chart j).symm ⁻¹' W ⊆ ovl A.chart j i :=
      fun v hv => ⟨hv.1, hW hv.2⟩
    have h1 := (A.holo_g la j i).mono hsub
    have h2 := hu.comp_differentiableOn ((A.holo_trans j i).mono hsub)
    exact h1.mul h2
  · show A.g la j i y * _ = A.g la j l y * (A.g la l i y * _)
    rw [A.g_cocycle la j l i y hj hl (hW hy)]; ring

theorem peak_section : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (H G : La) (i : ι) (p : V n) (ρ c : ℝ) (q f : V n → ℂ), 0 < ρ → 0 < c → closedBall p ρ ⊆ (A.chart i).target → Differentiable ℂ q → Differentiable ℂ f → (∀ v ∈ closedBall p ρ, c * ‖v - p‖ ^ 2 ≤ A.ph H i ((A.chart i).symm v) - 2 * (q v).re) → ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ, ∃ F0 : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) F0 ∧ (∀ v ∈ ball p (ρ / 2), F0 i ((A.chart i).symm v) = f v * Complex.exp (k * q v)) ∧ (∀ j y, y ∉ (A.chart i).source ∩ A.chart i ⁻¹' ball p ρ → F0 j y = 0) ∧ n1 C (G + k • H) F0 ≤ ENNReal.ofReal (K * Real.exp (-(c * ρ ^ 2 / 4) * k)) := by
  intro n Y _ _ _ _ _ ι La _ A C H G i p ρ c q f hρ hc hball hq hf hpeak
  obtain ⟨χ, hχs, hχsupp, hχ1⟩ := GlobalTheory.T.smooth_bump_chart_ball_halfOne n Y ι La A i p ρ hρ hball
  obtain ⟨K0, hK0, hcut⟩ := GlobalTheory.T.n1_cutoff_mul_section_le_lintegral n Y ι La A C χ hχs
  set W : Set Y := (A.chart i).source ∩ A.chart i ⁻¹' ball p ρ with hWdef
  set Wi : Set Y := (A.chart i).source ∩ A.chart i ⁻¹' ball p (ρ / 2) with hWidef
  have hWo : IsOpen W := (A.chart i).isOpen_inter_preimage isOpen_ball
  have hWio : IsOpen Wi := (A.chart i).isOpen_inter_preimage isOpen_ball
  have hWs : W ⊆ (A.chart i).source := Set.inter_subset_left
  set Z : Set Y := W \ Wi with hZdef
  have hZm : MeasurableSet Z := hWo.measurableSet.diff hWio.measurableSet
  have hZloc : ∀ y, y ∉ Z → ∀ᶠ x in 𝓝 y, χ x = χ y := by
    intro y hy
    by_cases hyW : y ∈ W
    · have hyi : y ∈ Wi := by
        by_contra h
        exact hy ⟨hyW, h⟩
      filter_upwards [hWio.mem_nhds hyi] with x hx
      rw [hχ1 x hx.1 hx.2, hχ1 y hyi.1 hyi.2]
    · have hns : y ∉ tsupport χ := fun h => hyW (hχsupp h)
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hns] with x hx
      rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hns]
  have hKc : IsCompact ((A.chart i).symm '' closedBall p ρ) :=
    (isCompact_closedBall p ρ).image_of_continuousOn ((A.chart i).continuousOn_symm.mono hball)
  have hWK : Z ∩ W ⊆ (A.chart i).symm '' closedBall p ρ := fun y hy =>
    ⟨A.chart i y, ball_subset_closedBall hy.2.2, (A.chart i).left_inv hy.2.1⟩
  have hfin : A.mu (Z ∩ W) ≠ ⊤ :=
    ((measure_mono hWK).trans_lt (ap_mu_compact A _ hKc)).ne
  have hcont : ContinuousOn (fun v => ‖f v‖ ^ 2 *
      Real.exp (-A.ph (A.kap + G) i ((A.chart i).symm v))) (closedBall p ρ) :=
    (hf.continuous.continuousOn.norm.pow 2).mul
      (((A.smooth_ph (A.kap + G) i).continuousOn.mono hball).neg.rexp)
  obtain ⟨M, hM⟩ := (isCompact_closedBall p ρ).exists_bound_of_continuousOn hcont
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p (mem_closedBall_self hρ.le))
  refine ⟨K0 * (M * (A.mu (Z ∩ W)).toReal), by positivity, fun k => ?_⟩
  have hu : Differentiable ℂ (fun v => f v * Complex.exp (k * q v)) :=
    hf.mul ((hq.const_mul _).cexp)
  have hsec := peak_isSecOn A (A.kap + (G + k • H)) i W hWs _ hu
  refine ⟨_, GlobalTheory.T.smoothSection_cutoff_mul_holomorphic n Y ι La A _ W χ _ hWo hχs hχsupp hsec, ?_, ?_, ?_⟩
  · intro v hv
    have hvt : v ∈ (A.chart i).target :=
      hball (ball_subset_closedBall (ball_subset_ball (by linarith) hv))
    have hs := (A.chart i).map_target hvt
    have hr := (A.chart i).right_inv hvt
    have h1 : χ ((A.chart i).symm v) = 1 := hχ1 _ hs (by rw [hr]; exact hv)
    simp only [h1, A.g_self _ i hs, hr]
    simp
  · intro j y hy
    have hns : y ∉ tsupport χ := fun h => hy (hχsupp h)
    simp [image_eq_zero_of_notMem_tsupport hns]
  · refine (hcut (G + k • H) W Z _ hWo hχsupp hsec hZm hZloc).trans ?_
    have hbd : ∀ y ∈ Z ∩ W, ENNReal.ofReal (A.nsq (A.kap + (G + k • H))
        (fun j y => A.g (A.kap + (G + k • H)) j i y *
          (f (A.chart i y) * Complex.exp (k * q (A.chart i y)))) y) ≤
        ENNReal.ofReal (M * Real.exp (-(c * ρ ^ 2 / 4) * k)) := by
      intro y hy
      apply ENNReal.ofReal_le_ofReal
      have hs : y ∈ (A.chart i).source := hy.2.1
      have hcb : A.chart i y ∈ closedBall p ρ := ball_subset_closedBall hy.2.2
      have hout : ρ / 2 ≤ ‖A.chart i y - p‖ := by
        by_contra h
        exact hy.1.2 ⟨hs, by simpa [mem_ball, dist_eq_norm] using not_le.1 h⟩
      rw [A.nsq_chart _ _ i hs (hsec.2 _ i y hy.2 (A.mem_pick y) hs)]
      have h1 := hM _ hcb
      have h2 := hpeak _ hcb
      rw [(A.chart i).left_inv hs] at h1 h2
      rw [Real.norm_of_nonneg (by positivity)] at h1
      have h3 : c * ρ ^ 2 / 4 ≤ c * ‖A.chart i y - p‖ ^ 2 := by
        have : (ρ / 2) ^ 2 ≤ ‖A.chart i y - p‖ ^ 2 := by gcongr
        nlinarith
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have e : ‖A.g (A.kap + (G + k • H)) i i y *
          (f (A.chart i y) * Complex.exp (k * q (A.chart i y)))‖ ^ 2 *
          Real.exp (-A.ph (A.kap + (G + k • H)) i y) =
          (‖f (A.chart i y)‖ ^ 2 * Real.exp (-A.ph (A.kap + G) i y)) *
          Real.exp (-(A.ph H i y - 2 * (q (A.chart i y)).re) * k) := by
        rw [A.g_self _ i hs, one_mul, norm_mul, Complex.norm_exp, ← add_assoc,
          A.ph_add _ (k • H) i y hs, A.aap_ph_nsmul H k i hs, mul_pow, ← Real.exp_nat_mul,
          mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
        congr 2
        simp
        ring
      refine e.le.trans ?_
      refine mul_le_mul h1 (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hM0
      nlinarith
    have hint := setLIntegral_mono' (μ := A.mu) (hZm.inter hWo.measurableSet) hbd
    rw [setLIntegral_const] at hint
    refine (mul_le_mul_right hint _).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul hK0, ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    congr 1
    ring

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotPDivGroup
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory.HTPair

theorem exists_quotPDivGroup : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsLocalRing O] (G : PDivGroup p O) (τ : QuotTower G), ∃ (H : PDivGroup p O)
    (q : ∀ m, τ.B m →ₐc[O] H.A m), (∀ m, Function.Surjective (q m)) ∧
    (∀ m, RingHom.ker (q m) = torsionIdeal O (τ.B m) (p ^ m)) ∧
    ∀ m b, H.res m (q (m + 1) b) = q m (τ.r m b) := by
  intro p _ O _ _ _ G τ
  have hex := fun m => GlobalTheory.T.exists_hopf_quotient_ker_eq_torsionIdeal O (τ.B m) (p ^ m)
  choose D iR iH iC q hq hk using hex
  letI := iR
  letI := iH
  letI := iC
  have hB1 : ∀ m (x : PrimeSpectrum O),
      fibreDim (τ.B m ⧸ torsionIdeal O (τ.B m) (p ^ m)) x = p ^ (m * G.height) := by
    intro m x
    have h := GlobalTheory.T.torsion_fibreDim_quotient_pDivGroupLevel p O G 1 m le_rfl (τ.B m)
    rw [show 1 + m = m + 1 from Nat.add_comm 1 m] at h
    exact h (τ.j m) (τ.ρ m) (τ.ρ_j m) (τ.tors_le m) x
  have hB2 : ∀ m (x : PrimeSpectrum O),
      fibreDim (τ.B (m + 1) ⧸ torsionIdeal O (τ.B (m + 1)) (p ^ m)) x = p ^ (m * G.height) := by
    intro m x
    have h := GlobalTheory.T.torsion_fibreDim_quotient_pDivGroupLevel p O G 2 m (by norm_num) (τ.B (m + 1))
    rw [show 2 + m = m + 1 + 1 by omega] at h
    exact h (τ.j (m + 1)) (τ.ρ (m + 1)) (τ.ρ_j (m + 1)) (τ.tors_le (m + 1)) x
  haveI hfin : ∀ m, Module.Finite O (D m) := fun m =>
    Module.Finite.of_surjective (q m : τ.B m →ₗ[O] D m) (hq m)
  have hD : ∀ m (x : PrimeSpectrum O), fibreDim (D m) x = p ^ (m * G.height) := by
    intro m x
    have hk' : RingHom.ker (q m : τ.B m →ₐ[O] D m) = torsionIdeal O (τ.B m) (p ^ m) := hk m
    have e := ((Ideal.quotientEquivAlgOfEq O hk').symm.trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := (q m : τ.B m →ₐ[O] D m)) (hq m))).toLinearEquiv
    rw [← hB1 m x]
    exact (fibreDim_congr e x).symm
  have hPR := fun m => GlobalTheory.T.projective_rankAtStalk_of_const_fibreDim O (D m) (p ^ (m * G.height)) (hD m)
  haveI hproj : ∀ m, Module.Projective O (D m) := fun m => (hPR m).1
  have hle : ∀ m, RingHom.ker (q (m + 1)) ≤ RingHom.ker ((q m).comp (τ.r m)) := by
    intro m b hb
    rw [hk] at hb
    have h1 : τ.r m b ∈ torsionIdeal O (τ.B m) (p ^ (m + 1)) := by
      rw [← map_torsionIdeal (τ.r_surjective m)]
      exact Ideal.mem_map_of_mem (τ.r m : τ.B (m + 1) →ₐ[O] τ.B m) hb
    have h2 : τ.r m b ∈ RingHom.ker (q m) := by
      rw [hk]
      exact torsionIdeal_le_of_dvd (pow_dvd_pow p (Nat.le_succ m)) h1
    rw [RingHom.mem_ker] at h2 ⊢
    exact h2
  let res := fun m => liftSurj (q (m + 1)) (hq (m + 1)) ((q m).comp (τ.r m)) (hle m)
  have hres : ∀ m b, res m (q (m + 1) b) = q m (τ.r m b) := fun m b => liftSurj_apply ..
  have hres_surj : ∀ m, Function.Surjective (res m) := by
    intro m d
    obtain ⟨c, rfl⟩ := hq m d
    obtain ⟨b, rfl⟩ := τ.r_surjective m c
    exact ⟨_, hres m b⟩
  have hker : ∀ m, RingHom.ker (res m) = torsionIdeal O (D (m + 1)) (p ^ m) := by
    intro m
    refine ker_eq_of_fibreDim_eq (res m : D (m + 1) →ₐ[O] D m) (hres_surj m) _ ?_ fun x => ?_
    · rw [← map_torsionIdeal (hq (m + 1))]
      refine Ideal.map_le_iff_le_comap.2 fun b hb => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change res m (q (m + 1) b) = 0
      rw [hres, ← RingHom.mem_ker, hk, ← map_torsionIdeal (τ.r_surjective m)]
      exact Ideal.mem_map_of_mem (τ.r m : τ.B (m + 1) →ₐ[O] τ.B m) hb
    · let φ : τ.B (m + 1) →ₐ[O] D (m + 1) ⧸ torsionIdeal O (D (m + 1)) (p ^ m) :=
        (Ideal.Quotient.mkₐ O _).comp (q (m + 1) : τ.B (m + 1) →ₐ[O] D (m + 1))
      have hφ : Function.Surjective φ :=
        (Ideal.Quotient.mkₐ_surjective O _).comp (hq (m + 1))
      have hkφ : RingHom.ker φ = torsionIdeal O (τ.B (m + 1)) (p ^ m) := by
        ext b
        rw [RingHom.mem_ker]
        change Ideal.Quotient.mk _ (q (m + 1) b) = 0 ↔ _
        rw [Ideal.Quotient.eq_zero_iff_mem, ← map_torsionIdeal (hq (m + 1))]
        constructor
        · intro hb
          obtain ⟨c, hc, e⟩ := (Ideal.mem_map_iff_of_surjective
            (q (m + 1) : τ.B (m + 1) →ₐ[O] D (m + 1)) (hq (m + 1))).1 hb
          have h3 : b - c ∈ RingHom.ker (q (m + 1)) := by
            rw [RingHom.mem_ker, map_sub, sub_eq_zero]
            exact e.symm
          rw [hk] at h3
          have h4 := torsionIdeal_le_of_dvd (R := O) (A := τ.B (m + 1))
            (pow_dvd_pow p (Nat.le_succ m)) h3
          simpa using Ideal.add_mem _ h4 hc
        · intro hb
          exact Ideal.mem_map_of_mem (q (m + 1) : τ.B (m + 1) →ₐ[O] D (m + 1)) hb
      have e := ((Ideal.quotientEquivAlgOfEq O hkφ).symm.trans
        (Ideal.quotientKerAlgEquivOfSurjective hφ)).toLinearEquiv
      rw [hD, ← hB2 m x]
      exact (fibreDim_congr e x).symm
  let H : PDivGroup p O :=
    { height := G.height
      A := D
      commRing := iR
      hopf := iH
      cocomm := iC
      finite := hfin
      projective := hproj
      rank_eq := fun m x => (hPR m).2 x
      res := res
      res_surjective := hres_surj
      ker_res := hker }
  exact ⟨H, q, hq, hk, hres⟩

end GlobalTheory.HTPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeriesOfCompatible
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.CChartLimit

theorem smod_span_iff {R : Type} [CommRing R] (a x y : R) (n : ℕ) :
    x ≡ y [SMOD ((Ideal.span {a}) ^ n • ⊤ : Submodule R R)] ↔ a ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]

theorem exists_series_of_compatible : ∀ (p : ℕ) (O σ : Type) [CommRing O] [Fintype σ]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (A : ℕ → Type) [∀ n, CommRing (A n)]
    [∀ n, Algebra O (A n)], (∀ n, IsHausdorff (Ideal.span {(p : A n)}) (A n)) →
    ∀ (x : ∀ n, σ → A n) (E : ∀ n, MvPowerSeries σ O →ₐ[O] A n) (t : ∀ n, A n),
    (∀ n, IsEval p (x n) (E n)) → (∀ n, ∃ f, E n f = t n) →
    (∀ n f, E (n + 1) f = t (n + 1) → E n f = t n) →
    (∀ m N : ℕ, ∃ n, ∀ f, E n f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) →
    ∃ g, ∀ n, E n g = t n := by
  intro p O σ _ _ _ A _ _ hH x E t hE hs hstep hker
  classical
  choose g hg using hs
  have hdown : ∀ n d f, E (n + d) f = t (n + d) → E n f = t n := by
    intro n d f
    induction d with
    | zero => exact id
    | succ d ih => exact fun hf => ih (hstep (n + d) f hf)
  have hgk : ∀ n k, n ≤ k → E n (g k) = t n := by
    intro n k hnk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnk
    exact hdown n d _ (hg _)
  choose K hK using hker
  let K' : ℕ → ℕ := fun j => (Finset.range (j + 1)).sup (fun i => max i (K i i))
  have hK'mono : Monotone K' := fun a b hab =>
    Finset.sup_mono (Finset.range_subset_range.mpr (by omega))
  have hK'ge : ∀ j, j ≤ K' j ∧ K j j ≤ K' j := fun j => by
    have := Finset.le_sup (f := fun i => max i (K i i)) (Finset.mem_range.mpr (Nat.lt_succ_self j))
    exact ⟨le_trans (le_max_left _ _) this, le_trans (le_max_right _ _) this⟩
  let h : ℕ → MvPowerSeries σ O := fun j => g (K' j)
  have hcau : ∀ j j', j ≤ j' → ∀ α : σ →₀ ℕ, α.degree < j →
      (p : O) ^ j ∣ coeff α (h j) - coeff α (h j') := by
    intro j j' hjj α hα
    have h0 : E (K j j) (h j - h j') = 0 := by
      rw [map_sub, hgk _ _ (hK'ge j).2, hgk _ _ ((hK'ge j).2.trans (hK'mono hjj)), sub_self]
    have := hK j j _ h0 α hα
    rwa [map_sub] at this
  have hc : ∀ α : σ →₀ ℕ, ∃ L : O, ∀ n, (p : O) ^ n ∣ coeff α (h (n + α.degree + 1)) - L := by
    intro α
    have hpre : IsPrecomplete (Ideal.span {(p : O)}) O := inferInstance
    obtain ⟨L, hL⟩ := hpre.prec (f := fun n => coeff α (h (n + α.degree + 1))) (by
      intro m n hmn
      rw [smod_span_iff]
      have := hcau (m + α.degree + 1) (n + α.degree + 1) (by omega) α (by omega)
      exact (pow_dvd_pow _ (by omega)).trans this)
    exact ⟨L, fun n => (smod_span_iff _ _ _ _).1 (hL n)⟩
  choose L hL using hc
  let μ : MvPowerSeries σ O := L
  have hμ : ∀ α, coeff α μ = L α := fun α => rfl
  refine ⟨μ, fun n => ?_⟩
  haveI := hH n
  apply (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : A n)})).2
  intro m
  rw [smod_span_iff]
  obtain ⟨N, hN⟩ := (hE n).2 m
  have hj : E n (h (m + N + n)) = t n :=
    hgk n (K' (m + N + n)) (le_trans (by omega) (hK'ge (m + N + n)).1)
  have hd : ∀ α : σ →₀ ℕ, α.degree < N →
      (p : O) ^ m ∣ coeff α μ - coeff α (h (m + N + n)) := by
    intro α hα
    have h1 := hL α m
    have h2 := hcau (m + α.degree + 1) (m + N + n) (by omega) α (by omega)
    have h2' : (p : O) ^ m ∣ coeff α (h (m + α.degree + 1)) - coeff α (h (m + N + n)) :=
      (pow_dvd_pow _ (by omega)).trans h2
    have e : coeff α μ - coeff α (h (m + N + n)) =
        (coeff α (h (m + α.degree + 1)) - coeff α (h (m + N + n))) -
          (coeff α (h (m + α.degree + 1)) - L α) := by rw [hμ]; ring
    rw [e]; exact dvd_sub h2' h1
  choose q hq using hd
  let Q : MvPowerSeries σ O := fun α => if hα : α.degree < N then q α hα else 0
  have hQ : ∀ α (hα : α.degree < N), coeff α Q = q α hα := fun α hα => by
    show (if hα : α.degree < N then q α hα else 0) = q α hα
    rw [dif_pos hα]
  let R := μ - h (m + N + n) - (p : O) ^ m • Q
  have hR : ∀ α : σ →₀ ℕ, α.degree < N → coeff α R = 0 := by
    intro α hα
    simp only [R, map_sub, MvPowerSeries.coeff_smul, hQ α hα, smul_eq_mul, hq α hα, sub_self]
  have hER := hN R hR
  have hsplit : E n μ - t n = E n R + (p : A n) ^ m * E n Q := by
    have hμeq : μ = h (m + N + n) + ((p : O) ^ m • Q + R) := by simp only [R]; abel
    rw [hμeq, map_add, map_add, hj, map_smul, Algebra.smul_def, map_pow, map_natCast]
    ring
  rw [hsplit]
  exact dvd_add hER (dvd_mul_right _ _)

end GlobalTheory.CChartLimit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVerschiebungOfDieudonneFunctorBaseStatement
section
open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_verschiebung_of_dieudonneFunctorBase : ∀ (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Dieu.Base p (fun _ _ _ => True)), ∃ V : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k), B.M G trivial →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)] B.M G trivial, (∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k) (m : B.M G trivial), B.F G trivial (V G m) = p • m) ∧ ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : GlobalTheory.PDivGroup p k) (m : B.M G trivial), V G (B.F G trivial m) = p • m := by
  first | exact @GlobalTheory.Dieu.exists_V_of_base | exact GlobalTheory.Dieu.exists_V_of_base | (intros; apply GlobalTheory.Dieu.exists_V_of_base <;> assumption)
end

