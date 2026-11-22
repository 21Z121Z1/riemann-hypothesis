import Mathlib

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.EulerA
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.Euler

open MeasureTheory Set

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
  [LocallyCompactSpace H] [SecondCountableTopology H] {ν : Measure H} [ν.IsHaarMeasure] {K : Subgroup H}

theorem pres_right (hK : MeasurableSet (K : Set H)) (h1 : ν K = 1) {k : H} (hk : k ∈ K) :
    MeasurePreserving (· * k) ν ν := by
  have e := Measure.isMulLeftInvariant_eq_smul (ν.map (· * k)) ν
  have m : Measurable fun x : H => x * k := measurable_mul_const k
  have e2 := congrArg (· (K : Set H)) e
  have p : (fun x : H => x * k) ⁻¹' K = K := Set.ext fun x => K.mul_mem_cancel_right hk
  simp only [Measure.map_apply m hK, p, h1, Measure.coe_nnreal_smul_apply, mul_one] at e2
  refine ⟨m, ?_⟩
  rw [e, show Measure.haarScalarFactor (ν.map (· * k)) ν = 1 by exact_mod_cast e2.symm, one_smul]

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace G] [SecondCountableTopology G] {μ : Measure G} [μ.IsHaarMeasure]

theorem factor (hK : MeasurableSet (K : Set H)) (h1 : ν K = 1) (i : H →* G) (hi : Continuous i) (π : G → H) (hπ : Continuous π)
    (e : ∀ u g, π (i u * g) = u * π g) {f : G → ℂ} {l : H → ℂ} (hf : Integrable f μ)
    (hl : ∀ u g, π g = 1 → f (i u * g) = l u * f g) (hl1 : ∀ u ∈ K, l u = 1) {A : Set G} (hA : MeasurableSet A)
    (hAi : ∀ u g, i u * g ∈ A ↔ g ∈ A) : ∫ g in A, f g ∂μ = (∫ u, l u ∂ν) * ∫ g in A ∩ π ⁻¹' K, f g ∂μ := by
  let S : Set (H × G) := {p | p.1⁻¹ * π p.2 ∈ K}
  have hS : MeasurableSet S := (continuous_fst.inv.mul (hπ.comp continuous_snd)).measurable hK
  let Φ : H × G → ℂ := S.indicator fun p => A.indicator f p.2
  have vol : ∀ g, ν {u | u⁻¹ * π g ∈ K} = 1 := fun g => by
    rw [← h1, ← measure_preimage_mul ν (π g)⁻¹ K]
    congr 1
    ext u
    exact (K.inv_mem_iff.symm.trans (by simp))
  have mS : ∀ g, MeasurableSet {u | u⁻¹ * π g ∈ K} := fun g => (continuous_inv.mul continuous_const).measurable hK
  have sl : ∀ g, (fun u => Φ (u, g)) = {u | u⁻¹ * π g ∈ K}.indicator fun _ => A.indicator f g := fun g => rfl
  have hfA := hf.indicator hA
  have iΦ : Integrable Φ (ν.prod μ) := by
    refine (integrable_prod_iff' (hfA.1.comp_snd.indicator hS)).2 ⟨Filter.Eventually.of_forall fun g => ?_, ?_⟩
    · rw [sl, integrable_indicator_iff (mS g)]
      exact integrableOn_const (by simp [vol])
    · refine hfA.norm.congr (Filter.Eventually.of_forall fun g => ?_)
      have : (fun u => ‖Φ (u, g)‖) = {u | u⁻¹ * π g ∈ K}.indicator fun _ => ‖A.indicator f g‖ :=
        funext fun u => by rw [congrFun (sl g) u, norm_indicator_eq_indicator_norm]
      show _ = ∫ u, ‖Φ (u, g)‖ ∂ν
      rw [this, integral_indicator_const _ (mS g), Measure.real, vol]
      simp
  have sh : MeasurePreserving (fun p : H × G => (p.1, i p.1 * p.2)) (ν.prod μ) (ν.prod μ) :=
    (MeasurePreserving.id ν).skew_product (g := fun u g => i u * g) ((hi.comp continuous_fst).mul continuous_snd).measurable
      (Filter.Eventually.of_forall fun u => map_mul_left_eq_self μ (i u))
  have i2 := sh.integrable_comp_of_integrable iΦ
  have mB : MeasurableSet (A ∩ π ⁻¹' K) := hA.inter (hπ.measurable hK)
  calc ∫ g in A, f g ∂μ = ∫ g, ∫ u, Φ (u, g) ∂ν ∂μ := by
        rw [← integral_indicator hA]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only [sl]
        rw [integral_indicator_const _ (mS g), Measure.real, vol]
        simp
    _ = ∫ u, ∫ g, Φ (u, i u * g) ∂μ ∂ν := by
        rw [← integral_integral_swap (f := fun u g => Φ (u, g)) iΦ]
        exact integral_congr_ae (Filter.Eventually.of_forall fun u =>
          (integral_mul_left_eq_self (fun g => Φ (u, g)) (i u)).symm)
    _ = ∫ g, ∫ u, Φ (u, i u * g) ∂ν ∂μ := integral_integral_swap (f := fun u g => Φ (u, i u * g)) i2
    _ = _ := by
        rw [← integral_const_mul, ← integral_indicator mB]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        by_cases hg : g ∈ A ∩ π ⁻¹' K
        · have z : π (i (π g)⁻¹ * g) = 1 := by rw [e, inv_mul_cancel]
          have w : ∀ u, f (i u * g) = l (u * π g) * f (i (π g)⁻¹ * g) := fun u => by
            rw [← hl _ _ z, ← mul_assoc, ← map_mul, mul_inv_cancel_right]
          have w1 := w 1
          rw [map_one, one_mul, one_mul, hl1 _ hg.2, one_mul] at w1
          have : ∀ u, Φ (u, i u * g) = l (u * π g) * f g := fun u => by
            simp only [Φ]
            rw [indicator_of_mem (show (u, i u * g) ∈ S by simpa [S, e] using hg.2), indicator_of_mem ((hAi u g).2 hg.1), w, w1]
          simp only [this]
          rw [indicator_of_mem hg, integral_mul_const,
            (pres_right hK h1 hg.2).integral_comp (Homeomorph.mulRight (π g)).measurableEmbedding l]
        · have : ∀ u, Φ (u, i u * g) = 0 := fun u => by
            simp only [Φ]
            by_cases h2 : π g ∈ K
            · exact indicator_apply_eq_zero.2 fun _ => indicator_of_notMem (fun h => hg ⟨(hAi u g).1 h, h2⟩) _
            · exact indicator_of_notMem (by simpa [S, e] using h2) _
          simp only [this]
          rw [indicator_of_notMem hg, integral_zero]

end GlobalTheory.ThK.Dbl.Euler

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.FarRight
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.An

open MeasureTheory Filter Topology

def BC {X : Type} [TopologicalSpace X] (f : X → ℂ) : Prop := Continuous f ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C

section

variable {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] {f g : X → ℂ}

theorem BC.mul (h : BC f) (h' : BC g) : BC fun x => f x * g x := by
  obtain ⟨a, C, hC⟩ := h
  obtain ⟨b, C', hC'⟩ := h'
  exact ⟨a.mul b, C * C', fun x => (norm_mul_le _ _).trans
    (mul_le_mul (hC x) (hC' x) (norm_nonneg _) ((norm_nonneg _).trans (hC x)))⟩

theorem BC.star (h : BC f) : BC fun x => star (f x) := ⟨h.1.star, h.2.imp fun _ h x => (norm_star _).trans_le (h x)⟩

theorem BC.comp (h : BC f) {u : X' → X} (hu : Continuous u) : BC fun x => f (u x) := ⟨h.1.comp hu, h.2.imp fun _ h _ => h _⟩

theorem BC.int [MeasurableSpace X] [OpensMeasurableSpace X] (h : BC f) (μ : Measure X) [IsFiniteMeasure μ] : Integrable f μ :=
  .of_bound h.1.aestronglyMeasurable _ (.of_forall h.2.choose_spec)

end

variable {G H : Type} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  (ν : Measure G) [IsFiniteMeasure ν] (ρ : Measure H) [IsFiniteMeasure ρ] {φ : G → ℂ}

theorem at_value {θ : H × G → ℂ} (hθ : BC θ) (hφ : BC φ) :
    ∫ y, (∫ g, θ (g, y.1) * star (θ (g, y.2)) ∂ρ) * (φ y.2 * star (φ y.1)) ∂ν.prod ν =
      ∫ g, (∫ h, φ h * star (θ (g, h)) ∂ν) * star (∫ h, φ h * star (θ (g, h)) ∂ν) ∂ρ := by
  simp only [← integral_mul_const]
  rw [integral_integral_swap (f := fun (y : G × G) g => θ (g, y.1) * star (θ (g, y.2)) * (φ y.2 * star (φ y.1)))
    (BC.int (((hθ.comp (u := fun y : (G × G) × H => (y.2, y.1.1)) (by fun_prop)).mul
      (hθ.comp (u := fun y : (G × G) × H => (y.2, y.1.2)) (by fun_prop)).star).mul
      ((hφ.comp (by fun_prop)).mul (hφ.comp (by fun_prop)).star)) _)]
  refine integral_congr_ae (.of_forall fun g => ?_)
  simp only [integral_mul_const]
  rw [mul_comm, Complex.star_def, ← integral_conj, ← integral_prod_mul]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [map_mul, Complex.conj_conj]
  ring

theorem far_right [Group G] [ContinuousMul G] (μ : Measure G) [SFinite μ] {k : G × G → ℂ} {w : G → ℂ} (hk : BC k) (hφ : BC φ)
    (hw : Integrable w μ) (h : ∀ h, ∫ h', k (h, h') * φ h' ∂ν = ∫ g, w g * φ (h * g) ∂μ) :
    ∫ y, k y * (φ y.2 * star (φ y.1)) ∂ν.prod ν = ∫ g, w g * ∫ h, φ (h * g) * star (φ h) ∂ν ∂μ := by
  rw [integral_prod _ (BC.int (hk.mul ((hφ.comp continuous_snd).mul (hφ.comp continuous_fst).star)) _)]
  simp only [← mul_assoc, integral_mul_const, h]
  simp only [← integral_mul_const, ← integral_const_mul, mul_assoc]
  obtain ⟨c, C, hC⟩ := (hφ.comp (u := fun y : G × G => y.1 * y.2) (by fun_prop)).mul (hφ.comp continuous_fst).star
  exact integral_integral_swap (f := fun h g => w g * (φ (h * g) * star (φ h)))
    ((hw.comp_snd ν).mul_bdd c.aestronglyMeasurable (.of_forall hC))

theorem ident {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U) {g g' : ℂ → ℂ} (hg : DifferentiableOn ℂ g U)
    (hg' : DifferentiableOn ℂ g' U) {t : ℝ} (h : ∀ s : ℂ, t < s.re → s ∈ U ∧ g s = g' s) {s : ℂ} (hs : s ∈ U) : g s = g' s := by
  have h1 : t < ((t + 1 : ℝ) : ℂ).re := by simp
  refine (hg.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq (hg'.analyticOnNhd hU) hc (h _ h1).1 ?_ hs
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h1] with z hz using (h z hz).2

end GlobalTheory.ThK.Dbl.An

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.HgtCount
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.Hgt

open scoped NNReal ENNReal
open MeasureTheory Topology

theorem exists_cover {A : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A] (ν : Measure A) [ν.IsAddLeftInvariant]
    {X V Z : Set A} (hV : MeasurableSet V) (h0 : ν V ≠ 0) (hZ : ν Z ≠ ⊤) (hXZ : ∀ x ∈ X, ∀ v ∈ V, x + v ∈ Z) :
    ∃ s : Finset A, s.card * ν V ≤ ν Z ∧ ∀ x ∈ X, ∃ y ∈ s, ∃ v ∈ V, ∃ v' ∈ V, x - y = v - v' := by
  classical
  by_contra! h
  let T : A → Set A := fun x => (fun a => -x + a) ⁻¹' V
  have bd : ∀ s : Finset A, (s : Set A) ⊆ X → (s : Set A).PairwiseDisjoint T → s.card * ν V ≤ ν Z := fun s h1 h2 => by
    have := measure_biUnion_finset (μ := ν) h2 fun b _ => measurable_const_add _ hV
    simp only [T, measure_preimage_add, Finset.sum_const, nsmul_eq_mul] at this
    rw [← this]
    exact measure_mono (Set.iUnion₂_subset fun x hx a ha => by simpa using hXZ x (h1 hx) _ ha)
  obtain ⟨v₀, hv₀⟩ := nonempty_of_measure_ne_zero h0
  have key : ∀ k : ℕ, ∃ s : Finset A, s.card = k ∧ (s : Set A) ⊆ X ∧ (s : Set A).PairwiseDisjoint T := fun k => by
    induction k with
    | zero => exact ⟨∅, rfl, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨s, rfl, h1, h2⟩ := ih
      obtain ⟨x, hx, hx'⟩ := h s (bd s h1 h2)
      refine ⟨insert x s, Finset.card_insert_of_notMem fun hs => hx' x hs v₀ hv₀ v₀ hv₀ (by simp), ?_, ?_⟩
      · rw [Finset.coe_insert]; exact Set.insert_subset hx h1
      · rw [Finset.coe_insert]
        exact h2.insert fun y hy _ => Set.disjoint_left.2 fun a ha hb => hx' y hy (-y + a) hb (-x + a) ha (by rw [add_sub_add_right_eq_sub, neg_sub_neg])
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt h0 hZ
  obtain ⟨s, rfl, h1, h2⟩ := key N
  exact hN.not_ge (bd s h1 h2)

theorem integrable_of_count {G : Type} [MeasurableSpace G] (μ : Measure G) {f : G → ℝ} (hf : Measurable f) (h0 : ∀ g, 0 < f g)
    {R : ℝ} (h1 : 1 ≤ R) (hR : ∀ g, f g ≤ R) {C : ℝ≥0∞} (hC : C ≠ ⊤) (b : ℝ≥0)
    (h : ∀ j : ℕ, μ {g | (1 / 2) ^ j ≤ f g} ≤ C * b ^ j) : ∃ t₀ : ℝ, ∀ t, t₀ ≤ t → Integrable (fun g => f g ^ t) μ := by
  classical
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (b + 1) by positivity) (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨k, fun t ht => ⟨(hf.pow_const t).aestronglyMeasurable, ?_⟩⟩
  have t0 : 0 ≤ t := (Nat.cast_nonneg k).trans ht
  let P : ℕ → Set G := fun j => {g | (1 / 2) ^ j ≤ f g ∧ f g ≤ 2 * R * (1 / 2) ^ j}
  have hP : ⋃ j, P j = Set.univ := Set.eq_univ_of_forall fun g => by
    have ex : ∃ j : ℕ, (1 / 2 : ℝ) ^ j ≤ f g := (exists_pow_lt_of_lt_one (h0 g) (by norm_num)).imp fun _ => le_of_lt
    refine Set.mem_iUnion.2 ⟨Nat.find ex, Nat.find_spec ex, ?_⟩
    rcases e : Nat.find ex with _ | j
    · have := hR g; simp; linarith
    · have := Nat.find_min ex (m := j) (by omega)
      have p : (0 : ℝ) < (1 / 2) ^ j := by positivity
      rw [pow_succ]; nlinarith
  set ρ : ℝ≥0∞ := ENNReal.ofReal ((1 / 2) ^ t) * b
  have hρ : ρ < 1 := by
    have : ((1 / 2 : ℝ)) ^ t ≤ (1 / 2) ^ k := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) ht
    rw [lt_div_iff₀ (by positivity)] at hk
    have p : (0 : ℝ) < (1 / 2) ^ t := by positivity
    rw [show ρ = ENNReal.ofReal ((1 / 2) ^ t * b) by rw [ENNReal.ofReal_mul p.le, ENNReal.ofReal_coe_nnreal], ENNReal.ofReal_lt_one]
    nlinarith [b.2, show (0 : ℝ) ≤ b from b.2]
  calc ∫⁻ g, ‖f g ^ t‖ₑ ∂μ = ∫⁻ g in ⋃ j, P j, ‖f g ^ t‖ₑ ∂μ := by rw [hP, Measure.restrict_univ]
    _ ≤ ∑' j, ∫⁻ g in P j, ‖f g ^ t‖ₑ ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' j, ENNReal.ofReal ((2 * R) ^ t) * C * ρ ^ j := ENNReal.tsum_le_tsum fun j => by
      refine (setLIntegral_mono (g := fun _ => ENNReal.ofReal ((2 * R) ^ t) * ENNReal.ofReal ((1 / 2) ^ t) ^ j)
        measurable_const fun g hg => ?_).trans ?_
      · rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (h0 g).le _), ← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_mul_natCast (by norm_num), mul_comm t, Real.rpow_natCast_mul (by norm_num),
          ← Real.mul_rpow (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (h0 g).le hg.2 t0)
      · rw [setLIntegral_const]
        refine (mul_le_mul_right ((measure_mono fun g hg => hg.1).trans (h j)) _).trans_eq ?_
        simp only [ρ, mul_pow]; ring
    _ < ⊤ := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.lt_top)
        (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hρ))

theorem count_grp {R B κ : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Ring B] [Algebra R B] [TopologicalSpace B]
    [IsTopologicalRing B] [T2Space B] [Fintype κ] (c : B ≃ₗ[R] (κ → R)) (hc : Continuous c) (hc' : Continuous c.symm)
    (H : Subgroup Bˣ) (hH : IsClosed (H : Set Bˣ)) {Ω : Set B} (hΩ : IsCompact Ω) {W : Set R} (hW : IsCompact W) :
    ∃ (X : Set R) (U : Set H), IsCompact X ∧ IsCompact U ∧ ∀ (l : Rˣ) (s : Finset R),
      (∀ x ∈ X, ∃ y ∈ s, ∃ w ∈ W, x - y = l * l * w) → ∀ [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant],
        μ {g | l.1 • g.1.1 ∈ Ω ∧ l.1 • (g⁻¹).1.1 ∈ Ω} ≤ (s.card : ℝ≥0∞) ^ Fintype.card κ * μ U := by
  classical
  let W' : Set ((κ → R) × (κ → R)) := (Set.univ.pi fun _ => W) ×ˢ Set.univ.pi fun _ => W
  let Ω' : Set B := (fun y : B × (κ → R) × (κ → R) => 1 + y.1 * c.symm (y.2.1 - y.2.2)) '' Ω ×ˢ W'
  have hΩ' : IsCompact Ω' := (hΩ.prod ((isCompact_univ_pi fun _ => hW).prod (isCompact_univ_pi fun _ => hW))).image (by fun_prop)
  have em : IsClosedEmbedding (fun k : H => Units.embedProduct B k.1) :=
    Units.isClosedEmbedding_embedProduct.comp hH.isClosedEmbedding_subtypeVal
  refine ⟨⋃ k, (fun y => c y k) '' Ω, _, isCompact_iUnion fun k => hΩ.image (by fun_prop),
    em.isCompact_preimage (hΩ'.prod (hΩ'.image MulOpposite.continuous_op)), fun l s hs _ _ μ _ => ?_⟩
  let S : (κ → R) → Set H := fun y => {g | l.1 • (g⁻¹).1.1 ∈ Ω ∧ ∀ k, ∃ w ∈ W, c (l.1 • g.1.1) k - y k = l * l * w}
  have key : ∀ y, ∀ g ∈ S y, ∀ g' ∈ S y, (g⁻¹ * g').1.1 ∈ Ω' := fun y g hg g' hg' => by
    choose w hw e using hg.2
    choose w' hw' e' using hg'.2
    refine ⟨(_, w', w), ⟨hg.1, fun k _ => hw' k, fun k _ => hw k⟩, ?_⟩
    have e1 : g'.1.1 - g.1.1 = l.1 • c.symm (w' - w) := by
      refine c.injective (funext fun k => l.isUnit.mul_left_cancel ?_)
      have := e k
      have := e' k
      simp only [map_smul, map_sub, LinearEquiv.apply_symm_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at *
      linear_combination e' k - e k
    change 1 + l.1 • (g.1⁻¹).1 * c.symm (w' - w) = (g.1⁻¹).1 * g'.1.1
    rw [smul_mul_assoc, ← mul_smul_comm, ← e1, mul_sub, Units.inv_mul, add_sub_cancel]
  refine (measure_mono (t := ⋃ y ∈ Fintype.piFinset fun _ : κ => s, S y) fun g hg => ?_).trans
    ((measure_biUnion_finset_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (μ ((fun k : H => Units.embedProduct B k.1) ⁻¹'
      Ω' ×ˢ (MulOpposite.op '' Ω'))) fun y _ => ?_).trans_eq (by simp)))
  · choose y hy hy' using fun k => hs _ (Set.mem_iUnion.2 ⟨k, _, hg.1, rfl⟩)
    exact Set.mem_iUnion₂.2 ⟨y, Fintype.mem_piFinset.2 hy, hg.2, hy'⟩
  · rcases (S y).eq_empty_or_nonempty with e | ⟨g, hg⟩
    · simp [e]
    · refine (measure_mono ?_).trans_eq (measure_preimage_mul μ g⁻¹ _)
      exact fun g' hg' => ⟨key y g hg g' hg', _, key y g' hg' g hg, by simp⟩

end GlobalTheory.ThK.Dbl.Hgt

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.MemLam
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.Bmp

open Matrix

variable {O K : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]

theorem sep (ψ : AddChar K ℂ) (hψ : ∀ x, (∀ y : O, ψ (x * algebraMap O K y) = 1) ↔ x ∈ (algebraMap O K).range)
    {V : Type} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (L : Submodule O V) [L.IsLattice K] {y : V}
    (hy : y ∉ L) : ∃ l : V →ₗ[K] K, (∀ z ∈ L, ψ (l z) = 1) ∧ ψ (l y) ≠ 1 := by
  classical
  haveI : Module.Free O L := Submodule.IsLattice.free K L
  let b := Module.Free.chooseBasis O L
  let v : Module.Free.ChooseBasisIndex O L → V := fun i => (b i : V)
  have hliO : LinearIndependent O v := b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hliK : LinearIndependent K v := (LinearIndependent.iff_fractionRing O K).mp hliO
  have hspanO : Submodule.span O (Set.range v) = L := by
    have hr : Set.range v = L.subtype '' Set.range b := by rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspK : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← Submodule.IsLattice.span_eq_top (A := K) (M := L)]
    apply Submodule.span_le.mpr
    intro z hz
    have hz' : z ∈ Submodule.span O (Set.range v) := by rw [hspanO]; exact hz
    exact Submodule.span_le_restrictScalars O K _ hz'
  let bK := Module.Basis.mk hliK hspK
  have hrange : Set.range bK = Set.range v := by
    ext z
    simp only [Set.mem_range, bK, Module.Basis.mk_apply]
  have hmem : ∀ z, z ∈ L ↔ ∀ i, bK.repr z i ∈ Set.range (algebraMap O K) := by
    intro z
    rw [← Module.Basis.mem_span_iff_repr_mem O bK z, hrange, hspanO]
  obtain ⟨i, hi⟩ : ∃ i, bK.repr y i ∉ Set.range (algebraMap O K) := by
    by_contra hcon
    push_neg at hcon
    exact hy ((hmem y).mpr hcon)
  obtain ⟨t, ht⟩ : ∃ t : O, ψ (bK.repr y i * algebraMap O K t) ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hi ((hψ _).mp hcon)
  have hψO : ∀ o : O, ψ (algebraMap O K o) = 1 := fun o => by
    have h1 := ((hψ (algebraMap O K o)).mpr ⟨o, rfl⟩) 1
    simpa using h1
  refine ⟨algebraMap O K t • bK.coord i, ?_, ?_⟩
  · intro z hz
    obtain ⟨o, ho⟩ := (hmem z).mp hz i
    simp only [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
    rw [← ho, ← map_mul]
    exact hψO _
  · simp only [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
    rwa [mul_comm]

variable (K) in

def lam (a : O) (m m' : ℕ) : Submodule O (Matrix (Fin m) (Fin m') K) :=
  LinearMap.range (a • (Algebra.linearMap O K).mapMatrix)

variable {a : O} {n d : ℕ}

omit [IsDomain O] [IsPrincipalIdealRing O] [IsFractionRing O K] in
theorem mem_lam {Y : Matrix (Fin n) (Fin d) K} : Y ∈ lam K a n d ↔ ∃ α : Matrix (Fin n) (Fin d) O, a • α.map (algebraMap O K) = Y := by
  simp only [lam, LinearMap.mem_range, LinearMap.smul_apply, LinearMap.mapMatrix_apply, Algebra.coe_linearMap]

omit [IsDomain O] [IsPrincipalIdealRing O] [IsFractionRing O K] in
theorem keep {h : Matrix (Fin n) (Fin n) K} (hh : h - 1 ∈ lam K a n n) (y : Matrix (Fin n) (Fin d) O) {Y : Matrix (Fin n) (Fin d) K}
    (hY : Y - y.map (algebraMap O K) ∈ lam K a n d) : h * Y - y.map (algebraMap O K) ∈ lam K a n d := by
  rw [mem_lam] at hh hY ⊢
  obtain ⟨α, hα⟩ := hh
  obtain ⟨β, hβ⟩ := hY
  have hf : ∀ x : O, algebraMap O K (a • x) = a • algebraMap O K x := fun x => by
    rw [smul_eq_mul, map_mul, Algebra.smul_def]
  refine ⟨β + α * y + a • (α * β), ?_⟩
  have e1 : h = 1 + a • α.map (algebraMap O K) := by rw [hα]; abel
  have e2 : Y = y.map (algebraMap O K) + a • β.map (algebraMap O K) := by rw [hβ]; abel
  rw [e1, e2, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), Matrix.map_smul (algebraMap O K) a hf, Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_add]
  abel

private theorem isLattice_lam_of_ne_zero [IsFractionRing O K] {a : O} {n d : ℕ} (h0 : a ≠ 0) :
    (lam K a n d).IsLattice K := by
  classical
  refine ⟨?_, ?_⟩
  · unfold lam
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  · rw [eq_top_iff]
    intro Y _
    rw [Matrix.matrix_eq_sum_single Y]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    have hmem : a • (Matrix.single i j (1 : O)).map (algebraMap O K) ∈ lam K a n d :=
      mem_lam.mpr ⟨_, rfl⟩
    have hne : algebraMap O K a ≠ 0 := fun hz =>
      h0 ((IsFractionRing.injective O K) (by rw [hz, map_zero]))
    have hrw : Matrix.single i j (Y i j) =
        (Y i j * (algebraMap O K a)⁻¹) • (a • (Matrix.single i j (1 : O)).map (algebraMap O K)) := by
      rw [Matrix.map_single, map_one, ← algebraMap_smul K a, smul_smul, inv_mul_cancel_right₀ hne,
        Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hrw]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

private theorem isLattice_map_of_surjective {n d : ℕ} (L : Submodule O (Matrix (Fin n) (Fin d) K)) [L.IsLattice K]
    (G : Matrix (Fin n) (Fin d) K →ₗ[K] Matrix (Fin n) (Fin d) K) (hG : Function.Surjective G) :
    (L.map (G.restrictScalars O)).IsLattice K := by
  refine ⟨(Submodule.IsLattice.fg (A := K) (M := L)).map _, ?_⟩
  have himg : ((L.map (G.restrictScalars O) : Submodule O (Matrix (Fin n) (Fin d) K)) :
      Set (Matrix (Fin n) (Fin d) K)) = G '' (L : Set (Matrix (Fin n) (Fin d) K)) := by
    rw [Submodule.map_coe]
    rfl
  rw [himg, Submodule.span_image, Submodule.IsLattice.span_eq_top, Submodule.map_top,
    LinearMap.range_eq_top.mpr hG]

private theorem isUnit_det_lemma_3 [IsLocalRing O] {a : O} {n : ℕ} (ha : a ∈ IsLocalRing.maximalIdeal O)
    (M : Matrix (Fin n) (Fin n) O) : IsUnit (1 + a • M).det := by
  rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, RingHom.map_det]
  have hπa : IsLocalRing.residue O a = 0 := (IsLocalRing.residue_eq_zero_iff a).mpr ha
  have hone : (IsLocalRing.residue O).mapMatrix (1 + a • M) = 1 := by
    ext i j
    simp [Matrix.one_apply, hπa, apply_ite]
  rw [hone, Matrix.det_one]
  exact one_ne_zero

theorem dich [IsLocalRing O] (ψ : AddChar K ℂ) (hψ : ∀ x, (∀ y : O, ψ (x * algebraMap O K y) = 1) ↔ x ∈ (algebraMap O K).range)
    (h0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal O) (y : Matrix (Fin n) (Fin d) O) (r : Matrix (Fin d) (Fin n) O) (hr : y * r = 1)
    (h : GL (Fin n) K) : (h.1 - 1 ∈ lam K a n n ∧ (h⁻¹).1 - 1 ∈ lam K a n n) ∨ ∃ l : Matrix (Fin n) (Fin d) K →ₗ[K] K,
      (∀ Y ∈ lam K a n d, ψ (l Y) = 1 ∧ ψ (l (h.1 * Y)) = 1) ∧ ψ (l (h.1 * y.map (algebraMap O K) - y.map (algebraMap O K))) ≠ 1 := by
  classical
  have hf : ∀ x : O, algebraMap O K (a • x) = a • algebraMap O K x := fun x => by
    rw [smul_eq_mul, map_mul, Algebra.smul_def]
  have hm1 : (1 : Matrix (Fin n) (Fin n) O).map (algebraMap O K) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  let G : Matrix (Fin n) (Fin d) K →ₗ[K] Matrix (Fin n) (Fin d) K :=
    { toFun := fun Y => h.1 * Y
      map_add' := Matrix.mul_add _
      map_smul' := fun c Y => by simp [Matrix.mul_smul] }
  have hGs : Function.Surjective G := fun Y =>
    ⟨(h⁻¹).1 * Y, by
      show h.1 * ((h⁻¹).1 * Y) = Y
      rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]⟩
  haveI : (lam K a n d).IsLattice K := isLattice_lam_of_ne_zero h0
  haveI : ((lam K a n d).map (G.restrictScalars O)).IsLattice K := isLattice_map_of_surjective _ G hGs
  haveI : ((lam K a n d) ⊔ (lam K a n d).map (G.restrictScalars O)).IsLattice K :=
    Submodule.IsLattice.sup K _ _
  by_cases hmem : h.1 * y.map (algebraMap O K) - y.map (algebraMap O K) ∈
      (lam K a n d) ⊔ (lam K a n d).map (G.restrictScalars O)
  · left
    obtain ⟨Y1, hY1, Z, hZ, hsum⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨Y2, hY2, rfl⟩ := Submodule.mem_map.mp hZ
    obtain ⟨A1, rfl⟩ := mem_lam.mp hY1
    obtain ⟨A2, rfl⟩ := mem_lam.mp hY2
    change a • A1.map (algebraMap O K) + h.1 * (a • A2.map (algebraMap O K)) =
      h.1 * y.map (algebraMap O K) - y.map (algebraMap O K) at hsum
    have hyr : y.map (algebraMap O K) * r.map (algebraMap O K) = 1 := by
      rw [← Matrix.map_mul, hr, hm1]
    have e : a • (A1.map (algebraMap O K) * r.map (algebraMap O K)) +
        a • (h.1 * (A2.map (algebraMap O K) * r.map (algebraMap O K))) = h.1 - 1 := by
      have h2 := congrArg (fun M => M * r.map (algebraMap O K)) hsum
      simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, hyr,
        Matrix.mul_one, Matrix.one_mul] at h2
      exact h2
    let P : Matrix (Fin n) (Fin n) O := 1 + a • (-(A2 * r))
    let Q : Matrix (Fin n) (Fin n) O := 1 + a • (A1 * r)
    have hPm : P.map (algebraMap O K) = 1 - a • (A2.map (algebraMap O K) * r.map (algebraMap O K)) := by
      simp only [P, Q]
      rw [Matrix.map_add _ (map_add _), hm1, Matrix.map_smul _ a hf, Matrix.map_neg _ (map_neg _),
        Matrix.map_mul, smul_neg, sub_eq_add_neg]
    have hQm : Q.map (algebraMap O K) = 1 + a • (A1.map (algebraMap O K) * r.map (algebraMap O K)) := by
      simp only [Q]
      rw [Matrix.map_add _ (map_add _), hm1, Matrix.map_smul _ a hf, Matrix.map_mul]
    have key : h.1 * P.map (algebraMap O K) = Q.map (algebraMap O K) := by
      rw [hPm, hQm, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
      calc h.1 - a • (h.1 * (A2.map (algebraMap O K) * r.map (algebraMap O K)))
          = (h.1 - 1) - a • (h.1 * (A2.map (algebraMap O K) * r.map (algebraMap O K))) + 1 := by abel
        _ = (a • (A1.map (algebraMap O K) * r.map (algebraMap O K)) +
              a • (h.1 * (A2.map (algebraMap O K) * r.map (algebraMap O K)))) -
              a • (h.1 * (A2.map (algebraMap O K) * r.map (algebraMap O K))) + 1 := by rw [e]
        _ = 1 + a • (A1.map (algebraMap O K) * r.map (algebraMap O K)) := by abel
    have hPu : IsUnit P.det := isUnit_det_lemma_3 ha _
    have hQu : IsUnit Q.det := isUnit_det_lemma_3 ha _
    have hPi : P.map (algebraMap O K) * P⁻¹.map (algebraMap O K) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv P hPu, hm1]
    have hQi : Q.map (algebraMap O K) * Q⁻¹.map (algebraMap O K) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv Q hQu, hm1]
    have hh : h.1 = Q.map (algebraMap O K) * P⁻¹.map (algebraMap O K) := by
      calc h.1 = h.1 * (P.map (algebraMap O K) * P⁻¹.map (algebraMap O K)) := by rw [hPi, Matrix.mul_one]
        _ = Q.map (algebraMap O K) * P⁻¹.map (algebraMap O K) := by rw [← Matrix.mul_assoc, key]
    have key2 : (h⁻¹).1 * Q.map (algebraMap O K) = P.map (algebraMap O K) := by
      rw [← key, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have hhi : (h⁻¹).1 = P.map (algebraMap O K) * Q⁻¹.map (algebraMap O K) := by
      calc (h⁻¹).1 = (h⁻¹).1 * (Q.map (algebraMap O K) * Q⁻¹.map (algebraMap O K)) := by
            rw [hQi, Matrix.mul_one]
        _ = P.map (algebraMap O K) * Q⁻¹.map (algebraMap O K) := by rw [← Matrix.mul_assoc, key2]
    have hQP : Q - P = a • (A1 * r + A2 * r) := by
      simp only [P, Q, smul_add, smul_neg]
      abel
    have hPQ : P - Q = a • (-(A1 * r + A2 * r)) := by
      rw [← neg_sub, hQP, smul_neg]
    refine ⟨mem_lam.mpr ⟨(A1 * r + A2 * r) * P⁻¹, ?_⟩, mem_lam.mpr ⟨-(A1 * r + A2 * r) * Q⁻¹, ?_⟩⟩
    · have hd : h.1 - 1 = (Q - P).map (algebraMap O K) * P⁻¹.map (algebraMap O K) := by
        rw [Matrix.map_sub _ (map_sub _), Matrix.sub_mul, hPi, ← hh]
      rw [hd, hQP, Matrix.map_smul _ a hf, Matrix.smul_mul, Matrix.map_mul]
    · have hd : (h⁻¹).1 - 1 = (P - Q).map (algebraMap O K) * Q⁻¹.map (algebraMap O K) := by
        rw [Matrix.map_sub _ (map_sub _), Matrix.sub_mul, hQi, ← hhi]
      rw [hd, hPQ, Matrix.map_smul _ a hf, Matrix.smul_mul, Matrix.map_mul]
  · right
    obtain ⟨l, hl1, hl2⟩ := sep ψ hψ _ hmem
    exact ⟨l, fun Y hY => ⟨hl1 Y (Submodule.mem_sup_left hY),
      hl1 _ (Submodule.mem_sup_right (Submodule.mem_map_of_mem hY))⟩, hl2⟩

end GlobalTheory.ThK.Dbl.Bmp

end
end

