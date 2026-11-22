import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableCosetSection
section
open MeasureTheory

namespace GlobalTheory

open Filter Topology

theorem exists_measurable_invariant_index {G : Type} [Group G] [MetricSpace G]
    [ContinuousMul G] [MeasurableSpace G] [BorelSpace G] (L : Subgroup G) (y : ℕ → G)
    (r : ℝ) (Q : ℕ → G → Prop) (hQm : ∀ n, MeasurableSet {x | Q n x})
    (hQi : ∀ n, ∀ l ∈ L, ∀ x, Q n (l * x) ↔ Q n x)
    (hex : ∀ x, ∃ n, (∃ l ∈ L, dist (y n) (l * x) < r) ∧ Q n x) :
    ∃ s : G → ℕ, Measurable s ∧ (∀ x, ∃ l ∈ L, dist (y (s x)) (l * x) < r) ∧
      (∀ l ∈ L, ∀ x, s (l * x) = s x) ∧ ∀ x, Q (s x) x := by
  classical
  have hPm : ∀ n, MeasurableSet {x : G | (∃ l ∈ L, dist (y n) (l * x) < r) ∧ Q n x} := by
    intro n
    have hset : {x : G | ∃ l ∈ L, dist (y n) (l * x) < r} =
        ⋃ l : L, {x : G | dist (y n) ((l : G) * x) < r} := by
      ext x; simp
    have hopen : IsOpen {x : G | ∃ l ∈ L, dist (y n) (l * x) < r} := by
      rw [hset]
      exact isOpen_iUnion fun l =>
        isOpen_lt (continuous_const.dist (continuous_const.mul continuous_id)) continuous_const
    exact hopen.measurableSet.inter (hQm n)
  have hinv : ∀ l ∈ L, ∀ x n, ((∃ l' ∈ L, dist (y n) (l' * (l * x)) < r) ∧ Q n (l * x)) ↔
      ((∃ l' ∈ L, dist (y n) (l' * x) < r) ∧ Q n x) := by
    intro l hl x n
    refine and_congr ⟨?_, ?_⟩ (hQi n l hl x)
    · rintro ⟨m, hm, hd⟩
      exact ⟨m * l, L.mul_mem hm hl, by rwa [mul_assoc]⟩
    · rintro ⟨m, hm, hd⟩
      refine ⟨m * l⁻¹, L.mul_mem hm (L.inv_mem hl), ?_⟩
      simpa [mul_assoc] using hd
  refine ⟨fun x => Nat.find (hex x), measurable_find hex hPm, fun x => (Nat.find_spec (hex x)).1,
    fun l hl x => ?_, fun x => (Nat.find_spec (hex x)).2⟩
  exact le_antisymm (Nat.find_min' _ ((hinv l hl x _).2 (Nat.find_spec (hex x))))
    (Nat.find_min' _ ((hinv l hl x _).1 (Nat.find_spec (hex (l * x)))))

theorem exists_measurable_coset_section_metric {G : Type} [Group G] [MetricSpace G]
    [CompleteSpace G] [SecondCountableTopology G]
    [ContinuousMul G] [MeasurableSpace G] [BorelSpace G] (L : Subgroup G)
    (hL : IsClosed (L : Set G)) :
    ∃ σ : G → G, Measurable σ ∧ (∀ x, σ x * x⁻¹ ∈ L) ∧ ∀ l ∈ L, ∀ x, σ (l * x) = σ x := by
  classical
  obtain ⟨y, hy⟩ : ∃ y : ℕ → G, DenseRange y := TopologicalSpace.exists_dense_seq G
  let S : ℕ → Type := fun k => {s : G → ℕ // Measurable s ∧ (∀ l ∈ L, ∀ x, s (l * x) = s x) ∧
    ∀ x, ∃ l ∈ L, dist (y (s x)) (l * x) < (1 / 2 : ℝ) ^ k}
  have hy_meas : ∀ s : G → ℕ, Measurable s → Measurable (fun x => y (s x)) :=
    fun s hs => measurable_from_nat.comp hs

  have h0 : Nonempty (S 0) := by
    obtain ⟨s, hs, hclose, hinv, -⟩ := exists_measurable_invariant_index L y 1 (fun _ _ => True)
      (fun _ => MeasurableSet.univ) (fun _ _ _ _ => Iff.rfl) (fun x => by
        obtain ⟨n, hn⟩ := hy.exists_dist_lt x one_pos
        exact ⟨n, ⟨1, L.one_mem, by rw [one_mul, dist_comm]; exact hn⟩, trivial⟩)
    exact ⟨⟨s, hs, hinv, fun x => by simpa using hclose x⟩⟩

  have hstep : ∀ k (s : S k), ∃ s' : S (k + 1),
      ∀ x, dist (y (s'.1 x)) (y (s.1 x)) < 2 * (1 / 2 : ℝ) ^ k := by
    intro k s
    obtain ⟨s, hsm, hsi, hsc⟩ := s
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (k + 1) := by positivity
    have hhalf : (1 / 2 : ℝ) ^ (k + 1) = (1 / 2 : ℝ) ^ k / 2 := by ring
    obtain ⟨s', hs'm, hclose, hinv, hQ⟩ := exists_measurable_invariant_index L y ((1 / 2 : ℝ) ^ (k + 1))
      (fun n x => dist (y n) (y (s x)) < 2 * (1 / 2 : ℝ) ^ k)
      (fun n => measurableSet_lt (measurable_const.dist (hy_meas s hsm)) measurable_const)
      (fun n l hl x => by simp only [hsi l hl x])
      (fun x => by
        obtain ⟨l, hl, hd⟩ := hsc x
        obtain ⟨n, hn⟩ := hy.exists_dist_lt (l * x) hpos
        refine ⟨n, ⟨l, hl, by rw [dist_comm]; exact hn⟩, ?_⟩
        have hk : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
        calc dist (y n) (y (s x)) ≤ dist (y n) (l * x) + dist (l * x) (y (s x)) := dist_triangle _ _ _
          _ < 2 * (1 / 2 : ℝ) ^ k := by
            rw [hhalf] at hn
            have e1 := dist_comm (y n) (l * x)
            have e2 := dist_comm (l * x) (y (s x))
            linarith)
    exact ⟨⟨s', hs'm, hinv, hclose⟩, hQ⟩
  choose step hstep using hstep
  let seq : (k : ℕ) → S k := fun k => Nat.rec (motive := S) h0.some (fun k s => step k s) k
  let f : ℕ → G → G := fun k x => y ((seq k).1 x)
  have hf_succ : ∀ k x, dist (f k x) (f (k + 1) x) ≤ 2 * (1 / 2 : ℝ) ^ k := fun k x => by
    rw [dist_comm]; exact (hstep k (seq k) x).le
  have hcauchy : ∀ x, CauchySeq (fun k => f k x) := fun x =>
    cauchySeq_of_le_geometric (1 / 2 : ℝ) 2 (by norm_num) (hf_succ · x)
  choose σ hσ using fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  refine ⟨σ, ?_, ?_, ?_⟩
  · exact measurable_of_tendsto_metrizable (fun k => hy_meas _ (seq k).2.1) (tendsto_pi_nhds.2 hσ)
  · intro x
    have hC : IsClosed {z : G | z * x⁻¹ ∈ L} := hL.preimage (continuous_id.mul continuous_const)
    suffices h : σ x ∈ closure {z : G | z * x⁻¹ ∈ L} by rwa [hC.closure_eq] at h
    rw [Metric.mem_closure_iff]
    intro ε hε
    have h1 : ∀ᶠ k in atTop, dist (f k x) (σ x) < ε / 2 :=
      (hσ x).eventually (Metric.ball_mem_nhds _ (half_pos hε))
    have h2 : ∀ᶠ k in atTop, (1 / 2 : ℝ) ^ k < ε / 2 :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually
        (gt_mem_nhds (half_pos hε))
    obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
    obtain ⟨l, hl, hd⟩ := (seq k).2.2.2 x
    refine ⟨l * x, by simpa using hl, ?_⟩
    calc dist (σ x) (l * x) ≤ dist (σ x) (f k x) + dist (f k x) (l * x) := dist_triangle _ _ _
      _ < ε := by rw [dist_comm] at hk1; change dist (f k x) (l * x) < _ at hd; linarith
  · intro l hl x
    have hfx : (fun k => f k (l * x)) = fun k => f k x := by
      funext k; simp only [f, (seq k).2.2.1 l hl x]
    have := hσ (l * x)
    rw [hfx] at this
    exact tendsto_nhds_unique this (hσ x)

theorem exists_measurable_coset_section (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [PolishSpace G] [MeasurableSpace G] [BorelSpace G] (L : Subgroup G)
    (hL : IsClosed (L : Set G)) :
    ∃ σ : G → G, Measurable σ ∧ (∀ x, σ x * x⁻¹ ∈ L) ∧ ∀ l ∈ L, ∀ x, σ (l * x) = σ x := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable G
  exact exists_measurable_coset_section_metric L hL

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableFundamentalDomain
section
namespace GlobalTheory.MeasurableFundamentalDomain

open Set Topology

theorem exists_small_open {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] (Γ : Subgroup G)
    (hΓ : ∀ C : Set G, IsCompact C → Set.Finite (C ∩ (↑Γ : Set G))) :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ ∀ a ∈ V, ∀ b ∈ V, a * b⁻¹ ∈ Γ → a * b⁻¹ = 1 := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hfin : ((K ∩ (↑Γ : Set G)) \ {1}).Finite := (hΓ K hK).subset sdiff_subset
  have hcl : IsClosed ((K ∩ (↑Γ : Set G)) \ {1}) := hfin.isClosed
  have h1 : ((K ∩ (↑Γ : Set G)) \ {1})ᶜ ∈ 𝓝 (1 : G) :=
    hcl.isOpen_compl.mem_nhds (by simp)
  have hW : K ∩ ((K ∩ (↑Γ : Set G)) \ {1})ᶜ ∈ 𝓝 (1 : G) := Filter.inter_mem hK1 h1
  obtain ⟨V, hV, hVW⟩ := exists_nhds_split_inv hW
  refine ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.2 hV, ?_⟩
  intro a ha b hb hab
  have h := hVW a (interior_subset ha) b (interior_subset hb)
  rw [div_eq_mul_inv] at h
  by_contra hne
  exact h.2 ⟨⟨h.1, hab⟩, hne⟩

theorem exists_measurable_fundamental_domain {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [OpensMeasurableSpace G] (Γ : Subgroup G) [Countable ↥Γ]
    (hΓ : ∀ C : Set G, IsCompact C → Set.Finite (C ∩ (↑Γ : Set G))) :
    ∃ D : Set G, MeasurableSet D ∧ (∀ y : G, ∃ γ ∈ Γ, γ * y ∈ D) ∧
      ∀ γ ∈ Γ, ∀ y ∈ D, γ * y ∈ D → γ = (1 : G) := by
  classical
  obtain ⟨V, hVo, hV1, hV⟩ := exists_small_open Γ hΓ
  obtain ⟨g, hg⟩ := TopologicalSpace.exists_dense_seq G
  let U : ℕ → Set G := fun n => {y | y * (g n)⁻¹ ∈ V}
  let S : ℕ → Set G := fun n => ⋃ γ ∈ Γ, {y | γ * y ∈ U n}
  have hUo : ∀ n, IsOpen (U n) := fun n => hVo.preimage (continuous_id.mul continuous_const)
  have hSo : ∀ n, IsOpen (S n) := fun n =>
    isOpen_biUnion fun γ _ => (hUo n).preimage (continuous_const.mul continuous_id)
  have hS : ∀ n y, y ∈ S n ↔ ∃ γ ∈ Γ, γ * y ∈ U n := by
    intro n y
    simp [S]
  have hSinv : ∀ n, ∀ γ ∈ Γ, ∀ y, γ * y ∈ S n → y ∈ S n := by
    intro n γ hγ y hy
    obtain ⟨δ, hδ, h⟩ := (hS _ _).1 hy
    exact (hS _ _).2 ⟨δ * γ, Γ.mul_mem hδ hγ, by rwa [mul_assoc]⟩
  refine ⟨⋃ n, (U n \ ⋃ m ∈ Set.Iio n, S m), ?_, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun n =>
      (hUo n).measurableSet.diff (isOpen_biUnion fun m _ => hSo m).measurableSet
  · intro y
    have hex : ∃ n, y ∈ S n := by
      have ho : IsOpen {x : G | y * x⁻¹ ∈ V} :=
        hVo.preimage (continuous_const.mul continuous_inv)
      obtain ⟨n, hn⟩ := hg.exists_mem_open ho ⟨y, by simpa using hV1⟩
      exact ⟨n, (hS _ _).2 ⟨1, Γ.one_mem, by rw [one_mul]; exact hn⟩⟩
    obtain ⟨γ, hγ, h⟩ := (hS _ _).1 (Nat.find_spec hex)
    refine ⟨γ, hγ, mem_iUnion.2 ⟨Nat.find hex, h, ?_⟩⟩
    intro hm
    obtain ⟨m, hm, hy⟩ := mem_iUnion₂.1 hm
    exact Nat.find_min hex hm (hSinv m γ hγ y hy)
  · intro γ hγ y hy hγy
    obtain ⟨n, hn, hn'⟩ := mem_iUnion.1 hy
    obtain ⟨m, hm, hm'⟩ := mem_iUnion.1 hγy
    have hnm : n = m := by
      rcases lt_trichotomy n m with h | h | h
      · exact absurd (mem_iUnion₂.2 ⟨n, h, (hS _ _).2
          ⟨γ⁻¹, Γ.inv_mem hγ, by rwa [inv_mul_cancel_left]⟩⟩) hm'
      · exact h
      · exact absurd (mem_iUnion₂.2 ⟨m, h, (hS _ _).2 ⟨γ, hγ, hm⟩⟩) hn'
    subst hnm
    have e : (γ * y * (g n)⁻¹) * (y * (g n)⁻¹)⁻¹ = γ := by group
    have := hV _ hm _ hn (by rw [e]; exact hγ)
    rwa [e] at this

end GlobalTheory.MeasurableFundamentalDomain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableLintegralCosetEqOneClosedSubgrou
section
open MeasureTheory

namespace GlobalTheory

open MeasureTheory in
open scoped ENNReal in
open scoped Pointwise in

theorem _root_.GlobalTheory.exists_measurable_lintegral_coset_eq_one
    (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (ν : Measure H)
    [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G) (hj : Topology.IsClosedEmbedding j) :
    ∃ b : G → ENNReal, Measurable b ∧ ∀ g, ∫⁻ h, b (j h * g) ∂ν = 1 := by
  let K := CompactExhaustion.choice G
  set a : ℕ → ℝ≥0∞ := fun n => ν (j ⁻¹' (K n * (K n)⁻¹)) with ha_def
  have ha : ∀ n, a n ≠ ∞ := fun n =>
    (hj.isCompact_preimage ((K.isCompact n).mul (K.isCompact n).inv)).measure_lt_top.ne
  set c : ℕ → ℝ≥0∞ := fun n => (2⁻¹ : ℝ≥0∞) ^ n / (a n + 1) with hc_def
  have hc_pos : ∀ n, c n ≠ 0 := fun n =>
    (ENNReal.div_pos (pow_ne_zero _ (by simp)) (by simp [ha n])).ne'
  have hc_le : ∀ n, c n ≤ 2⁻¹ ^ n := fun n =>
    ENNReal.div_le_of_le_mul (le_mul_of_one_le_right' le_add_self)
  have hca : ∀ n, c n * a n ≤ 2⁻¹ ^ n := fun n => by
    calc c n * a n ≤ c n * (a n + 1) := by gcongr; exact le_self_add
      _ = 2⁻¹ ^ n := ENNReal.div_mul_cancel (by simp) (by simp [ha n])
  have hKm : ∀ n, MeasurableSet (K n) := fun n => (K.isCompact n).isClosed.measurableSet
  set f : G → ℝ≥0∞ := fun y => ∑' n, (K n).indicator (fun _ => c n) y with hf_def
  have hf : Measurable f := Measurable.ennreal_tsum fun n => measurable_const.indicator (hKm n)
  have hf_pos : ∀ y, f y ≠ 0 := by
    intro y
    obtain ⟨n, hn⟩ := K.exists_mem y
    refine ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 (hc_pos n)) ?_)
    calc c n = (K n).indicator (fun _ => c n) y := (Set.indicator_of_mem hn (fun _ => c n)).symm
      _ ≤ f y := ENNReal.le_tsum n
  have hjg : ∀ g, Measurable fun h => j h * g := fun g => hj.continuous.measurable.mul_const g
  have hmeas : ∀ g, Measurable fun h => f (j h * g) := fun g => hf.comp (hjg g)
  set F : G → ℝ≥0∞ := fun g => ∫⁻ h, f (j h * g) ∂ν with hF_def
  have hF : Measurable F :=
    Measurable.lintegral_prod_right' (ν := ν) (f := fun p : G × H => f (j p.2 * p.1))
      (hf.comp ((hj.continuous.measurable.comp measurable_snd).mul measurable_fst))
  have hF_inv : ∀ h' g, F (j h' * g) = F g := by
    intro h' g
    have e : ∀ h, f (j h * (j h' * g)) = (fun k => f (j k * g)) (h * h') := by
      intro h; simp only [map_mul, mul_assoc]
    calc F (j h' * g) = ∫⁻ h, (fun k => f (j k * g)) (h * h') ∂ν := lintegral_congr e
      _ = F g := lintegral_mul_right_eq_self (μ := ν) (fun k => f (j k * g)) h'
  have hF0 : ∀ g, F g ≠ 0 := by
    intro g h0
    rw [hF_def, lintegral_eq_zero_iff (hmeas g), Filter.EventuallyEq, ae_iff] at h0
    have : ν Set.univ = 0 := by simpa [hf_pos] using h0
    exact NeZero.ne ν (Measure.measure_univ_eq_zero.1 this)
  have hFtop : ∀ g, F g ≠ ∞ := by
    intro g
    obtain ⟨m, hm⟩ := K.exists_mem g
    have hterm : ∀ n, ∫⁻ h, (K n).indicator (fun _ => c n) (j h * g) ∂ν
        ≤ (1 + a m) * 2⁻¹ ^ n := by
      intro n
      have hsub : (fun h => j h * g) ⁻¹' K n ⊆ j ⁻¹' (K (max n m) * (K (max n m))⁻¹) := by
        intro h hh
        have h1 : j h * g ∈ K (max n m) := K.subset (le_max_left n m) hh
        have h2 : g ∈ K (max n m) := K.subset (le_max_right n m) hm
        have e : j h = (j h * g) * g⁻¹ := by group
        rw [Set.mem_preimage, e]
        exact Set.mul_mem_mul h1 (Set.inv_mem_inv.2 h2)
      have hle : ν ((fun h => j h * g) ⁻¹' K n) ≤ a n + a m := by
        refine (measure_mono hsub).trans ?_
        rcases le_total n m with hnm | hnm
        · rw [max_eq_right hnm]; exact le_add_self
        · rw [max_eq_left hnm]; exact le_self_add
      calc ∫⁻ h, (K n).indicator (fun _ => c n) (j h * g) ∂ν
          = ∫⁻ h, ((fun h => j h * g) ⁻¹' K n).indicator (fun _ => c n) h ∂ν := rfl
        _ = c n * ν ((fun h => j h * g) ⁻¹' K n) :=
            lintegral_indicator_const (hjg g (hKm n)) _
        _ ≤ c n * (a n + a m) := by gcongr
        _ = c n * a n + c n * a m := mul_add _ _ _
        _ ≤ 2⁻¹ ^ n + 2⁻¹ ^ n * a m := by gcongr; exacts [hca n, hc_le n]
        _ = (1 + a m) * 2⁻¹ ^ n := by ring
    have hF_eq : F g = ∑' n, ∫⁻ h, (K n).indicator (fun _ => c n) (j h * g) ∂ν :=
      lintegral_tsum fun n =>
        ((measurable_const.indicator (hKm n)).comp (hjg g)).aemeasurable
    rw [hF_eq]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top (by simp [ha m]) (by simp)
  refine ⟨fun g => f g * (F g)⁻¹, hf.mul hF.inv, fun g => ?_⟩
  simp only [hF_inv]
  rw [lintegral_mul_const _ (hmeas g)]
  exact ENNReal.mul_inv_cancel (hF0 g) (hFtop g)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMemFractionalIdealGeneratorAtPrimesOver
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_mem_notMem_coeIdeal_mul {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (c : FractionalIdeal (nonZeroDivisors R) K) (hc : c ≠ 0)
    (P : Ideal R) (hP : P ≠ ⊤) :
    ∃ b : K, b ∈ c ∧ b ∉ (P : FractionalIdeal (nonZeroDivisors R) K) * c := by
  by_contra h
  push_neg at h
  have h1 : c ≤ (P : FractionalIdeal (nonZeroDivisors R) K) * c := fun b hb => h b hb
  have h2 : c * c⁻¹ ≤ (P : FractionalIdeal (nonZeroDivisors R) K) * c * c⁻¹ := by
    gcongr
  rw [mul_assoc, mul_inv_cancel₀ hc, mul_one, ← FractionalIdeal.coeIdeal_top,
    FractionalIdeal.coeIdeal_le_coeIdeal] at h2
  exact hP (top_le_iff.mp h2)

theorem exists_mem_forall_notMem_coeIdeal_mul {R K : Type} [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (c : FractionalIdeal (nonZeroDivisors R) K)
    (hc : c ≠ 0) (S : Finset (Ideal R)) (hS : ∀ Q ∈ S, Q.IsMaximal) :
    ∃ a : K, a ∈ c ∧ ∀ Q ∈ S, a ∉ (Q : FractionalIdeal (nonZeroDivisors R) K) * c := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, c.zero_mem, by simp⟩
  | insert P S hPS ih =>
    obtain ⟨a, ha, haS⟩ := ih (fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ))
    have hP : P.IsMaximal := hS P (Finset.mem_insert_self _ _)
    by_cases haP : a ∈ (P : FractionalIdeal (nonZeroDivisors R) K) * c
    swap
    · refine ⟨a, ha, fun Q hQ => ?_⟩
      rcases Finset.mem_insert.mp hQ with rfl | hQ
      · exact haP
      · exact haS Q hQ
    obtain ⟨b, hb, hbP⟩ := exists_mem_notMem_coeIdeal_mul c hc P hP.ne_top
    have hnle : ¬ S.inf id ≤ P := by
      rw [hP.isPrime.inf_le']
      rintro ⟨Q, hQ, hQP⟩
      have : Q = P := (hS Q (Finset.mem_insert_of_mem hQ)).eq_of_le hP.ne_top hQP
      exact hPS (this ▸ hQ)
    obtain ⟨e, heS, heP⟩ := SetLike.not_le_iff_exists.mp hnle
    have key : ∀ (Q : Ideal R) (x : R), x ∈ Q →
        x • b ∈ (Q : FractionalIdeal (nonZeroDivisors R) K) * c := by
      intro Q x hx
      rw [Algebra.smul_def]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hx) hb
    refine ⟨a + e • b, (c : Submodule R K).add_mem ha ((c : Submodule R K).smul_mem e hb),
      fun Q hQ h => ?_⟩
    rcases Finset.mem_insert.mp hQ with rfl | hQ
    · obtain ⟨y, p, hp, hy⟩ := hP.exists_inv heP
      set J : Submodule R K := (((Q : FractionalIdeal (nonZeroDivisors R) K) * c :
        FractionalIdeal (nonZeroDivisors R) K) : Submodule R K) with hJ
      have h1 : e • b ∈ J := (J.add_mem_iff_right haP).mp h
      have h2 : y • (e • b) + p • b ∈ J := J.add_mem (J.smul_mem y h1) (key Q p hp)
      rw [smul_smul, ← add_smul, hy, one_smul] at h2
      exact hbP h2
    · have heQ : e ∈ Q := (Finset.inf_le (f := id) hQ) heS
      set J : Submodule R K := (((Q : FractionalIdeal (nonZeroDivisors R) K) * c :
        FractionalIdeal (nonZeroDivisors R) K) : Submodule R K) with hJ
      exact haS Q hQ ((J.add_mem_iff_left (key Q e heQ)).mp h)

theorem exists_mem_fractionalIdeal_generator_at_primes_over :
    ∀ (E : Type) [Field E] [NumberField E] (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E),
      c ≠ 0 → ∀ N : 𝓞 E, N ≠ 0 → ∃ a : E, a ∈ c ∧ ∀ Q : Ideal (𝓞 E), Q.IsMaximal → N ∈ Q →
        a ∉ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
  intro E _ _ c hc N hN
  have hN' : Ideal.span {N} ≠ (0 : Ideal (𝓞 E)) := by
    simpa using hN
  have hfin : {Q : Ideal (𝓞 E) | Q.IsMaximal ∧ N ∈ Q}.Finite := by
    refine ((Ideal.finite_factors hN').image (fun v => v.asIdeal)).subset ?_
    rintro Q ⟨hQ, hNQ⟩
    have h0 : Q ≠ ⊥ := by
      rintro rfl
      exact hN (by simpa using hNQ)
    refine ⟨⟨Q, hQ.isPrime, h0⟩, ?_, rfl⟩
    simpa [Ideal.dvd_iff_le] using hNQ
  obtain ⟨a, ha, h⟩ := exists_mem_forall_notMem_coeIdeal_mul c hc hfin.toFinset
    (fun Q hQ => (hfin.mem_toFinset.mp hQ).1)
  exact ⟨a, ha, fun Q hQ hNQ => h Q (hfin.mem_toFinset.mpr ⟨hQ, hNQ⟩)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRealSubmoduleBlockFinrankLe
section
open Finset

namespace GlobalTheory

theorem exists_real_submodule_block_finrank_le :
    ∀ (n : ℕ) (E E' : Submodule ℂ (EuclideanSpace ℂ (Fin n))),
    ∃ U : Submodule ℝ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)),
      Module.finrank ℝ U ≤ 2 * Module.finrank ℂ E' * Module.finrank ℂ E ∧
      ∀ T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n),
        E'.starProjection ∘L T ∘L E.starProjection ∈ U := by
  intro n E E'
  let f : (E →L[ℂ] E') →ₗ[ℝ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    { toFun := fun M => E'.subtypeL ∘L M ∘L E.orthogonalProjection
      map_add' := fun M N => by ext; simp
      map_smul' := fun c M => by ext; simp }
  refine ⟨LinearMap.range f, ?_, fun T => ⟨E'.orthogonalProjection ∘L T ∘L E.subtypeL, rfl⟩⟩
  refine (LinearMap.finrank_range_le f).trans (le_of_eq ?_)
  have h1 : Module.finrank ℂ (E →L[ℂ] E') = Module.finrank ℂ E * Module.finrank ℂ E' := by
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := E) (F' := E')).finrank_eq,
      Module.finrank_linearMap]
  rw [← Module.finrank_mul_finrank ℝ ℂ (E →L[ℂ] E'), Complex.finrank_real_complex, h1]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSubmoduleSkewBlockFinrankLe
section
open Finset
open scoped InnerProductSpace

namespace GlobalTheory

def skewOpsBlock (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℂ F] :
    Submodule ℝ (F →L[ℂ] F) where
  carrier := {M | ∀ x z, ⟪M x, z⟫_ℂ + ⟪x, M z⟫_ℂ = 0}
  zero_mem' := by intro x z; simp
  add_mem' := by
    intro a b ha hb x z
    have h1 := ha x z
    have h2 := hb x z
    simp only [ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
    linear_combination h1 + h2
  smul_mem' := by
    intro c a ha x z
    have h1 := ha x z
    have e : ∀ y, (c • a) y = (c : ℂ) • a y := fun y => by
      simp [Complex.coe_smul]
    simp only [e, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    linear_combination (c : ℂ) * h1

theorem finrank_skewOpsBlock_le (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] :
    Module.finrank ℝ (skewOpsBlock F) ≤ Module.finrank ℂ F ^ 2 := by
  let J : (F →L[ℂ] F) →ₗ[ℝ] (F →L[ℂ] F) :=
    { toFun := fun M => Complex.I • M
      map_add' := fun a b => smul_add _ _ _
      map_smul' := fun c a => by simp only [RingHom.id_apply]; exact smul_comm _ _ _ }
  have hJ : Function.Injective J := by
    intro a b h
    exact smul_right_injective _ Complex.I_ne_zero h
  have hd : Disjoint (skewOpsBlock F) ((skewOpsBlock F).map J) := by
    rw [Submodule.disjoint_def]
    rintro a ha ⟨b, hb, rfl⟩
    have hb0 : b = 0 := by
      ext x
      have h1 := ha x (b x)
      have h2 := hb x (b x)
      have e : ∀ y, J b y = Complex.I • b y := fun y => rfl
      simp only [e, inner_smul_left, inner_smul_right, Complex.conj_I] at h1
      have h3 : ⟪b x, b x⟫_ℂ = 0 := by
        linear_combination (Complex.I / 2) * h1 + (1 / 2 : ℂ) * h2 +
          ((⟪b x, b x⟫_ℂ - ⟪x, b (b x)⟫_ℂ) / 2) * Complex.I_mul_I
      simpa using h3
    rw [hb0, map_zero]
  haveI : FiniteDimensional ℝ (F →L[ℂ] F) := FiniteDimensional.complexToReal _
  have h1 := Submodule.finrank_add_finrank_le_of_disjoint hd
  rw [← (Submodule.equivMapOfInjective J hJ (skewOpsBlock F)).finrank_eq,
    finrank_real_of_complex] at h1
  have h2 : Module.finrank ℂ (F →L[ℂ] F) = Module.finrank ℂ F ^ 2 := by
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := F) (F' := F)).finrank_eq,
      Module.finrank_linearMap, sq]
  omega

theorem exists_submodule_skew_block_finrank_le (n : ℕ)
    (E : Submodule ℂ (EuclideanSpace ℂ (Fin n))) :
    ∃ U : Submodule ℝ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)),
      Module.finrank ℝ U ≤ Module.finrank ℂ E ^ 2 ∧
      ∀ T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n),
        (∀ x ∈ E, ∀ z ∈ E, ⟪T x, z⟫_ℂ + ⟪x, T z⟫_ℂ = 0) →
          E.starProjection ∘L T ∘L E.starProjection ∈ U := by
  let Φ : (E →L[ℂ] E) →ₗ[ℝ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    { toFun := fun M => E.subtypeL ∘L M ∘L E.orthogonalProjection
      map_add' := fun a b => by ext1 x; rfl
      map_smul' := fun c a => by ext1 x; rfl }
  haveI : FiniteDimensional ℝ (E →L[ℂ] E) := FiniteDimensional.complexToReal _
  refine ⟨(skewOpsBlock E).map Φ,
    (Submodule.finrank_map_le Φ _).trans (finrank_skewOpsBlock_le E), ?_⟩
  intro T hT
  refine ⟨E.orthogonalProjection ∘L T ∘L E.subtypeL, ?_, ?_⟩
  · intro x z
    have := hT x x.2 z z.2
    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      Submodule.inner_orthogonalProjection_eq_of_mem_left,
      Submodule.inner_orthogonalProjection_eq_of_mem_right]
    exact this
  · ext1 x; rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpperDens
section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.HaarDensChart

def upperDens {V : Type} [PseudoMetricSpace V] [MeasurableSpace V] (l ν : Measure V) (x : V) : ℝ≥0∞ :=
  limsup (fun r : ℝ => ν (Metric.closedBall x r) / l (Metric.closedBall x r)) (𝓝[>] 0)

end GlobalTheory.HaarDensChart
end
end

