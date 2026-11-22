import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0033
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLatticeChainLatAndComap
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.ChainLattice

theorem exists_smul_mem {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (M : Submodule R V) {v : V} (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ a : R, a ≠ 0 ∧ a • v ∈ M := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert R K V h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 M v hv; exact @_root_.GlobalTheory.SmulMemOfMemSpan.main)
  | exact @_root_.GlobalTheory.SmulMemOfMemSpan.main
  | exact _root_.GlobalTheory.SmulMemOfMemSpan.main
  | (apply _root_.GlobalTheory.SmulMemOfMemSpan.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmulMemOfMemSpan.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmulMemOfMemSpan.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmulMemOfMemSpan.main ..)

theorem span_eq_top_of_smul_mem {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (M : Submodule R V) (h : ∀ v : V, ∃ a : R, a ≠ 0 ∧ a • v ∈ M) :
    Submodule.span K (M : Set V) = ⊤ := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert R K V h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 M h; exact @_root_.GlobalTheory.LemmaTwoFortyThirteen.main)
  | exact @_root_.GlobalTheory.LemmaTwoFortyThirteen.main
  | exact _root_.GlobalTheory.LemmaTwoFortyThirteen.main
  | (apply _root_.GlobalTheory.LemmaTwoFortyThirteen.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LemmaTwoFortyThirteen.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LemmaTwoFortyThirteen.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LemmaTwoFortyThirteen.main ..)

theorem isLattice_chainLat_and_comap :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (n : Type) [Fintype n] [DecidableEq n] (c : ℕ),
      (∀ (ϖ : 𝒪[k]), (ϖ : k) ≠ 0 → ∀ L : Submodule 𝒪[k] (n → k), Submodule.IsLattice k L →
        Submodule.IsLattice k (chainLat ϖ c L)) ∧
      ∀ Λ : Submodule 𝒪[k] (n ⊕ Fin c → k), Submodule.IsLattice k Λ →
        Submodule.IsLattice k (Λ.comap (inX k n c)) := by
  intro k _ _ _ _ n _ _ c
  refine ⟨fun ϖ hϖ L hL => ⟨?_, ?_⟩, fun Λ hΛ => ⟨?_, ?_⟩⟩
  · exact (hL.fg.map _).sup (Submodule.fg_span (Set.finite_range _))
  · rw [eq_top_iff]
    intro v _
    have hv : v = inX k n c (fun r => v (Sum.inl r)) +
        ∑ i : Fin c, (v (Sum.inr i) / (ϖ : k) ^ ((i : ℕ) + 1)) •
          ((ϖ : k) ^ ((i : ℕ) + 1) • aux k n i) := by
      have h : ∀ i : Fin c, (v (Sum.inr i) / (ϖ : k) ^ ((i : ℕ) + 1)) •
          ((ϖ : k) ^ ((i : ℕ) + 1) • aux k n i) = v (Sum.inr i) • aux k n i := by
        intro i
        rw [smul_smul, div_mul_cancel₀ _ (pow_ne_zero _ hϖ)]
      simp only [h]
      funext j
      rcases j with r | j
      · simp [inX_apply, aux, Finset.sum_apply]
      · simp [inX_apply, aux, Finset.sum_apply, Pi.single_apply]
    rw [hv]
    refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (scaled_basis_mem_chainLattice ϖ L i)))
    obtain ⟨a, ha, hav⟩ := exists_smul_mem (K := k) L (v := fun r => v (Sum.inl r))
      (by rw [hL.span_eq_top]; trivial)
    have h1 : algebraMap 𝒪[k] k a ≠ 0 := by simpa using ha
    have : inX k n c (fun r => v (Sum.inl r)) =
        (algebraMap 𝒪[k] k a)⁻¹ • inX k n c (a • fun r => v (Sum.inl r)) := by
      rw [map_smul, ← algebraMap_smul k a, smul_smul, inv_mul_cancel₀ h1, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (inX_mem_chainLat.2 hav))
  · refine Submodule.fg_of_fg_map_injective (inX k n c) ?_
      (hΛ.fg.of_le (Submodule.map_comap_le _ _))
    intro x y hxy
    funext r
    have := congrFun hxy (Sum.inl r)
    simpa [inX_apply] using this
  · refine span_eq_top_of_smul_mem _ fun v => ?_
    obtain ⟨a, ha, hav⟩ := exists_smul_mem (K := k) Λ (v := inX k n c v)
      (by rw [hΛ.span_eq_top]; trivial)
    exact ⟨a, ha, by rw [Submodule.mem_comap, map_smul]; exact hav⟩

end GlobalTheory.RootEx.ChainLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped ENNReal NNReal

namespace GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
  (ν : Measure k) [ν.IsAddHaarMeasure]

theorem map_mul_left_volM (h : GL n k) :
    (volM ν n n).map (fun x => h.val * x) =
      ENNReal.ofReal (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card n : ℝ))) • volM ν n n := by
  haveI := secondCountable k
  haveI := t2Space k
  haveI : BorelSpace (Matrix n n k) := inferInstanceAs (BorelSpace (n → n → k))
  haveI : LocallyCompactSpace (Matrix n n k) := inferInstanceAs (LocallyCompactSpace (n → n → k))
  haveI : SecondCountableTopology (Matrix n n k) := inferInstanceAs (SecondCountableTopology (n → n → k))
  haveI : (volM ν n n).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let e : Matrix n n k ≃+ Matrix n n k :=
    { toFun := fun x => h.val * x
      invFun := fun x => (h⁻¹).val * x
      left_inv := fun x => by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun x => by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      map_add' := fun x y => Matrix.mul_add _ _ _ }
  have c1 : Continuous e := continuous_const.matrix_mul continuous_id
  have c2 : Continuous e.symm := continuous_const.matrix_mul continuous_id
  haveI := e.isAddHaarMeasure_map (volM ν n n) c1 c2
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, (volM ν n n).map e = c • volM ν n n :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  change (volM ν n n).map e = _
  set K : Set (Matrix n n k) := {A | ∀ i j, A i j ∈ 𝒪[k]} with hK
  have hKo : IsOpen K := SplitFlip.isOpen_intMatrix
  have hKc : IsCompact K := SplitFlip.isCompact_intMatrix
  have h0 : volM ν n n K ≠ 0 := (hKo.measure_pos _ ⟨0, fun _ _ => zero_mem _⟩).ne'
  have ht : volM ν n n K ≠ ⊤ := hKc.measure_lt_top.ne
  have hr : (volM ν n n).real K ≠ 0 := by simp [Measure.real, ENNReal.toReal_eq_zero_iff, h0, ht]
  have key := integral_comp_mul_mul_volM ν (1 : GL n k) h (K.indicator fun _ => (1 : ℂ))
  have h1 : ∫ x, K.indicator (fun _ => (1 : ℂ)) (h.val * x * (1 : GL n k).val) ∂(volM ν n n) =
      ∫ x, K.indicator (fun _ => (1 : ℂ)) x ∂((volM ν n n).map e) := by
    rw [integral_map c1.measurable.aemeasurable
      (stronglyMeasurable_const.indicator hKo.measurableSet).aestronglyMeasurable]
    simp only [Units.val_one, Matrix.mul_one]
    rfl
  rw [h1, hc, integral_smul_nnreal_measure, integral_indicator_const _ hKo.measurableSet, map_one, nabs_one,
    Real.one_rpow, mul_one] at key
  have h2 : (c : ℝ) = nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card n : ℝ)) := by
    refine mul_right_cancel₀ hr ?_
    simp only [NNReal.smul_def, smul_smul, Complex.real_smul, mul_one] at key
    exact_mod_cast key
  rw [hc, ← h2, ENNReal.ofReal_coe_nnreal]
  rfl

omit [MeasurableSpace k] [BorelSpace k] in
theorem continuous_density_volGL : Continuous fun g : GL n k =>
    ENNReal.ofReal (nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card n : ℝ))) :=
  (((isLocallyConstant_nabs k).comp_continuous Matrix.GeneralLinearGroup.continuous_det).comp
    (fun t : ℝ => ENNReal.ofReal (t ^ (-(Fintype.card n : ℝ))))).continuous

theorem isMulLeftInvariant_volGL : (volGL ν n).IsMulLeftInvariant := by
  haveI := secondCountable k
  haveI : BorelSpace (Matrix n n k) := inferInstanceAs (BorelSpace (n → n → k))
  have hE := Model.measurableEmbedding_val (k := k) n
  have hd := (continuous_density_volGL (k := k) (n := n)).measurable
  set μ := (volM ν n n).comap (fun g : GL n k => g.val) with hμ
  set d := fun g : GL n k =>
    ENNReal.ofReal (nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card n : ℝ))) with hdd
  have dmul : ∀ g h, d (g * h) = d g * d h := fun g h => by
    simp only [hdd, map_mul, nabs_mul]
    rw [Real.mul_rpow (nabs_pos' _).le (nabs_pos' _).le,
      ENNReal.ofReal_mul (Real.rpow_nonneg (nabs_pos' _).le _)]
  have done' : d 1 = 1 := by simp [hdd, nabs_one]
  have hm : ∀ h : GL n k, μ.map (fun x => h * x) = d h • μ := fun h => by
    ext s hs
    have cm : Measurable fun x : Matrix n n k => h.val * x :=
      (continuous_const.matrix_mul continuous_id).measurable
    rw [Measure.map_apply (measurable_const_mul h) hs, Measure.smul_apply, hE.comap_apply, hE.comap_apply,
      ← Measure.smul_apply, ← map_mul_left_volM ν h, Measure.map_apply cm (hE.measurableSet_image.2 hs)]
    congr 1
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨h * g, hg, rfl⟩
    · rintro ⟨g, hg, e⟩
      refine ⟨h⁻¹ * g, by simpa using hg, ?_⟩
      have e' : g.val = h.val * x := e
      simp only [Units.val_mul, e', ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  refine ⟨fun h => ?_⟩
  ext s hs
  have hs' := measurable_const_mul h hs
  change (μ.withDensity d).map _ s = μ.withDensity d s
  rw [Measure.map_apply (measurable_const_mul h) hs, withDensity_apply _ hs', withDensity_apply _ hs,
    ← lintegral_indicator hs', ← lintegral_indicator hs]
  have e1 : ∀ x, ((fun x => h * x) ⁻¹' s).indicator d x = d h⁻¹ * s.indicator d (h * x) := fun x => by
    by_cases hx : h * x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ (fun x => h * x) ⁻¹' s from hx), ← dmul,
        inv_mul_cancel_left]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ (fun x => h * x) ⁻¹' s from hx),
        mul_zero]
  simp_rw [e1]
  rw [lintegral_const_mul _ (f := fun a => s.indicator d (h * a))
      ((hd.indicator hs).comp (measurable_const_mul h)),
    ← lintegral_map (hd.indicator hs) (measurable_const_mul h), hm, lintegral_smul_measure, smul_eq_mul,
    ← mul_assoc, ← dmul, inv_mul_cancel, done', one_mul]

theorem volGL_KO : volGL ν n (KO k n) = volM ν n n ((fun g : GL n k => g.val) '' (KO k n)) := by
  have hE := Model.measurableEmbedding_val (k := k) n
  have hs := (SplitFlip.isOpen_KO (k := k) (n := n)).measurableSet
  unfold volGL
  rw [withDensity_apply _ hs, setLIntegral_congr_fun hs (g := fun _ => 1), setLIntegral_one, hE.comap_apply]
  rintro _ ⟨u, rfl⟩
  have h1 : nabs k (Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u)) = 1 := by
    rw [nabs_eq_one_iff]
    have : ((Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) : kˣ) : k) = algebraMap 𝒪[k] k u.val.det :=
      ((algebraMap 𝒪[k] k).map_det u.val).symm
    rw [this]
    exact (Valuation.integer.integers (valuation k)).one_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit)
  simp only [h1, Real.one_rpow, ENNReal.ofReal_one]

theorem isHaarMeasure_volGL : (volGL ν n).IsHaarMeasure := by
  haveI := secondCountable k
  haveI := t2Space k
  haveI : (volM ν n n).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI := isMulLeftInvariant_volGL (n := n) ν
  have ho := SplitFlip.isOpen_KO (k := k) (n := n)
  have hc := SplitFlip.isCompact_KO (k := k) (n := n)
  have hoe : Topology.IsOpenEmbedding (fun g : GL n k => g.val) := by
    refine ⟨SplitFlip.isEmbedding_val_GL, ?_⟩
    have : Set.range (fun g : GL n k => g.val) = {x : Matrix n n k | x.det ≠ 0} := by
      ext x
      simp only [Set.mem_range, Set.mem_setOf_eq]
      rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
      rfl
    rw [this]
    exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  refine Measure.isHaarMeasure_of_isCompact_nonempty_interior _ _ hc
    (by rw [ho.interior_eq]; exact ⟨1, one_mem _⟩) ?_ ?_
  · rw [volGL_KO]
    exact ((hoe.isOpenMap _ ho).measure_pos _ ⟨_, 1, one_mem _, rfl⟩).ne'
  · rw [volGL_KO]
    exact (hc.image hoe.continuous).measure_lt_top.ne

theorem volGL_haar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure], BorelSpace (GL n k) ∧ LocallyCompactSpace (GL n k) ∧ SecondCountableTopology (GL n k) ∧ IsCompact (KO k n : Set (GL n k)) ∧ IsOpen (KO k n : Set (GL n k)) ∧ IsOpen (KOne k n : Set (GL n k)) ∧ (volGL ν n).IsHaarMeasure ∧ (volGL ν n).IsMulRightInvariant :=
  fun _ _ _ _ _ _ _ n _ _ ν _ =>
    haveI := isHaarMeasure_volGL (n := n) ν
    ⟨SplitFlip.borel_GL, SplitFlip.locallyCompact_GL, SplitFlip.secondCountable_GL, SplitFlip.isCompact_KO,
      SplitFlip.isOpen_KO, StepData.isOpen_KOne, this, SplitFlip.isMulRightInvariant_of_haar _⟩

end GlobalTheory.SplitWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenAndRelIndexNeZero
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.LatOpen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type}

theorem eventually_smul_mem (L : Submodule 𝒪[k] (ι → k))
    (hL : Submodule.span k (L : Set (ι → k)) = ⊤) (x : ι → k) :
    ∀ᶠ t in nhds (0 : k), t • x ∈ L := by
  have hx : x ∈ Submodule.span k (L : Set (ι → k)) := by rw [hL]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    have h : (𝒪[k] : Set k) ∈ nhds (0 : k) := (isOpen_int k).mem_nhds (zero_mem 𝒪[k])
    filter_upwards [h] with t ht
    exact L.smul_mem (⟨t, ht⟩ : 𝒪[k]) hy
  | zero => exact Filter.Eventually.of_forall fun t => by simp
  | add y z _ _ hy hz =>
    filter_upwards [hy, hz] with t h1 h2
    rw [smul_add]
    exact L.add_mem h1 h2
  | smul a y _ hy =>
    have ht : Filter.Tendsto (fun t : k => t * a) (nhds 0) (nhds 0) := by
      have h : Continuous (fun t : k => t * a) := continuous_id.mul continuous_const
      simpa using h.tendsto 0
    filter_upwards [ht.eventually hy] with t h
    rwa [smul_smul]

theorem isOpen_of_span_eq_top [Fintype ι] [DecidableEq ι] (L : Submodule 𝒪[k] (ι → k))
    (hL : Submodule.span k (L : Set (ι → k)) = ⊤) : IsOpen (L : Set (ι → k)) := by
  refine AddSubgroup.isOpen_of_mem_nhds L.toAddSubgroup (g := 0) ?_
  have h : ∀ᶠ x in nhds (0 : ι → k), ∀ i, x i • (Pi.single i (1 : k) : ι → k) ∈ L := by
    refine Filter.eventually_all.2 fun i => ?_
    have ht : Filter.Tendsto (fun x : ι → k => x i) (nhds 0) (nhds 0) :=
      (continuous_apply i).tendsto (0 : ι → k)
    exact ht.eventually (eventually_smul_mem L hL _)
  filter_upwards [h] with x hx
  have e : x = ∑ i, x i • (Pi.single i (1 : k) : ι → k) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  change x ∈ L
  rw [e]
  exact L.sum_mem fun i _ => hx i

theorem isCompact_stdLat : IsCompact (stdLat k ι : Set (ι → k)) := by
  have e : (stdLat k ι : Set (ι → k)) = Set.pi Set.univ fun _ => (𝒪[k] : Set k) := by
    ext v
    simp only [SetLike.mem_coe, mem_stdLat, Set.mem_pi, Set.mem_univ, true_imp_iff]
  rw [e]
  exact isCompact_univ_pi fun _ => isCompact_int k

theorem isOpen_and_relIndex_ne_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι]
    (L : Submodule 𝒪[k] (ι → k)) (hL : Submodule.IsLattice k L) :
    IsOpen (L : Set (ι → k)) ∧ L.toAddSubgroup.relIndex (stdLat k ι).toAddSubgroup ≠ 0 := by
  have ho := isOpen_of_span_eq_top L hL.span_eq_top
  refine ⟨ho, ?_⟩
  haveI : CompactSpace (stdLat k ι).toAddSubgroup :=
    isCompact_iff_compactSpace.1 (isCompact_stdLat (k := k) (ι := ι))
  haveI : Finite ((stdLat k ι).toAddSubgroup ⧸
      L.toAddSubgroup.addSubgroupOf (stdLat k ι).toAddSubgroup) :=
    AddSubgroup.quotient_finite_of_isOpen _ (ho.preimage continuous_subtype_val)
  exact AddSubgroup.index_ne_zero_of_finite

end GlobalTheory.RootEx.LatOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSplitThetaGridPathFlipGridPathAtSquare
section
open GlobalTheory.SplitFlip

namespace GlobalTheory.FlipPathPairwise

def srcDiff (e : Edge) : ℤ := (e.src.1 : ℤ) - e.src.2

theorem srcDiff_of_join {e e' : Edge} (h : e.tgt = e'.src) : srcDiff e' = srcDiff e + 1 := by
  cases e <;> cases e' <;> simp only [Edge.src, Edge.tgt, Prod.mk.injEq] at h <;>
    simp only [srcDiff, Edge.src] <;> omega

theorem pairwise_of_isPath {γ : List Edge} (h : IsPath γ) :
    γ.Pairwise fun a b => srcDiff a < srcDiff b := by
  have h' : γ.IsChain fun a b => srcDiff a < srcDiff b :=
    List.IsChain.imp (fun a b hab => by rw [srcDiff_of_join hab]; omega) h
  haveI : Trans (fun a b : Edge => srcDiff a < srcDiff b) (fun a b => srcDiff a < srcDiff b)
      (fun a b => srcDiff a < srcDiff b) := ⟨fun h1 h2 => lt_trans h1 h2⟩
  exact h'.pairwise

end GlobalTheory.FlipPathPairwise

open GlobalTheory.FlipPathPairwise in

theorem GlobalTheory.SplitFlip.isPath_flipPath : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ →
    IsPath (flipPath i j γ) := by
  intro γ i j hγ hP
  obtain ⟨s, t, rfl⟩ := hP
  have hpw := pairwise_of_isPath hγ
  rw [List.pairwise_append, List.pairwise_append] at hpw
  have hs : ∀ a ∈ s, a ≠ .theta i j ∧ a ≠ .ex i j := fun a ha => by
    have h1 := hpw.1.2.2 a ha (.theta i j) (by simp)
    have h2 := hpw.1.2.2 a ha (.ex i j) (by simp)
    exact ⟨fun h => by subst h; exact lt_irrefl _ h1, fun h => by subst h; exact lt_irrefl _ h2⟩
  have ht : ∀ a ∈ t, a ≠ .theta i j ∧ a ≠ .ex i j := fun a ha => by
    have h1 := hpw.2.2 (.theta i j) (by simp) a ha
    have h2 := hpw.2.2 (.ex i j) (by simp) a ha
    exact ⟨fun h => by subst h; exact lt_irrefl _ h1, fun h => by subst h; exact lt_irrefl _ h2⟩
  have hflip : flipPath i j (s ++ [Edge.theta i j, Edge.ex i j] ++ t) =
      s ++ Edge.ex i (j + 1) :: Edge.theta (i + 1) j :: t := by
    have key : ∀ l : List Edge, (∀ a ∈ l, a ≠ .theta i j ∧ a ≠ .ex i j) →
        l.map (fun e => if e = .theta i j then Edge.ex i (j + 1) else if e = .ex i j then .theta (i + 1) j else e)
          = l := fun l hl =>
      (List.map_congr_left fun a ha => by simp [hl a ha]).trans (List.map_id l)
    unfold flipPath
    rw [List.map_append, List.map_append, key s hs, key t ht]
    simp
  rw [hflip]
  unfold IsPath at hγ ⊢
  rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append, List.isChain_append] at hγ
  obtain ⟨h1, h2, h3⟩ := hγ
  rw [List.isChain_cons_cons] at h2
  obtain ⟨-, h2⟩ := h2
  rw [List.isChain_cons] at h2
  refine List.isChain_append.2 ⟨h1, ?_, ?_⟩
  · rw [List.isChain_cons_cons, List.isChain_cons]
    exact ⟨rfl, h2.1, h2.2⟩
  · intro x hx y hy
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    exact h3 x hx (Edge.theta i j) rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftColumnsMulVecInjectiveOfRankEqCard
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory

open Matrix Topology Module in

theorem _root_.GlobalTheory.mulVec_firstCols_eq_zero_of_rank_eq_card :
    ∀ (k m a b n : Type) [Field k] [Fintype m] [Fintype a] [Fintype b] [Fintype n] (e : a ⊕ b ≃ n) (x : Matrix m n k), x.rank = Fintype.card a → (∀ i j, x i (e (Sum.inr j)) = 0) → ∀ v : a → k, (x.submatrix id (fun i => e (Sum.inl i))) *ᵥ v = 0 → v = 0 := by
  intro k m a b n _ _ _ _ _ e x hx hz v hv
  classical
  set x' := x.submatrix id (fun i => e (Sum.inl i))
  let Q : Matrix n a k := Matrix.of fun l i => if l = e (Sum.inl i) then 1 else 0
  let P : Matrix a n k := Matrix.of fun i l => if l = e (Sum.inl i) then 1 else 0
  have hQ : x' = x * Q := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [x', Q, Matrix.of_apply, Matrix.submatrix_apply, id, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hP : x = x' * P := by
    ext i l
    obtain ⟨t, rfl⟩ := e.surjective l
    rcases t with t | t
    · rw [Matrix.mul_apply]
      simp only [x', P, Matrix.of_apply, Matrix.submatrix_apply, id, mul_ite, mul_one, mul_zero,
        EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    · rw [Matrix.mul_apply]
      simp [x', P, hz]
  have hr : x'.rank = Fintype.card a := by
    apply le_antisymm
    · rw [← hx, hQ]; exact Matrix.rank_mul_le_left _ _
    · rw [← hx, hP]; exact Matrix.rank_mul_le_left _ _
  have hrn := LinearMap.finrank_range_add_finrank_ker x'.mulVecLin
  have hxr : finrank k (LinearMap.range x'.mulVecLin) = Fintype.card a := hr
  rw [hxr, finrank_fintype_fun_eq_card] at hrn
  have hker : LinearMap.ker x'.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
  have hvk : v ∈ LinearMap.ker x'.mulVecLin := hv
  rw [hker] at hvk
  exact (Submodule.mem_bot k).1 hvk

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrixStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_change_of_variables_localField_matrix : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ν : Measure k) [ν.IsAddHaarMeasure], (∀ (g : GL a k) (f : (a → k) → ℂ), ∫ x, f (g.val.mulVec x) ∂(Measure.pi fun _ => ν) = ((nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ => ν)) ∧ ∀ (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ), ∫ x, Φ (h.val * x * g.val) ∂(volM ν b a) = (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ)) * nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card b : ℝ))) • ∫ x, Φ x ∂(volM ν b a) := by
  first | exact @GlobalTheory.SplitWeil.linear_change_of_variables | exact GlobalTheory.SplitWeil.linear_change_of_variables | (intros; apply GlobalTheory.SplitWeil.linear_change_of_variables <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGridPathInnerVerticesFlipGridPathAtSquare
section
namespace GlobalTheory.SplitFlip

def pathInnerDiff (X : ℕ × ℕ) : ℤ := (X.1 : ℤ) - X.2

theorem pathInnerDiff_tgt (e : Edge) : pathInnerDiff e.tgt = pathInnerDiff e.src + 1 := by
  cases e <;> simp [pathInnerDiff, Edge.tgt, Edge.src] <;> push_cast <;> ring

theorem IsPath.pairwise_lt_source_index_difference_along_path {γ : List Edge} (hγ : IsPath γ) :
    (γ.map fun e => pathInnerDiff e.src).Pairwise (· < ·) := by
  have h : (γ.map fun e => pathInnerDiff e.src).IsChain (· < ·) :=
    List.isChain_map_of_isChain _ (R := fun a b : Edge => a.tgt = b.src) (fun a b (hab : a.tgt = b.src) => by
      show pathInnerDiff a.src < pathInnerDiff b.src
      rw [← hab, pathInnerDiff_tgt]; omega) (by unfold IsPath at hγ; exact hγ)
  exact h.pairwise

theorem IsPath.eq_of_src_eq_of_mem {γ : List Edge} (hγ : IsPath γ) {a b : Edge} (ha : a ∈ γ) (hb : b ∈ γ)
    (h : a.src = b.src) : a = b :=
  List.inj_on_of_nodup_map hγ.pairwise_lt_source_index_difference_along_path.nodup ha hb (by simp [h])

theorem src_flipEdge_pathInner (i j : ℕ) (e : Edge) :
    (if e = .theta i j then Edge.ex i (j + 1) else if e = .ex i j then .theta (i + 1) j else e).src =
      if e = .ex i j then (i + 1, j + 1) else e.src := by
  by_cases h1 : e = .theta i j
  · subst h1; simp
  · by_cases h2 : e = .ex i j
    · subst h2; simp
    · simp [h1, h2]

theorem mem_innerVertices_flipPath {γ : List Edge} {i j : ℕ} (hγ : IsPath γ) (hp : PassesThrough i j γ) :
    ∀ X ∈ innerVertices (flipPath i j γ), X ≠ (i, j) ∧ (X ≠ (i + 1, j + 1) → X ∈ innerVertices γ) := by
  intro X hX
  rw [innerVertices, flipPath, ← List.map_tail, List.map_map, List.mem_map] at hX
  obtain ⟨e, he, rfl⟩ := hX
  rw [Function.comp_apply, src_flipEdge_pathInner]
  have hex : Edge.ex i j ∈ γ := hp.subset (by simp)
  have heγ : e ∈ γ := List.mem_of_mem_tail he
  by_cases h : e = .ex i j
  · simp only [h, if_true]
    refine ⟨fun H => ?_, fun H => absurd rfl H⟩
    simp at H
  · simp only [h, if_false]
    refine ⟨fun H => h (hγ.eq_of_src_eq_of_mem heγ hex (by simpa using H)), fun _ => List.mem_map.2 ⟨e, he, rfl⟩⟩

end GlobalTheory.SplitFlip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyEquivOfSmoothTraceEqAdmissibleStatement
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_equiv_of_smoothTrace_eq_admissible : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (π' : Representation ℂ G W), IsAdmissible π → IsAdmissible π' → π.IsIrreducible → π'.IsIrreducible → (∀ f : G → ℂ, IsLocallyConstant f → HasCompactSupport f → smoothTrace π μ f = smoothTrace π' μ f) → Nonempty (π.Equiv π') := by
  first | exact @GlobalTheory.CharIndep.nonempty_equiv_of_smoothTrace_eq | exact GlobalTheory.CharIndep.nonempty_equiv_of_smoothTrace_eq | (intros; apply GlobalTheory.CharIndep.nonempty_equiv_of_smoothTrace_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeHeisenbergVariableSignStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootExchange_heisenbergVariable_sign : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∀ (x₀ : Matrix n n' k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} → k) (β : n → k) (r : n) (i : Fin (c + 1)), i.val + 1 = ρ + 1 → ((1 - ((colE c (ρ + 1) β).val - 1)) * affPt (ρ + 1) x₀ e : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (Sum.inl r) (Sum.inr i) = -β r) ∧ ∀ (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure], Continuous ψ → ∀ (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (β : n → k), (∀ x, om μ 1 (colE c (ρ + 1) β) Φ.1 x = Φ.1 ((1 - ((colE c (ρ + 1) β).val - 1)) * x)) ∧ ∀ x₀, fl ψ ν μ ρ Φ.1 x₀ β = opE ψ ν (ρ + 1) (fun x => Φ.1 (x + colM c (ρ + 1) (-β))) x₀ := by
  first | exact @GlobalTheory.RootEx.HeisenbergSign.sign | exact GlobalTheory.RootEx.HeisenbergSign.sign | (intros; apply GlobalTheory.RootEx.HeisenbergSign.sign <;> assumption)
end

