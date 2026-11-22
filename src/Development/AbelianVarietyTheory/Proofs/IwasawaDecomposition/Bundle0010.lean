import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalKerAevalOfEigenspaces
section
open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem finiteDimensional_ker_aeval_of_eigenspaces
    (M : Type) [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M)
    (hT : ∀ lam : ℂ, FiniteDimensional ℂ (T.eigenspace lam)) (p : Polynomial ℂ) (hp : p ≠ 0) :
    FiniteDimensional ℂ (LinearMap.ker (Polynomial.aeval T p)) := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
  by_cases h0 : p.degree = 0
  · have hu : IsUnit p := Polynomial.isUnit_iff_degree_eq_zero.mpr h0
    have hu' : IsUnit (Polynomial.aeval T p) := hu.map _
    have hk : LinearMap.ker (Polynomial.aeval T p) = ⊥ :=
      LinearMap.ker_eq_bot.mpr ((Module.End.isUnit_iff _).mp hu').1
    rw [hk]
    infer_instance
  · obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p h0
    obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr ha
    have hq0 : q ≠ 0 := by
      rintro rfl
      simp at hq
      exact hp hq
    have hdeg : q.natDegree < n := by
      rw [← hn, hq, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero a) hq0,
        Polynomial.natDegree_X_sub_C]
      omega
    have ihq := ih _ hdeg q hq0 rfl
    have hfg : (LinearMap.ker (Polynomial.aeval T p)).FG := by
      apply Submodule.fg_of_fg_map_of_fg_inf_ker (Polynomial.aeval T q)
      · have hle : (LinearMap.ker (Polynomial.aeval T p)).map (Polynomial.aeval T q)
            ≤ T.eigenspace a := by
          rintro _ ⟨x, hx, rfl⟩
          rw [Module.End.mem_eigenspace_iff]
          have hx' : Polynomial.aeval T p x = 0 := hx
          rw [hq, map_mul, Module.End.mul_apply] at hx'
          simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply,
            Module.algebraMap_end_apply] at hx'
          exact sub_eq_zero.mp hx'
        haveI := hT a
        exact (Module.Finite.iff_fg).mp (Submodule.finiteDimensional_of_le hle)
      · exact (Module.Finite.iff_fg).mp (Submodule.finiteDimensional_of_le
          (inf_le_right : _ ≤ LinearMap.ker (Polynomial.aeval T q)))
    exact (Module.Finite.iff_fg).mpr hfg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalOfUniformlyAlmostInvariant
section
open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem norm_sq_toLp_two_eq_integral_norm_sq {K : Type} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (g : C(K, ℂ)) :
    ‖ContinuousMap.toLp 2 μ ℂ g‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂μ := by
  have h := ContinuousMap.inner_toLp μ g g
  rw [inner_self_eq_norm_sq_to_K] at h
  simp_rw [Complex.mul_conj'] at h
  have h2 : (∫ x, ((‖g x‖ : ℂ)) ^ 2 ∂μ) = ((∫ x, ‖g x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]; simp
  rw [h2] at h
  apply Complex.ofReal_injective
  rw [← h, Complex.ofReal_pow]
  rfl

theorem finiteDimensional_of_uniformly_almost_invariant :
    ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
      [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure]
      [μ.IsMulRightInvariant] [IsProbabilityMeasure μ] (E : Submodule ℂ (K → ℂ)),
      (∀ f ∈ E, Continuous f) → ∀ U ∈ 𝓝 (1 : K),
      (∀ f ∈ E, ∀ u ∈ U, ∫ x, ‖f (x * u) - f x‖ ^ 2 ∂μ ≤ (1 / 4) * ∫ x, ‖f x‖ ^ 2 ∂μ) →
      FiniteDimensional ℂ E := by
  intro K _ _ _ _ _ _ _ μ _ _ _ E hE U hU hinv
  classical
  obtain ⟨β, hβ1, -, hβU, hβ01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    (isCompact_singleton (x := (1 : K))) isOpen_interior
    (Set.singleton_subset_iff.2 (mem_interior_iff_mem_nhds.2 hU))
  have hβ0 : ∀ x, 0 ≤ β x := fun x => (hβ01 x).1
  have hβU' : ∀ u, β u ≠ 0 → u ∈ U := fun u hu =>
    interior_subset (hβU (subset_tsupport _ hu))
  set c : ℝ := ∫ u, β u ∂μ with hc
  have hcpos : 0 < c := β.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := 1) (HasCompactSupport.of_compactSpace _) hβ0 (by simp [hβ1 (Set.mem_singleton _)])
  set L := ContinuousMap.toLp (α := K) (E := ℂ) 2 μ ℂ with hL

  let b : C(K, C(K, ℂ)) := ContinuousMap.curry
    ⟨fun p : K × K => (β (p.1⁻¹ * p.2) : ℂ), by fun_prop⟩
  have hb : Continuous fun x => L (b x) := L.continuous.comp b.continuous
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover
    (fun x : K => (fun y => L (b y)) ⁻¹' Metric.ball (L (b x)) (c / 4))
    (fun x _ => hb.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by positivity)))
  let ι : E →ₗ[ℂ] C(K, ℂ) :=
    { toFun := fun f => ⟨f.1, hE f.1 f.2⟩
      map_add' := fun f g => by ext; simp
      map_smul' := fun a f => by ext; simp }
  let Φ : E →ₗ[ℂ] (t → ℂ) := LinearMap.pi fun j : t =>
    (innerSL ℂ (L (b j.1))).toLinearMap ∘ₗ L.toLinearMap ∘ₗ ι
  refine FiniteDimensional.of_injective Φ ((injective_iff_map_eq_zero Φ).2 fun f hf => ?_)
  have hf0 : ∀ j ∈ t, inner ℂ (L (b j)) (L (ι f)) = 0 := fun j hj => by
    simpa [Φ] using congrFun hf ⟨j, hj⟩
  set g : C(K, ℂ) := ι f with hg
  let R : C(K, C(K, ℂ)) := ContinuousMap.curry
    ⟨fun p : K × K => g (p.2 * p.1), by fun_prop⟩
  have hint : ∀ {V : Type} [NormedAddCommGroup V] {F : K → V}, Continuous F → Integrable F μ :=
    fun hF => hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi1 : Integrable (fun u => β u • R u) μ := hint (by fun_prop)
  set T : C(K, ℂ) := ∫ u, β u • R u ∂μ with hT
  have hTx : ∀ x, T x = inner ℂ (L (b x)) (L g) := fun x => by
    rw [hT, ContinuousMap.integral_apply hi1, hL, ContinuousMap.inner_toLp,
      ← integral_mul_left_eq_self (μ := μ) (fun z => g z * (starRingEnd ℂ) (b x z)) x]
    congr 1
    ext u
    simp [R, b, mul_comm]
  have hTb : ∀ x, ‖T x‖ ≤ c / 4 * ‖L g‖ := fun x => by
    obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    have hx' : ‖L (b x) - L (b j)‖ ≤ c / 4 := by
      rw [← dist_eq_norm]; exact le_of_lt hx
    have : T x = inner ℂ (L (b x) - L (b j)) (L g) := by
      rw [inner_sub_left, hf0 j hj, sub_zero, hTx]
    rw [this]
    exact (norm_inner_le_norm _ _).trans (by gcongr)
  have hLT : ‖L T‖ ≤ c / 4 * ‖L g‖ := by
    have := Lp.norm_le_of_ae_bound (f := L T) (C := c / 4 * ‖L g‖) (by positivity)
      (by
        filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ T] with x hx
        rw [hL, hx]; exact hTb x)
    simpa [measureUnivNNReal] using this
  have hmove : ∀ u ∈ U, ‖L (R u) - L g‖ ≤ 1 / 2 * ‖L g‖ := fun u hu => by
    have h1 := hinv f.1 f.2 u hu
    have h2 : ‖L (R u - g)‖ ^ 2 ≤ (1 / 2 * ‖L g‖) ^ 2 := by
      rw [mul_pow, hL, norm_sq_toLp_two_eq_integral_norm_sq, norm_sq_toLp_two_eq_integral_norm_sq]
      norm_num
      simpa [R, hg, ι] using h1
    rw [← map_sub]
    exact le_of_sq_le_sq h2 (by positivity)
  have hdiff : L T - c • L g = ∫ u, β u • (L (R u) - L g) ∂μ := by
    rw [hT, ← L.integral_comp_comm hi1, hc, ← integral_smul_const, ← integral_sub]
    · congr 1
      ext1 u
      rw [smul_sub, L.map_smul_of_tower]
    · exact L.integrable_comp hi1
    · exact hint (by fun_prop)
  have hdn : ‖L T - c • L g‖ ≤ c * (1 / 2 * ‖L g‖) := by
    rw [hdiff, hc, ← integral_mul_const]
    refine norm_integral_le_of_norm_le (hint (by fun_prop)) (Eventually.of_forall fun u => ?_)
    rw [norm_smul, Real.norm_of_nonneg (hβ0 u)]
    by_cases hu : β u = 0
    · simp [hu]
    · exact mul_le_mul_of_nonneg_left (hmove u (hβU' u hu)) (hβ0 u)
  have hfin : c * ‖L g‖ ≤ c / 4 * ‖L g‖ + c * (1 / 2 * ‖L g‖) := by
    have : ‖c • L g‖ ≤ ‖L T‖ + ‖L T - c • L g‖ := by
      simpa using norm_sub_le (L T) (L T - c • L g)
    rw [norm_smul, Real.norm_of_nonneg hcpos.le] at this
    linarith
  have hg0 : ‖L g‖ = 0 := by
    have := norm_nonneg (L g)
    nlinarith
  have hg1 : g = 0 := ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) μ
    (by rw [map_zero]; exact norm_eq_zero.1 hg0)
  ext x
  simpa [hg, ι] using congrArg (fun h : C(K, ℂ) => h x) hg1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitelyManyIsoClassesProjectiveNumberField
section
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory.ProjModFinIso

variable {R : Type} [CommRing R] [IsDedekindDomain R]

theorem finrank_prod_eq (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] :
    Module.finrank R (M × N) = Module.finrank R M + Module.finrank R N := by
  have h1 := (TensorProduct.isBaseChange R (M × N) (FractionRing R)).finrank_eq
  have h2 := (TensorProduct.isBaseChange R M (FractionRing R)).finrank_eq
  have h2' := (TensorProduct.isBaseChange R N (FractionRing R)).finrank_eq
  have h3 := (TensorProduct.prodRight R (FractionRing R) (FractionRing R) M N).finrank_eq
  rw [← h1, h3, Module.finrank_prod, h2, h2']

theorem projective_of_isTorsionFree (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.IsTorsionFree R M] : Module.Projective R M :=
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  Module.Flat.projective_of_finitePresentation

theorem finrank_ideal (I : Ideal R) (h : I ≠ ⊥) : Module.finrank R I = 1 := by
  have h1 : Module.finrank R I ≤ 1 := by simpa using Submodule.finrank_le I
  have : Nontrivial I := Submodule.nontrivial_iff_ne_bot.mpr h
  have h2 := Module.finrank_pos (R := R) (M := I)
  omega

theorem nonempty_equiv_of_mk0_eq {I J : (Ideal R)⁰} (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    Nonempty ((I : Ideal R) ≃ₗ[R] (J : Ideal R)) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 h
  have key : ∀ (z : R), z ≠ 0 → ∀ K : Ideal R, Nonempty (K ≃ₗ[R] ↥(Ideal.span {z} * K)) := by
    intro z hz K
    have hinj : Function.Injective (LinearMap.mulLeft R z) := fun a b hab => mul_left_cancel₀ hz hab
    refine ⟨(Submodule.equivMapOfInjective _ hinj K).trans (LinearEquiv.ofEq _ _ ?_)⟩
    ext w
    rw [Submodule.mem_map, Ideal.mem_span_singleton_mul]
    constructor <;> rintro ⟨a, ha, rfl⟩ <;> exact ⟨a, ha, rfl⟩
  exact ⟨(key x hx I).some.trans ((LinearEquiv.ofEq _ _ hxy).trans (key y hy J).some.symm)⟩

theorem exists_split (X : Type) [AddCommGroup X] [Module R X] [Module.Projective R X]
    [Nontrivial X] :
    ∃ (I : (Ideal R)⁰) (K : Submodule R X), Nonempty (X ≃ₗ[R] K × (I : Ideal R)) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective R X)
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  have hsx : s x ≠ 0 := by
    intro h
    apply hx
    have := LinearMap.congr_fun hs x
    simp only [LinearMap.comp_apply, h, map_zero, LinearMap.id_apply] at this
    exact this.symm
  obtain ⟨a, ha⟩ : ∃ a, s x a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hsx (Finsupp.ext h)
  let f : X →ₗ[R] R := Finsupp.lapply a ∘ₗ s
  have hI : LinearMap.range f ≠ ⊥ := by
    intro h
    have hm : f x ∈ LinearMap.range f := LinearMap.mem_range_self f x
    rw [h, Submodule.mem_bot] at hm
    exact ha hm
  let I : (Ideal R)⁰ := ⟨LinearMap.range f, mem_nonZeroDivisors_of_ne_zero hI⟩
  let g := f.rangeRestrict
  haveI := projective_of_isTorsionFree (R := R) (LinearMap.range f)
  obtain ⟨l, hl⟩ := Module.projective_lifting_property g LinearMap.id f.surjective_rangeRestrict
  have hex : Function.Exact (LinearMap.ker g).subtype g := LinearMap.exact_subtype_ker_map g
  obtain ⟨e, -⟩ := hex.splitSurjectiveEquiv (LinearMap.ker g).injective_subtype ⟨l, hl⟩
  exact ⟨I, LinearMap.ker g, ⟨e⟩⟩

theorem exists_equiv_pi (r : ℕ) : ∀ (X : Type) [AddCommGroup X] [Module R X] [Module.Finite R X]
    [Module.IsTorsionFree R X], Module.finrank R X = r →
    ∃ (ι : Type) (_ : Fintype ι) (I : ι → (Ideal R)⁰), Fintype.card ι = r ∧
      Nonempty (X ≃ₗ[R] ((i : ι) → ((I i : Ideal R)))) := by
  induction r with
  | zero =>
    intro X _ _ _ _ h
    have : Subsingleton X := by
      by_contra hne
      rw [not_subsingleton_iff_nontrivial] at hne
      have := Module.finrank_pos (R := R) (M := X)
      omega
    exact ⟨Empty, inferInstance, Empty.elim, by simp, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
  | succ r ih =>
    intro X _ _ _ _ h
    have : Nontrivial X := Module.nontrivial_of_finrank_pos (R := R) (by omega)
    haveI := projective_of_isTorsionFree (R := R) X
    obtain ⟨I, K, ⟨e⟩⟩ := exists_split (R := R) X
    have hK : Module.finrank R K = r := by
      have h1 := e.finrank_eq
      rw [finrank_prod_eq, finrank_ideal _ (by simpa using nonZeroDivisors.ne_zero I.2)] at h1
      omega
    obtain ⟨ι, _, J, hcard, ⟨eK⟩⟩ := ih K hK
    refine ⟨Option ι, inferInstance, fun o => o.elim I J, by simp [hcard], ⟨?_⟩⟩
    exact e ≪≫ₗ LinearEquiv.prodComm R _ _ ≪≫ₗ
      LinearEquiv.prodCongr (LinearEquiv.refl R _) eK ≪≫ₗ
      (LinearEquiv.piOptionEquivProd R (M := fun o => ((o.elim I J : (Ideal R)⁰) : Ideal R))).symm

theorem exists_finite_reps [Finite (ClassGroup R)] (q : ℕ) :
    ∃ (n : ℕ) (Y : Fin n → ModuleCat.{0} R), ∀ (X : Type) [AddCommGroup X] [Module R X]
      [Module.Finite R X] [Module.Projective R X], Module.finrank R X ≤ q →
      ∃ k, Nonempty (X ≃ₗ[R] Y k) := by
  let rep : ClassGroup R → Ideal R := fun c => ((ClassGroup.mk0_surjective c).choose : Ideal R)
  have hrep : ∀ c : ClassGroup R, ClassGroup.mk0 (ClassGroup.mk0_surjective c).choose = c :=
    fun c => (ClassGroup.mk0_surjective c).choose_spec
  let S := Σ r : Fin (q + 1), (Fin r → ClassGroup R)
  let Y' : S → ModuleCat.{0} R := fun s => ModuleCat.of R ((b : Fin s.1) → rep (s.2 b))
  obtain ⟨n, ⟨eS⟩⟩ := Finite.exists_equiv_fin S
  refine ⟨n, fun k => Y' (eS.symm k), ?_⟩
  intro X _ _ _ _ hX
  obtain ⟨ι, _, I, hcard, ⟨e⟩⟩ := exists_equiv_pi (R := R) (Module.finrank R X) X rfl
  let eι := Fintype.equivFin ι
  let s : S := ⟨⟨Fintype.card ι, by omega⟩, fun b => ClassGroup.mk0 (I (eι.symm b))⟩
  refine ⟨eS s, ?_⟩
  show Nonempty (X ≃ₗ[R] Y' (eS.symm (eS s)))
  rw [Equiv.symm_apply_apply]
  have hI : ∀ i, Nonempty ((I i : Ideal R) ≃ₗ[R] rep (ClassGroup.mk0 (I i))) := fun i =>
    nonempty_equiv_of_mk0_eq (hrep _).symm
  exact ⟨e ≪≫ₗ LinearEquiv.piCongrRight (fun i => (hI i).some) ≪≫ₗ
    LinearEquiv.piCongrLeft' R (fun i => ↥(rep (ClassGroup.mk0 (I i)))) eι⟩

theorem finitely_many_iso_classes : ∀ (E : Type) [Field E] [NumberField E] (q : ℕ),
    ∃ (n : ℕ) (Y : Fin n → ModuleCat.{0} (𝓞 E)), ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
      [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q →
      ∃ k, Nonempty (X ≃ₗ[𝓞 E] Y k) := by
  intro E _ _ q
  exact exists_finite_reps q

end GlobalTheory.ProjModFinIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankSpanImage
section
open Module

noncomputable section

namespace GlobalTheory.RatSpan

section Lin

variable {K' V' W : Type} [Field K'] [AddCommGroup V'] [Module K' V'] [AddCommGroup W] [Module ℂ W]
  {σ' : K' →+* ℂ} (j' : V' →ₛₗ[σ'] W)

private theorem span_range_le_comap_span_image {κ : Type} (x : κ → V') :
    Submodule.span K' (Set.range x) ≤ (Submodule.span ℂ (Set.range fun k => j' (x k))).comap j' := by
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact Submodule.subset_span ⟨k, rfl⟩

private theorem linearIndependent_image_basis_of_linearIndependent {ι' : Type} [Fintype ι'] (b' : Basis ι' K' V')
    (hb : LinearIndependent ℂ fun i => j' (b' i)) {κ : Type} [Fintype κ] (c : Basis κ K' V') :
    LinearIndependent ℂ fun k => j' (c k) := by
  have := Module.Finite.of_basis b'
  have hcard : Fintype.card ι' = Fintype.card κ := by
    rw [← Module.finrank_eq_card_basis b', ← Module.finrank_eq_card_basis c]
  have hle : Submodule.span ℂ (Set.range fun i => j' (b' i)) ≤
      Submodule.span ℂ (Set.range fun k => j' (c k)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : b' i ∈ Submodule.span K' (Set.range c) := by rw [c.span_eq]; trivial
    exact span_range_le_comap_span_image j' c hi
  have : Module.Finite ℂ (Submodule.span ℂ (Set.range fun k => j' (c k))) :=
    Module.Finite.span_of_finite ℂ (Set.finite_range _)
  rw [linearIndependent_iff_card_eq_finrank_span]
  apply le_antisymm
  · rw [← hcard, linearIndependent_iff_card_eq_finrank_span.mp hb]
    exact Submodule.finrank_mono hle
  · exact finrank_range_le_card _

theorem linInd_comp {ι' : Type} [Fintype ι'] (b' : Basis ι' K' V') (hb : LinearIndependent ℂ fun i => j' (b' i))
    {κ : Type} {x : κ → V'} (hx : LinearIndependent K' x) : LinearIndependent ℂ fun k => j' (x k) := by
  have := Module.Finite.of_basis b'
  have hs : LinearIndepOn K' id (Set.range x) := (linearIndepOn_id_range_iff hx.injective).mpr hx
  have : Fintype (hs.extend (Set.subset_univ _)) := by
    have := Module.Finite.finite_basis (Basis.extend hs)
    exact Fintype.ofFinite _
  have he := linearIndependent_image_basis_of_linearIndependent j' b' hb (Basis.extend hs)
  let g : κ → hs.extend (Set.subset_univ _) := fun k => ⟨x k, Basis.subset_extend hs ⟨k, rfl⟩⟩
  have hg : Function.Injective g := fun a b h => hx.injective (congrArg Subtype.val h)
  have h2 := he.comp g hg
  simpa [g, Function.comp_def, Basis.coe_extend] using h2

end Lin

section Main

variable {K K' V V' W : Type} [Field K] [Field K'] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K' V']
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {σ : K →+* ℂ} {σ' : K' →+* ℂ}

theorem finrank_span_image (j' : V' →ₛₗ[σ'] W) {ι' : Type} [Fintype ι'] (b' : Basis ι' K' V')
    (hb : LinearIndependent ℂ fun i => j' (b' i)) (X : Submodule K' V') :
    finrank ℂ (Submodule.span ℂ (j' '' X)) = finrank K' X := by
  have := Module.Finite.of_basis b'
  let e := Module.finBasis K' X
  let x : Fin (finrank K' X) → V' := fun i => (e i : V')
  have hx : LinearIndependent K' x := e.linearIndependent.map' X.subtype X.ker_subtype
  have hjx := linInd_comp j' b' hb hx
  have hspan : Submodule.span ℂ (j' '' X) = Submodule.span ℂ (Set.range fun i => j' (x i)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨v, hv, rfl⟩
      have hvx : v ∈ Submodule.span K' (Set.range x) := by
        have h1 : (⟨v, hv⟩ : X) ∈ Submodule.span K' (Set.range e) := by rw [e.span_eq]; trivial
        have h2 := Submodule.mem_map_of_mem (f := X.subtype) h1
        rw [Submodule.map_span, ← Set.range_comp] at h2
        exact h2
      exact span_range_le_comap_span_image j' x hvx
    · apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨x i, (e i).2, rfl⟩
  rw [hspan, finrank_span_eq_card hjx, Fintype.card_fin]

theorem comap_eq_span (j : V →ₛₗ[σ] W) (j' : V' →ₛₗ[σ'] W) (ι : V → V') (hj : ∀ v, j' (ι v) = j v)
    {ι' : Type} [Fintype ι'] (b' : Basis ι' K' V') (hb : LinearIndependent ℂ fun i => j' (b' i))
    (U : Submodule ℂ W) (hU : U ≤ Submodule.span ℂ (j '' (U.comap j))) :
    U.comap j' = Submodule.span K' (ι '' (U.comap j)) := by
  have := Module.Finite.of_basis b'
  have hle : Submodule.span K' (ι '' (U.comap j)) ≤ U.comap j' := by
    rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    show j' (ι v) ∈ U
    rw [hj]
    exact hv
  symm
  apply Submodule.eq_of_le_of_finrank_le hle
  rw [← finrank_span_image j' b' hb, ← finrank_span_image j' b' hb]
  calc finrank ℂ (Submodule.span ℂ (j' '' (U.comap j'))) ≤ finrank ℂ U := by
        apply Submodule.finrank_mono
        rw [Submodule.span_le]
        rintro _ ⟨v, hv, rfl⟩
        exact hv
    _ ≤ finrank ℂ (Submodule.span ℂ (j' '' (Submodule.span K' (ι '' (U.comap j))))) := by
        apply Submodule.finrank_mono
        refine hU.trans (Submodule.span_mono ?_)
        rintro _ ⟨v, hv, rfl⟩
        exact ⟨ι v, Submodule.subset_span ⟨v, hv, rfl⟩, hj v⟩

end Main

end GlobalTheory.RatSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatComapMapOfOneTmulMem
section
open scoped TensorProduct

namespace GlobalTheory

theorem flat_comap_map_of_one_tmul_mem {B C R : Type} [CommRing B] [CommRing C] [CommRing R]
    [Algebra B C] [Algebra B R] [Module.Flat B R] (J : Ideal C) (r : R)
    (h : (1 : C) ⊗ₜ[B] r ∈ J.map (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[B] R)) :
    r ∈ (J.comap (algebraMap B C)).map (algebraMap B R) := by
  let f : B →ₗ[B] C ⧸ J := (Ideal.Quotient.mkₐ B J).toLinearMap ∘ₗ Algebra.linearMap B C
  have hex := Module.Flat.rTensor_exact R (LinearMap.exact_subtype_ker_map f)
  let φ : C ⊗[B] R →ₐ[B] (C ⧸ J) ⊗[B] R :=
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ B J) (AlgHom.id B R)
  have hle : J.map (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[B] R) ≤
      RingHom.ker φ.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro j hj
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    show φ (j ⊗ₜ[B] (1 : R)) = 0
    simp [φ, Algebra.TensorProduct.map_tmul, (Ideal.Quotient.eq_zero_iff_mem).2 hj]
  have h0 : LinearMap.rTensor R f ((1 : B) ⊗ₜ[B] r) = 0 := by
    have := hle h
    rw [RingHom.mem_ker] at this
    simpa [f, φ, LinearMap.rTensor_tmul, Algebra.TensorProduct.map_tmul] using this
  obtain ⟨x, hx⟩ := (hex ((1 : B) ⊗ₜ[B] r)).1 h0
  have key : ∀ y : (LinearMap.ker f) ⊗[B] R,
      TensorProduct.lid B R (LinearMap.rTensor R (LinearMap.ker f).subtype y) ∈
        (J.comap (algebraMap B C)).map (algebraMap B R) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul i s =>
      simp only [LinearMap.rTensor_tmul, Submodule.coe_subtype, TensorProduct.lid_tmul]
      rw [Algebra.smul_def]
      apply Ideal.mul_mem_right
      apply Ideal.mem_map_of_mem
      have hi := i.2
      rw [LinearMap.mem_ker] at hi
      simp only [f, LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply,
        AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hi
      exact hi
    | add a b ha hb => simpa [map_add] using Ideal.add_mem _ ha hb
  have := key x
  rwa [hx, TensorProduct.lid_tmul, one_smul] at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatTensorEmbedsTensorFractionFields
section
open TensorProduct

namespace GlobalTheory

theorem flat_tensor_embeds_tensor_fractionFields
    (T U C F K L : Type) [CommRing T] [IsDomain T] [CommRing U] [IsDomain U] [CommRing C]
    [IsDomain C] [Field F] [Field K] [Field L] [Algebra T U] [Algebra T C] [Algebra T F]
    [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L]
    [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L]
    [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L] [Module.Flat T U] :
    ∃ φ : U ⊗[T] C →+* L ⊗[F] K, Function.Injective φ ∧
      ∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c := by
  have hF : Module.Flat T F := IsLocalization.flat F (nonZeroDivisors T)
  have hK : Module.Flat T K := Module.Flat.trans T F K
  let f : U →ₐ[T] L := IsScalarTower.toAlgHom T U L
  let g : C →ₐ[T] K := IsScalarTower.toAlgHom T C K
  let e : L ⊗[F] K ≃ₐ[F] L ⊗[T] K :=
    IsLocalization.algebraTensorEquiv (nonZeroDivisors T) F L K
  refine ⟨(e.symm.toRingHom : L ⊗[T] K →+* L ⊗[F] K).comp
    (Algebra.TensorProduct.map f g).toRingHom, ?_, ?_⟩
  · have hf : Function.Injective f.toLinearMap := IsFractionRing.injective U L
    have hg : Function.Injective g.toLinearMap := IsFractionRing.injective C K
    have h1 : Function.Injective (LinearMap.lTensor U g.toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hg
    have h2 : Function.Injective (LinearMap.rTensor K f.toLinearMap) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ hf
    have h3 : Function.Injective (TensorProduct.map f.toLinearMap g.toLinearMap) := by
      rw [← LinearMap.rTensor_comp_lTensor]
      exact h2.comp h1
    intro x y hxy
    apply h3
    exact e.symm.injective hxy
  · intro u c
    show e.symm (f u ⊗ₜ g c) = _
    rw [AlgEquiv.symm_apply_eq]
    rfl

end GlobalTheory
end

