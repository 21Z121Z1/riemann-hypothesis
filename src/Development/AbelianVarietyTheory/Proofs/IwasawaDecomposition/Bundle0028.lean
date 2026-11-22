import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodicLeftHalfPlaneShiftNonnegOfImPosStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_left_halfPlane_shift_nonneg_of_im_pos : ∀ (c : ℝ) (f : ℂ → ℂ) (m : ℤ), DifferentiableOn ℂ f {s : ℂ | s.re < c} → (∀ s : ℂ, s.re < c → f (s + 2 * Real.pi * Complex.I) = f s + m) → (∀ s : ℂ, s.re < c → 0 < (f s).im) → 0 ≤ m := by
  first | exact @GlobalTheory.periodic_strip_shift_nonneg | exact GlobalTheory.periodic_strip_shift_nonneg | (intros; apply GlobalTheory.periodic_strip_shift_nonneg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyDerivRenameOfConvex
section
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)

namespace GlobalTheory.ConvexCutOff

theorem exists_support {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {K : Set V} (hK : Convex ℝ K) (hne : K.Nonempty) {x : V} (hx : x ∉ interior K) :
    ∃ f : V →L[ℝ] ℝ, f ≠ 0 ∧ ∀ y ∈ K, f y ≤ f x := by
  by_cases hi : (interior K).Nonempty
  · obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hK.interior isOpen_interior hx
    refine ⟨f, ?_, ?_⟩
    · rintro rfl
      obtain ⟨a, ha⟩ := hi
      simpa using hf a ha
    · intro y hy
      have h1 : y ∈ closure (interior K) := by
        rw [hK.closure_interior_eq_closure_of_nonempty_interior hi]
        exact subset_closure hy
      have h2 : IsClosed {z | f z ≤ f x} := isClosed_le f.continuous continuous_const
      exact closure_minimal (fun a ha => (hf a ha).le) h2 h1
  · rw [hK.interior_nonempty_iff_affineSpan_eq_top] at hi
    obtain ⟨k, hk⟩ := hne
    have hd : (affineSpan ℝ K).direction < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro h
      exact hi ((AffineSubspace.direction_eq_top_iff_of_nonempty
        ⟨k, subset_affineSpan ℝ K hk⟩).1 h)
    obtain ⟨g, hg0, hg⟩ := Submodule.exists_le_ker_of_lt_top _ hd
    have hc : ∀ y ∈ K, g y = g k := by
      intro y hy
      have := hg (AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ K hy)
        (subset_affineSpan ℝ K hk))
      simpa [sub_eq_zero] using this
    have hg1 : LinearMap.toContinuousLinearMap g ≠ 0 := by
      intro h
      apply hg0
      ext z
      simpa using congrArg (fun φ : V →L[ℝ] ℝ => φ z) h
    rcases le_total (g k) (g x) with h | h
    · exact ⟨LinearMap.toContinuousLinearMap g, hg1, fun y hy => by simpa [hc y hy] using h⟩
    · exact ⟨-LinearMap.toContinuousLinearMap g, neg_ne_zero.2 hg1,
        fun y hy => by simpa [hc y hy] using h⟩

theorem uniqueDiffWithinAt_compl {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {K : Set V} (hK : Convex ℝ K) {x : V} (hx : x ∉ interior K) :
    UniqueDiffWithinAt ℝ Kᶜ x := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simpa using uniqueDiffWithinAt_univ
  obtain ⟨f, hf0, hf⟩ := exists_support hK hne hx
  obtain ⟨v, hv⟩ : ∃ v, 0 < f v := by
    obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
      by_contra h
      push_neg at h
      exact hf0 (ContinuousLinearMap.ext h)
    rcases lt_or_gt_of_ne hw with h | h
    · exact ⟨-w, by simpa using h⟩
    · exact ⟨w, h⟩
  have hH : Convex ℝ {y | f x < f y} := convex_halfSpace_gt f.toLinearMap.isLinear (f x)
  have hO : IsOpen {y | f x < f y} := isOpen_lt continuous_const f.continuous
  have hcl : x ∈ closure {y | f x < f y} := by
    have ht : Filter.Tendsto (fun t : ℝ => x + t • v) (nhdsWithin 0 (Set.Ioi 0)) (nhds x) := by
      have : Continuous (fun t : ℝ => x + t • v) := by fun_prop
      have h2 := this.tendsto 0
      simp only [zero_smul, add_zero] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    simp only [Set.mem_setOf_eq, map_add, map_smul, smul_eq_mul]
    nlinarith [mul_pos ht' hv]
  have hU := uniqueDiffWithinAt_convex hH (by
    rw [hO.interior_eq]
    exact ⟨x + v, by simpa using hv⟩) hcl
  exact hU.mono fun y hy hyK => absurd (hf y hyK) (not_le.2 hy)

theorem fderiv_eq_zero {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] {K : Set V} (hK : Convex ℝ K) {G : V → W}
    (hG : ∀ z, z ∉ K → G z = 0) {x : V} (hx : x ∉ interior K) : fderiv ℂ G x = 0 := by
  by_cases hd : DifferentiableAt ℂ G x
  swap
  · exact fderiv_zero_of_not_differentiableAt hd
  have hU := uniqueDiffWithinAt_compl hK hx
  have hx0 : G x = 0 := by
    have := hd.continuousAt.continuousWithinAt.mem_closure_image hU.mem_closure
    have hs : G '' Kᶜ ⊆ {0} := by
      rintro _ ⟨z, hz, rfl⟩
      exact hG z hz
    exact closure_minimal hs isClosed_singleton this
  have h1 : HasFDerivWithinAt G ((fderiv ℂ G x).restrictScalars ℝ) Kᶜ x :=
    (hd.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have h2 : HasFDerivWithinAt G (0 : V →L[ℝ] W) Kᶜ x :=
    (hasFDerivWithinAt_const (0 : W) x Kᶜ).congr (fun z hz => hG z hz) hx0
  have h3 := hU.eq h1 h2
  ext z
  simpa using congrArg (fun φ : V →L[ℝ] W => φ z) h3

theorem iteratedFDeriv_eq_zero_off {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {K : Set V} (hK : Convex ℝ K) {F : V → ℂ}
    (hF : ∀ z, z ∉ K → F z = 0) (n : ℕ) : ∀ z, z ∉ K → iteratedFDeriv ℂ n F z = 0 := by
  induction n with
  | zero =>
    intro z hz
    ext m
    simp [hF z hz]
  | succ n ih =>
    intro z hz
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
      fderiv_eq_zero hK ih (fun h => hz (interior_subset h))]
    exact map_zero _

theorem iteratedFDeriv_symm {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {K : Set V} (hK : Convex ℝ K) {F : V → ℂ}
    (hF : ∀ z, z ∉ K → F z = 0) (hd : DifferentiableOn ℂ F (interior K)) (x : V) (n : ℕ)
    (v : Fin n → V) (σ : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℂ n F x (v ∘ σ) = iteratedFDeriv ℂ n F x v := by
  by_cases hx : x ∈ interior K
  · exact (GlobalTheory.SCV.analyticOnNhd_of_differentiableOn isOpen_interior hd x
      hx).contDiffAt.iteratedFDeriv_comp_perm v σ
  · cases n with
    | zero => simp
    | succ n =>
      have : iteratedFDeriv ℂ (n + 1) F x = 0 := by
        rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
          fderiv_eq_zero hK (iteratedFDeriv_eq_zero_off hK hF n) hx]
        exact map_zero _
      simp [this]

theorem exists_perm_of_ofFn_perm {α : Type} {n : ℕ} (v w : Fin n → α)
    (h : (List.ofFn v).Perm (List.ofFn w)) : ∃ σ : Equiv.Perm (Fin n), v = w ∘ σ := by
  first
  | exact @_root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm
  | exact _root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm
  | (apply _root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm ..)

theorem term_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {F : V → ℂ} {x : V}
    (hs : ∀ (n : ℕ) (v : Fin n → V) (σ : Equiv.Perm (Fin n)),
      iteratedFDeriv ℂ n F x (v ∘ σ) = iteratedFDeriv ℂ n F x v)
    {n m : ℕ} (v : Fin n → V) (w : Fin m → V) (h : (List.ofFn v).Perm (List.ofFn w)) :
    iteratedFDeriv ℂ n F x v = iteratedFDeriv ℂ m F x w := by
  have hnm : n = m := by simpa using h.length_eq
  subst hnm
  obtain ⟨σ, rfl⟩ := exists_perm_of_ofFn_perm v w h
  exact hs n w σ

theorem ofFn_get_cast {α β : Type} (l : List α) {n : ℕ} (u : α → β) (h : n = l.length) :
    List.ofFn (fun k : Fin n => u (l.get (Fin.cast h k))) = l.map u := by
  subst h
  apply List.ext_getElem <;> simp

theorem polyDeriv_rename_of_convex : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (K : Set V) (F : V → ℂ), Convex ℝ K → (∀ z, z ∉ K → F z = 0) → DifferentiableOn ℂ F (interior K) → ∀ (x : V) (ι κ : Type) (ρ : ι → κ), Function.Injective ρ → ∀ (Q : MvPolynomial ι ℂ) (u : κ → V), polyDeriv (MvPolynomial.rename ρ Q) u F x = polyDeriv Q (u ∘ ρ) F x := by
  intro V _ _ _ K F hK hF hd x ι κ ρ hρ Q u
  classical
  unfold polyDeriv
  rw [MvPolynomial.support_rename_of_injective hρ,
    Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hρ h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain ρ hρ]
  congr 1
  apply term_eq (iteratedFDeriv_symm hK hF hd x)
  rw [ofFn_get_cast, ofFn_get_cast, ← List.map_map]
  apply List.Perm.map
  rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, Multiset.coe_toList,
    Finsupp.toMultiset_map]

end GlobalTheory.ConvexCutOff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialApproxPowMaximalStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_approx_pow_maximal : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] (φ : A →+* R), (maximalIdeal A).map φ = maximalIdeal R → ∀ θ : R, (∀ r : R, ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R) → ∀ (n : ℕ) (r : R), ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R ^ n := by
  first | exact @GlobalTheory.exists_poly_sub_mem_maximalIdeal_pow | exact GlobalTheory.exists_poly_sub_mem_maximalIdeal_pow | (intros; apply GlobalTheory.exists_poly_sub_mem_maximalIdeal_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialApproxUniquenessStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_approx_uniqueness : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] (φ : A →+* R), φ.Flat → (maximalIdeal A).map φ = maximalIdeal R → ∀ (θ : R) (q : Polynomial A), q.Monic → (q.map φ).eval θ = 0 → (∀ (n : ℕ) (r : R), ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R ^ n) → (∀ P : Polynomial A, P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R → ∀ i, P.coeff i ∈ maximalIdeal A) → ∀ (n : ℕ) (P : Polynomial A), P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R ^ n → ∀ i, P.coeff i ∈ maximalIdeal A ^ n := by
  first | exact @GlobalTheory.coeff_mem_pow_of_flat_of_indep_mod_max | exact GlobalTheory.coeff_mem_pow_of_flat_of_indep_mod_max | (intros; apply GlobalTheory.coeff_mem_pow_of_flat_of_indep_mod_max <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefQuadMarginStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_margin_quadForm_pos_of_perturbation : ∀ {ι : Type} [Fintype ι] (M : ι → ι → ℝ), (∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * M i j) → ∃ η : ℝ, 0 < η ∧ ∀ E : ι → ι → ℝ, (∀ i j, |E i j| ≤ η) → ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * (M i j + E i j) := by
  first | exact @GlobalTheory.posDef_quad_margin | exact GlobalTheory.posDef_quad_margin | (intros; apply GlobalTheory.posDef_quad_margin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosSemidefRealOfIntQuadFormNonnegStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.posSemidef_real_of_int_quadForm_nonneg : ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℤ), B.IsSymm → (∀ v : Fin g → ℤ, 0 ≤ dotProduct v (B.mulVec v)) → (B.map (Int.cast : ℤ → ℝ)).PosSemidef := by
  first | exact @GlobalTheory.intSymm_posSemidef_real | exact GlobalTheory.intSymm_posSemidef_real | (intros; apply GlobalTheory.intSymm_posSemidef_real <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageGenericFiberIsOpen
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GenericFibreOpen

theorem range_spMap_algebraMap_eq (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] :
    Set.range (spMap (algebraMap O K)) = {x : Sp O | (x : PrimeSpectrum O).asIdeal = ⊥} := by
  have key : ∀ y : Sp K, ((spMap (algebraMap O K)).base y : PrimeSpectrum O).asIdeal = ⊥ := fun y => by
    change Ideal.comap (algebraMap O K) (y : PrimeSpectrum K).asIdeal = ⊥
    rw [(Ideal.eq_bot_or_top (y : PrimeSpectrum K).asIdeal).resolve_right (y : PrimeSpectrum K).isPrime.ne_top]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact key y
  · intro hx
    refine ⟨(show Sp K from (default : PrimeSpectrum K)), ?_⟩
    apply PrimeSpectrum.ext
    exact (key _).trans hx.symm

end GlobalTheory.GenericFibreOpen

open GlobalTheory.GenericFibreOpen in

theorem GlobalTheory.GenericFibreOpen.isOpen_preimage_range_spMap_fraction :
    ∀ (O K R : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [CommRing R]
      [IsLocalRing R] (g : Sp R ⟶ Sp O), IsOpen (g ⁻¹' Set.range (spMap (algebraMap O K))) := by
  intro O K R _ _ _ _ _ _ _ g
  rw [range_spMap_algebraMap_eq O K]
  have hc : Continuous g.base := g.base.hom.continuous
  set c : Sp R := (IsLocalRing.closedPoint R : PrimeSpectrum R)
  have hle : ∀ x : Sp R, ((g.base x : Sp O) : PrimeSpectrum O).asIdeal ≤ ((g.base c : Sp O) : PrimeSpectrum O).asIdeal := by
    intro x
    have hs : (x : PrimeSpectrum R) ⤳ IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint _
    exact (PrimeSpectrum.le_iff_specializes _ _).2 (hs.map hc)
  by_cases hp : ((g.base c : Sp O) : PrimeSpectrum O).asIdeal = ⊥
  · have : (fun x : Sp R => g.base x) ⁻¹' {x : Sp O | (x : PrimeSpectrum O).asIdeal = ⊥} = Set.univ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact le_bot_iff.1 (hp ▸ hle x)
    exact this ▸ isOpen_univ
  · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
    have hmax : ((g.base c : Sp O) : PrimeSpectrum O).asIdeal.IsMaximal :=
      ((g.base c : Sp O) : PrimeSpectrum O).isPrime.isMaximal hp
    have : (fun x : Sp R => g.base x) ⁻¹' {x : Sp O | (x : PrimeSpectrum O).asIdeal = ⊥} =
        (fun x : Sp R => g.base x) ⁻¹' (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum O)) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · intro h hx
        rw [h, Ideal.mem_bot] at hx
        exact ha0 hx
      · intro hx
        by_contra hne
        have hq : ((g.base x : Sp O) : PrimeSpectrum O).asIdeal.IsMaximal :=
          ((g.base x : Sp O) : PrimeSpectrum O).isPrime.isMaximal hne
        have heq := hq.eq_of_le hmax.ne_top (hle x)
        exact hx (heq ▸ ha)
    rw [this]
    exact (PrimeSpectrum.basicOpen a).isOpen.preimage hc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeIdealsCountingBounds
section
open NumberField IsDedekindDomain

namespace GlobalTheory.Mem.FewPrimes

variable {K : Type} [Field K] [NumberField K]

theorem prod_absNorm_dvd (s : Finset (HeightOneSpectrum (𝓞 K))) (I : Ideal (𝓞 K))
    (h : ∀ v ∈ s, v.asIdeal ∣ I) :
    ∏ v ∈ s, Ideal.absNorm v.asIdeal ∣ Ideal.absNorm I := by
  have h1 : ∏ v ∈ s, v.asIdeal ∣ I :=
    Finset.prod_dvd_of_coprime
      (fun a _ b _ hab => HeightOneSpectrum.isCoprime_of_ne _ _ hab) h
  rw [← map_prod]
  exact map_dvd _ h1

theorem finite_absNorm_le (X : ℝ) :
    {v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal : ℝ) ≤ X}.Finite := by
  have h := Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊X⌋₊
  have h2 := h.preimage (f := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab)
  refine h2.subset ?_
  intro v hv
  exact Nat.le_floor hv

theorem exists_prime_mem (v : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ v.asIdeal := by
  first
  | exact @_root_.GlobalTheory.PrimeInHeightOneSpectrum.target
  | exact _root_.GlobalTheory.PrimeInHeightOneSpectrum.target
  | (apply _root_.GlobalTheory.PrimeInHeightOneSpectrum.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeInHeightOneSpectrum.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeInHeightOneSpectrum.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeInHeightOneSpectrum.target ..)

theorem exists_eq_span (hK : Module.finrank ℚ K = 2) (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ (Ideal.absNorm v.asIdeal).Prime) :
    ∃ p : ℕ, p.Prime ∧ v.asIdeal = Ideal.span {(p : 𝓞 K)} ∧ Ideal.absNorm v.asIdeal = p ^ 2 := by
  obtain ⟨p, hp, hm⟩ := exists_prime_mem v
  have hd : v.asIdeal ∣ Ideal.span {(p : 𝓞 K)} := Ideal.dvd_span_singleton.2 hm
  have hN : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, hK]
  have h1 := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have h2 : Ideal.absNorm v.asIdeal ∣ p ^ 2 := hN ▸ map_dvd _ hd
  obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow hp).1 h2
  have h3 : Ideal.absNorm v.asIdeal = p ^ 2 := by
    interval_cases i
    · rw [pow_zero] at he; exact absurd he h1.ne'
    · rw [pow_one] at he; exact absurd (he ▸ hp) hv
    · exact he
  refine ⟨p, hp, ?_, h3⟩
  obtain ⟨J, hJ⟩ := hd
  have h4 : Ideal.absNorm J = 1 := by
    have h5 := hN
    rw [hJ, map_mul, h3] at h5
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) (by rw [h5, mul_one])
  rw [Ideal.absNorm_eq_one_iff] at h4
  rw [hJ, h4, Ideal.mul_top]

theorem ncard_not_prime_le (hK : Module.finrank ℚ K = 2) (X : ℝ) :
    ({v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal : ℝ) ≤ X ∧
      ¬ (Ideal.absNorm v.asIdeal).Prime}.ncard : ℝ) ≤ Real.sqrt X := by
  have h : {v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal : ℝ) ≤ X ∧
      ¬ (Ideal.absNorm v.asIdeal).Prime}.ncard ≤
      ((Finset.Icc 1 ⌊Real.sqrt X⌋₊ : Finset ℕ) : Set ℕ).ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun v => Nat.sqrt (Ideal.absNorm v.asIdeal)) ?_ ?_
      (Finset.finite_toSet _)
    · rintro v ⟨hX, hv⟩
      obtain ⟨p, hp, -, h3⟩ := exists_eq_span hK v hv
      rw [h3] at hX
      simp only [h3, Nat.sqrt_eq', Finset.coe_Icc, Set.mem_Icc]
      refine ⟨hp.pos, Nat.le_floor ?_⟩
      apply Real.le_sqrt_of_sq_le
      exact_mod_cast hX
    · rintro v ⟨-, hv⟩ w ⟨-, hw⟩ hvw
      obtain ⟨p, hp, e1, h3⟩ := exists_eq_span hK v hv
      obtain ⟨q, hq, e2, h4⟩ := exists_eq_span hK w hw
      simp only [h3, h4, Nat.sqrt_eq'] at hvw
      apply HeightOneSpectrum.ext
      rw [e1, e2, hvw]
  rw [Set.ncard_coe_finset, Nat.card_Icc, Nat.add_sub_cancel] at h
  exact le_trans (by exact_mod_cast h) (Nat.floor_le (Real.sqrt_nonneg X))

theorem ncard_absNorm_eq_le (hK : Module.finrank ℚ K = 2) (p : ℕ) (hp : p.Prime) :
    {v : HeightOneSpectrum (𝓞 K) | Ideal.absNorm v.asIdeal = p}.ncard ≤ 2 := by
  have hf : {v : HeightOneSpectrum (𝓞 K) | Ideal.absNorm v.asIdeal = p}.Finite :=
    (finite_absNorm_le (K := K) p).subset (fun v hv => by
      have hv' : Ideal.absNorm v.asIdeal = p := hv
      show (Ideal.absNorm v.asIdeal : ℝ) ≤ p
      rw [hv'])
  have h := prod_absNorm_dvd hf.toFinset (Ideal.span {(p : 𝓞 K)}) (fun v hv => by
    have hv' : Ideal.absNorm v.asIdeal = p := by simpa using hv
    rw [Ideal.dvd_span_singleton, ← hv']
    exact Ideal.absNorm_mem _)
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, hK,
    Finset.prod_congr rfl (g := fun _ => p) (fun v hv => by simpa using hv),
    Finset.prod_const] at h
  rw [Set.ncard_eq_toFinset_card _ hf]
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h

theorem ncard_dvd_le (𝔮 : Ideal (𝓞 K)) (hq : 𝔮 ≠ ⊥) :
    ({v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔮}.ncard : ℝ) ≤
      3 * Real.log (4 * Ideal.absNorm 𝔮) := by
  have hf : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔮}.Finite := Ideal.finite_factors hq
  have hN : Ideal.absNorm 𝔮 ≠ 0 := fun h => hq (Ideal.absNorm_eq_zero_iff.1 h)
  have h := Nat.le_of_dvd (Nat.pos_of_ne_zero hN)
    (prod_absNorm_dvd hf.toFinset 𝔮 (fun v hv => by simpa using hv))
  have h2 : 2 ^ hf.toFinset.card ≤ Ideal.absNorm 𝔮 :=
    le_trans (Finset.pow_card_le_prod _ _ _
      (fun v _ => NumberField.HeightOneSpectrum.one_lt_absNorm v)) h
  rw [Set.ncard_eq_toFinset_card _ hf]
  have h3 : (2 : ℝ) ^ hf.toFinset.card ≤ 4 * Ideal.absNorm 𝔮 := by
    have : ((2 ^ hf.toFinset.card : ℕ) : ℝ) ≤ Ideal.absNorm 𝔮 := by exact_mod_cast h2
    push_cast at this
    have h0 : (0 : ℝ) ≤ Ideal.absNorm 𝔮 := Nat.cast_nonneg _
    linarith
  have h4 := Real.log_le_log (by positivity) h3
  rw [Real.log_pow] at h4
  have h5 := Real.log_two_gt_d9
  have h6 : (0 : ℝ) ≤ hf.toFinset.card := Nat.cast_nonneg _
  nlinarith

theorem few_primes : ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → Module.finrank ℚ K = 2 → (∀ X : ℝ, 1 ≤ X → {v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal : ℝ) ≤ X}.Finite ∧ ({v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal : ℝ) ≤ X ∧ ¬ (Ideal.absNorm v.asIdeal).Prime}.ncard : ℝ) ≤ Real.sqrt X) ∧ (∀ p : ℕ, p.Prime → {v : HeightOneSpectrum (𝓞 K) | Ideal.absNorm v.asIdeal = p}.ncard ≤ 2) ∧ ∀ 𝔮 : Ideal (𝓞 K), 𝔮 ≠ ⊥ → ({v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔮}.ncard : ℝ) ≤ 3 * Real.log (4 * Ideal.absNorm 𝔮) :=
  fun _ _ _ _ hK => ⟨fun X _ => ⟨finite_absNorm_le X, ncard_not_prime_le hK X⟩,
    ncard_absNorm_eq_le hK, ncard_dvd_le⟩

end GlobalTheory.Mem.FewPrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatAlternatingOrthogonalOrthogonalLeStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_of_orthogonal_orthogonal_of_skew_det_ne_zero : ∀ (r : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (V : Submodule ℚ (Fin r → ℚ)), Mqᵀ = -Mq → Mq.det ≠ 0 → ∀ x : Fin r → ℚ, (∀ y : Fin r → ℚ, (∀ w ∈ V, y ⬝ᵥ Mq *ᵥ w = 0) → x ⬝ᵥ Mq *ᵥ y = 0) → x ∈ V := by
  first | exact @GlobalTheory.rat_alternating_orthogonal_orthogonal_le | exact GlobalTheory.rat_alternating_orthogonal_orthogonal_le | (intros; apply GlobalTheory.rat_alternating_orthogonal_orthogonal_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatMemSpanOfRealMemSpanFinStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rat_mem_span_of_real_mem_span_fin : ∀ (k r : ℕ) (w : Fin k → Fin r → ℚ) (v : Fin r → ℚ), (fun j => ((v j : ℚ) : ℝ)) ∈ Submodule.span ℝ (Set.range fun i j => ((w i j : ℚ) : ℝ)) → v ∈ Submodule.span ℚ (Set.range w) := by
  first | exact @GlobalTheory.rat_mem_span_of_real_mem_span | exact GlobalTheory.rat_mem_span_of_real_mem_span | (intros; apply GlobalTheory.rat_mem_span_of_real_mem_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFiniteStatement
section
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueFieldMap_finite_of_quasiFinite : ∀ {Y Z : Scheme.{0}} (g : Y ⟶ Z) [LocallyQuasiFinite g] (y : Y), (g.residueFieldMap y).hom.Finite := by
  first | exact @GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite | exact GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite | (intros; apply GlobalTheory.residueFieldMap_finite_of_locallyQuasiFinite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RightTranslationCurveSqLeAndIntegralDerivEqZeroAStatement
section
open MeasureTheory Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_translation_curve_sq_le_and_integral_deriv_eq_zero_alt : ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [IsProbabilityMeasure μ] (c : ℝ → K), Continuous c → c 0 = 1 → ∀ f f' : K → ℂ, Continuous f → Continuous f' → (∀ x t, HasDerivAt (fun t : ℝ => f (x * c t)) (f' (x * c t)) t) → (∫ x, ‖f (x * c 1) - f x‖ ^ 2 ∂μ ≤ ∫ x, ‖f' x‖ ^ 2 ∂μ) ∧ ∫ x, f' x ∂μ = 0 := by
  first | exact @GlobalTheory.right_translation_curve_sq_le_and_integral_deriv_eq_zero | exact GlobalTheory.right_translation_curve_sq_le_and_integral_deriv_eq_zero | (intros; apply GlobalTheory.right_translation_curve_sq_le_and_integral_deriv_eq_zero <;> assumption)
end

