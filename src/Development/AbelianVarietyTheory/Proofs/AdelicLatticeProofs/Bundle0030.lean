import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsGlIsometryCompEqOfNondegenerate

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AdelicUnitaryScalingUnitStatement
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_unitary_scaling_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → (∀ x, c (c x) = x) → c ≠ 1 → ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) (RA F E)) (e : FiniteAdeleRing (𝓞 F) F), e * e = e → {v | e v ≠ 0}.Finite → ∃ lam : E, lam * c lam = 1 ∧ IsUnit (1 + ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] lam) • ((e ⊗ₜ[F] (1 : E)) • g + ((1 - e) ⊗ₜ[F] (1 : E)) • (1 : Matrix (Fin n) (Fin n) (RA F E)))).det := by
  first | exact @GlobalTheory.UnRep.exists_norm_one_isUnit_det | exact GlobalTheory.UnRep.exists_norm_one_isUnit_det | (intros; apply GlobalTheory.UnRep.exists_norm_one_isUnit_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AlgebraMapNormTensorEqProdConjugatesStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraMap_norm_tensor_eq_prod_galois_conjugates : ∀ (F E K : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E] [CommRing K] [Algebra F K] (y : K ⊗[F] E), algebraMap K (K ⊗[F] E) (Algebra.norm K y) = ∏ g : E ≃ₐ[F] E, Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E) y := by
  first | exact @GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates | exact GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates | (intros; apply GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.BorelHarishChandraStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nsq_act_le_of_isSiegel_of_entries_zero_or_ge : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [LinearOrder ι] (m : ℕ) (d : Fin m → ℕ) (v : TIdx ι d → ℂ), (∀ C : ℝ, ∃ C' : ℝ, ∀ y : Matrix ι ι ℂ, y.det = 1 → nsq (act d v y) ≤ C → ∃ h : Matrix ι ι ℂ, h.det = 1 ∧ act d v h = v ∧ ∀ i j, ‖(h * y) i j‖ ≤ C') → (∀ g : Matrix ι ι ℂ, g.det = 1 → act d v g = v → act d v gᴴ = v) → ∀ C c : ℝ, 0 < c → ∃ C' : ℝ, ∀ (k : Matrix ι ι ℝ) (a : ι → ℝ) (n : Matrix ι ι ℝ), IsSiegel C k a n → (∀ j, act d v ((k * diagonal a * n).map (fun r : ℝ => (r : ℂ))) j = 0 ∨ c ≤ ‖act d v ((k * diagonal a * n).map (fun r : ℝ => (r : ℂ))) j‖) → nsq (act d v ((k * diagonal a * n).map (fun r : ℝ => (r : ℂ)))) ≤ C' := by
  first | exact @GlobalTheory.ClassFin.SiegelBound.borel_harishChandra | exact GlobalTheory.ClassFin.SiegelBound.borel_harishChandra | (intros; apply GlobalTheory.ClassFin.SiegelBound.borel_harishChandra <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CayleyTransformUnitarySkewInvolutiveStatement
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cayleyTransform_unitary_skew_involutive : ∀ (R : Type) [CommRing R] (σ : R →+* R) (n : ℕ) (G : Matrix (Fin n) (Fin n) R), (∀ x, σ (σ x) = x) → (G.map σ)ᵀ = G → IsUnit G.det → IsUnit (2 : R) → (∀ g : Matrix (Fin n) (Fin n) R, gᵀ * G * g.map σ = G → IsUnit (1 + g).det → ((1 - g) * (1 + g)⁻¹)ᵀ * G + G * ((1 - g) * (1 + g)⁻¹).map σ = 0 ∧ IsUnit (1 + (1 - g) * (1 + g)⁻¹ : Matrix (Fin n) (Fin n) R).det) ∧ (∀ g : Matrix (Fin n) (Fin n) R, IsUnit (1 + g).det → (1 - (1 - g) * (1 + g)⁻¹) * (1 + (1 - g) * (1 + g)⁻¹)⁻¹ = g) ∧ (∀ S : Matrix (Fin n) (Fin n) R, Sᵀ * G + G * S.map σ = 0 → IsUnit (1 + S).det → ((1 - S) * (1 + S)⁻¹)ᵀ * G * ((1 - S) * (1 + S)⁻¹).map σ = G) ∧ ∀ A : Matrix (Fin n) (Fin n) R, (A - (G * A.map σ * G⁻¹)ᵀ)ᵀ * G + G * (A - (G * A.map σ * G⁻¹)ᵀ).map σ = 0 := by
  first | exact @GlobalTheory.CayleyInv.cayley_transform | exact GlobalTheory.CayleyInv.cayley_transform | (intros; apply GlobalTheory.CayleyInv.cayley_transform <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousSymmFinite
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors
open scoped Topology

namespace GlobalTheory.AdeleBaseChange

theorem continuous_symm_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ι : FiniteAdeleRing (𝓞 F) F ⊗[F] E ≃+* FiniteAdeleRing (𝓞 E) E), (∀ y, y ∈ AddSubgroup.closure {y : FiniteAdeleRing (𝓞 F) F ⊗[F] E | ∃ a ∈ {a : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F}, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} ↔ ∀ P, Valued.v (ι y P) ≤ 1) → letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E); Continuous ι.symm := by
  intro F E _ _ _ _ _ ι hι
  letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
    moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (FiniteAdeleRing (𝓞 F) F) _
  have h0 := (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat F E 0 ⊤ (Subsingleton.elim _ _)).2
  refine continuous_of_continuousAt_zero ι.symm.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  intro W hW
  obtain ⟨N, hN, hNW⟩ := h0 W hW
  rw [Filter.mem_map]
  refine Filter.mem_of_superset (GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds E N hN) ?_
  rintro _ ⟨a, ha, rfl⟩
  rw [Set.mem_preimage, map_nsmul]
  apply hNW
  have h1 := (hι (ι.symm a)).2 (fun P => by rw [ι.apply_symm_apply]; exact ha P)
  refine AddSubgroup.closure_mono ?_ h1
  rintro _ ⟨b, hb, x, rfl⟩
  exact ⟨b, hb, _, ⟨x, rfl⟩, rfl⟩

end GlobalTheory.AdeleBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CyclicKummerNormFixedHilbert90
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in

theorem _root_.GlobalTheory.CNorm.kummer_basic : ∀ (p : ℕ) (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), _root_.GlobalTheory.CNorm.IsKum p ζ δ θ σ → FiniteDimensional F E ∧ Module.finrank F E = p ∧ (∀ y : E, σ^[p] y = y) ∧ (∀ y : E, σ y = y → ∃ a : F, y = algebraMap F E a) ∧ (∀ y : E, ∏ i ∈ Finset.range p, σ^[i] y = 1 → ∃ z : E, z ≠ 0 ∧ y = σ z / z) ∧ (∀ (u : F) (y : E), y ^ p = algebraMap F E u → ∃ (k : ℕ) (r : F), u = δ ^ k * r ^ p) ∧ ∀ x : Fˣ, x ∈ _root_.GlobalTheory.CNorm.kNorm p (RingHom.id F) δ ↔ ∃ y : E, ∏ i ∈ Finset.range p, σ^[i] y = algebraMap F E (x : F) := by
  intro p F E _ _ _ _ ζ δ θ σ h
  obtain ⟨hfd, hrank, hgal, hord, hgen, ⟨e⟩, -⟩ :=
    _root_.GlobalTheory.CNorm.kummer_galois p F E ζ δ θ σ h
  have hp := h.prime
  classical
  have hprod : ∀ y : E, algebraMap F E (Algebra.norm F y) = ∏ i ∈ Finset.range p, σ^[i] y := by
    intro y
    rw [Algebra.norm_eq_prod_automorphisms]
    have huniv : (Finset.univ : Finset Gal(E/F)) = (Finset.range p).image (σ ^ ·) := by
      ext τ
      simp only [Finset.mem_univ, true_iff]
      rw [← hord]
      exact mem_zpowers_iff_mem_range_orderOf.1 (hgen τ)
    rw [huniv, Finset.prod_image]
    · exact Finset.prod_congr rfl fun i _ => by rw [AlgEquiv.coe_pow]
    · intro i hi j hj hij
      exact pow_injOn_Iio_orderOf (by rw [hord]; simpa using hi) (by rw [hord]; simpa using hj) hij
  have hfix : ∀ y : E, σ y = y → ∃ a : F, y = algebraMap F E a := by
    intro y hy
    have hmem : y ∈ (⊥ : IntermediateField F E) := by
      rw [IsGalois.mem_bot_iff_fixed]
      intro τ
      have hσ : σ ∈ MulAction.stabilizer Gal(E/F) y := MulAction.mem_stabilizer_iff.2 hy
      exact MulAction.mem_stabilizer_iff.1 ((Subgroup.zpowers_le.2 hσ) (hgen τ))
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 hmem
    exact ⟨a, ha.symm⟩
  refine ⟨hfd, hrank, ?_, hfix, ?_, ?_, ?_⟩
  · intro y
    rw [← AlgEquiv.coe_pow, ← hord, pow_orderOf_eq_one]
    rfl
  · intro y hy
    haveI : IsCyclic Gal(E/F) := ⟨⟨σ, fun τ => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen τ)
      exact ⟨k, hk⟩⟩⟩
    have hn : Algebra.norm F y = 1 :=
      (algebraMap F E).injective (by rw [hprod, hy, map_one])
    obtain ⟨z, hz⟩ := groupCohomology.exists_div_of_norm_eq_one hgen hn
    refine ⟨(z : E)⁻¹, inv_ne_zero z.ne_zero, ?_⟩
    rw [map_inv₀, inv_div_inv, hz]
  · intro u y hy
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hζ := h.root.map_of_injective (algebraMap F E).injective
    by_cases hy0 : y = 0
    · refine ⟨1, 0, ?_⟩
      subst hy0
      rw [zero_pow hp.ne_zero] at hy
      have hu : u = 0 := (algebraMap F E).injective (by rw [← hy, map_zero])
      simp [hu, hp.ne_zero]
    · have hσy : (σ y / y) ^ p = 1 := by
        rw [div_pow, ← map_pow, hy, AlgEquiv.commutes, ← hy]
        exact div_self (pow_ne_zero _ hy0)
      obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one hσy
      have hσy' : σ y = algebraMap F E ζ ^ j * y := by
        rw [hj]; field_simp
      have hδ : δ ≠ 0 := by
        intro hδ
        exact h.nonpow 0 (by rw [hδ, zero_pow hp.ne_zero])
      have hθ : θ ≠ 0 := by
        intro hθ
        have := h.pow
        rw [hθ, zero_pow hp.ne_zero, eq_comm, map_eq_zero] at this
        exact hδ this
      have hζ0 : algebraMap F E ζ ≠ 0 := hζ.ne_zero hp.ne_zero
      have hw : σ (y / θ ^ j) = y / θ ^ j := by
        rw [map_div₀, map_pow, h.conj, hσy', mul_pow]
        field_simp
      obtain ⟨a, ha⟩ := hfix _ hw
      have hy' : y = algebraMap F E a * θ ^ j := by
        rw [← ha]; field_simp
      refine ⟨j, a, (algebraMap F E).injective ?_⟩
      rw [← hy, hy', mul_pow, ← pow_mul, mul_comm j p, pow_mul, h.pow]
      simp only [map_mul, map_pow]
      ring
  · intro x
    rw [_root_.GlobalTheory.CNorm.mem_kNorm]
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨e.symm w, ?_⟩
      rw [← hprod, Algebra.norm_eq_of_algEquiv, hw]
      rfl
    · rintro ⟨y, hy⟩
      have hn : Algebra.norm F y = x := (algebraMap F E).injective (by rw [hprod, hy])
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [Algebra.norm_zero] at hn
        exact x.ne_zero hn.symm
      refine ⟨Units.map (e : E →* AdjoinRoot (X ^ p - C δ)) (Units.mk0 y hy0), ?_⟩
      simp only [Units.coe_map, Units.val_mk0, MonoidHom.coe_coe, RingHom.id_apply]
      rw [Algebra.norm_eq_of_algEquiv, hn]

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdmissiblePlacesContainingPrimeSupersetMonStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissiblePlacesContainingPrime_superset_mono : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F], 0 < p → (∀ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∃ S, S₀ ⊆ S ∧ AdmP p F S) ∧ ∀ S T : Finset (HeightOneSpectrum (𝓞 F)), S ⊆ T → AdmP p F S → AdmP p F T := by
  first | exact @GlobalTheory.CNorm.exists_admissiblePlaces_superset_and_mono | exact GlobalTheory.CNorm.exists_admissiblePlaces_superset_and_mono | (intros; apply GlobalTheory.CNorm.exists_admissiblePlaces_superset_and_mono <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAnisotropicOrthogonalBasisHermitianStatement
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_anisotropic_orthogonal_basis_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∃ x : Fin n → Fin n → E, (∀ i, hermE c G (x i) (x i) ≠ 0) ∧ (∀ i j, i ≠ j → hermE c G (x i) (x j) = 0) ∧ Submodule.span E (Set.range x) = ⊤ := by
  first | exact @GlobalTheory.UnRep.exists_anisotropic_orthogonal_basis | exact GlobalTheory.UnRep.exists_anisotropic_orthogonal_basis | (intros; apply GlobalTheory.UnRep.exists_anisotropic_orthogonal_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsApproxModPowersStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_approx_mod_powers' : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (y : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F), 0 < p → (∀ v, y v ≠ 0) → ∃ x : F, x ≠ 0 ∧ ∀ v ∈ S, ∃ r : v.adicCompletion F, algebraMap F (v.adicCompletion F) x = y v * r ^ p := by
  first | exact @GlobalTheory.CNorm.exists_approx_mod_powers | exact GlobalTheory.CNorm.exists_approx_mod_powers | (intros; apply GlobalTheory.CNorm.exists_approx_mod_powers <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCommonDenominatorNilpotentCoboundaryStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_denominator_nilpotent_coboundary : ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra ℚ B] [Algebra B A] [Algebra.FiniteType B A] [IsReduced A] [Nontrivial B], Function.Injective (algebraMap B A) → ∀ s : Finset A, (∀ f ∈ s, IsNilpotent (f ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] f)) → ∃ b : B, b ≠ 0 ∧ ∀ f ∈ s, ∃ b' : B, algebraMap B A b * f = algebraMap B A b' := by
  first | exact @GlobalTheory.exists_common_denominator_of_isNilpotent | exact GlobalTheory.exists_common_denominator_of_isNilpotent | (intros; apply GlobalTheory.exists_common_denominator_of_isNilpotent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometric
section
open scoped Matrix

namespace GlobalTheory.LocalQuad.TraceIsometry

open Module

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {c : E →+* E}

theorem finiteDimensional_of_involution (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    (hF : ∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t) : FiniteDimensional F E := by
  classical
  obtain ⟨δ, hδ⟩ : ∃ δ : E, ∀ x : E, ∃ s t : F, x = s • (1 : E) + t • δ := by
    by_cases h : ∀ t, c t = t
    · refine ⟨0, fun x => ?_⟩
      obtain ⟨s, hs⟩ := (hF x).1 (h x)
      exact ⟨s, 0, by simp [Algebra.smul_def, hs]⟩
    · push Not at h
      obtain ⟨u, hu⟩ := h
      have hne : u - c u ≠ 0 := sub_ne_zero.2 hu.symm
      have hne' : c u - u ≠ 0 := sub_ne_zero.2 hu
      refine ⟨u - c u, fun x => ?_⟩
      obtain ⟨s, hs⟩ := (hF ((x + c x) / 2)).1 (by
        rw [map_div₀, map_add, hc, map_ofNat, add_comm])
      obtain ⟨t, ht⟩ := (hF ((x - c x) / (2 * (u - c u)))).1 (by
        rw [map_div₀, map_sub, hc, map_mul, map_ofNat, map_sub, hc]
        field_simp
        ring)
      refine ⟨s, t, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, hs, ht]
      field_simp
      ring
  refine Module.finite_def.2 ⟨{1, δ}, ?_⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨s, t, rfl⟩ := hδ x
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem exists_traceForm (hF : ∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t)
    {V : Type*} [AddCommGroup V] [Module E V] [Module F V] [IsScalarTower F E V]
    {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x) :
    ∃ b : V →ₗ[F] V →ₗ[F] F, ∀ x y, algebraMap F E (b x y) = B x y + B y x := by
  have h : ∀ x y, ∃ s : F, algebraMap F E s = B x y + B y x := fun x y =>
    (hF _).1 (by rw [map_add, hB, hB, add_comm])
  choose b hb using h
  have hi := (algebraMap F E).injective
  have hs : ∀ s : F, c (algebraMap F E s) = algebraMap F E s := fun s => (hF _).2 ⟨s, rfl⟩
  refine ⟨LinearMap.mk₂ F b (fun x x' y => hi ?_) (fun s x y => hi ?_) (fun x y y' => hi ?_)
    (fun s x y => hi ?_), hb⟩
  · simp only [map_add, hb, LinearMap.add_apply]
    ring
  · rw [smul_eq_mul, map_mul, hb, hb, ← algebraMap_smul E s x]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, hs, smul_eq_mul]
    ring
  · simp only [map_add, hb, LinearMap.add_apply]
    ring
  · rw [smul_eq_mul, map_mul, hb, hb, ← algebraMap_smul E s y]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, hs, smul_eq_mul]
    ring

theorem trace_eq_of_apply_self_eq {V W : Type*} [AddCommGroup V] [Module E V] [AddCommGroup W]
    [Module E W] {B : V →ₗ[E] V →ₛₗ[c] E} {B' : W →ₗ[E] W →ₛₗ[c] E} {φ : V → W}
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (hφ : ∀ x, B' (φ x) (φ x) = B x x) (x y : V) :
    B' (φ x) (φ y) + B' (φ y) (φ x) = B x y + B y x := by
  have h := hφ (x + y)
  rw [hadd] at h
  simp only [map_add, LinearMap.add_apply, hφ] at h
  linear_combination h

theorem exists_map_smul_eq (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    (hF : ∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t)
    {V W : Type*} [AddCommGroup V] [Module E V] [Module F V] [IsScalarTower F E V]
    [AddCommGroup W] [Module E W] [Module F W] [IsScalarTower F E W]
    {B : V →ₗ[E] V →ₛₗ[c] E} {B' : W →ₗ[E] W →ₛₗ[c] E} (hB' : ∀ x y, c (B' x y) = B' y x)
    (φ : V →ₗ[F] W) (hφ : ∀ x, B' (φ x) (φ x) = B x x) {e : V} (he : B e e ≠ 0) :
    ∃ φ' : V →ₗ[F] W, (∀ x, B' (φ' x) (φ' x) = B x x) ∧ ∀ t : E, φ' (t • e) = t • φ e := by
  have := finiteDimensional_of_involution h2 hc hF
  obtain ⟨b, hb⟩ := exists_traceForm hF hB'
  have hi := (algebraMap F E).injective
  have h2F : (2 : F) ≠ 0 := fun h => h2 (by
    rw [← map_ofNat (algebraMap F E) 2, h, map_zero])
  have hp := trace_eq_of_apply_self_eq (map_add φ) hφ
  obtain ⟨γ, hγ, hγe⟩ := GlobalTheory.HermWitt.exists_isometry_comp_eq_of_nondegenerate
    (c := RingHom.id F) h2F (B := b)
    (fun x y => hi (by rw [RingHom.id_apply, hb, hb, add_comm]))
    (g := φ ∘ₗ (LinearMap.toSpanSingleton E V e).restrictScalars F)
    (f := (LinearMap.toSpanSingleton E W (φ e)).restrictScalars F)
    (fun s t => hi (by
      simp only [hb, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        LinearMap.toSpanSingleton_apply, hp, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hφ]))
    (fun s hs => by
      have h := congrArg (algebraMap F E) (hs s)
      simp only [hb, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        LinearMap.toSpanSingleton_apply, hφ, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
        map_zero, smul_eq_mul, RingHom.id_apply] at h
      by_contra hne
      exact mul_ne_zero h2 (mul_ne_zero ((map_ne_zero c).2 hne) (mul_ne_zero hne he))
        (by linear_combination h))
  refine ⟨γ.toLinearMap ∘ₗ φ, fun x => ?_, fun t => hγe t⟩
  have h := congrArg (algebraMap F E) (hγ (φ x) (φ x))
  rw [hb, hb, hφ] at h
  apply mul_left_cancel₀ h2
  change 2 * B' (γ (φ x)) (γ (φ x)) = _
  linear_combination h

universe u v in

theorem exists_linearMap_isometry (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    (hF : ∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t) (d : ℕ) :
    ∀ {V : Type u} {W : Type v} [AddCommGroup V] [Module E V] [Module F V] [IsScalarTower F E V]
      [FiniteDimensional E V] [AddCommGroup W] [Module E W] [Module F W] [IsScalarTower F E W]
      (B : V →ₗ[E] V →ₛₗ[c] E) (B' : W →ₗ[E] W →ₛₗ[c] E),
      (∀ x y, c (B x y) = B y x) → (∀ x y, c (B' x y) = B' y x) → finrank E V = d →
      ∀ φ : V →ₗ[F] W, (∀ x, B' (φ x) (φ x) = B x x) →
      ∃ ψ : V →ₗ[E] W, ∀ x y, B' (ψ x) (ψ y) = B x y := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V W _ _ _ _ _ _ _ _ _ B B' hB hB' hd φ₀ hφ₀
  obtain rfl | hne := eq_or_ne B 0
  · exact ⟨0, fun x y => by simp⟩
  obtain ⟨e, he⟩ := GlobalTheory.HermDiag.exists_apply_self_ne_zero h2 hB hne
  have hk := GlobalTheory.HermDiag.finrank_ker_flip_add_one he
  obtain ⟨φ, hφ, hφe⟩ := exists_map_smul_eq h2 hc hF hB' φ₀ hφ₀ he
  have hf : B' (φ₀ e) (φ₀ e) = B e e := hφ₀ e
  generalize φ₀ e = f at hφe hf
  have hp := trace_eq_of_apply_self_eq (map_add φ) hφ
  have hker : ∀ x : LinearMap.ker (B.flip e), φ x ∈ LinearMap.ker (B'.flip f) := by
    intro x
    have hx : B x e = 0 := x.2
    have hx' : B e x = 0 := by rw [← hB, hx, map_zero]
    have h := hp x (B' (φ x) f • e)
    rw [hφe] at h
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx, hx', smul_eq_mul,
      RingHom.id_apply, ← hB' (φ x) f] at h
    change B' (φ x) f = 0
    by_contra hne
    exact mul_ne_zero h2 (mul_ne_zero ((map_ne_zero c).2 hne) hne) (by linear_combination h)
  obtain ⟨ψ, hψ⟩ := ih _ (by omega)
    (B.domRestrict₁₂ (LinearMap.ker (B.flip e)) (LinearMap.ker (B.flip e)))
    (B'.domRestrict₁₂ (LinearMap.ker (B'.flip f)) (LinearMap.ker (B'.flip f)))
    (fun y z => hB y z) (fun y z => hB' y z) rfl
    { toFun := fun x => ⟨φ x, hker x⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun s x => Subtype.ext (by simp) }
    (fun x => hφ x)
  replace hψ : ∀ x y : LinearMap.ker (B.flip e), B' (ψ x) (ψ y) = B x y := hψ
  let p : V →ₗ[E] LinearMap.ker (B.flip e) :=
    (LinearMap.id - ((B e e)⁻¹ • B.flip e).smulRight e).codRestrict _ (fun x => by
      have h : (B e e)⁻¹ * B x e * B e e = B x e := by field_simp
      simp [h])
  have hpx : ∀ x, (p x : V) = x - ((B e e)⁻¹ * B x e) • e := fun x => rfl
  refine ⟨(LinearMap.ker (B'.flip f)).subtype ∘ₗ ψ ∘ₗ p + ((B e e)⁻¹ • B.flip e).smulRight f,
    fun x y => ?_⟩
  have h1 : ∀ z, B' (ψ z) f = 0 := fun z => (ψ z).2
  have h3 : ∀ z, B' f (ψ z) = 0 := fun z => by rw [← hB', h1, map_zero]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    LinearMap.smulRight_apply, LinearMap.smul_apply, LinearMap.flip_apply, map_add,
    LinearMap.map_smulₛₗ, h1, h3, hψ, hpx, hf, map_sub, LinearMap.sub_apply, smul_eq_mul,
    RingHom.id_apply, map_mul, map_inv₀, hB]
  field_simp
  ring

end GlobalTheory.LocalQuad.TraceIsometry

theorem GlobalTheory.LocalQuad.exists_congr_iff_trace_forms_isometric {F E : Type*} [Field F] [Field E]
    [Algebra F E] (h2 : (2 : E) ≠ 0) (c : E →+* E) (hc : ∀ t, c (c t) = t)
    (hF : ∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t)
    {n : Type*} [Fintype n] [DecidableEq n] {G G' : Matrix n n E}
    (hG : ∀ a b, c (G a b) = G b a) (hG' : ∀ a b, c (G' a b) = G' b a)
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0) :
    (∃ P : Matrix n n E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map c) ↔
      ∃ φ : (n → E) ≃ₗ[F] (n → E),
        ∀ x, x ⬝ᵥ G' *ᵥ (c ∘ x) = φ x ⬝ᵥ G *ᵥ (c ∘ φ x) := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    refine ⟨(Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P hP.isUnit)).restrictScalars F,
      fun x => ?_⟩
    rw [GlobalTheory.HermWitt.dotProduct_congr_mulVec]
    rfl
  · rintro ⟨φ, hφ⟩
    obtain ⟨ψ, hψ⟩ := TraceIsometry.exists_linearMap_isometry h2 hc hF _
      (Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c G')
      (Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c G)
      (fun x y => by
        simp only [GlobalTheory.HermDiag.toLinearMapₛₗ₂'_eq_dotProduct,
          GlobalTheory.HermDiag.map_dotProduct_mulVec_comp hc hG'])
      (fun x y => by
        simp only [GlobalTheory.HermDiag.toLinearMapₛₗ₂'_eq_dotProduct,
          GlobalTheory.HermDiag.map_dotProduct_mulVec_comp hc hG])
      rfl φ.toLinearMap
      (fun x => by
        simp only [GlobalTheory.HermDiag.toLinearMapₛₗ₂'_eq_dotProduct]
        exact (hφ x).symm)
    have h : G' = (LinearMap.toMatrix' ψ)ᵀ * G * (LinearMap.toMatrix' ψ).map c := by
      apply (Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c).injective
      refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
      rw [← hψ, GlobalTheory.HermDiag.toLinearMapₛₗ₂'_eq_dotProduct,
        GlobalTheory.HermDiag.toLinearMapₛₗ₂'_eq_dotProduct, GlobalTheory.HermWitt.dotProduct_congr_mulVec,
        LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    refine ⟨_, fun h0 => hd' ?_, h⟩
    rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGlobalUniformizerResidueRepresentativesStatement
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_uniformizer_residue_representatives : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), (∃ π : F, v.valuation F π = WithZero.exp (-1) ∧ Valued.v (algebraMap F (v.adicCompletion F) π) = WithZero.exp (-1)) ∧ (∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x) ∧ (∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (a : F)) < 1) ∧ ∃ R : Finset (v.adicCompletion F), R.card ≤ Ideal.absNorm v.asIdeal ∧ (∀ r ∈ R, Valued.v r ≤ 1) ∧ ∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃ r ∈ R, Valued.v (x - r) < 1 := by
  first | exact @GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives | exact GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives | (intros; apply GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives <;> assumption)
end

