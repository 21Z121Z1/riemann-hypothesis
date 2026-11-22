import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQuotBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRepresentativeAverage
section
open MeasureTheory
open scoped ContDiff

namespace GlobalTheory.LocRep

open MeasureTheory in
open scoped ContDiff Pointwise in

theorem _root_.GlobalTheory.LocRep.exists_continuous_rep_average : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ι : K → G → ℂ), (∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖) → (∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) → ∀ (ρ : G →* (K →L[ℂ] K)), (∀ g v, ‖ρ g v‖ = ‖v‖) → (∀ v, Continuous fun g => ρ g v) → (∀ g v, ι (ρ g v) =ᵐ[μ] fun x => ι v (x * g)) → ∀ (η : G → ℂ) (v : K), Continuous η → HasCompactSupport η → ∃ φ : G → ℂ, Continuous φ ∧ ι (∫ y, η y • ρ y v ∂μ) =ᵐ[μ] φ := by
  intro G _ _ _ _ _ _ _ _ μ _ K _ _ _ ι hloc hlin ρ hnorm hcont htrans η v hηc hηs
  have hιv : LocallyIntegrable (ι v) μ := _root_.GlobalTheory.LocRep.locallyIntegrable_rep hloc v
  obtain ⟨B, hB⟩ := hηc.bounded_above_of_compact_support hηs
  set φ : G → ℂ := fun x => ∫ y, η y * ι v (x * y) ∂μ with hφdef
  have hφeq : φ = fun x => ∫ z, η (x⁻¹ * z) * ι v z ∂μ := by
    funext x
    rw [hφdef, ← integral_mul_left_eq_self (fun z => η (x⁻¹ * z) * ι v z) x]
    simp
  have hφc : Continuous φ := by
    rw [hφeq, continuous_iff_continuousAt]
    intro x₀
    obtain ⟨V, hV, hVn⟩ := exists_compact_mem_nhds x₀
    have hL : IsCompact (V * tsupport η) := hV.mul hηs
    refine continuousAt_of_dominated (bound := (V * tsupport η).indicator fun z => B * ‖ι v z‖)
      (Filter.Eventually.of_forall fun x =>
        ((hηc.comp (continuous_const.mul continuous_id)).aestronglyMeasurable).mul
          hιv.aestronglyMeasurable) ?_ ?_
      (Filter.Eventually.of_forall fun z =>
        ((hηc.comp (continuous_id.inv.mul continuous_const)).mul continuous_const).continuousAt)
    · filter_upwards [hVn] with x hx
      refine Filter.Eventually.of_forall fun z => ?_
      by_cases hz : η (x⁻¹ * z) = 0
      · rw [hz, zero_mul, norm_zero]
        exact Set.indicator_nonneg
          (fun _ _ => mul_nonneg ((norm_nonneg _).trans (hB 1)) (norm_nonneg _)) _
      have hzL : z ∈ V * tsupport η := by
        have := Set.mul_mem_mul hx (subset_tsupport η hz)
        rwa [mul_inv_cancel_left] at this
      rw [Set.indicator_of_mem hzL, norm_mul]
      exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
    · exact IntegrableOn.integrable_indicator
        ((hιv.integrableOn_isCompact hL).norm.const_mul B) hL.measurableSet
  refine ⟨φ, hφc, _root_.GlobalTheory.LocRep.rep_of_pairing hloc hφc.locallyIntegrable ?_⟩
  intro C hC
  obtain ⟨Λ, hΛ⟩ := _root_.GlobalTheory.LocRep.exists_pairing hloc hlin hC
  obtain ⟨M, hM⟩ := hloc C hC
  have hint : Integrable (fun y => η y • ρ y v) μ :=
    (hηc.smul (hcont v)).integrable_of_hasCompactSupport hηs.smul_right
  have hηI : Integrable η μ := hηc.integrable_of_hasCompactSupport hηs
  have hrestr : μ.prod (μ.restrict C) = (μ.prod μ).restrict (Set.univ ×ˢ C) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hmeas : AEStronglyMeasurable (fun p : G × G => η p.1 * ι v (p.2 * p.1))
      (μ.prod (μ.restrict C)) := by
    have h1 : AEStronglyMeasurable (fun p : G × G => ι v (p.2 * p.1)) (μ.prod μ) :=
      (hιv.aestronglyMeasurable.comp_snd (μ := μ)).comp_measurePreserving
        (measurePreserving_prod_mul_swap μ μ)
    rw [hrestr]
    exact ((hηc.comp continuous_fst).aestronglyMeasurable).mul h1.restrict
  have hslice : ∀ y, IntegrableOn (fun x => ι v (x * y)) C μ ∧
      ∫ x in C, ‖ι v (x * y)‖ ∂μ ≤ M * ‖v‖ := by
    intro y
    have hae : ι (ρ y v) =ᵐ[μ.restrict C] fun x => ι v (x * y) := ae_restrict_of_ae (htrans y v)
    obtain ⟨h1, h2⟩ := hM (ρ y v)
    refine ⟨h1.congr_fun_ae hae, ?_⟩
    rw [← hnorm y v]
    refine le_of_eq_of_le (integral_congr_ae (hae.mono fun x hx => ?_)).symm h2
    simp only [hx]
  have hprod : Integrable (Function.uncurry fun y x => η y * ι v (x * y))
      (μ.prod (μ.restrict C)) := by
    refine (integrable_prod_iff hmeas).2 ⟨Filter.Eventually.of_forall fun y =>
      (hslice y).1.const_mul (η y), ?_⟩
    refine Integrable.mono' (hηI.norm.mul_const (M * ‖v‖)) hmeas.norm.integral_prod_right' ?_
    refine Filter.Eventually.of_forall fun y => ?_
    simp only [norm_mul, Function.uncurry_apply_pair]
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => by positivity), integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hslice y).2 (norm_nonneg _)
  calc ∫ x in C, ι (∫ y, η y • ρ y v ∂μ) x ∂μ = Λ (∫ y, η y • ρ y v ∂μ) := (hΛ _).symm
    _ = ∫ y, Λ (η y • ρ y v) ∂μ := (Λ.integral_comp_comm hint).symm
    _ = ∫ y, ∫ x in C, η y * ι v (x * y) ∂μ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        rw [map_smul, hΛ, smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_of_ae (htrans y v)] with x hx
        rw [hx]
    _ = ∫ x in C, φ x ∂μ := integral_integral_swap hprod

end GlobalTheory.LocRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinateProjectionComplexStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coordinate_projection_complex : ∀ (g : ℕ) (K : Type) (ρ : K → Fin g → ℝ), (∀ j k, j ≠ k → ∃ a, ρ a j ≠ ρ a k) →
    ∀ (T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)),
    (∀ a, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v, T (fun m ↦ (ρ a m : ℂ) * v m) = M (T v)) →
    ∀ j : Fin g, ∃ q : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v, q (T v) = T (Pi.single j (v j)) := by
  first | exact @GlobalTheory.realDiag_conj_coordProj | exact GlobalTheory.realDiag_conj_coordProj | (intros; apply GlobalTheory.realDiag_conj_coordProj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordsRangeIdempotentOfRetractStatement
section
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coords_range_idempotent_of_retract : ∀ {C : Type} [CommRing C] [IsLocalRing C] (I : Ideal C), I ≠ ⊤ →
  ∀ {W : Type u} [AddCommGroup W] [Module C W] (m : ℕ) (s : W →ₗ[C] (Fin m → C ⧸ I))
  (r : (Fin m → C ⧸ I) →ₗ[C] W), r ∘ₗ s = LinearMap.id →
  ∀ (p : Module.End C W), p * p = p →
  ∃ (n : ℕ) (b : Fin n → W) (f : Fin n → W →ₗ[C] C ⧸ I),
    (∀ k, b k ∈ LinearMap.range p) ∧ (∀ k w, f k (p w) = f k w) ∧
    (∀ j k, f j (b k) = if j = k then 1 else 0) ∧
    (∀ w ∈ LinearMap.range p, (∀ k, f k w = 0) → w = 0) := by
  first | exact @GlobalTheory.idem_retract_coords | exact GlobalTheory.idem_retract_coords | (intros; apply GlobalTheory.idem_retract_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeIdealMulEqSpanNumberFieldStatement
section
open scoped NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_ideal_mul_eq_span_numberField : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime → ∀ (w : Ideal (𝓞 F)), w ≠ ⊥ → ∃ (g e : 𝓞 F) (𝔟 : Ideal (𝓞 F)), g ≠ 0 ∧ e ∈ w ∧ 1 - e ∈ 𝔟 ∧ w * 𝔟 = Ideal.span {g} ∧ 𝔟 ⊔ Ideal.span {(p : 𝓞 F)} = ⊤ := by
  first | (exact @GlobalTheory.IdealPrincipalCoprime.exists_mul_eq_span_coprime) | (exact GlobalTheory.IdealPrincipalCoprime.exists_mul_eq_span_coprime) | (intros; apply GlobalTheory.IdealPrincipalCoprime.exists_mul_eq_span_coprime  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeIntegerInIdealStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_integer_in_ideal : ∀ (K : Type) [Field K] [NumberField K] (c : Ideal (𝓞 K)) (l : ℕ), l.Prime → c ≠ ⊥ →
    (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ c → (l : 𝓞 K) ∉ v.asIdeal) → ∃ m : ℕ, m.Coprime l ∧ (m : 𝓞 K) ∈ c := by
  first | exact @GlobalTheory.NormCoprime.exists_coprime_mem | exact GlobalTheory.NormCoprime.exists_coprime_mem | (intros; apply GlobalTheory.NormCoprime.exists_coprime_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulIsIntegralOfPadicIntegral
section
open scoped TensorProduct Classical
open Polynomial

namespace GlobalTheory.IntegralDescent

theorem not_dvd_den_coeff_minpoly (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (ℓ : ℕ) [Fact ℓ.Prime] (w : E) (hw : IsIntegral ℤ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w)) (i : ℕ) :
    ¬ ℓ ∣ ((minpoly ℚ w).coeff i).den := by
  obtain ⟨p, hpm, hp⟩ := hw
  have hzi : IsIntegral ℚ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w) := IsIntegral.of_finite _ _
  have hdvd : minpoly ℚ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w) ∣ p.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) := by
    apply minpoly.dvd
    rw [aeval_def, eval₂_map]
    exact hp
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ_[ℓ] hpm hdvd
  rw [(minpoly.monic hzi).leadingCoeff, C_1, mul_one, GlobalTheory.DescCoeff.minpoly_one_tmul_eq] at hg
  have hc := congrArg (fun q => q.coeff i) hg
  simp only [coeff_map] at hc
  have hn : ‖(((minpoly ℚ w).coeff i : ℚ) : ℚ_[ℓ])‖ ≤ 1 := by
    rw [← eq_ratCast (algebraMap ℚ ℚ_[ℓ]), ← hc]
    exact (g.coeff i).2
  intro hd
  have hu := PadicInt.isUnit_den _ hn
  exact PadicInt.irreducible_p.not_isUnit
    (isUnit_of_dvd_unit (Nat.cast_dvd_cast (α := ℤ_[ℓ]) hd) hu)

theorem exists_not_dvd_isIntegral_mul : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (ℓ : ℕ) [Fact ℓ.Prime] (w : E), IsIntegral ℤ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w) → ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * w) := by
  intro E _ _ _ ℓ hℓ w hw
  set f := minpoly ℚ w with hf
  have hfm : f.Monic := minpoly.monic (IsIntegral.of_finite ℚ w)
  set d : ℕ := ∏ i ∈ Finset.range f.natDegree, (f.coeff i).den with hd
  refine ⟨d, ?_, ?_⟩
  · intro h
    obtain ⟨i, -, hi⟩ := (hℓ.out.prime.dvd_finsetProd_iff _).mp h
    exact not_dvd_den_coeff_minpoly E ℓ w hw i hi
  · have hroot : aeval ((d : E) * w) (f.scaleRoots (d : ℚ)) = 0 := by
      have := scaleRoots_aeval_eq_zero (r := (d : ℚ)) (minpoly.aeval ℚ w)
      rwa [map_natCast] at this
    have hlift : f.scaleRoots (d : ℚ) ∈ Polynomial.lifts (algebraMap ℤ ℚ) := by
      rw [lifts_iff_coeff_lifts]
      intro i
      rw [coeff_scaleRoots]
      rcases lt_trichotomy i f.natDegree with hi | hi | hi
      · obtain ⟨c, hc⟩ : (f.coeff i).den ∣ d :=
          Finset.dvd_prod_of_mem (fun j => (f.coeff j).den) (Finset.mem_range.mpr hi)
        obtain ⟨k, hk⟩ : ∃ k, f.natDegree - i = k + 1 := ⟨f.natDegree - i - 1, by omega⟩
        refine ⟨(f.coeff i).num * c * (d : ℤ) ^ k, ?_⟩
        rw [hk, pow_succ]
        have h1 : (d : ℚ) = ((f.coeff i).den : ℚ) * c := by exact_mod_cast hc
        have h2 : f.coeff i * ((f.coeff i).den : ℚ) = (f.coeff i).num := Rat.mul_den_eq_num _
        simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
        rw [← h2]
        linear_combination (-(f.coeff i) * (d : ℚ) ^ k) * h1
      · subst hi
        exact ⟨1, by simp [hfm.coeff_natDegree]⟩
      · exact ⟨0, by simp [coeff_eq_zero_of_natDegree_lt hi]⟩
    obtain ⟨q, hq, -, hqm⟩ :=
      lifts_and_natDegree_eq_and_monic hlift ((monic_scaleRoots_iff _).mpr hfm)
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ, hq]
    exact hroot

end GlobalTheory.IntegralDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCornerUnitOfRightInverseStatement
section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_corner_unit_of_right_inverse' : ∀ {F R : Type} [Field F] [CommRing R] [Algebra F R] (e : R), e * e = e → (∀ ψ : Polynomial R, (∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0) → ∃ t : F, IsUnit (e * ψ.eval (algebraMap F R t) + (1 - e))) → ∀ {n : ℕ} (D C P Q : Matrix (Fin n) (Fin n) R), D * P + C * Q = 1 → ∃ x : Matrix (Fin n) (Fin n) R, IsUnit (e * (D + C * x).det + (1 - e)) := by
  first | exact @GlobalTheory.exists_corner_unit_of_right_inverse | exact GlobalTheory.exists_corner_unit_of_right_inverse | (intros; apply GlobalTheory.exists_corner_unit_of_right_inverse <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCyclicGeneratorsSeparableMin
section
open scoped TensorProduct nonZeroDivisors
open Polynomial

namespace GlobalTheory

theorem semisimple_charpoly_pow_generators (κ : Type) [Field κ] [IsAlgClosed κ] (G : Type)
    [AddCommGroup G] [Module κ G] [FiniteDimensional κ G] (T : Module.End κ G) (h : κ[X])
    (hm : h.Monic) (hs : h.Separable) (h0 : aeval T h = 0) (N : ℕ)
    (hc : LinearMap.charpoly T = h ^ N) :
    ∃ x : Fin N → G, ∀ v : G, ∃ p : Fin N → κ[X], v = ∑ j, aeval T (p j) (x j) := by
  classical
  have hne : h ≠ 0 := hm.ne_zero
  have hsemi : T.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs.squarefree h0
  have hgen : ∀ μ, T.maxGenEigenspace μ = T.eigenspace μ :=
    fun μ => hsemi.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ

  have hev : ∀ (q : κ[X]) (ν : κ) (v : G), v ∈ T.eigenspace ν → aeval T q v = eval ν q • v := by
    intro q ν v hv
    by_cases hv0 : v = 0
    · simp [hv0]
    · exact Module.End.aeval_apply_of_hasEigenvector (Module.End.hasEigenvector_iff.2 ⟨hv, hv0⟩)
  set R : Finset κ := h.roots.toFinset with hR
  have hmemR : ∀ μ, μ ∈ R ↔ h.IsRoot μ := fun μ => by
    rw [hR, Multiset.mem_toFinset, mem_roots hne]

  have hfr : ∀ μ ∈ R, Module.finrank κ (T.eigenspace μ) = N := by
    intro μ hμ
    have hμ' : μ ∈ h.roots := Multiset.mem_toFinset.1 hμ
    rw [← hgen, LinearMap.finrank_maxGenEigenspace_eq, hc, ← count_roots, roots_pow,
      Multiset.count_nsmul, Multiset.count_eq_one_of_mem (nodup_roots hs) hμ', mul_one]

  have hout : ∀ μ, μ ∉ R → ∀ v ∈ T.eigenspace μ, v = 0 := by
    intro μ hμ v hv
    by_contra hv0
    apply hμ
    rw [hmemR]
    have h1 := hev h μ v hv
    rw [h0] at h1
    have h2 : eval μ h • v = 0 := by simpa using h1.symm
    exact (smul_eq_zero.1 h2).resolve_right hv0
  have hbasis : ∀ μ ∈ R, ∃ b : Fin N → G, (∀ j, b j ∈ T.eigenspace μ) ∧
      ∀ v ∈ T.eigenspace μ, ∃ c : Fin N → κ, v = ∑ j, c j • b j := by
    intro μ hμ
    let B := Module.finBasisOfFinrankEq κ (T.eigenspace μ) (hfr μ hμ)
    refine ⟨fun j => (B j : G), fun j => (B j).2, fun v hv => ⟨B.repr ⟨v, hv⟩, ?_⟩⟩
    have h2 := congrArg Subtype.val (B.sum_repr ⟨v, hv⟩)
    push_cast at h2
    exact h2.symm
  choose! b hbmem hbspan using hbasis
  refine ⟨fun j => ∑ μ ∈ R, b μ j, fun v => ?_⟩
  have hinj : Set.InjOn (id : κ → κ) R := Function.injective_id.injOn

  have hpick : ∀ μ ∈ R, ∀ j, aeval T (Lagrange.basis R id μ) (∑ ν ∈ R, b ν j) = b μ j := by
    intro μ hμ j
    rw [map_sum, Finset.sum_eq_single μ]
    · rw [hev _ μ _ (hbmem μ hμ j)]
      have := Lagrange.eval_basis_self hinj hμ
      simp only [id] at this
      rw [this, one_smul]
    · intro ν hν hne'
      rw [hev _ ν _ (hbmem ν hν j)]
      have := Lagrange.eval_basis_of_ne (v := id) hne'.symm hν
      simp only [id] at this
      rw [this, zero_smul]
    · intro h'
      exact absurd hμ h'
  have htop : v ∈ ⨆ μ, T.eigenspace μ := by
    have : (⨆ μ, T.eigenspace μ) = ⊤ := by
      rw [← Module.End.iSup_maxGenEigenspace_eq_top T]
      exact iSup_congr fun μ => (hgen μ).symm
    rw [this]
    exact Submodule.mem_top
  induction htop using Submodule.iSup_induction' with
  | mem μ w hw =>
    by_cases hμ : μ ∈ R
    · obtain ⟨c, rfl⟩ := hbspan μ hμ w hw
      refine ⟨fun j => C (c j) * Lagrange.basis R id μ, ?_⟩
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, aeval_C, Module.End.mul_apply, hpick μ hμ j]
      simp [Module.algebraMap_end_apply]
    · rw [hout μ hμ w hw]
      exact ⟨0, by simp⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨p, rfl⟩ := hy
    obtain ⟨q, rfl⟩ := hz
    refine ⟨p + q, ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [map_add, Finset.sum_add_distrib]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegLtTwoCorrectionSimple
section
open Polynomial

namespace GlobalTheory.PicDiv

theorem exists_deg_lt_two_correction_simple :
    ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A]
      [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A]
      [Module.Free k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) (P₀ : Ideal A) (w : A),
      P₀.IsMaximal → ∃ p : Fin n → k[X], (∀ i, (p i).degree < (2 : ℕ)) ∧
        w + ∑ i, p i • b i ∈ P₀ ∧ w + ∑ i, p i • b i ∉ P₀ ^ 2 := by
  intro k A _ _ _ _ _ _ _ _ _ n b P₀ w hP
  haveI : Algebra.FiniteType k A := Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  obtain ⟨φ, hφ⟩ := ((GlobalTheory.DedekindCodimG.dedekind_finiteType_codim k A).2.1 P₀ hP).2
  set α : k := φ (algebraMap k[X] A X) with hα
  have hC : algebraMap k[X] A (C α) = algebraMap k A α := by
    rw [IsScalarTower.algebraMap_apply k k[X] A]; rfl
  have hlin : algebraMap k[X] A (X - C α) ∈ P₀ := by
    rw [hφ, map_sub, map_sub, hC, φ.commutes, ← hα]
    simp
  have hne : algebraMap k[X] A (X - C α) ≠ 0 := by
    intro h0
    have h1 : (X - C α) • (1 : A) = 0 := by rw [Algebra.smul_def, h0, zero_mul]
    have h3 : b.repr (1 : A) ≠ 0 := by
      rw [Ne, LinearEquiv.map_eq_zero_iff]; exact one_ne_zero
    obtain ⟨i, hi⟩ := DFunLike.ne_iff.mp h3
    have h4 := congrArg (fun a => b.repr a i) h1
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero,
      Pi.zero_apply] at h4
    exact mul_ne_zero (X_sub_C_ne_zero α) hi h4
  have hbot : P₀ ≠ ⊥ := fun h => hne (by rw [h] at hlin; simpa using hlin)
  have hlt := Ideal.pow_lt_self P₀ hbot hP.ne_top 2 le_rfl
  obtain ⟨π, hπP, hπ2⟩ := SetLike.exists_of_lt hlt
  set q : k[X] := (X - C α) ^ 2 with hq
  have hmon : q.Monic := (monic_X_sub_C α).pow 2
  have hqdeg : q.degree = (2 : ℕ) := by
    rw [hq, degree_pow, degree_X_sub_C]; rfl
  have hqmem : algebraMap k[X] A q ∈ P₀ ^ 2 := by
    rw [hq, map_pow]; exact Ideal.pow_mem_pow hlin 2
  let c : Fin n → k[X] := fun i => b.repr (π - w) i
  let p : Fin n → k[X] := fun i => c i %ₘ q
  let d : Fin n → k[X] := fun i => c i /ₘ q
  have hs : ∑ i, c i • b i = π - w := b.sum_repr (π - w)
  have h2 : ∑ i, c i • b i = ∑ i, p i • b i + algebraMap k[X] A q * ∑ i, d i • b i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Algebra.smul_def, smul_smul, ← add_smul]
    exact congrArg (· • b i) (modByMonic_add_div (c i) q).symm
  have key : w + ∑ i, p i • b i = π - algebraMap k[X] A q * ∑ i, d i • b i := by
    linear_combination hs - h2
  have hM : algebraMap k[X] A q * ∑ i, d i • b i ∈ P₀ ^ 2 := Ideal.mul_mem_right _ _ hqmem
  refine ⟨p, fun i => ?_, ?_, ?_⟩
  · rw [← hqdeg]; exact degree_modByMonic_lt _ hmon
  · rw [key]; exact P₀.sub_mem hπP (Ideal.pow_le_self two_ne_zero hM)
  · intro h
    apply hπ2
    have : π = (w + ∑ i, p i • b i) + algebraMap k[X] A q * ∑ i, d i • b i := by
      rw [key]; ring
    rw [this]; exact (P₀ ^ 2).add_mem h hM

end GlobalTheory.PicDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationEqOneOfPowMemStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_eq_one_of_pow_mem' : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] (L : Subfield K) (f : K), f ∉ L → f ^ p ∈ L → IntermediateField.adjoin L ({f} : Set K) = ⊤ → ∃ D : Derivation L K K, D f = 1 := by
  first | exact @GlobalTheory.exists_derivation_eq_one_of_pow_mem | exact GlobalTheory.exists_derivation_eq_one_of_pow_mem | (intros; apply GlobalTheory.exists_derivation_eq_one_of_pow_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendingCotangentFormStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_extending_cotangent_form : ∀ (R B : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] [CommRing B] [IsLocalRing B] [Algebra R B], (∀ r : R, r ≠ 0 → IsUnit (algebraMap R B r)) → ∀ (lam : CotangentSpace B →ₗ[ResidueField B] ResidueField B), ∃ δ : Derivation R B (ResidueField B), ∀ y (hy : y ∈ maximalIdeal B), δ y = lam ((maximalIdeal B).toCotangent ⟨y, hy⟩) := by
  first | exact @GlobalTheory.ConormalDer.exists_derivation_extending | exact GlobalTheory.ConormalDer.exists_derivation_extending | (intros; apply GlobalTheory.ConormalDer.exists_derivation_extending <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendingKernelFormOfLiftingStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_extending_kernel_form_of_lifting : ∀ (A P R K : Type) [CommRing A] [CommRing P] [IsNoetherianRing P] [CommRing R] [Field K] [Algebra A P] [Algebra A R] [Algebra P R] [IsScalarTower A P R] [Algebra R K] [Algebra P K] [IsScalarTower P R K] [Algebra A K] [IsScalarTower A P K], Function.Surjective (algebraMap P R) → Function.Surjective (algebraMap R K) → (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (β : A →+* C) (φ₀ : R →+* C₀), φ₀.comp (algebraMap A R) = π.comp β → ∃ φ : R →+* C, π.comp φ = φ₀ ∧ φ.comp (algebraMap A R) = β) → ∀ ℓ : RingHom.ker (algebraMap P R) →ₗ[P] K, ∃ D : Derivation A P K, ∀ i : RingHom.ker (algebraMap P R), D i = ℓ i := by
  first | exact @GlobalTheory.LiftDeriv.exists_derivation_extending | exact GlobalTheory.LiftDeriv.exists_derivation_extending | (intros; apply GlobalTheory.LiftDeriv.exists_derivation_extending <;> assumption)
end

