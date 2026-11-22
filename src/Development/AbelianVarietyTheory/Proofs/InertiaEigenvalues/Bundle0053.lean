import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0013
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousCongruenceNearSymmetricMatrix
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem symm_congr_local_continuous : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (H₀ : Matrix (Fin r) (Fin r) F), H₀.IsSymm → H₀.det ≠ 0 →
    ∃ (Ω : Set (Matrix (Fin r) (Fin r) F)) (k : Matrix (Fin r) (Fin r) F → Matrix (Fin r) (Fin r) F),
      IsOpen Ω ∧ H₀ ∈ Ω ∧ ContinuousOn k Ω ∧ k H₀ = 1 ∧ ∀ H ∈ Ω, H.IsSymm → (k H)ᵀ * H₀ * k H = H := by
  intro F E _ _ _ _ hU r H₀ hsym hdet
  haveI : CharZero F := hU.charZero
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  letI : NormedRing (Matrix (Fin r) (Fin r) F) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra F (Matrix (Fin r) (Fin r) F) := Matrix.linftyOpNormedAlgebra
  haveI : @CompleteSpace (Matrix (Fin r) (Fin r) F) PseudoMetricSpace.toUniformSpace := FiniteDimensional.complete F _
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  let L : Matrix (Fin r) (Fin r) F ≃L[F] Matrix (Fin r) (Fin r) F :=
    ContinuousLinearEquiv.equivOfInverse ((2 : F) • ContinuousLinearMap.id F _)
      ((2 : F)⁻¹ • ContinuousLinearMap.id F _)
      (by intro x; simp [smul_smul, inv_mul_cancel₀ h2]) (by intro x; simp [smul_smul, mul_inv_cancel₀ h2])
  have hf : HasStrictFDerivAt (fun Y : Matrix (Fin r) (Fin r) F => Y * Y)
      (L : Matrix (Fin r) (Fin r) F →L[F] Matrix (Fin r) (Fin r) F) 1 := by
    have h := (hasStrictFDerivAt_id (𝕜 := F) (1 : Matrix (Fin r) (Fin r) F)).mul' (hasStrictFDerivAt_id 1)
    have e : (L : Matrix (Fin r) (Fin r) F →L[F] Matrix (Fin r) (Fin r) F) =
        (id 1 : Matrix (Fin r) (Fin r) F) • ContinuousLinearMap.id F (Matrix (Fin r) (Fin r) F) +
          MulOpposite.op (id 1 : Matrix (Fin r) (Fin r) F) • ContinuousLinearMap.id F (Matrix (Fin r) (Fin r) F) := by
      ext1 D
      simp [L, two_smul]
    rw [e]
    exact h
  set P := hf.toOpenPartialHomeomorph _ with hPdef
  have hPc : ∀ Y, P Y = Y * Y := fun Y => by
    rw [hPdef, hf.toOpenPartialHomeomorph_coe]
  have h1s : (1 : Matrix (Fin r) (Fin r) F) ∈ P.source := hf.mem_toOpenPartialHomeomorph_source
  have h1t : (1 : Matrix (Fin r) (Fin r) F) ∈ P.target := by
    have := hf.image_mem_toOpenPartialHomeomorph_target
    simpa using this
  have hS1 : P.symm 1 = 1 := by
    have := P.left_inv h1s
    rwa [hPc, one_mul] at this
  have hu : IsUnit H₀.det := isUnit_iff_ne_zero.mpr hdet
  set A := H₀⁻¹ with hA
  have hAH : A * H₀ = 1 := Matrix.nonsing_inv_mul H₀ hu
  have hHA : H₀ * A = 1 := Matrix.mul_nonsing_inv H₀ hu
  have hAT : Aᵀ = A := by
    rw [hA, Matrix.transpose_nonsing_inv, hsym.eq]
  let φ : Matrix (Fin r) (Fin r) F → Matrix (Fin r) (Fin r) F := fun Y => A * Yᵀ * H₀
  have hφc : Continuous φ := by
    exact (continuous_const.matrix_mul (continuous_id.matrix_transpose)).matrix_mul continuous_const
  let ψ : Matrix (Fin r) (Fin r) F → Matrix (Fin r) (Fin r) F := fun H => A * H
  have hψc : Continuous ψ := continuous_const.matrix_mul continuous_id
  have hT : IsOpen (P.target ∩ P.symm ⁻¹' (φ ⁻¹' P.source)) :=
    P.continuousOn_symm.isOpen_inter_preimage P.open_target (P.open_source.preimage hφc)
  refine ⟨ψ ⁻¹' (P.target ∩ P.symm ⁻¹' (φ ⁻¹' P.source)), fun H => P.symm (A * H), hT.preimage hψc, ?_, ?_, ?_, ?_⟩
  · show A * H₀ ∈ P.target ∩ P.symm ⁻¹' (φ ⁻¹' P.source)
    rw [hAH]
    refine ⟨h1t, ?_⟩
    show φ (P.symm 1) ∈ P.source
    simp only [φ, hS1, Matrix.transpose_one, Matrix.mul_one, hAH]
    exact h1s
  · exact P.continuousOn_symm.comp hψc.continuousOn (fun H hH => hH.1)
  · show P.symm (A * H₀) = 1
    rw [hAH, hS1]
  · intro H hH hHs
    obtain ⟨hX, hφS⟩ := hH
    set S := P.symm (A * H) with hSdef
    have hSs : S ∈ P.source := P.map_target hX
    have hSS : S * S = A * H := by rw [← hPc]; exact P.right_inv hX
    have hφφ : φ S * φ S = S * S := by
      show A * Sᵀ * H₀ * (A * Sᵀ * H₀) = S * S
      have e1 : A * Sᵀ * H₀ * (A * Sᵀ * H₀) = A * (S * S)ᵀ * H₀ := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc H₀ A, hHA, Matrix.one_mul]
      rw [e1, hSS, Matrix.transpose_mul, hAT, hHs.eq, Matrix.mul_assoc, Matrix.mul_assoc, hAH, Matrix.mul_one]
    have heq : φ S = S := P.injOn hφS hSs (by rw [hPc, hPc]; exact hφφ)
    have hcomm : Sᵀ * H₀ = H₀ * S := by
      have : H₀ * (A * Sᵀ * H₀) = H₀ * S := by rw [show A * Sᵀ * H₀ = φ S from rfl, heq]
      rwa [Matrix.mul_assoc, ← Matrix.mul_assoc H₀ A, hHA, Matrix.one_mul] at this
    rw [hcomm, Matrix.mul_assoc, hSS, ← Matrix.mul_assoc, hHA, Matrix.one_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExponentStrictlyLeastWeightStatement
section
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_least_weight_exponent : ∀ (ρ : ℕ) (S : Set (Fin ρ → ℕ)), S.Nonempty → ∃ m ∈ S, ∀ c : Fin ρ → ℕ, (∀ i, ∑ i' ∈ Finset.Iio i, m i' * c i' < c i) → ∀ a ∈ S, a ≠ m → ∑ i, m i * c i < ∑ i, a i * c i := by
  first | exact @GlobalTheory.exists_exponent_strictly_least_weight | exact GlobalTheory.exists_exponent_strictly_least_weight | (intros; apply GlobalTheory.exists_exponent_strictly_least_weight <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteGaloisContainsRootsOfUnitsStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_galois_contains_roots_of_units : ∀ (E F Ω : Type) [Field E] [NumberField E] [Field F] [Field Ω] [IsAlgClosed Ω]
    [Algebra E F] [Algebra E Ω] [Algebra F Ω] [IsScalarTower E F Ω] (M : ℕ), 0 < M →
    (∃ ζ : F, IsPrimitiveRoot ζ M) → ∃ L : IntermediateField F Ω, FiniteDimensional F L ∧ IsGalois F L ∧
      ∀ (u : (𝓞 E)ˣ) (w : Ω), w ^ M = algebraMap E Ω ((u : 𝓞 E) : E) → w ∈ L := by
  first | exact @GlobalTheory.KummerUnits.exists_finite_galois_mem_of_pow_eq_unit | exact GlobalTheory.KummerUnits.exists_finite_galois_mem_of_pow_eq_unit | (intros; apply GlobalTheory.KummerUnits.exists_finite_galois_mem_of_pow_eq_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussPoint
section
open NumberField IsDedekindDomain Formalism.L2.Pj IsLocalRing

namespace GlobalTheory.GaussPoint

theorem C_dvd_iff {V : Type*} [CommRing V] (a : V) (f : PowerSeries V) :
    PowerSeries.C a ∣ f ↔ ∀ n, a ∣ PowerSeries.coeff n f := by
  constructor
  · rintro ⟨g, rfl⟩ n
    rw [PowerSeries.coeff_C_mul]
    exact dvd_mul_right _ _
  · intro h
    choose c hc using h
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc]

theorem isPrime_span_C {V : Type*} [CommRing V] {a : V} (ha : Prime a) :
    (Ideal.span {(PowerSeries.C a : PowerSeries V)}).IsPrime := by
  have h1 : (Ideal.span {a}).IsPrime := (Ideal.span_singleton_prime ha.ne_zero).2 ha
  have h2 : Ideal.span {(PowerSeries.C a : PowerSeries V)} =
      RingHom.ker (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {a}))) := by
    ext f
    rw [Ideal.mem_span_singleton, C_dvd_iff, RingHom.mem_ker, PowerSeries.ext_iff]
    refine forall_congr' fun n => ?_
    rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [h2]
  exact RingHom.ker_isPrime _

section Val

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
  [Algebra V K] [IsFractionRing V K]

theorem valV_irreducible {π : V} (hπ : Irreducible π) :
    valV V (algebraMap V K π) = WithZero.exp (-1 : ℤ) := by
  rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _ hπ.ne_zero hπ.maximalIdeal_eq

theorem valV_unit {u : V} (hu : IsUnit u) : valV V (algebraMap V K u) = 1 := by
  rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  exact fun h => h hu

theorem vV_map_eq {V' K' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V']
    [Field K'] [Algebra V' K'] [IsFractionRing V' K'] (f : V →+* V') (i : K →+* K')
    (hi : ∀ a, i (algebraMap V K a) = algebraMap V' K' (f a)) {π : V} (hπ : Irreducible π)
    (hπ' : Irreducible (f π)) (x : K) : vV V' (i x) = vV V x := by
  have key : ∀ a : V, valV V' (i (algebraMap V K a)) = valV V (algebraMap V K a) := by
    intro a
    by_cases ha : a = 0
    · simp [ha]
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    rw [hi]
    simp only [map_mul, map_pow]
    rw [valV_unit u.isUnit, valV_unit (u.isUnit.map f), valV_irreducible hπ, valV_irreducible hπ']
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := V) x
  simp only [vV, map_div₀, key]

end Val

theorem exists_gaussPoint (T : CDVR) (ϖ : T.V) (hϖ : Irreducible ϖ) :
    ∃ (T' : CDVR) (ev : PowerSeries T.V →+* T'.V) (i : T.Fr →+* T'.Fr), Function.Injective ev ∧
      IsUnit (ev PowerSeries.X) ∧ (∀ s, ev (PowerSeries.C ϖ) ∣ ev s → PowerSeries.C ϖ ∣ s) ∧
      (∀ a, i (algebraMap T.V T.Fr a) = algebraMap T'.V T'.Fr (ev (PowerSeries.C a))) ∧
      ∀ x, vV T'.V (i x) = vV T.V x := by
  let R := PowerSeries T.V
  let P : Ideal R := Ideal.span {(PowerSeries.C ϖ : PowerSeries T.V)}
  haveI hP : P.IsPrime := isPrime_span_C hϖ.prime
  let L := Localization.AtPrime P
  have hinj : Function.Injective (algebraMap R L) :=
    IsLocalization.injective L P.primeCompl_le_nonZeroDivisors
  have hm : maximalIdeal L = Ideal.span {algebraMap R L (PowerSeries.C ϖ)} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
  have hC0 : (PowerSeries.C ϖ : R) ≠ 0 := fun h =>
    hϖ.ne_zero (PowerSeries.C_injective (h.trans (map_zero _).symm))
  have hn : ¬ IsNilpotent (algebraMap R L (PowerSeries.C ϖ)) := by
    rw [IsNilpotent.map_iff hinj]
    exact fun h => hC0 h.eq_zero
  obtain ⟨_, hdvr, hirr⟩ := isDiscreteValuationRing_of_maximalIdeal_eq_span hm hn
  let S := AdicCompletion (maximalIdeal L) L
  let ev : R →+* S := (algebraMap L S).comp (algebraMap R L)
  have hev : Function.Injective ev :=
    (algebraMap_adicCompletion_injective_of_dvr L).comp hinj
  have hirr' : Irreducible (ev (PowerSeries.C ϖ)) :=
    irreducible_algebraMap_adicCompletion_of_dvr hirr
  have hunit : ∀ s : R, ¬ PowerSeries.C ϖ ∣ s → IsUnit (ev s) := fun s hs =>
    (IsLocalization.map_units L (⟨s, fun h => hs (Ideal.mem_span_singleton.1 h)⟩ :
      P.primeCompl)).map (algebraMap L S)
  haveI : CharZero S := charZero_of_injective_ringHom
    (f := ev.comp PowerSeries.C) (hev.comp PowerSeries.C_injective)
  let T' : CDVR := { V := S }
  let g : T.V →+* T'.Fr := (algebraMap T'.V T'.Fr).comp (ev.comp PowerSeries.C)
  have hg : Function.Injective g :=
    (IsFractionRing.injective T'.V T'.Fr).comp (hev.comp PowerSeries.C_injective)
  have hi : ∀ a, IsFractionRing.lift (K := T.Fr) hg (algebraMap T.V T.Fr a) =
      algebraMap T'.V T'.Fr (ev (PowerSeries.C a)) := fun a => IsFractionRing.lift_algebraMap hg a
  refine ⟨T', ev, IsFractionRing.lift hg, hev, hunit _ ?_, fun s hs => ?_, hi,
    vV_map_eq (ev.comp PowerSeries.C) _ hi hϖ hirr'⟩
  · rw [C_dvd_iff]
    intro h
    have h1 := h 1
    rw [PowerSeries.coeff_one_X] at h1
    exact hϖ.not_isUnit (isUnit_of_dvd_one h1)
  · by_contra h
    exact hirr'.not_isUnit (isUnit_of_dvd_unit hs (hunit s h))

end GlobalTheory.GaussPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeneratorsOfCardHomResidueFieldLeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generators_of_card_hom_residueField_le : ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Finite (IsLocalRing.ResidueField Λ)] (A : Type) [AddCommGroup A] [Module Λ A] [Module.Finite Λ A] (a : ℕ),
  Nat.card (A →ₗ[Λ] IsLocalRing.ResidueField Λ) ≤ Nat.card (IsLocalRing.ResidueField Λ) ^ a →
  ∃ v : Fin a → A, Submodule.span Λ (Set.range v) = ⊤ := by
  first | exact @GlobalTheory.exists_span_eq_top_of_card_hom_residueField_le | exact GlobalTheory.exists_span_eq_top_of_card_hom_residueField_le | (intros; apply GlobalTheory.exists_span_eq_top_of_card_hom_residueField_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalElementNearIdempotentAdicCompletionStatement
section
open NumberField IsDedekindDomain TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_element_near_idempotent_adicCompletion : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [Algebra E E'] [FiniteDimensional E E'] (w : HeightOneSpectrum (𝓞 E)) {ι : Type} [Fintype ι] (b : Module.Basis ι E E') (ψ : w.adicCompletion E ⊗[E] E' →ₐ[w.adicCompletion E] w.adicCompletion E) (e : w.adicCompletion E ⊗[E] E'), e * e = e → ψ e = 1 → ∀ (p q : w.adicCompletion E ⊗[E] E') (n : ℕ), ∃ ε : E', (∀ i, w.valuation E (b.repr (ε * ε - ε) i) ≤ 1) ∧ Valued.v (ψ ((1 : w.adicCompletion E) ⊗ₜ ε) - 1) ≤ WithZero.exp (-(n : ℤ)) ∧ Valued.v (Algebra.norm (w.adicCompletion E) (p + q * ((1 : w.adicCompletion E) ⊗ₜ ε - e)) - Algebra.norm (w.adicCompletion E) p) ≤ WithZero.exp (-(n : ℤ)) := by
  first | exact @GlobalTheory.exists_global_near_idempotent | exact GlobalTheory.exists_global_near_idempotent | (intros; apply GlobalTheory.exists_global_near_idempotent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIndepSpan
section
noncomputable section
namespace GlobalTheory.IndependentSpanDual
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam

variable {k : Type} [Field k]

theorem exists_indep_span {Q : Type} [AddCommGroup Q] [Module k⸨X⸩ Q] [Module k⟦X⟧ Q]
    [IsScalarTower k⟦X⟧ k⸨X⸩ Q] {P : Submodule k⟦X⟧ Q} (hP : P.FG) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → Q), LinearIndependent k⸨X⸩ e ∧
      Submodule.span k⟦X⟧ (Set.range e) = P := by
  classical
  haveI : Module.Finite k⟦X⟧ P := Module.Finite.iff_fg.mpr hP
  haveI : NoZeroSMulDivisors k⟦X⟧ Q := by
    refine ⟨fun {c x} h => ?_⟩
    by_contra hne
    push_neg at hne
    have hc : algebraMap k⟦X⟧ k⸨X⸩ c ≠ 0 := by
      intro h0
      exact hne.1 ((IsFractionRing.injective k⟦X⟧ k⸨X⸩) (by rw [h0, map_zero]))
    have h' : algebraMap k⟦X⟧ k⸨X⸩ c • x = 0 := by
      rw [algebraMap_smul]
      exact h
    exact hne.2 ((smul_eq_zero.mp h').resolve_left hc)
  haveI : Module.Free k⟦X⟧ P := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis k⟦X⟧ P
  refine ⟨Module.Free.ChooseBasisIndex k⟦X⟧ P, inferInstance, fun i => (b i : Q), ?_, ?_⟩
  · have hli : LinearIndependent k⟦X⟧ (P.subtype ∘ b) :=
      b.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
    exact (LinearIndependent.iff_fractionRing k⟦X⟧ k⸨X⸩).mp hli
  · have hr : Set.range (fun i => (b i : Q)) = P.subtype '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [hr, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem exists_form {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k V] {l n : ℕ} {R : RingPG k l}
    (D : ModPG R n V) (i : ZMod n) (t : V →ₗ[k⸨X⸩] k⸨X⸩) :
    ∃ u : V →ₗ[k⸨X⸩] k⸨X⸩, ∀ x, u (D.φ i x) = R.φ (t x) := by
  let b := Module.Basis.ofVectorSpace k⸨X⸩ V
  let c := Module.Basis.mk (D.linearIndependent_φ i b) (D.span_φ i b).ge
  refine ⟨c.constr k⸨X⸩ fun j => R.φ (t (b j)), fun x => ?_⟩
  have hx : x ∈ Submodule.span k⸨X⸩ (Set.range b) := by rw [b.span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    have hc : D.φ i (b j) = c j :=
      (Module.Basis.mk_apply (D.linearIndependent_φ i b) (D.span_φ i b).ge j).symm
    rw [hc, Module.Basis.constr_basis]
  | zero => simp
  | add y z _ _ hy hz => simp only [map_add, hy, hz]
  | smul a y _ hy => rw [D.φ_semi i a y, map_smul, map_smul, hy, smul_eq_mul, smul_eq_mul, map_mul]

theorem exists_dual {K Q ι : Type} [Field K] [AddCommGroup Q] [Module K Q] [DecidableEq ι] {e : ι → Q}
    (he : LinearIndependent K e) (j : ι) :
    ∃ t : Q →ₗ[K] K, ∀ m, t (e m) = if m = j then 1 else 0 := by
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span he).coord j)
  refine ⟨g, fun m => ?_⟩
  have hm : e m = (Submodule.span K (Set.range e)).subtype (Module.Basis.span he m) := by
    rw [Module.Basis.span_apply]
    rfl
  rw [hm, ← LinearMap.comp_apply, hg, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply]

theorem comap_pull {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V]
    [IsScalarTower k⟦X⟧ k⸨X⸩ V] {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W]
    [IsScalarTower k⟦X⟧ k⸨X⸩ W] [Module k V] [Module k W] {l n : ℕ} {R : RingPG k l}
    (D : ModPG R n V) (D' : ModPG R n W) (i : ZMod n) (f g : W →ₗ[k⸨X⸩] V)
    (_hf : Function.Injective f) (hg : Function.Injective g)
    (h : ∀ x, g (D'.φ i x) = D.φ i (f x)) {N : Submodule k⟦X⟧ V} (hN : N.FG) :
    (pull (D.φ i) N).comap (g.restrictScalars k⟦X⟧) = pull (D'.φ i) (N.comap (f.restrictScalars k⟦X⟧)) := by
  classical
  apply le_antisymm
  swap
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    change g (D'.φ i x) ∈ pull (D.φ i) N
    rw [h]
    exact Submodule.subset_span ⟨_, hx, rfl⟩
  let π := (LinearMap.range f).mkQ
  obtain ⟨ι, _, e, he, hsp⟩ := exists_indep_span (hN.map (π.restrictScalars k⟦X⟧))
  have hlift : ∀ j, ∃ s ∈ N, π s = e j := fun j => by
    have : e j ∈ N.map (π.restrictScalars k⟦X⟧) := hsp ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this
  choose s hsN hs using hlift

  have hle : pull (D.φ i) N ≤ (pull (D'.φ i) (N.comap (f.restrictScalars k⟦X⟧))).map (g.restrictScalars k⟦X⟧) ⊔
      Submodule.span k⟦X⟧ (Set.range fun j => D.φ i (s j)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    have hx' : π x ∈ Submodule.span k⟦X⟧ (Set.range e) := hsp ▸ ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun k⟦X⟧).1 hx'
    have h0 : x - ∑ j, a j • s j ∈ LinearMap.range f := by
      rw [← Submodule.ker_mkQ (LinearMap.range f), LinearMap.mem_ker]
      change (π.restrictScalars k⟦X⟧) _ = 0
      rw [map_sub, map_sum, sub_eq_zero]
      simp only [map_smul, LinearMap.restrictScalars_apply, hs, ha]
    obtain ⟨w, hw⟩ := h0
    have hwN : f w ∈ N := hw ▸ N.sub_mem hx (N.sum_mem fun j _ => N.smul_mem _ (hsN j))
    have hx2 : x = f w + ∑ j, a j • s j := by rw [hw, sub_add_cancel]
    rw [hx2, map_add, map_sum, ← h]
    refine Submodule.add_mem_sup ⟨_, Submodule.subset_span ⟨w, hwN, rfl⟩, rfl⟩
      (Submodule.sum_mem _ fun j _ => ?_)
    obtain ⟨b, hb⟩ := R.φ_int (a j)
    have : D.φ i (a j • s j) = b • D.φ i (s j) := by
      rw [← algebraMap_smul k⸨X⸩ (a j), D.φ_semi i, ← algebraMap_smul k⸨X⸩ b]
      exact congrArg (· • D.φ i (s j)) hb
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  intro y hy
  obtain ⟨_, ⟨p, hp, rfl⟩, q, hq, hpq⟩ := Submodule.mem_sup.1 (hle hy)
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k⟦X⟧).1 hq
  have hq' : ∑ j, a j • D.φ i (s j) = g (y - p) := by
    rw [map_sub, eq_sub_iff_add_eq']
    exact hpq
  have ha : ∀ j, algebraMap k⟦X⟧ k⸨X⸩ (a j) = 0 := fun j => by
    obtain ⟨t, ht⟩ := exists_dual he j
    obtain ⟨u, hu⟩ := exists_form D i (t.comp π)
    have hug : u.comp g = 0 := by
      refine LinearMap.ext_on_range (D'.etale i) fun x => ?_
      have : π (f x) = 0 := (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
      rw [LinearMap.comp_apply, h, hu, LinearMap.comp_apply, this, map_zero, map_zero, LinearMap.zero_apply]
    have h1 : u (∑ m, a m • D.φ i (s m)) = 0 := by
      rw [hq']; exact LinearMap.congr_fun hug _
    have h2 : ∀ m, u (a m • D.φ i (s m)) = if m = j then algebraMap k⟦X⟧ k⸨X⸩ (a m) else 0 := fun m => by
      rw [← algebraMap_smul k⸨X⸩ (a m), map_smul, hu, LinearMap.comp_apply, hs, ht]
      split_ifs <;> simp
    rw [map_sum] at h1
    simpa [h2] using h1
  have hz : g (y - p) = 0 := by
    rw [← hq']
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← algebraMap_smul k⸨X⸩ (a j), ha, zero_smul]
  have : y = p := sub_eq_zero.1 (hg (hz.trans (map_zero g).symm))
  rw [this]
  exact hp

end GlobalTheory.IndependentSpanDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIndependentModPrimeOfPowLeCardStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_independent_mod_prime_of_pow_le_card : ∀ (l : ℕ) [Fact l.Prime] (V ι : Type) [AddCommGroup V] (K' : AddSubgroup V) (h : ℕ) (Z : Finset ι) (v : ι → V), (∀ x : V, l • x = 0) → l ^ h ≤ Z.card → (∀ i ∈ Z, ∀ i' ∈ Z, i ≠ i' → v i - v i' ∉ K') → ∃ x : Fin h → ι, (∀ a, x a ∈ Z) ∧ ∀ n : Fin h → ℕ, ∑ a, n a • v (x a) ∈ K' → ∀ a, l ∣ n a := by
  first | exact @GlobalTheory.ph_a_basis | exact GlobalTheory.ph_a_basis | (intros; apply GlobalTheory.ph_a_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralPowerSeriesDivisionApprox
section
namespace GlobalTheory.BK.DivApprox

open PowerSeries GlobalTheory.BK

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_coeff_mul_le' {f g : K⟦X⟧} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : ∀ n, ‖coeff n f‖ ≤ a) (hg : ∀ n, ‖coeff n g‖ ≤ b) (n : ℕ) :
    ‖coeff n (f * g)‖ ≤ a * b := by
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
    ha hb (f := f) (g := g) (by simpa using hf) (by simpa using hg) n

omit [IsUltrametricDist K] in
theorem eq_low_add_high (f : K⟦X⟧) (n₀ : ℕ) :
    f = (PowerSeries.mk fun n => if n < n₀ then coeff n f else 0) +
      X ^ n₀ * PowerSeries.mk fun n => coeff (n + n₀) f := by
  ext n
  rw [map_add, coeff_mk, coeff_X_pow_mul', coeff_mk]
  by_cases h : n < n₀
  · rw [if_pos h, if_neg (not_le.2 h), add_zero]
  · rw [if_neg h, if_pos (not_lt.1 h), zero_add, Nat.sub_add_cancel (not_lt.1 h)]

theorem exists_inv_mem_A {O : Type} [CommRing O] [Algebra O K] [IsUnitBall O K] {u : K⟦X⟧}
    (hu : u ∈ A O K) (h0 : ‖coeff 0 u‖ = 1) : ∃ w ∈ A O K, u * w = 1 := by
  obtain ⟨v, hv⟩ := (equivA O K).surjective ⟨u, hu⟩
  have hv' : PowerSeries.map (algebraMap O K) v = u := by
    rw [← coe_equivA, hv]
  have hc : algebraMap O K (constantCoeff v) = coeff 0 u := by
    rw [← hv', coeff_map, coeff_zero_eq_constantCoeff_apply]
  have hne : coeff 0 u ≠ 0 := by
    intro h
    rw [h, norm_zero] at h0
    exact zero_ne_one h0
  obtain ⟨c, hc'⟩ := (IsUnitBall.mem_range_iff (O := O) (coeff 0 u)⁻¹).2
    (by rw [norm_inv, h0, inv_one])
  have hunit : IsUnit (constantCoeff v) := by
    refine IsUnit.of_mul_eq_one c (IsUnitBall.inj (O := O) (K := K) ?_)
    rw [map_mul, hc, hc', map_one, mul_inv_cancel₀ hne]
  obtain ⟨w, hw⟩ := (isUnit_iff_constantCoeff.2 hunit).exists_right_inv
  refine ⟨equivA O K w, (equivA O K w).2, ?_⟩
  rw [coe_equivA, ← hv', ← map_mul, hw, map_one]

theorem step {g p u w : K⟦X⟧} {n₀ : ℕ} {ρ t : ℝ} (hρ : 0 ≤ ρ) (ht : 0 ≤ t)
    (hg : g = p + X ^ n₀ * u) (huw : u * w = 1) (hw : ∀ n, ‖coeff n w‖ ≤ 1)
    (hp : ∀ n, ‖coeff n p‖ ≤ ρ) (f : K⟦X⟧) (hf : ∀ n, ‖coeff n f‖ ≤ t) :
    ∃ q r : K⟦X⟧, (∀ n, ‖coeff n q‖ ≤ t) ∧ (∀ i, n₀ ≤ i → coeff i r = 0) ∧
      (∀ i, ‖coeff i r‖ ≤ t) ∧ ∀ n, ‖coeff n (f - q * g - r)‖ ≤ t * ρ := by
  have hfe := eq_low_add_high f n₀
  set r : K⟦X⟧ := PowerSeries.mk fun n => if n < n₀ then coeff n f else 0 with hr
  set fh : K⟦X⟧ := PowerSeries.mk fun n => coeff (n + n₀) f with hfh
  have hq : ∀ n, ‖coeff n (w * fh)‖ ≤ t := fun n => by
    have := norm_coeff_mul_le' zero_le_one ht hw (g := fh)
      (fun m => by rw [hfh, coeff_mk]; exact hf _) n
    rwa [one_mul] at this
  refine ⟨w * fh, r, hq, fun i hi => ?_, fun i => ?_, fun n => ?_⟩
  · rw [hr, coeff_mk, if_neg (not_lt.2 hi)]
  · rw [hr, coeff_mk]
    split_ifs
    · exact hf _
    · rwa [norm_zero]
  · have : f - w * fh * g - r = -(w * fh * p) := by
      rw [hg]
      linear_combination hfe - X ^ n₀ * fh * huw
    rw [this, map_neg, norm_neg]
    exact norm_coeff_mul_le' ht hρ hq hp n

theorem iterate {g p u w : K⟦X⟧} {n₀ : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hg : g = p + X ^ n₀ * u) (huw : u * w = 1) (hw : ∀ n, ‖coeff n w‖ ≤ 1)
    (hp : ∀ n, ‖coeff n p‖ ≤ ρ) (f : K⟦X⟧) (hf : ∀ n, ‖coeff n f‖ ≤ 1) (k : ℕ) :
    ∃ q r : K⟦X⟧, (∀ n, ‖coeff n q‖ ≤ 1) ∧ (∀ i, n₀ ≤ i → coeff i r = 0) ∧
      (∀ i, ‖coeff i r‖ ≤ 1) ∧ ∀ n, ‖coeff n (f - q * g - r)‖ ≤ ρ ^ k := by
  induction k with
  | zero => exact ⟨0, 0, by simp, by simp, by simp, by simpa using hf⟩
  | succ k ih =>
    obtain ⟨q, r, hq, hr0, hr, he⟩ := ih
    obtain ⟨q', r', hq', hr0', hr', he'⟩ := step hρ (pow_nonneg hρ k) hg huw hw hp _ he
    have h1 : ρ ^ k ≤ 1 := pow_le_one₀ hρ hρ1
    refine ⟨q + q', r + r', fun n => ?_, fun i hi => ?_, fun n => ?_, fun n => ?_⟩
    · rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hq n) ((hq' n).trans h1))
    · rw [map_add, hr0 i hi, hr0' i hi, add_zero]
    · rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hr n) ((hr' n).trans h1))
    · have : f - (q + q') * g - (r + r') = f - q * g - r - q' * g - r' := by ring
      rw [this, pow_succ]
      exact he' n

theorem exists_div_approx (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (g : K⟦X⟧) (hg : g ∈ A O K) (n₀ : ℕ)
    (h1 : ‖coeff n₀ g‖ = 1) (hlt : ∀ i < n₀, ‖coeff i g‖ < 1) (δ : ℝ) (hδ : 0 < δ)
    (f : K⟦X⟧) (hf : f ∈ A O K) :
    ∃ q ∈ A O K, ∃ r : K⟦X⟧, (∀ i, n₀ ≤ i → coeff i r = 0) ∧ (∀ i, ‖coeff i r‖ ≤ 1) ∧
      ∀ n, ‖coeff n (f - q * g - r)‖ ≤ δ := by
  set ρ : NNReal := (Finset.range n₀).sup (fun i => ‖coeff i g‖₊) with hρ
  have hρ1 : ρ < 1 := by
    rw [hρ, Finset.sup_lt_iff (by simp)]
    intro i hi
    exact_mod_cast hlt i (Finset.mem_range.1 hi)
  have hρ1' : (ρ : ℝ) < 1 := by exact_mod_cast hρ1
  obtain ⟨w, hw, huw⟩ := exists_inv_mem_A (O := O)
    (u := PowerSeries.mk fun n => coeff (n + n₀) g)
    (fun n => by rw [coeff_mk]; exact hg _) (by rw [coeff_mk, zero_add, h1])
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ hρ1'
  obtain ⟨q, r, hq, hr0, hr, he⟩ := iterate ρ.2 hρ1'.le (eq_low_add_high g n₀) huw hw
    (fun n => by
      rw [coeff_mk]
      split_ifs with h
      · exact_mod_cast Finset.le_sup (f := fun i => ‖coeff i g‖₊) (Finset.mem_range.2 h)
      · rw [norm_zero]; exact ρ.2) f hf k
  exact ⟨q, hq, r, hr0, hr, fun n => (he n).trans hk.le⟩

end GlobalTheory.BK.DivApprox
end

