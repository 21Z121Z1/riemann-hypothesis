import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateLinearTensorModuleDecomposition
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0063
import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositumIntermediateFieldExistsPlaceValuationE
section
open NumberField IsDedekindDomain

namespace GlobalTheory.UnramCompositum

theorem card_inertia (k N : Type) [Field k] [NumberField k] [Field N] [NumberField N]
    [Algebra k N] [IsGalois k N] (Q : Ideal (𝓞 N)) [Q.IsPrime] :
    Nat.card (Q.inertia (N ≃ₐ[k] N)) = Q.ramificationIdx (𝓞 k) := by
  have : IsGaloisGroup (N ≃ₐ[k] N) (𝓞 k) (𝓞 N) := IsGaloisGroup.of_isFractionRing _ _ _ k N
  have hpr : (Q.under (𝓞 k)).IsPrime := Ideal.IsPrime.under _ Q
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := N ≃ₐ[k] N) (Q.under (𝓞 k)) Q
  rwa [Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 k)) Q (N ≃ₐ[k] N)] at hcard

theorem ramificationIdx_eq_one_iff_fix (k E N : Type) [Field k] [NumberField k] [Field E] [NumberField E]
    [Field N] [NumberField N] [Algebra k E] [Algebra k N] [Algebra E N] [IsScalarTower k E N] [IsGalois k N]
    (Q : Ideal (𝓞 N)) [Q.IsPrime] :
    (Q.under (𝓞 E)).ramificationIdx (𝓞 k) = 1 ↔
      ∀ τ : N ≃ₐ[k] N, (∀ x : 𝓞 N, τ • x - x ∈ Q) → ∀ y : E, τ (algebraMap E N y) = algebraMap E N y := by
  haveI : IsGalois E N := IsGalois.tower_top_of_isGalois k E N
  have h1 := card_inertia k N Q
  have h2 := card_inertia E N Q
  have h3 : Q.ramificationIdx (𝓞 k) = (Q.under (𝓞 E)).ramificationIdx (𝓞 k) * Q.ramificationIdx (𝓞 E) :=
    Ideal.ramificationIdx_tower (Q.under (𝓞 E)) Q
  have h4 : 0 < Q.ramificationIdx (𝓞 E) := Ideal.ramificationIdx_pos Q (𝓞 E)
  let f : Q.inertia (N ≃ₐ[E] N) → Q.inertia (N ≃ₐ[k] N) := fun σ =>
    ⟨σ.1.restrictScalars k, AddSubgroup.mem_inertia.mpr fun x => AddSubgroup.mem_inertia.mp σ.2 x⟩
  have hf : Function.Injective f := fun σ σ' h =>
    Subtype.ext (AlgEquiv.restrictScalars_injective k (congrArg Subtype.val h))
  constructor
  · intro h τ hτ y
    have hb : Function.Bijective f := hf.bijective_of_nat_card_le (by rw [h1, h2, h3, h, one_mul])
    obtain ⟨σ, hσ⟩ := hb.2 ⟨τ, AddSubgroup.mem_inertia.mpr hτ⟩
    have : σ.1.restrictScalars k = τ := congrArg Subtype.val hσ
    rw [← this]
    exact σ.1.commutes y
  · intro h
    have hs : Function.Surjective f := fun τ =>
      ⟨⟨{ τ.1.toRingEquiv with commutes' := h τ.1 (AddSubgroup.mem_inertia.mp τ.2) },
        AddSubgroup.mem_inertia.mpr fun x => AddSubgroup.mem_inertia.mp τ.2 x⟩, rfl⟩
    have hc := Nat.card_eq_of_bijective f ⟨hf, hs⟩
    rw [h1, h2, h3] at hc
    exact Nat.eq_of_mul_eq_mul_right h4 (by rw [one_mul]; exact hc.symm)

theorem exists_galois_above (K : Type) [Field K] [NumberField K] :
    ∃ (N : Type) (_ : Field N) (_ : NumberField N) (_ : Algebra K N), IsGalois ℚ N := by
  have : IsAlgClosure ℚ (AlgebraicClosure K) := IsAlgClosure.ofAlgebraic ℚ K (AlgebraicClosure K)
  have : IsGalois ℚ (AlgebraicClosure K) := ⟨⟩
  have : NumberField (IntermediateField.normalClosure ℚ K (AlgebraicClosure K)) := ⟨⟩
  exact ⟨IntermediateField.normalClosure ℚ K (AlgebraicClosure K), inferInstance, inferInstance, inferInstance,
    IsGalois.normalClosure ℚ K (AlgebraicClosure K)⟩

theorem exists_valuation_eq (F F' K : Type) [Field F] [NumberField F] [Field F'] [NumberField F'] [Field K]
    [NumberField K] [Algebra F K] [Algebra F' K]
    (hgen : ∀ (N : Type) [Field N] (f g : K →+* N), (∀ x : F, f (algebraMap F K x) = g (algebraMap F K x)) →
      (∀ x : F', f (algebraMap F' K x) = g (algebraMap F' K x)) → f = g)
    (q : ℕ) (hq : q.Prime) (hd : ¬ (q : ℤ) ∣ discr F') (w : HeightOneSpectrum (𝓞 F))
    (hw : ((q : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ∀ a : F, 𝔭.valuation K (algebraMap F K a) = w.valuation F a := by
  obtain ⟨N, _, _, _, hN⟩ := exists_galois_above K
  letI : Algebra F N := ((algebraMap K N).comp (algebraMap F K)).toAlgebra
  letI : Algebra F' N := ((algebraMap K N).comp (algebraMap F' K)).toAlgebra
  have : IsScalarTower F K N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsGalois F N := IsGalois.tower_top_of_isGalois ℚ F N
  have := w.isMaximal
  obtain ⟨Q, hQ, hQw⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 N) w.asIdeal
  have hqQ : ((q : ℕ) : 𝓞 N) ∈ Q := by
    have := (Ideal.mem_of_liesOver Q w.asIdeal _).1 hw
    rwa [map_natCast] at this
  have hu : Algebra.IsUnramifiedAt ℤ (Q.under (𝓞 F')) :=
    (not_dvd_discr_iff_forall_mem F' (𝓞 F') (Nat.prime_iff_prime_int.1 hq)).1 hd _ inferInstance (by
      rw [Ideal.under, Ideal.mem_comap, map_intCast, Int.cast_natCast]; exact hqQ)
  have hu' : Algebra.IsUnramifiedAt (𝓞 ℚ) (Q.under (𝓞 F')) := Algebra.IsUnramifiedAt.of_restrictScalars ℤ _
  have hfix := (ramificationIdx_eq_one_iff_fix ℚ F' N Q).1 (Ideal.ramificationIdx_eq_one _ _)
  have he : (Q.under (𝓞 K)).ramificationIdx (𝓞 F) = 1 := by
    refine (ramificationIdx_eq_one_iff_fix F K N Q).2 fun τ hτ y => ?_
    exact RingHom.congr_fun (hgen N ((τ : N →+* N).comp (algebraMap K N)) (algebraMap K N)
      (fun x => τ.commutes x) (fun x => hfix (τ.restrictScalars ℚ) hτ x)) y
  have hlo : (Q.under (𝓞 K)).LiesOver w.asIdeal := Ideal.LiesOver.tower_bot Q _ _
  let 𝔭 : HeightOneSpectrum (𝓞 K) :=
    ⟨Q.under (𝓞 K), inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot w.ne_bot _⟩
  have hlo' : 𝔭.asIdeal.LiesOver w.asIdeal := hlo
  refine ⟨𝔭, fun a => ?_⟩
  rw [← HeightOneSpectrum.valuation_liesOver K w 𝔭 a,
    Ideal.ramificationIdx'_eq_ramificationIdx w.asIdeal 𝔭.asIdeal w.ne_bot]
  change _ ^ (Q.under (𝓞 K)).ramificationIdx (𝓞 F) = _
  rw [he, pow_one]

open Formalism.L2.Pj in

theorem exists_vLa_eq : ∀ (F F' K : IntermediateField ℚ ℂ) [NumberField F] [NumberField F'] [NumberField K]
    (hF : F ≤ K), K = F ⊔ F' → ∀ q : ℕ, q.Prime → ¬ (q : ℤ) ∣ discr F' → ∀ w : HeightOneSpectrum (𝓞 F),
    ((q : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ 𝔭 : HeightOneSpectrum (𝓞 K),
      ∀ a : F, vLa 𝔭 (IntermediateField.inclusion hF a) = vLa w a := by
  intro F F' K _ _ _ hF hK q hq hd w hw
  have hF' : F' ≤ K := hK ▸ le_sup_right
  letI : Algebra F K := (IntermediateField.inclusion hF).toRingHom.toAlgebra
  letI : Algebra F' K := (IntermediateField.inclusion hF').toRingHom.toAlgebra
  obtain ⟨𝔭, h⟩ := exists_valuation_eq F F' K (fun N _ f g h1 h2 => by
    let T : Subfield ℂ := (RingHom.eqLocusField f g).map (K.val : K →+* ℂ)
    let S : IntermediateField ℚ ℂ := T.toIntermediateField fun x => by
      rw [eq_ratCast]; exact SubfieldClass.ratCast_mem T x
    have hle : K ≤ S := by
      refine hK.le.trans (sup_le (fun x hx => ⟨⟨x, hF hx⟩, h1 ⟨x, hx⟩, rfl⟩)
        (fun x hx => ⟨⟨x, hF' hx⟩, h2 ⟨x, hx⟩, rfl⟩))
    ext z
    obtain ⟨y, hy, hyz⟩ := hle z.2
    have hyz' : y = z := Subtype.ext hyz
    subst hyz'
    exact hy) q hq hd w hw
  exact ⟨𝔭, fun a => congrArg (fun t => -WithZero.log t) (h a)⟩

end GlobalTheory.UnramCompositum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjDualPartsKilledOfPerfectPairingStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_dual_parts_killed_of_perfect_pairing : ∀ (O : Type) [CommRing O] (bar : O →+* O) (U : Type) [CommRing U] [IsDomain U] (M M' : Type) [CommGroup M] [CommGroup M'] (α : O → M →* M) (α' : O → M' →* M'), (∀ y, α 1 y = y) → (∀ a b y, α (a * b) y = α a (α b y)) → (∀ a b y, α (a + b) y = α a y * α b y) → (∀ x, α' 1 x = x) → (∀ a b x, α' (a * b) x = α' a (α' b x)) → (∀ a b x, α' (a + b) x = α' a x * α' b x) → (∀ a, bar (bar a) = a) → ∀ (e : M' →* M →* Uˣ) (e' : M →* M' →* Uˣ), Function.Injective e → Function.Injective e' → (∀ a x y, e (α' a x) y = e x (α (bar a) y)) → (∀ a y x, e' (α a y) x = e' y (α' (bar a) x)) → ∀ (u w : Ideal O) (n : ℕ), u ≤ w → u ⊔ u.map bar = ⊤ → (∀ a ∈ (u * u.map bar) ^ n, (∀ y, α a y = 1) ∧ ∀ x, α' a x = 1) → (∀ y, (∃ m : ℕ, ∀ a ∈ u ^ m, α a y = 1) → ∀ a ∈ w, α a y = 1) → Finite {y : M // ∀ a ∈ w, α a y = 1} → (∀ x, (∃ m : ℕ, ∀ a ∈ (u.map bar) ^ m, α' a x = 1) → ∀ a ∈ w.map bar, α' a x = 1) ∧ Nat.card {x : M' // ∀ a ∈ w.map bar, α' a x = 1} = Nat.card {y : M // ∀ a ∈ w, α a y = 1} := by
  first | (exact @GlobalTheory.DualParts.conj_dual_parts) | (exact GlobalTheory.DualParts.conj_dual_parts) | (intros; apply GlobalTheory.DualParts.conj_dual_parts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTransposeMulMulSelfOfUnitaryConjStatement
section
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjTranspose_mul_self_of_witt_frame_unitary : ∀ (n d : ℕ) (J P : Matrix (Fin n) (Fin n) ℂ) (Xb Yb : Matrix (Fin n) (Fin d) ℂ) (y₀ : GL (Fin d) ℂ),
    J.conjTranspose = J → P.conjTranspose = P → Xb.conjTranspose * J * Xb = 0 → Yb.conjTranspose * J * Yb = 0 →
    Xb.conjTranspose * J * Yb = 1 →
    P * Xb = J * Yb * ((y₀⁻¹).1.conjTranspose * (y₀⁻¹).1) → P * Yb = J * Xb * (y₀.1 * (y₀.1).conjTranspose) →
    ∀ k : GL (Fin d) ℂ, (k.1).conjTranspose * k.1 = 1 →
      let m : GL (Fin d) ℂ := y₀ * k * y₀⁻¹
      let G : Matrix (Fin n) (Fin n) ℂ := 1 + Xb * (m.1 - 1) * (Yb.conjTranspose * J) + Yb * ((m⁻¹).1.conjTranspose - 1) * (Xb.conjTranspose * J)
      G.conjTranspose * P * G = P := by
  first | exact @GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj | exact GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj | (intros; apply GlobalTheory.conjTranspose_mul_mul_self_of_unitary_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateLinearTensorModuleDecompositionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_linear_tensor_module_decomposition : ∀ (A R Λ : Type) [CommRing A] [CommRing R] [CommRing Λ] [Algebra A R] (ι : Λ →+* R),
    Submodule.span A (Set.range ι) = ⊤ → ∀ (c : Λ →+* Λ) (cR : R →ₐ[A] R), (∀ a, cR (ι a) = ι (c a)) →
    (∀ a, c (c a) = a) →
    ∀ (T₁ T₂ T : Type) [AddCommGroup T₁] [Module A T₁] [AddCommGroup T₂] [Module A T₂] [AddCommGroup T] [Module A T]
      (ρ₁ : Λ →+* Module.End A T₁) (ρ₂ : Λ →+* Module.End A T₂) (ρ : Λ →+* Module.End A T)
      (e₁ : LinearMap.BilinForm A T₁) (e₂ : LinearMap.BilinForm A T₂) (e : LinearMap.BilinForm A T),
      Function.Bijective e₁ → Function.Bijective e₂ → Function.Bijective e →
      (∀ a x y, e₁ (ρ₁ a x) y = e₁ x (ρ₁ (c a) y)) → (∀ a x y, e₂ (ρ₂ a x) y = e₂ x (ρ₂ (c a) y)) →
      (∀ a x y, e (ρ a x) y = e x (ρ (c a) y)) →
    ∀ (m n : Type) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
      (φ₁ : m → (T₁ →ₗ[A] T)) (φ₂ : n → (T₂ →ₗ[A] T)) (g₁ : Matrix m m Λ) (g₂ : Matrix n n Λ),
      (∀ k a x, φ₁ k (ρ₁ a x) = ρ a (φ₁ k x)) → (∀ k a x, φ₂ k (ρ₂ a x) = ρ a (φ₂ k x)) →
      (∀ k l x y, e (φ₁ k x) (φ₁ l y) = e₁ (ρ₁ (g₁ k l) x) y) →
      (∀ k l x y, e (φ₂ k x) (φ₂ l y) = e₂ (ρ₂ (g₂ k l) x) y) →
      (∀ k l x y, e (φ₁ k x) (φ₂ l y) = 0) → (∀ k l x y, e (φ₂ k x) (φ₁ l y) = 0) →
    ∀ (f₁ : (Unit → R) ≃ₗ[A] T₁) (f₂ : (Unit → R) ≃ₗ[A] T₂) (f : (m ⊕ n → R) ≃ₗ[A] T),
      (∀ a r, f₁ (ι a • r) = ρ₁ a (f₁ r)) → (∀ a r, f₂ (ι a • r) = ρ₂ a (f₂ r)) →
      (∀ a r, f (ι a • r) = ρ a (f r)) →
    ∀ M : Matrix (m ⊕ n) (m ⊕ n) R, (∀ k, f (M (Sum.inl k)) = φ₁ k (f₁ 1)) →
      (∀ k, f (M (Sum.inr k)) = φ₂ k (f₂ 1)) →
      Associated (M.det * cR M.det) (ι (g₁.det * g₂.det)) := by
  first | exact @GlobalTheory.CMNorm.associated_det_mul_conj | exact GlobalTheory.CMNorm.associated_det_mul_conj | (intros; apply GlobalTheory.CMNorm.associated_det_mul_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugationDerivCutoffPolynomialMemUnitarySpan
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Pc1

private theorem sg_sq' {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : sg ε a * sg ε a = 1 := by
  unfold sg; split_ifs <;> simp

private theorem conj_sg' {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    (starRingEnd ℂ) (sg ε a) = sg ε a := by
  unfold sg; split_ifs <;> simp

private theorem lieU_decomposition {n : ℕ} (ε : Fin n → Bool) (Z : Mat n) :
    ∃ A B : Mat n, LieU ε A ∧ LieU ε B ∧ Z = A + Complex.I • B := by
  refine ⟨Matrix.of fun a b => (Z a b + (starRingEnd ℂ) (barM ε Z a b)) / 2,
    Matrix.of fun a b => -Complex.I * (Z a b - (starRingEnd ℂ) (barM ε Z a b)) / 2, ?_, ?_, ?_⟩
  · intro a b
    have ha := sg_sq' ε a
    have hb := sg_sq' ε b
    simp only [barM, Matrix.of_apply, map_div₀, map_add, map_neg, map_mul, conj_sg',
      Complex.conj_conj, map_ofNat]
    linear_combination (-(starRingEnd ℂ) (Z a b) / 2 * (sg ε b * sg ε b)) * ha
      + (-(starRingEnd ℂ) (Z a b) / 2) * hb
  · intro a b
    have ha := sg_sq' ε a
    have hb := sg_sq' ε b
    simp only [barM, Matrix.of_apply, map_div₀, map_sub, map_neg, map_mul, conj_sg',
      Complex.conj_conj, map_ofNat, Complex.conj_I]
    linear_combination (-Complex.I * (starRingEnd ℂ) (Z a b) / 2 * (sg ε b * sg ε b)) * ha
      + (-Complex.I * (starRingEnd ℂ) (Z a b) / 2) * hb
  · ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    linear_combination ((Z a b - (starRingEnd ℂ) (barM ε Z a b)) / 2) * Complex.I_mul_I

theorem dZ_add_smul {n : ℕ} (ε : Fin n → Bool) (A B : Mat n) (c : ℂ) :
    dZ ε (A + c • B) = dZ ε A + c • dZ ε B := by
  apply MvPolynomial.derivation_ext
  rintro (x | x)
  · simp only [dZ, Derivation.add_apply, Derivation.smul_apply, mkDerivation_X, Sum.elim_inl,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, smul_eq_C_mul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  · simp only [dZ, Derivation.add_apply, Derivation.smul_apply, mkDerivation_X, Sum.elim_inr, barM,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_neg, smul_eq_C_mul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem adBas_add_smul {n : ℕ} (ε : Fin n → Bool) (A B : Mat n) (c : ℂ) (H : ℝ → ℝ)
    (P : GlobalTheory.PsCo.Pc1.Poly n) :
    adBas ε (A + c • B) H P = adBas ε A H P + c • adBas ε B H P := by
  funext g
  have hC : ev g (C c) = c := by simp [ev]
  simp only [adBas, bas, dZ_add_smul, Derivation.add_apply, Derivation.smul_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, smul_eq_C_mul, map_add, map_mul, hC]
  ring

theorem adBas_mem_adSpanM  : ∀ {n : ℕ} (ε : Fin n → Bool) (Z : GlobalTheory.PsCo.Pc1.Mat n) (H : ℝ → ℝ)
    (P : GlobalTheory.PsCo.Pc1.Poly n), GlobalTheory.PsCo.Pc1.IsCutFn H →
    GlobalTheory.PsCo.Pc1.adBas ε Z H P ∈ GlobalTheory.PsCo.Pc1.AdSpanM ε := by
  intro n ε Z H P hH
  obtain ⟨A, B, hA, hB, rfl⟩ := lieU_decomposition ε Z
  rw [adBas_add_smul]
  exact Submodule.add_mem _ (Submodule.subset_span ⟨A, H, P, hA, hH, rfl⟩)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨B, H, P, hB, hH, rfl⟩))

end GlobalTheory.PsCo.Pc1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffTsumOfLocallySummableBoundsStatement
section
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_tsum_of_summable_iteratedFDeriv_bounds : ∀ {k : ℕ} {ι : Type} (f : ι → (Fin k → ℝ) → ℂ), (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f i)) → (∀ (n : ℕ) (R : ℝ), ∃ u : ι → ℝ, Summable u ∧ ∀ i t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (f i) t‖ ≤ u i) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ∑' i, f i t) := by
  first | exact @GlobalTheory.contDiff_tsum_of_locally_summable_bounds | exact GlobalTheory.contDiff_tsum_of_locally_summable_bounds | (intros; apply GlobalTheory.contDiff_tsum_of_locally_summable_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtCharSeriesCoefZeroStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousAt_coeff_zero_of_continuousAt_char_series : ∀ {Y Ξ P : Type} [AddCommGroup Y] [Zero Ξ] [TopologicalSpace P] (e : Ξ → AddChar Y ℂ),
    (∀ a y, ‖e a y‖ = 1) → (∀ y, e 0 y = 1) → (∀ a, a ≠ 0 → ∃ y, e a y ≠ 1) →
    ∀ (c : P → Ξ → ℂ) (p0 : P) (M : Ξ → ℝ), Summable M → (∀ᶠ p in nhds p0, ∀ a, ‖c p a‖ ≤ M a) →
    (∀ y, ContinuousAt (fun p => ∑' a, e a y * c p a) p0) → ContinuousAt (fun p => c p 0) p0 := by
  first | exact @GlobalTheory.continuousAt_charSeries_coef_zero | exact GlobalTheory.continuousAt_charSeries_coef_zero | (intros; apply GlobalTheory.continuousAt_charSeries_coef_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCharacterCocycleTrivialNearZero
section
noncomputable section

namespace GlobalTheory.CocycleChar

theorem pow_near_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.InductiveNormBound.main
  | exact _root_.GlobalTheory.InductiveNormBound.main
  | (apply _root_.GlobalTheory.InductiveNormBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.InductiveNormBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InductiveNormBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InductiveNormBound.main ..)

theorem cocycle_char_trivial_near_zero :
    ∀ {A V : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [CompactSpace A]
    [NonarchimedeanAddGroup A] [AddCommGroup V] [TopologicalSpace V] [T2Space V] (lam : A →+ V), Continuous lam →
    ∀ (ε : V → V → ℂ), (∃ N ∈ nhds (0 : V), ∀ x ∈ N, ∀ y ∈ N, ε x y = 1) → (∀ x, ε x 0 = 1) →
    ∀ (χ : A → ℂ), Continuous χ → (∀ a, lam a = 0 → χ a = 1) →
    (∀ a b, χ (a + b) = χ a * χ b * ε (lam a) (lam b)) → ∃ U ∈ nhds (0 : V), ∀ a, lam a ∈ U → χ a = 1 := by
  intro A V _ _ _ _ _ _ _ _ lam hlam ε ⟨N, hN, hεN⟩ hε0 χ hχ hker hmul
  have hχ0 : χ 0 = 1 := hker 0 (map_zero lam)

  have hW : lam ⁻¹' N ∩ {a : A | ‖χ a - 1‖ < 1 / 2} ∈ nhds (0 : A) := by
    refine Filter.inter_mem ?_ ?_
    · exact hlam.continuousAt.preimage_mem_nhds (by simpa using hN)
    · exact (isOpen_lt (hχ.sub continuous_const).norm continuous_const).mem_nhds (by simp [hχ0])
  obtain ⟨K₀, hK₀⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hW
  have hpow : ∀ a ∈ K₀, ∀ n : ℕ, χ (n • a) = χ a ^ n := by
    intro a ha n
    induction n with
    | zero => simp [hχ0]
    | succ n ih =>
      have h1 : n • a ∈ K₀ := K₀.toAddSubgroup.nsmul_mem ha n
      rw [succ_nsmul, hmul, ih, hεN _ (hK₀ h1).1 _ (hK₀ ha).1, pow_succ, mul_one]
  have hK₀one : ∀ a ∈ K₀, χ a = 1 := by
    intro a ha
    refine pow_near_one fun n => ?_
    rw [← hpow a ha n]
    exact (hK₀ (K₀.toAddSubgroup.nsmul_mem ha n)).2

  set S : AddSubgroup A := K₀.toAddSubgroup ⊔ lam.ker with hSdef
  have hSopen : IsOpen (S : Set A) :=
    AddSubgroup.isOpen_mono (le_sup_left : K₀.toAddSubgroup ≤ S) K₀.isOpen
  set C : Set A := (S : Set A)ᶜ
  have hCc : IsCompact C := hSopen.isClosed_compl.isCompact
  have hLc : IsClosed (lam '' C) := (hCc.image hlam).isClosed
  have h0 : (0 : V) ∉ lam '' C := by
    rintro ⟨c, hc, hc0⟩
    exact hc (le_sup_right (a := K₀.toAddSubgroup) (AddMonoidHom.mem_ker.2 hc0))
  refine ⟨(lam '' C)ᶜ, hLc.isOpen_compl.mem_nhds h0, fun a ha => ?_⟩
  have haS : a ∈ S := by
    by_contra h
    exact ha ⟨a, h, rfl⟩
  obtain ⟨k, hk, n, hn, rfl⟩ := AddSubgroup.mem_sup.1 haS
  rw [AddMonoidHom.mem_ker] at hn
  rw [hmul, hK₀one k hk, hker n hn, hn, hε0, mul_one, mul_one]

end GlobalTheory.CocycleChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFirstCoords
section
noncomputable section

namespace GlobalTheory.SphereMeanDrop

open MeasureTheory Set

def gaussProb (n : ℕ) : Measure (EuclideanSpace ℂ (Fin n)) :=
  ProbabilityTheory.cond ((volume : Measure (EuclideanSpace ℂ (Fin n))).withDensity
    fun x => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2))) univ

def radProb (n : ℕ) : Measure (Ioi (0 : ℝ)) :=
  ProbabilityTheory.cond ((Measure.volumeIoiPow (2 * n - 1)).withDensity
    fun r => ENNReal.ofReal (Real.exp (-(r : ℝ) ^ 2))) univ

def firstCoords {N n : ℕ} (h : N ≤ n) (x : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 fun j => WithLp.ofLp x (Fin.castLE h j)

end GlobalTheory.SphereMeanDrop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMatrixCoefficient
section
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

namespace GlobalTheory.RealWeil

theorem continuous_matrixCoeff_rhoFun : ∀ (n : ℕ) (g g' : Sch (Fin n)),
    Continuous (fun w : Fin n ⊕ Fin n → ℝ => ∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)) := by
  intro n g g'
  have hp : Continuous (fun w : Fin n ⊕ Fin n → ℝ => pPart w) := by
    unfold pPart; fun_prop
  have hq : Continuous (fun w : Fin n ⊕ Fin n → ℝ => qPart w) := by
    unfold qPart; fun_prop
  refine continuous_of_dominated (bound := fun x => SchwartzMap.seminorm ℂ 0 0 g * ‖g' x‖) ?_ ?_ ?_ ?_
  · intro w
    exact (((continuous_phase w).mul (g.continuous.comp (continuous_id.add continuous_const))).mul
      (continuous_star.comp g'.continuous)).aestronglyMeasurable
  · intro w
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [rhoFun, norm_mul, norm_phase, one_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℂ g _) (norm_nonneg _)
  · exact (SchwartzMap.integrable g').norm.const_mul _
  · refine Filter.Eventually.of_forall fun x => ?_
    simp only [rhoFun, phase]
    fun_prop

end GlobalTheory.RealWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnComplexHessianOfContDiffOnTwo
section
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

namespace GlobalTheory

theorem contDiffOn_one_wdb_of_contDiffOn_two_isOpen {n : ℕ} {U : Set (V n)} {g : V n → ℂ}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U) (l : Fin n) :
    ContDiffOn ℝ 1 (wdb n l g) U := by
  have hD : ContDiffOn ℝ 1 (fun y => fderiv ℝ g y) U :=
    hg.fderiv_of_isOpen hU (by norm_num)
  have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ g y (bas n l)) U :=
    hD.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ 1 (fun y => fderiv ℝ g y (Complex.I • bas n l)) U :=
    hD.clm_apply contDiffOn_const
  have h3 : ContDiffOn ℝ 1
      (fun y => (fderiv ℝ g y (bas n l) + Complex.I * fderiv ℝ g y (Complex.I • bas n l)) / 2) U :=
    (h1.add (contDiffOn_const.mul h2)).div_const 2
  have e : wdb n l g = fun y =>
      (fderiv ℝ g y (bas n l) + Complex.I * fderiv ℝ g y (Complex.I • bas n l)) / 2 :=
    funext fun y => rfl
  rw [e]
  exact h3

theorem continuousOn_wd_of_contDiffOn_one_isOpen {n : ℕ} {U : Set (V n)} {g : V n → ℂ}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U) (j : Fin n) :
    ContinuousOn (wd n j g) U := by
  have hD : ContinuousOn (fun y => fderiv ℝ g y) U :=
    hg.continuousOn_fderiv_of_isOpen hU le_rfl
  have h1 : ContinuousOn (fun y => fderiv ℝ g y (bas n j)) U :=
    hD.clm_apply continuousOn_const
  have h2 : ContinuousOn (fun y => fderiv ℝ g y (Complex.I • bas n j)) U :=
    hD.clm_apply continuousOn_const
  have h3 : ContinuousOn
      (fun y => (fderiv ℝ g y (bas n j) - Complex.I * fderiv ℝ g y (Complex.I • bas n j)) / 2) U :=
    (h1.sub (continuousOn_const.mul h2)).div_const 2
  have e : wd n j g = fun y =>
      (fderiv ℝ g y (bas n j) - Complex.I * fderiv ℝ g y (Complex.I • bas n j)) / 2 :=
    funext fun y => rfl
  rw [e]
  exact h3

theorem continuousOn_cHess_of_contDiffOn_two :
    ∀ (n : ℕ) (U : Set (V n)) (φ : V n → ℝ), IsOpen U → ContDiffOn ℝ 2 φ U → ∀ j l,
      ContinuousOn (fun z => cHess n (fun v => (φ v : ℂ)) z j l) U := by
  intro n U φ hU hφ j l
  have hc : ContDiffOn ℝ 2 (fun v => (φ v : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hφ
  have hb := contDiffOn_one_wdb_of_contDiffOn_two_isOpen hU hc l
  simpa only [cHess, Matrix.of_apply] using continuousOn_wd_of_contDiffOn_one_isOpen hU hb j

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnCoordsOfLinearIndependentStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_coords_of_linearIndependent' : ∀ (g m : ℕ) (U : Set ℂ) (μ : ℂ → Fin m → Fin g → ℂ) (v : ℂ → Fin g → ℂ) (c : ℂ → Fin m → ℝ), ContinuousOn μ U → ContinuousOn v U → (∀ s ∈ U, LinearIndependent ℝ (μ s)) → (∀ s ∈ U, v s = ∑ i, c s i • μ s i) → ContinuousOn c U := by
  first | exact @GlobalTheory.continuousOn_coords_of_linearIndependent | exact GlobalTheory.continuousOn_coords_of_linearIndependent | (intros; apply GlobalTheory.continuousOn_coords_of_linearIndependent <;> assumption)
end

