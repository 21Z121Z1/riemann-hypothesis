import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorOfValuationLeCofinite
section
open NumberField IsDedekindDomain

namespace GlobalTheory.ValBoundDenom

theorem exists_nat_le_exp (a : WithZero (Multiplicative ℤ)) : ∃ n : ℕ, a ≤ WithZero.exp (n : ℤ) := by
  induction a using WithZero.recZeroCoe with
  | zero => exact ⟨0, zero_le'⟩
  | coe m =>
    refine ⟨(Multiplicative.toAdd m).toNat, ?_⟩
    show (m : WithZero (Multiplicative ℤ)) ≤ ((Multiplicative.ofAdd ((Multiplicative.toAdd m).toNat : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    rw [WithZero.coe_le_coe]
    exact Int.self_le_toNat (Multiplicative.toAdd m)

theorem exists_common_denominator_of_valuation_le (E : Type) [Field E] [NumberField E]
    (β : IsDedekindDomain.HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ))
    (hβ : ∀ᶠ w in Filter.cofinite, β w ≤ 1) : ∃ D : 𝓞 E, D ≠ 0 ∧
      ∀ x : E, (∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E), w.valuation E x ≤ β w) →
        IsIntegral ℤ ((D : E) * x) := by
  classical
  have hfin : {w | ¬ β w ≤ 1}.Finite := Filter.eventually_cofinite.mp hβ
  set T := hfin.toFinset with hT
  choose k hk using fun w => exists_nat_le_exp (β w)
  set I : Ideal (𝓞 E) := ∏ w ∈ T, w.asIdeal ^ k w with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro w _
    exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)
  obtain ⟨D, hDI, hD0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  refine ⟨D, hD0, fun x hx => ?_⟩
  have hle : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 E), w.valuation E ((D : E) * x) ≤ 1 := by
    intro w
    rw [map_mul]
    by_cases hw : w ∈ T
    · have hmem : D ∈ w.asIdeal ^ k w :=
        (Finset.inf_le hw : T.inf (fun w => w.asIdeal ^ k w) ≤ _) (Ideal.prod_le_inf hDI)
      have h1 : w.valuation E (D : E) ≤ WithZero.exp (-(k w : ℤ)) := by
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        exact (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).mpr hmem
      have h2 : w.valuation E x ≤ WithZero.exp (k w : ℤ) := (hx w).trans (hk w)
      calc w.valuation E (D : E) * w.valuation E x
          ≤ WithZero.exp (-(k w : ℤ)) * WithZero.exp (k w : ℤ) := mul_le_mul' h1 h2
        _ = 1 := by rw [← WithZero.exp_add]; simp
    · have hw1 : β w ≤ 1 := by
        by_contra h
        exact hw (by rw [hT, Set.Finite.mem_toFinset]; exact h)
      exact mul_le_one' (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _) ((hx w).trans hw1)
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one E _ hle
  rw [← hr]
  exact r.isIntegral_coe

end GlobalTheory.ValBoundDenom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFieldExtension
section
open scoped TensorProduct

namespace GlobalTheory

theorem exists_common_field_extension :
    ∀ (Ω Ω₁ Ω₂ : Type) [Field Ω] [Field Ω₁] [Field Ω₂] (i₁ : Ω →+* Ω₁) (i₂ : Ω →+* Ω₂),
      ∃ (Ω₃ : Type) (_ : Field Ω₃) (j₁ : Ω₁ →+* Ω₃) (j₂ : Ω₂ →+* Ω₃), j₁.comp i₁ = j₂.comp i₂ := by
  intro Ω Ω₁ Ω₂ _ _ _ i₁ i₂
  letI : Algebra Ω Ω₁ := i₁.toAlgebra
  letI : Algebra Ω Ω₂ := i₂.toAlgebra
  haveI : Nontrivial (Ω₁ ⊗[Ω] Ω₂) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (Ω₁ ⊗[Ω] Ω₂)
  refine ⟨(Ω₁ ⊗[Ω] Ω₂) ⧸ m, Ideal.Quotient.field m,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeLeftRingHom),
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := Ω) (A := Ω₁) (B := Ω₂)).toRingHom, ?_⟩
  ext x
  have h : (algebraMap Ω Ω₁ x) ⊗ₜ[Ω] (1 : Ω₂) = (1 : Ω₁) ⊗ₜ[Ω] (algebraMap Ω Ω₂ x) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  exact congrArg (Ideal.Quotient.mk m) h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentSurjectsClopen
section
namespace GlobalTheory

theorem clopen_image_irreducibleComponent : ∀ {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (f : A → B), Continuous f → IsOpenMap f → IsClosedMap f →
    (∀ C ∈ irreducibleComponents A, IsOpen C) → ∀ S : Set B, IsClopen S → IsPreconnected S → ∀ a : A, f a ∈ S →
    ∃ C ∈ irreducibleComponents A, a ∈ C ∧ f '' C = S := by
  intro A B _ _ f hf hop hcl hcomp S hS hSc a ha
  refine ⟨irreducibleComponent a, irreducibleComponent_mem_irreducibleComponents a,
    mem_irreducibleComponent, ?_⟩
  have hCc : IsClosed (irreducibleComponent a) := isClosed_irreducibleComponent
  have hCo : IsOpen (irreducibleComponent a) :=
    hcomp _ (irreducibleComponent_mem_irreducibleComponents a)
  have hCp : IsPreconnected (irreducibleComponent a) :=
    (IsIrreducible.isConnected (isIrreducible_irreducibleComponent (x := a))).isPreconnected
  have hsub : irreducibleComponent a ⊆ f ⁻¹' S :=
    hCp.subset_isClopen (hS.preimage hf) ⟨a, mem_irreducibleComponent, ha⟩
  have himg : f '' irreducibleComponent a ⊆ S := Set.image_subset_iff.mpr hsub
  have hclo : IsClopen (f '' irreducibleComponent a) := ⟨hcl _ hCc, hop _ hCo⟩
  refine le_antisymm himg ?_
  exact hSc.subset_isClopen hclo ⟨f a, ha, a, mem_irreducibleComponent, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjDiagonal
section
namespace GlobalTheory.DiagonalConjugateExistence

theorem exists_conj_diagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : Fin n → ℂ)
    (ht : Function.Injective t)
    (hA : Matrix.charpoly A = ∏ i : Fin n, (Polynomial.X - Polynomial.C (t i))) :
    ∃ P : GL (Fin n) ℂ, A * (P : Matrix (Fin n) (Fin n) ℂ)
      = (P : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal t := by
  have hev : ∀ i, ∃ v : Fin n → ℂ, v ≠ 0 ∧ A.mulVec v = t i • v := by
    intro i
    have h0 : (Matrix.scalar (Fin n) (t i) - A).det = 0 := by
      rw [← Matrix.eval_charpoly, hA, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv0
    rw [← hv0]
    ext j
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  choose v hv0 hv using hev
  have hli : LinearIndependent ℂ v := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' A) t ht v ?_
    intro i
    refine ⟨?_, hv0 i⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, hv]
  have hu : IsUnit (Matrix.of fun i j => v j i : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli
  refine ⟨hu.unit, ?_⟩
  rw [hu.unit_spec]
  ext i j
  have := congrFun (hv j) i
  rw [Matrix.mul_diagonal]
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [this, mul_comm]

end GlobalTheory.DiagonalConjugateExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjSkewDetUnitOfAvoidance
section
open scoped Matrix

namespace GlobalTheory

theorem exists_conj_skew_det_unit_of_avoidance :
  ∀ {F R : Type} [Field F] [CommRing R] [Algebra F R] [Invertible (2 : R)] (c : R →+* R), (∀ r, c (c r) = r) → (∀ t : F, c (algebraMap F R t) = algebraMap F R t) → ∀ (e : R), (∀ ψ : Polynomial R, (∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0) → ∃ t : F, IsUnit (e * ψ.eval (algebraMap F R t) + (1 - e))) → ∀ (ρ : R), IsUnit ρ → c ρ = -ρ → ∀ {n : ℕ} (J₀ : Matrix (Fin n) (Fin n) R) (ε : ℤˣ), (J₀.map c)ᵀ = ((ε : ℤ) : R) • J₀ → IsUnit J₀.det → ∀ (D C x₀ : Matrix (Fin n) (Fin n) R), IsUnit (e * (D + C * x₀).det + (1 - e)) → ∃ x : Matrix (Fin n) (Fin n) R, xᵀ * J₀ + J₀ * x.map c = 0 ∧ IsUnit (e * (D + C * x).det + (1 - e)) := by
  intro F R _ _ _ _ c hcc hcF e H ρ hρ hcρ n J₀ ε hJ hdet D C x₀ hx₀
  obtain ⟨e', he'⟩ : ∃ a : R, a = ((ε : ℤ) : R) := ⟨_, rfl⟩
  rw [← he'] at hJ
  have hee : e' * e' = 1 := by
    rw [he', ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hce : c e' = e' := by rw [he']; exact map_intCast c _
  have h2 : (2 : R) * ⅟2 = 1 := mul_invOf_self 2
  have hc2 : c (⅟2 : R) = ⅟2 := by
    have h1 : c (⅟2 : R) * 2 = 1 := by
      have := congrArg c (invOf_mul_self (2 : R))
      rwa [map_mul, map_ofNat, map_one] at this
    calc c (⅟2 : R) = c (⅟2) * (2 * ⅟2) := by rw [h2, mul_one]
      _ = ⅟2 := by rw [← mul_assoc, h1, one_mul]
  obtain ⟨r, hr'⟩ : ∃ a : R, a = ↑hρ.unit⁻¹ := ⟨_, rfl⟩
  have hr : ρ * r = 1 := by rw [hr']; exact hρ.mul_val_inv
  have hcr : c r = -r := by
    have h1 : c r * (-ρ) = 1 := by rw [← hcρ, ← map_mul, mul_comm, hr, map_one]
    linear_combination (-r) * h1 + (-c r) * hr
  have hKdet : IsUnit (J₀ᵀ).det := by rw [Matrix.det_transpose]; exact hdet
  have hLK : J₀ᵀ⁻¹ * J₀ᵀ = 1 := Matrix.nonsing_inv_mul _ hKdet
  have hLtJ : (J₀ᵀ⁻¹)ᵀ * J₀ = 1 := by
    have : J₀ * (J₀ᵀ⁻¹)ᵀ = 1 := by
      have := congrArg Matrix.transpose hLK
      rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
    exact mul_eq_one_comm.mp this
  have hJLc : J₀ * (J₀ᵀ⁻¹).map c = e' • 1 := by
    have h1 : (J₀ᵀ⁻¹).map c * (e' • J₀) = 1 := by
      have := congrArg c.mapMatrix hLK
      rw [map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.transpose_map, hJ] at this
      exact this
    have h3 : (e' • J₀) * (J₀ᵀ⁻¹).map c = 1 := mul_eq_one_comm.mp h1
    rw [Matrix.smul_mul] at h3
    calc J₀ * (J₀ᵀ⁻¹).map c = (e' * e') • (J₀ * (J₀ᵀ⁻¹).map c) := by rw [hee, one_smul]
      _ = e' • (e' • (J₀ * (J₀ᵀ⁻¹).map c)) := by rw [mul_smul]
      _ = e' • 1 := by rw [h3]
  obtain ⟨M₀, hM₀⟩ : ∃ M : Matrix (Fin n) (Fin n) R, M = J₀ᵀ * x₀ := ⟨_, rfl⟩
  obtain ⟨v, hv'⟩ : ∃ M : Matrix (Fin n) (Fin n) R,
      M = (⅟2 : R) • (M₀ - Matrix.of fun i j => e' * c (M₀ j i)) := ⟨_, rfl⟩
  obtain ⟨w, hw'⟩ : ∃ M : Matrix (Fin n) (Fin n) R,
      M = (r * ⅟2) • (M₀ + Matrix.of fun i j => e' * c (M₀ j i)) := ⟨_, rfl⟩
  have hv : ∀ i j, v j i + e' * c (v i j) = 0 := by
    intro i j
    simp only [hv', Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply, smul_eq_mul, map_mul,
      map_sub, hc2, hce, hcc]
    linear_combination (-(⅟2 : R) * M₀ j i) * hee
  have hw : ∀ i j, w j i + e' * c (w i j) = 0 := by
    intro i j
    simp only [hw', Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, smul_eq_mul, map_mul,
      map_add, hc2, hce, hcc, hcr]
    linear_combination (-(r * ⅟2) * M₀ j i) * hee
  have hsum : v + ρ • w = M₀ := by
    ext i j
    simp only [hv', hw', Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply,
      smul_eq_mul]
    linear_combination ((⅟2 : R) * (M₀ i j + e' * c (M₀ j i))) * hr + M₀ i j * h2
  have hcond : ∀ s, c s = s →
      (J₀ᵀ⁻¹ * (v + s • w))ᵀ * J₀ + J₀ * (J₀ᵀ⁻¹ * (v + s • w)).map c = 0 := by
    intro s hs
    have e1 : (J₀ᵀ⁻¹ * (v + s • w))ᵀ * J₀ = (v + s • w)ᵀ := by
      rw [Matrix.transpose_mul, Matrix.mul_assoc, hLtJ, Matrix.mul_one]
    have e2 : J₀ * (J₀ᵀ⁻¹ * (v + s • w)).map c = e' • (v + s • w).map c := by
      rw [Matrix.map_mul, ← Matrix.mul_assoc, hJLc, Matrix.smul_mul, Matrix.one_mul]
    rw [e1, e2]
    ext i j
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply,
      smul_eq_mul, map_add, map_mul, hs, Matrix.zero_apply]
    linear_combination hv i j + s * hw i j
  obtain ⟨ψ, hψ⟩ : ∃ p : Polynomial R, p = ((D + C * J₀ᵀ⁻¹ * v).map Polynomial.C +
      (Polynomial.X : Polynomial R) • (C * J₀ᵀ⁻¹ * w).map Polynomial.C).det := ⟨_, rfl⟩
  have hev : ∀ s, ψ.eval s = (D + C * (J₀ᵀ⁻¹ * (v + s • w))).det := by
    intro s
    have hre : D + C * (J₀ᵀ⁻¹ * (v + s • w)) = (D + C * J₀ᵀ⁻¹ * v) + s • (C * J₀ᵀ⁻¹ * w) := by
      simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc, add_assoc]
    rw [hre, hψ, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C]
  have hρev : ψ.eval ρ = (D + C * x₀).det := by
    rw [hev, hsum, hM₀, ← Matrix.mul_assoc J₀ᵀ⁻¹, hLK, Matrix.one_mul]
  have hne : ∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0 := by
    intro Ω _ φ hφ h0
    have h1 := congrArg (Polynomial.eval (φ ρ)) h0
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, Polynomial.eval_zero, hρev] at h1
    have hu := hx₀.map φ
    rw [map_add, map_mul, map_sub, map_one, hφ, one_mul, sub_self, add_zero, h1] at hu
    exact not_isUnit_zero hu
  obtain ⟨t, ht⟩ := H ψ hne
  refine ⟨J₀ᵀ⁻¹ * (v + algebraMap F R t • w), hcond _ (hcF t), ?_⟩
  rwa [hev] at ht

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinateProjectionComplex
section
namespace GlobalTheory

theorem realDiag_conj_coordProj : ∀ (g : ℕ) (K : Type) (ρ : K → Fin g → ℝ), (∀ j k, j ≠ k → ∃ a, ρ a j ≠ ρ a k) →
    ∀ (T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)),
    (∀ a, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v, T (fun m ↦ (ρ a m : ℂ) * v m) = M (T v)) →
    ∀ j : Fin g, ∃ q : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v, q (T v) = T (Pi.single j (v j)) := by
  intro g K ρ hsep T hT j
  classical
  let P : (Fin g → ℝ) → Prop := fun c =>
    ∃ q : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v, T (fun m ↦ (c m : ℂ) * v m) = q (T v)
  have hconst : ∀ r : ℝ, P (fun _ => r) := by
    intro r
    refine ⟨(r : ℂ) • LinearMap.id, fun v => ?_⟩
    have h : (fun m ↦ ((r : ℝ) : ℂ) * v m) = r • v := by
      funext m; simp [Complex.real_smul]
    rw [h, map_smul]
    funext m
    simp [Complex.real_smul]
  have hadd : ∀ c d, P c → P d → P (c + d) := by
    rintro c d ⟨q1, h1⟩ ⟨q2, h2⟩
    refine ⟨q1 + q2, fun v => ?_⟩
    have h : (fun m ↦ (((c + d) m : ℝ) : ℂ) * v m)
        = (fun m ↦ (c m : ℂ) * v m) + (fun m ↦ (d m : ℂ) * v m) := by
      funext m; simp [add_mul]
    rw [h, map_add, h1, h2, LinearMap.add_apply]
  have hmul : ∀ c d, P c → P d → P (c * d) := by
    rintro c d ⟨q1, h1⟩ ⟨q2, h2⟩
    refine ⟨q1 ∘ₗ q2, fun v => ?_⟩
    calc T (fun m ↦ (((c * d) m : ℝ) : ℂ) * v m)
        = T (fun m ↦ (c m : ℂ) * ((d m : ℂ) * v m)) := by
          congr 1; funext m; simp [mul_assoc]
      _ = q1 (T (fun m ↦ (d m : ℂ) * v m)) := h1 _
      _ = (q1 ∘ₗ q2) (T v) := by rw [h2]; rfl
  have hρ : ∀ a, P (ρ a) := fun a => by
    obtain ⟨M, hM⟩ := hT a
    exact ⟨M, hM⟩
  have haff : ∀ c s t, P c → P (fun m => (c m - s) * t) := by
    intro c s t hc
    have h : (fun m => (c m - s) * t) = (c + (fun _ => -s)) * (fun _ => t) := by
      funext m; simp [sub_eq_add_neg]
    rw [h]; exact hmul _ _ (hadd _ _ hc (hconst _)) (hconst _)
  let f : Fin g → (Fin g → ℝ) := fun k =>
    if h : j ≠ k then
      (fun m => (ρ (Classical.choose (hsep j k h)) m - ρ (Classical.choose (hsep j k h)) k) *
        (ρ (Classical.choose (hsep j k h)) j - ρ (Classical.choose (hsep j k h)) k)⁻¹)
    else 1
  have hf : ∀ k, P (f k) := by
    intro k
    by_cases h : j ≠ k
    · simp only [f, dif_pos h]
      exact haff _ _ _ (hρ _)
    · simp only [f, dif_neg h]
      exact hconst 1
  let δ : Fin g → ℝ := ∏ k ∈ Finset.univ.erase j, f k
  have hδ : P δ := Finset.prod_induction _ P hmul (hconst 1) (fun k _ => hf k)
  have hδj : δ j = 1 := by
    simp only [δ, Finset.prod_apply]
    apply Finset.prod_eq_one
    intro k hk
    have hjk : j ≠ k := (Finset.ne_of_mem_erase hk).symm
    simp only [f, dif_pos hjk]
    exact mul_inv_cancel₀ (sub_ne_zero.mpr (Classical.choose_spec (hsep j k hjk)))
  have hδm : ∀ m, m ≠ j → δ m = 0 := by
    intro m hm
    simp only [δ, Finset.prod_apply]
    apply Finset.prod_eq_zero (i := m) (Finset.mem_erase.mpr ⟨hm, Finset.mem_univ _⟩)
    have hjm : j ≠ m := fun h => hm h.symm
    simp only [f, dif_pos hjm, sub_self, zero_mul]
  obtain ⟨q, hq⟩ := hδ
  refine ⟨q, fun v => ?_⟩
  rw [← hq]
  congr 1
  funext m
  by_cases hm : m = j
  · subst hm; simp [hδj]
  · simp [hδm m hm, Pi.single_apply, hm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordsRangeIdempotentOfRetract
section
universe u

namespace GlobalTheory

theorem idem_retract_coords : ∀ {C : Type} [CommRing C] [IsLocalRing C] (I : Ideal C), I ≠ ⊤ →
  ∀ {W : Type u} [AddCommGroup W] [Module C W] (m : ℕ) (s : W →ₗ[C] (Fin m → C ⧸ I))
  (r : (Fin m → C ⧸ I) →ₗ[C] W), r ∘ₗ s = LinearMap.id →
  ∀ (p : Module.End C W), p * p = p →
  ∃ (n : ℕ) (b : Fin n → W) (f : Fin n → W →ₗ[C] C ⧸ I),
    (∀ k, b k ∈ LinearMap.range p) ∧ (∀ k w, f k (p w) = f k w) ∧
    (∀ j k, f j (b k) = if j = k then 1 else 0) ∧
    (∀ w ∈ LinearMap.range p, (∀ k, f k w = 0) → w = 0) := by
  intro C _ _ I hI W _ _ m s r hrs p hp
  haveI : Nontrivial (C ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (C ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hrs' : ∀ w, r (s w) = w := fun w => by simpa using LinearMap.congr_fun hrs w
  have hp' : ∀ w, p (p w) = p w := fun w => by simpa [Module.End.mul_apply] using LinearMap.congr_fun hp w
  let q0 : (Fin m → C ⧸ I) →ₗ[C] (Fin m → C ⧸ I) := s ∘ₗ p ∘ₗ r
  let q : (Fin m → C ⧸ I) →ₗ[C ⧸ I] (Fin m → C ⧸ I) :=
    q0.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  have hq : ∀ x, q x = s (p (r x)) := fun x => rfl
  have hqq : ∀ x, q (q x) = q x := by
    intro x; simp only [hq, hrs', hp']
  let P := LinearMap.range q
  let π : (Fin m → C ⧸ I) →ₗ[C ⧸ I] P :=
    LinearMap.codRestrict P q (fun x => LinearMap.mem_range_self q x)
  have hπι : π ∘ₗ P.subtype = LinearMap.id := by
    ext ⟨x, y, rfl⟩
    simp [π, hqq]
  haveI : Module.Projective (C ⧸ I) P := Module.Projective.of_split P.subtype π hπι
  haveI : Module.Finite (C ⧸ I) P := Module.Finite.of_surjective π (by
    intro y; exact ⟨y, by simpa using LinearMap.congr_fun hπι y⟩)
  haveI : Module.FinitePresentation (C ⧸ I) P := Module.finitePresentation_of_projective _ _
  haveI : Module.Free (C ⧸ I) P := Module.free_of_flat_of_isLocalRing
  let β := Module.finBasis (C ⧸ I) P
  have mem : ∀ w, s (p w) ∈ P := fun w => ⟨s w, by simp [hq, hrs']⟩
  let f : Fin (Module.finrank (C ⧸ I) P) → W →ₗ[C] C ⧸ I := fun k =>
    { toFun := fun w => β.coord k ⟨s (p w), mem w⟩
      map_add' := by
        intro a c
        rw [← map_add]; congr 1; ext1; simp
      map_smul' := by
        intro c w
        have e : (⟨s (p (c • w)), mem _⟩ : P) = (Ideal.Quotient.mk I c) • ⟨s (p w), mem w⟩ := by
          ext1
          funext i
          simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
        show β.coord k ⟨s (p (c • w)), mem _⟩ = _
        rw [e, map_smul, RingHom.id_apply, smul_eq_mul, Algebra.smul_def,
          Ideal.Quotient.algebraMap_eq] }
  have hf : ∀ k w, f k w = β.coord k ⟨s (p w), mem w⟩ := fun _ _ => rfl
  refine ⟨_, fun k => r (β k), f, ?_, ?_, ?_, ?_⟩
  · intro k
    obtain ⟨x, hx⟩ := (β k).2
    refine ⟨r x, ?_⟩
    show p (r x) = r ((β k : P) : Fin m → C ⧸ I)
    rw [← hx, hq, hrs']
  · intro k w
    rw [hf, hf]
    congr 1
    ext1
    simp [hp']
  · intro j k
    rw [hf]
    have e : (⟨s (p (r (β k))), mem _⟩ : P) = β k := by
      ext1
      show s (p (r ((β k : P) : Fin m → C ⧸ I))) = ((β k : P) : Fin m → C ⧸ I)
      obtain ⟨x, hx⟩ := (β k).2
      rw [← hq, ← hx, hqq]
    rw [e, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    simp [eq_comm]
  · rintro w ⟨y, rfl⟩ h0
    have e : (⟨s (p (p y)), mem _⟩ : P) = 0 := by
      apply β.forall_coord_eq_zero_iff.mp
      intro k; rw [← hf]; exact h0 k
    have e2 : s (p (p y)) = 0 := congrArg Subtype.val e
    rw [← hrs' (p y), ← hp' y, e2, map_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeIdealMulEqSpanNumberField
section
open scoped NumberField

namespace GlobalTheory.IdealPrincipalCoprime

theorem natCast_prime_not_isUnit (F : Type) [Field F] [NumberField F] {p : ℕ} (hp : p.Prime) :
    ¬ IsUnit (p : 𝓞 F) := by
  intro h
  have h1 := h.map (Algebra.norm ℤ (S := 𝓞 F))
  rw [← map_natCast (algebraMap ℤ (𝓞 F)), Algebra.norm_algebraMap,
    isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at h1
  exact hp.ne_one h1

theorem exists_mul_eq_span_coprime : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime →
    ∀ (w : Ideal (𝓞 F)), w ≠ ⊥ → ∃ (g e : 𝓞 F) (𝔟 : Ideal (𝓞 F)), g ≠ 0 ∧ e ∈ w ∧ 1 - e ∈ 𝔟 ∧
      w * 𝔟 = Ideal.span {g} ∧ 𝔟 ⊔ Ideal.span {(p : 𝓞 F)} = ⊤ := by
  intro F _ _ p hp w hw
  set N : Ideal (𝓞 F) := Ideal.span {(p : 𝓞 F)} * w with hN
  have hp0 : (p : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hN0 : N ≠ ⊥ := by
    rw [hN, Ne, Ideal.mul_eq_bot, not_or, Ideal.span_singleton_eq_bot]
    exact ⟨hp0, hw⟩
  obtain ⟨g, hg⟩ := IsDedekindDomain.exists_sup_span_eq (I := w * N) (J := w) Ideal.mul_le_left
    (mul_ne_zero hw hN0)
  have hgw : Ideal.span {g} ≤ w := hg ▸ le_sup_right
  obtain ⟨𝔟, h𝔟⟩ := Ideal.dvd_iff_le.mpr hgw
  have hsup : N ⊔ 𝔟 = ⊤ := by
    apply mul_left_cancel₀ (show w ≠ 0 from hw)
    rw [Ideal.mul_sup, ← h𝔟, hg, Ideal.mul_top]
  have hNp : N ≤ Ideal.span {(p : 𝓞 F)} := Ideal.mul_le_left
  have hNw : N ≤ w := Ideal.mul_le_right
  have hbp : 𝔟 ⊔ Ideal.span {(p : 𝓞 F)} = ⊤ := by
    have h : N ⊔ 𝔟 ≤ 𝔟 ⊔ Ideal.span {(p : 𝓞 F)} := sup_le (le_sup_of_le_right hNp) le_sup_left
    rw [hsup] at h; exact eq_top_iff.mpr h
  have hwb : w ⊔ 𝔟 = ⊤ := by
    have h : N ⊔ 𝔟 ≤ w ⊔ 𝔟 := sup_le (le_sup_of_le_left hNw) le_sup_right
    rw [hsup] at h; exact eq_top_iff.mpr h
  have h1 : (1 : 𝓞 F) ∈ w ⊔ 𝔟 := by rw [hwb]; exact Submodule.mem_top
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.mp h1
  refine ⟨g, e, 𝔟, ?_, he, ?_, h𝔟.symm, hbp⟩
  · intro hg0
    have hb0 : 𝔟 = ⊥ := by
      have : w * 𝔟 = ⊥ := by rw [← h𝔟, hg0, Ideal.span_singleton_eq_bot.mpr rfl]
      rcases Ideal.mul_eq_bot.mp this with h | h
      · exact absurd h hw
      · exact h
    rw [hb0, bot_sup_eq] at hbp
    exact natCast_prime_not_isUnit F hp (Ideal.span_singleton_eq_top.mp hbp)
  · rw [← hef, add_sub_cancel_left]; exact hf

end GlobalTheory.IdealPrincipalCoprime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationSplitKaehlerDSmooth
section
open KaehlerDifferential
namespace GlobalTheory
theorem bertini_derivation_split : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.Smooth k A], ∃ (n : ℕ) (δ : Fin n → Derivation k A A) (ω : Fin n → KaehlerDifferential k A), ∀ a : A, KaehlerDifferential.D k A a = ∑ l, δ l a • ω l := by
  intro k A _ _ _ _
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A (KaehlerDifferential k A)
  refine ⟨n, fun l => (LinearMap.proj l ∘ₗ g).compDer (KaehlerDifferential.D k A), fun l => f (Pi.single l 1), ?_⟩
  intro a
  have h := LinearMap.congr_fun hfg (KaehlerDifferential.D k A a)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
  conv_lhs => rw [← h]
  conv_lhs => rw [pi_eq_sum_univ (g (KaehlerDifferential.D k A a))]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionEmbedding
section
open scoped TensorProduct

namespace GlobalTheory.FiniteExtensionEmbedding

theorem exists_finite_extension_embedding (F K : Type) [Field F] [CharZero F]
    [FiniteDimensional ℚ F] [Field K] [CharZero K] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧ Nonempty (F →+* L) := by
  haveI : Nontrivial (K ⊗[ℚ] F) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[ℚ] F)
  letI : Field ((K ⊗[ℚ] F) ⧸ m) := Ideal.Quotient.field m
  refine ⟨(K ⊗[ℚ] F) ⧸ m, inferInstance, inferInstance, ?_, ⟨?_⟩⟩
  · exact Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap
      (Ideal.Quotient.mkₐ_surjective K m)
  · exact (Ideal.Quotient.mk m).comp
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := K) (B := F)).toRingHom

end GlobalTheory.FiniteExtensionEmbedding
end

