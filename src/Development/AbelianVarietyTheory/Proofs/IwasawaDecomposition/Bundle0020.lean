import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorResidueUnramifiedFinite
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem tensor_quot_maximalIdeal_finite_formallyUnramified :
    ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [IsLocalRing R] [Algebra A B]
      [Algebra A R], ((IsLocalRing.residue R).comp (algebraMap A R)).Finite →
      ((IsLocalRing.residue R).comp (algebraMap A R)).FormallyUnramified →
      Algebra.FormallyUnramified B (TensorProduct A B R ⧸ (IsLocalRing.maximalIdeal R).map
        (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R)) ∧
      Module.Finite B (TensorProduct A B R ⧸ (IsLocalRing.maximalIdeal R).map
        (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R)) := by
  intro A B R _ _ _ _ _ _ hfin hfu
  have hf : Module.Finite A (R ⧸ maximalIdeal R) := by
    rw [← RingHom.finite_algebraMap]; exact hfin
  have hu : Algebra.FormallyUnramified A (R ⧸ maximalIdeal R) := by
    rw [← RingHom.formallyUnramified_algebraMap]; exact hfu
  let e := Algebra.TensorProduct.tensorQuotientEquiv (R := A) B R B (maximalIdeal R)
  haveI : Algebra.FormallyUnramified B (B ⊗[A] (R ⧸ maximalIdeal R)) :=
    Algebra.FormallyUnramified.base_change B
  haveI : Module.Finite B (B ⊗[A] (R ⧸ maximalIdeal R)) := Module.Finite.base_change A B _
  exact ⟨Algebra.FormallyUnramified.of_equiv e, Module.Finite.equiv e.toLinearEquiv⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeAevalLeOfLinear
section
namespace GlobalTheory.AevalTotalDegreeLinear

open MvPolynomial

theorem totalDegree_aeval_le_of_linear {κ : Type} (f : κ → MvPolynomial κ ℂ)
    (hf : ∀ (i : κ), MvPolynomial.totalDegree (f i) ≤ (1 : ℕ)) (P : MvPolynomial κ ℂ) :
    MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial κ ℂ → MvPolynomial κ ℂ) P)
      ≤ MvPolynomial.totalDegree P := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine (totalDegree_finset_sum _ _).trans ?_
  refine Finset.sup_le fun s hs => ?_
  rw [aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [algebraMap_eq, totalDegree_C, zero_add]
  have hprod : totalDegree (s.prod fun i k => f i ^ k) ≤ s.sum fun _ k => k := by
    rw [Finsupp.prod, Finsupp.sum]
    refine (totalDegree_finset_prod _ _).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine (totalDegree_pow _ _).trans ?_
    calc s i * totalDegree (f i) ≤ s i * 1 := Nat.mul_le_mul_left _ (hf i)
      _ = s i := mul_one _
  refine hprod.trans ?_
  exact Finset.le_sup (f := fun s : κ →₀ ℕ => s.sum fun _ e => e) hs

theorem main : ∀ {κ : Type} (f : κ → MvPolynomial κ ℂ), (∀ (i : κ), MvPolynomial.totalDegree (f i) ≤ (1 : ℕ)) → ∀ (P : MvPolynomial κ ℂ), MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial κ ℂ → MvPolynomial κ ℂ) P) ≤ MvPolynomial.totalDegree P :=
  fun f hf P => totalDegree_aeval_le_of_linear f hf P

end GlobalTheory.AevalTotalDegreeLinear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowEq
section
namespace GlobalTheory.TracePowEq

open Matrix

theorem trace_pow_eq {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ}
    (E : Fin n → Fin n → A) (E' : Fin m → Fin m → A)
    (P : Matrix (Fin m) (Fin n) ℂ) (Q : Matrix (Fin n) (Fin m) ℂ)
    (hPQ : P * Q = (1 : Matrix (Fin m) (Fin m) ℂ))
    (hQP : Q * P = (1 : Matrix (Fin n) (Fin n) ℂ))
    (h : ∀ (a b : Fin m), E' a b = ∑ c : Fin n, ∑ d : Fin n, (Q c a * P b d) • E c d) (k : ℕ) :
    ∑ c : Fin m, ((Matrix.of : (Fin m → Fin m → A) → Matrix (Fin m) (Fin m) A) E' ^ k) c c
      = ∑ c : Fin n, ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ k) c c := by

  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin m) (Fin n) A, S = Qᵀ.map (algebraMap ℂ A) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin m) A, T = Pᵀ.map (algebraMap ℂ A) := ⟨_, rfl⟩
  have hTS : T * S = 1 := by
    rw [hT, hS, ← Matrix.map_mul, ← Matrix.transpose_mul, hQP, Matrix.transpose_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hST : S * T = 1 := by
    rw [hT, hS, ← Matrix.map_mul, ← Matrix.transpose_mul, hPQ, Matrix.transpose_one,
      Matrix.map_one _ (map_zero _) (map_one _)]

  have hE : (Matrix.of E' : Matrix (Fin m) (Fin m) A) = S * Matrix.of E * T := by
    ext a b
    have key : ∀ c d, (Q c a * P b d) • E c d = S a c * E c d * T d b := by
      intro c d
      rw [hS, hT, Matrix.map_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.transpose_apply,
        Algebra.smul_def, map_mul, mul_assoc, Algebra.commutes (P b d) (E c d), ← mul_assoc]
    rw [Matrix.of_apply, h a b]
    simp only [key, Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
    exact Finset.sum_comm

  have hpow : ∀ j : ℕ, (S * Matrix.of E * T) ^ j = S * Matrix.of E ^ j * T := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hST]
    | succ j ih =>
      rw [pow_succ, ih, pow_succ]
      calc S * Matrix.of E ^ j * T * (S * Matrix.of E * T)
          = S * Matrix.of E ^ j * (T * S) * Matrix.of E * T := by simp only [Matrix.mul_assoc]
        _ = S * (Matrix.of E ^ j * Matrix.of E) * T := by rw [hTS, Matrix.mul_one, Matrix.mul_assoc S]

  have hcyc : ∀ X : Matrix (Fin n) (Fin m) A, ∑ c, (S * X) c c = ∑ d, (X * S) d d := by
    intro X
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun c _ => ?_
    rw [hS, Matrix.map_apply, Algebra.commutes]
  rw [hE, hpow, Matrix.mul_assoc, hcyc, Matrix.mul_assoc, hTS, Matrix.mul_one]

end GlobalTheory.TracePowEq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrdegResidueFieldEq
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.FibreMinimalPrime

theorem trdeg_residueField_eq {R : Type} [CommRing R] (r : ℕ) (Q : Ideal (MvPolynomial (Fin r) R)) [Q.IsPrime]
    (hmin : ∀ Q' : Ideal (MvPolynomial (Fin r) R), Q'.IsPrime → Q' ≤ Q →
      Q'.comap (MvPolynomial.C : R →+* _) = Q.comap MvPolynomial.C → Q' = Q) :
    @Algebra.trdeg (Q.comap (MvPolynomial.C : R →+* _)).ResidueField Q.ResidueField _ _
      (Ideal.ResidueField.map (Q.comap MvPolynomial.C) Q MvPolynomial.C rfl).toAlgebra = r := by
  classical
  set q : Ideal R := Q.comap (MvPolynomial.C : R →+* _) with hq_def
  let f : MvPolynomial (Fin r) R →+* MvPolynomial (Fin r) (R ⧸ q) := MvPolynomial.map (Ideal.Quotient.mk q)
  have hfs : Function.Surjective f := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective

  have hker_prime : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  have hker_le : RingHom.ker f ≤ Q := by
    show RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk q)) ≤ Q
    rw [MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_le_iff_le_comap]
  have hker_comap : (RingHom.ker f).comap (MvPolynomial.C : R →+* _) = q := by
    ext a
    simp only [Ideal.mem_comap, RingHom.mem_ker, f, MvPolynomial.map_C, MvPolynomial.C_eq_zero,
      Ideal.Quotient.eq_zero_iff_mem]

  have hQ : Q = RingHom.ker f := (hmin _ hker_prime hker_le hker_comap).symm

  letI algKL : Algebra q.ResidueField Q.ResidueField :=
    (Ideal.ResidueField.map q Q MvPolynomial.C rfl).toAlgebra
  letI algkL : Algebra (R ⧸ q) Q.ResidueField :=
    ((algebraMap q.ResidueField Q.ResidueField).comp (algebraMap (R ⧸ q) q.ResidueField)).toAlgebra
  haveI : IsScalarTower (R ⧸ q) q.ResidueField Q.ResidueField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI algkB : Algebra (R ⧸ q) (MvPolynomial (Fin r) R ⧸ Q) :=
    (Ideal.quotientMap Q (MvPolynomial.C : R →+* _) le_rfl).toAlgebra
  haveI : IsScalarTower (R ⧸ q) (MvPolynomial (Fin r) R ⧸ Q) Q.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    show Ideal.ResidueField.map q Q MvPolynomial.C rfl
        (algebraMap (R ⧸ q) q.ResidueField (Ideal.Quotient.mk q a)) =
      algebraMap (MvPolynomial (Fin r) R ⧸ Q) Q.ResidueField
        (Ideal.quotientMap Q (MvPolynomial.C : R →+* _) le_rfl (Ideal.Quotient.mk q a))
    rw [Ideal.algebraMap_quotient_residueField_mk, Ideal.ResidueField.map_algebraMap,
      Ideal.quotientMap_mk, Ideal.algebraMap_quotient_residueField_mk]
  haveI : FaithfulSMul (R ⧸ q) q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective _ _)
  haveI : FaithfulSMul q.ResidueField Q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap q.ResidueField Q.ResidueField).injective
  haveI : FaithfulSMul (R ⧸ q) (MvPolynomial (Fin r) R ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.quotientMap_injective
  haveI : FaithfulSMul (MvPolynomial (Fin r) R ⧸ Q) Q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective _ _)

  let e0 : (MvPolynomial (Fin r) R ⧸ Q) ≃+* MvPolynomial (Fin r) (R ⧸ q) :=
    (Ideal.quotEquivOfEq hQ).trans (RingHom.quotientKerEquivOfSurjective hfs)
  let e : (MvPolynomial (Fin r) R ⧸ Q) ≃ₐ[R ⧸ q] MvPolynomial (Fin r) (R ⧸ q) :=
    AlgEquiv.ofRingEquiv (f := e0) (fun x => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      show e0 (Ideal.quotientMap Q (MvPolynomial.C : R →+* _) le_rfl (Ideal.Quotient.mk q a)) =
        MvPolynomial.C (Ideal.Quotient.mk q a)
      rw [Ideal.quotientMap_mk]
      simp only [e0, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
        RingHom.quotientKerEquivOfSurjective_apply_mk, f, MvPolynomial.map_C])
  have hB : Algebra.trdeg (R ⧸ q) (MvPolynomial (Fin r) R ⧸ Q) = r := by
    rw [e.trdeg_eq, MvPolynomial.trdeg_of_isDomain]
    simp
  have h0K : Algebra.trdeg (R ⧸ q) q.ResidueField = 0 := by
    haveI := IsLocalization.isAlgebraic (R := R ⧸ q) q.ResidueField (nonZeroDivisors (R ⧸ q))
    exact trdeg_eq_zero
  have h0L : Algebra.trdeg (MvPolynomial (Fin r) R ⧸ Q) Q.ResidueField = 0 := by
    haveI := IsLocalization.isAlgebraic (R := MvPolynomial (Fin r) R ⧸ Q) Q.ResidueField
      (nonZeroDivisors _)
    exact trdeg_eq_zero
  have h1 := trdeg_add_eq (R ⧸ q) q.ResidueField (A := Q.ResidueField)
  have h2 := trdeg_add_eq (R ⧸ q) (MvPolynomial (Fin r) R ⧸ Q) (A := Q.ResidueField)
  rw [h0K, zero_add] at h1
  rw [hB, h0L, add_zero] at h2
  exact h1.trans h2.symm

end GlobalTheory.FibreMinimalPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFamilyEqCayleyOfSkewFamily
section
open NumberField Matrix

namespace GlobalTheory

variable {n : ℕ}

theorem cayleyInv_one_sub (X : Matrix (Fin n) (Fin n) ℂ) (hu : IsUnit (X + 1).det) :
    1 - (X - 1) * (X + 1)⁻¹ = (2:ℂ) • (X + 1)⁻¹ := by
  have h1 : (X + 1) * (X + 1)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have e : (X + 1) - (X - 1) = (1 : Matrix (Fin n) (Fin n) ℂ) + 1 := by abel
  calc 1 - (X - 1) * (X + 1)⁻¹ = (X + 1) * (X + 1)⁻¹ - (X - 1) * (X + 1)⁻¹ := by rw [h1]
    _ = ((X + 1) - (X - 1)) * (X + 1)⁻¹ := by rw [← Matrix.sub_mul]
    _ = (2:ℂ) • (X + 1)⁻¹ := by rw [e, add_mul, one_mul, two_smul]

theorem cayleyInv_one_add (X : Matrix (Fin n) (Fin n) ℂ) (hu : IsUnit (X + 1).det) :
    1 + (X - 1) * (X + 1)⁻¹ = X * ((2:ℂ) • (X + 1)⁻¹) := by
  have h1 : (X + 1) * (X + 1)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have e : (X + 1) + (X - 1) = X + X := by abel
  calc 1 + (X - 1) * (X + 1)⁻¹ = (X + 1) * (X + 1)⁻¹ + (X - 1) * (X + 1)⁻¹ := by rw [h1]
    _ = (X + X) * (X + 1)⁻¹ := by rw [← add_mul, e]
    _ = X * ((2:ℂ) • (X + 1)⁻¹) := by rw [mul_smul_comm, two_smul, add_mul]

theorem cayleyInv_det_one_sub (X : Matrix (Fin n) (Fin n) ℂ) (hu : IsUnit (X + 1).det) :
    IsUnit (1 - (X - 1) * (X + 1)⁻¹).det := by
  rw [cayleyInv_one_sub _ hu, isUnit_iff_ne_zero]
  intro h0
  have h2 : ((2:ℂ) • (X + 1)⁻¹ * (X + 1)).det = (2:ℂ) ^ n := by
    rw [smul_mul_assoc, nonsing_inv_mul _ hu, det_smul, det_one, mul_one, Fintype.card_fin]
  rw [det_mul, h0, zero_mul] at h2
  exact (pow_ne_zero n two_ne_zero) h2.symm

theorem cayleyInv_skew (X Z : Matrix (Fin n) (Fin n) ℂ) (hXZ : X * Zᵀ = 1)
    (hX : IsUnit (X + 1).det) (hZ : IsUnit (Z + 1).det) :
    (Z - 1) * (Z + 1)⁻¹ = -((X - 1) * (X + 1)⁻¹)ᵀ := by
  have hZX : Zᵀ * X = 1 := mul_eq_one_comm.mp hXZ
  have hAZ : Xᵀ * Z = 1 := by
    simpa [transpose_mul, transpose_transpose, transpose_one] using congrArg Matrix.transpose hZX
  have hA : IsUnit (Xᵀ + 1).det := by
    rw [show Xᵀ + 1 = (X + 1)ᵀ by rw [transpose_add, transpose_one], det_transpose]; exact hX
  have key : (Xᵀ + 1) * (Z - 1) = -((Xᵀ - 1) * (Z + 1)) := by
    simp only [mul_sub, mul_add, sub_mul, add_mul, mul_one, one_mul, hAZ]; abel
  rw [transpose_mul, transpose_nonsing_inv, transpose_add, transpose_sub, transpose_one]
  calc (Z - 1) * (Z + 1)⁻¹ = (Xᵀ + 1)⁻¹ * ((Xᵀ + 1) * (Z - 1)) * (Z + 1)⁻¹ := by
        rw [← Matrix.mul_assoc, nonsing_inv_mul _ hA, Matrix.one_mul]
    _ = (Xᵀ + 1)⁻¹ * (-((Xᵀ - 1) * (Z + 1))) * (Z + 1)⁻¹ := by rw [key]
    _ = -((Xᵀ + 1)⁻¹ * (Xᵀ - 1)) := by
        rw [mul_neg, neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hZ,
          Matrix.mul_one]

theorem unitary_isCayley_of_det_ne_zero : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ)
    (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ),
    (∀ σ, X σ * (X (ComplexEmbedding.conjugate σ))ᵀ = 1) → (∀ σ, (1 + X σ).det ≠ 0) →
    ∃ Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, (∀ σ, Y (ComplexEmbedding.conjugate σ) = -(Y σ)ᵀ) ∧
      (∀ σ, (1 - Y σ).det ≠ 0) ∧ ∀ σ, (1 + Y σ) * (1 - Y σ)⁻¹ = X σ := by
  intro L _ _ n X hX hdet
  have hu : ∀ σ, IsUnit (X σ + 1).det := fun σ => by
    rw [add_comm]; exact isUnit_iff_ne_zero.mpr (hdet σ)
  refine ⟨fun σ => (X σ - 1) * (X σ + 1)⁻¹, fun σ => ?_, fun σ => ?_, fun σ => ?_⟩
  · exact cayleyInv_skew (X σ) (X (ComplexEmbedding.conjugate σ)) (hX σ) (hu σ) (hu _)
  · exact isUnit_iff_ne_zero.mp (cayleyInv_det_one_sub (X σ) (hu σ))
  · show (1 + (X σ - 1) * (X σ + 1)⁻¹) * (1 - (X σ - 1) * (X σ + 1)⁻¹)⁻¹ = X σ
    have hY := cayleyInv_det_one_sub (X σ) (hu σ)
    rw [cayleyInv_one_add _ (hu σ), ← cayleyInv_one_sub _ (hu σ), Matrix.mul_assoc,
      mul_nonsing_inv _ hY, Matrix.mul_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitriangularInductionTransvection
section
open Matrix

namespace GlobalTheory

theorem mul_transvection_apply' {n : ℕ} (a b : Fin n) (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n) :
    (M * transvection a b c) x y = M x y + if y = b then M x a * c else 0 := by
  rw [transvection, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  by_cases hy : y = b
  · subst hy; simp [Matrix.mul_apply, single_apply]
  · simp [Matrix.mul_apply, single_apply, hy, Ne.symm hy]

theorem unitriangular_induction_transvection :
    ∀ (n : ℕ) (P : GL (Fin n) ℂ → Prop), P 1 → (∀ A B, P A → P B → P (A * B)) →
      (∀ (i j : Fin n), i < j → ∀ (s : ℂ) (B : GL (Fin n) ℂ), B.val = transvection i j s → P B) →
      ∀ U : GL (Fin n) ℂ, U.val.BlockTriangular id → (∀ i, U.val i i = 1) → P U := by
  intro n P h1 hmul htr
  let S : GL (Fin n) ℂ → Finset (Fin n × Fin n) := fun U =>
    Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ U.val p.1 p.2 ≠ 0)
  suffices H : ∀ k, ∀ U : GL (Fin n) ℂ, U.val.BlockTriangular id → (∀ i, U.val i i = 1) →
      (S U).card = k → P U from fun U hU hd => H _ U hU hd rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro U hU hd hk
  rcases (S U).eq_empty_or_nonempty with hS | hne
  · have : U = 1 := by
      apply Units.ext
      ext i j
      simp only [Units.val_one, Matrix.one_apply]
      rcases lt_trichotomy i j with hij | hij | hij
      · rw [if_neg hij.ne]
        by_contra h
        have : (i, j) ∈ S U := by simp [S, hij, h]
        rw [hS] at this; simp at this
      · subst hij; simp [hd]
      · rw [if_neg hij.ne']
        exact hU hij
    rw [this]; exact h1
  · obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image (S U) (fun p => p.2) hne
    obtain ⟨a, b⟩ := p
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hab, hs⟩ := hp
    set s := U.val a b with hsdef
    have col : ∀ x, U.val x a = if x = a then 1 else 0 := by
      intro x
      split_ifs with hx
      · subst hx; exact hd x
      · rcases lt_trichotomy x a with hxa | hxa | hxa
        · by_contra h
          have hm := hmin (x, a) (by simp [S, hxa, h])
          simp at hm
          exact absurd (lt_of_le_of_lt hm hab) (lt_irrefl _)
        · exact absurd hxa hx
        · exact hU hxa
    let T : ℂ → GL (Fin n) ℂ := fun c =>
      ⟨transvection a b c, transvection a b (-c),
        by rw [transvection_mul_transvection_same _ _ hab.ne]; simp,
        by rw [transvection_mul_transvection_same _ _ hab.ne]; simp⟩
    let U' := U * T (-s)
    have ent : ∀ x y, U'.val x y = U.val x y + if y = b ∧ x = a then -s else 0 := by
      intro x y
      show (U.val * transvection a b (-s)) x y = _
      rw [mul_transvection_apply', col]
      by_cases hy : y = b <;> by_cases hx : x = a <;> simp [hy, hx]
    have hU' : U'.val.BlockTriangular id := by
      intro x y hxy
      rw [ent, hU hxy]
      simp only [id] at hxy
      rw [if_neg]; · simp
      rintro ⟨rfl, rfl⟩
      exact absurd (hab.trans hxy) (lt_irrefl _)
    have hd' : ∀ i, U'.val i i = 1 := by
      intro i
      rw [ent, hd]
      rw [if_neg]; · simp
      rintro ⟨rfl, h⟩
      exact hab.ne h.symm
    have hlt : (S U').card < k := by
      rw [← hk]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨(a, b), ?_, ?_⟩
        · simpa [S, hab] using hs
        · simp [S, ent, hsdef]
      · intro q hq
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        refine ⟨hq.1, ?_⟩
        by_cases hqe : q.2 = b ∧ q.1 = a
        · obtain ⟨q1, q2⟩ := q
          simp only at hqe
          obtain ⟨rfl, rfl⟩ := hqe
          exact hs
        · have := hq.2
          rw [ent, if_neg hqe, add_zero] at this
          exact this
    have PU' : P U' := ih _ hlt U' hU' hd' rfl
    have PT : P (T s) := htr a b hab s (T s) rfl
    have hUeq : U = U' * T s := by
      apply Units.ext
      show U.val = U.val * transvection a b (-s) * transvection a b s
      rw [mul_assoc, transvection_mul_transvection_same _ _ hab.ne]
      simp
    rw [hUeq]
    exact hmul _ _ PU' PT

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperTriangularMul
section
namespace GlobalTheory.UpperTriangularMul

theorem upperTriangular_mul :
    ∀ {n : ℕ} {R : Type} [inst : CommRing R] {M N : Matrix (Fin n) (Fin n) R},
      (∀ (a i : Fin n), i < a → M a i = (0 : R)) →
      (∀ (a i : Fin n), i < a → N a i = (0 : R)) →
      (∀ (a i : Fin n), i < a → (M * N) a i = (0 : R)) ∧
        ∀ (i : Fin n), (M * N) i i = M i i * N i i := by
  intro n R _ M N hM hN
  refine ⟨fun a i hia => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases lt_or_ge j a with h | h
    · rw [hM a j h, zero_mul]
    · rw [hN j i (lt_of_lt_of_le hia h), mul_zero]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hM i j h, zero_mul]
    · rw [hN j i h, mul_zero]

end GlobalTheory.UpperTriangularMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowSubPowLe
section
universe u_1 u_2

namespace GlobalTheory.ValuationPowSubPow

theorem valuation_pow_sub_pow_le {K : Type u_1} {Γ : Type u_2} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) {a b : K}
    (ha : w a ≤ 1) (hb : w b ≤ 1) (m : ℕ) : w (a ^ m - b ^ m) ≤ w (a - b) := by
  induction m with
  | zero => simp
  | succ n ih =>
    have h : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + b ^ n * (a - b) := by ring
    rw [h]
    refine w.map_add_le ?_ ?_
    · rw [map_mul]
      exact (mul_le_of_le_one_left' ha).trans ih
    · rw [map_mul, map_pow]
      exact mul_le_of_le_one_left' (pow_le_one' hb n)

end GlobalTheory.ValuationPowSubPow
end

