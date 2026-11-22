import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Derivation.ToSquareZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoCaten
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0021
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0006
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0018

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.CocRel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem cr_fst_mul {K : Type} [CommRing K] {n : ℕ} (M N : Matrix (Fin n) (Fin n) (DualNumber K)) :
    (M * N).map TrivSqZeroExt.fst = M.map TrivSqZeroExt.fst * N.map TrivSqZeroExt.fst :=
  Matrix.map_mul (f := dF K)

private theorem cr_snd_mul {K : Type} [CommRing K] {n : ℕ} (M N : Matrix (Fin n) (Fin n) (DualNumber K)) :
    (M * N).map TrivSqZeroExt.snd =
      M.map TrivSqZeroExt.fst * N.map TrivSqZeroExt.snd + M.map TrivSqZeroExt.snd * N.map TrivSqZeroExt.fst := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [smul_eq_mul, mul_comm]

private theorem cr_alg {K : Type} [CommRing K] {n : ℕ} (A B P Q y y' Ai Bi Pi : Matrix (Fin n) (Fin n) K) (e : K)
    (hA : Ai * A = 1) (hB : B * Bi = 1) (hP : Pi * P = 1) (hP' : P * Pi = 1)
    (h1 : Aᵀ * P * B = e • P)
    (h2 : Aᵀ * P * (y' * B) + (Aᵀ * Q + (y * A)ᵀ * P) * B = e • Q) :
    y' = -(Pi * yᵀ * P) + (B * (Pi * Q) * Bi - Pi * Q) := by
  have hBi : Bi * B = 1 := mul_eq_one_comm.mp hB
  have hAi : A * Ai = 1 := mul_eq_one_comm.mp hA
  have canc : ∀ X : Matrix (Fin n) (Fin n) K, Pi * Aiᵀ * (Aᵀ * P * X * B) * Bi = X := by
    intro X
    simp only [Matrix.mul_assoc]
    rw [hB, Matrix.mul_one, ← Matrix.mul_assoc Aiᵀ Aᵀ, ← Matrix.transpose_mul, hAi, Matrix.transpose_one,
      Matrix.one_mul, ← Matrix.mul_assoc Pi P, hP, Matrix.one_mul]
  have lhs : Aᵀ * P * y' * B = e • Q - Aᵀ * (Q * B) - Aᵀ * (yᵀ * (P * B)) := by
    rw [Matrix.transpose_mul] at h2
    rw [← h2]
    simp only [Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add]
    abel
  have rhs : Aᵀ * P * (-(Pi * yᵀ * P) + (B * (Pi * Q) * Bi - Pi * Q)) * B
      = e • Q - Aᵀ * (Q * B) - Aᵀ * (yᵀ * (P * B)) := by
    have t1 : Aᵀ * P * (Pi * yᵀ * P) * B = Aᵀ * (yᵀ * (P * B)) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P Pi, hP', Matrix.one_mul]
    have t2 : Aᵀ * P * (B * (Pi * Q) * Bi) * B = e • Q := by
      calc Aᵀ * P * (B * (Pi * Q) * Bi) * B = (Aᵀ * P * B) * (Pi * Q) * (Bi * B) := by
            simp only [Matrix.mul_assoc]
        _ = e • Q := by
            rw [h1, hBi, Matrix.mul_one, Matrix.smul_mul, ← Matrix.mul_assoc, hP', Matrix.one_mul]
    have t3 : Aᵀ * P * (Pi * Q) * B = Aᵀ * (Q * B) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P Pi, hP', Matrix.one_mul]
    rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_neg, Matrix.add_mul, Matrix.sub_mul, Matrix.neg_mul, t1, t2, t3]
    abel
  rw [← canc y', ← canc (-(Pi * yᵀ * P) + (B * (Pi * Q) * Bi - Pi * Q)), lhs, rhs]

theorem UpperTheory.V.Ws.Eb.cocRel :
    ∀ {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] {K : Type} [Field K] [Algebra O K] {n : ℕ} (ρ : F.G₀ →* GL (Fin n) K) (y : F.G₀ → Matrix (Fin n) (Fin n) K) (ρ' : F.G₀ →* GL (Fin n) (DualNumber K)) (P' : GL (Fin n) (DualNumber K)), IsTan ρ y ρ' → F.IsForm O n ρ' P' →
        F.IsForm O n ρ (Matrix.GeneralLinearGroup.map (dF K) P') ∧ ∀ R, IsAdExt F ρ (Matrix.GeneralLinearGroup.map (dF K) P') R → ∃ Z, ∀ g, y (F.conj g) = R F.c (y g) + (R (F.conj g) Z - Z) := by
  intro l _ F O _ _ K _ _ n ρ y ρ' P' hT hF
  have hfst : ∀ g, (W.mat ρ' g).map TrivSqZeroExt.fst = W.mat ρ g := by
    intro g; ext i j
    simp only [Matrix.map_apply]
    rw [show (W.mat ρ' g) i j = ((ρ' g : Matrix (Fin n) (Fin n) (DualNumber K)) i j) from rfl, hT g i j]
    rfl
  have hsnd : ∀ g, (W.mat ρ' g).map TrivSqZeroExt.snd = y g * W.mat ρ g := by
    intro g; ext i j
    simp only [Matrix.map_apply]
    rw [show (W.mat ρ' g) i j = ((ρ' g : Matrix (Fin n) (Fin n) (DualNumber K)) i j) from rfl, hT g i j]
    rfl
  have hP : (↑P' : Matrix (Fin n) (Fin n) (DualNumber K)).map TrivSqZeroExt.fst
      = (↑(Matrix.GeneralLinearGroup.map (dF K) P') : Matrix (Fin n) (Fin n) K) := by
    ext i j; rfl
  have hc : ∀ g, ((F.eps O (DualNumber K) g ^ (1 - (n : ℤ)) : (DualNumber K)ˣ) : DualNumber K)
      = (TrivSqZeroExt.inl ((F.eps O K g ^ (1 - (n : ℤ)) : Kˣ) : K) : DualNumber K) := by
    intro g
    have : F.eps O (DualNumber K) g = Units.map (TrivSqZeroExt.inlHom K K : K →* DualNumber K) (F.eps O K g) :=
      Units.ext rfl
    rw [this, ← map_zpow]; rfl
  have hs1 : ∀ (e : K) (M : Matrix (Fin n) (Fin n) (DualNumber K)),
      ((TrivSqZeroExt.inl e : DualNumber K) • M).map TrivSqZeroExt.fst = e • M.map TrivSqZeroExt.fst := by
    intro e M; ext i j; simp
  have hs2 : ∀ (e : K) (M : Matrix (Fin n) (Fin n) (DualNumber K)),
      ((TrivSqZeroExt.inl e : DualNumber K) • M).map TrivSqZeroExt.snd = e • M.map TrivSqZeroExt.snd := by
    intro e M; ext i j; simp
  have part1 : ∀ g, (W.mat ρ g)ᵀ * (↑(Matrix.GeneralLinearGroup.map (dF K) P') : Matrix (Fin n) (Fin n) K)
      * W.mat ρ (F.conj g)
      = ((F.eps O K g ^ (1 - (n : ℤ)) : Kˣ) : K) •
        (↑(Matrix.GeneralLinearGroup.map (dF K) P') : Matrix (Fin n) (Fin n) K) := by
    intro g
    have h := congrArg (fun M => M.map TrivSqZeroExt.fst) (hF g)
    rw [cr_fst_mul, cr_fst_mul] at h
    simp only [Matrix.transpose_map, hfst, hP, hc, hs1] at h
    exact h
  refine ⟨fun g => part1 g, fun R hR => ?_⟩
  refine ⟨(↑(Matrix.GeneralLinearGroup.map (dF K) P')⁻¹ : Matrix (Fin n) (Fin n) K) *
    (↑P' : Matrix (Fin n) (Fin n) (DualNumber K)).map TrivSqZeroExt.snd, fun g => ?_⟩
  have h := congrArg (fun M => M.map TrivSqZeroExt.snd) (hF g)
  rw [cr_snd_mul, cr_fst_mul, cr_snd_mul] at h
  simp only [Matrix.transpose_map, hfst, hsnd, hP, hc, hs2] at h
  rw [hR.c, hR.ad]
  exact cr_alg (A := W.mat ρ g) (B := W.mat ρ (F.conj g)) (Ai := ↑(ρ g)⁻¹) (Bi := ↑(ρ (F.conj g))⁻¹)
    (Pi := ↑(Matrix.GeneralLinearGroup.map (dF K) P')⁻¹) (hA := Units.inv_mul _) (hB := Units.mul_inv _)
    (hP := Units.inv_mul _) (hP' := Units.mul_inv _) (h1 := part1 g) (h2 := h)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.ConjOf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private def dmk {K : Type} [CommRing K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) (DualNumber K) := Matrix.of fun i j => (⟨A i j, B i j⟩ : DualNumber K)

private theorem dmk_mul {K : Type} [CommRing K] {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) K) :
    dmk A B * dmk C D = dmk (A * C) (A * D + B * C) := by
  have hf : ∀ (P Q : Matrix (Fin n) (Fin n) K) i j, TrivSqZeroExt.fst (dmk P Q i j) = P i j := fun _ _ _ _ => rfl
  have hs : ∀ (P Q : Matrix (Fin n) (Fin n) K) i j, TrivSqZeroExt.snd (dmk P Q i j) = Q i j := fun _ _ _ _ => rfl
  ext i j
  · rw [hf, Matrix.mul_apply, TrivSqZeroExt.fst_sum, Matrix.mul_apply]
    simp only [TrivSqZeroExt.fst_mul, hf]
  · rw [hs, Matrix.mul_apply, TrivSqZeroExt.snd_sum, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [TrivSqZeroExt.snd_mul, hf, hs, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]

private theorem dmk_one {K : Type} [CommRing K] {n : ℕ} :
    dmk (1 : Matrix (Fin n) (Fin n) K) 0 = 1 := by
  have hf : ∀ (P Q : Matrix (Fin n) (Fin n) K) i j, TrivSqZeroExt.fst (dmk P Q i j) = P i j := fun _ _ _ _ => rfl
  have hs : ∀ (P Q : Matrix (Fin n) (Fin n) K) i j, TrivSqZeroExt.snd (dmk P Q i j) = Q i j := fun _ _ _ _ => rfl
  ext i j
  · rw [hf, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · rw [hs, Matrix.one_apply, Matrix.zero_apply]
    split_ifs <;> simp

theorem UpperTheory.V.Ws.Eb.conjOf :
    ∀ {K H : Type} [CommRing K] [Group H] {n : ℕ} (ρ : H →* GL (Fin n) K) (y : H → Matrix (Fin n) (Fin n) K) (ρ' : H →* GL (Fin n) (DualNumber K)) (X : Matrix (Fin n) (Fin n) K), IsTan ρ y ρ' → (∀ g, y g = Loc.adGL ρ g X - X) →
        ∃ Q : GL (Fin n) (DualNumber K), ∀ g, ρ' g = Q * W.pushRep (algebraMap K (DualNumber K)) ρ g * Q⁻¹ := by
  intro K H _ _ n ρ y ρ' X hT hy
  unfold IsTan at hT
  have hinv : dmk (1 : Matrix (Fin n) (Fin n) K) (-X) * dmk 1 X = 1 := by
    rw [dmk_mul]
    simp [dmk_one]
  have hinv' : dmk (1 : Matrix (Fin n) (Fin n) K) X * dmk 1 (-X) = 1 := by
    rw [dmk_mul]
    simp [dmk_one]
  refine ⟨⟨dmk 1 (-X), dmk 1 X, hinv, hinv'⟩, fun g => ?_⟩
  have hp : ((W.pushRep (algebraMap K (DualNumber K)) ρ g : GL (Fin n) (DualNumber K)) : Matrix (Fin n) (Fin n) (DualNumber K)) = dmk (ρ g : Matrix (Fin n) (Fin n) K) 0 := by
    ext i j
    · simp [W.pushRep, TrivSqZeroExt.algebraMap_eq_inl]
      rfl
    · simp [W.pushRep, TrivSqZeroExt.algebraMap_eq_inl]
      rfl
  have hyg : y g * (ρ g : Matrix (Fin n) (Fin n) K) = 1 * (ρ g : Matrix (Fin n) (Fin n) K) * X + (1 * 0 + -X * (ρ g : Matrix (Fin n) (Fin n) K)) * 1 := by
    rw [hy g]
    simp only [Loc.adGL, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, sub_mul, mul_assoc, ← Matrix.coe_units_inv, Units.inv_mul, mul_one, one_mul, mul_zero, zero_add, neg_mul, sub_eq_add_neg]
    rw [add_mul, mul_assoc, mul_assoc, Units.inv_mul, mul_one, neg_mul]
  ext i j : 2
  rw [Units.val_mul, Units.val_mul, hp, Units.inv_mk]
  rw [dmk_mul, dmk_mul, hT g i j, ← hyg]
  simp only [one_mul, mul_one]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.CotDer
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Eb.cotDer :
    ∀ (O R : Type) [CommRing O] [IsDomain O] [CharZero O] [CommRing R] [IsLocalRing R] [Algebra O R], Function.Injective (algebraMap O (ResidueField R)) → Algebra.IsAlgebraic O (ResidueField R) →
        ∃ d : Derivation O R (CotangentSpace R), ∀ a : maximalIdeal R, d a = (maximalIdeal R).toCotangent a := by
  intro O R _ _ _ _ _ _ hinj halg
  haveI : FaithfulSMul O (ResidueField R) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  letI : Algebra (FractionRing O) (ResidueField R) := FractionRing.liftAlgebra O _
  haveI := FractionRing.isScalarTower_liftAlgebra O (ResidueField R)
  haveI := halg
  haveI : Algebra.IsAlgebraic (FractionRing O) (ResidueField R) :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective O (FractionRing O))
  haveI : Algebra.FormallyEtale (FractionRing O) (ResidueField R) := Algebra.FormallyEtale.of_isSeparable _ _
  haveI : Algebra.FormallyEtale O (FractionRing O) := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors O)
  haveI : Algebra.FormallyEtale O (ResidueField R) := Algebra.FormallyEtale.comp O (FractionRing O) _
  have hle : maximalIdeal R ^ 2 ≤ maximalIdeal R := Ideal.pow_le_self two_ne_zero
  let g : R ⧸ maximalIdeal R ^ 2 →ₐ[O] ResidueField R := Ideal.Quotient.factorₐ O hle
  have hgmk : ∀ a : R, g (Ideal.Quotient.mk _ a) = residue R a := fun a => rfl
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨a, rfl⟩ := residue_surjective x
    exact ⟨_, hgmk a⟩
  have hker : ∀ x, g x = 0 → x ∈ (maximalIdeal R).cotangentIdeal := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hgmk, residue_eq_zero_iff] at hx
    exact Ideal.mk_mem_cotangentIdeal.mpr hx
  have hnil : IsNilpotent (RingHom.ker (g : R ⧸ maximalIdeal R ^ 2 →+* ResidueField R)) := by
    refine ⟨2, le_bot_iff.mp ?_⟩
    refine (Ideal.pow_right_mono (fun x hx => hker x hx) 2).trans ?_
    rw [Ideal.cotangentIdeal_square]
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id O (ResidueField R)) g hg hnil
  have hs : ∀ x, g (s x) = x := fun x => Algebra.FormallySmooth.liftOfSurjective_apply _ g hg hnil x
  let φ := s.comp (IsScalarTower.toAlgHom O R (ResidueField R))
  have e : (Ideal.Quotient.mkₐ O (maximalIdeal R).cotangentIdeal).comp φ
      = IsScalarTower.toAlgHom O R ((R ⧸ maximalIdeal R ^ 2) ⧸ (maximalIdeal R).cotangentIdeal) := by
    ext r
    show Ideal.Quotient.mk _ (s (algebraMap R (ResidueField R) r))
      = Ideal.Quotient.mk _ (Ideal.Quotient.mk (maximalIdeal R ^ 2) r)
    rw [Ideal.Quotient.eq]
    apply hker
    rw [map_sub, hs, hgmk, ResidueField.algebraMap_eq, sub_self]
  let D := derivationToSquareZeroOfLift (maximalIdeal R).cotangentIdeal
    (Ideal.cotangentIdeal_square _) φ e
  refine ⟨-(((maximalIdeal R).cotangentEquivIdeal.symm :
      (maximalIdeal R).cotangentIdeal →ₗ[R] (maximalIdeal R).Cotangent).compDer D), fun a => ?_⟩
  have hφ : φ a = 0 := by
    show s (algebraMap R (ResidueField R) a) = 0
    rw [ResidueField.algebraMap_eq, (residue_eq_zero_iff _).mpr a.2, map_zero]
  show -((maximalIdeal R).cotangentEquivIdeal.symm (D a)) = _
  rw [neg_eq_iff_eq_neg, ← map_neg, LinearEquiv.symm_apply_eq]
  ext
  simp only [D, derivationToSquareZeroOfLift_apply, hφ, zero_sub, Ideal.cotangentEquivIdeal_apply, map_neg,
    Submodule.coe_neg, Ideal.toCotangent_to_quotient_square]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DblRep
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private def dblMat {K H : Type} [Field K] [TopologicalSpace K] [Group H] [TopologicalSpace H] {n : ℕ}
    (ρ : H →* GL (Fin n) K) (y : H → Matrix (Fin n) (Fin n) K)
    (hy : ∀ g h, y (g * h) = y g + Loc.adGL ρ g (y h)) : H →* Matrix (Fin (n + n)) (Fin (n + n)) K where
  toFun g := Matrix.reindexAlgEquiv K K finSumFinEquiv
    (Matrix.fromBlocks (ρ g : Matrix (Fin n) (Fin n) K) (y g * (ρ g : Matrix (Fin n) (Fin n) K)) 0 (ρ g : Matrix (Fin n) (Fin n) K))
  map_one' := by
    have h1 : y 1 = 0 := by
      have := hy 1 1
      simpa using this
    simp only [map_one, Units.val_one, h1, Matrix.zero_mul, Matrix.fromBlocks_one]
  map_mul' g h := by
    rw [← map_mul, Matrix.fromBlocks_multiply, hy]
    congr 2
    · simp
    · simp only [Loc.adGL, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, map_mul, Units.val_mul,
        Matrix.add_mul, Matrix.mul_assoc, Units.inv_mul_cancel_left]
      exact add_comm _ _
    · simp
    · simp

theorem UpperTheory.V.Ws.Eb.dblRep :
    ∀ {K H : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {n : ℕ} (ρ : H →* GL (Fin n) K), Continuous ρ → ∀ y ∈ Z1 (Loc.adGL ρ),
        ∃ ρ₂ : H →* GL (Fin (n + n)) K, Continuous ρ₂ ∧ (∀ g, (W.mat ρ₂ g).charpoly = (W.mat ρ g).charpoly ^ 2) ∧ ∀ g, ρ₂ g = 1 → y g = 0 := by
  intro K H _ _ _ _ _ _ n ρ hρ y hy
  obtain ⟨hyc, hyco⟩ := hy
  let D := dblMat ρ y hyco
  have hρv : Continuous (fun g => (ρ g : Matrix (Fin n) (Fin n) K)) := Units.continuous_val.comp hρ
  have hblk : Continuous (fun g => Matrix.fromBlocks (ρ g : Matrix (Fin n) (Fin n) K)
      (y g * (ρ g : Matrix (Fin n) (Fin n) K)) 0 (ρ g : Matrix (Fin n) (Fin n) K)) :=
    Continuous.matrix_fromBlocks hρv (hyc.matrix_mul hρv) continuous_const hρv
  have hDc : Continuous (fun g => D g) := by
    have e : (fun g => D g) = fun g => (Matrix.fromBlocks (ρ g : Matrix (Fin n) (Fin n) K)
        (y g * (ρ g : Matrix (Fin n) (Fin n) K)) 0 (ρ g : Matrix (Fin n) (Fin n) K)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := by
      funext g
      rfl
    rw [e]
    exact hblk.matrix_submatrix _ _
  refine ⟨D.toHomUnits, ?_, ?_, ?_⟩
  · refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact hDc
    · have e : (fun g => ((D.toHomUnits g)⁻¹ : GL (Fin (n + n)) K).val) = fun g => D g⁻¹ := by
        funext g
        rw [← map_inv, MonoidHom.coe_toHomUnits]
      rw [e]
      exact hDc.comp continuous_inv
  · intro g
    show (D g).charpoly = ((ρ g : Matrix (Fin n) (Fin n) K)).charpoly ^ 2
    simp only [D, dblMat, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindexAlgEquiv_apply,
      Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₂₁, pow_two]
  · intro g hg
    have h1 : D g = 1 := by
      rw [← MonoidHom.coe_toHomUnits D g, hg, Units.val_one]
    have h2 : Matrix.fromBlocks (ρ g : Matrix (Fin n) (Fin n) K) (y g * (ρ g : Matrix (Fin n) (Fin n) K))
        0 (ρ g : Matrix (Fin n) (Fin n) K) = Matrix.fromBlocks 1 0 0 1 := by
      rw [Matrix.fromBlocks_one]
      apply (Matrix.reindexAlgEquiv K K finSumFinEquiv).injective
      rw [map_one]
      exact h1
    obtain ⟨-, hB, -, -⟩ := Matrix.fromBlocks_inj.mp h2
    calc y g = y g * (ρ g : Matrix (Fin n) (Fin n) K) * ((ρ g)⁻¹ : GL (Fin n) K) := by
          rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = 0 := by rw [hB, Matrix.zero_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DerZero
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Eb.derZero :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (x' : R →ₐ[c.O] DualNumber (PadicAlgCl l)) (S : Set R), (∀ (N : ℕ) (a : R), ∃ b ∈ Algebra.adjoin c.O S, a - b ∈ maximalIdeal R ^ N) → (∀ a ∈ S, (x' a).snd = 0) → ∀ a, (x' a).snd = 0 := by
  intro l _ c R _ _ _ x' S hdense hS a
  have hadj : ∀ b ∈ Algebra.adjoin c.O S, (x' b).snd = 0 := by
    intro b hb
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact hS x hx
    | algebraMap r =>
      rw [AlgHom.commutes]
      first
        | rfl
        | simp [TrivSqZeroExt.algebraMap_eq_inl']
    | add x y _ _ hx hy => rw [map_add, TrivSqZeroExt.snd_add, hx, hy, add_zero]
    | mul x y _ _ hx hy => simp [map_mul, TrivSqZeroExt.snd_mul, hx, hy]
  have hcont := ((coPt c R).2 x').2
  by_contra h
  have hpos : 0 < ‖(x' a).snd‖ := norm_pos_iff.mpr h
  obtain ⟨n, hn⟩ := hcont _ (half_pos hpos)
  obtain ⟨b, hb, hab⟩ := hdense n a
  have key := hn _ hab
  rw [map_sub, TrivSqZeroExt.snd_sub, hadj b hb, sub_zero] at key
  linarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DimLeOfInt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem dim_le_of_int (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A] :
    ringKrullDim A ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R A)) fun _ _ h =>
    Ideal.IsIntegral.comap_lt_comap (R := R) h

theorem UpperTheory.V.Ws.Eb.htLow :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (N : ℕ) (T : Type) [CommRing T] [IsDomain T] [Algebra c.O T] [IsCO c.O T] (f : MvPowerSeries (Fin N) c.O →ₐ[c.O] T), Function.Injective f → (f : MvPowerSeries (Fin N) c.O →+* T).Finite → ∀ x : T →ₐ[c.O] PadicAlgCl l, (N : ℕ∞) ≤ (RingHom.ker x).height := by
  intro l _ c N T _ _ _ _ f hinj hfin x
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1
  haveI : Algebra.IsAlgebraic ℤ_[l] (PadicAlgCl l) :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ_[l]) (K := ℚ_[l])).2 inferInstance
  haveI : Algebra.IsAlgebraic c.O (PadicAlgCl l) :=
    Algebra.IsAlgebraic.extendScalars (R := ℤ_[l]) (UpperTheory.V.Base.dvrFacts l c.O).1
  haveI : FaithfulSMul c.O (PadicAlgCl l) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  haveI := UpperTheory.V.W.exists_algebraicPoint_of_groupDeterminant c.O T (PadicAlgCl l) x
  haveI : (RingHom.ker x).IsPrime := RingHom.ker_isPrime _
  have h1 := UpperTheory.V.Alg.co_caten c.O T (RingHom.ker x)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have h2 := (UpperTheory.V.AlgebraTools.mvPowerSeries_cotInd c.O ϖ hϖ (Fin N)).2.1
  have h3 : ringKrullDim T = ringKrullDim (MvPowerSeries (Fin N) c.O) := by
    letI : Algebra (MvPowerSeries (Fin N) c.O) T := (f : MvPowerSeries (Fin N) c.O →+* T).toAlgebra
    haveI : Module.Finite (MvPowerSeries (Fin N) c.O) T := hfin
    exact ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj
  have h4 : ringKrullDim (T ⧸ RingHom.ker x) ≤ 1 := by
    rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange x).toRingEquiv,
      ← IsDiscreteValuationRing.ringKrullDim_eq_one c.O]
    exact dim_le_of_int c.O x.range
  rw [h3, h2, Fintype.card_fin] at h1
  have h5 : ((N + 1 : ℕ) : WithBot ℕ∞) ≤ ((RingHom.ker x).height : WithBot ℕ∞) + 1 := by
    rw [← h1]; exact add_le_add le_rfl h4
  have h6 : (N : ℕ∞) + 1 ≤ (RingHom.ker x).height + 1 := by exact_mod_cast h5
  exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 h6
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.EbSMul
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private def ebS {K : Type} [CommRing K] {n : ℕ} (X : Matrix (Fin n) (Fin n) (DualNumber K)) :
    Matrix (Fin n) (Fin n) K := Matrix.of fun i j => (X i j).snd

private theorem ebS_mul {K : Type} [CommRing K] {n : ℕ} (X Y : Matrix (Fin n) (Fin n) (DualNumber K)) :
    ebS (X * Y) = X.map (dF K) * ebS Y + ebS X * Y.map (dF K) := by
  ext i j
  simp only [ebS, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.add_apply, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [dF, smul_eq_mul, MulOpposite.smul_eq_mul_unop, mul_comm]

theorem UpperTheory.V.Ws.Eb.tanOf :
    ∀ {K G : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ} (ρ' : G →* GL (Fin n) (DualNumber K)), Continuous ρ' →
        Continuous (W.pushRep (dF K) ρ') ∧ ∃ y ∈ Z1 (Loc.adGL (W.pushRep (dF K) ρ')), IsTan (W.pushRep (dF K) ρ') y ρ' := by
  intro K G _ _ _ _ _ _ n ρ' hρ'
  set ρ := W.pushRep (dF K) ρ' with hρ
  have hdF : Continuous (dF K) := TrivSqZeroExt.continuous_fst
  have hv : Continuous fun g => (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) :=
    Units.continuous_val.comp hρ'
  have hi : Continuous fun g => (↑((ρ' g)⁻¹) : Matrix (Fin n) (Fin n) (DualNumber K)) :=
    Units.continuous_coe_inv.comp hρ'
  have hc : Continuous ρ := by
    rw [Units.continuous_iff]
    exact ⟨hv.matrix_map hdF, hi.matrix_map hdF⟩
  have hci : Continuous fun g => (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K) :=
    Units.continuous_coe_inv.comp hc
  have e : ∀ g, (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)).map (dF K) = (↑(ρ g) : Matrix (Fin n) (Fin n) K) :=
    fun g => rfl
  have hS : Continuous fun g => ebS (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) :=
    continuous_matrix fun i j => TrivSqZeroExt.continuous_snd.comp (hv.matrix_elem i j)
  refine ⟨hc, fun g => ebS (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K),
    ⟨hS.matrix_mul hci, ?_⟩, ?_⟩
  · intro g h
    show ebS (↑(ρ' (g * h)) : Matrix (Fin n) (Fin n) (DualNumber K)) * (↑((ρ (g * h))⁻¹) : Matrix (Fin n) (Fin n) K) =
      ebS (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K) +
        (↑(ρ g) : Matrix (Fin n) (Fin n) K) * (ebS (↑(ρ' h) : Matrix (Fin n) (Fin n) (DualNumber K)) *
          (↑((ρ h)⁻¹) : Matrix (Fin n) (Fin n) K)) * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K)
    rw [map_mul, map_mul, Units.val_mul, ebS_mul, e, e, _root_.mul_inv_rev, Units.val_mul, add_mul]
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
    exact add_comm _ _
  · intro g i j
    show _ = (_, (ebS (↑(ρ' g) : Matrix (Fin n) (Fin n) (DualNumber K)) * (↑((ρ g)⁻¹) : Matrix (Fin n) (Fin n) K) *
      (↑(ρ g) : Matrix (Fin n) (Fin n) K)) i j)
    rw [Units.inv_mul_cancel_right]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.FlagDual
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Ws.Eb.residue_dual {K : Type} [Field K] (x : DualNumber K) :
    residue (DualNumber K) x = ((residue (DualNumber K)).comp (algebraMap K (DualNumber K))) (dF K x) := by
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have e : x - algebraMap K (DualNumber K) (dF K x) = TrivSqZeroExt.inr x.snd := by
    ext <;> simp [dF, TrivSqZeroExt.algebraMap_eq_inl]
  rw [e, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simp

private theorem UpperTheory.V.Ws.Eb.charpoly_lift {A K H : Type} [CommRing A] [CommRing K] [Group H] {n : ℕ} (f : A →+* K)
    (r : H →* GL (Fin n) A) (κ : Fin n → H →* Aˣ) (h : W.HasFlag (W.pushRep f r) fun i => W.pushCh f (κ i))
    (z : MonoidAlgebra A H) :
    (MonoidAlgebra.lift A (Matrix (Fin n) (Fin n) A) H ((Units.coeHom _).comp r) z).charpoly.map f =
      ∏ i, (X - C (f (MonoidAlgebra.lift A A H ((Units.coeHom _).comp (κ i)) z))) := by
  unfold W.HasFlag W.pushRep W.pushCh at h
  obtain ⟨g, hg⟩ := h
  have key : ∀ y : MonoidAlgebra A H,
      (∀ i j : Fin n, j < i → ((g : Matrix (Fin n) (Fin n) K) * f.mapMatrix (MonoidAlgebra.lift A (Matrix (Fin n) (Fin n) A) H ((Units.coeHom _).comp r) y) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i j = 0) ∧
      ∀ i, ((g : Matrix (Fin n) (Fin n) K) * f.mapMatrix (MonoidAlgebra.lift A (Matrix (Fin n) (Fin n) A) H ((Units.coeHom _).comp r) y) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i i = f (MonoidAlgebra.lift A A H ((Units.coeHom _).comp (κ i)) y) := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
      simp only [map_add, mul_add, add_mul, Matrix.add_apply]
      exact ⟨fun i j hij => by rw [hx.1 i j hij, hy.1 i j hij, add_zero], fun i => by rw [hx.2, hy.2]⟩
    | single s a =>
      have e : (g : Matrix (Fin n) (Fin n) K) * f.mapMatrix (MonoidAlgebra.lift A (Matrix (Fin n) (Fin n) A) H ((Units.coeHom _).comp r) (MonoidAlgebra.single s a)) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = f a • ((g * ((GeneralLinearGroup.map f).comp r) s * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [MonoidAlgebra.lift_single]
        have e' : f.mapMatrix (a • ((r s : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)) = f a • ((GeneralLinearGroup.map f (r s) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          ext i j
          simp [GeneralLinearGroup.map]
        simp only [MonoidHom.comp_apply, Units.coeHom_apply, e', Units.val_mul, Matrix.mul_smul, Matrix.smul_mul]
      rw [e]
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · rw [Matrix.smul_apply, (hg s).1 i j hij, smul_zero]
      · rw [Matrix.smul_apply, (hg s).2 i]
        simp [MonoidAlgebra.lift_single]
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_units_conj g, ← Matrix.coe_units_inv]
  simp only [← RingHom.mapMatrix_apply]
  rw [Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => (key z).1 i j hij)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [(key z).2 i]

theorem UpperTheory.V.Ws.Eb.flagDual :
    ∀ {K H : Type} [Field K] [Infinite K] [Group H] {n : ℕ} (ρ' : H →* GL (Fin n) (DualNumber K)) (κ : Fin n → H →* (DualNumber K)ˣ), (Function.Injective fun i => W.pushCh (dF K) (κ i)) →
        W.HasFlag (W.pushRep (dF K) ρ') (fun i => W.pushCh (dF K) (κ i)) → (∀ g : Fin n → H, (List.ofFn fun i => W.mat ρ' (g i) - algebraMap (DualNumber K) _ (κ i (g i) : DualNumber K)).prod = 0) → W.HasFlag ρ' κ := by
  intro K H _ _ _ n ρ' κ hinj hflag hprod
  set φ : K →+* ResidueField (DualNumber K) := (residue (DualNumber K)).comp (algebraMap K (DualNumber K)) with hφ
  have hres : residue (DualNumber K) = φ.comp (dF K) := RingHom.ext fun x => UpperTheory.V.Ws.Eb.residue_dual x
  have hcard : (n : Cardinal) ≤ Cardinal.mk (ResidueField (DualNumber K)) := by
    haveI : Infinite (ResidueField (DualNumber K)) := Infinite.of_injective φ φ.injective
    exact (Cardinal.nat_lt_aleph0 n).le.trans (Cardinal.infinite_iff.mp inferInstance)
  have hinj' : Function.Injective fun i => ((residue (DualNumber K) : DualNumber K →* ResidueField (DualNumber K))).comp ((Units.coeHom (DualNumber K)).comp (κ i)) := by
    intro i j hij
    apply hinj
    ext s
    have hs := DFunLike.congr_fun hij s
    simp only [MonoidHom.comp_apply, Units.coeHom_apply, MonoidHom.coe_coe] at hs
    rw [hres, RingHom.comp_apply, RingHom.comp_apply] at hs
    have := φ.injective hs
    simpa [W.pushCh] using this
  have hchar : ∀ z : MonoidAlgebra (DualNumber K) H,
      Polynomial.map (residue (DualNumber K))
          ((MonoidAlgebra.lift (DualNumber K) (Matrix (Fin n) (Fin n) (DualNumber K)) H ((Units.coeHom _).comp ρ')) z).charpoly =
        ∏ i, (X - C ((residue (DualNumber K)) ((MonoidAlgebra.lift (DualNumber K) (DualNumber K) H ((Units.coeHom _).comp (κ i))) z))) := by
    intro z
    rw [hres, ← Polynomial.map_map, UpperTheory.V.Ws.Eb.charpoly_lift (dF K) ρ' κ hflag z, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.comp_apply]
    rfl
  obtain ⟨z, g, -, -, hg⟩ := AlgebraTools.lemma_L ρ' κ hcard hprod hinj' hchar
  unfold W.HasFlag
  exact ⟨g, hg⟩
end

