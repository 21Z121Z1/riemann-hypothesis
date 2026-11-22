import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0077
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0051
import ReciprocityTheory.GaloisValuations.Global
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0074
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0059
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0094
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0090
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0078
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0079
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulStarEqOfNormOneUnramifiedQuadratic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexEmbeddingFractionFieldFiniteOverCdvStatement
section
open NumberField Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complex_embedding_fractionField_finite_over_cdvr : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T T' : CDVR) (g : T.V →+* T'.V), Function.Injective g → g.Finite → Countable (IsLocalRing.ResidueField T.V) → ∀ io : K →+* T'.Fr, ∃ ι : T'.Fr →+* ℂ, ι.comp io = σ := by
  first | exact @GlobalTheory.ComplexEmbedding.exists_embedding_fractionField_of_finite | exact GlobalTheory.ComplexEmbedding.exists_embedding_fractionField_of_finite | (intros; apply GlobalTheory.ComplexEmbedding.exists_embedding_fractionField_of_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicCrossingFieldDecidingFrobenius
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.ChebCross

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]

theorem autToPow_eq_iff {m : ℕ} [NeZero m] {ζ : Ω} (hζ : IsPrimitiveRoot ζ m) (f : Ω ≃ₐ[F] Ω)
    (j : (ZMod m)ˣ) : hζ.autToPow F f = j ↔ f ζ = ζ ^ (j : ZMod m).val := by
  constructor
  · rintro rfl
    exact (hζ.autToPow_spec F f).symm
  · intro h
    rw [← hζ.autToPow_spec F f] at h
    have := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h
    exact Units.ext (ZMod.val_injective m this)

theorem exists_fixing [CharZero Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω) {m : ℕ}
    [NeZero m] {ζ : Ω} (hζ : IsPrimitiveRoot ζ m) (hirr : Irreducible (cyclotomic m L))
    (j : (ZMod m)ˣ) : ∃ u : Ω ≃ₐ[F] Ω, u ∈ L.fixingSubgroup ∧ hζ.autToPow F u = j := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := F) L
  haveI : IsAlgClosure L Ω := ⟨inferInstance, inferInstance⟩
  haveI : CharZero L := (algebraMap L Ω).charZero
  have hj : IsPrimitiveRoot (ζ ^ (j : ZMod m).val) m :=
    hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime j)
  have h1 : minpoly L (ζ ^ (j : ZMod m).val) = minpoly L ζ := by
    rw [← hζ.minpoly_eq_cyclotomic_of_irreducible hirr,
      ← hj.minpoly_eq_cyclotomic_of_irreducible hirr]
  obtain ⟨u, hu⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := L) Ω).1 h1
  refine ⟨u.restrictScalars F, ?_, ?_⟩
  · rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact u.commutes ⟨x, hx⟩
  · rw [autToPow_eq_iff]
    exact hu

theorem irreducible_of_onto [CharZero Ω] (Z : IntermediateField F Ω) {m : ℕ}
    [NeZero m] {ζ : Ω} (hζ : IsPrimitiveRoot ζ m)
    (h : ∀ j : (ZMod m)ˣ, ∃ u : Ω ≃ₐ[F] Ω, u ∈ Z.fixingSubgroup ∧ hζ.autToPow F u = j) :
    Irreducible (cyclotomic m Z) := by
  classical
  haveI : CharZero Z := (algebraMap Z Ω).charZero
  have hm : 0 < m := NeZero.pos m
  have h0 : aeval ζ (cyclotomic m Z) = 0 := by
    rw [aeval_def, ← eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hm
  have hint : IsIntegral Z ζ := ⟨_, cyclotomic.monic m Z, h0⟩
  have hdvd := minpoly.dvd Z ζ h0
  have hsub : primitiveRoots m Ω ⊆ ((minpoly Z ζ).aroots Ω).toFinset := by
    intro μ hμ
    rw [mem_primitiveRoots hm] at hμ
    obtain ⟨i, hi, hic, rfl⟩ := (hζ.isPrimitiveRoot_iff).1 hμ
    obtain ⟨u, hu, hj⟩ := h (ZMod.unitOfCoprime i hic)
    rw [autToPow_eq_iff, ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt hi] at hj
    rw [Multiset.mem_toFinset, mem_aroots]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    let v : Ω ≃ₐ[Z] Ω := Z.fixingSubgroupEquiv ⟨u, hu⟩
    have hv : v ζ = ζ ^ i := hj
    rw [← hv, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hdeg : (cyclotomic m Z).natDegree ≤ (minpoly Z ζ).natDegree := by
    rw [natDegree_cyclotomic, ← hζ.card_primitiveRoots]
    refine (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans ?_)
    refine (card_roots' _).trans ?_
    exact natDegree_map_le
  have := eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic m Z) hdvd hdeg
  rw [this]
  exact minpoly.irreducible hint

theorem exists_pow_eq_on (M : IntermediateField F Ω) [FiniteDimensional F M] [IsGalois F M]
    (h σ : Ω ≃ₐ[F] Ω)
    (hσ : σ ∈ (M ⊓ IntermediateField.fixedField (Subgroup.zpowers h)).fixingSubgroup) :
    ∃ k : ℕ, ∀ x ∈ M, σ x = (h ^ k) x := by
  let ρ := AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) M
  have hρ : ∀ (f : Ω ≃ₐ[F] Ω) (x : M), ((ρ f x : M) : Ω) = f x := fun f x =>
    AlgEquiv.restrictNormal_commutes f M x
  have h1 : ρ σ ∈ Subgroup.zpowers (ρ h) := by
    rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers (ρ h)),
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    apply Subtype.ext
    rw [hρ]
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    refine hσ _ ⟨x.2, ?_⟩
    change (x : Ω) ∈ IntermediateField.fixedField (Subgroup.zpowers h)
    rw [IntermediateField.mem_fixedField_iff]
    rintro f ⟨n, rfl⟩
    have := hx (ρ (h ^ n)) ⟨n, by simp⟩
    rw [← hρ, this]
  rw [← mem_powers_iff_mem_zpowers] at h1
  obtain ⟨k, hk⟩ := h1
  refine ⟨k, fun x hx => ?_⟩
  have := hρ σ ⟨x, hx⟩
  rw [← hk] at this
  simp only [← map_pow] at this
  rw [hρ] at this
  exact this.symm

theorem cross : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (L : IntermediateField F Ω) [FiniteDimensional F L] [IsGalois F L] (g : G F Ω) (m : ℕ), m.Prime → Module.finrank F L ∣ m - 1 → Irreducible (cyclotomic m L) → ∃ (Z : IntermediateField F Ω) (τ : (ZMod m)ˣ), FiniteDimensional F Z ∧ Irreducible (cyclotomic m Z) ∧ ∀ σ : G F Ω, σ ∈ Z.fixingSubgroup → (∀ ζ : Ω, ζ ^ m = 1 → σ ζ = ζ ^ (τ : ZMod m).val) → σ * g⁻¹ ∈ L.fixingSubgroup := by
  intro F Ω _ _ _ _ _ L _ _ g m hm hdiv hirr
  haveI : Fact m.Prime := ⟨hm⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := (ZMod m)ˣ)
  obtain ⟨u, hu, hu'⟩ := exists_fixing L hζ hirr (τ * (hζ.autToPow F g)⁻¹)
  set h := u * g with hh
  have hχ : hζ.autToPow F h = τ := by rw [hh, map_mul, hu']; simp
  haveI : IsCyclotomicExtension {m} F (IntermediateField.adjoin F {ζ}) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension F
  haveI : FiniteDimensional F (IntermediateField.adjoin F {ζ}) :=
    IsCyclotomicExtension.finiteDimensional {m} F _
  haveI : IsGalois F (IntermediateField.adjoin F {ζ}) := IsCyclotomicExtension.isGalois {m} F _
  let M : IntermediateField F Ω := L ⊔ IntermediateField.adjoin F {ζ}
  haveI : FiniteDimensional F M := IntermediateField.finiteDimensional_sup _ _
  haveI : IsGalois F M := { }
  have hζM : ζ ∈ M := (le_sup_right : _ ≤ M) (IntermediateField.mem_adjoin_simple_self F ζ)
  refine ⟨M ⊓ IntermediateField.fixedField (Subgroup.zpowers h), τ, ?_, ?_, ?_⟩
  · exact Module.Finite.of_injective
      (IntermediateField.inclusion (inf_le_left : _ ≤ M)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  · refine irreducible_of_onto _ hζ fun j => ?_
    obtain ⟨n, rfl⟩ := hτ j
    refine ⟨h ^ n, ?_, by simp [hχ]⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact (IntermediateField.mem_fixedField_iff _ _).1 hx.2 _ ⟨n, rfl⟩
  · intro σ hσ hσζ
    obtain ⟨k, hk⟩ := exists_pow_eq_on M h σ hσ
    have h1 : hζ.autToPow F (h ^ k) = τ := by
      rw [autToPow_eq_iff, ← hk ζ hζM]
      exact hσζ ζ hζ.pow_eq_one
    rw [map_pow, hχ] at h1
    have hord : orderOf τ = m - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hτ, Nat.card_eq_fintype_card, ZMod.card_units]
    have hmod : k ≡ 1 [MOD m - 1] := by
      rw [← hord, ← pow_eq_pow_iff_modEq, h1, pow_one]
    let ρ := AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) L
    have hρ : ∀ (f : Ω ≃ₐ[F] Ω) (x : L), ((ρ f x : L) : Ω) = f x := fun f x =>
      AlgEquiv.restrictNormal_commutes f L x
    have h2 : ρ σ = ρ (h ^ k) := by
      ext x
      rw [hρ, hρ]
      exact hk _ ((le_sup_left : L ≤ M) x.2)
    have h3 : ρ h ^ k = ρ h := by
      conv_rhs => rw [← pow_one (ρ h)]
      rw [pow_eq_pow_iff_modEq]
      refine hmod.of_dvd (dvd_trans ?_ hdiv)
      rw [← IsGalois.card_aut_eq_finrank]
      exact orderOf_dvd_natCard _
    have h4 : ρ u = 1 := by
      rw [← IntermediateField.restrictNormalHom_ker] at hu
      exact hu
    rw [← IntermediateField.restrictNormalHom_ker]
    change ρ (σ * g⁻¹) = 1
    rw [map_mul, h2, map_pow, h3, hh, map_mul, h4, map_inv]
    simp

end GlobalTheory.ChebCross
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleHermitianPairIsGenCompanion
section
open Polynomial Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR

theorem charpoly_companion {k : Type} [Field k] {r : ℕ} (p : Fin r → k) :
    (companion p).charpoly = X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) := by
  set P : k[X] := X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) with hP
  have hlt : (∑ i, C (p i) * X ^ (i : ℕ) : k[X]).degree < r := degree_sum_fin_lt p
  have hm : P.Monic := monic_X_pow_add hlt
  have hd : P.natDegree = r := by
    have : P.degree = r := by
      rw [hP, degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
    exact natDegree_eq_of_degree_eq_some this
  let pb := AdjoinRoot.powerBasis' hm
  have hdim : pb.dim = r := hd
  let b : Module.Basis (Fin r) k (AdjoinRoot P) := pb.basis.reindex (finCongr hdim)
  have hb : ∀ i : Fin r, b i = AdjoinRoot.root P ^ (i : ℕ) := by
    intro i
    simp only [b, Module.Basis.reindex_apply, pb.basis_eq_pow]
    rfl
  have hroot : AdjoinRoot.root P ^ r = ∑ i, (- p i) • b i := by
    have h0 := AdjoinRoot.aeval_eq (f := P) P
    rw [AdjoinRoot.mk_self] at h0
    have h2 : aeval (AdjoinRoot.root P) (X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) : k[X]) = 0 := h0
    simp only [map_add, map_pow, map_sum, map_mul, aeval_X, aeval_C] at h2
    rw [eq_neg_of_add_eq_zero_left h2, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb, neg_smul, Algebra.smul_def]
  have hmat : companion p = Algebra.leftMulMatrix b (AdjoinRoot.root P) := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, hb, ← pow_succ']
    simp only [companion, Matrix.of_apply]
    by_cases hj : (j : ℕ) + 1 = r
    · rw [if_pos hj, hj, hroot, ← b.equivFun_symm_apply, ← b.equivFun_apply, LinearEquiv.apply_symm_apply]
    · rw [if_neg hj]
      have hlt' : (j : ℕ) + 1 < r := lt_of_le_of_ne j.2 hj
      have : AdjoinRoot.root P ^ ((j : ℕ) + 1) = b ⟨(j : ℕ) + 1, hlt'⟩ := by rw [hb]
      rw [this, b.repr_self, Finsupp.single_apply]
      by_cases hi : (i : ℕ) = (j : ℕ) + 1
      · rw [if_pos hi, if_pos (Fin.ext hi.symm)]
      · rw [if_neg hi, if_neg (fun h => hi (congrArg Fin.val h).symm)]
  have hP0 : P ≠ 0 := hm.ne_zero
  haveI : Module.Finite k (AdjoinRoot P) := pb.finite
  rw [hmat, Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, ← LinearMap.charpoly_toMatrix _ pb.basis,
    ← Algebra.leftMulMatrix_apply]
  have hg : pb.gen = AdjoinRoot.root P := rfl
  rw [← hg, charpoly_leftMulMatrix, hg, AdjoinRoot.minpoly_root hP0, hm.leadingCoeff, inv_one, C_1, mul_one]

theorem exists_et_isGen_companion : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (p : Fin r → F),
    (companion p).charpoly.Separable → ∃ (A : Et F E) (τ : A.K), A.IsGen τ p := by
  intro F E _ _ _ _ _ r p hs
  rw [charpoly_companion] at hs
  exact EtExist.exists_isGen F E r p hs

end GlobalTheory.JR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusCompatibleLiftStatement
section
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_compatible_wittVector_lift : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (φ : A →+* A), (∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) → (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) → ∀ (O : Type) [CommRing O] [CharP O l] (f : A →+* O), ∃ F : A →+* WittVector l O, (∀ a, (F a).coeff 0 = f a) ∧ ∀ a, F (φ a) = WittVector.frobenius (F a) := by
  first | exact @GlobalTheory.DworkLift.exists_frobenius_compatible_lift | exact GlobalTheory.DworkLift.exists_frobenius_compatible_lift | (intros; apply GlobalTheory.DworkLift.exists_frobenius_compatible_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlConjugateLastBasisNormalFormOfNeZeroStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glConjugate_lastBasisNormalForm_of_ne_zero : ∀ (k : Type) [Field k] (r : ℕ) (a : Inv (r + 1) k), a.2.1 0 ≠ 0 → ∃ (g : GL (Fin (r + 1)) k) (Z : Gl r k), act g (sec a) = GlobalTheory.JR.Step.lift Z (a.2.1 0) a.2.2 := by
  first | exact @GlobalTheory.JR.Step.glNormal_of_ne_zero | exact GlobalTheory.JR.Step.glNormal_of_ne_zero | (intros; apply GlobalTheory.JR.Step.glNormal_of_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHyperplaneResidueOutsideTranslatesStatement
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hyperplane_residue_outside_translates : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) O, (¬ ∃ (g : GL (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), x.map (algebraMap O K) * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K)) → ∃ a : Fin r → IsLocalRing.ResidueField O, a ≠ 0 ∧ ∀ g : GL (Fin r) (IsLocalRing.ResidueField O), (∀ v, a ⬝ᵥ v = 0 → (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).mulVec v = v) → ∀ L : Matrix (Fin r) (Fin r) O, L.map (IsLocalRing.residue O) = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) → ∃ h : GL (Fin r ⊕ Fin t) O, (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl i) (Sum.inl j) - (1 : Matrix (Fin r) (Fin r) O) i j ∈ Ideal.span {ϖ}) ∧ (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr i) (Sum.inl j) ∈ Ideal.span {ϖ}) ∧ (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) * (Matrix.fromBlocks L 0 0 (1 : Matrix (Fin t) (Fin t) O) * x) = x := by
  first | exact @GlobalTheory.gen_type_core | exact GlobalTheory.gen_type_core | (intros; apply GlobalTheory.gen_type_core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentStarEqOneSubOfNotIsField
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp

theorem exists_idempotent_of_not_isField : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → ¬ IsField A.L → ∃ e : A.L, e * e = e ∧ star e = 1 - e := by
  intro F E _ _ _ _ _ A hK hL
  obtain ⟨-, hinj, hN, hT, hnd⟩ := Et.quadratic_structure F E A
  have hnt : ∃ x y : A.L, x ≠ y := by
    obtain ⟨x, y, hxy⟩ := hK.exists_pair_ne
    exact ⟨_, _, hinj.ne hxy⟩
  have hy : ∃ y : A.L, y ≠ 0 ∧ ∀ b, y * b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hL ⟨hnt, mul_comm, fun {a} ha => hcon a ha⟩
  obtain ⟨y, hy0, hyu⟩ := hy
  have hz : ∃ z, Algebra.trace A.K A.L (star y * z) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy0 (hnd y hcon)
  obtain ⟨z, hz⟩ := hz
  obtain ⟨s, hs⟩ := hK.mul_inv_cancel hz
  have hn : y * star y = 0 := by
    by_contra hne
    have h1 : A.NL y ≠ 0 := by
      intro h0
      apply hne
      rw [← hN, h0, map_zero]
    obtain ⟨n, hn⟩ := hK.mul_inv_cancel h1
    apply hyu (star y * algebraMap A.K A.L n)
    rw [← mul_assoc, ← hN, ← map_mul, hn, map_one]
  have hs' := congrArg (algebraMap A.K A.L) hs
  rw [map_mul, hT, map_one, star_mul', star_star] at hs'
  have hst : star (star y * z * algebraMap A.K A.L s) = y * star z * algebraMap A.K A.L s := by
    rw [star_mul', star_mul', star_star, A.star_K]
  refine ⟨star y * z * algebraMap A.K A.L s, ?_, ?_⟩
  · linear_combination (star y * z * algebraMap A.K A.L s) * hs'
      - (z * star z * algebraMap A.K A.L s ^ 2) * hn
  · rw [hst]
    linear_combination hs'

end GlobalTheory.JR.Hyp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerSpanningFamilyOfUnramifiedExt
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma IsDedekindDomain IsLocalRing

variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}

theorem valuation_map_eq_of_unr (hU : IsUnrExt K K' d φ) (x : K.E) :
    (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E (φ x) =
      (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x := by
  by_cases hx : x = 0
  · simp [hx]
  have h := hU.2.2.1 x
  unfold val at h
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x ≠ 0 := by simpa using hx
  have h0' : (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E (φ x) ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h0, ← WithZero.exp_log h0']
  congr 1
  omega

theorem exists_intMap_of_unr (hU : IsUnrExt K K' d φ) :
    ∃ ψ : K.O →+* K'.O, ∀ a, algebraMap K'.O K'.E (ψ a) = φ (algebraMap K.O K.E a) := by
  choose f hf using exists_int_image hU
  have inj := IsFractionRing.injective K'.O K'.E
  let ψ : K.O →+* K'.O :=
    { toFun := f, map_one' := inj (by simp only [hf, map_one]),
      map_mul' := fun a b => inj (by simp only [hf, map_mul]),
      map_zero' := inj (by simp only [hf, map_zero]),
      map_add' := fun a b => inj (by simp only [hf, map_add]) }
  exact ⟨ψ, hf⟩

theorem exists_int_basis_of_unr (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ) :
    ∃ u : Fin d → K'.O, ∀ y : K'.O, ∃ a : Fin d → K.O,
      algebraMap K'.O K'.E y = ∑ i, φ (algebraMap K.O K.E (a i)) * algebraMap K'.O K'.E (u i) := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_intMap_of_unr hU
  have hv := valuation_map_eq_of_unr hU
  set v := (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E with hvdef
  set v' := (IsDiscreteValuationRing.maximalIdeal K'.O).valuation K'.E with hv'def

  have memK : ∀ a : K.O, a ∈ maximalIdeal K.O ↔ v (algebraMap K.O K.E a) < 1 := fun a =>
    (HeightOneSpectrum.valuation_lt_one_iff_mem (IsDiscreteValuationRing.maximalIdeal K.O) a).symm
  have memK' : ∀ a : K'.O, a ∈ maximalIdeal K'.O ↔ v' (algebraMap K'.O K'.E a) < 1 := fun a =>
    (HeightOneSpectrum.valuation_lt_one_iff_mem (IsDiscreteValuationRing.maximalIdeal K'.O) a).symm
  haveI : IsLocalHom ψ := ⟨fun a ha => by
    by_contra hna
    have h1 : a ∈ maximalIdeal K.O := (mem_maximalIdeal a).2 hna
    have h2 : ψ a ∈ maximalIdeal K'.O := by
      rw [memK', hψ, hv]; exact (memK a).1 h1
    exact (mem_maximalIdeal _).1 h2 ha⟩
  letI : Algebra (ResidueField K.O) (ResidueField K'.O) := (ResidueField.map ψ).toAlgebra
  letI : Fintype (ResidueField K.O) := Fintype.ofFinite _
  letI : Fintype (ResidueField K'.O) := Fintype.ofFinite _
  have hfr : Module.finrank (ResidueField K.O) (ResidueField K'.O) = d := by
    have h1 := Module.card_eq_pow_finrank (K := ResidueField K.O) (V := ResidueField K'.O)
    have c1 : Fintype.card (ResidueField K.O) = K.q ^ 2 := by
      rw [← Nat.card_eq_fintype_card]; exact K.card_res
    have c2 : Fintype.card (ResidueField K'.O) = (K.q ^ 2) ^ d := by
      rw [← Nat.card_eq_fintype_card, K'.card_res, hU.1, ← pow_mul, ← pow_mul, mul_comm]
    have h2 : 2 ≤ K.q ^ 2 := by
      rw [← c1]; exact Fintype.one_lt_card
    rw [c1, c2] at h1
    exact (Nat.pow_right_injective h2 h1).symm
  let b := Module.finBasisOfFinrankEq (ResidueField K.O) (ResidueField K'.O) hfr
  choose u hu using fun i => IsLocalRing.residue_surjective (b i)

  have hres : ∀ c : Fin d → K.O, ∀ j, c j = 1 → ∑ i, ψ (c i) * u i ∉ maximalIdeal K'.O := by
    intro c j hj hmem
    have h0 : residue K'.O (∑ i, ψ (c i) * u i) = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hmem
    rw [map_sum] at h0
    simp only [map_mul, ← ResidueField.map_residue, hu] at h0
    have h1 : ∑ i, residue K.O (c i) • b i = 0 := by
      simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra] using h0
    have := Fintype.linearIndependent_iff.1 b.linearIndependent _ h1 j
    rw [hj, map_one] at this
    exact one_ne_zero this

  set U : Fin d → K'.E := fun i => algebraMap K'.O K'.E (u i) with hUdef

  have key : ∀ e : Fin d → K.E, ∀ j, (∀ i, v (e i) ≤ v (e j)) → e j ≠ 0 →
      v (e j) ≤ v' (∑ i, φ (e i) * U i) := by
    intro e j hmax hj
    have hpos : 0 < v (e j) := zero_lt_iff.2 (by simpa using hj)
    have hc : ∀ i, ∃ a : K.O, algebraMap K.O K.E a = e i / e j := fun i =>
      IsDiscreteValuationRing.exists_lift_of_le_one (by
        rw [map_div₀]; exact (div_le_one₀ hpos).2 (hmax i))
    choose a ha using hc
    have haj : a j = 1 := IsFractionRing.injective K.O K.E (by rw [ha, div_self hj, map_one])
    have h1 := hres a j haj
    rw [memK', not_lt] at h1
    have h2 : algebraMap K'.O K'.E (∑ i, ψ (a i) * u i) = ∑ i, φ (e i / e j) * U i := by
      simp only [map_sum, map_mul, hψ, ha, hUdef]
    have h3 : ∑ i, φ (e i) * U i = φ (e j) * ∑ i, φ (e i / e j) * U i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, ← map_mul, mul_div_cancel₀ _ hj]
    rw [h3, map_mul, hv, ← h2]
    exact le_mul_of_one_le_right' h1
  letI : Algebra K.E K'.E := φ.toAlgebra
  have hsmul : ∀ (x : K.E) (y : K'.E), x • y = φ x * y := fun x y => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have hli : LinearIndependent K.E U := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    by_contra hi
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => v (g i)) ⟨i, Finset.mem_univ i⟩
    have hgi : 0 < v (g i) := zero_lt_iff.2 (by simpa using hi)
    have hgj : g j ≠ 0 := by
      intro h0
      have := hj i (Finset.mem_univ i)
      rw [h0, map_zero] at this
      exact absurd this (not_le.2 hgi)
    have := key g j (fun i => hj i (Finset.mem_univ i)) hgj
    simp only [← hsmul] at this
    rw [hg, map_zero] at this
    exact hgj ((map_eq_zero v).1 (le_antisymm this zero_le'))
  have hd : Module.finrank K.E K'.E = d := hU.2.2.2.2
  haveI : Nonempty (Fin d) := by
    have : 0 < d := hfr ▸ Module.finrank_pos
    exact ⟨⟨0, this⟩⟩
  have hspan := hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hd])
  refine ⟨u, fun y => ?_⟩
  have hy : algebraMap K'.O K'.E y ∈ Submodule.span K.E (Set.range U) := hspan ▸ Submodule.mem_top
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun K.E).1 hy
  have hint : ∀ i, v (e i) ≤ 1 := by
    intro i
    by_contra hi
    rw [not_le] at hi
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => v (e i)) ⟨i, Finset.mem_univ i⟩
    have hej : e j ≠ 0 := by
      intro h0
      have := hj i (Finset.mem_univ i)
      rw [h0, map_zero] at this
      exact absurd (lt_of_lt_of_le hi this) (not_lt.2 zero_le')
    have h1 := key e j (fun i => hj i (Finset.mem_univ i)) hej
    simp only [← hsmul] at h1
    rw [he] at h1
    have h2 := HeightOneSpectrum.valuation_le_one (IsDiscreteValuationRing.maximalIdeal K'.O) (K := K'.E) y
    exact absurd (lt_of_lt_of_le hi (le_trans (hj i (Finset.mem_univ i)) (le_trans h1 h2))) (lt_irrefl _)
  choose a ha using fun i => IsDiscreteValuationRing.exists_lift_of_le_one (hint i)
  refine ⟨a, ?_⟩
  rw [← he]
  simp only [hsmul, ha, hUdef]

end GlobalTheory.UnitLemma.Unr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralBasisUnramifiedInvolutionExtStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_basis_unramifiedInvolutionExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d → letI : Algebra K.E K'.E := φ.toAlgebra; ∃ w : Module.Basis (Fin d) K.E K'.E, ∀ z : K'.E, (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔ ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k := by
  first | exact @GlobalTheory.UnitLemma.Unr.IntBasis.intBasis | exact GlobalTheory.UnitLemma.Unr.IntBasis.intBasis | (intros; apply GlobalTheory.UnitLemma.Unr.IntBasis.intBasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralTraceUnitUnramifiedQuadraticStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_trace_unit_unramifiedQuadratic : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) → ∃ u : E, ‖u‖ ≤ 1 ∧ ‖Algebra.trace F E u‖ = 1 := by
  first | exact @GlobalTheory.TraceUnit.exists_trace_unit | exact GlobalTheory.TraceUnit.exists_trace_unit | (intros; apply GlobalTheory.TraceUnit.exists_trace_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocallyConstantCutoffClosedEmbeddingStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_locallyConstant_cutoff_closedEmbedding : ∀ (R S : Type) [Group R] [TopologicalSpace R] [IsTopologicalGroup R] [LocallyCompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [MeasurableSpace S] [BorelSpace S] (i : S →* R), Topology.IsClosedEmbedding i → ∀ (ν : Measure S) [ν.IsHaarMeasure] (Z : Set R), IsCompact Z → ∃ α : R → ℝ, IsLocallyConstant α ∧ HasCompactSupport α ∧ (∀ g, 0 ≤ α g) ∧ ∀ z ∈ Z, ∀ s₀ : S, ∫ s, α (z * i s₀ * i s) ∂ν = 1 := by
  first | exact @GlobalTheory.CutOff.exists_cutoff | exact GlobalTheory.CutOff.exists_cutoff | (intros; apply GlobalTheory.CutOff.exists_cutoff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_star_eq_of_norm_one_unramifiedQuadratic : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (u : F), ‖u‖ = 1 → ∃ v : E, v * star v = algebraMap F E u := by
  first | exact @GlobalTheory.NormUnits.norm_onto_units | exact GlobalTheory.NormUnits.norm_onto_units | (intros; apply GlobalTheory.NormUnits.norm_onto_units <;> assumption)
end

