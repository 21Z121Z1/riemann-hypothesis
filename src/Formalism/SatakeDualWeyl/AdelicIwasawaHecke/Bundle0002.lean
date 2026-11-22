import Formalism.SatakeDualWeyl.Statement
import Lemmata.NearbyExistence.ExistsNear

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
section
namespace Formalism.UG.P

open Formalism.UG

section Generic

variable {L : Type} [Field L] {n : Type} [Fintype n] [DecidableEq n]

theorem glint_mem_range_of_integral (O : Subring L) (U : GL n L)
    (h1 : (U : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (h2 : ((U⁻¹ : GL n L) : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range) :
    U ∈ (bc (n := n) O.subtype).range := by
  obtain ⟨A, hA⟩ := h1
  obtain ⟨B, hB⟩ := h2
  have inj : Function.Injective (RingHom.mapMatrix (m := n) O.subtype) := by
    intro X Y h
    ext i j
    simpa using congrFun (congrFun h i) j
  have hAB : A * B = 1 := inj (by rw [map_mul, map_one, hA, hB, Units.mul_inv])
  have hBA : B * A = 1 := inj (by rw [map_mul, map_one, hA, hB, Units.inv_mul])
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  ext : 1
  simp only [bc, Units.coe_map]
  exact hA

theorem glint_conj_integral (O : Subring L) (g : GL n L) (c : O)
    (hg : (c : L) • (g : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (hg' : (c : L) • ((g⁻¹ : GL n L) : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (h : GL n O) (hh : redGL (n := n) (Ideal.span {c * c}) h = 1) :
    ((g⁻¹ * bc (n := n) O.subtype h * g : GL n L) : Matrix n n L) ∈
      (RingHom.mapMatrix (m := n) O.subtype).range := by
  have hm : RingHom.mapMatrix (m := n) (Ideal.Quotient.mk (Ideal.span {c * c})) (h : Matrix n n O) =
      RingHom.mapMatrix (m := n) (Ideal.Quotient.mk (Ideal.span {c * c})) 1 := by
    rw [map_one]; exact congrArg Units.val hh
  have hent : ∀ a b, (h : Matrix n n O) a b - (1 : Matrix n n O) a b ∈ Ideal.span {c * c} := by
    intro a b
    rw [← Ideal.Quotient.eq]
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply] using congrFun (congrFun hm a) b
  choose e he using fun a b => Ideal.mem_span_singleton'.1 (hent a b)
  let E : Matrix n n O := Matrix.of e
  have hL : ∀ a b, (((h : Matrix n n O) a b : O) : L) =
      (1 : Matrix n n L) a b + (c : L) * (c : L) * ((e a b : O) : L) := by
    intro a b
    have h1 := he a b
    rw [Matrix.one_apply] at h1 ⊢
    split_ifs at h1 ⊢ with hab
    · have := congrArg Subtype.val h1
      push_cast at this
      linear_combination -this
    · have := congrArg Subtype.val h1
      push_cast at this
      linear_combination -this
  have hkey : ((bc (n := n) O.subtype h : GL n L) : Matrix n n L) =
      1 + ((c : L) * (c : L)) • RingHom.mapMatrix (m := n) O.subtype E := by
    ext a b
    simp only [bc, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      E, Matrix.of_apply, Subring.coe_subtype]
    exact hL a b
  have hcalc : ((g⁻¹ * bc (n := n) O.subtype h * g : GL n L) : Matrix n n L) =
      1 + ((c : L) • ((g⁻¹ : GL n L) : Matrix n n L)) * RingHom.mapMatrix (m := n) O.subtype E *
        ((c : L) • (g : Matrix n n L)) := by
    rw [Units.val_mul, Units.val_mul, hkey, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      ← Units.val_mul, inv_mul_cancel, Units.val_one]
    congr 1
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [hcalc]
  exact add_mem (one_mem _) (mul_mem (mul_mem hg' ⟨E, rfl⟩) hg)

theorem glint_princ_le_map_conj (O : Subring L) (g : GL n L) (c : O)
    (hg : (c : L) • (g : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (hg' : (c : L) • ((g⁻¹ : GL n L) : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range) :
    princ (n := n) O.subtype (Ideal.span {c * c}) ≤
      (GLint n O).map (MulAut.conj g).toMonoidHom := by
  intro k hk
  simp only [princ, congPre] at hk
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hk
  have hh' : redGL (n := n) (Ideal.span {c * c}) h = 1 := by
    simpa only [Subgroup.mem_comap, Subgroup.mem_bot] using hh
  have hh'' : redGL (n := n) (Ideal.span {c * c}) h⁻¹ = 1 := by rw [map_inv, hh', inv_one]
  refine Subgroup.mem_map.2 ⟨g⁻¹ * bc (n := n) O.subtype h * g, ?_, ?_⟩
  · apply glint_mem_range_of_integral
    · exact glint_conj_integral O g c hg hg' h hh'
    · have : (g⁻¹ * bc (n := n) O.subtype h * g)⁻¹ = g⁻¹ * bc (n := n) O.subtype h⁻¹ * g := by
        rw [map_inv]; group
      rw [this]
      exact glint_conj_integral O g c hg hg' h⁻¹ hh''
  · simp [MulAut.conj_apply, mul_assoc]

theorem glint_princ_relIndex_ne_zero (O : Subring L) (I : Ideal O) [Finite (O ⧸ I)] :
    (princ (n := n) O.subtype I).relIndex (bc (n := n) O.subtype).range ≠ 0 := by
  classical
  have : Finite (Matrix n n (O ⧸ I)) := inferInstanceAs (Finite (n → n → O ⧸ I))
  have hN : (redGL (n := n) I).ker.index ≠ 0 := by
    rw [Subgroup.index_ker]
    exact Nat.card_pos.ne'
  have hsup : ((redGL (n := n) I).ker ⊔ (bc (n := n) O.subtype).ker).index ≠ 0 := by
    intro h
    apply hN
    have hd := Subgroup.index_dvd_of_le
      (le_sup_left : (redGL (n := n) I).ker ≤ (redGL (n := n) I).ker ⊔ (bc (n := n) O.subtype).ker)
    rw [h] at hd
    exact Nat.eq_zero_of_zero_dvd hd
  have hprinc : princ (n := n) O.subtype I = ((redGL (n := n) I).ker).map (bc (n := n) O.subtype) := by
    unfold princ congPre
    rw [MonoidHom.comap_bot]
  rw [hprinc, MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq,
    Subgroup.relIndex_top_right]
  exact hsup

theorem glint_exists_denom (A : ValuationSubring L) (g : GL n L) :
    ∃ c : A.toSubring, c ≠ 0 ∧
      (c : L) • (g : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) A.toSubring.subtype).range ∧
      (c : L) • ((g⁻¹ : GL n L) : Matrix n n L) ∈
        (RingHom.mapMatrix (m := n) A.toSubring.subtype).range := by
  classical
  let f : (n × n) ⊕ (n × n) → L := fun i => match i with
    | .inl p => (g : Matrix n n L) p.1 p.2
    | .inr p => ((g⁻¹ : GL n L) : Matrix n n L) p.1 p.2
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) f
  have hmem : ∀ i, (b : L) * f i ∈ A := by
    intro i
    obtain ⟨y, hy⟩ := hb i
    rw [Algebra.smul_def] at hy
    have : (b : L) * f i = (y : L) := hy.symm
    rw [this]; exact y.2
  refine ⟨⟨(b : A), (b : A).2⟩, ?_, ?_, ?_⟩
  · intro h0
    apply nonZeroDivisors.ne_zero b.2
    exact Subtype.ext (congrArg Subtype.val h0)
  · refine ⟨Matrix.of fun i j => ⟨(b : L) * (g : Matrix n n L) i j, hmem (.inl (i, j))⟩, ?_⟩
    ext i j
    simp
  · refine ⟨Matrix.of fun i j => ⟨(b : L) * ((g⁻¹ : GL n L) : Matrix n n L) i j,
      hmem (.inr (i, j))⟩, ?_⟩
    ext i j
    simp

end Generic

section Adic

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem glint_exists_approx (x : v.adicCompletionIntegers F) :
    ∃ r : 𝓞 F, Valued.v ((x : v.adicCompletion F) - algebraMap (𝓞 F) (v.adicCompletion F) r) < 1 := by
  first | exact Bl.NearbyExistence.goal1 .. | (apply Bl.NearbyExistence.goal1 <;> assumption) | (intros; apply Bl.NearbyExistence.goal1 <;> assumption) | (apply @Bl.NearbyExistence.goal1 <;> assumption) | (intros; apply @Bl.NearbyExistence.goal1 <;> assumption) | (apply @Bl.NearbyExistence.goal1 <;> first | assumption | infer_instance)

theorem glint_finite_residueField :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := by
  let φ : 𝓞 F →+* IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
    (IsLocalRing.residue _).comp (algebraMap (𝓞 F) (v.adicCompletionIntegers F))
  have hmem : ∀ y : v.adicCompletionIntegers F, Valued.v (y : v.adicCompletion F) < 1 →
      y ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := fun y hy =>
    (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰))).2 hy
  have hker : ∀ r ∈ v.asIdeal, φ r = 0 := by
    intro r hr
    simp only [φ, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
    apply hmem
    rw [algebraMap_adicCompletionIntegers_apply, adicCompletion.valued_coe (K := F) (v := v),
      valuation_of_algebraMap]
    exact (intValuation_lt_one_iff_mem v r).2 hr
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨r, hr⟩ := glint_exists_approx v x
    refine ⟨r, ?_⟩
    simp only [φ, RingHom.comp_apply]
    show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
    rw [Ideal.Quotient.eq]
    apply hmem
    have e : ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) r - x : v.adicCompletionIntegers F) :
        v.adicCompletion F) = -((x : v.adicCompletion F) - algebraMap (𝓞 F) (v.adicCompletion F) r) := by
      rw [AddSubgroupClass.coe_sub, neg_sub, algebraMap_adicCompletionIntegers_apply,
        IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), algebraMap_adicCompletion]
      rfl
    rw [e, Valuation.map_neg]
    exact hr
  have := v.isMaximal
  have hs : Function.Surjective (Ideal.Quotient.lift v.asIdeal φ hker) :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hsurj
  exact Finite.of_surjective _ hs

theorem glint_finite_quotient_of_dvr {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (h : Finite (IsLocalRing.ResidueField R)) (I : Ideal R) (hI : I ≠ ⊥) : Finite (R ⧸ I) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have key : ∀ k : ℕ, Finite (R ⧸ IsLocalRing.maximalIdeal R ^ k) := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, Ideal.one_eq_top]
      exact Finite.of_fintype (R ⧸ ⊤)
    | succ k ih =>
      have hle : IsLocalRing.maximalIdeal R ^ (k + 1) ≤ IsLocalRing.maximalIdeal R ^ k :=
        Ideal.pow_le_pow_right (by simp)
      replace ih := Finite.of_equiv _ (DoubleQuot.quotQuotEquivQuotOfLE hle).symm.toEquiv
      suffices Finite (Ideal.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (k + 1)))
          (IsLocalRing.maximalIdeal R ^ k)) from
        .of_ideal_quotient (.map (Ideal.Quotient.mk _) (IsLocalRing.maximalIdeal R ^ k))
      exact @Finite.of_equiv _ _ h
        ((Ideal.quotEquivPowQuotPowSuccEquiv (IsPrincipalIdealRing.principal _)
          (IsDiscreteValuationRing.not_a_field _) k).trans
          (Ideal.powQuotPowSuccEquivMapMkPowSuccPow _ k))
  have : I = IsLocalRing.maximalIdeal R ^ m := by
    rw [hm, hmax, Ideal.span_singleton_pow]
  rw [this]
  exact key m

end Adic

theorem GL_integral_hecke_commute : Formalism.UG.GLintComm := by
  intro F _ _ v n g
  obtain ⟨c, hc0, hg, hg'⟩ := glint_exists_denom (v.adicCompletionIntegers F) g
  have hP := glint_princ_le_map_conj (v.adicCompletionIntegers F).toSubring g c hg hg'
  have hres : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := glint_finite_residueField v
  have hI : Ideal.span {c * c} ≠ (⊥ : Ideal (v.adicCompletionIntegers F).toSubring) := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero hc0 hc0
  have hfin : Finite ((v.adicCompletionIntegers F).toSubring ⧸ Ideal.span {c * c}) :=
    glint_finite_quotient_of_dvr hres _ hI
  have hne := glint_princ_relIndex_ne_zero (n := Fin n) (v.adicCompletionIntegers F).toSubring
    (Ideal.span {c * c})
  have hd := Subgroup.relIndex_dvd_of_le_left (bc (n := Fin n) (v.adicCompletionIntegers F).toSubring.subtype).range hP
  intro h0
  apply hne
  unfold GLint at h0 hd
  rw [h0] at hd
  exact Nat.eq_zero_of_zero_dvd hd

end Formalism.UG.P
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
section
noncomputable section

open Matrix TensorProduct

namespace Formalism.UG.P

open Formalism.UG

theorem bc_coe {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
    (φ : A →+* B) (g : GL n A) : ((bc φ g : GL n B) : Matrix n n B) = (g : Matrix n n A).map φ :=
  rfl

theorem incl_cT_map {A B : Type} [CommRing A] [CommRing B] {m p : Type}
    (σ : A →+* A) (σ' : B →+* B) (φ : A →+* B) (h : φ.comp σ = σ'.comp φ) (M : Matrix m p A) :
    cT σ' (M.map φ) = (cT σ M).map φ := by
  ext i j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
  exact (RingHom.congr_fun h (M j i)).symm

theorem bc_mem {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
    (σ : A →+* A) (σ' : B →+* B) (φ : A →+* B) (h : φ.comp σ = σ'.comp φ)
    (J : Matrix n n A) (g : GL n A) (hg : g ∈ UJ σ J) : bc φ g ∈ UJ σ' (J.map φ) := by
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  show cT σ' ((bc φ g : GL n B) : Matrix n n B) * J.map φ * ((bc φ g : GL n B) : Matrix n n B) = J.map φ
  rw [bc_coe, incl_cT_map σ σ' φ h, ← Matrix.map_mul, ← Matrix.map_mul, hg']

theorem inclE_injective (F E : Type) [Field F] [CommRing E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] [Nontrivial R] :
    Function.Injective (inclE (F := F) (E := E) R) := by
  intro x y hxy
  exact Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F R).injective hxy

theorem UG_inclusion_injective : Formalism.UG.InclInj := by
  intro F E _ _ _ n _ _ R _ _ hR
  haveI := hR
  intro g g' hgg
  apply Units.ext
  have h1 := congrArg Units.val hgg
  rw [bc_coe, bc_coe] at h1
  ext i j
  exact inclE_injective F E R (congrFun (congrFun h1 i) j)

private lemma sigR_tmul_adelic_iwasawa_hecke (F E : Type) [Field F] [CommRing E] [Algebra F E] (σ : E →ₐ[F] E)
    (x : E) (c : F) : Formalism.UG.sigR σ F (x ⊗ₜ[F] c) = σ x ⊗ₜ[F] c := by
  first
  | rfl
  | simp [Formalism.UG.sigR]
  | (unfold Formalism.UG.sigR; simp)

end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LinSubstIsHomogeneous
section
noncomputable section

open MvPolynomial

namespace Formalism.UG.P

variable {O : Type} [CommRing O] {n : Type} [Fintype n] [DecidableEq n]

theorem linSubst_isHomogeneous (M : Matrix n n O) {k : ℕ} {P : MvPolynomial n O}
    (hP : P.IsHomogeneous k) : (linSubst O n M P).IsHomogeneous k := by
  have h := hP.aeval (fun i => ∑ j, C (M i j) * X j) (n := 1)
    (fun i => IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ _))
  simpa [linSubst] using h

theorem nabla_subspace_stable : Formalism.UG.NablaStable := by
  intro O _ n _ _ k g P hP
  rw [nabla, mem_homogeneousSubmodule] at hP ⊢
  exact linSubst_isHomogeneous _ hP

theorem pow_sum_expand (a b : n → MvPolynomial n O) (K : ℕ) :
    (∑ j, C (a j) * map C (b j) : MvPolynomial n (MvPolynomial n O)) ^ K
      = ∑ β ∈ Finset.piAntidiag Finset.univ K,
          C ((Nat.multinomial Finset.univ β : MvPolynomial n O) * ∏ j, a j ^ β j) *
            map C (∏ j, b j ^ β j) := by
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow, map_mul, map_natCast]
  ring

theorem coeff_pow_sum_expand (a b : n → MvPolynomial n O) (K : ℕ) (α : n →₀ ℕ) :
    coeff α ((∑ j, C (a j) * map C (b j) : MvPolynomial n (MvPolynomial n O)) ^ K)
      = ∑ β ∈ Finset.piAntidiag Finset.univ K,
          (Nat.multinomial Finset.univ β : MvPolynomial n O) * (∏ j, a j ^ β j) *
            C (coeff α (∏ j, b j ^ β j)) := by
  rw [pow_sum_expand, coeff_sum]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  rw [coeff_C_mul, coeff_map]

theorem prod_X_pow_fun (β : n → ℕ) :
    (∏ j, X j ^ β j : MvPolynomial n O) = monomial (Finsupp.equivFunOnFinite.symm β) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype]
  · rfl
  · intro i; simp

theorem weyl_gen_eq (α : n →₀ ℕ) (K : ℕ) (hα : α.degree = K) :
    monomial α (α.multinomial : O) =
      coeff α ((∑ j, C (X j) * map C (X j) : MvPolynomial n (MvPolynomial n O)) ^ K) := by
  rw [coeff_pow_sum_expand, Finset.sum_eq_single (⇑α)]
  · have hs : Finsupp.equivFunOnFinite.symm ⇑α = α := Finsupp.equivFunOnFinite.symm_apply_apply α
    rw [prod_X_pow_fun, hs, coeff_monomial, if_pos rfl, C_1, mul_one,
      Finsupp.multinomial_of_support_subset (Finset.subset_univ _),
      ← map_natCast (C : O →+* MvPolynomial n O), C_mul_monomial, mul_one]
  · intro β _ hβ
    rw [prod_X_pow_fun, coeff_monomial, if_neg, C_0, mul_zero]
    intro h
    apply hβ
    rw [← h]
    rfl
  · intro h
    exfalso
    apply h
    rw [Finset.mem_piAntidiag]
    refine ⟨?_, fun i _ => Finset.mem_univ i⟩
    rw [← hα, Finsupp.degree_eq_sum]

theorem map_polyAct_pow (g : GL n O) (K : ℕ) :
    map (polyAct O n g).toRingHom
        ((∑ j, C (X j) * map C (X j) : MvPolynomial n (MvPolynomial n O)) ^ K)
      = (∑ i, C (X i) *
          map C (∑ j, C (((g⁻¹ : GL n O) : Matrix n n O) j i) * X j) :
            MvPolynomial n (MvPolynomial n O)) ^ K := by
  rw [map_pow]
  congr 1
  simp only [map_sum, map_mul, map_C, map_X, polyAct, linSubst, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, aeval_X, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

theorem polyAct_weyl_gen (g : GL n O) (K : ℕ) (α : n →₀ ℕ) (hα : α.degree = K) :
    polyAct O n g (monomial α (α.multinomial : O)) ∈ weylSub O n K := by
  rw [weyl_gen_eq α K hα]
  have h1 : polyAct O n g
      (coeff α ((∑ j, C (X j) * map C (X j) : MvPolynomial n (MvPolynomial n O)) ^ K))
      = coeff α (map (polyAct O n g).toRingHom
          ((∑ j, C (X j) * map C (X j) : MvPolynomial n (MvPolynomial n O)) ^ K)) :=
    (coeff_map _ _ _).symm
  rw [h1, map_polyAct_pow, coeff_pow_sum_expand]
  refine Submodule.sum_mem _ (fun β hβ => ?_)
  have hdeg : (Finsupp.equivFunOnFinite.symm β).degree = K := by
    rw [Finsupp.degree_eq_sum]
    exact (Finset.mem_piAntidiag.mp hβ).1
  have hm : Nat.multinomial Finset.univ β = (Finsupp.equivFunOnFinite.symm β).multinomial :=
    Finsupp.multinomial_of_support_subset (s := Finset.univ)
      (d := Finsupp.equivFunOnFinite.symm β) (Finset.subset_univ _)
  rw [prod_X_pow_fun, hm]
  generalize coeff (R := O) (σ := n) α _ = c
  have he : ((Finsupp.equivFunOnFinite.symm β).multinomial : MvPolynomial n O) *
      monomial (Finsupp.equivFunOnFinite.symm β) 1 * C c
      = c • monomial (Finsupp.equivFunOnFinite.symm β)
          ((Finsupp.equivFunOnFinite.symm β).multinomial : O) := by
    rw [smul_eq_C_mul, ← map_natCast (C : O →+* MvPolynomial n O), C_mul_monomial, mul_one,
      mul_comm]
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hdeg, rfl⟩)

theorem weyl_module_stable : Formalism.UG.WeylStable := by
  intro O _ n _ _ k g P hP
  have hle : weylSub O n k ≤ (weylSub O n k).comap (polyAct O n g).toLinearMap := by
    refine Submodule.span_le.mpr ?_
    rintro p ⟨α, hα, rfl⟩
    exact polyAct_weyl_gen g k α hα
  exact hle hP

end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Nabladual
section
namespace Formalism.UG.P

open MvPolynomial

section

variable (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n]

noncomputable def monFam (k : ℕ) : {d : n →₀ ℕ | d.degree = k} → MvPolynomial n O :=
  fun d => monomial (d : n →₀ ℕ) 1

theorem monFam_linearIndependent (k : ℕ) : LinearIndependent O (monFam O n k) := by
  have h := (basisMonomials n O).linearIndependent.comp
    (Subtype.val : {d : n →₀ ℕ | d.degree = k} → n →₀ ℕ) Subtype.val_injective
  have e : monFam O n k = ⇑(basisMonomials n O) ∘ Subtype.val := by
    funext d
    simp [monFam, coe_basisMonomials]
  rw [e]
  exact h

theorem span_monFam (k : ℕ) :
    Submodule.span O (Set.range (monFam O n k)) = Formalism.UG.nabla O n k := by
  rw [Formalism.UG.nabla, homogeneousSubmodule_eq_finsupp_supported]
  change _ = restrictSupport O _
  rw [restrictSupport_eq_span, Set.image_eq_range]
  rfl

noncomputable def nablaBasis (k : ℕ) :
    Module.Basis {d : n →₀ ℕ | d.degree = k} O (Formalism.UG.nabla O n k) :=
  (Module.Basis.span (monFam_linearIndependent O n k)).map
    (LinearEquiv.ofEq _ _ (span_monFam O n k))

end

section

variable (n : Type) [Fintype n] [DecidableEq n]

theorem degree_eq_one_iff (d : n →₀ ℕ) : d.degree = 1 ↔ ∃ i, d = Finsupp.single i 1 := by
  constructor
  · intro hd
    have hne : d ≠ 0 := by
      rintro rfl
      simp at hd
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (Finsupp.ext h)
    have hle : d i ≤ 1 := hd ▸ Finsupp.le_degree i d
    have hi1 : d i = 1 := by omega
    have hsle : Finsupp.single i 1 ≤ d := by
      rw [Finsupp.single_le_iff]
      omega
    have hsplit : d = Finsupp.single i 1 + (d - Finsupp.single i 1) :=
      (add_tsub_cancel_of_le hsle).symm
    have hdeg : (d - Finsupp.single i 1).degree = 0 := by
      have := congrArg Finsupp.degree hsplit
      rw [map_add, Finsupp.degree_single] at this
      omega
    rw [Finsupp.degree_eq_zero_iff] at hdeg
    refine ⟨i, ?_⟩
    rw [hdeg, add_zero] at hsplit
    exact hsplit
  · rintro ⟨i, rfl⟩
    simp

noncomputable def idx1 : n ≃ {d : n →₀ ℕ | d.degree = 1} :=
  Equiv.ofBijective (fun i => ⟨Finsupp.single i 1, by simp⟩)
    ⟨fun i j h => by
      have h' : Finsupp.single i 1 = Finsupp.single j 1 := congrArg Subtype.val h
      exact (Finsupp.single_left_inj one_ne_zero).mp h',
     fun d => by
      obtain ⟨i, hi⟩ := (degree_eq_one_iff n d).mp d.2
      exact ⟨i, Subtype.ext hi.symm⟩⟩

end

noncomputable def nablaDualEquiv (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] :
    Formalism.UG.nabla O n 1 ≃ₗ[O] Module.Dual O (n → O) :=
  (nablaBasis O n 1).equiv (Pi.basisFun O n).dualBasis (idx1 n).symm

end Formalism.UG.P
end

