import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0035

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatricesIntertwiningOfSemilinearStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matrices_intertwining_of_semilinear_alt : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (emb : O →+* PadicAlgCl l) (I M : Type) [AddCommGroup M] [Module O M] [Module (MvPolynomial I O) M] [IsScalarTower O (MvPolynomial I O) M], Module.Finite O M → (∀ (c : O) (x : M), c • x = 0 → c = 0 ∨ x = 0) → ∀ (V : Type) [AddCommGroup V] [Module (PadicAlgCl l) V] (j : M →ₛₗ[emb] V) (Tq : I → V →ₗ[PadicAlgCl l] V), (∀ (n : ℕ) (x : Fin n → M), LinearIndependent O x → LinearIndependent (PadicAlgCl l) fun a => j (x a)) → (∀ i x, j ((MvPolynomial.X i : MvPolynomial I O) • x) = Tq i (j x)) → ∃ (n : ℕ) (σ : MvPolynomial I O →ₐ[O] Matrix (Fin n) (Fin n) O) (e : (Fin n → PadicAlgCl l) →ₗ[PadicAlgCl l] V), (∀ p, σ p = 0 → ∀ x : M, p • x = 0) ∧ Function.Injective e ∧ (∀ c, e c ∈ Submodule.span (PadicAlgCl l) (Set.range j)) ∧ ∀ i c, Tq i (e c) = e ((σ (MvPolynomial.X i)).map emb *ᵥ c) := by
  first | exact @GlobalTheory.exists_matrices_intertwining_of_semilinear | exact GlobalTheory.exists_matrices_intertwining_of_semilinear | (intros; apply GlobalTheory.exists_matrices_intertwining_of_semilinear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixSqrtNearOneUltrametricStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matrix_sqrt_near_one_ultrametric : ∀ (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] (n : ℕ) (σ : K →+* K), Continuous σ → ∃ W ∈ nhds (1 : Matrix (Fin n) (Fin n) K), ∀ s ∈ W, ∃ r : Matrix (Fin n) (Fin n) K, r * r = s ∧ (∀ a : Matrix (Fin n) (Fin n) K, a * s = s * a → a * r = r * a) ∧ ((s.map σ)ᵀ = s → (r.map σ)ᵀ = r) := by
  first | exact @GlobalTheory.matrix_sqrt_near_one_ultrametric | exact GlobalTheory.matrix_sqrt_near_one_ultrametric | (intros; apply GlobalTheory.matrix_sqrt_near_one_ultrametric <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalPrimeCharNotMemFiniteTypeIntStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maximal_prime_char_not_mem_finiteType_int : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] (f : R), f ≠ 0 → ∃ M : Ideal R, M.IsMaximal ∧ f ∉ M ∧ ∃ p : ℕ, p.Prime ∧ (p : R) ∈ M := by
  first | exact @GlobalTheory.closedPt_of_finiteType_int | exact GlobalTheory.closedPt_of_finiteType_int | (intros; apply GlobalTheory.closedPt_of_finiteType_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalSubfieldMissingElemExpOneStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maximal_subfield_missing_elem_expOne : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] (F : Subfield K), (∀ y : K, y ^ p ∈ F) → ∀ f : K, f ∉ F → ∃ L : Subfield K, F ≤ L ∧ f ∉ L ∧ IntermediateField.adjoin L ({f} : Set K) = ⊤ := by
  first | exact @GlobalTheory.cfmax_main | exact GlobalTheory.cfmax_main | (intros; apply GlobalTheory.cfmax_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemSubmonoidDvdMulOfForallHeightEqOne
section
open IsLocalRing

namespace GlobalTheory

theorem exists_mem_submonoid_dvd_mul_of_forall_height_eq_one :
    ∀ (B : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    (S : Submonoid B), (0 : B) ∉ S → ∀ x y : B, y ≠ 0 →
    (∀ Q : Ideal B, Q.IsPrime → Q.height = 1 → y ∈ Q → Disjoint (S : Set B) (Q : Set B) →
      ∃ t ∉ Q, y ∣ t * x) → ∃ u ∈ S, y ∣ u * x := by
  intro B _ _ _ _ S _ x y hy h
  by_contra! hS
  set M := B ⧸ Ideal.span {y}
  set N : Submodule B M := B ∙ (Ideal.Quotient.mk (Ideal.span {y}) x)
  have hmem : ∀ r : B, r ∈ Module.annihilator B N ↔ y ∣ r * x := by
    intro r
    change r ∈ Submodule.annihilator N ↔ _
    rw [Submodule.mem_annihilator_span_singleton, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  set I := Module.annihilator B N
  have hdisj : Disjoint (S : Set B) (I : Set B) := by
    rw [Set.disjoint_left]
    intro u hu huI
    exact hS u hu ((hmem u).mp huI)
  obtain ⟨P, hP, hIP, hPS⟩ := Ideal.exists_le_prime_disjoint I S hdisj.symm
  obtain ⟨P', hP'min, hP'P⟩ := Ideal.exists_minimalPrimes_le hIP
  have hass : P' ∈ associatedPrimes B N :=
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes B N hP'min
  have hass' : P' ∈ associatedPrimes B M :=
    associatedPrimes.subset_of_injective Subtype.val_injective (f := N.subtype) hass
  obtain ⟨hpr, h1, hyP⟩ := (mem_associatedPrimes_iff_height_eq_one hy).mp hass'
  obtain ⟨t, htQ, ht⟩ := h P' hpr h1 hyP (hPS.symm.mono_right hP'P)
  exact htQ (hP'min.1.2 ((hmem t).mpr ht))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMinimalLocalGenerators
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem coeffs_mem_maximalIdeal_of_sum_mem_sq {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {n : ℕ} (z : Fin n → R) (hz : Ideal.span (Set.range z) = maximalIdeal R)
    (hn : n = (maximalIdeal R).spanFinrank) (b : Fin n → R)
    (hb : ∑ j, b j * z j ∈ maximalIdeal R ^ 2) : ∀ j, b j ∈ maximalIdeal R := by
  have h : ∀ k, z k ∈ maximalIdeal R := fun k => hz ▸ Ideal.subset_span ⟨k, rfl⟩
  have h1 : Submodule.span R (Set.range fun k => (⟨z k, h k⟩ : maximalIdeal R)) = ⊤ := by
    apply Submodule.map_injective_of_injective (maximalIdeal R).injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    exact hz
  have h2 := IsLocalRing.CotangentSpace.span_image_eq_top_iff.2 h1
  rw [← Set.range_comp] at h2
  have hli := linearIndependent_of_top_le_span_of_card_le_finrank h2.ge (by
    rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]; simp [hn])
  have key : ∑ k, residue R (b k) • ((maximalIdeal R).toCotangent ⟨z k, h k⟩ : CotangentSpace R)
      = 0 := by
    have h3 : ∑ k, residue R (b k) • ((maximalIdeal R).toCotangent ⟨z k, h k⟩ : CotangentSpace R)
        = (maximalIdeal R).toCotangent (∑ k, b k • (⟨z k, h k⟩ : maximalIdeal R)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul]
      exact algebraMap_smul (ResidueField R) (b k) _
    rw [h3, Ideal.toCotangent_eq_zero]
    simpa using hb
  intro j
  have := Fintype.linearIndependent_iff.1 hli (fun k => residue R (b k)) key j
  exact (residue_eq_zero_iff _).1 this

theorem exists_minimal_local_generators :
    ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (Q : Ideal S) [Q.IsPrime],
      ∃ (h : ℕ) (f : Fin h → S) (g : S), g ∉ Q ∧ (∀ j, f j ∈ Q) ∧
        (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧
        h = (maximalIdeal (Localization.AtPrime Q)).spanFinrank ∧
        ∀ (a : Fin h → S) (u : S), u ∉ Q → u * ∑ j, a j * f j ∈ Q ^ 2 → ∀ j, a j ∈ Q := by
  first
  | exact @_root_.GlobalTheory.MultipleMembershipForAll.main
  | exact _root_.GlobalTheory.MultipleMembershipForAll.main
  | (apply _root_.GlobalTheory.MultipleMembershipForAll.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.MultipleMembershipForAll.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MultipleMembershipForAll.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MultipleMembershipForAll.main ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulIsIntegralElemOfForallDiscreteValuation
section
open IsLocalRing

namespace GlobalTheory

theorem exists_mul_isIntegralElem_of_forall_discreteValuationSubring :
    ∀ (C B : Type) [CommRing C] [IsDomain C] [IsNoetherianRing C] [CommRing B] (e : C →+* B),
      Function.Injective e → (∀ b : B, ∃ c s : C, IsUnit (e s) ∧ b * e s = e c) →
      ∀ (p : Ideal C), p.IsPrime → ∀ f : B,
        (∀ (F : Type) [Field F] (β : B →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V →
          (∀ c, β (e c) ∈ V) → (∀ c ∈ p, β (e c) ∈ V.nonunits) → β f ∈ V) →
        ∃ d : C, d ∉ p ∧ e.IsIntegralElem (e d * f) := by
  intro C B _ _ _ _ e he hloc p hp f hf
  haveI : Nontrivial B := ⟨⟨e 0, e 1, fun h => zero_ne_one (he h)⟩⟩
  haveI : NoZeroDivisors B := ⟨fun {a b} hab => by
    obtain ⟨c₁, s₁, u₁, h₁⟩ := hloc a
    obtain ⟨c₂, s₂, u₂, h₂⟩ := hloc b
    have hc : c₁ * c₂ = 0 := he (by
      rw [map_mul, ← h₁, ← h₂, map_zero,
        show a * e s₁ * (b * e s₂) = (a * b) * (e s₁ * e s₂) by ring, hab, zero_mul])
    rcases mul_eq_zero.1 hc with h | h
    · left
      rw [h, map_zero] at h₁
      exact u₁.mul_left_eq_zero.1 h₁
    · right
      rw [h, map_zero] at h₂
      exact u₂.mul_left_eq_zero.1 h₂⟩
  haveI : IsDomain B := NoZeroDivisors.to_isDomain B
  let L := FractionRing B
  let β : B →+* L := algebraMap B L
  have hβ : Function.Injective β := IsFractionRing.injective B L
  letI : Algebra C L := (β.comp e).toAlgebra
  have hCL : ∀ c, algebraMap C L c = β (e c) := fun _ => rfl
  have hinj : Function.Injective (algebraMap C L) := hβ.comp he
  haveI : FaithfulSMul C L := (faithfulSMul_iff_algebraMap_injective C L).2 hinj
  have hne : ∀ s : C, IsUnit (e s) → β (e s) ≠ 0 := fun s hs => ((hs.map β).ne_zero)
  haveI : IsFractionRing C L := IsFractionRing.of_field C L fun z => by
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := B) z
    obtain ⟨cx, sx, ux, hx⟩ := hloc x
    obtain ⟨cy, sy, uy, hy'⟩ := hloc y
    refine ⟨cx * sy, cy * sx, ?_⟩
    have hy0 : β y ≠ 0 := by
      rw [map_ne_zero_iff _ hβ]; exact nonZeroDivisors.ne_zero hy
    show β x / β y = _
    simp only [hCL, map_mul]
    rw [← hx, ← hy']
    simp only [map_mul]
    rw [div_eq_div_iff hy0 (mul_ne_zero (mul_ne_zero hy0 (hne sy uy)) (hne sx ux))]
    ring
  let Cp := Localization.AtPrime p
  haveI : IsNoetherianRing Cp := IsLocalization.isNoetherianRing p.primeCompl Cp inferInstance
  have hunit : ∀ y : p.primeCompl, IsUnit (algebraMap C L y) := fun y => by
    refine isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ hinj).2 ?_)
    intro h0
    exact y.2 (h0 ▸ p.zero_mem)
  letI : Algebra Cp L := (IsLocalization.lift (M := p.primeCompl) (S := Cp) hunit).toAlgebra
  haveI : IsScalarTower C Cp L :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunit x).symm
  haveI : IsFractionRing Cp L := IsFractionRing.isFractionRing_of_isLocalization p.primeCompl Cp L
    p.primeCompl_le_nonZeroDivisors
  haveI : Algebra.EssFiniteType Cp L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors Cp)
  have hint : IsIntegral Cp (β f) := by
    by_contra hn
    obtain ⟨V, hV, hd, hfV⟩ := exists_discreteValuationSubring_dominating_notMem hn
    obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff _ V).1 hd
    apply hfV
    refine hf L β V hV (fun c => ?_) (fun c hc => ?_)
    · have := h1 (algebraMap C Cp c)
      rwa [← IsScalarTower.algebraMap_apply] at this
    · have := h2 (algebraMap C Cp c)
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff Cp p c).2 hc)
      rwa [← IsScalarTower.algebraMap_apply] at this
  obtain ⟨⟨d, hd⟩, hdi⟩ := IsIntegral.exists_multiple_integral_of_isLocalization p.primeCompl (β f) hint
  refine ⟨d, hd, ?_⟩
  obtain ⟨q, hq, hq0⟩ := hdi
  refine ⟨q, hq, hβ ?_⟩
  rw [Polynomial.hom_eval₂, map_zero, ← hq0, Submonoid.smul_def, Algebra.smul_def, hCL, map_mul]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultilinearFormOfPicTorsion
section
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PicTorsionForm

open CommRing Module

variable {B : Type} [CommRing B]

theorem exists_local_generator (M : Type) [AddCommGroup M] [Module B M] [Module.Invertible B M]
    (p : Ideal B) [p.IsPrime] : ∃ e : M, ∀ x : M, ∃ w a : B, w ∉ p ∧ w • x = a • e := by
  have ⟨f⟩ := Invertible.free_iff_linearEquiv.mp
    (inferInstance : Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M))
  obtain ⟨e, s, he⟩ : ∃ (e : M) (s : p.primeCompl), LocalizedModule.mk e s = f.symm 1 :=
    LocalizedModule.induction_on (β := fun y => ∃ (e : M) (s : p.primeCompl), LocalizedModule.mk e s = y)
      (fun e s => ⟨e, s, rfl⟩) (f.symm 1)
  refine ⟨e, fun x => ?_⟩
  obtain ⟨a, t, ht⟩ : ∃ (a : B) (t : p.primeCompl), Localization.mk a t = f (LocalizedModule.mk x 1) :=
    Localization.induction_on (f (LocalizedModule.mk x 1)) fun z => ⟨z.1, z.2, rfl⟩
  have key : LocalizedModule.mk x (1 : p.primeCompl) = LocalizedModule.mk (a • e) (t * s) := by
    rw [← f.symm_apply_apply (LocalizedModule.mk x 1), ← ht, ← mul_one (Localization.mk a t),
      ← smul_eq_mul, map_smul, ← he, LocalizedModule.mk_smul_mk]
  obtain ⟨u, hu⟩ := (LocalizedModule.mk_eq).mp key
  refine ⟨(u : B) * ((t : B) * s), u * a, ?_, ?_⟩
  · exact p.primeCompl.mul_mem u.2 (p.primeCompl.mul_mem t.2 s.2)
  · simpa only [Submonoid.smul_def, Submonoid.coe_mul, OneMemClass.coe_one, one_smul, smul_smul] using hu

theorem tensorPow_equiv (c : Pic B) (n : ℕ) :
    Nonempty (Pic.AsModule (c ^ n) ≃ₗ[B] ⨂[B] _ : Fin n, Pic.AsModule c) := by
  induction n with
  | zero =>
    have ⟨e⟩ := Pic.ext_iff.mp (pow_zero c)
    have ⟨g⟩ := Pic.mk_eq_one_iff.mp (Pic.mk_eq_self (M := (1 : Pic B)))
    exact ⟨e ≪≫ₗ g ≪≫ₗ (PiTensorProduct.isEmptyEquiv (Fin 0)).symm⟩
  | succ n ih =>
    obtain ⟨ih⟩ := ih
    have ⟨e1⟩ := Pic.ext_iff.mp (pow_succ c n)
    have ⟨e2⟩ := Pic.ext_iff.mp (Pic.mul_eq_tensor (c ^ n) c)
    exact ⟨e1 ≪≫ₗ e2 ≪≫ₗ Pic.mk.linearEquiv B _ ≪≫ₗ TensorProduct.congr ih
      (PiTensorProduct.subsingletonEquiv (R := B) (s := fun _ : Fin 1 => Pic.AsModule c) 0).symm ≪≫ₗ
      PiTensorProduct.tmulEquiv B (Pic.AsModule c) ≪≫ₗ PiTensorProduct.reindex B _ finSumFinEquiv⟩

theorem exists_form : ∀ (B : Type) [CommRing B] (q : ℕ) (c : CommRing.Pic B), c ^ q = 1 →
    ∃ φ : MultilinearMap B (fun _ : Fin q => CommRing.Pic.AsModule c) B,
      ∀ p : Ideal B, p.IsPrime → ∃ e : CommRing.Pic.AsModule c, φ (fun _ => e) ∉ p := by
  intro B _ q c hc
  obtain ⟨T⟩ := tensorPow_equiv c q
  have ⟨e1⟩ := Pic.ext_iff.mp hc
  have ⟨g⟩ := Pic.mk_eq_one_iff.mp (Pic.mk_eq_self (M := (1 : Pic B)))
  let ψ : (⨂[B] _ : Fin q, Pic.AsModule c) ≃ₗ[B] B := T.symm ≪≫ₗ e1 ≪≫ₗ g
  refine ⟨ψ.toLinearMap.compMultilinearMap (PiTensorProduct.tprod B), fun p hp => ?_⟩
  obtain ⟨x, hx⟩ : ∃ x : Fin q → Pic.AsModule c, ψ (PiTensorProduct.tprod B x) ∉ p := by
    by_contra! h
    have hall : ∀ t, ψ t ∈ p := fun t => by
      induction t using PiTensorProduct.induction_on with
      | smul_tprod r x => rw [map_smul, smul_eq_mul]; exact p.mul_mem_left r (h x)
      | add a b ha hb => rw [map_add]; exact p.add_mem ha hb
    exact hp.ne_top ((Ideal.eq_top_iff_one p).mpr (by simpa using hall (ψ.symm 1)))
  obtain ⟨e, he⟩ := exists_local_generator (Pic.AsModule c) p
  choose w a hw hwa using fun i => he (x i)
  refine ⟨e, fun hmem => ?_⟩
  have hmem' : ψ (PiTensorProduct.tprod B fun _ => e) ∈ p := hmem
  have h1 : ψ (PiTensorProduct.tprod B (fun i => w i • x i)) =
      (∏ i, w i) * ψ (PiTensorProduct.tprod B x) := by
    rw [MultilinearMap.map_smul_univ, map_smul, smul_eq_mul]
  have h2 : ψ (PiTensorProduct.tprod B (fun i => w i • x i)) =
      (∏ i, a i) * ψ (PiTensorProduct.tprod B (fun _ => e)) := by
    simp_rw [hwa]; rw [MultilinearMap.map_smul_univ, map_smul, smul_eq_mul]
  have hin : (∏ i, w i) * ψ (PiTensorProduct.tprod B x) ∈ p := by
    rw [← h1, h2]; exact p.mul_mem_left _ hmem'
  rcases hp.mem_or_mem hin with h | h
  · exact (p.primeCompl.prod_mem fun i _ => hw i) h
  · exact hx h

end GlobalTheory.PicTorsionForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMvPolynomialPickPoint
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem exists_mvPolynomial_pick_point :
    ∀ (S : Type) (T : Finset (S → ℂ)) (p : S → ℂ), ∃ Q : MvPolynomial S ℂ,
      MvPolynomial.eval p Q = 1 ∧ ∀ t ∈ T, t ≠ p → MvPolynomial.eval t Q = 0 := by
  classical
  intro S T p
  induction T using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert a T _ ih =>
    obtain ⟨Q, hQ1, hQ0⟩ := ih
    by_cases hap : a = p
    · refine ⟨Q, hQ1, fun t ht htp => ?_⟩
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact absurd hap htp
      · exact hQ0 t ht htp
    · obtain ⟨s, hs⟩ := Function.ne_iff.1 hap
      have hne : p s - a s ≠ 0 := sub_ne_zero.2 (Ne.symm hs)
      refine ⟨Q * (MvPolynomial.C (p s - a s)⁻¹ * (MvPolynomial.X s - MvPolynomial.C (a s))),
        ?_, fun t ht htp => ?_⟩
      · simp only [map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X, hQ1, one_mul]
        exact inv_mul_cancel₀ hne
      · rcases Finset.mem_insert.1 ht with rfl | ht
        · simp
        · simp [hQ0 t ht htp]

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulMemRangePiQuotientMinimalPrimesStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nat_mul_mem_range_pi_quotient_minimalPrimes' : ∀ (B : Type) [CommRing B] [Module.Finite ℤ B], ∃ n : ℕ, n ≠ 0 ∧ ∀ b' : ((P : minimalPrimes B) → B ⧸ (P : Ideal B)), (n : (P : minimalPrimes B) → B ⧸ (P : Ideal B)) * b' ∈ (Pi.ringHom fun P : minimalPrimes B => Ideal.Quotient.mk (P : Ideal B)).range := by
  first | exact @GlobalTheory.CokerMinimalPrimes.exists_nat_mul_mem_range_pi_quotient_minimalPrimes | exact GlobalTheory.CokerMinimalPrimes.exists_nat_mul_mem_range_pi_quotient_minimalPrimes | (intros; apply GlobalTheory.CokerMinimalPrimes.exists_nat_mul_mem_range_pi_quotient_minimalPrimes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroAlgebraMapEqMulOfFormallyUnramifiedAStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified' : ∀ (P D : Type) [CommRing P] [IsDomain P] [CommRing D] [IsDomain D] [Algebra P D] [Algebra.FiniteType P D] [Algebra.FormallyUnramified P D] (f : D), f ≠ 0 → ∃ Q : P, Q ≠ 0 ∧ ∃ d : D, algebraMap P D Q = f * d := by
  first | exact @GlobalTheory.exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified | exact GlobalTheory.exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified | (intros; apply GlobalTheory.exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsFixOfContinuousCoefficientsStatement
section
open Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nhds_fix_of_continuous_coefficients : (∀ {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V),
    (∀ l : V →ₗ[ℂ] ℂ, ∃ C : ℝ, ∀ x ∈ s, ‖l x‖ ≤ C) → FiniteDimensional ℂ (Submodule.span ℂ s)) →
  ∀ {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G) {V : Type} [AddCommGroup V] [Module ℂ V]
    (S : G → Module.End ℂ V), (∀ x ∈ H, ∀ y ∈ H, S (x * y) = S x * S y) → S 1 = 1 →
    (∀ (l : V →ₗ[ℂ] ℂ) (w : V), ContinuousOn (fun x => l (S x w)) (H : Set G)) →
    (∀ U ∈ 𝓝 (1 : G), ∃ K : Subgroup G, K ≤ H ∧ IsCompact (K : Set G) ∧
      (∃ O : Set G, IsOpen O ∧ (1 : G) ∈ O ∧ ∀ x ∈ O, x ∈ H → x ∈ K) ∧ (K : Set G) ⊆ U) →
    ∀ v : V, ∃ U ∈ 𝓝 (1 : G), ∀ x ∈ U, x ∈ H → S x v = v := by
  first | exact @GlobalTheory.SmoothFix.exists_nhds_fix | exact GlobalTheory.SmoothFix.exists_nhds_fix | (intros; apply GlobalTheory.SmoothFix.exists_nhds_fix <;> assumption)
end

