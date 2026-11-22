import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0038
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0020
import Formalism.PairingDivisors.StatementN

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdjacentSelfDualLatticesIndexSimple
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

open Classical in
open scoped BigOperators in
private lemma existsUnique_quotient_sub_smul_mem {R X : Type} [CommRing R] [AddCommGroup X]
    [Module R X] (A B : Submodule R X) (x : X) (P : Ideal R)
    (hxP : ∀ r : R, r • x ∈ A ↔ r ∈ P) (hBle : B ≤ (A ⊓ B) ⊔ Submodule.span R {x}) :
    ∀ b ∈ B, ∃! q : R ⧸ P, b - (Quotient.out q : R) • x ∈ A := by
  intro b hb
  obtain ⟨c, hc, y, hy, rfl⟩ := Submodule.mem_sup.1 (hBle hb)
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
  refine ⟨Ideal.Quotient.mk P r, ?_, ?_⟩
  · have h1 : (r - Quotient.out (Ideal.Quotient.mk P r)) • x ∈ A := by
      rw [hxP, ← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
    have h2 : c + r • x - Quotient.out (Ideal.Quotient.mk P r) • x =
        c + (r - Quotient.out (Ideal.Quotient.mk P r)) • x := by
      rw [sub_smul]; abel
    show c + r • x - Quotient.out (Ideal.Quotient.mk P r) • x ∈ A
    rw [h2]
    exact A.add_mem (Submodule.mem_inf.1 hc).1 h1
  · intro q hq
    have h2 : (r - Quotient.out q) • x ∈ A := by
      have h3 : (r - Quotient.out q) • x = (c + r • x - Quotient.out q • x) - c := by
        rw [sub_smul]; abel
      rw [h3]
      exact A.sub_mem hq (Submodule.mem_inf.1 hc).1
    rw [hxP, ← Ideal.Quotient.eq, Ideal.Quotient.mk_out] at h2
    exact h2.symm

open Classical in
open scoped BigOperators in
private lemma le_or_eq_of_inf_le_of_le_of_isMaximal {R X : Type} [CommRing R] [AddCommGroup X]
    [Module R X] (A B : Submodule R X) (x : X) (hx : x ∈ B) (P : Ideal R) (hP : P.IsMaximal)
    (hxP : ∀ r : R, r • x ∈ A ↔ r ∈ P) (hBle : B ≤ (A ⊓ B) ⊔ Submodule.span R {x})
    (T : Submodule R X) (h1 : A ⊓ B ≤ T) (h2 : T ≤ B) : T ≤ A ∨ T = B := by
  by_cases hTA : T ≤ A
  · exact Or.inl hTA
  right
  obtain ⟨t, htT, htA⟩ := Set.not_subset.1 hTA
  obtain ⟨c, hc, y, hy, rfl⟩ := Submodule.mem_sup.1 (hBle (h2 htT))
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have hr : r ∉ P := fun hr => htA (A.add_mem (Submodule.mem_inf.1 hc).1 ((hxP r).2 hr))
  obtain ⟨s, i, hi, hsi⟩ := hP.exists_inv hr
  have hrx : r • x ∈ T := by
    have h3 := T.sub_mem htT (h1 hc)
    rwa [add_sub_cancel_left] at h3
  have hix : i • x ∈ T := h1 (Submodule.mem_inf.2 ⟨(hxP i).2 hi, B.smul_mem i hx⟩)
  have hxT : x ∈ T := by
    have h4 : x = s • r • x + i • x := by rw [smul_smul, ← add_smul, hsi, one_smul]
    rw [h4]
    exact T.add_mem (T.smul_mem s hrx) hix
  refine le_antisymm h2 (hBle.trans (sup_le h1 ?_))
  rw [Submodule.span_singleton_le_iff_mem]
  exact hxT

open Classical in
open scoped BigOperators in
private lemma toAddSubgroup_inf {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    (A B : Submodule R X) : (A ⊓ B).toAddSubgroup = A.toAddSubgroup ⊓ B.toAddSubgroup := by
  ext; simp

open Classical in
open scoped BigOperators in

theorem _root_.GlobalTheory.FinWeil.adjacent_selfDual_simple : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W → ∀ (A B : Submodule R X), _root_.GlobalTheory.FinWeil.SelfDual γ A → _root_.GlobalTheory.FinWeil.SelfDual γ B → ∀ x ∈ B, ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) → (∀ r : R, r • x ∈ A ↔ r ∈ P) → B ≤ (A ⊓ B) ⊔ Submodule.span R {x} → _root_.GlobalTheory.FinWeil.idx A B = Nat.card (R ⧸ P) ∧ _root_.GlobalTheory.FinWeil.idx B A = Nat.card (R ⧸ P) ∧ (∀ b ∈ B, ∃! q : R ⧸ P, b - (Quotient.out q : R) • x ∈ A) ∧ (∀ T : Submodule R X, A ⊓ B ≤ T → T ≤ B → T ≤ A ∨ T = B) ∧ (∀ T : Submodule R X, A ⊓ B ≤ T → T ≤ A → T ≤ B ∨ T = A) := by
  intro R X M _ _ _ _ _ σ w γ W hW A B hA hB x hx P hP hfin hxP hBle
  have hA' : ∀ y, y ∈ A ↔ ∀ a ∈ A, γ y a = 1 := hA
  have hB' : ∀ y, y ∈ B ↔ ∀ b ∈ B, γ y b = 1 := hB
  have hrep := existsUnique_quotient_sub_smul_mem A B x P hxP hBle
  have hN : Nat.card (R ⧸ P) ≠ 0 := Nat.card_pos.ne'
  have hAB : _root_.GlobalTheory.FinWeil.idx A B = Nat.card (R ⧸ P) := by
    haveI := Fintype.ofFinite (R ⧸ P)
    rw [Nat.card_eq_fintype_card]
    exact (_root_.GlobalTheory.FinWeil.sumOp_eq_sum_transversal hW A B hB (0 : M) (fun a _ => map_zero (W a)) (R ⧸ P)
      (fun q => Quotient.out q • x) (fun q => B.smul_mem _ hx) hrep).2
  have hAB' : A.toAddSubgroup.relIndex B.toAddSubgroup = Nat.card (R ⧸ P) := hAB
  have hBA : B.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (R ⧸ P) := by
    have key := (_root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW B.toAddSubgroup A.toAddSubgroup A.toAddSubgroup
      B.toAddSubgroup (fun a _ => by simpa only [Submodule.mem_toAddSubgroup] using hB' a)
      (fun t ht => by
        simp only [Submodule.mem_toAddSubgroup] at ht ⊢
        rw [hA' t]
        exact ⟨fun h a ha => hW.swap_eq_one (h a ha),
          fun h a ha => hW.swap_eq_one (h a ha)⟩)
      (by rw [hAB']; exact hN)).1
    rw [key, hAB']
  have hdich := le_or_eq_of_inf_le_of_le_of_isMaximal A B x hx P hP hxP hBle
  refine ⟨hAB, hBA, hrep, hdich, ?_⟩
  intro T h1 h2
  by_cases hTB : T ≤ B
  · exact Or.inl hTB
  right
  let T' : Submodule R X :=
    { carrier := {b | b ∈ B ∧ ∀ t ∈ T, γ t b = 1}
      add_mem' := fun {b b'} hb hb' => ⟨B.add_mem hb.1 hb'.1, fun t ht => by
        rw [hW.add_right, hb.2 t ht, hb'.2 t ht, one_mul]⟩
      zero_mem' := ⟨B.zero_mem, fun t _ => hW.zero_right t⟩
      smul_mem' := fun r b hb => ⟨B.smul_mem r hb.1, fun t ht => by
        have h3 := hW.adj (σ r) t b
        rw [hW.sg_sg] at h3
        rw [← h3]
        exact hb.2 _ (T.smul_mem _ ht)⟩ }
  have hmemT' : ∀ b, b ∈ T' ↔ b ∈ B ∧ ∀ t ∈ T, γ t b = 1 := fun b => Iff.rfl
  have hT'1 : A ⊓ B ≤ T' := fun c hc => (hmemT' c).2
    ⟨(Submodule.mem_inf.1 hc).2, fun t ht =>
      hW.iso hA (h2 ht) (Submodule.mem_inf.1 hc).1⟩
  have hT'2 : T' ≤ B := fun b hb => ((hmemT' b).1 hb).1
  rcases hdich T' hT'1 hT'2 with hle | heq
  · have hT'eq : T' = A ⊓ B := le_antisymm (le_inf hle hT'2) hT'1
    have hprod : (A ⊓ B).toAddSubgroup.relIndex T.toAddSubgroup *
        T.toAddSubgroup.relIndex A.toAddSubgroup = Nat.card (R ⧸ P) := by
      rw [AddSubgroup.relIndex_mul_relIndex (A ⊓ B).toAddSubgroup T.toAddSubgroup
        A.toAddSubgroup (fun y hy => h1 hy) (fun y hy => h2 hy),
        toAddSubgroup_inf, AddSubgroup.inf_relIndex_left, hBA]
    have hne : (A ⊓ B).toAddSubgroup.relIndex T.toAddSubgroup ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hprod; exact hN hprod.symm
    have key := (_root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW T'.toAddSubgroup B.toAddSubgroup
      (A ⊓ B).toAddSubgroup T.toAddSubgroup
      (fun b hb => by
        simp only [Submodule.mem_toAddSubgroup] at hb ⊢
        rw [hmemT']
        exact ⟨fun h t ht => hW.swap_eq_one (h.2 t ht),
          fun h => ⟨hb, fun t ht => hW.swap_eq_one (h t ht)⟩⟩)
      (fun t ht => by
        simp only [Submodule.mem_toAddSubgroup, Submodule.mem_inf] at ht ⊢
        rw [hB' t]
        exact ⟨fun h b hb => hW.swap_eq_one (h.2 b hb),
          fun h => ⟨h2 ht, fun b hb => hW.swap_eq_one (h b hb)⟩⟩)
      hne).1
    rw [hT'eq, toAddSubgroup_inf, AddSubgroup.inf_relIndex_right, hAB',
      ← toAddSubgroup_inf] at key
    rw [← key] at hprod
    have hone : T.toAddSubgroup.relIndex A.toAddSubgroup = 1 := by
      have h5 : Nat.card (R ⧸ P) * T.toAddSubgroup.relIndex A.toAddSubgroup =
          Nat.card (R ⧸ P) * 1 := by rw [hprod, mul_one]
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hN) h5
    have hAT := AddSubgroup.relIndex_eq_one.1 hone
    exact le_antisymm h2 (fun a ha => hAT ha)
  · exfalso
    apply hTB
    intro t ht
    rw [hB' t]
    intro b hb
    rw [← heq] at hb
    exact ((hmemT' b).1 hb).2 t ht

end GlobalTheory.FinWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleOfSl2Action
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

private theorem natCast_mul_act_mem_range_intCast (c : ℕ) (z : Fin 2 → ℚ) (δ : SL(2, ℤ))
    (h0 : (c : ℚ) * z 0 ∈ Set.range ((↑) : ℤ → ℚ)) (h1 : (c : ℚ) * z 1 ∈ Set.range ((↑) : ℤ → ℚ))
    (i : Fin 2) : (c : ℚ) * act z δ i ∈ Set.range ((↑) : ℤ → ℚ) := by
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  refine ⟨a * (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 i + b * (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 i, ?_⟩
  simp only [act, Fin.sum_univ_two]
  push_cast
  rw [ha, hb]
  ring

private theorem act_act_inv' (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) : act (act x γ) γ⁻¹ = x := by
  have hd := γ.2
  rw [Matrix.det_fin_two] at hd
  have hq : ((((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
      - (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ)) : ℚ) = 1 := by
    rw [hd]; simp
  push_cast at hq
  funext i
  fin_cases i <;>
    simp [act, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two] <;>
    push_cast
  · linear_combination x 0 * hq
  · linear_combination x 1 * hq

theorem admissible_act_SL2 : ∀ (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)), admitted c x → admitted c (act x γ) := by
  rintro c x γ ⟨h1, h2, h3⟩
  refine ⟨h1, h2, fun ⟨k0, k1⟩ => h3 ?_⟩
  rw [← act_act_inv' x γ]
  exact ⟨natCast_mul_act_mem_range_intCast c _ _ k0 k1 0, natCast_mul_act_mem_range_intCast c _ _ k0 k1 1⟩

end GlobalTheory.Sieg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraNormEqHomogeneousPolynomialInCoordinatesStatement
section
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraNorm_eq_homogeneous_polynomial_in_coordinates : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L],
  ∃ f : MvPolynomial (Fin (Module.finrank K L)) K, f.IsHomogeneous (Module.finrank K L) ∧
    ∀ x : L, Algebra.norm K x = MvPolynomial.eval (fun i => (Module.finBasis K L).repr x i) f := by
  first | exact @GlobalTheory.norm_isHomogeneous_poly_coords | exact GlobalTheory.norm_isHomogeneous_poly_coords | (intros; apply GlobalTheory.norm_isHomogeneous_poly_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApproxPthRootClosedMulDivPowStatement
section
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approxPthRoot_closed_mul_div_pow : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ) (F : Subfield L) (θ : ℝ≥0), θ < 1 → ∀ u u' : L, (∃ w ∈ F, v (u - w ^ p) ≤ θ * v u) → (∃ w ∈ F, v (u' - w ^ p) ≤ θ * v u') → (∃ w ∈ F, v (u * u' - w ^ p) ≤ θ * v (u * u')) ∧ (u' ≠ 0 → ∃ w ∈ F, v (u / u' - w ^ p) ≤ θ * v (u / u')) ∧ ∀ k : ℕ, ∃ w ∈ F, v (u ^ k - w ^ p) ≤ θ * v (u ^ k) := by
  first | exact @GlobalTheory.AlmostEt.approxRoot_closed | exact GlobalTheory.AlmostEt.approxRoot_closed | (intros; apply GlobalTheory.AlmostEt.approxRoot_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphismExtensionUniformStatement
section
open GlobalTheory.K5 Polynomial
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphism_extension_uniform : ∀ (Ω L K : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Field L] [IsAlgClosed L] [Field K] [CharZero K] [Algebra K L] [Algebra.IsAlgebraic K L] (j : Ω →+* L) (s : Ω ≃ₐ[ℚ] Ω), (∀ x : Ω, ∃ g : L ≃ₐ[K] L, g (j x) = j (s x)) → ∃ g : L ≃ₐ[K] L, ∀ x : Ω, g (j x) = j (s x) := by
  first | exact @GlobalTheory.exists_algEquiv_inducing_of_forall_conj | exact GlobalTheory.exists_algEquiv_inducing_of_forall_conj | (intros; apply GlobalTheory.exists_algEquiv_inducing_of_forall_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AutomorphismOnExtensionPointwiseStatement
section
open GlobalTheory.K5 Polynomial
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphism_on_extension_pointwise : ∀ (Ω L K : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [Field L] [IsAlgClosed L] [Field K] [CharZero K] [Algebra K L] [Algebra.IsAlgebraic K L] (j : Ω →+* L) (s : Ω ≃ₐ[ℚ] Ω), (∀ a : Ω, j a ∈ Set.range (algebraMap K L) → s a = a) → ∀ x : Ω, ∃ g : L ≃ₐ[K] L, g (j x) = j (s x) := by
  first | exact @GlobalTheory.exists_algEquiv_apply_eq_of_fixes_preimage_base | exact GlobalTheory.exists_algEquiv_apply_eq_of_fixes_preimage_base | (intros; apply GlobalTheory.exists_algEquiv_apply_eq_of_fixes_preimage_base <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FiniteExtensionLangStatement
section
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFirstChernClass_of_finiteDimensional_of_forms_have_zeros : ∀ (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K],
  (∀ (n r d : ℕ) (f : Fin r → MvPolynomial (Fin n) F), (∀ i, (f i).IsHomogeneous d) → 0 < d → r * d < n →
    ∃ x : Fin n → F, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0) → IsFirstChernClassOfLineBundle K := by
  first | exact @GlobalTheory.is_c1_of_finite_of_tsen_lang_systems | exact GlobalTheory.is_c1_of_finite_of_tsen_lang_systems | (intros; apply GlobalTheory.is_c1_of_finite_of_tsen_lang_systems <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassGroupNthPowerOfCongruentPointsMod
section
open Polynomial

namespace GlobalTheory

theorem classGroup_nthPower_of_codim_one_mod : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ), 1 ≤ N → (∀ P₀ : Ideal A, P₀.IsMaximal → ∀ h₀ : P₀ ∈ nonZeroDivisors (Ideal A), ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal → a ∉ P → ∀ h : P ∈ nonZeroDivisors (Ideal A), ∃ d : ClassGroup A, ClassGroup.mk0 ⟨P, h⟩ = ClassGroup.mk0 ⟨P₀, h₀⟩ * d ^ N) → (∃ f : A, f ≠ 0 ∧ Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N) → ∀ c : ClassGroup A, ∃ d, c = d ^ N := by
  intro k A _ _ _ _ _ _ _ N _hN hyp hf c
  obtain ⟨f, hf0, hfm⟩ := hf
  obtain ⟨_hfin, hmax, hadd, _hle⟩ := GlobalTheory.T.dedekind_finiteType_ideal_codimension k A
  have nz : ∀ I : Ideal A, I ≠ ⊥ → I ∈ nonZeroDivisors (Ideal A) := fun I hI =>
    mem_nonZeroDivisors_of_ne_zero hI
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  have hI0 : (I : Ideal A) ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
  by_cases hex : ∃ P₀ : Ideal A, P₀.IsMaximal ∧ P₀ ≠ ⊥
  swap
  · push_neg at hex
    have htop : (I : Ideal A) = ⊤ := by
      by_contra h
      obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ h
      exact hI0 (le_bot_iff.mp (hex M hM ▸ hIM))
    refine ⟨1, ?_⟩
    have : I = 1 := Subtype.ext (by rw [htop]; exact Ideal.one_eq_top.symm)
    rw [this, map_one, one_pow]
  obtain ⟨P₀, hP₀, hP₀ne⟩ := hex
  let H : Subgroup (ClassGroup A) := (powMonoidHom N : ClassGroup A →* ClassGroup A).range
  let π : ClassGroup A →* ClassGroup A ⧸ H := QuotientGroup.mk' H
  have hπ : ∀ d : ClassGroup A, π (d ^ N) = 1 := fun d =>
    (QuotientGroup.eq_one_iff _).mpr ⟨d, rfl⟩
  let γ : ClassGroup A := ClassGroup.mk0 ⟨P₀, nz P₀ hP₀ne⟩
  have hbot : ¬ (⊥ : Ideal A).IsMaximal := fun h =>
    hP₀ne (h.eq_of_le hP₀.ne_top bot_le).symm
  have hjac : ∀ x : A, x ≠ 0 → ∃ Q : Ideal A, Q.IsMaximal ∧ x ∉ Q := by
    intro x hx
    haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
    have hj : (⊥ : Ideal A).jacobson = ⊥ :=
      IsJacobsonRing.out' _ (Ideal.isPrime_bot).isRadical
    by_contra hne
    push_neg at hne
    apply hx
    have : x ∈ (⊥ : Ideal A).jacobson := by
      rw [Ideal.jacobson]
      exact Submodule.mem_sInf.mpr fun J hJ => hne J hJ.2
    rw [hj] at this
    exact (Submodule.mem_bot A).mp this
  have hmaxcls : ∀ (P : Ideal A) (hP : P.IsMaximal) (hPne : P ≠ ⊥),
      π (ClassGroup.mk0 ⟨P, nz P hPne⟩) = π γ := by
    intro P hP hPne
    obtain ⟨a₀, ha₀, H0⟩ := hyp P₀ hP₀ (nz P₀ hP₀ne)
    obtain ⟨a₁, ha₁, H1⟩ := hyp P hP (nz P hPne)
    obtain ⟨Q, hQ, hQa⟩ := hjac (a₀ * a₁) (mul_ne_zero ha₀ ha₁)
    have hQne : Q ≠ ⊥ := by rintro rfl; exact hbot hQ
    obtain ⟨d, hd⟩ := H0 Q hQ (fun h => hQa (Q.mul_mem_right _ h)) (nz Q hQne)
    obtain ⟨e, he⟩ := H1 Q hQ (fun h => hQa (Q.mul_mem_left _ h)) (nz Q hQne)
    have h1 := congrArg π hd
    have h2 := congrArg π he
    rw [map_mul, hπ, mul_one] at h1 h2
    rw [← h2, h1]
  have hall : ∀ J : Ideal A, ∀ hJ : J ∈ nonZeroDivisors (Ideal A),
      π (ClassGroup.mk0 ⟨J, hJ⟩) = π γ ^ Module.finrank k (A ⧸ J) := by
    intro J
    refine UniqueFactorizationMonoid.induction_on_prime (P := fun J : Ideal A => ∀ hJ : J ∈ nonZeroDivisors (Ideal A),
      π (ClassGroup.mk0 ⟨J, hJ⟩) = π γ ^ Module.finrank k (A ⧸ J)) J ?_ ?_ ?_
    · intro h; exact absurd rfl (nonZeroDivisors.ne_zero h)
    · intro x hx h
      have hx' : x = ⊤ := Ideal.isUnit_iff.mp hx
      subst hx'
      have e1 : (⟨⊤, h⟩ : nonZeroDivisors (Ideal A)) = 1 := Subtype.ext Ideal.one_eq_top.symm
      haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.mpr rfl
      rw [e1, map_one, map_one, Module.finrank_zero_of_subsingleton, pow_zero]
    · intro a p ha hp ih h
      have hpne : p ≠ ⊥ := hp.ne_zero
      have hpmax : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hpne
      have e1 : (⟨p * a, h⟩ : nonZeroDivisors (Ideal A)) = ⟨p, nz p hpne⟩ * ⟨a, nz a ha⟩ := rfl
      rw [e1, map_mul, map_mul, hmaxcls p hpmax hpne, ih (nz a ha), hadd p a hpne ha,
        (hmax p hpmax).1, pow_add, pow_one]
  have hγN : π γ ^ N = 1 := by rw [← map_pow]; exact hπ γ
  have hspan : Ideal.span {f} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hf0
  have hγ1 : π γ = 1 := by
    have e := hall _ (nz _ hspan)
    have e0 : ClassGroup.mk0 (⟨Ideal.span {f}, nz _ hspan⟩ : nonZeroDivisors (Ideal A)) = 1 :=
      (ClassGroup.mk0_eq_one_iff _).mpr ⟨⟨f, rfl⟩⟩
    rw [e0, map_one] at e
    calc π γ = π γ ^ (1 % N) := by rw [← pow_eq_pow_mod 1 hγN, pow_one]
      _ = π γ ^ (Module.finrank k (A ⧸ Ideal.span {f}) % N) := by rw [hfm]
      _ = 1 := by rw [← pow_eq_pow_mod _ hγN, ← e]
  have hc := hall I.1 I.2
  rw [hγ1, one_pow] at hc
  have hmem : ClassGroup.mk0 I ∈ H := (QuotientGroup.eq_one_iff _).mp hc
  obtain ⟨d, hd⟩ := hmem
  exact ⟨d, hd.symm⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmValuesExponentLogSumLeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmValues_exponent_log_sum_le : Formalism.PairingDivisionLocalBalance.CESum := by
  first | exact @GlobalTheory.dividedPowerValuations_cESum | exact GlobalTheory.dividedPowerValuations_cESum | (intros; apply GlobalTheory.dividedPowerValuations_cESum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmValuesMinPadicValBoundStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedPowerValuations_minVal : Formalism.PairingDivisionLocalBalance.MinVal := by
  first | exact @GlobalTheory.cmValues_minPadicVal_bound | exact GlobalTheory.cmValues_minPadicVal_bound | (intros; apply GlobalTheory.cmValues_minPadicVal_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CochainCoboundaryProdHomIdentitiesStatement
section
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eta_one_conj_mul_of_cup_coboundary : ∀ (Γ : Type) [Group Γ] (N : ℕ) (x y : Γ →* Multiplicative (ZMod N)) (η : Γ → ZMod N),
  (∀ g h, (x g).toAdd * (y h).toAdd = η h - η (g * h) + η g) →
  η 1 = 0 ∧ (∀ g n, η (g * n * g⁻¹) = η n + (x n).toAdd * (y g).toAdd - (x g).toAdd * (y n).toAdd) ∧
  (∀ m n, (x m).toAdd = 0 → η (m * n) = η m + η n) := by
  first | exact @GlobalTheory.cochain_coboundary_prod_hom_identities | exact GlobalTheory.cochain_coboundary_prod_hom_identities | (intros; apply GlobalTheory.cochain_coboundary_prod_hom_identities <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEqZeroOfExpDecayOfIntegralIdentityStatement
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_eq_zero_of_exp_decay_of_integral_identity : ∀ (v : ℝ → ℂ) (K c : ℂ) (C α β : ℝ) (w : ℕ), 1 ≤ w → 0 < α → 0 < β → K ≠ 0 → (∀ y : ℝ, 0 < y → ‖v y‖ ≤ C * y ^ ((w : ℝ) / 2) * Real.exp (-α * y)) → (∀ a b : ℝ, 0 < a → a ≤ b → v b - v a = K * c * ∫ y in a..b, (y : ℂ) ^ w * (Real.exp (-β * y) : ℂ)) → c = 0 := by
  first | exact @GlobalTheory.ode_coeff_zero_of_decay_ends | exact GlobalTheory.ode_coeff_zero_of_decay_ends | (intros; apply GlobalTheory.ode_coeff_zero_of_decay_ends <;> assumption)
end

