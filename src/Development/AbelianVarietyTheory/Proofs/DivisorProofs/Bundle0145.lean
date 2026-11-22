import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0038
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroMinorOfRankStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_minor_of_rank : ∀ (k : Type) [Field k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ρ : ℕ) (Y : Matrix A D k), ρ ≤ Y.rank → ∃ S : Fin ρ → A, ∃ τ : Fin ρ → D, (Y.submatrix S τ).det ≠ 0 := by
  first | exact @GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank | exact GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank | (intros; apply GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderContainingIntegers
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_order_containing_integers : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] (OB : Subring B), Module.Finite ℤ OB →
    (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ OB) →
    ∃ Λ : Subring B, OB ≤ Λ ∧ (∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) ∧
      Module.Finite ℤ Λ ∧ ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Λ, (N : B) * x ∈ OB := by
  first | (exact @GlobalTheory.exists_order_integers_mul_finite_index) | (exact GlobalTheory.exists_order_integers_mul_finite_index) | (intros; apply GlobalTheory.exists_order_integers_mul_finite_index  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalEigenIdempotentsOfSeparabilityStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_eigen_idempotents_of_separability : ∀ (R C K : Type) [CommRing R] [CommRing C] [CommRing K] (tR : R →+* C) (a : ℕ) (t : Fin a → (K →+* R)), (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → ∀ (N : ℤ) (k : ℕ) (u v : Fin k → K), ∑ j, u j * v j = (N : K) → (∀ c : K, ∑ j, (c * u j) ⊗ₜ[ℤ] v j = ∑ j, u j ⊗ₜ[ℤ] (v j * c)) → IsUnit (N : C) → ∀ (H : Type*) [AddCommGroup H] [Module C H] (ρF : K →+* Module.End C H), ∃ φ : Fin a → Module.End C H, (∀ i c, ρF c * φ i = tR (t i c) • φ i) ∧ (∀ i j, φ i * φ j = if i = j then φ i else 0) ∧ (∀ g : Module.End C H, (∀ c, g * ρF c = ρF c * g) → ∀ i, g * φ i = φ i * g) ∧ (∀ F : Submodule C H, (∀ c, ∀ x ∈ F, ρF c x ∈ F) → ∀ i, ∀ x ∈ F, φ i x ∈ F) ∧ (∀ F : Submodule C H, (∀ c, ∀ x ∈ F, ρF c x ∈ F) → ∀ i w, (∀ c, ρF c w - tR (t i c) • w ∈ F) → ∀ j, φ j w - (if j = i then w else 0) ∈ F) := by
  first | exact @GlobalTheory.lie_idempotents | exact GlobalTheory.lie_idempotents | (intros; apply GlobalTheory.lie_idempotents <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyEntriesConjLeftRightMulStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_poly_entries_conj_left_right_mul : ∀ (n : ℕ) (a b : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ), ∃ Q : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, Q.totalDegree ≤ P.totalDegree ∧ ∀ g : Matrix (Fin n) (Fin n) ℂ, MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (a * g * b) z.1 z.2) (fun z : Fin n × Fin n => star ((a * g * b) z.1 z.2))) P = MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (g) z.1 z.2) (fun z : Fin n × Fin n => star ((g) z.1 z.2))) Q := by
  first | exact @GlobalTheory.PolyEntryMul.main | exact GlobalTheory.PolyEntryMul.main | (intros; apply GlobalTheory.PolyEntryMul.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosMulExtendIntLinearFormStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_mul_extend_int_linearForm' : ∀ (F : Type) [AddCommGroup F] [Module.Free ℤ F] [Module.Finite ℤ F] (P : Submodule ℤ F) (f : P →ₗ[ℤ] ℤ), ∃ c : ℤ, 0 < c ∧ ∃ lam : F →ₗ[ℤ] ℤ, ∀ x : P, lam x = c * f x := by
  first | exact @GlobalTheory.exists_pos_mul_extend_int_linearForm | exact GlobalTheory.exists_pos_mul_extend_int_linearForm | (intros; apply GlobalTheory.exists_pos_mul_extend_int_linearForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosNatSmulMemOfFgAndSpanningLattice
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem exists_pos_nat_smul_mem_of_fg_of_span_eq_top :
    ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (Λ Λ' : Submodule (𝓞 E) (Fin r → E)),
      Λ'.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ →
        ∃ n : ℕ, 0 < n ∧ ∀ v ∈ Λ', (n : E) • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.DenominatorExistence.main
  | exact _root_.GlobalTheory.DenominatorExistence.main
  | (apply _root_.GlobalTheory.DenominatorExistence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenominatorExistence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenominatorExistence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenominatorExistence.main ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosNatSmulMemOfSpanningNumberFieldLattice
section
open NumberField

namespace GlobalTheory

theorem exists_pos_nat_smul_mem_of_span_eq_top (E : Type) [Field E] [NumberField E] (r : ℕ)
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E))
    (h : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (v : Fin r → E) :
    ∃ q : ℕ, 0 < q ∧ (q : E) • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.NatMultipleIntegral.exists_nat_smul_mem
  | exact _root_.GlobalTheory.NatMultipleIntegral.exists_nat_smul_mem
  | (apply _root_.GlobalTheory.NatMultipleIntegral.exists_nat_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMultipleIntegral.exists_nat_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMultipleIntegral.exists_nat_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMultipleIntegral.exists_nat_smul_mem ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowKillsOnCompactOfLocalStatement
section
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_kills_on_compact_of_local : ∀ (S : Scheme.{0}) (Φ : ∀ (T : Scheme.{0}), (T ⟶ S) → Prop) (W : S.Opens), IsCompact (W : Set S) → ∀ (s c : Γ(S, W)), (∀ y ∈ W, ∃ (V : S.Opens) (hV : V ≤ W), y ∈ V ∧ ∃ n : ℕ, ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app V).hom ((S.presheaf.map (homOfLE hV).op).hom (s ^ n * c)) = 0) → ∃ n : ℕ, ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app W).hom (s ^ n * c) = 0 := by
  first | exact @GlobalTheory.pow_kills_on_compact_of_local | exact GlobalTheory.pow_kills_on_compact_of_local | (intros; apply GlobalTheory.pow_kills_on_compact_of_local; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulAppEqZeroNearOfRepresentedStatement
section
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_mul_app_eq_zero_near_of_represented' : ∀ (S : Scheme.{0}) (Φ : ∀ (T : Scheme.{0}), (T ⟶ S) → Prop), (∀ (T T' : Scheme.{0}) (t : T ⟶ S) (u : T' ⟶ T), Φ T t → Φ T' (u ≫ t)) → ∀ (U : S.Opens) (Z : Scheme.{0}) (i : Z ⟶ U), IsClosedImmersion i → (∀ (T : Scheme.{0}) (t : T ⟶ U), Φ T (t ≫ U.ι) ↔ ∃ z : T ⟶ Z, z ≫ i = t) → ∀ (W : S.Opens) (s c : Γ(S, W)), (∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app (S.basicOpen s)).hom ((S.presheaf.map (homOfLE (S.basicOpen_le s)).op).hom c) = 0) → ∀ y : S, y ∈ U → y ∈ W → ∃ (V : S.Opens) (hV : V ≤ W), y ∈ V ∧ ∃ n : ℕ, ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app V).hom ((S.presheaf.map (homOfLE hV).op).hom (s ^ n * c)) = 0 := by
  first | exact @GlobalTheory.exists_pow_mul_app_eq_zero_near_of_represented | exact GlobalTheory.exists_pow_mul_app_eq_zero_near_of_represented | (intros; apply GlobalTheory.exists_pow_mul_app_eq_zero_near_of_represented; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulMemAdjoinOfLocalizationAwayStatement
section
open Algebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_mul_mem_adjoin_of_localizationAway : ∀ {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A'], ∀ (T : Set A) (b : A), algebraMap A A' b ∈ Algebra.adjoin R' (algebraMap A A' '' T) → ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Algebra.adjoin R T := by
  first | exact @GlobalTheory.adjoin_mem_of_away_localization' | exact GlobalTheory.adjoin_mem_of_away_localization' | (intros; apply GlobalTheory.adjoin_mem_of_away_localization' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
section
open Polynomial GlobalTheory.EtC

namespace GlobalTheory

theorem exists_algebraMap_sub_mem_of_isMaximal_of_isAlgClosed (k B : Type) [Field k] [IsAlgClosed k]
    [CommRing B] [Algebra k B] [Algebra.FiniteType k B] (P : Ideal B) [hP : P.IsMaximal] (b : B) :
    ∃ c : k, b - algebraMap k B c ∈ P := by
  letI := Ideal.Quotient.field P
  haveI : Module.Finite k (B ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ P)
  let φ : (B ⧸ P) →ₐ[k] k := IsAlgClosed.lift
  refine ⟨φ (Ideal.Quotient.mk P b), ?_⟩
  have h : algebraMap k (B ⧸ P) (φ (Ideal.Quotient.mk P b)) = Ideal.Quotient.mk P b := by
    apply φ.toRingHom.injective
    simp
  have h2 : Ideal.Quotient.mk P (algebraMap k B (φ (Ideal.Quotient.mk P b))) =
      algebraMap k (B ⧸ P) (φ (Ideal.Quotient.mk P b)) := rfl
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h2, h, sub_self]

theorem exists_pow_sub_mem_pow_of_isMaximal_of_isAlgClosed (k B : Type) [Field k] [IsAlgClosed k]
    [CommRing B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ) (hq : IsUnit (q : k))
    (P : Ideal B) [hP : P.IsMaximal] (b : B) (hb : b ∉ P) :
    ∀ m : ℕ, ∃ r : B, b - r ^ q ∈ P ^ (m + 1) := by
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp at hq
    · exact h
  have hqB : IsUnit (q : B) := by
    have := hq.map (algebraMap k B); simpa using this
  intro m
  induction m with
  | zero =>
    obtain ⟨c, hc⟩ := exists_algebraMap_sub_mem_of_isMaximal_of_isAlgClosed k B P b
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq c hq0
    refine ⟨algebraMap k B z, ?_⟩
    rw [← map_pow, hz]; simpa using hc
  | succ m ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨e, he⟩ : ∃ e, e = b - r ^ q := ⟨_, rfl⟩
    rw [← he] at hr
    have hrP : r ∉ P := by
      intro h
      apply hb
      have h1 : r ^ q ∈ P := P.pow_mem_of_mem h q hq0
      have h2 : e ∈ P := Ideal.pow_le_self (Nat.succ_ne_zero m) hr
      have : b = e + r ^ q := by rw [he]; ring
      rw [this]; exact P.add_mem h2 h1
    have hderP : (q : B) * r ^ (q - 1) ∉ P := by
      intro h
      rcases hP.isPrime.mem_or_mem h with h | h
      · exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P h hqB)
      · exact hrP (hP.isPrime.mem_of_pow_mem _ h)
    obtain ⟨w, i, hi, hw⟩ := hP.exists_inv hderP
    obtain ⟨t, ht⟩ := binomExpansion (X ^ q : B[X]) r (e * w)
    simp [derivative_X_pow] at ht
    refine ⟨r + e * w, ?_⟩
    have key : b - (r + e * w) ^ q = e * i - t * w ^ 2 * e ^ 2 := by
      rw [ht]; linear_combination (-e) * hw - he
    rw [key]
    refine Ideal.sub_mem _ ?_ ?_
    · rw [pow_succ]; exact Ideal.mul_mem_mul hr hi
    · apply Ideal.mul_mem_left
      have h3 : e ^ 2 ∈ (P ^ (m + 1)) ^ 2 := Ideal.pow_mem_pow hr 2
      rw [← pow_mul] at h3
      exact Ideal.pow_le_pow_right (by omega) h3

theorem exists_pow_sub_mem_span_of_isUnit_mod_of_isAlgClosed : ∀ (k B : Type) [Field k] [IsAlgClosed k]
    [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ),
    IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ b c : B, b * c - 1 ∈ Ideal.span {f} →
      ∃ r : B, b - r ^ q ∈ Ideal.span {f} := by
  intro k B _ _ _ _ _ _ q hq f hf b c hbc
  classical
  have hI : Ideal.span {f} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hf
  have hroot : ∀ P : (UniqueFactorizationMonoid.factors (Ideal.span {f})).toFinset, ∃ r : B,
      b - r ^ q ∈ (P : Ideal B) ^ Multiset.count (P : Ideal B)
        (UniqueFactorizationMonoid.factors (Ideal.span {f})) := by
    intro P
    have hmem := Multiset.mem_toFinset.mp P.prop
    have hprime : Prime (P : Ideal B) := UniqueFactorizationMonoid.prime_of_factor _ hmem
    have hne : (P : Ideal B) ≠ ⊥ := hprime.ne_zero
    haveI hmax : (P : Ideal B).IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hne
    have hle : Ideal.span {f} ≤ (P : Ideal B) :=
      Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_factors hmem)
    have hb : b ∉ (P : Ideal B) := by
      intro h
      apply hmax.ne_top
      rw [Ideal.eq_top_iff_one]
      have h1 := hle hbc
      have : (1 : B) = b * c - (b * c - 1) := by ring
      rw [this]; exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ h) h1
    obtain ⟨r, hr⟩ := exists_pow_sub_mem_pow_of_isMaximal_of_isAlgClosed k B q hq (P : Ideal B) b hb
      (Multiset.count (P : Ideal B) (UniqueFactorizationMonoid.factors (Ideal.span {f})))
    exact ⟨r, Ideal.pow_le_pow_right (Nat.le_succ _) hr⟩
  choose r hr using hroot
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective
    ((IsDedekindDomain.quotientEquivPiFactors hI).symm (fun P => Ideal.Quotient.mk _ (r P)))
  refine ⟨s, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply (IsDedekindDomain.quotientEquivPiFactors hI).injective
  rw [map_zero]
  funext P
  have h1 := congrFun (congrArg (IsDedekindDomain.quotientEquivPiFactors hI) hs) P
  rw [RingEquiv.apply_symm_apply, IsDedekindDomain.quotientEquivPiFactors_mk] at h1
  simp only at h1
  rw [IsDedekindDomain.quotientEquivPiFactors_mk]
  show Ideal.Quotient.mk _ (b - s ^ q) = 0
  rw [map_sub, map_pow, h1, ← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact hr P

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPresentationMatrixOfProjectiveBaseChangeStatement
section
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_presentation_matrix_of_projective_baseChange : ∀ (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module R M] (n m : ℕ) (π : (Fin n → R) →ₗ[R] M), Function.Surjective π →
    ∀ (r : Fin m → Fin n → R), Submodule.span R (Set.range r) = LinearMap.ker π →
    Module.Projective B (B ⊗[R] M) →
    ∃ (v : Fin n → Fin n → B) (w : Fin n → Fin m → B),
    (∀ b l, ∑ a, algebraMap R B (r b a) * v a l = 0) ∧
    (∀ a l, v a l = (if a = l then 1 else 0) + ∑ b, w a b * algebraMap R B (r b l)) := by
  first | (exact @GlobalTheory.projective_baseChange_presentation_matrix) | (exact GlobalTheory.projective_baseChange_presentation_matrix) | (intros; apply GlobalTheory.projective_baseChange_presentation_matrix <;> assumption)
end

