import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeierstrassPOddMulSubTwoTorsionProduct

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryIntegralOfSplitPlaceComponent
section
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

namespace GlobalTheory.LevNorm

section Idem

variable {R : Type} [CommRing R] {n : ℕ}

theorem matrix_mul_orthogonal_three_idempotents_smul (a b c : R) (hab : a * b = 0) (hac : a * c = 0) (hbc : b * c = 0) (ha : a * a = a)
    (hb : b * b = b) (hc : c * c = c) (M₁ M₂ M₃ N₁ N₂ N₃ : Matrix (Fin n) (Fin n) R) :
    (a • M₁ + b • M₂ + c • M₃) * (a • N₁ + b • N₂ + c • N₃) = a • (M₁ * N₁) + b • (M₂ * N₂) + c • (M₃ * N₃) := by
  have hba : b * a = 0 := by rw [mul_comm]; exact hab
  have hca : c * a = 0 := by rw [mul_comm]; exact hac
  have hcb : c * b = 0 := by rw [mul_comm]; exact hbc
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, hab, hac, hbc, hba, hca, hcb,
    ha, hb, hc, zero_smul, add_zero, zero_add]

theorem cT_smul' (τ : R →+* R) (a : R) (M : Matrix (Fin n) (Fin n) R) : cT τ (a • M) = τ a • cT τ M := by
  ext i j; simp [cT]

theorem cT_add' (τ : R →+* R) (M N : Matrix (Fin n) (Fin n) R) : cT τ (M + N) = cT τ M + cT τ N := by
  ext i j; simp [cT]

theorem cT_cT' (τ : R →+* R) (hτ : ∀ x, τ (τ x) = x) (M : Matrix (Fin n) (Fin n) R) : cT τ (cT τ M) = M := by
  ext i j; simp [cT, hτ]

theorem map_idem3 (a b c : R) (X Y : Matrix (Fin n) (Fin n) R) {T : Type} [CommRing T] (f : R →+* T) :
    (a • X + b • Y + c • (1 : Matrix (Fin n) (Fin n) R)).map f
      = f a • X.map f + f b • Y.map f + f c • (1 : Matrix (Fin n) (Fin n) T) := by
  ext i j; simp [Matrix.one_apply]; split_ifs <;> simp

theorem idem_split_inv (τ : R →+* R) (a b : R) (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0)
    (G Gi X Xi : Matrix (Fin n) (Fin n) R) (hG : G * Gi = 1) (hGi : Gi * G = 1) (hX : X * Xi = 1) :
    (a • X + b • (Gi * cT τ Xi * G) + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R)) *
      (a • Xi + b • (Gi * cT τ X * G) + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R)) = 1 := by
  have hac : a * (1 - a - b) = 0 := by linear_combination -ha - hab
  have hbc : b * (1 - a - b) = 0 := by linear_combination -hb - hab
  have hc : (1 - a - b) * (1 - a - b) = 1 - a - b := by linear_combination ha + hb + 2 * hab
  rw [matrix_mul_orthogonal_three_idempotents_smul a b _ hab hac hbc ha hb hc]
  have h1 : Gi * cT τ Xi * G * (Gi * cT τ X * G) = 1 := by
    calc _ = Gi * (cT τ Xi * (G * Gi) * cT τ X) * G := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hG, Matrix.mul_one, ← cT_mul, hX, cT_one, Matrix.mul_one, hGi]
  rw [hX, h1, Matrix.mul_one, ← add_smul, ← add_smul, show a + b + (1 - a - b) = 1 by ring, one_smul]

theorem idem_split_unitary (τ : R →+* R) (hτ : ∀ x, τ (τ x) = x) (a b : R) (ha : a * a = a) (hb : b * b = b)
    (hab : a * b = 0) (hτa : τ a = b)
    (G Gi X Xi : Matrix (Fin n) (Fin n) R) (hG : G * Gi = 1) (hXi : Xi * X = 1) (hGh : cT τ G = G) :
    cT τ (a • X + b • (Gi * cT τ Xi * G) + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R)) * G *
      (a • X + b • (Gi * cT τ Xi * G) + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R)) = G := by
  have hac : a * (1 - a - b) = 0 := by linear_combination -ha - hab
  have hbc : b * (1 - a - b) = 0 := by linear_combination -hb - hab
  have hc : (1 - a - b) * (1 - a - b) = 1 - a - b := by linear_combination ha + hb + 2 * hab
  have hτb : τ b = a := by rw [← hτa, hτ]
  have hτc : τ (1 - a - b) = 1 - a - b := by rw [map_sub, map_sub, map_one, hτa, hτb]; ring
  have hGc : cT τ Gi * G = 1 := by
    have : cT τ Gi * cT τ G = 1 := by rw [← cT_mul, hG, cT_one]
    rwa [hGh] at this
  have hct : cT τ (a • X + b • (Gi * cT τ Xi * G) + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R))
      = a • (G * (Xi * cT τ Gi)) + b • cT τ X + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [cT_add', cT_add', cT_smul', cT_smul', cT_smul', hτa, hτb, hτc, cT_one, cT_mul, cT_mul, hGh, cT_cT' τ hτ]
    abel
  have hGs : G = a • G + b • G + (1 - a - b) • G := by
    rw [← add_smul, ← add_smul, show a + b + (1 - a - b) = 1 by ring, one_smul]
  rw [hct, show (a • (G * (Xi * cT τ Gi)) + b • cT τ X + (1 - a - b) • (1 : Matrix (Fin n) (Fin n) R)) * G
      = a • (G * (Xi * cT τ Gi) * G) + b • (cT τ X * G) + (1 - a - b) • (1 * G) by
    simp only [Matrix.add_mul, Matrix.smul_mul]]
  rw [matrix_mul_orthogonal_three_idempotents_smul a b _ hab hac hbc ha hb hc]
  have e1 : G * (Xi * cT τ Gi) * G * X = G := by
    calc _ = G * (Xi * (cT τ Gi * G) * X) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hGc, Matrix.mul_one, hXi, Matrix.mul_one]
  have e2 : cT τ X * G * (Gi * cT τ Xi * G) = G := by
    calc _ = cT τ X * (G * Gi) * cT τ Xi * G := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hG, Matrix.mul_one, ← cT_mul, hXi, cT_one, Matrix.one_mul]
  rw [e1, e2, Matrix.one_mul, Matrix.mul_one, ← hGs]

end Idem

end GlobalTheory.LevNorm

namespace GlobalTheory.LevNorm

theorem exists_unitary_int_of_component {A : Type} [CommRing A] {S : Subring A} {P : Type} {k : P → Type}
    [∀ Q, Field (k Q)] {r : ∀ Q, S →+* k Q} (Z : PlaceSys A S P k r) (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a)
    (hS : ∀ a ∈ S, σ a ∈ S) (n : ℕ) (G : GL (Fin n) S)
    (hG : cT σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)
      = ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A))
    (Q Q' : P) (hQ : σ (Z.e Q) = Z.e Q') (hne : Q ≠ Q') (y : GL (Fin n) (Z.O Q)) :
    ∃ u : GL (Fin n) S, bc S.subtype u ∈ UJ σ ((bc S.subtype G : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) ∧
      bc (Z.pO Q) u = y ∧ ∀ Q'', Q'' ≠ Q → Q'' ≠ Q' → bc (Z.pO Q'') u = 1 := by
  obtain ⟨x, hx1, hx2⟩ := Z.gl_single Q (bc (Z.O Q).subtype y)
  obtain ⟨X, hX⟩ := Z.gl_int (x := x) fun R => by
    by_cases h : R = Q
    · subst h; exact ⟨y, hx1.symm⟩
    · exact ⟨1, by rw [map_one, hx2 R h]⟩
  have hcomp : ∀ R, bc (Z.O R).subtype (bc (Z.pO R) X) = bc (Z.p R) x := fun R => by
    rw [← hX]; rfl
  have binj : ∀ R, Function.Injective (bc (n := Fin n) (Z.O R).subtype) := fun R g h e =>
    Units.ext (Matrix.map_injective Subtype.val_injective (congrArg Units.val e))
  have hXQ : bc (Z.pO Q) X = y := binj Q (by rw [hcomp, hx1])
  have hXR : ∀ R, R ≠ Q → bc (Z.pO R) X = 1 := fun R h => binj R (by rw [hcomp, hx2 R h, map_one])
  let τ : S →+* S := σ.restrict S S hS
  have hτv : ∀ s : S, (τ s : A) = σ s := fun s => rfl
  have hτ : ∀ s, τ (τ s) = s := fun s => Subtype.ext (by rw [hτv, hτv, hσ])
  let a : S := ⟨Z.e Q, Z.e_mem Q⟩
  let b : S := ⟨Z.e Q', Z.e_mem Q'⟩
  have ha : a * a = a := Subtype.ext (Z.e_idem Q)
  have hb : b * b = b := Subtype.ext (Z.e_idem Q')
  have hab : a * b = 0 := Subtype.ext (by
    show Z.e Q * Z.e Q' = 0
    refine Z.ext _ fun R => ?_
    rw [map_mul]
    by_cases h : R = Q
    · subst h; rw [Z.e_ne Q' R hne, mul_zero]
    · rw [Z.e_ne Q R h, zero_mul])
  have hτa : τ a = b := Subtype.ext hQ
  have hmap : ∀ M : Matrix (Fin n) (Fin n) S, (cT τ M).map S.subtype = cT σ (M.map S.subtype) := fun M => by
    ext i j; rfl
  have hGh : cT τ (G : Matrix (Fin n) (Fin n) S) = G :=
    Matrix.map_injective (f := (S.subtype : S → A)) S.subtype_injective ((hmap _).trans hG)
  let uM : Matrix (Fin n) (Fin n) S := a • (X : Matrix (Fin n) (Fin n) S) +
    b • (((G⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) * cT τ ((X⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) * G) +
    (1 - a - b) • (1 : Matrix (Fin n) (Fin n) S)
  let vM : Matrix (Fin n) (Fin n) S := a • ((X⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) +
    b • (((G⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) * cT τ (X : Matrix (Fin n) (Fin n) S) * G) +
    (1 - a - b) • (1 : Matrix (Fin n) (Fin n) S)
  let u : GL (Fin n) S := ⟨uM, vM,
    idem_split_inv τ a b ha hb hab _ _ _ _ (Units.mul_inv G) (Units.inv_mul G) (Units.mul_inv X),
    idem_split_inv τ a b ha hb hab _ _ _ _ (Units.mul_inv G) (Units.inv_mul G) (Units.inv_mul X)⟩
  have hcompU : ∀ R, ((bc (Z.pO R) u : GL (Fin n) (Z.O R)) : Matrix (Fin n) (Fin n) (Z.O R)) =
      Z.pO R a • (X : Matrix (Fin n) (Fin n) S).map (Z.pO R) + Z.pO R b • _ + Z.pO R (1 - a - b) • 1 :=
    fun R => map_idem3 _ _ _ _ _ _
  refine ⟨u, ?_, ?_, ?_⟩
  · show cT σ (uM.map S.subtype) * (G : Matrix (Fin n) (Fin n) S).map S.subtype * uM.map S.subtype
      = (G : Matrix (Fin n) (Fin n) S).map S.subtype
    rw [← hmap, ← Matrix.map_mul, ← Matrix.map_mul,
      idem_split_unitary τ hτ a b ha hb hab hτa _ _ _ _ (Units.mul_inv G) (Units.inv_mul X) hGh]
  · have hpa : Z.pO Q a = 1 := Subtype.ext (Z.e_self Q)
    have hpb : Z.pO Q b = 0 := Subtype.ext (Z.e_ne Q' Q hne)
    refine Units.ext ?_
    rw [hcompU, map_sub, map_sub, map_one, hpa, hpb]
    simp only [one_smul, zero_smul, add_zero, sub_self]
    exact congrArg Units.val hXQ
  · intro R h1 h2
    have hpa : Z.pO R a = 0 := Subtype.ext (Z.e_ne Q R h1)
    have hpb : Z.pO R b = 0 := Subtype.ext (Z.e_ne Q' R h2)
    refine Units.ext ?_
    rw [hcompU, map_sub, map_sub, map_one, hpa, hpb]
    simp

end GlobalTheory.LevNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsScalarMulIntegralOfConjIntegralGenerators
section
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

noncomputable section
namespace GlobalTheory.ScalConj

theorem single_conj_apply {K : Type} [Field K] {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) (a b i j : Fin n) :
    (A * (Matrix.single a b (1 : K) : Matrix (Fin n) (Fin n) K) * B) i j = A i a * B b j := by
  rw [Matrix.mul_apply]
  simp [Matrix.mul_apply, Matrix.single_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and]

def conjInt {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (m : GL (Fin n) K) :
    Subalgebra O (Matrix (Fin n) (Fin n) O) where
  carrier := {X | ∃ Y : Matrix (Fin n) (Fin n) O,
    Y.map O.subtype = (m : Matrix (Fin n) (Fin n) K) * X.map O.subtype * ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
  mul_mem' := by
    rintro X X' ⟨Y, hY⟩ ⟨Y', hY'⟩
    refine ⟨Y * Y', ?_⟩
    rw [Matrix.map_mul, Matrix.map_mul, hY, hY']
    have : ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (m : Matrix (Fin n) (Fin n) K) = 1 := Units.inv_mul m
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), this, Matrix.one_mul]
  add_mem' := by
    rintro X X' ⟨Y, hY⟩ ⟨Y', hY'⟩
    refine ⟨Y + Y', ?_⟩
    rw [Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), hY, hY', Matrix.mul_add, Matrix.add_mul]
  algebraMap_mem' := by
    intro r
    refine ⟨algebraMap O _ r, ?_⟩
    have h : (algebraMap O (Matrix (Fin n) (Fin n) O) r).map O.subtype = (r : K) • (1 : Matrix (Fin n) (Fin n) K) := by
      ext i j
      by_cases h : i = j
      · subst h; simp [Matrix.algebraMap_matrix_apply]
      · simp [Matrix.algebraMap_matrix_apply, h, Matrix.one_apply_ne h]
    rw [h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.mul_inv]

theorem single_map_subtype {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (a b : Fin n) :
    (Matrix.single a b (1 : O)).map O.subtype = (Matrix.single a b (1 : K) : Matrix (Fin n) (Fin n) K) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem entry_mul_inv_entry_mem {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (m : GL (Fin n) K)
    (T : Set (GL (Fin n) O))
    (hT : Algebra.adjoin O ((fun x : GL (Fin n) O => (x : Matrix (Fin n) (Fin n) O)) '' T) = ⊤)
    (hc : ∀ x ∈ T, ∃ x' : GL (Fin n) O, bc O.subtype x' = m * bc O.subtype x * m⁻¹) (i a b j : Fin n) :
    (m : Matrix (Fin n) (Fin n) K) i a * ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) b j ∈ O := by
  have hle : Algebra.adjoin O ((fun x : GL (Fin n) O => (x : Matrix (Fin n) (Fin n) O)) '' T) ≤ conjInt O m := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨x', hx'⟩ := hc x hx
    exact ⟨x', congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hx'⟩
  rw [hT] at hle
  obtain ⟨Y, hY⟩ := hle (Algebra.mem_top : Matrix.single a b (1 : O) ∈ (⊤ : Subalgebra O (Matrix (Fin n) (Fin n) O)))
  have h := congrFun (congrFun hY i) j
  rw [single_map_subtype, single_conj_apply] at h
  rw [← h]
  exact (Y i j).2

theorem isScal_of_conj (K : Type) [Field K] (O : ValuationSubring K) (n : ℕ) (m : GL (Fin n) K)
    (T : Set (GL (Fin n) O))
    (hT : Algebra.adjoin O ((fun x : GL (Fin n) O => (x : Matrix (Fin n) (Fin n) O)) '' T) = ⊤)
    (hc : ∀ x ∈ T, ∃ x' : GL (Fin n) O, bc O.subtype x' = m * bc O.subtype x * m⁻¹) : IsScal O m := by
  have H := entry_mul_inv_entry_mem O m T hT hc
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, 1, Subsingleton.elim _ _⟩
  set M : Matrix (Fin n) (Fin n) K := (m : Matrix (Fin n) (Fin n) K) with hM
  set N : Matrix (Fin n) (Fin n) K := ((m⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hN
  have hMN : M * N = 1 := Units.mul_inv m
  obtain ⟨⟨i0, a0⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
    (fun p => O.valuation (M p.1 p.2)) ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
  set c := M i0 a0 with hcdef
  have hc0 : c ≠ 0 := by
    intro h0
    have hz : ∀ i a, M i a = 0 := fun i a => by
      have h1 := hmax (i, a) (Finset.mem_univ _)
      simp only [h0, map_zero] at h1
      exact (Valuation.zero_iff _).1 (le_antisymm h1 zero_le')
    have h1 := congrFun (congrFun hMN ⟨0, hn⟩) ⟨0, hn⟩
    simp [Matrix.mul_apply, hz] at h1
  have hv : 0 < O.valuation c := (Valuation.pos_iff _).2 hc0
  have hy : ∀ i a, c⁻¹ * M i a ∈ O := fun i a => by
    rw [← O.valuation_le_one_iff, map_mul, map_inv₀]
    exact (inv_mul_le_one₀ hv).2 (hmax (i, a) (Finset.mem_univ _))
  have hz : ∀ b j, c * N b j ∈ O := fun b j => H i0 a0 b j
  let Y : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, hy i j⟩
  let Z : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, hz i j⟩
  have hYm : Y.map O.subtype = c⁻¹ • M := by ext i j; rfl
  have hZm : Z.map O.subtype = c • N := by ext i j; rfl
  have inj : Function.Injective fun X : Matrix (Fin n) (Fin n) O => X.map O.subtype :=
    Matrix.map_injective (Subtype.val_injective)
  have key : ∀ {A B : Matrix (Fin n) (Fin n) K}, A * B = 1 → (c⁻¹ • A) * (c • B) = 1 := fun {A B} h => by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul, h]
  have hNM : N * M = 1 := Units.inv_mul m
  have e1 : Y * Z = 1 := inj (by
    show (Y * Z).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hYm, hZm, key hMN])
  have e2 : Z * Y = 1 := inj (by
    show (Z * Y).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hYm, hZm, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_inv_cancel₀ hc0, one_smul, hNM])
  refine ⟨Units.mk0 c hc0, ⟨Y, Z, e1, e2⟩, ?_⟩
  show M = c • (Y.map O.subtype)
  rw [hYm, smul_smul, mul_inv_cancel₀ hc0, one_smul]

end GlobalTheory.ScalConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerUnipotentDiagDoubleCosetRepresentatives
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke

namespace GlobalTheory.LowerHecke

theorem repsBuild : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (R : Finset (GL D k)), IsRepsK (torusElt k D ϖ (indic s)) R → ∀ (κ κ' : GL D k → GL D k), (∀ g ∈ R, κ g ∈ KO k D ∧ κ' g ∈ KO k D ∧ g = κ g * torusElt k D ϖ (indic s) * κ' g) → ∀ N : GL D k → Finset (Matrix D A k), (∀ g ∈ R, (∀ ν ∈ N g, ∀ i a, valuation k (ν i a) < 1) ∧ ∀ ν : Matrix D A k, (∀ i a, valuation k (ν i a) < 1) → ∃! ν', ν' ∈ N g ∧ ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν - ν' = g.1 * μ) → ∃ R' : Finset (GL (A ⊕ D) k), IsReps (mtor ϖ (indic s)) R' blockDet ∧ ∀ F : GL (A ⊕ D) k → ℂ, ∑ j ∈ R', F j = ∑ g ∈ R, ∑ ν ∈ N g, F (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g)) := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ s R hR κ κ' hκ N hN
  classical
  set t : GL (A ⊕ D) k := mtor ϖ (indic s) with ht
  let f : (Σ _ : GL D k, Matrix D A k) → GL (A ⊕ D) k :=
    fun x => lowU x.2 * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ x.1)

  have key : ∀ g₁ ∈ R, ∀ ν₁ ∈ N g₁, ∀ g₂ ∈ R, ∀ ν₂ ∈ N g₂,
      (f ⟨g₁, ν₁⟩ * t)⁻¹ * (f ⟨g₂, ν₂⟩ * t) ∈ parahoric k A D → g₁ = g₂ ∧ ν₁ = ν₂ := by
    intro g₁ hg₁ ν₁ hν₁ g₂ hg₂ ν₂ hν₂ h
    obtain ⟨rfl, μ, hμ, hdiff⟩ := GlobalTheory.T.lowerUnipotent_blockDiag_cosets_distinct k A D ϖ hϖ s R hR κ κ' hκ g₁ hg₁ g₂ hg₂ ν₁ ν₂ h
    refine ⟨rfl, ?_⟩
    obtain ⟨hsmall, huniq⟩ := hN g₁ hg₁
    obtain ⟨ν', _, hν'⟩ := huniq ν₂ (hsmall ν₂ hν₂)
    have e2 : ν₂ = ν' := hν' ν₂ ⟨hν₂, 0, fun i a => by simp, by simp⟩
    have e1 : ν₁ = ν' := hν' ν₁ ⟨hν₁, μ, hμ, hdiff⟩
    rw [e1, e2]
  refine ⟨(R.sigma N).image f, ⟨?_, ?_⟩, ?_⟩
  · intro j hj
    obtain ⟨⟨g, ν⟩, hx, rfl⟩ := Finset.mem_image.1 hj
    rw [Finset.mem_sigma] at hx
    obtain ⟨hg, hν⟩ := hx
    refine ⟨Subgroup.mul_mem _ (lowU_mem ((hN g hg).1 ν hν)) (emb_mem (hκ g hg).1), ?_⟩
    have h22 : (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g)).1.toBlocks₂₂ = (κ g).1 := by
      rw [Units.val_mul, val_emb_one, val_lowU, fromBlocks_multiply]; simp
    show ((blockDet (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g)) : kˣ) : k) = _
    rw [blockDet_lowU_emb, h22, GeneralLinearGroup.val_det_apply]
  · intro j hj
    obtain ⟨g, hg, ν₀, hν₀, hall⟩ := GlobalTheory.T.exists_lowerUnipotent_blockDiag_coset_rep k A D ϖ hϖ s R hR κ κ' hκ j hj
    obtain ⟨ν', ⟨hν'N, μ, hμ, hdiff⟩, -⟩ := (hN g hg).2 ν₀ hν₀
    refine ⟨f ⟨g, ν'⟩, ⟨Finset.mem_image.2 ⟨(⟨g, ν'⟩ : Σ _ : GL D k, Matrix D A k), Finset.mem_sigma.2 ⟨hg, hν'N⟩, rfl⟩,
      hall ν' ⟨μ, hμ, hdiff⟩⟩, ?_⟩
    rintro j' ⟨hj', hmem⟩
    obtain ⟨⟨g₂, ν₂⟩, hx, rfl⟩ := Finset.mem_image.1 hj'
    rw [Finset.mem_sigma] at hx
    have hmem' : (f ⟨g, ν'⟩ * t)⁻¹ * (j * t) ∈ parahoric k A D := hall ν' ⟨μ, hμ, hdiff⟩
    have hc : (f ⟨g₂, ν₂⟩ * t)⁻¹ * (f ⟨g, ν'⟩ * t) ∈ parahoric k A D := by
      have := Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ hmem')
      simpa [mul_assoc] using this
    obtain ⟨rfl, rfl⟩ := key g₂ hx.1 ν₂ hx.2 g hg ν' hν'N hc
    rfl
  · intro F
    rw [Finset.sum_image, Finset.sum_sigma]
    rintro ⟨g₁, ν₁⟩ h₁ ⟨g₂, ν₂⟩ h₂ heq
    rw [Finset.coe_sigma, Set.mem_sigma_iff] at h₁ h₂
    have hc : (f ⟨g₁, ν₁⟩ * t)⁻¹ * (f ⟨g₂, ν₂⟩ * t) ∈ parahoric k A D := by
      rw [show f ⟨g₁, ν₁⟩ = f ⟨g₂, ν₂⟩ from heq, inv_mul_cancel]; exact Subgroup.one_mem _
    obtain ⟨rfl, rfl⟩ := key g₁ h₁.1 ν₁ h₁.2 g₂ h₂.1 ν₂ h₂.2 hc
    rfl

end GlobalTheory.LowerHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SegmentsBoundsAndDoublingLFactorStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segments_bounds_and_doubling_lFactor : ∀ {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (k t N : ℕ) (z : ℕ → ℂˣ), (∀ i, ‖(z i : ℂ)‖ = 1) → ∀ α : Fin N → ℂˣ, Finset.univ.val.map α = ∑ i ∈ Finset.Icc 1 k, GlobalTheory.LFun.seg w (z i) t → (∀ j, ‖(α j : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((t : ℝ) - 1) / 2) ∧ ‖(α j : ℂ)‖⁻¹ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((t : ℝ) - 1) / 2)) ∧ GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α ((t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.lFactor (Ideal.absNorm w.asIdeal) α⁻¹ ((t : ℂ) / 2 + 1 / 2) = ∏ i ∈ Finset.Icc 1 k, ∏ n ∈ Finset.Icc 1 t, ((1 - (z i : ℂ) * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹) * (1 - (z i : ℂ)⁻¹ * ((Ideal.absNorm w.asIdeal : ℂ) ^ n)⁻¹))⁻¹ := by
  first | exact @GlobalTheory.LFun.seg_bounds_and_doubling_lFactor | exact GlobalTheory.LFun.seg_bounds_and_doubling_lFactor | (intros; apply GlobalTheory.LFun.seg_bounds_and_doubling_lFactor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumRepsDatumEq
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

open Classical

namespace GlobalTheory.ParHeckeTarget

theorem sum_reps_datum_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ : kˣ →* ℂˣ), IsTame ξ → ∀ (s : Finset D') (R : Finset (GL (A ⊕ D') k)) d, IsReps (mtor ϖ (indic s)) R d → ∀ RK, IsRepsK (torusElt k D' ϖ (indic s)) RK → ∀ x : Matrix (A ⊕ D') (A ⊕ D) k, ∑ j ∈ R, ((ξ (d j) * (ξ (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ) * datum ξ (((j * mtor ϖ (indic s))⁻¹).1 * x) = ∑ g ∈ RK, liftS ξ (fun y => intInd ((g⁻¹).1 * y)) x := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ ξ hξ s R d hR RK hRK x
  have hL : ∀ j ∈ R, ((ξ (d j) * (ξ (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ) * datum ξ (((j * mtor ϖ (indic s))⁻¹).1 * x) =
      if InSupp (((j * mtor ϖ (indic s))⁻¹).1 * x) then datum ξ x else 0 := by
    intro j hj
    have h := GlobalTheory.T.parahoric_hecke_sum_term_at_coset k A D D' ϖ hϖ ξ hξ s j (hR.1 j hj).1 (d j) (hR.1 j hj).2 x
    split_ifs with hs
    · exact h.1 hs
    · rw [h.2 hs, mul_zero]
  have hRt : ∀ g ∈ RK, liftS ξ (fun y => intInd ((g⁻¹).1 * y)) x =
      if (∀ i l, ((g⁻¹).1 * schur x) i l ∈ 𝒪[k]) then datum ξ x else 0 := by
    intro g _
    simp only [liftS, intInd]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hRt, ← Finset.sum_filter, ← Finset.sum_filter,
    Finset.sum_const, Finset.sum_const]
  by_cases hx : InSupp x
  · rw [GlobalTheory.T.card_filter_parahoric_cosets_eq_schur_count k A D D' ϖ hϖ s R d hR RK hRK x hx]
  · have h0 : datum ξ x = 0 := by simp only [datum, dif_neg hx]
    simp [h0]

end GlobalTheory.ParHeckeTarget
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymEdgeStableSubmoduleEqTop
section
open Matrix Formalism.UG Formalism.L2.DIV GlobalTheory.LevNorm

namespace GlobalTheory

theorem symEdge_span_eq_top : ∀ (k : Type) [Field k] (n ρ κ : ℕ), n = 2 * ρ + κ + 1 → 1 ≤ ρ → ∀ (a : Fin n → Fin n → k), (∀ i j, symEdge ρ κ i j → a i j ≠ 0) → ∀ (V : Submodule k (Fin n → k)), V ≠ ⊥ → (∀ w ∈ V, (fun j => ∑ i, if symEdge ρ κ i j then a i j * w i else 0) ∈ V) → (∀ i j : Fin n, i < j → ¬(ρ ≤ i.val ∧ i.val < ρ + κ ∧ j.val = ρ + κ) → ∀ w ∈ V, Pi.single i (w j) ∈ V) → V = ⊤ := by
  intro k _ n ρ κ hn hρ a ha V hV hT hU
  have hsc : ∀ (i : Fin n) (c : k), c ≠ 0 → Pi.single i c ∈ V → Pi.single i (1 : k) ∈ V := by
    intro i c hc h
    have e : c⁻¹ • Pi.single i c = Pi.single i (1 : k) := by
      ext j; by_cases hj : j = i <;> simp [hj, hc]
    rw [← e]; exact V.smul_mem _ h
  let i0 : Fin n := ⟨0, by omega⟩
  have h0 : Pi.single i0 (1 : k) ∈ V := by
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
    by_cases hex : ∃ j : Fin n, 0 < j.val ∧ w j ≠ 0
    · obtain ⟨j, hj, hwj⟩ := hex
      exact hsc i0 (w j) hwj (hU i0 j (Fin.lt_def.2 hj) (by simp [i0]; omega) w hw)
    · push_neg at hex
      have hwe : w = Pi.single i0 (w i0) := by
        funext j
        by_cases hj : j = i0
        · subst hj; simp
        · have : 0 < j.val := by
            rcases Nat.eq_zero_or_pos j.val with h | h
            · exact absurd (Fin.ext h) hj
            · exact h
          rw [hex j this, Pi.single_eq_of_ne hj]
      have hne : w i0 ≠ 0 := fun h => hw0 (by rw [hwe, h, Pi.single_zero])
      exact hsc i0 _ hne (hwe ▸ hw)
  have hstep : ∀ x y : Fin n, symEdge ρ κ x y → (∀ j : Fin n, symEdge ρ κ x j → j = y) →
      Pi.single x (1 : k) ∈ V → Pi.single y (1 : k) ∈ V := by
    intro x y hxy huniq hx
    refine hsc y (a x y) (ha x y hxy) ?_
    have hu := hT _ hx
    convert hu using 1
    funext j
    rw [Finset.sum_eq_single x]
    · by_cases hj : j = y
      · subst hj; simp [hxy]
      · have : ¬ symEdge ρ κ x j := fun h => hj (huniq j h)
        simp [this, Pi.single_eq_of_ne hj]
    · intro i _ hi; simp [Pi.single_eq_of_ne hi]
    · simp
  have hwalk : ∀ t, t ≤ 2 * ρ → ∀ x : Fin n, x.val = (if t < ρ then t else t + κ) → Pi.single x (1 : k) ∈ V := by
    intro t
    induction t with
    | zero =>
      intro _ x hx
      have : x = i0 := Fin.ext (by simp [i0] at hx ⊢; split_ifs at hx <;> omega)
      rw [this]; exact h0
    | succ t ih =>
      intro ht y hy
      have hxlt : (if t < ρ then t else t + κ) < n := by split_ifs <;> omega
      let x : Fin n := ⟨_, hxlt⟩
      refine hstep x y ?_ ?_ (ih (by omega) x rfl)
      · unfold symEdge
        simp only [x]
        split_ifs at hy ⊢ <;> omega
      · intro j hj
        apply Fin.ext
        unfold symEdge at hj
        simp only [x] at hj
        split_ifs at hy hj <;> omega
  let last : Fin n := ⟨2 * ρ + κ, by omega⟩
  have hlast : Pi.single last (1 : k) ∈ V := hwalk (2 * ρ) le_rfl last (by simp [last]; omega)
  have hall : ∀ i : Fin n, Pi.single i (1 : k) ∈ V := by
    intro i
    by_cases hi : i = last
    · rw [hi]; exact hlast
    · have hlt : i < last := by
        rw [Fin.lt_def]; have := i.2; have : i.val ≠ 2 * ρ + κ := fun h => hi (Fin.ext h); simp [last]; omega
      have := hU i last hlt (by simp [last]; omega) _ hlast
      simpa using this
  rw [eq_top_iff, ← (Pi.basisFun k (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  exact hall i

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedSubfieldCriterionStatement
section
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_subfield_criterion : ∀ (l : ℕ) [Fact l.Prime] (F : Subfield ℂ_[l]) (N : ℕ), 0 < N → (∀ x ∈ F, ‖x‖ < 1 → ‖x‖ ≤ ‖(l : ℂ_[l])‖) → (∀ x ∈ F, ‖x‖ ≤ 1 → ‖x ^ (l ^ N) - x‖ < 1) → F ≤ MaximalUnramifiedExtension l := by
  first | exact @GlobalTheory.SubKur.le_Kur | exact GlobalTheory.SubKur.le_Kur | (intros; apply GlobalTheory.SubKur.le_Kur <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeierstrassPIntegralOfMulIntegralGoodReductionStatement
section
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_integral_of_mul_integral_good_reduction : ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 → ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∀ (z : ℂ) (N : ℕ), (N : ℂ) * z ∉ L.lattice → ‖ι (L.weierstrassP (N * z))‖ ≤ 1 → ‖ι (L.weierstrassP z)‖ ≤ 1 := by
  first | exact @GlobalTheory.Honda.integral_of_mul_integral | exact GlobalTheory.Honda.integral_of_mul_integral | (intros; apply GlobalTheory.Honda.integral_of_mul_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeierstrassPOddMulSubTwoTorsionProductStatement
section
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_odd_mul_sub_twoTorsion_product : ∀ (L : PeriodPair) (n : ℕ) (S : Finset ℂ) (t : ℂ), Odd n → Formalism.L2.Th1.F.IsKerReps L (n : ℂ) S → t ∉ L.lattice → 2 * t ∈ L.lattice → ∀ z, (n : ℂ) * z ∉ L.lattice → (n : ℂ) ^ 2 * (L.weierstrassP (n * z) - L.weierstrassP t) * ∏ P ∈ S, (L.weierstrassP z - L.weierstrassP P) = (L.weierstrassP z - L.weierstrassP t) * ∏ P ∈ S, (L.weierstrassP z - L.weierstrassP (t + P)) := by
  first | exact @GlobalTheory.OddHalfProduct.wp_odd_mul_sub_half_prod | exact GlobalTheory.OddHalfProduct.wp_odd_mul_sub_half_prod | (intros; apply GlobalTheory.OddHalfProduct.wp_odd_mul_sub_half_prod <;> assumption)
end

