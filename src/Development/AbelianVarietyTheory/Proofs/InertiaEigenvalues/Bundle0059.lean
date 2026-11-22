import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0025
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0024
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0026
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0023
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0028

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMatrixComatrixDivisibleStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_dvd_entries_of_mul_eq_diagonal_pow : ∀ {R : Type} [CommRing R] [IsDomain R] (d N N₀ q : ℕ) (p : Fin d → ℕ) (ξ : R) (A A' B B' c c' V₀ V₀' : Matrix (Fin d) (Fin d) R), ξ ≠ 0 → B * B' = 1 → c * c' = 1 → V₀ * V₀' = 1 → A * A' = ξ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) → ξ ^ q • (A * B * c) = ξ ^ N • (V₀ * Matrix.diagonal (fun j => ξ ^ p j)) → N₀ ≤ N → (∀ i, |(p i : ℤ) - q| ≤ N₀) → (∀ i j, ξ ^ (N - N₀) ∣ A i j) ∧ ∀ i j, ξ ^ (N - N₀) ∣ A' i j := by
  first | (exact @GlobalTheory.frobenius_matrix_comatrix_divisible) | (exact GlobalTheory.frobenius_matrix_comatrix_divisible) | (intros; apply GlobalTheory.frobenius_matrix_comatrix_divisible  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPowEquationDvdAllPowStatement
section
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusPowEquation_dvd_all_pow : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u : R), ((l : ℕ) : R) = 0 → u ∈ nonZeroDivisors R → ∀ (κ : Type) [Fintype κ] (D : κ → R) (c : κ → κ → R) (h : ℕ), (∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) → (∀ j (M : ℕ), ∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * D j ^ n) → ∀ (m : ℕ) j, u ^ m ∣ D j := by
  first | exact @GlobalTheory.phiEq_dvd_all_pow | exact GlobalTheory.phiEq_dvd_all_pow | (intros; apply GlobalTheory.phiEq_dvd_all_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
section
open Matrix

noncomputable section

namespace GlobalTheory.JR.Step

section Alg
variable {r : ℕ} {k : Type} [CommRing k]

def eL (r : ℕ) (k : Type) [CommRing k] : Fin (r + 1) → k := Pi.single (Fin.last r) 1

def blocks (A : Matrix (Fin (r + 1)) (Fin (r + 1)) k) : Gl r k :=
  (A.submatrix Fin.castSucc Fin.castSucc, fun i => A (Fin.castSucc i) (Fin.last r),
    fun j => A (Fin.last r) (Fin.castSucc j), A (Fin.last r) (Fin.last r))

def lift (Z : Gl r k) (μ l : k) : Gl (r + 1) k := (full Z, μ • eL r k, eL r k, l)

def embHom (r : ℕ) (k : Type) [CommRing k] :
    Matrix (Fin r) (Fin r) k →* Matrix (Fin (r + 1)) (Fin (r + 1)) k where
  toFun g := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g 0 0 1)
  map_one' := by
    rw [Matrix.fromBlocks_one]
    exact Matrix.submatrix_one_equiv _
  map_mul' g h := by
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

def emb (r : ℕ) (k : Type) [CommRing k] : GL (Fin r) k →* GL (Fin (r + 1)) k := Units.map (embHom r k)

def glMap {k' : Type} [CommRing k'] (φ : k →+* k') (Y : Gl r k) : Gl r k' :=
  (Y.1.map φ, fun i => φ (Y.2.1 i), fun i => φ (Y.2.2.1 i), φ Y.2.2.2)

end Alg

section Herm
variable {r : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]

theorem full_toGl_isSelfAdjoint (X : Hn r F E) (hl : star (algebraMap F E X.2.2) = algebraMap F E X.2.2) :
    IsSelfAdjoint (full X.toGl) := by
  have hA : X.1.1ᴴ = X.1.1 := X.1.2
  unfold IsSelfAdjoint full Hn.toGl
  simp only [Matrix.star_eq_conjTranspose, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.fromBlocks_conjTranspose, hA]
  congr 1
  congr 1
  all_goals (ext i j; simp [hl])

end Herm

section Unr
variable {r : ℕ} {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
  [StarRing E] [Unram F E]

def liftH (X : Hn r F E) (ν : E) (l : F) : Hn (r + 1) F E :=
  (⟨full X.toGl, full_toGl_isSelfAdjoint X (Unram.star_fix _)⟩, ν • eL r E, l)

def uEmb (r : ℕ) (E : Type) [Field E] [StarRing E] :
    Matrix.unitaryGroup (Fin r) E →* Matrix.unitaryGroup (Fin (r + 1)) E where
  toFun g := ⟨embHom r E g.1, by
    have hs : star (embHom r E g.1) = embHom r E (star g.1) := by
      simp only [embHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.star_eq_conjTranspose, Matrix.reindex_apply,
        Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
        Matrix.conjTranspose_one]
    rw [Matrix.mem_unitaryGroup_iff, hs, ← map_mul, Matrix.mem_unitaryGroup_iff.mp g.2, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ _ _)

end Unr

end GlobalTheory.JR.Step
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLinearDisjointStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_sum_map_mul_eq_zero_of_linearIndependent : ∀ (k Ω D : Type) [Field k] [Field Ω] [Field D] [Algebra k Ω] [IsGalois k Ω] (o : Ω →+* D) (F : Subfield D), (∀ x : Ω, o x ∈ F ↔ x ∈ (algebraMap k Ω).range) → ∀ (m : ℕ) (x : Fin m → Ω), LinearIndependent k x → ∀ b : Fin m → D, (∀ i, b i ∈ F) → ∑ i, o (x i) * b i = 0 → ∀ i, b i = 0 := by
  first | exact @GlobalTheory.GalDisj.galois_linearDisjoint | exact GlobalTheory.GalDisj.galois_linearDisjoint | (intros; apply GlobalTheory.GalDisj.galois_linearDisjoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenEigenMultiplicityQuotientAdditiveChain
section
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
noncomputable section
namespace GlobalTheory.PhiGam.GmultAdd

variable {k U : Type} [Field k] [AddCommGroup U] [Module k U]

def quotEquiv (A B S : Submodule k U) (hSB : S ≤ B) :
    (↥A ⧸ B.submoduleOf A) ≃ₗ[k] (↥(A.map S.mkQ) ⧸ (B.map S.mkQ).submoduleOf (A.map S.mkQ)) :=
  (Submodule.quotEquivOfEq _ _ (by
      ext a
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      change (a : U) ∈ B ↔ S.mkQ a ∈ B.map S.mkQ
      have h : (B.map S.mkQ).comap S.mkQ = B := by
        rw [Submodule.comap_map_mkQ]; exact sup_eq_right.2 hSB
      constructor
      · intro ha
        exact Submodule.mem_map_of_mem (f := S.mkQ) ha
      · intro ha
        rw [← h]
        exact ha)).trans
    (LinearMap.quotKerEquivOfSurjective
      (((B.map S.mkQ).submoduleOf (A.map S.mkQ)).mkQ ∘ₗ (S.mkQ.submoduleMap A))
      ((Submodule.mkQ_surjective _).comp (LinearMap.submoduleMap_surjective _ _)))

theorem map_self (S : Submodule k U) : S.map S.mkQ = ⊥ := by
  simp

theorem fin_map (A S : Submodule k U) (h : FiniteDimensional k (↥A ⧸ S.submoduleOf A)) :
    FiniteDimensional k (A.map S.mkQ) := by
  have e := quotEquiv A S S le_rfl
  have h2 : (S.map S.mkQ).submoduleOf (A.map S.mkQ) = ⊥ := by
    rw [map_self]; simp [Submodule.submoduleOf]
  have e2 := e.trans (Submodule.quotEquivOfEqBot _ h2)
  exact e2.finiteDimensional

theorem finrank_quot (A B S : Submodule k U) (hSB : S ≤ B) (hBA : B ≤ A)
    [FiniteDimensional k (A.map S.mkQ)] :
    Module.finrank k (↥A ⧸ B.submoduleOf A) + Module.finrank k (B.map S.mkQ)
      = Module.finrank k (A.map S.mkQ) := by
  rw [(quotEquiv A B S hSB).finrank_eq,
    ← Submodule.finrank_quotient_add_finrank ((B.map S.mkQ).submoduleOf (A.map S.mkQ)),
    (Submodule.submoduleOfEquivOfLe (Submodule.map_mono hBA)).finrank_eq]

theorem map_inf_mkQ (A B S : Submodule k U) (hA : S ≤ A) :
    (A ⊓ B).map S.mkQ = A.map S.mkQ ⊓ B.map S.mkQ := by
  apply le_antisymm (Submodule.map_inf_le _)
  rintro y ⟨⟨a, ha, rfl⟩, b, hb, hab⟩
  refine ⟨b, ⟨?_, hb⟩, hab⟩
  have : b - a ∈ S := by
    simpa [Submodule.Quotient.eq] using hab
  simpa using A.add_mem (hA this) ha

theorem pow_mem (N : Module.End k U) (Q : Submodule k U) (hQ : ∀ y ∈ Q, N y ∈ Q) (m : ℕ) :
    ∀ y ∈ Q, (N ^ m) y ∈ Q := by
  induction m with
  | zero => intro y hy; simpa using hy
  | succ m ih => intro y hy; rw [pow_succ', Module.End.mul_apply]; exact hQ _ (ih y hy)

theorem mem_gen (N : Module.End k U) (Q : Submodule k U) (hQ : ∀ y ∈ Q, N y ∈ Q) (y : U) :
    y ∈ (⨆ m : ℕ, Q.comap (N ^ m)) ↔ ∃ m : ℕ, (N ^ m) y ∈ Q := by
  have hmono : Monotone (fun m : ℕ => Q.comap (N ^ m)) := by
    apply monotone_nat_of_le_succ
    intro m z hz
    simp only [Submodule.mem_comap] at hz ⊢
    rw [pow_succ', Module.End.mul_apply]; exact hQ _ hz
  rw [Submodule.mem_iSup_of_directed _ hmono.directed_le]
  rfl

theorem stab (N : Module.End k U) (Q S : Submodule k U) (hQ : ∀ y ∈ Q, N y ∈ Q)
    [FiniteDimensional k (Q.map S.mkQ)] :
    ∃ M : ℕ, ∀ m : ℕ, (Q.map (N ^ M)).map S.mkQ ≤ (Q.map (N ^ (M + m))).map S.mkQ := by
  have hle : ∀ j : ℕ, (Q.map (N ^ j)).map S.mkQ ≤ Q.map S.mkQ := fun j =>
    Submodule.map_mono (by rintro _ ⟨y, hy, rfl⟩; exact pow_mem N Q hQ j y hy)
  have hfin : ∀ j : ℕ, FiniteDimensional k ((Q.map (N ^ j)).map S.mkQ) := fun j =>
    Submodule.finiteDimensional_of_le (hle j)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ j : ℕ, Module.finrank k ((Q.map (N ^ M)).map S.mkQ)
      ≤ Module.finrank k ((Q.map (N ^ j)).map S.mkQ) :=
    ⟨Function.argmin (fun j : ℕ => Module.finrank k ((Q.map (N ^ j)).map S.mkQ)),
      fun j => Function.argmin_le (fun j : ℕ => Module.finrank k ((Q.map (N ^ j)).map S.mkQ)) j⟩
  refine ⟨M, fun m => ?_⟩
  have h1 : (Q.map (N ^ (M + m))).map S.mkQ ≤ (Q.map (N ^ M)).map S.mkQ := by
    apply Submodule.map_mono
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨(N ^ m) y, pow_mem N Q hQ m y hy, by rw [pow_add, Module.End.mul_apply]⟩
  haveI := hfin M
  exact (Submodule.eq_of_le_of_finrank_le h1 (hM _)).ge

theorem gen_sup (N : Module.End k U) (P Q S : Submodule k U) (hSQ : S ≤ Q) (hQP : Q ≤ P)
    (hQ : ∀ y ∈ Q, N y ∈ Q) (hS : ∀ y ∈ S, N y ∈ S) [FiniteDimensional k (Q.map S.mkQ)] :
    P ⊓ (⨆ m : ℕ, Q.comap (N ^ m)) = (P ⊓ ⨆ m : ℕ, S.comap (N ^ m)) ⊔ Q := by
  apply le_antisymm
  · rintro u ⟨huP, hu⟩
    obtain ⟨m, hm⟩ := (mem_gen N Q hQ u).1 hu
    obtain ⟨M, hM⟩ := stab N Q S hQ
    obtain ⟨_, ⟨q, hq, rfl⟩, h⟩ := hM m
      (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem (f := N ^ M) hm))
    have h' : (N ^ M) ((N ^ m) u) - (N ^ (M + m)) q ∈ S := by
      simpa [Submodule.Quotient.eq] using h.symm
    have hu' : u = (u - q) + q := by abel
    rw [hu']
    refine Submodule.add_mem_sup ⟨P.sub_mem huP (hQP hq), (mem_gen N S hS _).2 ⟨M + m, ?_⟩⟩ hq
    rw [map_sub]
    convert h' using 2
    rw [pow_add, Module.End.mul_apply]
  · refine sup_le (inf_le_inf_left _ (iSup_mono fun m => Submodule.comap_mono hSQ)) (le_inf hQP ?_)
    intro y hy
    exact (mem_gen N Q hQ y).2 ⟨0, by simpa using hy⟩

theorem main : ∀ {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U) (P Q S : Submodule k U), S ≤ Q → Q ≤ P → (∀ x ∈ P, T x ∈ P) → (∀ x ∈ Q, T x ∈ Q) → (∀ x ∈ S, T x ∈ S) → FiniteDimensional k (↥P ⧸ S.submoduleOf P) → ∀ x : k, gmult T P S x = gmult T P Q x + gmult T Q S x := by
  intro k U _ _ _ T P Q S hSQ hQP _ hQ hS hfin x
  unfold gmult
  set N := T - algebraMap k (Module.End k U) x with hN
  have hst : ∀ A : Submodule k U, (∀ y ∈ A, T y ∈ A) → ∀ y ∈ A, N y ∈ A := by
    intro A hA y hy
    have : N y = T y - x • y := by simp [hN, Module.algebraMap_end_apply]
    rw [this]
    exact A.sub_mem (hA y hy) (A.smul_mem x hy)
  haveI hP := fin_map P S hfin
  have hf : ∀ A : Submodule k U, A ≤ P → FiniteDimensional k (A.map S.mkQ) := fun A hA =>
    Submodule.finiteDimensional_of_le (Submodule.map_mono hA)
  haveI := hf Q hQP
  have hSG : S ≤ ⨆ m : ℕ, S.comap (N ^ m) := fun y hy =>
    (mem_gen N S (hst S hS) y).2 ⟨0, by simpa using hy⟩
  have h1 := gen_sup N P Q S hSQ hQP (hst Q hQ) (hst S hS)
  set G := ⨆ m : ℕ, S.comap (N ^ m) with hG
  have h2 : Q ⊓ G = (P ⊓ G) ⊓ Q := by
    rw [inf_right_comm, inf_eq_right.2 hQP]
  rw [h1, h2]
  set A := P ⊓ G with hA
  have hSA : S ≤ A := le_inf (hSQ.trans hQP) hSG
  haveI := hf A inf_le_left
  haveI := hf (A ⊔ Q) (sup_le inf_le_left hQP)
  haveI := hf (A ⊓ Q) (inf_le_right.trans hQP)
  have e1 := finrank_quot A S S le_rfl hSA
  have e2 := finrank_quot (A ⊔ Q) Q S hSQ le_sup_right
  have e3 := finrank_quot (A ⊓ Q) S S le_rfl (le_inf hSA hSQ)
  have e4 := Submodule.finrank_sup_add_finrank_inf_eq (A.map S.mkQ) (Q.map S.mkQ)
  rw [← Submodule.map_sup, ← map_inf_mkQ A Q S hSA] at e4
  rw [map_self, finrank_bot] at e1 e3
  omega

end GlobalTheory.PhiGam.GmultAdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GhostComponentInjectiveOfNoTorsionStatement
section
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittVector_eq_of_ghostComponent_eq_of_no_torsion : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A], (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) → ∀ x y : WittVector l A, (∀ n, WittVector.ghostComponent n x = WittVector.ghostComponent n y) → x = y := by
  first | exact @GlobalTheory.WittVector.ghostComponent_injective_of_noTorsion | exact GlobalTheory.WittVector.ghostComponent_injective_of_noTorsion | (intros; apply GlobalTheory.WittVector.ghostComponent_injective_of_noTorsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlFactorFromBlocksModUniformizerStatement
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gl_factor_fromBlocks_mod_uniformizer_alt : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (g : GL (Fin r) (IsLocalRing.ResidueField O)) (L : Matrix (Fin r) (Fin r) O), L.map (IsLocalRing.residue O) = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) → ∀ (B : Matrix (Fin r) (Fin t) O) (q : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O), (∀ i j, IsLocalRing.residue O (q i j) = IsLocalRing.residue O (Matrix.fromBlocks L B 0 (1 : Matrix (Fin t) (Fin t) O) i j)) → ∃ h : GL (Fin r ⊕ Fin t) O, (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl i) (Sum.inl j) - (1 : Matrix (Fin r) (Fin r) O) i j ∈ Ideal.span {ϖ}) ∧ (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr i) (Sum.inl j) ∈ Ideal.span {ϖ}) ∧ (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) * Matrix.fromBlocks L 0 0 (1 : Matrix (Fin t) (Fin t) O) = q := by
  first | exact @GlobalTheory.gl_factor_fromBlocks_mod_uniformizer | exact GlobalTheory.gl_factor_fromBlocks_mod_uniformizer | (intros; apply GlobalTheory.gl_factor_fromBlocks_mod_uniformizer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GramDetEqNormMulGramDetOne
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.InvAlg

theorem gramDet_eq_norm_mul (K : UQ) (B : InvAlg K) (x : B.A) :
    B.gramDet x = Algebra.norm K.E x * B.gramDet 1 := by
  classical
  set b := Module.finBasis K.E B.A
  have hM : (Matrix.of fun i j => B.herm x (b i) (b j)) =
      (Algebra.leftMulMatrix b x).transpose * (Matrix.of fun i j => B.herm 1 (b i) (b j)) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, herm, one_mul,
      Algebra.leftMulMatrix_apply]
    have h := b.sum_repr (x * b i)
    conv_lhs => rw [← h]
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul, LinearMap.toMatrix_apply]
    simp
  unfold gramDet
  rw [hM, Matrix.det_mul, Matrix.det_transpose, Algebra.norm_eq_matrix_det b]

end GlobalTheory.UnitLemma.InvAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateOperatorOfGaloisRelationsStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTate_operator_of_galois_relations : ∀ {k : Type} [Field k] (d N q : ℕ) (p : Fin d → ℕ) (a b z w : k) (y y' v v₀ e r sy sv : Matrix (Fin d) (Fin d) k), a ≠ 0 → b ≠ 0 → z * w = 1 → y * y' = a ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) k) → y * v₀ = a ^ N • v → a ^ N • (r * sy) = b ^ N • (y * e) → r * sv * Matrix.diagonal (fun j => w ^ p j) = w ^ q • v → sy * v₀ = b ^ N • sv → ∃ u : Matrix (Fin d) (Fin d) k, u * y = y * e ∧ u * v = v * Matrix.diagonal (fun i => z ^ ((p i : ℤ) - q)) := by
  first | (exact @GlobalTheory.ht_operator_of_galois_relations) | (exact GlobalTheory.ht_operator_of_galois_relations) | (intros; apply GlobalTheory.ht_operator_of_galois_relations  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageFiniteExtensionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.image_finite_extension : ∀ (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : FractionRing O →+* PadicAlgCl l), (∀ z : ℤ_[l], ι (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l])) → ∃ L : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] L ∧ ∀ y, y ∈ L ↔ ∃ a, ι a = y := by
  first | exact @GlobalTheory.exists_finiteDimensional_intermediateField_eq_range_fractionRing | exact GlobalTheory.exists_finiteDimensional_intermediateField_eq_range_fractionRing | (intros; apply GlobalTheory.exists_finiteDimensional_intermediateField_eq_range_fractionRing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageFiniteOfTrivialOnInfFiniteIndexStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_image_of_trivial_on_inf_finiteIndex : ∀ (G Q : Type) [Group G] [Group Q] (ρ : G →* Q) (J H : Subgroup G), H.FiniteIndex → (∀ g ∈ J, g ∈ H → ρ g = 1) → (ρ '' (J : Set G)).Finite := by
  first | exact @GlobalTheory.image_finite_of_trivial_on_inf_finiteIndex | exact GlobalTheory.image_finite_of_trivial_on_inf_finiteIndex | (intros; apply GlobalTheory.image_finite_of_trivial_on_inf_finiteIndex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndepOverPadicOfIndepModPrimeStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indep_over_padic_of_indep_mod_prime : ∀ (l : ℕ) [Fact l.Prime] (d : ℕ) (ι : Type) (w : Fin d → ι → ℂ_[l]) (γ : ι → ℝ), (∀ a i, ‖w a i‖ ≤ γ i) → (∀ n : Fin d → ℕ, (∀ i, ‖∑ a, (n a : ℂ_[l]) * w a i‖ ≤ ‖(l : ℂ_[l])‖ * γ i) → ∀ a, l ∣ n a) → ∀ c : Fin d → ℚ_[l], (∀ i, ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * w a i = 0) → c = 0 := by
  first | exact @GlobalTheory.indep_over_Ql_of_indep_mod_l | exact GlobalTheory.indep_over_Ql_of_indep_mod_l | (intros; apply GlobalTheory.indep_over_Ql_of_indep_mod_l <;> assumption)
end

