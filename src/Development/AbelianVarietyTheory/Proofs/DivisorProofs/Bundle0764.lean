import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Formalism.RealPlaceAnalysis.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0749
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0731
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0752
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0005
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0013
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0602
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0750
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalQuantumDeterminantIntertwining
section
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.CapelliIntertw

theorem qdet_map {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (E : Fin n → Fin n → A) (u : ℂ) :
    f (Formalism.REAL.qdet E u) = Formalism.REAL.qdet (fun a b => f (E a b)) u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor Formalism.REAL.Tm
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 2
  congr 1
  funext k
  simp only [Function.comp_apply, map_add, apply_ite, AlgHom.commutes, map_zero]

variable {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] (T : M →ₗ[ℂ] M')

def intertw : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ M') where
  carrier := {z | ∀ v, T (z.1 v) = z.2 (T v)}
  mul_mem' := by
    intro a b ha hb v
    simp only [Prod.fst_mul, Prod.snd_mul, Module.End.mul_apply]
    rw [ha, hb]
  add_mem' := by
    intro a b ha hb v
    simp only [Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add]
    rw [ha, hb]
  algebraMap_mem' := by
    intro c v
    simp [Module.algebraMap_end_apply]

end GlobalTheory.CapelliIntertw

theorem GlobalTheory.capelli_intertw : ∀ (M M' : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] (T : M →ₗ[ℂ] M') (n : ℕ) (X : Fin n → Fin n → Module.End ℂ M) (Y : Fin n → Fin n → Module.End ℂ M'), (∀ i j v, T (X i j v) = Y i j (T v)) → ∀ (u : ℂ) (p : Polynomial ℂ) (v : M), T (Polynomial.aeval (Formalism.REAL.qdet X u) p v) = Polynomial.aeval (Formalism.REAL.qdet Y u) p (T v) := by
  intro M M' _ _ _ _ T n X Y hXY u p v
  let S := GlobalTheory.CapelliIntertw.intertw T
  let Z : Fin n → Fin n → S := fun a b => ⟨(X a b, Y a b), fun w => hXY a b w⟩
  let q : S := Polynomial.aeval (Formalism.REAL.qdet Z u) p
  have h1 : ((q : Module.End ℂ M × Module.End ℂ M').1) = Polynomial.aeval (Formalism.REAL.qdet X u) p := by
    have := Polynomial.aeval_algHom_apply ((AlgHom.fst ℂ _ _).comp S.val) (Formalism.REAL.qdet Z u) p
    rw [GlobalTheory.CapelliIntertw.qdet_map] at this
    exact this.symm
  have h2 : ((q : Module.End ℂ M × Module.End ℂ M').2) = Polynomial.aeval (Formalism.REAL.qdet Y u) p := by
    have := Polynomial.aeval_algHom_apply ((AlgHom.snd ℂ _ _).comp S.val) (Formalism.REAL.qdet Z u) p
    rw [GlobalTheory.CapelliIntertw.qdet_map] at this
    exact this.symm
  rw [← h1, ← h2]
  exact q.2 v
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrameSolutionCongrEqTransposeMulStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainfFrame_solution_congr_eq_transpose_mul : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U U' X : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y Z : Matrix (Fin d ⊕ Fin k) (Fin h) F.B), IsUnit U' → IsNil F.θ F.σ (U'.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U' * blk d k (p : F.B) 1) → X * (U' * blk d k (p : F.B) 1) = U * blk d k (p : F.B) 1 * X.map F.σ → (∀ i j, F.τ ∣ X i j - (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) i j) → Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y → Z.map F.σ = blk d k (p : F.B) 1 * U'.transpose * Z → (∀ i m, F.τ ∣ Z i m - Y i m) → Z = X.transpose * Y := by
  first | exact @GlobalTheory.CmpB.comparison | exact GlobalTheory.CmpB.comparison | (intros; apply GlobalTheory.CmpB.comparison <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrameSolutionMulCongrGmTransposeStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainfFrame_solution_mul_congr_Gm_transpose : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U U' X : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (u l : F.B) (Gm : Matrix (Fin h) (Fin d ⊕ Fin k) F.B) (W : Matrix (Fin d ⊕ Fin k) (Fin h) F.B), IsUnit U → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → F.τ ∣ u - 1 → X * (U' * blk d k (p : F.B) 1) = U * blk d k (p : F.B) 1 * X.map F.σ → (∀ i j, F.τ ∣ X i j - (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) i j) → F.σ l = u * l → F.τ ∣ l - 1 → U * blk d k (p : F.B) 1 * Gm.transpose.map F.σ = (p : F.B) • Gm.transpose → U' * blk d k (p : F.B) 1 * W.map F.σ = ((p : F.B) * u) • W → (∀ i m, F.τ ∣ W i m - Gm m i) → X * W = l • Gm.transpose := by
  first | exact @GlobalTheory.CmpG.comparison | exact GlobalTheory.CmpG.comparison | (intros; apply GlobalTheory.CmpG.comparison <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicNormalizedWeierstrassValuesCmStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_normalized_weierstrass_values_cm : ∀ (L : PeriodPair) (β Ω : ℂ), MulStable L β → β.im ≠ 0 → Ω ^ 12 = latDisc L → IsAlgebraic ℚ (s2 L / Ω ^ 2) ∧ ∀ (M : ℕ) (P : ℂ), 0 < M → (M : ℂ) * P ∈ L.lattice → IsAlgebraic ℚ (L.weierstrassP P / Ω ^ 2) ∧ IsAlgebraic ℚ (L.derivWeierstrassP P / Ω ^ 3) := by
  first | exact @GlobalTheory.AlgebraicitySecondEisenstein.main | exact GlobalTheory.AlgebraicitySecondEisenstein.main | (intros; apply GlobalTheory.AlgebraicitySecondEisenstein.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
section
noncomputable section

open Matrix

namespace GlobalTheory.LeviGA

variable {R S : Type} [CommRing R] [CommRing S] {a r : ℕ}

def blkEquiv (h : r ≤ a) : Fin r ⊕ Fin (a - r) ≃ Fin a :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h))

@[simp] theorem blkEquiv_inl (h : r ≤ a) (i : Fin r) : ((blkEquiv h (Sum.inl i) : Fin a) : ℕ) = i := rfl

@[simp] theorem blkEquiv_inr (h : r ≤ a) (i : Fin (a - r)) : ((blkEquiv h (Sum.inr i) : Fin a) : ℕ) = r + i := rfl

variable (R) in

def blkMat (h : r ≤ a) :
    Matrix (Fin r) (Fin r) R × Matrix (Fin (a - r)) (Fin (a - r)) R →* Matrix (Fin a) (Fin a) R where
  toFun p := Matrix.reindex (blkEquiv h) (blkEquiv h) (Matrix.fromBlocks p.1 0 0 p.2)
  map_one' := by simp [Matrix.fromBlocks_one]
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

def blkGL (h : r ≤ a) : GL (Fin r) R × GL (Fin (a - r)) R →* GL (Fin a) R :=
  (Units.map (blkMat R h)).comp MulEquiv.prodUnits.symm.toMonoidHom

theorem blkGL_val (h : r ≤ a) (p : GL (Fin r) R × GL (Fin (a - r)) R) :
    (blkGL h p : Matrix (Fin a) (Fin a) R) =
      Matrix.reindex (blkEquiv h) (blkEquiv h) (Matrix.fromBlocks (p.1 : Matrix _ _ R) 0 0 (p.2 : Matrix _ _ R)) :=
  rfl

theorem blkGL_apply (h : r ≤ a) (p : GL (Fin r) R × GL (Fin (a - r)) R) (i j : Fin r ⊕ Fin (a - r)) :
    (blkGL h p : Matrix (Fin a) (Fin a) R) (blkEquiv h i) (blkEquiv h j) =
      Matrix.fromBlocks (p.1 : Matrix _ _ R) 0 0 (p.2 : Matrix _ _ R) i j := by
  rw [blkGL_val, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem blkGL_block (h : r ≤ a) (p : GL (Fin r) R × GL (Fin (a - r)) R) (i j : Fin a) :
    ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ (blkGL h p : Matrix (Fin a) (Fin a) R) i j = 0 := by
  obtain ⟨i, rfl⟩ := (blkEquiv h).surjective i
  obtain ⟨j, rfl⟩ := (blkEquiv h).surjective j
  rw [blkGL_apply]
  rcases i with i | i <;> rcases j with j | j
  · left; simp
  · right; simp
  · right; simp
  · left; simp

theorem exists_blkGL (h : r ≤ a) (m : GL (Fin a) R)
    (hm : ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ (m : Matrix (Fin a) (Fin a) R) i j = 0) :
    ∃ p, blkGL h p = m := by
  obtain ⟨M, hM⟩ : ∃ M, M = (m : Matrix (Fin a) (Fin a) R).submatrix (blkEquiv h) (blkEquiv h) := ⟨_, rfl⟩
  have h12 : M.toBlocks₁₂ = 0 := by
    ext i j
    rw [Matrix.toBlocks₁₂, Matrix.of_apply, hM, Matrix.submatrix_apply, Matrix.zero_apply]
    rcases hm (blkEquiv h (Sum.inl i)) (blkEquiv h (Sum.inr j)) with h' | h'
    · rw [blkEquiv_inl, blkEquiv_inr] at h'; omega
    · exact h'
  have h21 : M.toBlocks₂₁ = 0 := by
    ext i j
    rw [Matrix.toBlocks₂₁, Matrix.of_apply, hM, Matrix.submatrix_apply, Matrix.zero_apply]
    rcases hm (blkEquiv h (Sum.inr i)) (blkEquiv h (Sum.inl j)) with h' | h'
    · rw [blkEquiv_inl, blkEquiv_inr] at h'; omega
    · exact h'
  have hMb : M = Matrix.fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂ := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
    rw [h12, h21]
  have hdet : IsUnit M.det := by
    rw [hM, Matrix.det_submatrix_equiv_self]
    exact (Matrix.isUnit_iff_isUnit_det _).1 m.isUnit
  rw [hMb, Matrix.det_fromBlocks_zero₂₁] at hdet
  have hA : IsUnit M.toBlocks₁₁ := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hdet)
  have hD : IsUnit M.toBlocks₂₂ := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hdet)
  refine ⟨(hA.unit, hD.unit), Units.ext ?_⟩
  rw [blkGL_val]
  simp only [IsUnit.unit_spec]
  rw [← hMb, hM]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.apply_symm_apply]

theorem map_blkGL (h : r ≤ a) (f : R →+* S) (p : GL (Fin r) R × GL (Fin (a - r)) R) :
    Units.map f.mapMatrix.toMonoidHom (blkGL h p) =
      blkGL h (Units.map f.mapMatrix.toMonoidHom p.1, Units.map f.mapMatrix.toMonoidHom p.2) := by
  apply Units.ext
  simp only [Units.coe_map, blkGL_val]
  ext i j
  obtain ⟨i, rfl⟩ := (blkEquiv h).surjective i
  obtain ⟨j, rfl⟩ := (blkEquiv h).surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.reindex_apply]

end GlobalTheory.LeviGA

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockGLHomConjPermMatrixOfBlocksMatchStatement
section
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockGLHom_conj_permMatrix_of_blocks_match : ∀ (F : Type) [Field F] (r : ℕ) (b b' : Fin r → ℕ) (w : Equiv.Perm (Fin r)), (∀ i j : Fin r, b i = b j ↔ b' (w i) = b' (w j)) → ∀ i : Fin r, (block b (b i)).card = (block b' (b' (w i))).card ∧ ∀ (d : ℕ) (h : (block b (b i)).card = d) (h' : (block b' (b' (w i))).card = d), ∃ π : GL (Fin d) F, ∀ g : GL (Fin d) F, (blockHom F b' (b' (w i)) h' (π * g * π⁻¹) : GL (Fin r) F) * permGL F w = permGL F w * (blockHom F b (b i) h g : GL (Fin r) F) := by
  first | exact @GlobalTheory.Proof.BlockConj.blockHom_conj_permGL | exact GlobalTheory.Proof.BlockConj.blockHom_conj_permGL | (intros; apply GlobalTheory.Proof.BlockConj.blockHom_conj_permGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockTriangularPrimitiveCharacters
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI Formalism.L2.DIV GlobalTheory.FinGL

noncomputable section

namespace GlobalTheory.FinGL.LeviChar

variable {F : Type} [Field F] {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}

def diagHom (b : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1) :
    (∀ a, GL (Fin (d a)) F) →* blockTri (κ := F) b :=
  MonoidHom.codRestrict (MonoidHom.toHomUnits
    { toFun := fun x => (Matrix.blockDiagonal' fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)).submatrix e.symm e.symm
      map_one' := by
        have : (fun a => ((1 : ∀ a, GL (Fin (d a)) F) a : Matrix (Fin (d a)) (Fin (d a)) F)) = 1 := rfl
        rw [this, Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]
      map_mul' := fun x y => by
        rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul]
        rfl }) _
    fun x i j hij => Matrix.blockDiagonal'_apply_ne
      (fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)) (e.symm i).2 (e.symm j).2 fun e' => by
        have := (he _ _).2 e'
        rw [e.apply_symm_apply, e.apply_symm_apply] at this
        exact hij.ne' this

theorem diagHom_apply (b : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1)
    (x : ∀ a, GL (Fin (d a)) F) (p q : Σ a, Fin (d a)) :
    ((diagHom b e he x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (e p) (e q) =
      Matrix.blockDiagonal' (fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)) p q := by
  show Matrix.blockDiagonal' (fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)) (e.symm (e p)) (e.symm (e q)) = _
  rw [e.symm_apply_apply, e.symm_apply_apply]

omit [Fintype ι] [DecidableEq ι] in

theorem exists_blocks (b : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1)
    (p : blockTri (κ := F) b) : ∃ x : ∀ a, GL (Fin (d a)) F, ∀ a i j, (x a : Matrix (Fin (d a)) (Fin (d a)) F) i j =
      ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (e ⟨a, i⟩) (e ⟨a, j⟩) := by
  refine ⟨fun a => GlobalTheory.Parabolic.leviBlock b (fun i => e ⟨a, i⟩)
    (fun _ _ hij => sigma_mk_injective (β := fun a => Fin (d a)) (e.injective hij)) (fun i j hij => ?_)
    (GlobalTheory.Parabolic.leviProj b p), fun a i j => ?_⟩
  · obtain ⟨⟨c, l⟩, rfl⟩ := e.surjective j
    obtain rfl : a = c := (he _ _).1 hij
    exact ⟨l, rfl⟩
  · exact if_pos ((he ⟨a, i⟩ ⟨a, j⟩).2 rfl)

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem act_eq {b : Fin r → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1)
    {σ : Representation ℂ (blockTri (κ := F) b) V} (hσ : IsCuspDatum b σ) (p : blockTri (κ := F) b)
    (x : ∀ a, GL (Fin (d a)) F) (hx : ∀ a i j, (x a : Matrix (Fin (d a)) (Fin (d a)) F) i j =
      ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (e ⟨a, i⟩) (e ⟨a, j⟩)) :
    σ p = σ (diagHom b e he x) := by
  obtain ⟨m, hm, hm'⟩ := IsCuspDatum.exists_blockDiag_act_eq F r V b σ hσ p
  rw [← hm]
  congr 1
  apply Subtype.ext
  apply Units.ext
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨c, j⟩, rfl⟩ := e.surjective j
  rw [hm', diagHom_apply]
  by_cases hac : a = c
  · subst hac
    rw [Matrix.blockDiagonal'_apply_eq, if_pos ((he ⟨a, i⟩ ⟨a, j⟩).2 rfl), hx]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hac, if_neg (fun h => hac ((he _ _).1 h))]

theorem irr_comp {b : Fin r → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1)
    {σ : Representation ℂ (blockTri (κ := F) b) V} (hσ : IsCuspDatum b σ) :
    Representation.IsIrreducible (σ.comp (diagHom b e he) : Representation ℂ (∀ a, GL (Fin (d a)) F) V) := by
  have hi := hσ.irr
  let φ : Subrepresentation (σ.comp (diagHom b e he) : Representation ℂ (∀ a, GL (Fin (d a)) F) V) ≃o
      Subrepresentation σ :=
    { toFun := fun W => ⟨W.toSubmodule, fun p v hv => by
        obtain ⟨x, hx⟩ := exists_blocks b e he p
        rw [act_eq e he hσ p x hx]
        exact W.apply_mem_toSubmodule x hv⟩
      invFun := fun W => ⟨W.toSubmodule, fun x v hv => W.apply_mem_toSubmodule (diagHom b e he x) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact φ.isSimpleOrder_iff.2 hi

theorem sum_act_eq_zero {b : Fin r → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1)
    {σ : Representation ℂ (blockTri (κ := F) b) V} (hσ : IsCuspDatum b σ) (c : ι) (a : ℕ) (h0 : 0 < a)
    (h1 : a < d c) (H : Subgroup (GL (Fin (d c)) F)) [Fintype H]
    (hH : (H : Set (GL (Fin (d c)) F)) = {u : GL (Fin (d c)) F | ∀ i j : Fin (d c),
      (u : Matrix (Fin (d c)) (Fin (d c)) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}) :
    ∑ u : H, σ (diagHom b e he (Pi.mulSingle c (u : GL (Fin (d c)) F))) = 0 := by
  ext v
  rw [LinearMap.sum_apply, LinearMap.zero_apply]
  refine hσ.cusp (Finset.univ.filter fun i => (e.symm i).1 = c ∧ (e.symm i).2.val < a)
    ⟨e ⟨c, ⟨0, h0.trans h1⟩⟩, e ⟨c, ⟨a, h1⟩⟩, (he _ _).2 rfl, ?_, ?_⟩ _ fun u hu => ?_
  · rw [Finset.mem_filter, e.symm_apply_apply]
    exact ⟨Finset.mem_univ _, rfl, h0⟩
  · rw [Finset.mem_filter, e.symm_apply_apply]
    exact fun h => lt_irrefl _ h.2.2
  obtain ⟨x, hx⟩ := exists_blocks b e he u
  have key : ∀ c' i j, (x c' : Matrix (Fin (d c')) (Fin (d c')) F) i j = (if i = j then 1 else 0) ∨
      (c' = c ∧ i.val < a ∧ a ≤ j.val) := by
    intro c' i j
    refine or_iff_not_imp_left.2 fun hne => ?_
    have h := hu (e ⟨c', i⟩) (e ⟨c', j⟩) (by
      rw [← hx, Matrix.one_apply]
      simpa using hne)
    rw [Finset.mem_filter, Finset.mem_filter, e.symm_apply_apply, e.symm_apply_apply] at h
    obtain ⟨-, ⟨-, h2, h3⟩, h4⟩ := h
    exact ⟨h2, h3, not_lt.1 fun h5 => h4 ⟨Finset.mem_univ _, h2, h5⟩⟩
  have hxc : x c ∈ H := by
    rw [← SetLike.mem_coe, hH]
    exact fun i j => (key c i j).imp id fun h => h.2
  have hx1 : x = Pi.mulSingle c (x c) := by
    funext c'
    by_cases hc : c' = c
    · subst hc
      rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hc]
      apply Units.ext
      ext i j
      rw [Units.val_one, Matrix.one_apply]
      exact (key c' i j).resolve_right fun h => hc h.1
  rw [act_eq e he hσ u x hx, hx1, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨x c, hxc⟩ : H)) _ _ fun w => ?_
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, ← Pi.mulSingle_mul]
  rfl

theorem irrChar_one_ne_zero {G : Type} [Group G] [Finite G] {χ : G → ℂ} (h : IsIrrChar ℂ ℂ χ) : χ 1 ≠ 0 := by
  have hp := GlobalTheory.BI.pair_self_of_isIrrChar_algClosed ℂ G χ h
  obtain ⟨n, ρ, -, hρ⟩ := h
  intro h1
  have hn : n = 0 := by
    rw [hρ] at h1
    simpa [Representation.character] using h1
  subst hn
  have : χ = 0 := by
    funext g
    rw [hρ, Representation.character, Subsingleton.elim (ρ g) 0]
    simp
  rw [this] at hp
  simp [pair] at hp

theorem exists_prod [Finite F] {b : Fin r → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin r)
    (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1) {n : ℕ}
    {σ : Representation ℂ (blockTri (κ := F) b) (Fin n → ℂ)} (hσ : IsCuspDatum b σ) :
    ∃ ψ : ∀ a, GL (Fin (d a)) F → ℂ, (∀ a, IsIrrChar ℂ ℂ (ψ a) ∧ IsPrimitive (extZero (ψ a))) ∧
      ∀ (p : blockTri (κ := F) b) (x : ∀ a, GL (Fin (d a)) F), (∀ a i j, (x a : Matrix (Fin (d a)) (Fin (d a)) F) i j =
      ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (e ⟨a, i⟩) (e ⟨a, j⟩)) → σ.character p = ∏ a, ψ a (x a) := by
  obtain ⟨ψ, hψ, hprod⟩ := GlobalTheory.T.irreducible_character_of_product ι (fun a => GL (Fin (d a)) F) (fun x => σ.character (diagHom b e he x))
    ⟨n, σ.comp (diagHom b e he), irr_comp e he hσ, fun _ => rfl⟩
  refine ⟨ψ, fun c => ⟨hψ c, ?_⟩, fun p x hx => ?_⟩
  · refine isPrimitive_extZero_of_sum_unipotent F _ _ ?_ fun a h0 h1 => ?_
    · obtain ⟨m, ρ, -, hρ⟩ := hψ c
      exact ⟨m, ρ, hρ⟩
    obtain ⟨-, H, -, hH, -⟩ := GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical F (d c) a h1.le
    letI : Fintype H := Fintype.ofFinite H
    have hs := congrArg (LinearMap.trace ℂ (Fin n → ℂ)) (sum_act_eq_zero e he hσ c a h0 h1 H hH)
    rw [map_sum, map_zero] at hs
    have hv : ∀ u : GL (Fin (d c)) F, LinearMap.trace ℂ (Fin n → ℂ) (σ (diagHom b e he (Pi.mulSingle c u))) =
        ψ c u * ∏ c' ∈ Finset.univ.erase c, ψ c' 1 := by
      intro u
      refine (hprod _).trans ?_
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c), Pi.mulSingle_eq_same]
      congr 1
      refine Finset.prod_congr rfl fun c' hc' => ?_
      rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hc')]
    simp only [hv] at hs
    rw [← Finset.sum_mul] at hs
    have hs' := (mul_eq_zero.1 hs).resolve_right
      (Finset.prod_ne_zero_iff.2 fun c' _ => irrChar_one_ne_zero (hψ c'))
    rw [← hH, ← finsum_set_coe_eq_finsum_mem (f := ψ c) (H : Set (GL (Fin (d c)) F))]
    exact (finsum_eq_sum_of_fintype (fun u : H => ψ c u)).trans hs'
  · rw [← hprod x, Representation.character, act_eq e he hσ p x hx]
    rfl

theorem character_eq_prod_blocks : ∀ (F : Type) [Field F] [Finite F] (r : ℕ) (b : Fin r → ℕ) (n : ℕ) (σ : Representation ℂ (blockTri (κ := F) b) (Fin n → ℂ)), IsCuspDatum b σ → ∃ χ : ∀ c : ℕ, GL (Fin (Fintype.card {a : Fin r // b a = c})) F → ℂ, (∀ c ∈ Finset.univ.image b, IsIrrChar ℂ ℂ (χ c) ∧ IsPrimitive (extZero (χ c))) ∧ ∀ (p : blockTri (κ := F) b) (x : ∀ c : ℕ, GL (Fin (Fintype.card {a : Fin r // b a = c})) F), (∀ c, (x c : Matrix _ _ F) = Matrix.reindex (Fintype.equivFin _) (Fintype.equivFin _) (blkMat b c p)) → σ.character p = ∏ c ∈ Finset.univ.image b, χ c (x c) := by
  intro F _ _ r b n σ hσ
  let f : (Σ c : ↥(Finset.univ.image b), Fin (Fintype.card {a : Fin r // b a = c.1})) → Fin r :=
    fun x => ((Fintype.equivFin {a : Fin r // b a = x.1.1}).symm x.2).1
  have hf : ∀ x, b (f x) = x.1.1 := fun x => ((Fintype.equivFin {a : Fin r // b a = x.1.1}).symm x.2).2
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨c, i⟩ ⟨c', j⟩ h
      obtain rfl : c = c' := Subtype.ext ((hf ⟨c, i⟩).symm.trans ((congrArg b h).trans (hf ⟨c', j⟩)))
      obtain rfl : i = j := (Fintype.equivFin {a : Fin r // b a = c.1}).symm.injective (Subtype.ext h)
      rfl
    · intro i
      refine ⟨⟨⟨b i, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, Fintype.equivFin _ ⟨i, rfl⟩⟩, ?_⟩
      simp only [f, Equiv.symm_apply_apply]
  obtain ⟨ψ, hψ, hprod⟩ := exists_prod (F := F) (b := b) (Equiv.ofBijective f hbij) (fun x y => by
    rw [Equiv.ofBijective_apply, Equiv.ofBijective_apply, hf, hf, Subtype.ext_iff]) hσ
  refine ⟨fun c => if h : c ∈ Finset.univ.image b then ψ ⟨c, h⟩ else 0, fun c hc => ?_, fun p x hx => ?_⟩
  · simp only [dif_pos hc]
    exact hψ ⟨c, hc⟩
  · rw [hprod p (fun c => x c.1) fun c i j => by rw [hx]; rfl,
      ← Finset.prod_coe_sort (Finset.univ.image b)]
    refine Finset.prod_congr rfl fun c _ => ?_
    simp only [dif_pos c.2]

end GlobalTheory.FinGL.LeviChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp
section
noncomputable section

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.HCAlpha

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)

def lapOp : Module.End ℂ (Sm E a) :=
  ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a,
    ((lieS E a i j (atEmb τ 1)) ^ 2 + (lieS E a i j (atEmb τ Complex.I)) ^ 2)

def casKOp : Module.End ℂ (Sm E a) :=
  ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a, (1 / 4 : ℂ) •
    ((lieS E a i j (atEmb τ 1) - lieS E a j i (atEmb τ 1)) ^ 2 +
      (lieS E a i j (atEmb τ Complex.I) + lieS E a j i (atEmb τ Complex.I)) ^ 2)

def vecF (X : Lie E a) (f : Lie E a → ℂ) : Lie E a → ℂ := fun y => fderiv ℝ f y (rmul X y)

def lapF (f : Lie E a → ℂ) : Lie E a → ℂ :=
  ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a,
    (vecF E a (toL (Matrix.single i j (atEmb τ 1))) (vecF E a (toL (Matrix.single i j (atEmb τ 1))) f) +
      vecF E a (toL (Matrix.single i j (atEmb τ Complex.I))) (vecF E a (toL (Matrix.single i j (atEmb τ Complex.I))) f))

def polyF (p : Polynomial ℂ) (f : Lie E a → ℂ) : Lie E a → ℂ :=
  ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • (lapF E a)^[k] f

end GlobalTheory.HCAlpha

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAugEqvOfIsIntegralHomOfStrictlyHenselianStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eqv_cechAug_of_isIntegralHom_of_surjective_of_sh : ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of A)), IsIntegralHom g → Surjective g → Eqv _ (cechAug g) (tw q i) := by
  first
  | exact @GlobalTheory.EtC.cechAug_eqv_of_isIntegralHom_of_strictlyHenselian
  | exact GlobalTheory.EtC.cechAug_eqv_of_isIntegralHom_of_strictlyHenselian
  | (intros; apply GlobalTheory.EtC.cechAug_eqv_of_isIntegralHom_of_strictlyHenselian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelAcyclicStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_cech_level_eq_zero_of_pos : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ) (m : ℕ), 0 < m → ∀ y : H R (disc.obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op (SimplexCategory.mk (k))))) F m, y = 0 := by
  first
  | exact @GlobalTheory.EtC.cech_level_acyclic
  | exact GlobalTheory.EtC.cech_level_acyclic
  | (intros; apply GlobalTheory.EtC.cech_level_acyclic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CenterActsByScalarOnEigenformsStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.center_acts_by_scalar_on_eigenforms : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (c : (E →+* ℂ) → ℂ → ℂ) (z : Module.End ℂ (GlobalTheory.CuspRep.Sm E a)), z ∈ GlobalTheory.CuspRep.Zalg E a → ∃ s : ℂ, ∀ φ : GlobalTheory.CuspRep.Sm E a, (∀ τ u, GlobalTheory.CuspRep.cap τ u φ = c τ u • φ) → z φ = s • φ := by
  first | exact @GlobalTheory.CuspRep.Zalg_acts_by_scalar | exact GlobalTheory.CuspRep.Zalg_acts_by_scalar | (intros; apply GlobalTheory.CuspRep.Zalg_acts_by_scalar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartUnipotentFderivContinuousOnStatement
section
open NumberField GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_unipotent_fderiv_continuousOn : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (φ : GlobalTheory.CuspRep.Sm E a), GlobalTheory.CuspRep.IsAutForm φ → ∀ (g : GlobalTheory.CuspRep.GA E a) (X : GlobalTheory.CuspRep.Lie E a), ContinuousOn (fun p : (GlobalTheory.CuspRep.BlockIx a r → GlobalTheory.CuspRep.Ad E) × GlobalTheory.CuspRep.Lie E a => GlobalTheory.CuspRep.chart φ.1 (GlobalTheory.CuspRep.unip p.1 * g) p.2) (Set.univ ×ˢ GlobalTheory.CuspRep.invSet E a) ∧ ContinuousOn (fun p : (GlobalTheory.CuspRep.BlockIx a r → GlobalTheory.CuspRep.Ad E) × GlobalTheory.CuspRep.Lie E a => fderiv ℝ (GlobalTheory.CuspRep.chart φ.1 (GlobalTheory.CuspRep.unip p.1 * g)) p.2 X) (Set.univ ×ˢ GlobalTheory.CuspRep.invSet E a) := by
  first | exact @GlobalTheory.CuspRep.JointCont.chart_jointCont | exact GlobalTheory.CuspRep.JointCont.chart_jointCont | (intros; apply GlobalTheory.CuspRep.JointCont.chart_jointCont <;> assumption)
end

