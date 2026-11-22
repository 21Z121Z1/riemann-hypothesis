import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryOsc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0034
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1032
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnramifiedExtTorsionPointsGoodReduction

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionNormalisingSchrodingerOper
section
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil Matrix

noncomputable section

namespace GlobalTheory.SchrodOsc

section Sign

variable {N : Type} [Fintype N] [DecidableEq N] (pos : N → Bool)

def signEquiv : N ≃ Fin (Fintype.card {n // pos n = true}) ⊕ Fin (Fintype.card {n // ¬ pos n = true}) :=
  (Equiv.sumCompl (fun n => pos n = true)).symm.trans
    (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _))

theorem pos_signEquiv_symm_inl (i : Fin (Fintype.card {n // pos n = true})) :
    pos ((signEquiv pos).symm (Sum.inl i)) = true := by
  simp only [signEquiv, Equiv.symm_trans_apply, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.symm_symm, Equiv.sumCompl_apply_inl]
  exact ((Fintype.equivFin _).symm i).2

theorem pos_signEquiv_symm_inr (j : Fin (Fintype.card {n // ¬ pos n = true})) :
    pos ((signEquiv pos).symm (Sum.inr j)) = false := by
  simp only [signEquiv, Equiv.symm_trans_apply, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr,
    Equiv.symm_symm, Equiv.sumCompl_apply_inr]
  simpa using ((Fintype.equivFin _).symm j).2

theorem fromBlocks_eq_reindex :
    (fromBlocks 1 0 0 (-1) : Matrix (Fin (Fintype.card {n // pos n = true}) ⊕ Fin (Fintype.card {n // ¬ pos n = true}))
      (Fin (Fintype.card {n // pos n = true}) ⊕ Fin (Fintype.card {n // ¬ pos n = true})) ℂ) =
      reindex (signEquiv pos) (signEquiv pos) (diagonal fun n => if pos n then 1 else -1) := by
  rw [reindex_apply, submatrix_diagonal_equiv]
  have h1 : (1 : Matrix (Fin (Fintype.card {n // pos n = true})) (Fin (Fintype.card {n // pos n = true})) ℂ) =
      diagonal fun _ => 1 := diagonal_one.symm
  have h2 : (-1 : Matrix (Fin (Fintype.card {n // ¬ pos n = true})) (Fin (Fintype.card {n // ¬ pos n = true})) ℂ) =
      diagonal fun _ => -1 := by rw [← diagonal_neg, diagonal_one]
  rw [h1, h2, fromBlocks_diagonal]
  congr 1
  funext i
  rcases i with i | j
  · simp [pos_signEquiv_symm_inl]
  · simp [pos_signEquiv_symm_inr]

end Sign

end GlobalTheory.SchrodOsc

namespace GlobalTheory.SchrodOsc

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ}

def sgn (n : Ix R S × (ι × Ix P Q)) : Bool := linePos (p := P) (q := Q) (r := R) (s := S) (n.2.2, n.1)

theorem lineSign_eq (a : Ix P Q) (b : Ix R S) : lineSign a b = if linePos (a, b) then 1 else -1 := by
  rcases a with a | a <;> rcases b with b | b <;> rfl

theorem Jm_transpose (R S : ℕ) : (Jm R S)ᵀ = Jm R S := by
  simp [Jm, Formalism.UG.Jpq, fromBlocks_transpose]

theorem Jm_map_star (R S : ℕ) : (Jm R S).map star = Jm R S := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [Jm, Formalism.UG.Jpq, one_apply] <;> split_ifs <;> simp

theorem diagonal_sgn : (diagonal fun n : Ix R S × (ι × Ix P Q) => if sgn n then (1 : ℂ) else -1) =
    blockDiagonal fun o : ι × Ix P Q => Jm P Q o.2 o.2 • Jm R S := by
  ext ⟨b, w, a⟩ ⟨b', w', a'⟩
  rcases a with a | a <;> rcases b with b | b <;> rcases b' with b' | b' <;>
    simp [diagonal_apply, blockDiagonal_apply, Jm, Formalism.UG.Jpq, sgn, linePos, one_apply, Prod.ext_iff] <;>
    split_ifs <;> simp_all

theorem blockDiagonal_mem (M : ι → Mat R S) (hM : ∀ w, (M w)ᴴ * Jm R S * M w = Jm R S) :
    (blockDiagonal fun o : ι × Ix P Q => M o.1)ᵀ *
        (diagonal fun n : Ix R S × (ι × Ix P Q) => if sgn n then (1 : ℂ) else -1) *
        (blockDiagonal fun o : ι × Ix P Q => M o.1).map star =
      diagonal fun n : Ix R S × (ι × Ix P Q) => if sgn n then (1 : ℂ) else -1 := by
  rw [diagonal_sgn, blockDiagonal_transpose, blockDiagonal_map _ _ (star_zero ℂ), ← blockDiagonal_mul,
    ← blockDiagonal_mul]
  congr 1
  funext o
  have h := congrArg transpose (hM o.1)
  rw [transpose_mul, transpose_mul, Jm_transpose] at h
  have e : (M o.1)ᴴᵀ = (M o.1).map star := by ext; simp
  rw [e] at h
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, h]

end Block

end GlobalTheory.SchrodOsc

namespace GlobalTheory.SchrodOsc

section Hom

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ} {G : Type} [Group G]

abbrev lineNum (ι : Type) [Fintype ι] [DecidableEq ι] (P Q R S : ℕ) :=
  signEquiv (sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S))

def blockHom (P Q : ℕ) (k : G →* (ι → Mat R S)) :
    G →* Matrix (Ix R S × (ι × Ix P Q)) (Ix R S × (ι × Ix P Q)) ℂ where
  toFun g := blockDiagonal fun o : ι × Ix P Q => k g o.1
  map_one' := by
    simp only [map_one, Pi.one_apply]
    exact blockDiagonal_one
  map_mul' g g' := by simp [blockDiagonal_mul]

def numHom (P Q : ℕ) (k : G →* (ι → Mat R S)) : G →* Matrix (Fin (Fintype.card {n // sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) ⊕ Fin (Fintype.card {n // ¬ sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}))
      (Fin (Fintype.card {n // sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) ⊕ Fin (Fintype.card {n // ¬ sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true})) ℂ :=
  (reindexAlgEquiv ℂ ℂ (lineNum ι P Q R S)).toAlgHom.toRingHom.toMonoidHom.comp (blockHom P Q k)

theorem numHom_apply (k : G →* (ι → Mat R S)) (g : G) :
    numHom P Q k g = reindex (lineNum ι P Q R S) (lineNum ι P Q R S) (blockDiagonal fun o : ι × Ix P Q => k g o.1) :=
  rfl

theorem numHom_mem (k : G →* (ι → Mat R S)) (hk : ∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) (g : G) :
    (numHom P Q k).toHomUnits g ∈ GlobalTheory.WeilM.UG (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) (fromBlocks 1 0 0 (-1)) := by
  have hc : ⇑(Complex.conjAe : ℂ →ₐ[ℝ] ℂ) = star := funext fun x => by simp
  show (numHom P Q k g)ᵀ * fromBlocks 1 0 0 (-1) * (numHom P Q k g).map (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) =
    fromBlocks 1 0 0 (-1)
  rw [hc, numHom_apply, fromBlocks_eq_reindex, transpose_reindex]
  have hm : (reindex (lineNum ι P Q R S) (lineNum ι P Q R S) (blockDiagonal fun o : ι × Ix P Q => k g o.1)).map star =
      reindex (lineNum ι P Q R S) (lineNum ι P Q R S) ((blockDiagonal fun o : ι × Ix P Q => k g o.1).map star) := rfl
  rw [hm, ← reindexAlgEquiv_apply ℂ ℂ, ← reindexAlgEquiv_apply ℂ ℂ, ← reindexAlgEquiv_apply ℂ ℂ, ← map_mul, ← map_mul,
    blockDiagonal_mem _ (hk g)]

def unitHom (P Q : ℕ) (k : G →* (ι → Mat R S)) (hk : ∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) :=
  (numHom P Q k).toHomUnits.codRestrict _ (numHom_mem k hk)

theorem continuous_unitHom [TopologicalSpace G] [IsTopologicalGroup G] (k : G →* (ι → Mat R S)) (hc : Continuous k)
    (hk : ∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) : Continuous (unitHom P Q k hk) := by
  have hn : Continuous (numHom P Q k) := by
    show Continuous fun g => reindex (lineNum ι P Q R S) (lineNum ι P Q R S) (blockDiagonal fun o : ι × Ix P Q => k g o.1)
    exact (Continuous.matrix_blockDiagonal (continuous_pi fun (o : ι × Ix P Q) => (continuous_apply o.1).comp hc)).matrix_reindex _ _
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨hn, ?_⟩)
  have : (fun g => (((Subtype.val ∘ unitHom P Q k hk) g)⁻¹ : GL _ ℂ).val) = fun g => numHom P Q k g⁻¹ := by
    funext g
    simp only [Function.comp_apply]
    rw [← Subgroup.coe_inv, ← map_inv]
    rfl
  rw [this]
  exact hn.comp continuous_inv

end Hom

end GlobalTheory.SchrodOsc

namespace GlobalTheory.SchrodOsc

section Final

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ}

def coordOf (z : Fin (Fintype.card {n // sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) ⊕
    Fin (Fintype.card {n // ¬ sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) → ℂ) :
    ι → Matrix (Ix P Q) (Ix R S) ℂ :=
  fun w a b => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * z (lineNum ι P Q R S (b, (w, a)))

theorem coordOf_add (z z' : Fin (Fintype.card {n // sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) ⊕
    Fin (Fintype.card {n // ¬ sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) → ℂ) :
    coordOf (z + z') = coordOf z + coordOf z' := by
  funext w a b
  simp [coordOf, mul_add]

theorem continuous_coordOf : Continuous (coordOf (ι := ι) (P := P) (Q := Q) (R := R) (S := S)) :=
  continuous_pi fun _ => continuous_pi fun _ => continuous_pi fun _ => continuous_const.mul (continuous_apply _)

theorem two_mul_sum_coordOf (z z' : Fin (Fintype.card {n // sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) ⊕
    Fin (Fintype.card {n // ¬ sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) → ℂ) :
    2 * ∑ w, ∑ a, ∑ b, lineSign a b * coordOf z w a b * star (coordOf z' w a b) =
      (∑ i, z (Sum.inl i) * star (z' (Sum.inl i))) - ∑ j, z (Sum.inr j) * star (z' (Sum.inr j)) := by
  set e := lineNum ι P Q R S with he
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = 2⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]
    push_cast
    rfl
  let F : Ix R S × (ι × Ix P Q) → ℂ := fun n => (if sgn n then 1 else -1) * z (e n) * star (z' (e n))
  have h1 : ∀ w a b, lineSign a b * coordOf z w a b * star (coordOf z' w a b) = 2⁻¹ * F (b, (w, a)) := by
    intro w a b
    simp only [coordOf, F, star_mul, sgn, lineSign_eq]
    rw [← hs, he]
    by_cases h : linePos (a, b) = true <;> simp only [h, ↓reduceIte, Bool.false_eq_true] <;> ring
  have h2 : ∑ n, F n = ∑ w, ∑ a, ∑ b, F (b, (w, a)) := by
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun w _ => Finset.sum_comm
  have h3 : ∑ n, F n = ∑ i, F (e.symm i) := (e.symm.sum_comp F).symm
  simp_rw [h1, ← Finset.mul_sum, ← h2, h3, Fintype.sum_sum_type]
  simp only [F, he, pos_signEquiv_symm_inl, pos_signEquiv_symm_inr, Equiv.apply_symm_apply]
  simp
  ring

theorem coordOf_mulVec {G : Type} [Group G] (k : G →* (ι → Mat R S)) (hk : ∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S)
    (g : G) (z : Fin (Fintype.card {n // sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) ⊕
    Fin (Fintype.card {n // ¬ sgn (ι := ι) (P := P) (Q := Q) (R := R) (S := S) n = true}) → ℂ) :
    coordOf (((unitHom P Q k hk g).1 : Matrix _ _ ℂ) *ᵥ z) = fun w => coordOf z w * (k g w)ᵀ := by
  show coordOf (numHom P Q k g *ᵥ z) = _
  rw [numHom_apply, reindex_apply, submatrix_mulVec_equiv]
  funext w
  ext a b
  simp [coordOf, mulVec, dotProduct, blockDiagonal_apply, Fintype.sum_prod_type, mul_apply, Finset.mul_sum, ite_mul]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring

end Final

end GlobalTheory.SchrodOsc

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

theorem GlobalTheory.SchrodOsc.exists_osc : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    (∀ v : L2 l, Continuous fun w : l ⊕ l → ℝ => rho w v) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (k : G →* (ι → Mat R S)), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) →
    ∃ ω : G →* (L2 l ≃ₗᵢ[ℂ] L2 l), (∀ v, Continuous fun g => ω g v) ∧
      ∀ g c v, ω g (rho (φ c) v) = rho (φ fun w => c w * (k g w)ᵀ) (ω g v) := by
  intro ι l _ _ _ _ P Q R S φ hφ hcont G _ _ _ k hkc hk
  obtain ⟨ω₀, hω₀c, hω₀, -⟩ := GlobalTheory.FockRep.exists_unitary_osc _ _ (L2 l)
    (fun z => rho (φ (GlobalTheory.SchrodOsc.coordOf z)))
    (fun v => (hcont v).comp ((LinearMap.continuous_of_finiteDimensional φ.toLinearMap).comp
      GlobalTheory.SchrodOsc.continuous_coordOf))
    (fun z z' v => by
      rw [rho_rho, ← map_add, ← GlobalTheory.SchrodOsc.coordOf_add, hφ, ← GlobalTheory.SchrodOsc.two_mul_sum_coordOf]
      congr 2
      simp [Complex.mul_im]
      ring)
  refine ⟨ω₀.comp (GlobalTheory.SchrodOsc.unitHom P Q k hk), fun v => (hω₀c v).comp (GlobalTheory.SchrodOsc.continuous_unitHom k hkc hk),
    fun g c v => ?_⟩
  obtain ⟨z, hz⟩ : ∃ z, GlobalTheory.SchrodOsc.coordOf (ι := ι) (P := P) (Q := Q) (R := R) (S := S) z = c := by
    refine ⟨fun i => ((Real.sqrt 2 : ℝ) : ℂ) * (fun n : Ix R S × (ι × Ix P Q) => c n.2.1 n.2.2 n.1)
      ((GlobalTheory.SchrodOsc.lineNum ι P Q R S).symm i), ?_⟩
    funext w a b
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 two_pos).ne'
    simp [GlobalTheory.SchrodOsc.coordOf, h2]
  have h := hω₀ (GlobalTheory.SchrodOsc.unitHom P Q k hk g) z v
  rw [hz, GlobalTheory.SchrodOsc.coordOf_mulVec, hz] at h
  exact h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarDecompositionIndefiniteUnitary
section
open scoped Matrix
open Formalism.BasicNotions.TH

namespace GlobalTheory.UnitaryPolar

open Matrix
open scoped MatrixOrder ComplexOrder

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem root {S A : Matrix ι ι ℂ} (h1 : S * S = 1) (h2 : Sᴴ = S) (hA : A.PosSemidef)
    (h : A * S * A = S) : ∃ R : Matrix ι ι ℂ, R.PosSemidef ∧ R * R = A ∧ R * S * R = S := by
  obtain ⟨R, hR, hRR, hu⟩ : ∃ R : Matrix ι ι ℂ, R.PosSemidef ∧ R * R = A ∧
      ∀ T : Matrix ι ι ℂ, T.PosSemidef → T * T = A → R = T :=
    ⟨CFC.sqrt A, (CFC.sqrt_nonneg A).posSemidef, CFC.sqrt_mul_sqrt_self A hA.nonneg,
      fun T hT e => CFC.sqrt_unique e hT.nonneg⟩
  have a1 : R * (R * (S * A * S)) = 1 := by
    rw [← Matrix.mul_assoc, hRR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, h1]
  have a2 : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R (Matrix.isUnit_det_of_right_inverse a1)
  have a3 : R⁻¹ * R⁻¹ = S * A * S := by
    calc R⁻¹ * R⁻¹ = R⁻¹ * R⁻¹ * (R * (R * (S * A * S))) := by rw [a1, Matrix.mul_one]
      _ = R⁻¹ * (R⁻¹ * R) * R * (S * A * S) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [a2, Matrix.mul_one, a2, Matrix.one_mul]
  have a4 : R = S * R⁻¹ * S := by
    refine hu _ ?_ ?_
    · have := hR.inv.conjTranspose_mul_mul_same S
      rwa [h2] at this
    · calc S * R⁻¹ * S * (S * R⁻¹ * S) = S * (R⁻¹ * (S * S) * R⁻¹) * S := by simp only [Matrix.mul_assoc]
        _ = (S * S) * A * (S * S) := by rw [h1, Matrix.mul_one, a3, ← h1]; simp only [Matrix.mul_assoc]
        _ = A := by rw [h1, Matrix.mul_one, Matrix.one_mul]
  refine ⟨R, hR, hRR, ?_⟩
  calc R * S * R = S * R⁻¹ * S * S * R := by rw [← a4]
    _ = S * (R⁻¹ * (S * S) * R) := by simp only [Matrix.mul_assoc]
    _ = S := by rw [h1, Matrix.mul_one, a2, Matrix.mul_one]

theorem polar_inv {S U : Matrix ι ι ℂ} (h1 : S * S = 1) (h2 : Sᴴ = S) (hU : Uᴴ * S * U = S) :
    ∃ K Q : Matrix ι ι ℂ, Kᴴ * S * K = S ∧ S * K = K * S ∧ Qᴴ * S * Q = S ∧ S * Q * S * Q = 1 ∧
      U = K * Q * Q := by
  have hS : ∀ X : Matrix ι ι ℂ, S * (S * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have b1 : (S * Uᴴ * S) * U = 1 := by
    rw [Matrix.mul_assoc S, Matrix.mul_assoc S, hU, h1]
  have b2 : U * S * Uᴴ = S := by
    have := congrArg (· * S) (mul_eq_one_comm.1 b1)
    simpa only [Matrix.mul_assoc, h1, Matrix.mul_one, Matrix.one_mul] using this
  obtain ⟨P, hP, hPP, hPS⟩ := root h1 h2 (Matrix.posSemidef_conjTranspose_mul_self U) (by
    calc Uᴴ * U * S * (Uᴴ * U) = Uᴴ * (U * S * Uᴴ) * U := by simp only [Matrix.mul_assoc]
      _ = S := by rw [b2, hU])
  obtain ⟨Q, hQ, hQQ, hQS⟩ := root h1 h2 hP hPS
  have hP' : ∀ X : Matrix ι ι ℂ, P * (S * (P * X)) = S * X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPS]
  have c0 : (U * (S * P * S))ᴴ = S * P * S * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, h2, hP.isHermitian.eq, Matrix.mul_assoc]
  have c1 : (U * (S * P * S))ᴴ * S * (U * (S * P * S)) = S := by
    rw [c0]
    calc _ = S * P * S * (Uᴴ * S * U) * (S * P * S) := by simp only [Matrix.mul_assoc]
      _ = S := by rw [hU]; simp only [Matrix.mul_assoc, hS, hP']
  have c2 : (U * (S * P * S))ᴴ * (U * (S * P * S)) = 1 := by
    rw [c0]
    calc _ = S * P * S * (Uᴴ * U) * (S * P * S) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← hPP]; simp only [Matrix.mul_assoc, hS, hP', h1]
  refine ⟨U * (S * P * S), Q, c1, ?_, by rw [hQ.isHermitian.eq, hQS], ?_, ?_⟩
  · generalize U * (S * P * S) = K at c1 c2
    calc S * K = (K * Kᴴ) * S * K := by rw [mul_eq_one_comm.1 c2, Matrix.one_mul]
      _ = K * (Kᴴ * S * K) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [c1]
  · rw [Matrix.mul_assoc S, Matrix.mul_assoc S, hQS, h1]
  · rw [Matrix.mul_assoc _ Q, hQQ, Matrix.mul_assoc, Matrix.mul_assoc S, Matrix.mul_assoc S, hPS, h1, Matrix.mul_one]

theorem jm_mul_self (R S : ℕ) : Jm R S * Jm R S = 1 := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem jm_conjTranspose (R S : ℕ) : (Jm R S)ᴴ = Jm R S := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem polar (R S : ℕ) (u : Mat R S) (hu : uᴴ * Jm R S * u = Jm R S) :
    ∃ k q : Mat R S, kᴴ * Jm R S * k = Jm R S ∧
      Jm R S * k = k * Jm R S ∧ qᴴ * Jm R S * q = Jm R S ∧ Jm R S * q * Jm R S * q = 1 ∧ u = k * q * q :=
  polar_inv (jm_mul_self R S) (jm_conjTranspose R S) hu

end GlobalTheory.UnitaryPolar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatedSetCoversSeminormBall
section
open Filter Topology GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.VolBr

theorem exists_sep_cover : ∀ (G : Type) [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B →
    ∀ R : ℝ, (B R).Finite → ∃ T : Finset G, (T : Set G) ⊆ B R ∧ (∀ x ∈ T, ∀ y ∈ T, x ≠ y → x - y ∉ B 1) ∧
      (B R).encard ≤ T.card * (B 1).encard := by
  intro G _ Λ B hB R hfin
  classical
  let sep : Finset G → Prop := fun T => ∀ x ∈ T, ∀ y ∈ T, x ≠ y → x - y ∉ B 1
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image (hfin.toFinset.powerset.filter sep) Finset.card
    ⟨∅, by simp [sep]⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hT
  obtain ⟨hTS, hTsep⟩ := hT
  have hsub : (T : Set G) ⊆ B R := fun x hx => hfin.mem_toFinset.1 (hTS hx)
  have h0 : (0 : G) ∈ B 1 := hB.zero_mem 1 zero_le_one
  have hsymm : ∀ u, u ∈ B 1 → -u ∈ B 1 := by
    intro u hu
    have := hB.sub_mem 0 1 0 u (hB.zero_mem 0 le_rfl) hu
    simpa using this
  have hcov : ∀ x ∈ B R, ∃ t ∈ T, x - t ∈ B 1 := by
    intro x hx
    by_cases hxT : x ∈ T
    · exact ⟨x, hxT, by simpa using h0⟩
    by_contra hne
    push_neg at hne
    have hins : insert x T ∈ hfin.toFinset.powerset.filter sep := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.insert_subset (hfin.mem_toFinset.2 hx) hTS, ?_⟩
      intro a ha b hb hab
      rw [Finset.mem_insert] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact absurd (ha.trans hb.symm) hab
      · rw [ha]; exact hne b hb
      · rw [hb]; intro h; exact hne a ha (by simpa using hsymm _ h)
      · exact hTsep a ha b hb hab
    have hc := hmax _ hins
    rw [Finset.card_insert_of_notMem hxT] at hc
    omega
  choose! f hfT hf using hcov
  refine ⟨T, hsub, hTsep, ?_⟩
  have hmaps : Set.MapsTo (fun x => (f x, x - f x)) (B R) ((T : Set G) ×ˢ B 1) :=
    fun x hx => ⟨hfT x hx, hf x hx⟩
  have hinj : Set.InjOn (fun x => (f x, x - f x)) (B R) := by
    intro x _ y _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    calc x = f x + (x - f x) := by abel
      _ = f y + (y - f y) := by rw [h2, h1]
      _ = y := by abel
  calc (B R).encard ≤ ((T : Set G) ×ˢ B 1).encard := Set.encard_le_encard_of_injOn hmaps hinj
    _ = T.card * (B 1).encard := by rw [Set.encard_prod, Set.encard_coe_eq_coe_finsetCard]

example : ∀ (G : Type) [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → ∀ R : ℝ, (B R).Finite → ∃ T : Finset G, (T : Set G) ⊆ B R ∧ (∀ x ∈ T, ∀ y ∈ T, x ≠ y → x - y ∉ B 1) ∧ (B R).encard ≤ T.card * (B 1).encard := exists_sep_cover

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitIdempotentConjugation
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.CentTorus GlobalTheory.CentAtP
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CentAtP

variable {p : ℕ} [Fact p.Prime]

theorem exists_conj_ne (G : HTGroup p) : ∃ x ∈ G.Kq, IsCMField.complexConj G.F x ≠ x := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace G.F) := inferInstance
  obtain ⟨x, hx, him⟩ := G.hKq.2 v.embedding
  refine ⟨x, hx, fun h => him ?_⟩
  have h2 := IsCMField.complexEmbedding_complexConj G.F v.embedding x
  rw [h] at h2
  have := congrArg Complex.im h2
  simp only [Complex.conj_im] at this
  linarith

end GlobalTheory.CentAtP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadOfPullbacksStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spread_of_pullbacks_alt : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (d : SiegPre g n ζ (spMap β)) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) [LocallyOfFinitePresentation sY] (u : SiegPre g n ζ sY) (r₀ : R) (ι₀ : Localization.Away r₀ →+* Localization.AtPrime 𝔭) (h : Sp (Localization.Away r₀) ⟶ Y) (e : SiegPre g n ζ (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β))), r₀ ∉ 𝔭 → ι₀.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.AtPrime 𝔭) → h ≫ sY = spMap ((algebraMap R (Localization.Away r₀)).comp β) → SiegPB e d (spMap (algebraMap R (Localization.AtPrime 𝔭))) → SiegPB e u (spMap ι₀ ≫ h) → ∃ r ∉ 𝔭, ∃ (κ : Localization.Away r₀ →+* Localization.Away r) (d' : SiegPre g n ζ (spMap ((algebraMap R (Localization.Away r)).comp β))), κ.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.Away r) ∧ SiegPB d' d (spMap (algebraMap R (Localization.Away r))) ∧ SiegPB d' u (spMap κ ≫ h) := by
  first | exact @GlobalTheory.SiegelSpreadLocal.exists_spread_of_pullbacks | exact GlobalTheory.SiegelSpreadLocal.exists_spread_of_pullbacks | (intros; apply GlobalTheory.SiegelSpreadLocal.exists_spread_of_pullbacks <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtFixedNearOneCommutativeCentralizerStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sqrt_fixed_near_one_commutative_centralizer : ∀ (p : ℕ) [Fact p.Prime] (v : AwayP p) (B : Type) [Ring B] [Algebra (Qv v) B] [Module.Finite (Qv v) B], letI : TopologicalSpace B := moduleTopology (Qv v) B; ∀ (e : B) (σ : B →ₗ[Qv v] B), (∀ a b : B, a * e = e * a → b * e = e * b → a * b = b * a) → (∀ a : B, a * e = e * a → σ a * e = e * σ a) → (∀ a b : B, a * e = e * a → b * e = e * b → σ (a * b) = σ a * σ b) → σ 1 = 1 → ∃ W ∈ nhds (1 : B), ∀ s ∈ W, s * e = e * s → σ s = s → ∃ r : B, r * e = e * r ∧ σ r = r ∧ r * r = s := by
  first | (exact @GlobalTheory.sqrt_fix_near_one_centralizer) | (exact GlobalTheory.sqrt_fix_near_one_centralizer) | (intros; apply GlobalTheory.sqrt_fix_near_one_centralizer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSumTwoSidedMulEqMatrixUnitUnitaryDatumStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sum_two_sided_mul_eq_matrixUnit_unitaryDatum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.Cˣ), (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∀ (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C), Function.Injective ι →
    (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) → ∀ (r : ℕ) (e : Fin r → G.C),
    (∀ x : G.C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) → ∀ i i' : Fin r,
    ∃ (N : ℕ) (l : Fin N → L) (c : Fin N → G.C), ∀ β : Fin r → L,
      ∑ k, ι (l k) * (∑ i'', ι (β i'') * e i'') * c k = ι (β i') * e i := by
  first | (exact @GlobalTheory.exists_sum_mul_mul_eq_matrixUnit_htGroup) | (exact GlobalTheory.exists_sum_mul_mul_eq_matrixUnit_htGroup) | (intros; apply GlobalTheory.exists_sum_mul_mul_eq_matrixUnit_htGroup  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueLeftBasisCoordsAdicCompletionStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_left_basis_coords_adicCompletion : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (r : ℕ)
    (e : Fin r → C), (∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i) →
    ∀ (v : HeightOneSpectrum ℤ) (y : v.adicCompletion ℚ ⊗[ℚ] C),
    ∃! β : Fin r → v.adicCompletion ℚ ⊗[ℚ] L,
      y = ∑ i, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι (β i) *
        ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] e i) := by
  first | (exact @GlobalTheory.LeftBasisBC.existsUnique_coords_adicCompletion) | (exact GlobalTheory.LeftBasisBC.existsUnique_coords_adicCompletion) | (intros; apply GlobalTheory.LeftBasisBC.existsUnique_coords_adicCompletion  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryAdelicPointOfEventuallyIntegralLocaStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryAdelicPoint_of_eventually_integral_local : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (h : ∀ v : AwayP p, Gv G v), (∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), h v ∈ IntV G v) → ∃ g : G.GAf, ∀ v, piV G v g = h v := by
  first | (exact @GlobalTheory.OrbFinAf.exists_glue) | (exact GlobalTheory.OrbFinAf.exists_glue) | (intros; apply GlobalTheory.OrbFinAf.exists_glue  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDoubledBlockDiagOneStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryDoubled_blockDiag_one : ∀ (R E : Type) [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) (β : Type) [Fintype β] [DecidableEq β] (J : Matrix β β E) (g : UG c J), ∃ gd : UG c (dbl J), ((gd : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1 := by
  first | exact @GlobalTheory.unitary_diag_one_mem_dbl | exact GlobalTheory.unitary_diag_one_mem_dbl | (intros; apply GlobalTheory.unitary_diag_one_mem_dbl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedDvrAdjoiningUnitRootsStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_dvr_adjoining_unit_roots : ∀ (F : Type) [Field F] [IsAlgClosed F] (T : Subring F) [IsDiscreteValuationRing T] (k : ℕ), IsUnit (k : T) → ∀ U : Set Tˣ, U.Finite → ∃ T' : Subring F, GlobalTheory.UnramSub T.subtype T' ∧ ∀ x : F, (∃ u ∈ U, x ^ k = ((u : T) : F)) → x ∈ T' := by
  first | exact @GlobalTheory.exists_unramSub_of_pow_eq_units | exact GlobalTheory.exists_unramSub_of_pow_eq_units | (intros; apply GlobalTheory.exists_unramSub_of_pow_eq_units <;> assumption)
end

