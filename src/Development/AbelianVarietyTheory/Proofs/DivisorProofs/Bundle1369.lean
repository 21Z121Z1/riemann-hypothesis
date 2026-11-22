import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0039
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0341
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1348
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1355
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.UnitaryClasses

def gramOn {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (V : Submodule K (Fin n → K)) :
    Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K :=
  Matrix.of fun i j => hform σ H (Module.finBasis K V i).1 (Module.finBasis K V j).1

def sgnOn {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K) {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (Q : K[X]) (A : Matrix (Fin n) (Fin n) K) : ℂ :=
  (-1) ^ ordL (gramOn σ H (LinearMap.ker (Matrix.toLin' (aeval A Q)))).det

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Gen
variable {K : Type} [Field K] (σ : K →+* K) {n : ℕ}

theorem cT_cT (hσ : ∀ x, σ (σ x) = x) (M : Matrix (Fin n) (Fin n) K) : cT σ (cT σ M) = M := by
  ext i j; simp [cT, hσ]

theorem cT_units (k : GL (Fin n) K) : cT σ (k⁻¹).val * cT σ k.val = 1 := by
  rw [← cT_mul, Units.mul_inv, cT_one]

theorem cT_units' (k : GL (Fin n) K) : cT σ k.val * cT σ (k⁻¹).val = 1 := by
  rw [← cT_mul, Units.inv_mul, cT_one]

theorem cT_units_left (k : GL (Fin n) K) (X : Matrix (Fin n) (Fin n) K) : cT σ (k⁻¹).val * (cT σ k.val * X) = X := by
  rw [← Matrix.mul_assoc, cT_units, Matrix.one_mul]

theorem cT_units_left' (k : GL (Fin n) K) (X : Matrix (Fin n) (Fin n) K) : cT σ k.val * (cT σ (k⁻¹).val * X) = X := by
  rw [← Matrix.mul_assoc, cT_units', Matrix.one_mul]

theorem herm_of (hσ : ∀ x, σ (σ x) = x) (k : GL (Fin n) K) : IsHerm σ (cT σ (k⁻¹).val * (k⁻¹).val) := by
  unfold IsHerm; rw [cT_mul, cT_cT σ hσ]

theorem det_ne (k : GL (Fin n) K) : (cT σ (k⁻¹).val * (k⁻¹).val).det ≠ 0 := by
  have h1 : ((k⁻¹).val).det ≠ 0 := ((k⁻¹).isUnit.map Matrix.detMonoidHom).ne_zero
  have h2 : (cT σ (k⁻¹).val).det = σ ((k⁻¹).val).det := by
    unfold cT; rw [Matrix.det_transpose, RingHom.map_det]; rfl
  rw [Matrix.det_mul, h2]
  exact mul_ne_zero ((map_ne_zero σ).2 h1) h1

theorem one_of (k : GL (Fin n) K) : cT σ k.val * (cT σ (k⁻¹).val * (k⁻¹).val) * k.val = 1 := by
  simp only [Matrix.mul_assoc, cT_units_left', Units.inv_mul]

theorem inv_of_unit (k a : GL (Fin n) K) (hy : cT σ (k⁻¹ * a * k).val * 1 * (k⁻¹ * a * k).val = 1) :
    cT σ a.val * (cT σ (k⁻¹).val * (k⁻¹).val) * a.val = cT σ (k⁻¹).val * (k⁻¹).val := by
  have ha : a = k * (k⁻¹ * a * k) * k⁻¹ := by group
  rw [ha]
  generalize k⁻¹ * a * k = y at hy ⊢
  simp only [Units.val_mul, cT_mul, Matrix.mul_assoc, Matrix.mul_one] at hy ⊢
  simp only [cT_units_left', Units.inv_mul_cancel_left]
  rw [← Matrix.mul_assoc (cT σ y.val), hy, Matrix.one_mul]

theorem unit_of_form (γ₀ h : GL (Fin n) K) (hinv : cT σ γ₀.val * (cT σ h.val * h.val) * γ₀.val = cT σ h.val * h.val) :
    cT σ (h * γ₀ * h⁻¹).val * 1 * (h * γ₀ * h⁻¹).val = 1 := by
  simp only [Units.val_mul, cT_mul, Matrix.mul_assoc, Matrix.mul_one]
  have key := congrArg (· * (h⁻¹).val) hinv
  simp only [Matrix.mul_assoc] at key
  rw [key, cT_units_left, Units.mul_inv]

theorem unit_of_two (k c h : GL (Fin n) K) (H' : Matrix (Fin n) (Fin n) K)
    (h1 : H' = cT σ c.val * (cT σ (k⁻¹).val * (k⁻¹).val) * c.val) (h2 : H' = cT σ h.val * h.val) :
    cT σ (k⁻¹ * c * h⁻¹).val * 1 * (k⁻¹ * c * h⁻¹).val = 1 := by
  simp only [Units.val_mul, cT_mul, Matrix.mul_assoc, Matrix.mul_one]
  have key := congrArg (· * (h⁻¹).val) (h1.symm.trans h2)
  simp only [Matrix.mul_assoc] at key
  rw [key, cT_units_left, Units.mul_inv]

end Gen

theorem cT_map (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) {n : ℕ} (M : Matrix (Fin n) (Fin n) E) :
    (cT (IsCMField.complexConj E).toRingEquiv.toRingHom M).map (algebraMap E (w.adicCompletion E)) =
      cT (cj w) (M.map (algebraMap E (w.adicCompletion E))) := by
  have h := ((GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hw).1
  ext i j; simp [cT, h]

theorem locPt_val (hU : Unr E) {n : ℕ} (w : Pl E) (γ : UE E n) :
    ((locPt w γ : UL n w) : GLw n w) = GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 := by
  have hm : GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1 ∈ UL n w := by
    unfold UL
    split_ifs with hs
    · trivial
    · have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E) * 1 * γ.1 = 1 := γ.2
      show cT (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1).val *
        (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1).val = 1
      have := congrArg (Matrix.map · (algebraMap E (w.adicCompletion E))) hγ
      simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), cT_map hU w hs] at this
      simpa using this
  unfold locPt toSub
  rw [dif_pos hm]

theorem aeval_map_mat {n : ℕ} (w : Pl E) (M : Matrix (Fin n) (Fin n) E) (p : E[X]) :
    aeval (M.map (algebraMap E (w.adicCompletion E))) (atPl w p) = (aeval M p).map (algebraMap E (w.adicCompletion E)) := by
  rw [atPl, aeval_map_algebraMap]
  have := aeval_algHom_apply (AlgHom.mapMatrix (Algebra.ofId E (w.adicCompletion E))) M p
  have e : (⇑(Algebra.ofId E (w.adicCompletion E)) : E → _) = algebraMap E _ := rfl
  simpa [AlgHom.mapMatrix_apply, e] using this

theorem kapSign_eq {n : ℕ} (w : Pl E) (hw : ¬ IsSplitAt w) (Q : (w.adicCompletion E)[X]) (γ : GLw n w) :
    kapSign n w Q γ = sgnOn (cj w) 1 Q γ.val := by
  unfold kapSign sgnOn gramOn hform
  rw [if_neg hw]
  simp [Matrix.one_apply]

theorem mem_S {S : Set (Pl E)} (hS : IsSection S) {w : Pl E} (hw : ¬ IsSplitAt w) : w ∈ S := by
  obtain ⟨u, ⟨hu, hu'⟩, -⟩ := hS w
  by_contra h
  exact hw ⟨u, fun e => h (e ▸ hu), hu'⟩

end GlobalTheory.UnitaryClasses
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAlgebraicIntegersBoundedArchimedeanLe
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

namespace GlobalTheory.IntCount

theorem exists_abs_repr_le_mul_house (E : Type) [Field E] [NumberField E] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : 𝓞 E) (j : Module.Free.ChooseBasisIndex ℤ (𝓞 E)),
      |(((RingOfIntegers.basis E).repr x j : ℤ) : ℝ)| ≤ C * house (x : E) := by
  let L := (canonicalEmbedding.latticeBasis E).equivFun.toLinearMap.toContinuousLinearMap
  refine ⟨‖L‖, norm_nonneg _, fun x j => ?_⟩
  have h1 := L.le_opNorm (canonicalEmbedding E x)
  have h2 := norm_le_pi_norm (L (canonicalEmbedding E x)) j
  have h3 : L (canonicalEmbedding E x) j = (((RingOfIntegers.basis E).repr x j : ℤ) : ℂ) := by
    have := canonicalEmbedding.integralBasis_repr_apply E (x : E) j
    rw [NumberField.integralBasis_repr_apply] at this
    simpa [L] using this
  rw [h3, Complex.norm_intCast] at h2
  exact h2.trans h1

theorem card_bounded_integers_le (E : Type) [Field E] [NumberField E] :
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      {ξ : 𝓞 E | ∀ w : InfinitePlace E, w (ξ : E) ≤ T}.Finite ∧
      ({ξ : 𝓞 E | ∀ w : InfinitePlace E, w (ξ : E) ≤ T}.ncard : ℝ) ≤ C * T ^ m := by
  classical
  obtain ⟨c, hc, hb⟩ := exists_abs_repr_le_mul_house E
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  refine ⟨Fintype.card ι, (2 * c + 3) ^ Fintype.card ι, by positivity, fun T hT => ?_⟩
  set S := {ξ : 𝓞 E | ∀ w : InfinitePlace E, w (ξ : E) ≤ T} with hS
  let M : ℕ := ⌈c * T⌉₊
  let s : Finset (ι → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(M : ℤ)) M
  let f : 𝓞 E → (ι → ℤ) := fun ξ j => (RingOfIntegers.basis E).repr ξ j
  have hf : Function.Injective f := fun ξ η h =>
    (RingOfIntegers.basis E).ext_elem fun j => congrFun h j
  have hmaps : ∀ ξ ∈ S, f ξ ∈ s := by
    intro ξ hξ
    refine Fintype.mem_piFinset.2 fun j => Finset.mem_Icc.2 (abs_le.1 ?_)
    have hh : house (ξ : E) ≤ T := by
      refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun φ => ?_
      have := hξ (InfinitePlace.mk φ)
      rwa [InfinitePlace.apply] at this
    have h1 := hb ξ j
    have h2 : c * house (ξ : E) ≤ (M : ℝ) :=
      (mul_le_mul_of_nonneg_left hh hc).trans (Nat.le_ceil _)
    exact_mod_cast h1.trans h2
  have hsub : S ⊆ f ⁻¹' (s : Set (ι → ℤ)) := fun ξ hξ => hmaps ξ hξ
  have hfin : S.Finite := ((s.finite_toSet).preimage hf.injOn).subset hsub
  refine ⟨hfin, ?_⟩
  have hcard : S.ncard ≤ s.card := by
    rw [← Set.ncard_coe_finset s]
    exact Set.ncard_le_ncard_of_injOn f (fun ξ hξ => hmaps ξ hξ) hf.injOn s.finite_toSet
  have hs : (s.card : ℝ) = (2 * (M : ℝ) + 1) ^ Fintype.card ι := by
    simp only [s, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Int.card_Icc]
    push_cast
    congr 1
    have : (↑M + 1 - -↑M : ℤ).toNat = 2 * M + 1 := by omega
    rw [this]; push_cast; ring
  have hM : (M : ℝ) ≤ c * T + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hbase : 2 * (M : ℝ) + 1 ≤ (2 * c + 3) * T := by nlinarith
  calc (S.ncard : ℝ) ≤ s.card := by exact_mod_cast hcard
    _ = (2 * (M : ℝ) + 1) ^ Fintype.card ι := hs
    _ ≤ ((2 * c + 3) * T) ^ Fintype.card ι := by gcongr
    _ = (2 * c + 3) ^ Fintype.card ι * T ^ Fintype.card ι := mul_pow _ _ _

end GlobalTheory.IntCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.RealLift.HermitianFrameExistence

open Matrix
open scoped ComplexOrder

theorem map_star_trip {m k l o : Type} [Fintype k] [Fintype l] (X : Matrix k m ℂ) (Y : Matrix k l ℂ)
    (Z : Matrix l o ℂ) : (Xᵀ * Y * Z.map star).map star = Xᴴ * Y.map star * Z := by
  have h : ∀ {a b : Type} (W : Matrix a b ℂ), W.map star = W.map (starRingEnd ℂ) := fun _ => rfl
  rw [h (Xᵀ * Y * Z.map star), Matrix.map_mul, Matrix.map_mul]
  simp [Matrix.conjTranspose, Matrix.map_map, Function.comp_def]

theorem quad {n ι : Type} [Fintype n] [Fintype ι] (G : Matrix n n ℂ) (B : Matrix n ι ℂ) (w : ι → ℂ) :
    star (B *ᵥ w) ⬝ᵥ G *ᵥ (B *ᵥ w) = star w ⬝ᵥ (Bᴴ * G * B) *ᵥ w := by
  conv_rhs => rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]

theorem val_inl {p q : ℕ} (u : Fin p → ℂ) :
    star (Sum.elim u (0 : Fin q → ℂ)) ⬝ᵥ (fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ
      Sum.elim u 0 = star u ⬝ᵥ u := by
  simp [fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]

theorem val_inr {p q : ℕ} (v : Fin q → ℂ) :
    star (Sum.elim (0 : Fin p → ℂ) v) ⬝ᵥ (fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ
      Sum.elim 0 v = -(star v ⬝ᵥ v) := by
  simp [fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, neg_mulVec, Finset.sum_neg_distrib]

theorem inertia {n p q r s : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ)
    (A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ) (hB : Bᴴ * G * B = fromBlocks 1 0 0 (-1))
    (hA : Aᴴ * G * A = fromBlocks 1 0 0 (-1)) : p + s ≤ n := by
  have key : ∀ (u : Fin p → ℂ) (v : Fin s → ℂ), B *ᵥ Sum.elim u 0 = A *ᵥ Sum.elim 0 v → u = 0 ∧ v = 0 := by
    intro u v h
    have h1 := quad G B (Sum.elim u 0)
    have h2 := quad G A (Sum.elim 0 v)
    rw [hB, val_inl] at h1
    rw [hA, val_inr, ← h, h1] at h2
    have hu := dotProduct_star_self_nonneg u
    have hv := dotProduct_star_self_nonneg v
    have h3 : star u ⬝ᵥ u = 0 := le_antisymm (by rw [h2]; exact neg_nonpos.2 hv) hu
    have h4 : star v ⬝ᵥ v = 0 := by rw [h3] at h2; exact neg_eq_zero.1 h2.symm
    exact ⟨dotProduct_star_self_eq_zero.1 h3, dotProduct_star_self_eq_zero.1 h4⟩
  let f : (Fin p → ℂ) × (Fin s → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    B.mulVecLin ∘ₗ ((LinearEquiv.sumArrowLequivProdArrow (Fin p) (Fin q) ℂ ℂ).symm.toLinearMap ∘ₗ
        (LinearMap.inl ℂ _ _ ∘ₗ LinearMap.fst ℂ _ _)) -
      A.mulVecLin ∘ₗ ((LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) ℂ ℂ).symm.toLinearMap ∘ₗ
        (LinearMap.inr ℂ _ _ ∘ₗ LinearMap.snd ℂ _ _))
  have e1 : ∀ u : Fin p → ℂ, (LinearEquiv.sumArrowLequivProdArrow (Fin p) (Fin q) ℂ ℂ).symm (u, 0) = Sum.elim u 0 := by
    intro u; ext (i | i) <;> simp
  have e2 : ∀ v : Fin s → ℂ, (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) ℂ ℂ).symm ((0 : Fin r → ℂ), v) = Sum.elim (0 : Fin r → ℂ) v := by
    intro v; ext (i | i) <;> simp
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, v⟩ huv
    have h0 : B *ᵥ Sum.elim u 0 - A *ᵥ Sum.elim 0 v = 0 := by
      simpa [f, e1, e2, Matrix.mulVecLin_apply] using huv
    obtain ⟨hu, hv⟩ := key u v (sub_eq_zero.1 h0)
    simp [hu, hv]
  have := LinearMap.finrank_le_finrank_of_injective hf
  simpa [Module.finrank_prod] using this

theorem card_le_of_mul_eq_one {m k : Type} [Fintype m] [Fintype k] [DecidableEq m] (X : Matrix m k ℂ)
    (Y : Matrix k m ℂ) (h : X * Y = 1) : Fintype.card m ≤ Fintype.card k := by
  have hi : Function.Injective Y.mulVecLin := by
    intro u v huv
    have := congrArg (fun w => X *ᵥ w) huv
    simpa [Matrix.mulVecLin_apply, mulVec_mulVec, h] using this
  simpa using LinearMap.finrank_le_finrank_of_injective hi

theorem star_form {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (v y : Fin n → ℂ) :
    star (v ⬝ᵥ M *ᵥ star y) = star v ⬝ᵥ M.map star *ᵥ y := by
  simp [dotProduct, mulVec, star_sum, Finset.mul_sum, mul_comm, mul_left_comm]

end GlobalTheory.RealLift.HermitianFrameExistence

namespace GlobalTheory.RealLift

open Matrix GlobalTheory.RealLift.HermitianFrameExistence
open scoped ComplexOrder

theorem frameEx_holds : FrameEx := by
  intro n r s M θ hSig hC
  obtain ⟨hrs, A0, hA0⟩ := hSig
  obtain ⟨hθθ, hiso, hpos⟩ := hC
  set G : Matrix (Fin n) (Fin n) ℂ := M.map star with hGdef
  have hJ : ∀ p q : ℕ, (fromBlocks 1 0 0 (-1) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).map star =
      fromBlocks 1 0 0 (-1) := by
    intro p q; ext (i | i) (j | j) <;> simp [one_apply] <;> split_ifs <;> simp
  have hA : A0ᴴ * G * A0 = fromBlocks 1 0 0 (-1) := by
    rw [← map_star_trip, hA0, hJ]

  obtain ⟨L, hLdef⟩ : ∃ L : Matrix (Fin r ⊕ Fin s) (Fin n) ℂ,
      L = (fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) * (A0ᴴ * G) := ⟨_, rfl⟩
  have hL : L * A0 = 1 := by
    calc L * A0 = (fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) * (A0ᴴ * G * A0) := by
          rw [hLdef]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA, fromBlocks_multiply]; simp
  have e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have hR : A0 * L = 1 := (mul_eq_one_comm_of_equiv e).1 hL
  have hLc : Lᴴ * A0ᴴ = 1 := by rw [← conjTranspose_mul, hR, conjTranspose_one]
  have hJh : ((fromBlocks 1 0 0 (-1)) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ)ᴴ = fromBlocks 1 0 0 (-1) := by
    simp [fromBlocks_conjTranspose]
  have hA' : A0ᴴ * Gᴴ * A0 = A0ᴴ * G * A0 := by
    calc A0ᴴ * Gᴴ * A0 = (A0ᴴ * G * A0)ᴴ := by simp [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hA, hJh]
  have Gherm : Gᴴ = G := by
    calc Gᴴ = (Lᴴ * A0ᴴ) * Gᴴ * (A0 * L) := by rw [hLc, hR]; simp
      _ = Lᴴ * (A0ᴴ * Gᴴ * A0) * L := by simp only [Matrix.mul_assoc]
      _ = Lᴴ * (A0ᴴ * G * A0) * L := by rw [hA']
      _ = (Lᴴ * A0ᴴ) * G * (A0 * L) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hLc, hR]; simp

  have hiso' : θᴴ * G * θ = G := by rw [← map_star_trip, hiso]
  have hcomm : θᴴ * G = G * θ := by
    calc θᴴ * G = θᴴ * G * θ * θ := by rw [Matrix.mul_assoc (θᴴ * G), hθθ, Matrix.mul_one]
      _ = G * θ := by rw [hiso']
  have hherm : (G * θ).IsHermitian := by
    unfold IsHermitian; rw [conjTranspose_mul, Gherm, hcomm]
  have hPD : (G * θ).PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hherm, fun x hx => ?_⟩
    have hval : star x ⬝ᵥ (G * θ) *ᵥ x = star ((θ *ᵥ x) ⬝ᵥ M *ᵥ star x) := by
      rw [← hcomm, star_form, ← hGdef, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
    refine Complex.pos_iff.2 ⟨?_, (hherm.im_star_dotProduct_mulVec_self x).symm⟩
    rw [hval, Complex.star_def, Complex.conj_re]; exact hpos x hx
  obtain ⟨p, q, B, B', h1, h2, h3, h4⟩ :=
    GlobalTheory.exists_basis_adapted_to_cartan_involution n G θ hθθ hiso' hPD
  have i1 := inertia G B A0 h3 hA
  have i2 := inertia G A0 B hA h3
  have i3 := card_le_of_mul_eq_one B B' h1
  simp only [Fintype.card_fin, Fintype.card_sum] at i3
  obtain rfl : p = r := by omega
  obtain rfl : q = s := by omega
  refine ⟨B, ⟨?_, B', h1⟩, h4⟩
  calc Bᵀ * M * B.map star = ((Bᵀ * M * B.map star).map star).map star := by simp [Matrix.map_map, Function.comp_def]
    _ = _ := by rw [map_star_trip, ← hGdef, h3, hJ]; rfl

end GlobalTheory.RealLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellHeightLocalReduction
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.WhitHered Matrix Topology Pointwise

namespace GlobalTheory.WhitHered.CellLoc

section Alg

variable {k : Type} [Field k] {N : ℕ}

def pm (σ : Equiv.Perm (Fin N)) : GL (Fin N) k :=
  ⟨Matrix.of fun a c => if a = σ c then 1 else 0, Matrix.of fun a c => if c = σ a then 1 else 0, by
    ext a c
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ.symm a)]
    · simp [Matrix.one_apply, eq_comm]
    · intro b _ hb
      have : a ≠ σ b := fun h => hb (by simp [h])
      simp [this]
    · simp, by
    ext a c
    simp [Matrix.mul_apply, Matrix.one_apply, eq_comm]⟩

end Alg

section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N c : ℕ} {m : Fin c → ℕ}

theorem isClosed_parab (e : (Σ a, Fin (m a)) ≃ Fin N) : IsClosed (parab k e : Set (GL (Fin N) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : (parab k e : Set (GL (Fin N) k)) = ⋂ i, ⋂ j, ⋂ _ : blk e j < blk e i, {g : GL (Fin N) k | g.val i j = 0} := by
    ext g
    simp only [SetLike.mem_coe, mem_parab, Set.mem_iInter, Set.mem_setOf_eq]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const

end Main

end GlobalTheory.WhitHered.CellLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerTorusEllipticElementRealPlaceStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_torusEllipticElement_realPlace : ∀ {D : D7} (V : HSp D) (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau)
    (dt : Measure (Tor P (placeOf D ρ).Completion)) [dt.IsHaarMeasure] {x φ}
    (h : IsIsom P (placeOf D ρ).Completion V.gram x φ),
    (centMeas h dt).IsHaarMeasure ∧ (centMeas h dt).IsMulRightInvariant ∧
      (centMeas h dt).real univ = dt.real univ ∧
      (IsCompact (cent (gam h) : Set (GArch D.sp.cm.sig V.gram (placeOf D ρ))) ↔
        CompactSpace (Tor P (placeOf D ρ).Completion)) := by
  first | exact @GlobalTheory.RealPlaceCentraliser.centMeas_real_place | exact GlobalTheory.RealPlaceCentraliser.centMeas_real_place | (intros; apply GlobalTheory.RealPlaceCentraliser.centMeas_real_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnity
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.NuGood

theorem not_root_of_unity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → (∀ (t : E →ₐ[F] Fv F v) (k : ℤ), k ≠ 0 → chrW X.ν t (unifAt v) ^ k ≠ 1) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h v hv t k hk hpow
  have hW : splitPrime t ∉ above E (X.T : Set (Pl F)) := by
    intro hmem
    exact hv.1 (by simpa [above, splitPrime_under] using hmem)
  have hunr : UnrAt X.ν (splitPrime t) := by
    rw [Chars.ν, div_eq_mul_inv]
    exact (h.chars.unrα _ hW).mul (h.chars.unrβ _ hW).inv
  rw [GlobalTheory.T.unramified_character_at_uniformizer F E X.ν v t hunr] at hpow
  have hHecke : IsHecke F E X.ν := by
    refine ⟨?_, fun x => ?_⟩
    · exact (h.chars.heckeα.1.div' h.chars.heckeβ.1 :)
    · rw [Chars.ν, MonoidHom.div_apply, h.chars.heckeα.2 x, h.chars.heckeβ.2 x, div_one]
  obtain ⟨H, hloc, hinf⟩ := GlobalTheory.T.hecke_character_of_idele_class F E σ h.base.cm X.ν hHecke
  have hexp : HasExp B.emb X.ν (fun w => B.mα w - B.mβ w) := by
    intro z hz
    have h1 := h.chars.expα z hz
    have h2 := h.chars.expβ z hz
    show (((X.α z / X.β z : Circle)) : ℂ) = _
    rw [Circle.coe_div, h1, h2, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hne : piInf (B.emb w) z ≠ 0 := (z.isUnit.map (piInf (B.emb w))).ne_zero
    have hne' : piInf (B.emb w) z / (‖piInf (B.emb w) z‖ : ℂ) ≠ 0 :=
      div_ne_zero hne (by exact_mod_cast (norm_ne_zero_iff.2 hne))
    rw [zpow_sub₀ hne']
  have hval : val X.ν (splitPrime t) = H.val (splitPrime t) := (hloc _ _).symm
  obtain ⟨p, hp, hN, hsq⟩ := GlobalTheory.T.split_prime_degree_one F E (splitPrime t) (by rw [splitPrime_under]; exact hv.2)
  refine GlobalTheory.T.hecke_value_not_finite_order F E σ h.base.cm h.base.galois B.emb H _ (hinf _ _ hexp) (fun w => ?_) p hp _ hN hsq ?_
  · have := h.geo.kappa w
    omega
  · rw [← hval]
    exact isOfFinOrder_iff_zpow_eq_one.2 ⟨k, hk, hpow⟩

end GlobalTheory.NuGood
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactRealPlaceTorusClassesSignVectors
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

noncomputable section
namespace GlobalTheory.RealSigns

theorem signs_real : ∀ {D : D7} (V : HSp D) {S : D.what₂.Tau → SPar} (M : DSModel V S) (ρ : D.what₂.Tau)
    (P : PPol D.sp.cm.sig V.rank), CompactSpace (Tor P (placeOf D ρ).Completion) →
    (XSet P (placeOf D ρ).Completion V.gram).Finite ∧
      ∃ (y : XSet P (placeOf D ρ).Completion V.gram → Equiv.Perm (Fin V.rank))
        (θ : XSet P (placeOf D ρ).Completion V.gram → Fin V.rank → ℝ),
        Function.Bijective (fun p : compactWeyl (M.ε ρ) × XSet P (placeOf D ρ).Completion V.gram =>
          (y p.2)⁻¹ * p.1.1) ∧
        (∀ q a, Complex.exp (θ q a * Complex.I) = cxRoots (embOverOf D ρ).1 P ((y q)⁻¹ a)) ∧
        ∀ q, ∃ g : GArch D.sp.cm.sig V.gram (placeOf D ρ), frameMat M ρ (g⁻¹ * gam q.2.choose_spec.choose_spec.2 * g) =
          Matrix.diagonal fun a => Complex.exp (θ q a * Complex.I) :=
  of_cosets GlobalTheory.T.real_place_compact_torus_classes_compactWeyl_cosets

end GlobalTheory.RealSigns
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockSymbolMatrixNeZeroStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_blockSymbolMatrix_ne_zero' : ∀ (E : Type) [Field E] (J : Type) [Fintype J] [DecidableEq J] (δ e : ℕ) (g : Fin δ → E) (R : Matrix (Fin δ) (Fin δ) E), (∀ p, g p ≠ 0) → R.det ≠ 0 → (Matrix.of fun i i' : J × Fin δ => if i.1 = i'.1 then g i.2 ^ e * R i.2 i'.2 else 0).det ≠ 0 := by
  first | exact @GlobalTheory.det_blockSymbolMatrix_ne_zero | exact GlobalTheory.det_blockSymbolMatrix_ne_zero | (intros; apply GlobalTheory.det_blockSymbolMatrix_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCrystallineBlockDataOfReductionPairStatement
section
open NumberField GlobalTheory.ExpFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralCrystallineBlockData_of_reductionPair : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n t : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), BlockPair E Ω l n t J bot → GlobalTheory.WachBlock.IntegralBlock E Ω l n t J bot := by
  first | exact @GlobalTheory.WachBlock.integralBlock_of_blockPair | exact GlobalTheory.WachBlock.integralBlock_of_blockPair | (intros; apply GlobalTheory.WachBlock.integralBlock_of_blockPair <;> assumption)
end

