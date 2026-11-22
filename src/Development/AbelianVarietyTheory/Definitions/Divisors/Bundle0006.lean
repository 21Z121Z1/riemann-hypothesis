import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0110
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.CurvSubQuotTautPairGram
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.HermFrame.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
  {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}

theorem blockSS_eq (K T : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    blockSS K T = T.toBlocks₁₁ + orthCoeff K * T.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks T]
  simp [blockSS, orthProj, incl, fromCols_mul_fromBlocks, fromCols_mul_fromRows]

theorem blockQQ_eq (K T : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    blockQQ K T = T.toBlocks₂₂ - T.toBlocks₂₁ * orthCoeff K := by
  conv_lhs => rw [← fromBlocks_toBlocks T]
  simp [blockQQ, quotMap, orthLift, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  abel

theorem conn_sub (hu : IsUnit (H z).det) (hs : IsUnit (subGram (H z)).det) (ξ : E) :
    conn (fun x => subGram (H x)) z ξ = blockSS (H z) (conn H z ξ) := by
  have h := transpose_mul_conn hu ξ
  rw [← fromBlocks_toBlocks (H z)ᵀ, ← fromBlocks_toBlocks (conn H z ξ), fromBlocks_multiply] at h
  have h1 := congrArg toBlocks₁₁ h
  rw [toBlocks_fromBlocks₁₁] at h1
  have hs' : IsUnit (H z).toBlocks₁₁ᵀ.det := by rwa [det_transpose]
  rw [blockSS_eq, conn,
    show (mdel (fun x => subGram (H x)) z ξ)ᵀ = (mdel H z ξ)ᵀ.toBlocks₁₁ from rfl, ← h1,
    show (H z)ᵀ.toBlocks₁₁ = (H z).toBlocks₁₁ᵀ from rfl,
    show (H z)ᵀ.toBlocks₁₂ = (H z).toBlocks₂₁ᵀ from rfl, subGram, Matrix.mul_add,
    nonsing_inv_mul_cancel_left _ _ hs', orthCoeff, Matrix.mul_assoc]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype l] [DecidableEq l] in

theorem mContDiffAt_orthCoeff {k : WithTop ℕ∞} (h : MContDiffAt k H z)
    (hs : IsUnit (subGram (H z)).det) : MContDiffAt k (fun x => orthCoeff (H x)) z :=
  (h.subGram.transpose.inv (by rwa [det_transpose])).mul (h.submatrix Sum.inr Sum.inl).transpose

theorem mdbar_orthCoeff (h : MContDiffAt 1 H z) (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian)
    (hu : IsUnit (H z).det) (hs : IsUnit (subGram (H z)).det) (η : E) :
    mdbar (fun x => orthCoeff (H x)) z η = secondFormAdj H z η := by
  have := extForm_eq_neg_secondFormAdj h hh hu hs η
  rwa [extForm_eq_neg_mdbar, neg_inj] at this

theorem curv_sub (h : MContDiffAt 2 H z) (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian)
    (hu : IsUnit (H z).det) (hs : IsUnit (subGram (H z)).det) (ξ η : E) :
    curv (fun x => subGram (H x)) z ξ η =
      blockSS (H z) (curv H z ξ η) - secondFormAdj H z η * secondForm H z ξ := by
  have h1 : MContDiffAt 1 H z := h.of_le one_le_two
  have hc : MContDiffAt 1 (fun x => conn H x ξ) z := h.conn hu (by norm_num) ξ
  have he : (fun x => conn (fun x => subGram (H x)) x ξ) =ᶠ[𝓝 z]
      fun x => (conn H x ξ).toBlocks₁₁ + orthCoeff (H x) * (conn H x ξ).toBlocks₂₁ := by
    filter_upwards [h.eventually_isUnit hu, h.subGram.eventually_isUnit hs] with x a b
    rw [conn_sub (H := H) a b, blockSS_eq]
  have c11 : MContDiffAt 1 (fun x => (conn H x ξ).toBlocks₁₁) z := hc.submatrix Sum.inl Sum.inl
  have c21 : MContDiffAt 1 (fun x => (conn H x ξ).toBlocks₂₁) z := hc.submatrix Sum.inr Sum.inl
  have ho := mContDiffAt_orthCoeff h1 hs
  rw [curv, mdbar_congr he, mdbar_add c11 (ho.mul c21), mdbar_mul ho c21,
    mdbar_orthCoeff h1 hh hu hs, blockSS_eq, secondForm_eq,
    show (curv H z ξ η).toBlocks₁₁ = -mdbar (fun x => (conn H x ξ).toBlocks₁₁) z η from rfl,
    show (curv H z ξ η).toBlocks₂₁ = -mdbar (fun x => (conn H x ξ).toBlocks₂₁) z η from rfl,
    Matrix.mul_neg]
  abel

theorem conn_quot (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det)
    (hs : IsUnit (subGram (H z)).det) (ξ : E) :
    conn (fun x => quotGram (H x)) z ξ = blockQQ (H z) (conn H z ξ) := by
  refine (eq_conn_of_compatible (H := fun x => quotGram (H x))
    (isUnit_det_quotGram hu hs) ?_).symm
  have hA : MContDiffAt 1 (fun x => (H x).toBlocks₁₁) z := h.subGram
  have hB : MContDiffAt 1 (fun x => (H x).toBlocks₁₂) z := h.submatrix Sum.inl Sum.inr
  have hC : MContDiffAt 1 (fun x => (H x).toBlocks₂₁) z := h.submatrix Sum.inr Sum.inl
  have hD : MContDiffAt 1 (fun x => (H x).toBlocks₂₂) z := h.submatrix Sum.inr Sum.inr
  have hs' : IsUnit (H z).toBlocks₁₁.det := hs
  have e := conn_transpose_mul hu ξ
  rw [← fromBlocks_toBlocks (conn H z ξ)ᵀ, ← fromBlocks_toBlocks (H z), fromBlocks_multiply] at e
  have e11 := congrArg toBlocks₁₁ e
  have e12 := congrArg toBlocks₁₂ e
  have e21 := congrArg toBlocks₂₁ e
  have e22 := congrArg toBlocks₂₂ e
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂] at e11 e12 e21 e22
  simp only [quotGram, sub_eq_add_neg]
  rw [mdel_add hD ((hC.mul (hA.inv hs')).mul hB).neg, mdel_neg, mdel_mul (hC.mul (hA.inv hs')) hB,
    mdel_mul hC (hA.inv hs'), mdel_inv hA hs',
    show mdel (fun x => (H x).toBlocks₁₁) z ξ = (mdel H z ξ).toBlocks₁₁ from rfl,
    show mdel (fun x => (H x).toBlocks₁₂) z ξ = (mdel H z ξ).toBlocks₁₂ from rfl,
    show mdel (fun x => (H x).toBlocks₂₁) z ξ = (mdel H z ξ).toBlocks₂₁ from rfl,
    show mdel (fun x => (H x).toBlocks₂₂) z ξ = (mdel H z ξ).toBlocks₂₂ from rfl,
    ← e11, ← e12, ← e21, ← e22, blockQQ_eq, transpose_sub, transpose_mul, orthCoeff, transpose_mul,
    transpose_transpose, transpose_nonsing_inv, transpose_transpose,
    show (conn H z ξ).toBlocks₂₂ᵀ = (conn H z ξ)ᵀ.toBlocks₂₂ from rfl,
    show (conn H z ξ).toBlocks₂₁ᵀ = (conn H z ξ)ᵀ.toBlocks₁₂ from rfl]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hs']
  abel

theorem curv_quot (h : MContDiffAt 2 H z) (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian)
    (hu : IsUnit (H z).det) (hs : IsUnit (subGram (H z)).det) (ξ η : E) :
    curv (fun x => quotGram (H x)) z ξ η =
      blockQQ (H z) (curv H z ξ η) + secondForm H z ξ * secondFormAdj H z η := by
  have h1 : MContDiffAt 1 H z := h.of_le one_le_two
  have hc : MContDiffAt 1 (fun x => conn H x ξ) z := h.conn hu (by norm_num) ξ
  have he : (fun x => conn (fun x => quotGram (H x)) x ξ) =ᶠ[𝓝 z]
      fun x => (conn H x ξ).toBlocks₂₂ + -((conn H x ξ).toBlocks₂₁ * orthCoeff (H x)) := by
    filter_upwards [h.eventually_two, h.eventually_isUnit hu, h.subGram.eventually_isUnit hs]
      with x c a b
    rw [conn_quot (c.of_le one_le_two) a b, blockQQ_eq, sub_eq_add_neg]
  have c22 : MContDiffAt 1 (fun x => (conn H x ξ).toBlocks₂₂) z := hc.submatrix Sum.inr Sum.inr
  have c21 : MContDiffAt 1 (fun x => (conn H x ξ).toBlocks₂₁) z := hc.submatrix Sum.inr Sum.inl
  have ho := mContDiffAt_orthCoeff h1 hs
  rw [curv, mdbar_congr he, mdbar_add c22 (c21.mul ho).neg, mdbar_neg, mdbar_mul c21 ho,
    mdbar_orthCoeff h1 hh hu hs, blockQQ_eq, secondForm_eq,
    show (curv H z ξ η).toBlocks₂₂ = -mdbar (fun x => (conn H x ξ).toBlocks₂₂) z η from rfl,
    show (curv H z ξ η).toBlocks₂₁ = -mdbar (fun x => (conn H x ξ).toBlocks₂₁) z η from rfl,
    Matrix.neg_mul]
  abel

def pairFrame (z : ℂ) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ :=
  fromBlocks 1 0 (of fun _ _ => z) 1

theorem tautPairGram_eq (z : ℂ) :
    tautPairGram z = (pairFrame z)ᵀ * (fun _ : ℂ => 1) z * (pairFrame z)ᴴᵀ := by
  ext (a | a) (b | b) <;> simp [tautPairGram, pairFrame, mul_apply]

theorem mContDiffAt_pairFrame (k : WithTop ℕ∞) (z : ℂ) : MContDiffAt k pairFrame z := by
  rintro (a | a) (b | b) <;> simp only [pairFrame, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply] <;> fun_prop

theorem det_pairFrame (z : ℂ) : (pairFrame z).det = 1 := by
  simp [pairFrame, det_fromBlocks_zero₁₂]

theorem isPosFrame_tautPairGram : IsPosFrame Set.univ tautPairGram := by
  refine ⟨isOpen_univ, fun a b z _ => ?_, fun z _ => ?_⟩
  · simp only [funext tautPairGram_eq]
    exact ((((mContDiffAt_pairFrame ∞ z).transpose.mul (mContDiffAt_const 1)).mul
      (mContDiffAt_pairFrame ∞ z).conjTranspose.transpose) a b).contDiffWithinAt
  · rw [tautPairGram_eq, ← PosDef.transpose_iff]
    simp only [transpose_mul, transpose_transpose, Matrix.mul_one]
    exact PosDef.conjTranspose_mul_self _ (mulVec_injective_iff_isUnit.2
      ((isUnit_iff_isUnit_det _).2 (by simp [det_pairFrame])))

theorem curv_tautPairGram (z ξ η : ℂ) : curv tautPairGram z ξ η = 0 := by
  rw [funext tautPairGram_eq, curv_changeFrame (mContDiffAt_const 1) (by simp)
    (mContDiffAt_pairFrame 2 z) (by simp [det_pairFrame])
    (Eventually.of_forall fun x η => ?_)]
  · simp
  · ext (a | a) (b | b) <;> simp only [mdbar_apply, pairFrame, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply] <;>
      rw [dbar_eq_zero (by fun_prop)] <;> rfl

theorem secondForm_tautPairGram (ξ : ℂ) : secondForm tautPairGram 0 ξ = of fun _ _ => ξ := by
  have h : tautPairGram 0 = 1 := by
    rw [← fromBlocks_one]; ext (a | a) (b | b) <;> simp [tautPairGram]
  ext a b
  rw [secondForm_eq, conn, h, transpose_one, inv_one, Matrix.one_mul]
  change del (fun x : ℂ => x) 0 ξ = ξ
  rw [del_eq_fderiv differentiableAt_fun_id]; simp

theorem secondFormAdj_tautPairGram (η : ℂ) :
    secondFormAdj tautPairGram 0 η = of fun _ _ => conj η := by
  have h : tautPairGram 0 = 1 := by
    rw [← fromBlocks_one]; ext (a | a) (b | b) <;> simp [tautPairGram]
  have h1 : subGram (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ) = 1 := by
    rw [← fromBlocks_one]; rfl
  have h2 : quotGram (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ) = 1 := by
    have : toBlocks₂₁ (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ) = 0 := by
      rw [← fromBlocks_one]; rfl
    rw [quotGram, this, Matrix.zero_mul, Matrix.zero_mul, sub_zero, ← fromBlocks_one]; rfl
  rw [secondFormAdj, h, h1, h2, secondForm_tautPairGram]
  ext a b; simp [adj]

theorem curv_sub_quot_tautPairGram (ξ η : ℂ) :
    curv (fun x => subGram (tautPairGram x)) 0 ξ η () () = -(ξ * conj η) ∧
    curv (fun x => quotGram (tautPairGram x)) 0 ξ η () () = ξ * conj η ∧
    extTrace tautPairGram 0 ξ η = kappa * (ξ * conj η) := by
  have h := isPosFrame_tautPairGram.isHermFrame
  have hs := isPosFrame_tautPairGram.sub.isHermFrame.isUnit 0 trivial
  have a := h.two (z := 0) trivial
  have b := h.eventually_herm (z := 0) trivial
  have c := h.isUnit 0 trivial
  rw [curv_sub a b c hs, curv_quot a b c hs, extTrace,
    extFormAdj_eq_neg_secondForm (h.one trivial) b c hs,
    extForm_eq_neg_secondFormAdj (h.one trivial) b c hs, curv_tautPairGram,
    secondForm_tautPairGram, secondFormAdj_tautPairGram]
  simp [blockSS, blockQQ, mul_apply, trace, mul_comm]

example : wedge (fun ξ η : Fin 2 → ℂ => ξ 0 * conj (η 0)) (fun ξ η => ξ 1 * conj (η 1))
      ![1, 0] ![1, 0] ![0, 1] ![0, 1] = 1 ∧
    wedge (fun ξ η : Fin 2 → ℂ => ξ 0 * conj (η 0)) (fun ξ η => ξ 1 * conj (η 1))
      ![1, 0] ![0, 1] ![0, 1] ![1, 0] = -1 := by
  simp [wedge]

example (C : ℝ) : ¬ OneFormBound {0} (fun _ : Fin 1 → ℂ => (0 : Matrix (Fin 1) (Fin 1) ℂ))
    (fun _ => 1) (fun _ _ => 1) C := fun h => by
  simpa using (h 0 rfl).1.diag_pos (i := 0)

end GlobalTheory.HermFrame.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.FibreRankCompOfSurjective
section
noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv Module

namespace GlobalTheory.PDiv

theorem finrank_eq_ker_mul_range (k A B : Type) [Field k] [CommRing A] [CommRing B]
    [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A) :
    finrank k A = finrank k (A ⧸ kerIdeal f) *
      finrank k (LinearMap.range (f : B →ₐ[k] A).toLinearMap) := by
  obtain ⟨e⟩ := GlobalTheory.HopfShear.shear k A B f
  exact GlobalTheory.finrank_eq_mul_of_basis_tensor_self k (AlgHom.range (f : B →ₐ[k] A)) A _ Subtype.val_injective
    ⟨((Module.finBasis k _).baseChange A).map e.symm⟩

variable {O : Type} [CommRing O]

abbrev fibreDim (M : Type) [AddCommGroup M] [Module O M] (q : PrimeSpectrum O) : ℕ :=
  finrank q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[O] M)

abbrev fibreRank {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (f : M →ₗ[O] N) (q : PrimeSpectrum O) : ℕ :=
  finrank q.asIdeal.ResidueField (LinearMap.range (f.baseChange q.asIdeal.ResidueField))

section Linear

variable {M N P : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
  [AddCommGroup P] [Module O P]

theorem fibreDim_congr (e : M ≃ₗ[O] N) (q : PrimeSpectrum O) : fibreDim M q = fibreDim N q :=
  (e.baseChange O _ M N).finrank_eq

theorem fibreRank_comp_of_surjective (g : N →ₗ[O] P) {f : M →ₗ[O] N}
    (hf : Function.Surjective f) (q : PrimeSpectrum O) :
    fibreRank (g ∘ₗ f) q = fibreRank g q := by
  rw [fibreRank, LinearMap.baseChange_comp, LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.2 (LinearMap.lTensor_surjective _ hf)

theorem fibreRank_equiv_comp (e : N ≃ₗ[O] P) (f : M →ₗ[O] N) (q : PrimeSpectrum O) :
    fibreRank (e.toLinearMap ∘ₗ f) q = fibreRank f q := by
  rw [fibreRank, LinearMap.baseChange_comp, LinearMap.range_comp]
  exact LinearEquiv.finrank_map_eq (e.baseChange O _ N P) _

variable [Module.Finite O M] [Module.Projective O M] [Module.Finite O N] [Module.Projective O N]

theorem fibreDim_dual (q : PrimeSpectrum O) : fibreDim (CartierDual O M) q = fibreDim M q :=
  (fibreDim_congr (CartierDual.toDual O M) q).trans (GlobalTheory.DualFibreRank.finrank_dual_and_range_dualMap_baseChange O M M _ LinearMap.id).1

theorem rankAtStalk_dual (q : PrimeSpectrum O) :
    rankAtStalk (CartierDual O M) q = rankAtStalk M q := by
  rw [rankAtStalk_eq, rankAtStalk_eq]
  exact fibreDim_dual q

theorem fibreRank_transpose (f : M →ₗ[O] N) (q : PrimeSpectrum O) :
    fibreRank (CartierDual.transpose f) q = fibreRank f q := by
  have h : CartierDual.transpose f = (CartierDual.toDual O M).symm.toLinearMap ∘ₗ
      (f.dualMap ∘ₗ (CartierDual.toDual O N).toLinearMap) := rfl
  rw [h, fibreRank_equiv_comp, fibreRank_comp_of_surjective _ (CartierDual.toDual O N).surjective]
  exact (GlobalTheory.DualFibreRank.finrank_dual_and_range_dualMap_baseChange O M N _ f).2

end Linear

variable {A B : Type} [CommRing A] [CommRing B] [HopfAlgebra O A] [HopfAlgebra O B]
  [Module.Finite O A]

theorem fibreDim_eq_ker_mul_range (f : B →ₐc[O] A) (q : PrimeSpectrum O) :
    fibreDim A q = fibreDim (A ⧸ kerIdeal f) q * fibreRank (f : B →ₐ[O] A).toLinearMap q :=
  GlobalTheory.hopf_order_formula_fibre finrank_eq_ker_mul_range O A B _ f

theorem fibreDim_ne_zero (q : PrimeSpectrum O) : fibreDim A q ≠ 0 := by
  have : Nontrivial (q.asIdeal.ResidueField ⊗[O] A) :=
    (counitAlgHom q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[O] A)).domain_nontrivial
  exact finrank_pos.ne'

variable [Module.Projective O A] [Module.Finite O B] [Module.Projective O B]

theorem dual_map_surjective (f : B →ₐc[O] A)
    (h : ∀ q : PrimeSpectrum O, fibreDim A q = fibreDim (A ⧸ kerIdeal f) q * fibreDim B q) :
    Function.Surjective (CartierDual.map f) := by
  refine (GlobalTheory.surjective_injective_of_fibre_rank O _ _ (CartierDual.transpose (f : B →ₐ[O] A).toLinearMap)).1 fun q => ?_
  refine (fibreRank_transpose _ q).trans (Eq.trans ?_ (fibreDim_dual q).symm)
  have h1 := fibreDim_eq_ker_mul_range f q
  have h2 : fibreDim (A ⧸ kerIdeal f) q ≠ 0 := fun h0 =>
    fibreDim_ne_zero (A := A) q (by rw [h1, h0, zero_mul])
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h2) (h1.symm.trans (h q))

theorem fibreDim_ker_dual [IsCocomm O A] (g : A →ₐc[O] A) (q : PrimeSpectrum O) :
    fibreDim (CartierDual O A ⧸ kerIdeal (CartierDual.map g)) q =
      fibreDim (A ⧸ kerIdeal g) q := by
  have h1 := fibreDim_eq_ker_mul_range g q
  have h2 := fibreDim_eq_ker_mul_range (CartierDual.map g) q
  have h3 : fibreRank (CartierDual.map g : CartierDual O A →ₐ[O] CartierDual O A).toLinearMap q =
    fibreRank (g : A →ₐ[O] A).toLinearMap q := fibreRank_transpose (g : A →ₐ[O] A).toLinearMap q
  rw [h3, fibreDim_dual, h1] at h2
  have h4 : fibreRank (g : A →ₐ[O] A).toLinearMap q ≠ 0 := fun h0 =>
    fibreDim_ne_zero (A := A) q (by rw [h1, h0, mul_zero])
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h4) h2).symm

theorem ker_eq_of_fibreDim_eq {D E : Type} [CommRing D] [CommRing E] [Algebra O D] [Algebra O E]
    [Module.Finite O D] [Module.Finite O E] [Module.Projective O E] (π : D →ₐ[O] E)
    (hπ : Function.Surjective π) (I : Ideal D) (hI : I ≤ RingHom.ker π)
    (h : ∀ q : PrimeSpectrum O, fibreDim (D ⧸ I) q = fibreDim E q) : RingHom.ker π = I := by
  refine le_antisymm (fun d hd => ?_) hI
  let π' : (D ⧸ I) →ₐ[O] E := Ideal.Quotient.liftₐ I π hI
  have hs : Function.Surjective π' := fun e => by
    obtain ⟨d, rfl⟩ := hπ e
    exact ⟨Ideal.Quotient.mk I d, rfl⟩
  have hi := (GlobalTheory.surjective_injective_of_fibre_rank O _ _ π'.toLinearMap).2 inferInstance inferInstance hs h
  exact Ideal.Quotient.eq_zero_iff_mem.1 (hi (a₁ := Ideal.Quotient.mk I d) (a₂ := 0)
    (by rw [map_zero]; exact hd))

end GlobalTheory.PDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
section
noncomputable section

open WittVector Ideal Matrix GlobalTheory.Sandwich TensorProduct

namespace GlobalTheory.DetInv

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

def IsDetElt (ε : PreTilt O p) (ψ : RL p O Λ →+* RL p O Λ) (N : ℕ) (Δ : RL p O Λ) : Prop :=
  Δ ∣ (inA (mu ε) : RL p O Λ) ^ N ∧ ∃ g, Δ = g * ψ Δ ∧ g ∣ (inA (xi ε) : RL p O Λ) ^ N

def HasOrders (C : Type) [Field C] [Algebra O C] (ε : PreTilt O p) (N : ℕ) (Δ : RL p O Λ)
    (a : (Λ →+* O) → ℕ) (c : (Λ →+* O) → C) : Prop :=
  ∀ σ f, IsTheta σ f →
    a σ ≤ N ∧ c σ ≠ 0 ∧ Lead ((algebraMap O C).comp f) (inA (xi ε)) Δ (a σ) (c σ)

def IsIsom (C : Type) [Field C] [Algebra O C] (v : Valuation C NNReal) (γ : O ≃+* O) : Prop :=
  ∃ γC : C ≃+* C, (∀ x, γC (algebraMap O C x) = algebraMap O C (γ x)) ∧ ∀ z, v (γC z) = v z

end GlobalTheory.DetInv
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogPair

variable {R : Type} [CommRing R] {X : Scheme.{0}}

def cstOn (p : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U le_top).hom

def IsEtCoord (p : X ⟶ Sp R) (U : X.Opens) {d : ℕ} (t : Fin d → Γ(X, U)) : Prop :=
  (MvPolynomial.eval₂Hom (cstOn p U) t).Etale

structure SncChart (p : X ⟶ Sp R) (d : ℕ) {s : ℕ} (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) where

  U : X.Opens
  affine : IsAffineOpen U

  t : Fin d → Γ(X, U)
  etale : IsEtCoord p U t

  c : ∀ i, (L i).ι
  le : ∀ i, U ≤ (L i).U (c i)

  e : Fin s → Option (Fin d)
  inj : ∀ i j a, e i = some a → e j = some a → i = j

  u : Fin s → Γ(X, U)ˣ
  eq : ∀ i, resG X (le i) ((σ i).f (c i)) = (u i : Γ(X, U)) * (e i).elim 1 t

structure RelSnc (p : X ⟶ Sp R) (d : ℕ) {s : ℕ} (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) : Prop where
  isLB : ∀ i, (L i).IsLB
  chart : ∀ x : X, ∃ C : SncChart p d L σ, x ∈ C.U

end GlobalTheory.LogPair
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ProdFam
section
set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.PD

section Pull

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {E : Type} [AddCommGroup E] [Module k E]

open Classical in

def idxSign (τ : κ → ι) (S : Finset κ) : ℤ := (-1) ^ ((S ×ˢ S).filter fun x => x.1 < x.2 ∧ τ x.2 < τ x.1).card

open Classical in

def pullIdx (τ : κ → ι) (a : Finset ι → E) : Finset κ → E := fun S =>
  if Set.InjOn τ (S : Set κ) then idxSign τ S • a (S.image τ) else 0

end Pull

section Cross

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
  {E E' : Type} [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E']

def fstL : ι ×ₗ κ → ι := fun x => (ofLex x).1

def sndL : ι ×ₗ κ → κ := fun x => (ofLex x).2

def crossC {E'' : Type} [AddCommGroup E''] [Module k E''] (μ : E →ₗ[k] E' →ₗ[k] E'') (a : Finset ι → E) (b : Finset κ → E') :
    Finset (ι ×ₗ κ) → E'' := fun u =>
  ∑ j ∈ u, μ (pullIdx fstL a (u.filter (· ≤ j))) (pullIdx sndL b (u.filter (j ≤ ·)))

def prodFam {E'' : Type} [AddCommGroup E''] [Module k E''] (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E)
    (B : Finset κ → Submodule k E') (S : Finset (ι ×ₗ κ)) : Submodule k E'' :=
  Submodule.map₂ μ (A (S.image fstL)) (B (S.image sndL))

def Disjoint₂ {E'' : Type} [AddCommGroup E''] [Module k E''] (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E)
    (B : Finset κ → Submodule k E') : Prop :=
  ∀ I J, Function.Injective (TensorProduct.lift (μ.compl₁₂ (A I).subtype (B J).subtype))

end Cross

end GlobalTheory.PD
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogPair

def SameDiv {X : Scheme.{0}} {L M : LB X} (σ : L.Sec) (τ : M.Sec) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (i : L.ι) (j : M.ι) (hi : U ≤ L.U i) (hj : U ≤ M.U j) (u : Γ(X, U)ˣ),
    x ∈ U ∧ resG X hi (σ.f i) = (u : Γ(X, U)) * resG X hj (τ.f j)

theorem SameDiv.refl {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (σ : L.Sec) : SameDiv σ σ := fun x => by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ x))
  exact ⟨L.U i, i, i, le_rfl, le_rfl, 1, hi, by simp⟩

theorem SameDiv.symm {X : Scheme.{0}} {L M : LB X} {σ : L.Sec} {τ : M.Sec} (h : SameDiv σ τ) : SameDiv τ σ :=
  fun x => by
    obtain ⟨U, i, j, hi, hj, u, hx, e⟩ := h x
    exact ⟨U, j, i, hj, hi, u⁻¹, hx, by rw [e, Units.inv_mul_cancel_left]⟩

end GlobalTheory.LogPair
end
end

