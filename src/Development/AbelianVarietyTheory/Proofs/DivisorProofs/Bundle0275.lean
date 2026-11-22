import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0233
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpNormLeOpNormBlockDiagonal
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.HermFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

section Two

variable {m l m' l' : Type*}

variable [Fintype m] [Fintype l] [Fintype m'] [Fintype l']

theorem form_fromBlocks_diag (A₁ : Matrix m m ℂ) (A₂ : Matrix l l ℂ) (u u' : m → ℂ)
    (w w' : l → ℂ) : form (fromBlocks A₁ 0 0 A₂) (Sum.elim u w) (Sum.elim u' w') =
      form A₁ u u' + form A₂ w w' := by
  simp [form_eq_sum, Fintype.sum_sum_type]

theorem posSemidef_fromBlocks_diag {A₁ : Matrix m m ℂ} {A₂ : Matrix l l ℂ} (h₁ : A₁.PosSemidef)
    (h₂ : A₂.PosSemidef) : (fromBlocks A₁ 0 0 A₂).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    (IsHermitian.fromBlocks h₁.isHermitian (by simp) h₂.isHermitian) fun x => ?_
  have h : star x ⬝ᵥ (fromBlocks A₁ 0 0 A₂ *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (A₁ *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (A₂ *ᵥ (x ∘ Sum.inr)) := by
    simp [dotProduct, mulVec, Fintype.sum_sum_type]
  rw [h]
  exact add_nonneg (h₁.dotProduct_mulVec_nonneg _) (h₂.dotProduct_mulVec_nonneg _)

theorem posDef_fromBlocks_diag {A₁ : Matrix m m ℂ} {A₂ : Matrix l l ℂ} (h₁ : A₁.PosDef)
    (h₂ : A₂.PosDef) : (fromBlocks A₁ 0 0 A₂).PosDef := by
  refine posDef_iff.2 ⟨IsHermitian.fromBlocks h₁.isHermitian (by simp) h₂.isHermitian,
    fun v hv => ?_⟩
  rw [← Sum.elim_comp_inl_inr v] at hv ⊢
  rw [form_fromBlocks_diag, form_self h₁.posSemidef, form_self h₂.posSemidef, ← ofReal_add,
    zero_lt_real]
  by_cases h : v ∘ Sum.inl = 0
  · have h' : v ∘ Sum.inr ≠ 0 := fun h' => hv (by rw [h, h']; simp)
    have := gnorm_pos h₂ h'
    positivity
  · have := gnorm_pos h₁ h
    positivity

variable [DecidableEq m] [DecidableEq l] {H₁ : E → Matrix m m ℂ} {H₂ : E → Matrix l l ℂ} {z : E}

end Two

section Family

variable {o : Type*} [DecidableEq o] {m m' : o → Type*}

theorem mdel_blockDiagonal' (A : ∀ i, E → Matrix (m i) (m' i) ℂ) (z ξ : E) :
    mdel (fun x => blockDiagonal' fun i => A i x) z ξ = blockDiagonal' fun i => mdel (A i) z ξ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases h : i = j
  · subst h; simp
  · simp [blockDiagonal'_apply_ne _ _ _ h]

theorem mdbar_blockDiagonal' (A : ∀ i, E → Matrix (m i) (m' i) ℂ) (z ξ : E) :
    mdbar (fun x => blockDiagonal' fun i => A i x) z ξ =
      blockDiagonal' fun i => mdbar (A i) z ξ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases h : i = j
  · subst h; simp
  · simp [blockDiagonal'_apply_ne _ _ _ h]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem mContDiffAt_blockDiagonal' {k : WithTop ℕ∞} {A : ∀ i, E → Matrix (m i) (m' i) ℂ} {z : E}
    (hA : ∀ i, MContDiffAt k (A i) z) :
    MContDiffAt k (fun x => blockDiagonal' fun i => A i x) z := by
  rintro ⟨i, a⟩ ⟨j, b⟩
  by_cases h : i = j
  · subst h; simpa using hA i a b
  · simpa [blockDiagonal'_apply_ne _ _ _ h] using contDiffAt_const

variable [Fintype o] [∀ i, Fintype (m i)] [∀ i, Fintype (m' i)]

omit [∀ i, Fintype (m' i)] in

theorem blockDiagonal'_mulVec_apply (T : ∀ i, Matrix (m' i) (m i) ℂ) (v : (Σ i, m i) → ℂ) (i : o)
    (a : m' i) : (blockDiagonal' T *ᵥ v) ⟨i, a⟩ = (T i *ᵥ fun b => v ⟨i, b⟩) a := by
  simp only [mulVec, dotProduct, Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [blockDiagonal'_apply_ne _ _ _ hj.symm]
  · simp

theorem form_blockDiagonal' (A : ∀ i, Matrix (m i) (m i) ℂ) (v w : (Σ i, m i) → ℂ) :
    form (blockDiagonal' A) v w = ∑ i, form (A i) (fun a => v ⟨i, a⟩) fun a => w ⟨i, a⟩ := by
  simp only [form, dotProduct, Fintype.sum_sigma, blockDiagonal'_mulVec_apply]
  rfl

theorem posSemidef_blockDiagonal' {A : ∀ i, Matrix (m i) (m i) ℂ} (h : ∀ i, (A i).PosSemidef) :
    (blockDiagonal' A).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    (isHermitian_blockDiagonal'_iff.2 fun i => (h i).isHermitian) fun x => ?_
  simp only [dotProduct, Fintype.sum_sigma, blockDiagonal'_mulVec_apply]
  exact Finset.sum_nonneg fun i _ => (h i).dotProduct_mulVec_nonneg fun a => x ⟨i, a⟩

theorem gnorm_blockDiagonal'_sq {A : ∀ i, Matrix (m i) (m i) ℂ} (h : ∀ i, (A i).PosSemidef)
    (v : (Σ i, m i) → ℂ) :
    gnorm (blockDiagonal' A) v ^ 2 = ∑ i, gnorm (A i) (fun a => v ⟨i, a⟩) ^ 2 := by
  simp only [gnorm_sq (posSemidef_blockDiagonal' h), gnorm_sq (h _), form_blockDiagonal', re_sum]

theorem posDef_blockDiagonal' {A : ∀ i, Matrix (m i) (m i) ℂ} (h : ∀ i, (A i).PosDef) :
    (blockDiagonal' A).PosDef := by
  refine posDef_iff.2 ⟨isHermitian_blockDiagonal'_iff.2 fun i => (h i).isHermitian,
    fun v hv => ?_⟩
  rw [form_self (posSemidef_blockDiagonal' fun i => (h i).posSemidef),
    gnorm_blockDiagonal'_sq fun i => (h i).posSemidef, zero_lt_real]
  obtain ⟨⟨i, a⟩, ha⟩ := Function.ne_iff.1 hv
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i, Finset.mem_univ _,
    pow_pos (gnorm_pos (h i) (Function.ne_iff.2 ⟨a, ha⟩)) 2⟩

variable [∀ i, DecidableEq (m i)] {H : ∀ i, E → Matrix (m i) (m i) ℂ} {z : E}

theorem isUnit_det_blockDiagonal' {A : ∀ i, Matrix (m i) (m i) ℂ} (h : ∀ i, IsUnit (A i).det) :
    IsUnit (blockDiagonal' A).det := by
  refine isUnit_det_of_right_inverse (B := blockDiagonal' fun i => (A i)⁻¹) ?_
  rw [← blockDiagonal'_mul, ← blockDiagonal'_one]
  congr 1
  funext i
  exact mul_nonsing_inv _ (h i)

theorem conn_blockDiagonal' (h : ∀ i, IsUnit (H i z).det) (ξ : E) :
    conn (fun x => blockDiagonal' fun i => H i x) z ξ = blockDiagonal' fun i => conn (H i) z ξ := by
  refine (eq_conn_of_compatible (H := fun x => blockDiagonal' fun i => H i x)
    (isUnit_det_blockDiagonal' h) ?_).symm
  rw [mdel_blockDiagonal', blockDiagonal'_transpose, ← blockDiagonal'_mul]
  congr 1
  funext i
  exact conn_transpose_mul (h i) ξ

theorem curv_blockDiagonal' {k : WithTop ℕ∞} (d : ∀ i, MContDiffAt k (H i) z)
    (h : ∀ i, IsUnit (H i z).det) (ξ η : E) :
    curv (fun x => blockDiagonal' fun i => H i x) z ξ η =
      blockDiagonal' fun i => curv (H i) z ξ η := by
  have he : (fun x => conn (fun x => blockDiagonal' fun i => H i x) x ξ) =ᶠ[𝓝 z]
      fun x => blockDiagonal' fun i => conn (H i) x ξ :=
    (eventually_all.2 fun i => (d i).eventually_isUnit (h i)).mono
      fun x hx => conn_blockDiagonal' hx ξ
  rw [curv, mdbar_congr he, mdbar_blockDiagonal' fun i x => conn (H i) x ξ, ← blockDiagonal'_neg]
  rfl

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in

theorem isHermFrame_blockDiagonal' {U : Set E} (hU : IsOpen U) (h : ∀ i, IsHermFrame U (H i)) :
    IsHermFrame U fun x => blockDiagonal' fun i => H i x :=
  .of_mContDiffAt hU (fun _ hz => mContDiffAt_blockDiagonal' fun i => (h i).mContDiffAt hz)
    (fun z hz => isHermitian_blockDiagonal'_iff.2 fun i => (h i).herm z hz)
    fun z hz => isUnit_det_blockDiagonal' fun i => (h i).isUnit z hz

end Family

end GlobalTheory.HermFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterFunctionEqZeroOfComposable
section
set_option autoImplicit false

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

theorem exists_composable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) (hK : K.Rich) (l m : Λ) (q : Tot I g) (hq : q.1 ∈ F.V) :
    ∃ k k' k'' : K.K, K.le l k' k ∧ K.le m k'' k' ∧ q ∈ K.W k'' := by
  obtain ⟨hcov, hjoin⟩ := hK
  obtain ⟨k, hk⟩ := hcov (F.shift l (F.shift m q)) hq
  obtain ⟨k₁, hk₁⟩ := hcov (F.shift m q) hq
  obtain ⟨k', hk', -, hlk⟩ := hjoin l k₁ k (F.shift m q) hk₁ hk
  obtain ⟨k₂, hk₂⟩ := hcov q hq
  obtain ⟨k'', hk'', -, hmk⟩ := hjoin m k₂ k' q hk₂ hk'
  exact ⟨k, k', k'', hlk, hmk, hk''⟩

theorem eq_zero_of_cst_composable : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F), K.Rich → ∀ (l m : Λ) (p : Hol F.V),
    (∀ (k k' k'' : K.K), K.le l k' k → K.le m k'' k' → K.cst k'' p = 0) → p = 0 := by
  intro I _ g Λ _ F K hK l m p hp
  apply Hol.ext_fn
  intro z hz
  obtain ⟨k, k', k'', h1, h2, hq⟩ := exists_composable K hK l m ((z, 0) : Tot I g) hz
  have h : (K.cst k'' p).fn ((z, 0) : Tot I g) = (0 : Hol (K.W k'')).fn ((z, 0) : Tot I g) := by
    rw [hp k k' k'' h1 h2]
  rw [fn_cst K k'' p hq, show (0 : Hol (K.W k'')) = algebraMap ℂ _ 0 from (map_zero _).symm,
    Hol.fn_algebraMap _ hq] at h
  rw [show (0 : Hol F.V) = algebraMap ℂ _ 0 from (map_zero _).symm, Hol.fn_algebraMap _ hz]
  exact h

end GlobalTheory.AnPer.Charts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialOperatorSchwartzSeminormBound
section
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff

noncomputable section
namespace GlobalTheory.SliceOpDecay

theorem norm_le_max_comp {V : Type} [NormedAddCommGroup V] {κ κ₁' : Type} [Fintype κ] [Fintype κ₁']
    (z : κ ⊕ κ₁' → V) : ‖z‖ ≤ max ‖z ∘ Sum.inl‖ ‖z ∘ Sum.inr‖ := by
  refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2 fun i => ?_
  cases i with
  | inl i => exact (norm_le_pi_norm (z ∘ Sum.inl) i).trans (le_max_left _ _)
  | inr j => exact (norm_le_pi_norm (z ∘ Sum.inr) j).trans (le_max_right _ _)

theorem pow_norm_le_add {V : Type} [NormedAddCommGroup V] {κ κ₁' : Type} [Fintype κ] [Fintype κ₁']
    (z : κ ⊕ κ₁' → V) (k : ℕ) : ‖z‖ ^ k ≤ ‖z ∘ Sum.inl‖ ^ k + ‖z ∘ Sum.inr‖ ^ k := by
  have h := pow_le_pow_left₀ (norm_nonneg z) (norm_le_max_comp z) k
  rcases le_total ‖z ∘ Sum.inl‖ ‖z ∘ Sum.inr‖ with hle | hle
  · rw [max_eq_right hle] at h; linarith [pow_nonneg (norm_nonneg (z ∘ Sum.inl)) k]
  · rw [max_eq_left hle] at h; linarith [pow_nonneg (norm_nonneg (z ∘ Sum.inr)) k]

theorem decay (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (κ κ' κ₁' : Type) [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (k : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (z : κ ⊕ κ₁' → V),
      ‖z‖ ^ k * ‖qOp P f z‖ ≤ C * s.sup (schwartzSeminormFamily ℂ (κ ⊕ κ' → V) ℂ) f := by
  obtain ⟨s1, C1, hC1, h1⟩ := clm_sup_bound P {(k, 0)}
  obtain ⟨s2, C2, hC2, h2⟩ := clm_sup_bound P {(0, 0)}
  let sh : ℕ × ℕ → ℕ × ℕ := fun i => (k + i.1, i.2)
  refine ⟨s1 ∪ s2.image sh, C1 + C2, add_nonneg hC1 hC2, fun f z => ?_⟩
  set F := schwartzSeminormFamily ℂ (κ ⊕ κ' → V) ℂ
  set x := z ∘ Sum.inl
  set y := z ∘ Sum.inr
  set g := sliceR f x
  have hq : qOp P f z = P g y := rfl
  set S := (s1 ∪ s2.image sh).sup F f
  have hS0 : 0 ≤ S := apply_nonneg _ _

  have hy : ‖y‖ ^ k * ‖P g y‖ ≤ C1 * S := by
    have a1 : ‖y‖ ^ k * ‖P g y‖ ≤ SchwartzMap.seminorm ℂ k 0 (P g) := by
      have := SchwartzMap.le_seminorm ℂ k 0 (P g) y
      simpa [norm_iteratedFDeriv_zero] using this
    have a2 := h1 g
    simp only [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply] at a2
    have a3 : s1.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) g ≤ S := by
      refine Seminorm.finset_sup_apply_le hS0 fun i hi => ?_
      have w := GlobalTheory.SliceWeight.pow_norm_mul_seminorm_sliceR_le V κ κ' f 0 i.1 i.2 x
      simp only [pow_zero, one_mul, zero_add] at w
      refine le_trans (b := SchwartzMap.seminorm ℂ _ _ f) w ?_
      have : F i f ≤ S := Seminorm.le_finset_sup_apply (Finset.mem_union_left _ hi)
      exact this
    calc _ ≤ _ := a1
      _ ≤ _ := a2
      _ ≤ C1 * S := by gcongr

  have hx : ‖x‖ ^ k * ‖P g y‖ ≤ C2 * S := by
    have a1 : ‖P g y‖ ≤ SchwartzMap.seminorm ℂ 0 0 (P g) := SchwartzMap.norm_le_seminorm ℂ (P g) y
    have a2 := h2 g
    simp only [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply] at a2
    have a3 : ‖x‖ ^ k * s2.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) g ≤ S := by
      have e : ‖x‖ ^ k * s2.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) g
          = s2.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) (((‖x‖ ^ k : ℝ) : ℂ) • g) := by
        rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
      rw [e]
      refine Seminorm.finset_sup_apply_le hS0 fun i hi => ?_
      rw [map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
      have w := GlobalTheory.SliceWeight.pow_norm_mul_seminorm_sliceR_le V κ κ' f k i.1 i.2 x
      refine le_trans (b := SchwartzMap.seminorm ℂ _ _ f) w ?_
      have : F (sh i) f ≤ S :=
        Seminorm.le_finset_sup_apply (Finset.mem_union_right _ (Finset.mem_image_of_mem sh hi))
      simpa [F, sh, SchwartzMap.schwartzSeminormFamily_apply] using this
    calc ‖x‖ ^ k * ‖P g y‖ ≤ ‖x‖ ^ k * (C2 * s2.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) g) := by
          gcongr; exact a1.trans a2
      _ = C2 * (‖x‖ ^ k * s2.sup (schwartzSeminormFamily ℂ (κ' → V) ℂ) g) := by ring
      _ ≤ C2 * S := by gcongr
  rw [hq]
  calc ‖z‖ ^ k * ‖P g y‖ ≤ (‖x‖ ^ k + ‖y‖ ^ k) * ‖P g y‖ := by
        gcongr; exact pow_norm_le_add z k
    _ = ‖x‖ ^ k * ‖P g y‖ + ‖y‖ ^ k * ‖P g y‖ := by ring
    _ ≤ C2 * S + C1 * S := add_le_add hx hy
    _ = (C1 + C2) * S := by ring

end GlobalTheory.SliceOpDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicardTorsionTrivialOfTorsorsHaveSections
section
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KummerStep

open GlobalTheory.KummerAlg

theorem p1 : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L] [Module.Invertible B L] (q : ℕ) (φ : MultilinearMap B (fun _ : Fin q => L) B), 0 < q → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) → Module.Finite B (GlobalTheory.KummerAlg.Alg φ) ∧ Module.Projective B (GlobalTheory.KummerAlg.Alg φ) ∧ Module.FaithfullyFlat B (GlobalTheory.KummerAlg.Alg φ) := GlobalTheory.T.kummerAlgebra_finite_projective_faithfullyFlat
theorem p2 : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L] [Module.Invertible B L] (q : ℕ) [NeZero q] (φ : MultilinearMap B (fun _ : Fin q => L) B), IsUnit (q : B) → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) → ∀ (ζ : B) (hζ : ζ ^ q = 1), (∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k)) → Function.Bijective (Algebra.TensorProduct.productMap (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ) (fun _ => AlgHom.id B (GlobalTheory.KummerAlg.Alg φ))) (Pi.algHom B (fun _ : Multiplicative (ZMod q) => GlobalTheory.KummerAlg.Alg φ) (fun g => (GlobalTheory.KummerAlg.act φ ζ hζ g).toAlgHom))) := GlobalTheory.T.kummerAlgebra_zmod_torsor_bijective
theorem p4 : ∀ (B : Type) [CommRing B] (q : ℕ) (c : CommRing.Pic B), c ^ q = 1 → ∃ φ : MultilinearMap B (fun _ : Fin q => CommRing.Pic.AsModule c) B, ∀ p : Ideal B, p.IsPrime → ∃ e : CommRing.Pic.AsModule c, φ (fun _ => e) ∉ p := GlobalTheory.T.exists_multilinear_form_of_pic_torsion

theorem free_of_section (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L]
    [Module.Invertible B L] (q : ℕ) (φ : MultilinearMap B (fun _ : Fin q => L) B) (hq : 0 < q)
    (hφ : ∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p)
    (s : Alg φ →ₐ[B] B) : Module.Free B L := by
  let f : L →ₗ[B] B := s.toLinearMap ∘ₗ gen φ
  have hf : ∀ e : L, f e ^ q = φ (fun _ => e) := fun e => by
    have := congrArg s (prod_gen φ (fun _ => e))
    simpa [f, map_prod, Finset.prod_const, AlgHom.commutes] using this
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (LinearMap.range f) h
    obtain ⟨e, he⟩ := hφ m hm.isPrime
    apply he
    rw [← hf e]
    exact Ideal.pow_mem_of_mem _ (hle ⟨e, rfl⟩) q hq
  exact Module.Free.of_equiv
    (LinearEquiv.ofBijective f (Module.Invertible.bijective_of_surjective hsurj)).symm

theorem kummer_step : ∀ (B : Type) [CommRing B] (q : ℕ), 0 < q → IsUnit (q : B) →
    (∃ ζ : B, ζ ^ q = 1 ∧ ∀ k : ℕ, 0 < k → k < q → IsUnit (1 - ζ ^ k)) →
    (∀ (D : Type) [CommRing D] [Algebra B D], Module.Finite B D → Module.Projective B D →
      Module.FaithfullyFlat B D → ∀ act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D),
      Function.Bijective (Algebra.TensorProduct.productMap
        (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
        (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom))) → Nonempty (D →ₐ[B] B)) →
    ∀ c : CommRing.Pic B, c ^ q = 1 → c = 1 := by
  intro B _ q hq hqu ⟨ζ, hζ, hζk⟩ hT c hc
  haveI : NeZero q := ⟨hq.ne'⟩
  obtain ⟨φ, hφ⟩ := p4 B q c hc
  obtain ⟨hfin, hproj, hff⟩ := p1 B (CommRing.Pic.AsModule c) q φ hq hφ
  obtain ⟨s⟩ := hT (Alg φ) hfin hproj hff (act φ ζ hζ) (p2 B (CommRing.Pic.AsModule c) q φ hqu hφ ζ hζ hζk)
  have := free_of_section B (CommRing.Pic.AsModule c) q φ hq hφ s
  rw [← CommRing.Pic.mk_eq_self (M := c), CommRing.Pic.mk_eq_one_iff_free]
  exact this

end GlobalTheory.KummerStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialGrowthOfPeriodicIntegralSpansStatement
section
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_growth_of_periodic_integral_spans : ∀ (g m : ℕ) (lam : ℂ → Fin m → Fin g → ℂ) (C : ℝ) (k : ℕ), ContinuousOn lam {s : ℂ | s.re < 0} → (∀ s : ℂ, s.re < 0 → LinearIndependent ℝ (lam s)) → (∀ s : ℂ, s.re < 0 → ∀ z : Fin g → ℂ, (∃ n : Fin m → ℤ, z = ∑ j, n j • lam (s + 2 * Real.pi * Complex.I) j) ↔ ∃ n : Fin m → ℤ, z = ∑ j, n j • lam s j) → (∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ Real.pi → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k) → ∀ R : ℝ, ∃ C' : ℝ, ∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ R → ‖lam s‖ ≤ C' * (1 + ‖s‖) ^ k := by
  first | exact @GlobalTheory.StripGrowth.strip_growth | exact GlobalTheory.StripGrowth.strip_growth | (intros; apply GlobalTheory.StripGrowth.strip_growth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulMemSubalgebraOfResBasicOpen
section
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub.PowerMultiple

variable {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)

theorem res_pow_mul_mem_gen
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {D W V : X.Opens} (hD : IsAffineOpen D) (hDW : D ≤ W) (hDV : D ≤ V)
    (T : Set (F.obj (op V))) (f : Γ(X, W)) (a : F.obj (op W))
    (ha : ∀ (W' : X.Opens), IsAffineOpen W' → ∀ (h1 : W' ≤ X.basicOpen f) (h2 : W' ≤ V),
      (F.map (homOfLE h1).op).hom ((F.map (homOfLE (X.basicOpen_le f)).op).hom a) ∈
        gen F α h2 T) :
    ∃ m : ℕ, (F.map (homOfLE hDW).op).hom ((α.app (op W)).hom f ^ m * a) ∈ gen F α hDV T := by
  set fD : Γ(X, D) := (X.presheaf.map (homOfLE hDW).op).hom f with hfD
  have hbo : X.basicOpen fD = D ⊓ X.basicOpen f := Scheme.basicOpen_res X f (homOfLE hDW).op
  have hD'D : X.basicOpen fD ≤ D := X.basicOpen_le fD
  have hD'f : X.basicOpen fD ≤ X.basicOpen f := hbo.le.trans inf_le_right
  have hD'V : X.basicOpen fD ≤ V := hD'D.trans hDV
  have hD' : IsAffineOpen (X.basicOpen fD) := hD.basicOpen fD
  letI iRA : Algebra Γ(X, D) (F.obj (op D)) := (α.app (op D)).hom.toAlgebra
  letI iRR' : Algebra Γ(X, D) Γ(X, X.basicOpen fD) :=
    (X.presheaf.map (homOfLE hD'D).op).hom.toAlgebra
  letI iR'A' : Algebra Γ(X, X.basicOpen fD) (F.obj (op (X.basicOpen fD))) :=
    (α.app (op (X.basicOpen fD))).hom.toAlgebra
  letI iAA' : Algebra (F.obj (op D)) (F.obj (op (X.basicOpen fD))) :=
    (F.map (homOfLE hD'D).op).hom.toAlgebra
  letI iRA' : Algebra Γ(X, D) (F.obj (op (X.basicOpen fD))) :=
    ((F.map (homOfLE hD'D).op).hom.comp (α.app (op D)).hom).toAlgebra
  haveI : IsScalarTower Γ(X, D) (F.obj (op D)) (F.obj (op (X.basicOpen fD))) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower Γ(X, D) Γ(X, X.basicOpen fD) (F.obj (op (X.basicOpen fD))) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    have := congr($(α.naturality (homOfLE hD'D).op).hom r)
    simp only [CommRingCat.comp_apply] at this
    exact this.symm
  haveI : IsLocalization.Away fD Γ(X, X.basicOpen fD) := hD.isLocalization_basicOpen fD
  haveI : IsLocalization.Away (algebraMap Γ(X, D) (F.obj (op D)) fD)
      (F.obj (op (X.basicOpen fD))) := isLocalizationAway F α hα hD fD
  have hres : ∀ {U₁ U₂ U₃ : X.Opens} (h₁ : U₂ ≤ U₁) (h₂ : U₃ ≤ U₂) (y : F.obj (op U₁)),
      (F.map (homOfLE h₂).op).hom ((F.map (homOfLE h₁).op).hom y) =
        (F.map (homOfLE (h₂.trans h₁)).op).hom y := by
    intro U₁ U₂ U₃ h₁ h₂ y
    rw [← CommRingCat.comp_apply, ← F.map_comp]
    rfl
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_pow_mul_mem_adjoin_of_localizationAway (R := Γ(X, D)) (A := F.obj (op D))
    (R' := Γ(X, X.basicOpen fD)) (A' := F.obj (op (X.basicOpen fD))) fD
    ((F.map (homOfLE hDV).op).hom '' T) ((F.map (homOfLE hDW).op).hom a) (by
      have h0 := ha _ hD' hD'f hD'V
      rw [hres, gen_eq_adjoin] at h0
      change (F.map (homOfLE hD'D).op).hom ((F.map (homOfLE hDW).op).hom a) ∈ _
      rw [hres, Set.image_image]
      have hfun : (fun x => (algebraMap (F.obj (op D)) (F.obj (op (X.basicOpen fD))))
          ((F.map (homOfLE hDV).op).hom x)) = ⇑(F.map (homOfLE hD'V).op).hom :=
        funext fun x => hres _ _ x
      rw [hfun]
      exact h0)
  refine ⟨m, ?_⟩
  have hnat : (F.map (homOfLE hDW).op).hom ((α.app (op W)).hom f) = (α.app (op D)).hom fD := by
    have := congr($(α.naturality (homOfLE hDW).op).hom f)
    simp only [CommRingCat.comp_apply] at this
    exact this.symm
  rw [map_mul, map_pow, hnat, gen_eq_adjoin]
  exact hm

end GlobalTheory.QcSub.PowerMultiple

theorem GlobalTheory.QcSub.pow_mul_mem_sub_of_res_basicOpen : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (T : ∀ j, Set (F.obj (op (V j)))) (W : X.Opens), IsAffineOpen W → ∀ (f : Γ(X, W)) (a : F.obj (op W)), (F.map (homOfLE (X.basicOpen_le f)).op).hom a ∈ sub F α V T (X.basicOpen f) → ∃ m : ℕ, (α.app (op W)).hom f ^ m * a ∈ sub F α V T W := by
  intro X hX F α hα ι _ V hV T W hW f a ha
  classical
  haveI := Fintype.ofFinite ι
  rw [mem_sub] at ha
  choose s hs1 hs2 using fun j => GlobalTheory.T.exists_finset_basicOpen_cover_inf_of_isAffineOpen X hX W (V j) hW (hV j)
  have hle : ∀ j, ∀ h ∈ s j, X.basicOpen h ≤ V j := by
    intro j h hh
    obtain ⟨r, hr⟩ := hs1 j h hh
    rw [hr]
    exact X.basicOpen_le r
  choose m hm using fun j (h : s j) =>
    GlobalTheory.QcSub.PowerMultiple.res_pow_mul_mem_gen F α hα (hW.basicOpen h.1) (X.basicOpen_le h.1)
      (hle j h.1 h.2) (T j) f a (fun W' hW' h1 h2 => ha j W' hW' h1 h2)
  refine ⟨∑ j, ∑ h : s j, m j h, ?_⟩
  rw [mem_sub]
  intro j W' hW' hWW' hWV
  refine GlobalTheory.T.mem_adjoin_restricted_sections_of_local X F α hα (V j) W (T j) _ ?_ W' hW' hWW' hWV
  intro x hx
  have hx' := hs2 j hx
  simp only [Set.mem_iUnion, SetLike.mem_coe] at hx'
  obtain ⟨h, hh, hxh⟩ := hx'
  refine ⟨X.basicOpen h, hW.basicOpen h, hxh, X.basicOpen_le h, hle j h hh, ?_⟩
  have hmle : m j ⟨h, hh⟩ ≤ ∑ j, ∑ h : s j, m j h :=
    le_trans (Finset.single_le_sum (f := fun h' => m j h') (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (⟨h, hh⟩ : s j)))
      (Finset.single_le_sum (f := fun j' => ∑ h' : s j', m j' h') (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j))
  rw [show ∑ j, ∑ h : s j, m j h = (∑ j, ∑ h : s j, m j h - m j ⟨h, hh⟩) + m j ⟨h, hh⟩ by omega,
    pow_add, mul_assoc, map_mul]
  refine mul_mem ?_ (hm j ⟨h, hh⟩)
  rw [map_pow]
  refine pow_mem ?_ _
  have := congr($(α.naturality (homOfLE (X.basicOpen_le h)).op).hom f)
  simp only [CommRingCat.comp_apply] at this
  rw [← this]
  exact algebraMap_mem_gen F α _ _ _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageEqOfSquareZeroThickening
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.SecGlue

theorem preimage_eq_of_comp_eq_of_sqZero : ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T),
    Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (Y : Scheme.{0}) (u w : Sp S ⟶ Y), spMap q ≫ u = spMap q ≫ w → ∀ V : Y.Opens,
      u ⁻¹ᵁ V = w ⁻¹ᵁ V := by
  intro S T _ _ q hq hsq Y u w huw V
  have hsurj : Function.Surjective (spMap q).base := by
    intro p
    have hker : RingHom.ker q ≤ p.asIdeal := by
      intro x hx
      have hx2 : x * x ∈ RingHom.ker q ^ 2 := by
        rw [sq]; exact Ideal.mul_mem_mul hx hx
      rw [hsq, Ideal.mem_bot] at hx2
      exact (p.isPrime.mem_or_mem (by rw [hx2]; exact p.asIdeal.zero_mem)).elim id id
    haveI := p.isPrime
    haveI : (Ideal.map q p.asIdeal).IsPrime := Ideal.map_isPrime_of_surjective hq hker
    refine ⟨⟨Ideal.map q p.asIdeal, this⟩, ?_⟩
    rw [Spec.map_base]
    apply PrimeSpectrum.ext
    change Ideal.comap q (Ideal.map q p.asIdeal) = p.asIdeal
    rw [Ideal.comap_map_of_surjective _ hq, sup_eq_left]
    intro x hx
    exact hker (by simpa [RingHom.mem_ker] using hx)
  ext x
  obtain ⟨y, rfl⟩ := hsurj x
  rw [SetLike.mem_coe, SetLike.mem_coe, Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage,
    ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, huw]

end GlobalTheory.SecGlue
end

