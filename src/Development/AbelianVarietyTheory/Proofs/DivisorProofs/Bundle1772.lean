import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticBasisOfUnitaryFrame
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

namespace GlobalTheory.ThKTorus

open Module

theorem exists_isSymplecticBasis_extend_family {R M ι : Type} [Field R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Fintype ι] {B : LinearMap.BilinForm R M} (hB : B.IsAlt) (hp : Function.Injective B)
    {v f : ι → M} (hf : IsSymplecticFamily B v f fun _ => 1) :
    ∃ (g : ℕ) (b : Basis ((ι ⊕ Fin g) ⊕ (ι ⊕ Fin g)) R M), IsSymplecticBasis B b ∧
      (∀ i, b (.inl (.inl i)) = v i) ∧ ∀ i, b (.inr (.inl i)) = f i := by
  classical
  let N : Submodule R M := (⨅ i, LinearMap.ker (B (v i))) ⊓ ⨅ i, LinearMap.ker (B (f i))
  have hmem : ∀ y, y ∈ N ↔ (∀ i, B (v i) y = 0) ∧ ∀ i, B (f i) y = 0 := fun y => by
    simp [N, Submodule.mem_iInf]
  have hdec : ∀ y, ∃ a b : ι → R, ∃ y' ∈ N, y = ∑ i, a i • v i + ∑ i, b i • f i + y' := by
    intro y
    refine ⟨fun i => B y (f i), fun i => B (v i) y,
      y - ∑ i, B y (f i) • v i - ∑ i, B (v i) y • f i, (hmem _).2 ⟨fun k => ?_, fun k => ?_⟩,
      by abel⟩
    · simp [hf.left_left, hf.left_right]
    · simp [hf.right_right, hf.right_left hB, ← hB.neg_eq y]
  obtain ⟨g, e', f', d, h', hd, -, hspan⟩ := exists_isSymplecticFamily_span_eq hB N (by
    intro x hx hx0
    refine (injective_iff_map_eq_zero B).1 hp x (LinearMap.ext fun y => ?_)
    obtain ⟨a, b, y', hy', rfl⟩ := hdec y
    simp [hx0 y' hy', fun i => hB.eq_iff.1 (((hmem x).1 hx).1 i),
      fun i => hB.eq_iff.1 (((hmem x).1 hx).2 i)])
  have he' : ∀ i, e' i ∈ N := fun i => hspan ▸ Submodule.subset_span ⟨Sum.inl i, rfl⟩
  have hf' : ∀ i, f' i ∈ N := fun i => hspan ▸ Submodule.subset_span ⟨Sum.inr i, rfl⟩
  have h'' : IsSymplecticFamily B e' (fun i => (d i)⁻¹ • f' i) fun _ => 1 :=
    ⟨h'.left_left, fun i j => by simp [h'.right_right], fun i => by simp [h'.left_right_self, hd i],
      fun i j hij => by simp [h'.left_right_ne i j hij]⟩
  have hs := IsSymplecticFamily.sum hB hf h'' (fun i j => ((hmem _).1 (he' j)).1 i)
    (fun i j => ((hmem _).1 (N.smul_mem _ (hf' j))).1 i) (fun i j => ((hmem _).1 (he' j)).2 i)
    (fun i j => ((hmem _).1 (N.smul_mem _ (hf' j))).2 i)
  have h1 : (Sum.elim (fun _ : ι => (1 : R)) fun _ : Fin g => (1 : R)) = fun _ => 1 := by
    funext i; cases i <;> rfl
  rw [h1] at hs
  have hsp : ⊤ ≤ Submodule.span R (Set.range (Sum.elim (Sum.elim v e')
      (Sum.elim f fun i => (d i)⁻¹ • f' i))) := by
    intro y _
    obtain ⟨a, b, y', hy', rfl⟩ := hdec y
    refine Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)) ?_
    · exact Submodule.subset_span ⟨Sum.inl (Sum.inl i), rfl⟩
    · exact Submodule.subset_span ⟨Sum.inr (Sum.inl i), rfl⟩
    · rw [← hspan] at hy'
      refine Submodule.span_le.2 ?_ hy'
      rintro _ ⟨i | i, rfl⟩
      · exact Submodule.subset_span ⟨Sum.inl (Sum.inr i), rfl⟩
      · have : Sum.elim e' f' (Sum.inr i) = d i • (d i)⁻¹ • f' i := by simp [smul_smul, hd i]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr (Sum.inr i), rfl⟩)
  refine ⟨g, Basis.mk (hs.linearIndependent fun _ => one_ne_zero) hsp, ?_, fun i => by simp, fun i => by simp⟩
  simpa [IsSymplecticBasis, IsSymplecticBasisOfType] using hs

section

variable {F E : Type} [Field F] [Field E] [Algebra F E]

noncomputable def colTraceBil (σ : E →ₐ[F] E) {d : ℕ} (K : Matrix (Fin d) (Fin d) E) :
    LinearMap.BilinForm F (Fin d → E) :=
  LinearMap.mk₂ F (fun f g => Algebra.trace F E (-1 * form σ K f g))
    (fun x x' y => by simp only [form, add_dotProduct, mul_add, map_add])
    (fun a x y => by simp only [form, smul_dotProduct, mul_smul_comm, map_smul])
    (fun x y y' => by
      simp only [form, dotProduct, Matrix.mulVec, Pi.add_apply, Finset.sum_add_distrib, mul_add, map_add])
    (fun a x y => by
      simp only [form, dotProduct, Matrix.mulVec, Pi.smul_apply, ← Finset.smul_sum, mul_smul_comm, map_smul])

theorem colTraceBil_apply (σ : E →ₐ[F] E) {d : ℕ} (K : Matrix (Fin d) (Fin d) E) (f g : Fin d → E) :
    colTraceBil σ K f g = Algebra.trace F E (-1 * form σ K f g) := rfl

theorem nondegenerate_colTraceBil [CharZero F] [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a)
    {d : ℕ} {K : Matrix (Fin d) (Fin d) E} (hK : K.det ≠ 0) : (colTraceBil σ K).Nondegenerate := by
  rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  refine Matrix.eq_zero_of_vecMul_eq_zero hK (funext fun l => ?_)
  refine (traceForm_nondegenerate F E).1 _ fun a => ?_
  have := LinearMap.congr_fun hf (Pi.single l (σ (-a)))
  rw [colTraceBil_apply, LinearMap.zero_apply] at this
  rw [Algebra.traceForm_apply, ← this]
  congr 1
  have h : (fun i => σ ((Pi.single l (σ (-a)) : Fin d → E) i)) = Pi.single l (-a) := by
    funext i
    by_cases hi : i = l
    · subst hi; simp only [Pi.single_eq_same, hσ]
    · simp [hi]
  rw [form, h, Matrix.dotProduct_mulVec, dotProduct_single]
  ring

theorem symp_vecMulVec_right (σ : E →ₐ[F] E) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (K : Matrix (Fin d) (Fin d) E) (m : Matrix (Fin n) (Fin d) E) (v : Fin n → E) (w : Fin d → E) :
    symp σ (-1) J K m (Matrix.vecMulVec v w) = colTraceBil σ K (fun l => form σ J (fun r => m r l) v) w := by
  rw [colTraceBil_apply, symp]
  congr 2
  simp only [hTens, form, dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem symp_vecMulVec (σ : E →ₐ[F] E) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (K : Matrix (Fin d) (Fin d) E) (u v : Fin n → E) (f w : Fin d → E) :
    symp σ (-1) J K (Matrix.vecMulVec u f) (Matrix.vecMulVec v w) = colTraceBil σ K (form σ J u v • f) w := by
  rw [symp_vecMulVec_right]
  congr 2
  funext l
  simp only [form, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem form_swap (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (u v : Fin n → E) : form σ J u v = σ (form σ J v u) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end

theorem exists_frame_symplectic_basis : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d q : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E) (x y : Fin q → Fin n → E),
    (∀ a, σ (σ a) = a) → Module.finrank F E = 2 → (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    (∀ i j, σ (K j i) = -K i j) → K.det ≠ 0 → IsFrameU σ J x y →
    ∃ (b : Module.Basis ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F (Matrix (Fin n) (Fin d) E))
      (blk : Fin q → Finset (Fin n × Fin d)),
      (∀ i j, i ≠ j → Disjoint (blk i) (blk j)) ∧
      (∀ k l, symp σ (-1) J K (b (.inl k)) (b (.inl l)) = 0) ∧
      (∀ k l, symp σ (-1) J K (b (.inr k)) (b (.inr l)) = 0) ∧
      (∀ k l, symp σ (-1) J K (b (.inl k)) (b (.inr l)) = if k = l then 1 else 0) ∧
      (∀ k l, symp σ (-1) J K (b (.inr k)) (b (.inl l)) = if k = l then -1 else 0) ∧
      (∀ i, ∀ k ∈ blk i, ∃ w : Fin d → E, b (.inl k) = Matrix.vecMulVec (y i) w) ∧
      (∀ i, ∀ k ∈ blk i, ∃ w : Fin d → E, b (.inr k) = Matrix.vecMulVec (x i) w) ∧
      (∀ k, (∀ i, k ∉ blk i) → ∀ (l : Fin d) (i : Fin q),
        form σ J (fun r => b (.inl k) r l) (x i) = 0 ∧ form σ J (fun r => b (.inl k) r l) (y i) = 0 ∧
        form σ J (fun r => b (.inr k) r l) (x i) = 0 ∧ form σ J (fun r => b (.inr k) r l) (y i) = 0) := by
  intro F E _ _ _ _ _ σ n d q J K x y hσ h2 hJ hJ' hK hK' hfr
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have halt := GlobalTheory.RatDarboux.isAlt_sympBil σ hσ hJ hK
  have hinj := (GlobalTheory.RatDarboux.bijective_sympBil σ hσ hJ' hK').1
  have hnd := nondegenerate_colTraceBil σ hσ hK'
  set B := GlobalTheory.RatDarboux.sympBil σ (-1) J K with hBdef
  have hB : ∀ a b, B a b = symp σ (-1) J K a b := fun _ _ => rfl
  let g := Module.finBasis F (Fin d → E)
  let f := (colTraceBil σ K).dualBasis hnd g
  have hfg : ∀ k l, colTraceBil σ K (f k) (g l) = if l = k then 1 else 0 :=
    LinearMap.BilinForm.apply_dualBasis_left hnd g
  have hyx : ∀ i j, form σ J (y i) (x j) = if i = j then 1 else 0 := fun i j => by
    rw [form_swap σ hσ hJ, hfr.2.2]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hfam : IsSymplecticFamily B
      (fun p : Fin q × Fin (Module.finrank F (Fin d → E)) => Matrix.vecMulVec (y p.1) (f p.2))
      (fun p => Matrix.vecMulVec (x p.1) (g p.2)) fun _ => 1 := by
    refine ⟨fun p r => ?_, fun p r => ?_, fun p => ?_, fun p r hpr => ?_⟩
    · simp [hB, symp_vecMulVec, hfr.2.1]
    · simp [hB, symp_vecMulVec, hfr.1]
    · simp [hB, symp_vecMulVec, hyx, hfg]
    · rw [hB, symp_vecMulVec, hyx]
      by_cases h : p.1 = r.1
      · have h' : ¬ r.2 = p.2 := fun h' => hpr (Prod.ext h h'.symm)
        simp [h, hfg, h']
      · simp [h]
  obtain ⟨s, b₀, hb₀, hl, hr⟩ := exists_isSymplecticBasis_extend_family halt hinj hfam
  have hcard : Fintype.card ((Fin q × Fin (Module.finrank F (Fin d → E))) ⊕ Fin s) =
      Fintype.card (Fin n × Fin d) := by
    have h1 := IsSymplecticBasisOfType.finrank_eq b₀
    rw [Module.finrank_matrix, h2] at h1
    rw [Fintype.card_prod (Fin n)]
    omega
  let ε := Fintype.equivOfCardEq hcard
  have hb := hb₀.reindex ε
  have hbl : ∀ k, b₀.reindex (ε.sumCongr ε) (.inl (ε k)) = b₀ (.inl k) := fun k => by simp
  have hbr : ∀ k, b₀.reindex (ε.sumCongr ε) (.inr (ε k)) = b₀ (.inr k) := fun k => by simp
  have hcol : ∀ (m : Matrix (Fin n) (Fin d) E) (v : Fin n → E)
      (c : Basis (Fin (Module.finrank F (Fin d → E))) F (Fin d → E)),
      (∀ k, B m (Matrix.vecMulVec v (c k)) = 0) → ∀ l, form σ J (fun r => m r l) v = 0 := by
    intro m v c h l
    have h0 : colTraceBil σ K (fun l => form σ J (fun r => m r l) v) = 0 :=
      c.ext fun k => by rw [← symp_vecMulVec_right, ← hB, h, LinearMap.zero_apply]
    exact congrFun (hnd.1 _ fun w => by rw [h0, LinearMap.zero_apply]) l
  refine ⟨b₀.reindex (ε.sumCongr ε), fun i => Finset.univ.image fun k => ε (.inl (i, k)), ?_,
    hb.left_left, hb.right_right, hb.left_right, hb.right_left halt, ?_, ?_, ?_⟩
  · intro i j hij
    rw [Finset.disjoint_left]
    intro a ha ha'
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨k', -, h⟩ := Finset.mem_image.1 ha'
    exact hij (congrArg Prod.fst (Sum.inl_injective (ε.injective h))).symm
  · intro i k hk
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hk
    exact ⟨f k, by rw [hbl, hl]⟩
  · intro i k hk
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hk
    exact ⟨g k, by rw [hbr, hr]⟩
  · intro k hk l i
    obtain ⟨k, rfl⟩ := ε.surjective k
    rcases k with ⟨j, k⟩ | k
    · exact absurd (Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩) (hk j)
    rw [hbl, hbr]
    refine ⟨hcol _ _ g (fun k' => ?_) l, hcol _ _ f (fun k' => ?_) l, hcol _ _ g (fun k' => ?_) l,
      hcol _ _ f (fun k' => ?_) l⟩
    · rw [← hr (i, k'), hb₀.left_right]; simp
    · rw [← hl (i, k'), hb₀.left_left]
    · rw [← hr (i, k'), hb₀.right_right]
    · rw [← hl (i, k'), hb₀.right_left halt]; simp

end GlobalTheory.ThKTorus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticBlockBasisOrthogonal
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.ThKTorus.FrameCoords

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in

theorem incM_vecMulVec {n d : ℕ} (u : Fin n → E) (w : Fin d → E) :
    incM F (Matrix.vecMulVec u w) = Matrix.vecMulVec (incV F u) (incV F w) := by
  ext r l
  simp [incM, incV, Matrix.vecMulVec_apply, map_mul]

theorem mul_vecMulVec_eq {n d : ℕ} {R : Type} [CommRing R] (A : Matrix (Fin n) (Fin n) R) (u : Fin n → R)
    (w : Fin d → R) : A * Matrix.vecMulVec u w = Matrix.vecMulVec (A *ᵥ u) w := by
  ext r l
  simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

omit [NumberField E] in

theorem mul_incM_of_cols {n d : ℕ} (A : Matrix (Fin n) (Fin n) (AE F E)) (m : Matrix (Fin n) (Fin d) E)
    (h : ∀ l, A *ᵥ incV F (fun r => m r l) = incV F (fun r => m r l)) : A * incM F m = incM F m := by
  ext r l
  have := congrFun (h l) r
  rw [Matrix.mulVec, dotProduct] at this
  rw [Matrix.mul_apply]
  exact this

omit [NumberField E] in

theorem mulVec_eq_tAd {n : ℕ} (A : Matrix (Fin n) (Fin n) (AE F E)) (v : Fin n → AE F E) (s : ℝ)
    (h : (A - 1) *ᵥ v = realAd F (s - 1) • v) : A *ᵥ v = tAd F s • v := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_iff_eq_add] at h
  rw [h, tAd, add_smul, one_smul, add_comm]

end GlobalTheory.ThKTorus.FrameCoords

open GlobalTheory.ThKTorus.FrameCoords

theorem GlobalTheory.ThKTorus.exists_frameCo_of_basis : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d q : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E) (x y : Fin q → Fin n → E)
    (b : Module.Basis ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F (Matrix (Fin n) (Fin d) E))
    (blk : Fin q → Finset (Fin n × Fin d)),
    (∀ i j, i ≠ j → Disjoint (blk i) (blk j)) →
    (∀ k l, symp σ (-1) J K (b (.inl k)) (b (.inl l)) = 0) →
    (∀ k l, symp σ (-1) J K (b (.inr k)) (b (.inr l)) = 0) →
    (∀ k l, symp σ (-1) J K (b (.inl k)) (b (.inr l)) = if k = l then 1 else 0) →
    (∀ k l, symp σ (-1) J K (b (.inr k)) (b (.inl l)) = if k = l then -1 else 0) →
    (∀ i, ∀ k ∈ blk i, ∃ w : Fin d → E, b (.inl k) = Matrix.vecMulVec (y i) w) →
    (∀ i, ∀ k ∈ blk i, ∃ w : Fin d → E, b (.inr k) = Matrix.vecMulVec (x i) w) →
    (∀ k, (∀ i, k ∉ blk i) → ∀ (l : Fin d) (i : Fin q),
        form σ J (fun r => b (.inl k) r l) (x i) = 0 ∧ form σ J (fun r => b (.inl k) r l) (y i) = 0 ∧
        form σ J (fun r => b (.inr k) r l) (x i) = 0 ∧ form σ J (fun r => b (.inr k) r l) (y i) = 0) →
    ∃ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F K)) (Fin n × Fin d),
      (∀ m : Matrix (Fin n) (Fin d) E, ∃ u v : Fin n × Fin d → F,
        co.e (incM F m) = (fun i => algebraMap F (AF F) (u i), fun i => algebraMap F (AF F) (v i))) ∧
      IsFrameCo σ J K x y co blk := by
  intro F E _ _ _ _ _ σ n d q J K x y b blk hdis h11 h22 h12 h21 hyl hxr hoff
  classical
  let b' : Module.Basis ((Fin n × Fin d) ⊕ (Fin n × Fin d)) (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
    (b.baseChange (AF F)).map (GlobalTheory.RatDarboux.matBC (AF F))
  have hb'v : ∀ j, b' j = incM F (b j) := fun j => by
    simp only [b', Module.Basis.map_apply, Module.Basis.baseChange_apply, GlobalTheory.RatDarboux.matBC_one]
    rfl
  have hb' : ∀ i j, GlobalTheory.RatDarboux.sympBil (cA σ) (-1) (incM F J) (incM F K) (b' i) (b' j) =
      algebraMap F (AF F) (symp σ (-1) J K (b i) (b j)) := fun i j => by
    rw [hb'v, hb'v]
    exact GlobalTheory.RatDarboux.symp_map (AF F) σ J K _ _
  obtain ⟨co, hco⟩ := GlobalTheory.RatDarboux.exists_darboux_of_basis
    (GlobalTheory.RatDarboux.sympBil (cA σ) (-1) (incM F J) (incM F K)) b'
    (fun i j => by rw [hb', h11, map_zero])
    (fun i j => by rw [hb', h22, map_zero])
    (fun i => by rw [hb', h12, if_pos rfl, map_one])
    (fun i j h => by rw [hb', h12, if_neg h, map_zero])
    (fun i => by rw [hb', h21, if_pos rfl, map_neg, map_one])
    (fun i j h => by rw [hb', h21, if_neg h, map_zero])
  refine ⟨co, fun m => ⟨fun k => b.repr m (.inl k), fun k => b.repr m (.inr k), ?_⟩, hdis, ?_⟩
  · have hx : ∀ i, b'.repr (incM F m) i = algebraMap F (AF F) (b.repr m i) := fun i => by
      rw [show incM F m = GlobalTheory.RatDarboux.matBC (AF F) ((1 : AF F) ⊗ₜ[F] m) from (GlobalTheory.RatDarboux.matBC_one _ m).symm]
      simp [b', Algebra.smul_def]
    rw [hco]
    simp only [hx]
  · intro t a _ hT z
    let c : (Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F :=
      Sum.elim (fun k => ∏ i, if k ∈ blk i then tAd F (t i)⁻¹ else 1)
        (fun k => ∏ i, if k ∈ blk i then tAd F (t i) else 1)
    have hprod : ∀ (s : Fin q → ℝ) (i : Fin q) (k : Fin n × Fin d), k ∈ blk i →
        (∏ i', if k ∈ blk i' then tAd F (s i') else 1) = tAd F (s i) := fun s i k hi => by
      rw [Finset.prod_eq_single i (fun i' _ hne => if_neg fun h' =>
        Finset.disjoint_left.1 (hdis i i' hne.symm) hi h') (fun h => absurd (Finset.mem_univ i) h), if_pos hi]
    have hone : ∀ (s : Fin q → ℝ) (k : Fin n × Fin d), (∀ i, k ∉ blk i) →
        (∏ i', if k ∈ blk i' then tAd F (s i') else 1) = 1 := fun s k hk =>
      Finset.prod_eq_one fun i _ => if_neg (hk i)
    have hfix : ∀ k, (∀ i, k ∉ blk i) → ∀ j, (j = Sum.inl k ∨ j = Sum.inr k) → mat a * b' j = b' j := by
      intro k hk j hj
      rw [hb'v]
      refine mul_incM_of_cols _ _ fun l => ?_
      have h0 := hT.2.2 (fun r => b j r l)
        (fun i => by rcases hj with rfl | rfl; exacts [(hoff k hk l i).1, (hoff k hk l i).2.2.1])
        (fun i => by rcases hj with rfl | rfl; exacts [(hoff k hk l i).2.1, (hoff k hk l i).2.2.2])
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
      exact h0
    have hc : ∀ j, mat a * b' j = c j • b' j := by
      rintro (k | k)
      · by_cases hk : ∃ i, k ∈ blk i
        · obtain ⟨i, hi⟩ := hk
          obtain ⟨w, hw⟩ := hyl i k hi
          have hcv : c (.inl k) = tAd F (t i)⁻¹ := hprod (fun i => (t i)⁻¹) i k hi
          rw [hcv, hb'v, hw, incM_vecMulVec, mul_vecMulVec_eq, mulVec_eq_tAd _ _ _ (hT.2.1 i)]
          ext r l
          simp [Matrix.vecMulVec_apply, smul_mul_assoc]
        · push_neg at hk
          have hcv : c (.inl k) = 1 := hone (fun i => (t i)⁻¹) k hk
          rw [hcv, one_smul]
          exact hfix k hk _ (.inl rfl)
      · by_cases hk : ∃ i, k ∈ blk i
        · obtain ⟨i, hi⟩ := hk
          obtain ⟨w, hw⟩ := hxr i k hi
          have hcv : c (.inr k) = tAd F (t i) := hprod t i k hi
          rw [hcv, hb'v, hw, incM_vecMulVec, mul_vecMulVec_eq, mulVec_eq_tAd _ _ _ (hT.1 i)]
          ext r l
          simp [Matrix.vecMulVec_apply, smul_mul_assoc]
        · push_neg at hk
          have hcv : c (.inr k) = 1 := hone t k hk
          rw [hcv, one_smul]
          exact hfix k hk _ (.inr rfl)
    have hrep : ∀ w j, b'.repr (mat a * w) j = c j * b'.repr w j := by
      intro w j
      conv_lhs => rw [← b'.sum_repr w]
      rw [Matrix.mul_sum]
      simp_rw [Matrix.mul_smul, hc, smul_smul]
      rw [b'.repr_sum_self]
      exact mul_comm _ _
    have hw : ∀ v : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F), ∀ k,
        b'.repr (co.e.symm v) (.inl k) = v.1 k ∧ b'.repr (co.e.symm v) (.inr k) = v.2 k := by
      intro v k
      have := hco (co.e.symm v)
      rw [LinearEquiv.apply_symm_apply] at this
      exact ⟨(congrFun (congrArg Prod.fst this) k).symm, (congrFun (congrArg Prod.snd this) k).symm⟩
    constructor
    · rw [hco]
      ext k
      · simp only [hrep, (hw _ k).1, c, Sum.elim_inl, blkScale]
      · simp only [hrep, (hw _ k).2, mul_zero, Pi.zero_apply]
    · rw [hco]
      ext k
      · simp only [hrep, (hw _ k).1, mul_zero, Pi.zero_apply]
      · simp only [hrep, (hw _ k).2, c, Sum.elim_inr, blkScale]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormRightMulTranspose
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

namespace GlobalTheory.SympRight

theorem hTens_eq_trace' {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α S) (JB : Matrix β β S) (x y : Matrix α β S) :
    hTens c JA JB x y = Matrix.trace (xᵀ * JA * y.map c * JBᵀ) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem symp_mul_transpose_right : ∀ {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) (ξ : S)
    {α β β' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype β'] [DecidableEq β']
    (JA : Matrix α α S) (JB : Matrix β β S) (Q : Matrix β β' S) (z z' : Matrix α β' S),
    symp c ξ JA JB (z * Qᵀ) (z' * Qᵀ) = symp c ξ JA (Qᵀ * JB * Q.map c) z z' := by
  intro R S _ _ _ c ξ α β β' _ _ _ _ _ _ JA JB Q z z'
  simp only [symp, hTens_eq_trace']
  congr 2
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.transpose_map,
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm Q]
  simp only [Matrix.mul_assoc]

end GlobalTheory.SympRight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqIntegralSpanGenerato
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

namespace GlobalTheory.LatParam

theorem vecMulVec_sum_zsmul {E : Type} [Field E] {n d kx ky : ℕ} (ex : Fin kx → Fin n → E) (fy : Fin ky → Fin d → E)
    (c : Fin kx → ℤ) (c' : Fin ky → ℤ) :
    Matrix.vecMulVec (∑ i, c i • ex i) (∑ j, c' j • fy j) =
      ∑ m : Fin kx × Fin ky, (c m.1 * c' m.2) • Matrix.vecMulVec (ex m.1) (fy m.2) := by
  ext a b
  simp only [Matrix.vecMulVec_apply, Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply,
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [zsmul_eq_mul, Int.cast_mul]; ring

theorem latAtV_param : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (X : Spc F E n)
    (Y : Spc F E d), X.L.IsLattice E → Y.L.IsLattice E → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F,
    ∃ (M : Type) (_ : Fintype M) (g : M → Matrix (Fin n) (Fin d) E), ∀ γ,
      γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v ↔ ∃ a : M → v.adicCompletionIntegers F,
        γ = ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m) := by
  intro F E _ _ _ _ _ n d X Y hX hY v
  obtain ⟨kx, ex, hex⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (hX.fg.restrictScalars (R := ℤ))
  obtain ⟨ky, fy, hfy⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (hY.fg.restrictScalars (R := ℤ))
  let I : Matrix (Fin n) (Fin d) E →+ Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) :=
    (inclR (F := F) (E := E) (AF F)).toAddMonoidHom.mapMatrix
  have hI : ∀ J, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J = I J := fun J => rfl
  refine ⟨Fin kx × Fin ky, inferInstance, fun m => Matrix.vecMulVec (ex m.1) (fy m.2), fun γ => ⟨fun h => ?_, ?_⟩⟩
  · induction h using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hint, x, hx, y, hy, rfl⟩ := hz
      have hx' : x ∈ Submodule.span ℤ (Set.range ex) := by rw [hex]; exact hx
      have hy' : y ∈ Submodule.span ℤ (Set.range fy) := by rw [hfy]; exact hy
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx'
      obtain ⟨c', rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy'
      refine ⟨fun m => ⟨(c m.1 * c' m.2) • GlobalTheory.AdelicU.evFin F v a, zsmul_mem hint _⟩, ?_⟩
      have ha' := GlobalTheory.VacAny.eq_atPlace_of_at v a ha
      simp only [hI, vecMulVec_sum_zsmul, map_sum, map_zsmul, Finset.smul_sum, map_zsmul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← ha', smul_comm, smul_assoc]
    | zero => exact ⟨fun _ => 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by simp only [Pi.add_apply, AddMemClass.coe_add, map_add, add_smul, Finset.sum_add_distrib]⟩
    | neg x _ hx =>
      obtain ⟨a, rfl⟩ := hx
      exact ⟨-a, by simp only [Pi.neg_apply, NegMemClass.coe_neg, map_neg, neg_smul, Finset.sum_neg_distrib]⟩
  · rintro ⟨a, rfl⟩
    refine AddSubgroup.sum_mem _ fun m _ => AddSubgroup.subset_closure ?_
    refine ⟨_, GlobalTheory.VacAny.at_atPlace _, ?_, ex m.1, ?_, fy m.2, ?_, rfl⟩
    · rw [GlobalTheory.EmbChart.evFin_atPlace]; exact (a m).2
    · have : ex m.1 ∈ Submodule.span ℤ (Set.range ex) := Submodule.subset_span ⟨m.1, rfl⟩
      rw [hex] at this; exact this
    · have : fy m.2 ∈ Submodule.span ℤ (Set.range fy) := Submodule.subset_span ⟨m.2, rfl⟩
      rw [hfy] at this; exact this

end GlobalTheory.LatParam
end

