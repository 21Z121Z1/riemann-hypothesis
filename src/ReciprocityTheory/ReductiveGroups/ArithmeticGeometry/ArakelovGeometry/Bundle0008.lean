import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0007

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CardPieceIrrelevantIdeal
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mem_multidegree_piece_iff {W : Ideal (MRing ι)} {a : K → ℕ} {y : MRing ι ⧸ W} :
    y ∈ mPiece W a ↔ ∃ h, IsMultiHomog h a ∧ Ideal.Quotient.mk W h = y := by
  unfold mPiece
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, (mem_mHom_iff _ _).1 hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, (mem_mHom_iff _ _).2 hh, rfl⟩

theorem quotient_mk_mul_congr_colon {F q : Ideal (MRing ι)} {f : MRing ι} (hq : ∀ g, g ∈ q ↔ g * f ∈ F)
    {g g' : MRing ι} (h : Ideal.Quotient.mk q g = Ideal.Quotient.mk q g') :
    Ideal.Quotient.mk F (g * f) = Ideal.Quotient.mk F (g' * f) := by
  rw [Ideal.Quotient.eq] at h ⊢
  rw [← sub_mul]
  exact (hq _).1 h

theorem card_piece_colon_exact {F q : Ideal (MRing ι)} (hF : IsMultiHomogIdeal F) {f : MRing ι} {c : K → ℕ}
    (hf : IsMultiHomog f c) (hq : ∀ g, g ∈ q ↔ g * f ∈ F) {a : K → ℕ} (hca : c ≤ a) :
    Nat.card (mPiece F a) =
      Nat.card (mPiece q (a - c)) * Nat.card (mPiece (F ⊔ Ideal.span {f}) a) := by
  have hle : F ≤ F ⊔ Ideal.span {f} := le_sup_left
  let ψ : mPiece F a →+ MRing ι ⧸ (F ⊔ Ideal.span {f}) :=
    (Ideal.Quotient.factor hle).toAddMonoidHom.comp (mPiece F a).subtype.toAddMonoidHom
  have hψ : ∀ y : mPiece F a, ψ y = Ideal.Quotient.factor hle y.1 := fun _ => rfl
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker
  have h2 : Nat.card (mPiece F a ⧸ ψ.ker) = Nat.card (mPiece (F ⊔ Ideal.span {f}) a) := by
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ψ).toEquiv]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    rw [AddMonoidHom.mem_range, mem_multidegree_piece_iff]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨h, hh, hx⟩ := mem_multidegree_piece_iff.1 x.2
      refine ⟨h, hh, ?_⟩
      rw [hψ, ← hx, Ideal.Quotient.factor_mk]
    · rintro ⟨h, hh, rfl⟩
      refine ⟨⟨Ideal.Quotient.mk F h, mem_multidegree_piece_iff.2 ⟨h, hh, rfl⟩⟩, ?_⟩
      rw [hψ, Ideal.Quotient.factor_mk]
  have h3 : Nat.card (mPiece q (a - c)) = Nat.card ψ.ker := by
    let g₀ : MRing ι ⧸ q → MRing ι := fun x => (Ideal.Quotient.mk_surjective x).choose
    have hg₀ : ∀ x, Ideal.Quotient.mk q (g₀ x) = x := fun x =>
      (Ideal.Quotient.mk_surjective x).choose_spec
    have hmem1 : ∀ x : mPiece q (a - c), Ideal.Quotient.mk F (g₀ x.1 * f) ∈ mPiece F a := by
      intro x
      obtain ⟨g, hg, hgx⟩ := mem_multidegree_piece_iff.1 x.2
      refine mem_multidegree_piece_iff.2 ⟨g * f, ?_, quotient_mk_mul_congr_colon hq (by rw [hg₀, hgx])⟩
      have := isMultiHomog_mul' hg hf
      rwa [tsub_add_cancel_of_le hca] at this
    have hmem2 : ∀ x : mPiece q (a - c), (⟨_, hmem1 x⟩ : mPiece F a) ∈ ψ.ker := by
      intro x
      rw [AddMonoidHom.mem_ker, hψ]
      show Ideal.Quotient.factor hle (Ideal.Quotient.mk F (g₀ x.1 * f)) = 0
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f))
    refine Nat.card_eq_of_bijective (fun x => ⟨⟨_, hmem1 x⟩, hmem2 x⟩)
      ⟨fun x y hxy => ?_, fun z => ?_⟩
    · have e : Ideal.Quotient.mk F (g₀ x.1 * f) = Ideal.Quotient.mk F (g₀ y.1 * f) :=
        congrArg (fun z : ψ.ker => (z.1.1 : MRing ι ⧸ F)) hxy
      rw [Ideal.Quotient.eq, ← sub_mul, ← hq] at e
      apply Subtype.ext
      rw [← hg₀ x.1, ← hg₀ y.1]
      exact Ideal.Quotient.eq.2 e
    · obtain ⟨⟨y, hy⟩, hz⟩ := z
      obtain ⟨h, hh, rfl⟩ := mem_multidegree_piece_iff.1 hy
      rw [AddMonoidHom.mem_ker, hψ] at hz
      change Ideal.Quotient.factor hle (Ideal.Quotient.mk F h) = 0 at hz
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, Submodule.mem_sup] at hz
      obtain ⟨u, hu, v, hv, huv⟩ := hz
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 hv
      have hx : Ideal.Quotient.mk q (i2comp (a - c) g) ∈ mPiece q (a - c) :=
        mem_multidegree_piece_iff.2 ⟨_, isMultiHomog_i2comp _ _, rfl⟩
      refine ⟨⟨_, hx⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      show Ideal.Quotient.mk F (g₀ (Ideal.Quotient.mk q (i2comp (a - c) g)) * f) =
        Ideal.Quotient.mk F h
      rw [quotient_mk_mul_congr_colon hq (hg₀ _)]
      have e : h = i2comp a u + i2comp (a - c) g * f := by
        rw [← i2comp_self hh, ← huv, i2comp_add, i2comp_mul_right hf, if_pos hca]
      rw [e, Ideal.Quotient.eq]
      have e2 : i2comp (a - c) g * f - (i2comp a u + i2comp (a - c) g * f) = -i2comp a u := by ring
      rw [e2]
      exact neg_mem (i2comp_mem hF a hu)
  rw [h1, h2, ← h3, mul_comm]

theorem card_piece_top_ideal (a : K → ℕ) : Nat.card (mPiece (⊤ : Ideal (MRing ι)) a) = 1 := by
  haveI : Subsingleton (MRing ι ⧸ (⊤ : Ideal (MRing ι))) := Ideal.Quotient.subsingleton_iff.2 rfl
  exact Nat.card_of_subsingleton (0 : mPiece (⊤ : Ideal (MRing ι)) a)

theorem card_piece_of_filtration : ∀ (N : ℕ) (F : Fin (N + 1) → Ideal (MRing ι)) (f : Fin N → MRing ι)
    (c : Fin N → K → ℕ) (q : Fin N → Ideal (MRing ι)), IsMultiHomogIdeal (F 0) →
    F (Fin.last N) = ⊤ →
    (∀ j, IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc) →
    ∀ a : K → ℕ, (∀ j, c j ≤ a) →
      Nat.card (mPiece (F 0) a) = ∏ j, Nat.card (mPiece (q j) (a - c j))
  | 0, F, f, c, q, _, hl, _, a, _ => by
    have : F 0 = ⊤ := hl
    rw [Finset.univ_eq_empty, Finset.prod_empty, this, card_piece_top_ideal]
  | N + 1, F, f, c, q, h0, hl, hs, a, ha => by
    obtain ⟨hf0, hF1, hq0⟩ := hs 0
    rw [Fin.castSucc_zero] at hF1 hq0
    have e1 := card_piece_colon_exact h0 hf0 hq0 (ha 0)
    rw [← hF1] at e1
    have h0' : IsMultiHomogIdeal (F (Fin.succ 0)) := by
      rw [hF1]
      exact isMultiHomogIdeal_sup_span h0 hf0
    have ih := card_piece_of_filtration N (fun i => F i.succ) (fun j => f j.succ) (fun j => c j.succ)
      (fun j => q j.succ) h0' (by simp only [Fin.succ_last]; exact hl)
      (fun j => by
        obtain ⟨x1, x2, x3⟩ := hs j.succ
        refine ⟨x1, ?_, ?_⟩
        · simp only [Fin.succ_castSucc] at x2 ⊢
          exact x2
        · simpa only [Fin.succ_castSucc] using x3) a (fun j => ha j.succ)
    rw [Fin.prod_univ_succ, e1]
    congr 1

theorem card_piece_irrelevant_ideal {q : Ideal (MRing ι)} {k : K} (hk : ∀ i, (X ⟨k, i⟩ : MRing ι) ∈ q)
    {a : K → ℕ} (ha : 1 ≤ a k) : Nat.card (mPiece q a) = 1 := by
  have key : ∀ y ∈ mPiece q a, y = 0 := by
    intro y hy
    obtain ⟨h, hh, rfl⟩ := mem_multidegree_piece_iff.1 hy
    rw [Ideal.Quotient.eq_zero_iff_mem, h.as_sum]
    refine Ideal.sum_mem _ fun m hm => ?_
    have hmk : i2bdeg m k = a k :=
      congrFun ((isMultiHomog_iff_coeff h a).1 hh m (mem_support_iff.1 hm)) k
    have : ∃ i, m ⟨k, i⟩ ≠ 0 := by
      by_contra hne
      push_neg at hne
      have h0 : i2bdeg m k = 0 := show ∑ i, m ⟨k, i⟩ = 0 from Finset.sum_eq_zero fun i _ => hne i
      rw [h0] at hmk
      rw [← hmk] at ha
      exact absurd ha (by norm_num)
    obtain ⟨i, hi⟩ := this
    have hle : Finsupp.single (⟨k, i⟩ : Σ k, ι k) 1 ≤ m :=
      Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi)
    have e : monomial m (coeff m h) =
        X ⟨k, i⟩ * monomial (m - Finsupp.single (⟨k, i⟩ : Σ k, ι k) 1) (coeff m h) := by
      rw [X, monomial_mul, one_mul, add_tsub_cancel_of_le hle]
    rw [e]
    exact Ideal.mul_mem_right _ _ (hk i)
  haveI : Subsingleton (mPiece q a) :=
    ⟨fun x y => Subtype.ext ((key _ x.2).trans (key _ y.2).symm)⟩
  exact Nat.card_of_subsingleton (0 : mPiece q a)

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ComplexHessianTransposeIsHermitian
section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Complex Filter Topology Finset Matrix
open scoped ComplexOrder

section

variable {D : ℕ}

theorem mixedDiscriminant_constant (A : Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun _ => A) = A.det := by
  show (1 / (D.factorial : ℂ)) * ∑ S : Finset (Fin D), (-1) ^ (D - S.card) * (∑ _k ∈ S, A).det = A.det
  have h1 : ∀ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (∑ _k ∈ S, A).det =
      ((-1 : ℂ) ^ (D - S.card) * (S.card : ℂ) ^ D) * A.det := by
    intro S
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, Matrix.det_smul, Fintype.card_fin]
    ring
  simp_rw [h1]
  rw [← Finset.sum_mul]
  have h2 : ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (S.card : ℂ) ^ D = D.factorial := by
    have h3 := congrFun (fwdDiff_iter_eq_factorial (R := ℂ) (n := D)) 0
    rw [fwdDiff_iter_eq_sum_shift] at h3
    rw [← Finset.powerset_univ,
      Finset.sum_powerset_apply_card (fun k => (-1 : ℂ) ^ (D - k) * (k : ℂ) ^ D),
      Finset.card_univ, Fintype.card_fin]
    simp only [Pi.natCast_apply, zero_add, nsmul_eq_mul, mul_one, zsmul_eq_mul] at h3
    rw [← h3]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [h2]
  have : (D.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero D)
  field_simp

theorem complexHessian_transpose_isHermitian {φ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h : IsSymmSndFDerivAt ℝ φ y) (c : ℝ) :
    ((c : ℂ) • (cxHessian φ y).transpose).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.smul_apply, cxHessian,
    smul_eq_mul]
  rw [h (Pi.single j 1) (Pi.single i 1), h (I • Pi.single j 1) (I • Pi.single i 1),
    h (Pi.single j 1) (I • Pi.single i 1), h (I • Pi.single j 1) (Pi.single i 1)]
  apply Complex.ext <;> simp

theorem im_hermitian_quadraticForm {n : Type*} [Fintype n] {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (w : n → ℂ) : (star w ⬝ᵥ M *ᵥ w).im = 0 := by
  have h := hM.im_star_dotProduct_mulVec_self w
  simpa using h

theorem complexHessian_posSemidef {φ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h : IsSymmSndFDerivAt ℝ φ y)
    {c : ℝ} (hc : 0 ≤ c) (hL : ∀ w, 0 ≤ leviForm φ y w) :
    ((c : ℂ) • (cxHessian φ y).transpose).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (complexHessian_transpose_isHermitian h c) fun w => ?_
  rw [Complex.nonneg_iff]
  refine ⟨?_, (im_hermitian_quadraticForm (complexHessian_transpose_isHermitian h c) w).symm⟩
  have e : (star w ⬝ᵥ ((c : ℂ) • (cxHessian φ y).transpose) *ᵥ w) =
      (c : ℂ) * ∑ i, ∑ j, starRingEnd ℂ (w i) * cxHessian φ y j i * w j := by
    simp only [dotProduct, mulVec, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul,
      Pi.star_apply, Finset.mul_sum, Complex.star_def]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e, Complex.re_ofReal_mul, ← leviForm_eq_complexHessian]
  exact mul_nonneg hc (hL w)

end

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsHomogeneousGrL
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

attribute [local instance 2000] lexDecEq
attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def lexDeg (a : K → ℕ) : Lex (Fin (Fintype.card K) → ℕ) := toLex (a ∘ (Fintype.equivFin K).symm)

theorem lexDeg_add (a b : K → ℕ) : lexDeg (a + b) = lexDeg a + lexDeg b := rfl

variable (ι) in

abbrev grL : Lex (Fin (Fintype.card K) → ℕ) → Submodule ℤ (MRing ι) :=
  weightedHomogeneousSubmodule ℤ (lexW (ι := ι) (Fintype.equivFin K))

theorem mem_grL_iff (f : MRing ι) (a : K → ℕ) : f ∈ grL ι (lexDeg a) ↔ IsMultiHomog f a := by
  constructor
  · intro h
    have := isMultiHomog_of_mem_lex _ h
    convert this using 1
    funext k
    simp [lexDeg]
  · exact mem_lex_of_isMultiHomog _

theorem mHom_eq (a : K → ℕ) : mHom ι a = grL ι (lexDeg a) := by
  rw [mHom]
  have : {s : MRing ι | IsMultiHomog s a} = (grL ι (lexDeg a) : Set (MRing ι)) := by
    ext s
    exact (mem_grL_iff s a).symm
  rw [this, Submodule.span_eq]

theorem mem_mHom_iff (f : MRing ι) (a : K → ℕ) : f ∈ mHom ι a ↔ IsMultiHomog f a := by
  rw [mHom_eq, mem_grL_iff]

theorem isHomogeneous_grL {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) :
    J.IsHomogeneous (grL ι) := (isHomogeneous_lex_iff _ J).mpr hJ

def pieceMap (J : Ideal (MRing ι)) (a : K → ℕ) : mHom ι a →ₗ[ℤ] MRing ι ⧸ J :=
  (Ideal.Quotient.mkₐ ℤ J).toLinearMap ∘ₗ (mHom ι a).subtype

theorem range_pieceMap (J : Ideal (MRing ι)) (a : K → ℕ) :
    LinearMap.range (pieceMap J a) = mPiece J a := by
  rw [pieceMap, LinearMap.range_comp, Submodule.range_subtype]
  rfl

theorem mem_ker_pieceMap (J : Ideal (MRing ι)) (a : K → ℕ) (x : mHom ι a) :
    x ∈ LinearMap.ker (pieceMap J a) ↔ (x : MRing ι) ∈ J := by
  simp [pieceMap, Ideal.Quotient.eq_zero_iff_mem]

theorem card_mPiece_eq (J : Ideal (MRing ι)) (a : K → ℕ) :
    Nat.card (mPiece J a) = Nat.card (mHom ι a ⧸ LinearMap.ker (pieceMap J a)) := by
  rw [← range_pieceMap]
  exact Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv.symm

theorem card_quot_chain {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] (A B : Submodule R V)
    (h : A ≤ B) :
    Nat.card (V ⧸ A) = Nat.card (V ⧸ B) * Nat.card (B ⧸ A.comap B.subtype) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (B.map A.mkQ)
  have e1 : Nat.card ((V ⧸ A) ⧸ B.map A.mkQ) = Nat.card (V ⧸ B) :=
    Nat.card_congr (Submodule.quotientQuotientEquivQuotient A B h).toEquiv
  let φ : B →ₗ[R] V ⧸ A := A.mkQ ∘ₗ B.subtype
  have hr : LinearMap.range φ = B.map A.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : LinearMap.ker φ = A.comap B.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have e2 : Nat.card (B.map A.mkQ) = Nat.card (B ⧸ A.comap B.subtype) := by
    rw [← hr, ← hk]
    exact Nat.card_congr (LinearMap.quotKerEquivRange φ).toEquiv.symm
  rw [h1, e1, e2]
  ring

theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  rw [← mem_grL_iff] at hf hg ⊢
  rw [lexDeg_add]
  exact SetLike.GradedMul.mul_mem hf hg

theorem card_mPiece_step {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) {f : MRing ι} {c : K → ℕ}
    (hf : IsMultiHomog f c) {q : Ideal (MRing ι)} (hq : ∀ g, g ∈ q ↔ g * f ∈ J) {a : K → ℕ}
    (hca : ∀ k, c k ≤ a k) :
    Nat.card (mPiece J a) = Nat.card (mPiece (J ⊔ Ideal.span {f}) a) * Nat.card (mPiece q (a - c)) := by
  classical
  set J' := J ⊔ Ideal.span {f}
  have hJJ' : J ≤ J' := le_sup_left
  set A := LinearMap.ker (pieceMap J a)
  set B := LinearMap.ker (pieceMap J' a)
  have hAB : A ≤ B := fun x hx => by
    rw [mem_ker_pieceMap] at hx ⊢
    exact hJJ' hx
  rw [card_mPiece_eq, card_mPiece_eq, card_mPiece_eq, card_quot_chain A B hAB]
  congr 1
  have hac : a - c + c = a := funext fun k => Nat.sub_add_cancel (hca k)
  have hmul : ∀ g : mHom ι (a - c), (g : MRing ι) * f ∈ mHom ι a := fun g => by
    rw [mem_mHom_iff]
    have := isMultiHomog_mul ((mem_mHom_iff _ _).mp g.2) hf
    rwa [hac] at this
  let χ' : mHom ι (a - c) →ₗ[ℤ] B :=
    { toFun := fun g => ⟨⟨(g : MRing ι) * f, hmul g⟩, by
        rw [mem_ker_pieceMap]
        exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f))⟩
      map_add' := fun g h => by ext; simp [add_mul]
      map_smul' := fun r g => by ext; simp [mul_assoc] }
  let χ := (A.comap B.subtype).mkQ ∘ₗ χ'
  have hsurj : Function.Surjective χ := by
    intro z
    obtain ⟨⟨⟨x, hxa⟩, hxB⟩, rfl⟩ := Submodule.mkQ_surjective _ z
    have hxJ' : x ∈ J' := (mem_ker_pieceMap J' a ⟨x, hxa⟩).mp hxB
    obtain ⟨j, hj, y, hy, hjx⟩ := Submodule.mem_sup.mp hxJ'
    obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have hf' : f ∈ grL ι (lexDeg c) := (mem_grL_iff f c).mpr hf
    set g := (DirectSum.decompose (grL ι) h (lexDeg (a - c)) : MRing ι)
    have hg : g ∈ mHom ι (a - c) := by
      rw [mHom_eq]
      exact SetLike.coe_mem _
    refine ⟨⟨g, hg⟩, ?_⟩
    have hx : x = (DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) + g * f := by
      have h1 : x ∈ grL ι (lexDeg a) := by rw [← mHom_eq]; exact hxa
      conv_lhs => rw [← DirectSum.decompose_of_mem_same (grL ι) h1, ← hjx]
      rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
      congr 1
      rw [← hac, lexDeg_add, DirectSum.coe_decompose_mul_add_of_right_mem (grL ι) hf']
    have hjc : (DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) ∈ J := isHomogeneous_grL hJ _ hj
    show (A.comap B.subtype).mkQ (χ' ⟨g, hg⟩) = (A.comap B.subtype).mkQ ⟨⟨x, hxa⟩, hxB⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap,
      Submodule.coe_subtype, mem_ker_pieceMap]
    have : (((χ' ⟨g, hg⟩ - ⟨⟨x, hxa⟩, hxB⟩ : B) : mHom ι a) : MRing ι) = g * f - x := rfl
    rw [this, hx, show g * f - ((DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) + g * f) =
      -(DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) by ring]
    exact J.neg_mem hjc
  have hker : LinearMap.ker χ = LinearMap.ker (pieceMap q (a - c)) := by
    ext g
    rw [LinearMap.mem_ker, mem_ker_pieceMap, hq]
    show (A.comap B.subtype).mkQ (χ' g) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
      mem_ker_pieceMap]
    rfl
  rw [← hker]
  exact Nat.card_congr (LinearMap.quotKerEquivOfSurjective χ hsurj).toEquiv.symm

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

