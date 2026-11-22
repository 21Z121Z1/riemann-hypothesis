import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesCoordDet
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace KLinesCoordDet

variable {K : Type} [Field K] {n m k : ℕ} (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K))
  (b : Fin m → Fin n → K) (c : Fin k → Fin n → K)

theorem toBlocks₁₁_eq (hb : ∀ i, B (Sum.inl i) = b i) :
    (B.toMatrix (Sum.elim b c)).toBlocks₁₁ = 1 := by
  ext i j
  rw [toBlocks₁₁, of_apply, Module.Basis.toMatrix_apply, Sum.elim_inl, ← hb, Module.Basis.repr_self,
    Finsupp.single_apply, one_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (fun e => h (Sum.inl_injective e).symm), if_neg h]

theorem toBlocks₂₁_eq (hb : ∀ i, B (Sum.inl i) = b i) :
    (B.toMatrix (Sum.elim b c)).toBlocks₂₁ = 0 := by
  ext i j
  rw [toBlocks₂₁, of_apply, Module.Basis.toMatrix_apply, Sum.elim_inl, ← hb, Module.Basis.repr_self,
    Finsupp.single_apply, Matrix.zero_apply, if_neg Sum.inl_ne_inr]

theorem det_eq (hb : ∀ i, B (Sum.inl i) = b i) :
    (B.toMatrix (Sum.elim b c)).det = (B.toMatrix (Sum.elim b c)).toBlocks₂₂.det := by
  set P := B.toMatrix (Sum.elim b c) with hPdef
  have hP : P = fromBlocks 1 P.toBlocks₁₂ 0 P.toBlocks₂₂ := by
    rw [← toBlocks₁₁_eq B b c hb, ← toBlocks₂₁_eq B b c hb, fromBlocks_toBlocks]
  conv_lhs => rw [hP]
  rw [det_fromBlocks_zero₂₁, det_one, one_mul]

theorem det_ne_zero (hli : LinearIndependent K (Sum.elim b c)) :
    (B.toMatrix (Sum.elim b c)).det ≠ 0 := by
  have hcard : Fintype.card (Fin m ⊕ Fin k) = Module.finrank K (Fin n → K) :=
    (Module.finrank_eq_card_basis B).symm
  let v := basisOfLinearIndependentOfCardEqFinrank' (Sum.elim b c) hli hcard
  have hv : (v : Fin m ⊕ Fin k → Fin n → K) = Sum.elim b c :=
    coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  have h := congrArg Matrix.det (Module.Basis.toMatrix_mul_toMatrix_flip B v)
  rw [det_mul, det_one, hv] at h
  exact left_ne_zero_of_mul_eq_one h

end KLinesCoordDet

theorem LinesCoordDet.proof : LinesCoordDet.Statement := by
  intro K _ n m k B b c hb hli
  exact ⟨KLinesCoordDet.det_eq B b c hb,
    KLinesCoordDet.det_eq B b c hb ▸ KLinesCoordDet.det_ne_zero B b c hli⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesCoordImage
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem LinesCoordImage.proof : LinesCoordImage.Statement := by
  intro K _ n m k B b c j
  funext l
  simp [coordProj, LinearMap.funLeft_apply, Module.Basis.equivFun_apply, Matrix.toBlocks₂₂,
    Module.Basis.toMatrix_apply, Matrix.mulVec, dotProduct, Pi.single_apply]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesDiagGram
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesDiagGram

theorem embVec_single {K : Type*} [Field K] (σ : K →+* ℂ) {n : ℕ} (x : Fin n) :
    embVec σ (Pi.single x 1 : Fin n → K) = Pi.single x 1 := by
  funext y
  simp only [embVec, Pi.single_apply]
  split_ifs <;> simp

end KLinesDiagGram

open KLinesDiagGram in

theorem LinesDiagGram.proof : LinesDiagGram.Statement := by
  intro K _ n d σ k τ hτ
  ext j j'
  simp only [gramAt, embVec_single, Matrix.diagonal_apply]
  rw [show (star (Pi.single (τ j) (1 : ℂ)) : Fin n → ℂ) = Pi.single (τ j) 1 by
    funext y; simp only [Pi.star_apply, Pi.single_apply]; split_ifs <;> simp]
  rw [single_dotProduct, one_mul, Matrix.mulVec_diagonal]
  simp only [Pi.single_apply, hτ.eq_iff]
  split_ifs with h
  · subst h; simp
  · simp

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesExtendBasis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesExtendBasis

theorem span_single_eq_top (K : Type) [Field K] (n : ℕ) :
    Submodule.span K (Set.range fun x : Fin n => (Pi.single x 1 : Fin n → K)) = ⊤ := by
  have h : (fun x : Fin n => (Pi.single x 1 : Fin n → K)) = ⇑(Pi.basisFun K (Fin n)) := by
    funext x
    simp
  rw [h]
  exact (Pi.basisFun K (Fin n)).span_eq

end KLinesExtendBasis

open KLinesExtendBasis in

theorem LinesExtendBasis.proof : LinesExtendBasis.Statement := by
  intro K _ n m k b hb hn
  set W : Submodule K (Fin n → K) := Submodule.span K (Set.range b) with hW
  let e : Fin n → (Fin n → K) := fun x => Pi.single x 1
  have hspan : Submodule.span K (Set.range (W.mkQ ∘ e)) = ⊤ := by
    rw [Set.range_comp, ← Submodule.map_span, span_single_eq_top, Submodule.map_top,
      Submodule.range_mkQ]
  obtain ⟨κ, a, ha, hsp, hli⟩ : ∃ (κ : Type) (a : κ → Fin n), Function.Injective a ∧
      Submodule.span K (Set.range ((W.mkQ ∘ e) ∘ a)) = Submodule.span K (Set.range (W.mkQ ∘ e)) ∧
      LinearIndependent K ((W.mkQ ∘ e) ∘ a) := exists_linearIndependent' K (W.mkQ ∘ e)
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  let B : Module.Basis κ K ((Fin n → K) ⧸ W) := Module.Basis.mk hli (by rw [hsp, hspan])
  have hcard : Fintype.card κ = k := by
    have h1 := W.finrank_quotient_add_finrank
    rw [Module.finrank_eq_card_basis B, hW, finrank_span_eq_card hb, Module.finrank_fin_fun,
      Fintype.card_fin] at h1
    omega
  let σ : Fin k ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ σ, ha.comp σ.injective, ?_⟩
  let f : Fin m → W := fun i => ⟨b i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hf : LinearIndependent K f := LinearIndependent.of_comp W.subtype hb
  have hg : LinearIndependent K (Submodule.Quotient.mk (p := W) ∘ fun j => e (a (σ j))) :=
    hli.comp σ σ.injective
  exact LinearIndependent.sumElim_of_quotient hf (fun j => e (a (σ j))) hg

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesFischer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix
open scoped ComplexOrder

namespace KLinesFischer

theorem toBlocks₂₁_eq {m k : Type*} {M : Matrix (m ⊕ k) (m ⊕ k) ℂ} (hM : M.IsHermitian) :
    M.toBlocks₂₁ = M.toBlocks₁₂ᴴ := by
  ext i j
  simp only [toBlocks₂₁, toBlocks₁₂, conjTranspose_apply, of_apply]
  exact (hM.apply (Sum.inr i) (Sum.inl j)).symm

end KLinesFischer

theorem LinesFischer.proof : LinesFischer.Statement := by
  intro m k _ _ _ _ M hM
  have hA : M.toBlocks₁₁.PosDef := hM.submatrix (e := (Sum.inl : m → m ⊕ k)) Sum.inl_injective
  have hApos : 0 < M.toBlocks₁₁.det.re := MCDet.re_det_pos hA
  have hdet0 : M.toBlocks₁₁.det ≠ 0 := fun h => by simp [h] at hApos
  let _ : Invertible M.toBlocks₁₁ := invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hdet0)
  have hMe : M = fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₁₂ᴴ M.toBlocks₂₂ := by
    rw [← KLinesFischer.toBlocks₂₁_eq hM.1]
    exact (fromBlocks_toBlocks M).symm
  have hS : (M.toBlocks₂₂ - M.toBlocks₁₂ᴴ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂).PosSemidef := by
    have h := hM.posSemidef
    rw [hMe] at h
    exact (PosDef.fromBlocks₁₁ _ _ hA).mp h
  have hdet : M.det = M.toBlocks₁₁.det *
      (M.toBlocks₂₂ - M.toBlocks₁₂ᴴ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂).det := by
    conv_lhs => rw [hMe]
    rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  have hmono : (M.toBlocks₂₂ - M.toBlocks₁₂ᴴ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂).det.re ≤
      M.toBlocks₂₂.det.re := by
    refine MCDet.re_det_mono hS ?_
    rw [sub_sub_cancel]
    exact hA.posSemidef.inv.conjTranspose_mul_mul_same _
  have him : M.toBlocks₁₁.det.im = 0 := by
    have h := congrArg Complex.im (MCDet.det_eq_ofReal_re hA.posSemidef)
    simpa using h
  rw [hdet, Complex.mul_re, him, zero_mul, sub_zero]
  exact mul_le_mul_of_nonneg_left hmono hApos.le

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexDet
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesGenIndexDet

theorem span_basis_isLattice {V : Type} [AddCommGroup V] [Module ℚ V] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℚ V) : Submodule.IsLattice ℚ (Submodule.span ℤ (Set.range b)) where
  fg := Submodule.fg_span (Set.finite_range b)
  span_eq_top := by rw [Submodule.span_span_of_tower, b.span_eq]

end KLinesGenIndexDet

open KLinesGenIndexDet in

theorem LinesGenIndexDet.proof (h1 : LinesLatticeBasis.Statement) : LinesGenIndexDet.Statement := by
  intro V _ _ _ ι _ _ bA bB A B hA hB
  set MA := Submodule.span ℤ (Set.range bA)
  set MB := Submodule.span ℤ (Set.range bB)
  have := span_basis_isLattice bA
  have := span_basis_isLattice bB
  obtain ⟨bE, hE⟩ := h1 V ι (Module.finrank_eq_card_basis bA).symm (MA ⊓ MB) inferInstance
  have hAB : A ⊓ B = AddSubgroup.closure (Set.range bE) := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, ← hE, hA, hB,
      ← Submodule.span_int_eq_addSubgroupClosure, ← Submodule.span_int_eq_addSubgroupClosure]
    rfl
  have hBA : B ⊓ A = AddSubgroup.closure (Set.range bE) := by rw [inf_comm, hAB]
  have e1 : ((B.relIndex A : ℕ) : ℚ) = |bA.det bE| := by
    rw [← AddSubgroup.inf_relIndex_right]
    exact AddSubgroup.relIndex_eq_abs_det _ _ inf_le_right bE bA hBA hA
  have e2 : ((A.relIndex B : ℕ) : ℚ) = |bB.det bE| := by
    rw [← AddSubgroup.inf_relIndex_right]
    exact AddSubgroup.relIndex_eq_abs_det _ _ inf_le_right bE bB hAB hB
  have hne : bB.det bE ≠ 0 := (bB.isUnit_det bE).ne_zero
  have key : (B.relIndex A : ℚ) / (A.relIndex B : ℚ) = |bA.det bB| := by
    rw [e1, e2, ← bA.det_mul_det bB bE, abs_mul, mul_div_assoc, div_self (abs_ne_zero.mpr hne),
      mul_one]
  unfold genIndex
  have := congrArg (fun q : ℚ => (q : ℝ)) key
  push_cast at this
  exact this

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexMono
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesGenIndexMono

theorem genIndex_of_le {G : Type*} [AddCommGroup G] {A A' : AddSubgroup G} (h : A ≤ A') :
    genIndex A' A = (A.relIndex A' : ℝ) := by
  unfold genIndex
  rw [AddSubgroup.relIndex_eq_one.mpr h, Nat.cast_one, div_one]

theorem genIndex_nonneg {G : Type*} [AddCommGroup G] (A B : AddSubgroup G) : 0 ≤ genIndex A B := by
  unfold genIndex
  positivity

end KLinesGenIndexMono

open KLinesGenIndexMono in

theorem LinesGenIndexMono.proof (h1 : LinesGenIndexTrans.Statement) : LinesGenIndexMono.Statement := by
  intro V _ _ _ A A' B hA hA' hB hle
  obtain ⟨hpos, heq⟩ := h1 V A' A B hA' hA hB
  have hle' : A.toAddSubgroup ≤ A'.toAddSubgroup := hle
  rw [← heq]
  rw [genIndex_of_le hle'] at hpos ⊢
  have hone : (1 : ℝ) ≤ (A.toAddSubgroup.relIndex A'.toAddSubgroup : ℝ) := by
    have : 0 < A.toAddSubgroup.relIndex A'.toAddSubgroup := by exact_mod_cast hpos
    exact_mod_cast this
  exact le_mul_of_one_le_left (genIndex_nonneg _ _) hone

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexPi
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesGenIndexPi

open AddSubgroup

variable {η : Type} {G : Type} [AddCommGroup G]

theorem index_pi_dep [Fintype η] {β : η → Type} [∀ i, AddCommGroup (β i)]
    (H : ∀ i, AddSubgroup (β i)) :
    (AddSubgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [AddSubgroup.index, ← Nat.card_pi]
  refine Nat.card_congr
    ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientAddGroup.leftRel_pi]

def piIncl (K : η → AddSubgroup G) : (∀ i, K i) →+ AddSubgroup.pi Set.univ K where
  toFun x := ⟨fun i => (x i : G), by simp [AddSubgroup.mem_pi]⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem piIncl_surjective (K : η → AddSubgroup G) : Function.Surjective (piIncl K) := by
  intro y
  refine ⟨fun i => ⟨(y : η → G) i, (AddSubgroup.mem_pi _).1 y.2 i (Set.mem_univ i)⟩, ?_⟩
  rfl

theorem relIndex_pi [Fintype η] (H K : η → AddSubgroup G) :
    (AddSubgroup.pi Set.univ H).relIndex (AddSubgroup.pi Set.univ K) =
      ∏ i, (H i).relIndex (K i) := by
  have hc : ((AddSubgroup.pi Set.univ H).addSubgroupOf (AddSubgroup.pi Set.univ K)).comap
      (piIncl K) = AddSubgroup.pi Set.univ fun i => (H i).addSubgroupOf (K i) := by
    ext x
    simp [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi, piIncl]
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_comap_of_surjective _ (piIncl_surjective K), hc, index_pi_dep]

end KLinesGenIndexPi

theorem LinesGenIndexPi.proof : LinesGenIndexPi.Statement := by
  intro η _ G _ A B
  unfold genIndex
  rw [KLinesGenIndexPi.relIndex_pi, KLinesGenIndexPi.relIndex_pi, Nat.cast_prod, Nat.cast_prod,
    ← Finset.prod_div_distrib]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexTrans
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesGenIndexTrans

theorem toAddSubgroup_span {V : Type} [AddCommGroup V] (s : Set V) :
    (Submodule.span ℤ s).toAddSubgroup = AddSubgroup.closure s :=
  Submodule.span_int_eq_addSubgroupClosure s

end KLinesGenIndexTrans

open KLinesGenIndexTrans in

theorem LinesGenIndexTrans.proof (h1 : LinesLatticeBasis.Statement)
    (h2 : LinesGenIndexDet.Statement) : LinesGenIndexTrans.Statement := by
  intro V _ _ _ A B C hA hB hC
  classical
  obtain ⟨bA, rfl⟩ := h1 V (Fin (Module.finrank ℚ V)) (Fintype.card_fin _) A hA
  obtain ⟨bB, rfl⟩ := h1 V (Fin (Module.finrank ℚ V)) (Fintype.card_fin _) B hB
  obtain ⟨bC, rfl⟩ := h1 V (Fin (Module.finrank ℚ V)) (Fintype.card_fin _) C hC
  have hAB := h2 V _ bA bB _ _ (toAddSubgroup_span _) (toAddSubgroup_span _)
  have hBC := h2 V _ bB bC _ _ (toAddSubgroup_span _) (toAddSubgroup_span _)
  have hAC := h2 V _ bA bC _ _ (toAddSubgroup_span _) (toAddSubgroup_span _)
  refine ⟨?_, ?_⟩
  · rw [hAB]
    have h0 : (bA.det bB : ℚ) ≠ 0 := (bA.isUnit_det bB).ne_zero
    positivity
  · rw [hAB, hBC, hAC, ← abs_mul, ← Rat.cast_mul, Module.Basis.det_mul_det]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGramChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace KLinesGramChange

noncomputable def colMatrix {K : Type*} [Field K] {n : ℕ} (σ : K →+* ℂ) {ι : Type*}
    (u : ι → Fin n → K) : Matrix (Fin n) ι ℂ :=
  Matrix.of fun j a => σ (u a j)

theorem gramAt_eq {K : Type*} [Field K] {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ)
    {ι : Type*} [Fintype ι] (u : ι → Fin n → K) :
    gramAt h σ u = (colMatrix σ u)ᴴ * h * colMatrix σ u := by
  ext a b
  simp only [gramAt, embVec, colMatrix, Matrix.mul_apply, dotProduct, mulVec,
    conjTranspose_apply, Matrix.of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem colMatrix_transform {K : Type*} [Field K] {n : ℕ} (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    (u : ι → Fin n → K) (P : Matrix ι ι K) :
    colMatrix σ (fun a => ∑ b, P b a • u b) = colMatrix σ u * P.map σ := by
  ext j a
  simp only [colMatrix, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

end KLinesGramChange

open KLinesGramChange in

theorem LinesGramChange.proof : LinesGramChange.Statement := by
  intro K _ n h σ ι _ u P
  rw [gramAt_eq, gramAt_eq, colMatrix_transform, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGramDetChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

theorem LinesGramDetChange.proof (h1 : LinesGramChange.Statement) :
    LinesGramDetChange.Statement := by
  intro K _ n h σ ι _ _ B u
  have hu : u = fun a => ∑ b, B.toMatrix u b a • B b := by
    funext a
    exact (B.sum_toMatrix_smul_self u a).symm
  have hg := h1 K n h σ ι (⇑B) (B.toMatrix u)
  rw [← hu] at hg
  rw [hg, det_mul, det_mul, det_conjTranspose, RingHom.map_det]
  simp only [RingHom.mapMatrix_apply]
  ring

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGramFischerBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix
open scoped ComplexOrder

theorem LinesGramFischerBound.proof (h1 : LinesGramPosDef.Statement)
    (h2 : LinesFischer.Statement) (h3 : LinesDiagGram.Statement) :
    LinesGramFischerBound.Statement := by
  intro K _ n m k d σ b τ hd hτ hli
  set t : Fin k → Fin n → K := fun j => Pi.single (τ j) 1 with ht
  set h : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun x => (d x : ℂ) with hh
  have hpos : h.PosDef := Matrix.PosDef.diagonal fun x => Complex.zero_lt_real.mpr (hd x)
  have hG := h1 K n h σ (Fin m ⊕ Fin k) (Sum.elim b t) hpos hli
  have hF := h2 (Fin m) (Fin k) _ hG
  have hB1 : (gramAt h σ (Sum.elim b t)).toBlocks₁₁ = gramAt h σ b := by
    ext i j; rfl
  have hB2 : (gramAt h σ (Sum.elim b t)).toBlocks₂₂ = gramAt h σ t := by
    ext i j; rfl
  have hD : gramAt h σ t = Matrix.diagonal fun j => (d (τ j) : ℂ) := h3 K n d σ k τ hτ
  rw [hB1, hB2, hD, Matrix.det_diagonal, ← Complex.ofReal_prod, Complex.ofReal_re] at hF
  exact hF

end GroundTheory.Heights₂.Heights
end

