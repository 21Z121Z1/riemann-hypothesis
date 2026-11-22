import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ExpToSat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0526
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1253
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0588
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LeOfAddNegOne
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.CuspRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Tail.PExp.DlB

theorem pair_sum (N : ℕ) (x : Fin N → ℤ) :
    ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), (x i - x j) =
      ∑ i : Fin N, ((N : ℤ) - 1 - 2 * (i : ℕ)) * x i := by
  have hswap : ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), x j =
      ∑ j : Fin N, ∑ i ∈ Finset.univ.filter (fun i => i < j), x j :=
    Finset.sum_comm' (fun i j => by simp)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hswap]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc1 : (Finset.univ.filter (fun j => i < j)).card = N - 1 - i := by
    rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  have hc2 : (Finset.univ.filter (fun j => j < i)).card = i := by
    rw [Finset.filter_gt_eq_Iio, Fin.card_Iio]
  rw [hc1, hc2]
  have hi := i.isLt
  have h : (((N - 1 - (i : ℕ) : ℕ)) : ℤ) = (N : ℤ) - 1 - (i : ℕ) := by omega
  rw [h]
  ring

theorem prod_zpow' (a : ℝ) (ha : a ≠ 0) {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ ha, ih]

theorem le_ofAdd_neg_one (b : WithZero (Multiplicative ℤ)) (h : b < 1) :
    b ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  induction b using WithZero.recZeroCoe with
  | zero => exact zero_le
  | coe a =>
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at h
    rw [WithZero.coe_le_coe]
    have h' : Multiplicative.toAdd a < 0 := h
    show Multiplicative.toAdd a ≤ -1
    omega

theorem unif_of_ordL (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (h : ordL (ϖ : w.adicCompletion E) = 1) :
    valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) = uniformizer (w.adicCompletion E) := by
  set K := w.adicCompletion E
  have hv : Valued.v (ϖ : K) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    unfold ordL at h
    split_ifs at h with h0
    · exact absurd h (by norm_num)
    rw [← WithZero.coe_unzero h0]
    congr 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    omega
  have key : ∀ a b : K, valuation K a ≤ valuation K b ↔ Valued.v a ≤ Valued.v b := fun a b =>
    (Valuation.Compatible.vle_iff_le (v := valuation K) a b).symm.trans Iff.rfl
  have hlt : ∀ a : K, valuation K a < 1 ↔ Valued.v a < 1 := fun a => by
    rw [← map_one (valuation K), ← map_one (Valued.v : Valuation K (WithZero (Multiplicative ℤ))),
      lt_iff_not_ge, lt_iff_not_ge, key]
  apply le_antisymm
  · rw [le_uniformizer_iff, hlt, hv, ← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero,
      Multiplicative.ofAdd_lt]
    norm_num
  · obtain ⟨a, ha⟩ := valuation_surjective (uniformizer K)
    have h1 : valuation K a < 1 := ha ▸ uniformizer_lt_one
    rw [← ha, key, hv]
    exact le_ofAdd_neg_one _ ((hlt a).1 h1)

end PositivityTheory.Rg.BcB.F.Tail.PExp.DlB

namespace PositivityTheory.Rg.BcB.F.Tail.PExp

open DlB in
theorem dlBridge' : DlBridge := by
  intro E _ _ _ w ϖ hord
  have hu := unif_of_ordL E w ϖ hord
  refine ⟨hu, fun N x => ?_⟩
  set q : ℝ := ((qV E w : ℕ) : ℝ) with hq
  have hn : nabs (w.adicCompletion E) ϖ = q⁻¹ := by
    rw [GlobalTheory.GLDoubling.nabs_unif hu, GlobalTheory.T.residue_card_eq_abs_norm]
    rfl
  have hqpos : 0 < q := by
    have := nabs_pos' (w.adicCompletion E) ϖ
    rw [hn] at this
    exact inv_pos.1 this
  have hz : ∀ n : ℤ, nabs (w.adicCompletion E) (ϖ ^ n) = q ^ (-n) := by
    intro n
    have h2 := hn
    unfold nabs at h2 ⊢
    rw [map_zpow, NNReal.coe_zpow, h2, _root_.inv_zpow']
  set S : ℤ := ∑ i : Fin N, ((N : ℤ) - 1 - 2 * (i : ℕ)) * x i with hS
  have hdB : deltaB (fun i => ϖ ^ x i) = q ^ (-S) := by
    unfold deltaB
    have e1 : ∀ i j : Fin N, nabs (w.adicCompletion E) (ϖ ^ x i / ϖ ^ x j) = q ^ (-(x i - x j)) := fun i j => by
      rw [show ϖ ^ x i / ϖ ^ x j = ϖ ^ (x i - x j) by rw [_root_.zpow_sub, div_eq_mul_inv], hz]
    simp only [e1]
    rw [Finset.prod_congr rfl fun i _ => prod_zpow' q hqpos.ne' _ _, prod_zpow' q hqpos.ne',
      hS, ← pair_sum]
    congr 1
    simp only [Finset.sum_neg_distrib]
  have hdH : (deltaHalf (w.adicCompletion E) (fun _ : Fin N => Unit) (leviTorus (w.adicCompletion E) (Fin N) fun i => ϖ ^ x i) : ℂ) =
      ((√(deltaB (fun i => ϖ ^ x i)) : ℝ) : ℂ) := by
    rw [val_deltaHalf, deltaB_eq_modulus]
  rw [hdH, hdB]
  set r : ℝ := √q with hr
  have hrpos : 0 < r := Real.sqrt_pos.2 hqpos
  have e : q ^ (-S) = (r ^ (-S)) ^ 2 := by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hr, Real.sq_sqrt hqpos.le]
  have hqh : GlobalTheory.BCT.qh w = (r : ℂ) := rfl
  rw [hqh, e, Real.sqrt_sq (zpow_nonneg hrpos.le _), ← Complex.ofReal_mul, ← Complex.ofReal_zpow]
  congr 1
  rw [← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_neg, ← zpow_add₀ hrpos.ne']
  congr 1
  push_cast
  ring

end PositivityTheory.Rg.BcB.F.Tail.PExp

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ParabolicFunctionLeftInvariant
section
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.Tail.B

theorem hint_mul_right_comm {H : Type} [CommGroup H] (K : Subgroup H) (u : H → ℂ) (t : H) :
    hint K (fun X => u (X * t)) = hint K u := by
  have hr : rStab (fun X => u (X * t)) = rStab u := by
    ext k
    show (∀ x, u (x * k * t) = u (x * t)) ↔ ∀ x, u (x * k) = u x
    constructor
    · intro hk x
      have := hk (x * t⁻¹)
      rwa [mul_right_comm (x * t⁻¹) k t, inv_mul_cancel_right] at this
    · intro hk x
      rw [mul_right_comm x k t, hk]
  unfold hint
  rw [hr]
  congr 1
  set S := rStab u ⊓ K with hS
  have key : ∀ q : H ⧸ S, u ((MulAction.toPerm t q : H ⧸ S).out) = u (q.out * t) := by
    intro q
    have h1 : (MulAction.toPerm t q : H ⧸ S) = ((t * q.out : H) : H ⧸ S) := by
      rw [MulAction.toPerm_apply]
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S (t * q.out)
    rw [h1, hs, (Subgroup.mem_inf.1 s.2).1, mul_comm]
  calc ∑ᶠ q : H ⧸ S, u (q.out * t) = ∑ᶠ q : H ⧸ S, u ((MulAction.toPerm t q : H ⧸ S).out) :=
        finsum_congr fun q => (key q).symm
    _ = ∑ᶠ q : H ⧸ S, u q.out := finsum_comp_equiv (MulAction.toPerm t) (f := fun q : H ⧸ S => u q.out)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_mul {n a b : ℕ} (h : a + b = n) (w : Pl E) (m m' : GLw a w × GLw b w)
    (X X' : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    blk h w m X * blk h w m' X' = blk h w (m * m') (X' + (m'.1⁻¹).val * X * m'.2.val) := by
  apply Units.ext
  rw [Units.val_mul, CtLevel.blk_val, CtLevel.blk_val, CtLevel.blk_val, reindex_apply, reindex_apply,
    reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
  have e : (m'.1.val) * (m'.1⁻¹).val = 1 := Units.mul_inv _
  have key : m.1.val * (m'.1.val * X') + m.1.val * X * m'.2.val =
      (m * m').1.val * (X' + (m'.1⁻¹).val * X * m'.2.val) := by
    rw [Prod.fst_mul, Units.val_mul]
    simp only [Matrix.mul_add, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc m'.1.val (m'.1⁻¹).val, e, Matrix.one_mul]
  rw [key]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Prod.fst_mul, Prod.snd_mul, Units.val_mul]

theorem blk_entries {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (∀ i j, (blk h w m X).val (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j)) = m.1.val i j) ∧
      ∀ i j, (blk h w m X).val (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j)) = m.2.val i j := by
  constructor <;> intro i j <;>
    rw [CtLevel.blk_val, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply] <;> rfl

theorem blocks_of_blk_mem {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) (hk : blk h w m X ∈ GlobalTheory.LFun.KGL w n) :
    m.1 ∈ GlobalTheory.LFun.KGL w a ∧ m.2 ∈ GlobalTheory.LFun.KGL w b := by
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hk
  rw [CtLevel.blk_inv] at h2
  refine ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩,
    GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · have := h1 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j))
    rwa [(blk_entries h w m X).1] at this
  · have := h2 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j))
    rwa [(blk_entries h w _ _).1] at this
  · have := h1 (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j))
    rwa [(blk_entries h w m X).2] at this
  · have := h2 (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j))
    rwa [(blk_entries h w _ _).2] at this

theorem parabolic_function_left_invariant {n a b : ℕ} (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)) (f : GLw n w → ℂ)
    (hf : ∀ k ∈ K', ∀ g, f (k * g) = f g) (x y : GLw n w) (mq : GLw a w × GLw b w) (hmq1 : mq.1 ∈ GlobalTheory.LFun.KGL w a)
    (hmq2 : mq.2 ∈ GlobalTheory.LFun.KGL w b) (Z : Matrix (Fin a) (Fin b) (w.adicCompletion E)) (k' : GLw n w) (hk' : k' ∈ K')
    (m : GLw a w × GLw b w) : phi3 h w f (blk h w mq Z * x * k') y m = phi3 h w f x y (mq⁻¹ * m) := by
  have hab : absHalf w ((mq⁻¹ * m).1.val.det ^ b / (mq⁻¹ * m).2.val.det ^ a) =
      absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) :=
    (absHalf_blockDet_KGL_invariant E a b w m mq⁻¹ (inv_mem hmq1) (inv_mem hmq2)).1
  set T : Matrix (Fin a) (Fin b) (w.adicCompletion E) :=
    (m.1⁻¹).val * (-(mq.1.val * Z * (mq.2⁻¹).val)) * m.2.val with hT
  have hstep : ∀ X : Matrix (Fin a) (Fin b) (w.adicCompletion E),
      f ((blk h w mq Z * x * k')⁻¹ * blk h w m X * y) = f (x⁻¹ * blk h w (mq⁻¹ * m) (X + T) * y) := by
    intro X
    have e1 : (blk h w mq Z * x * k')⁻¹ * blk h w m X * y =
        k'⁻¹ * (x⁻¹ * ((blk h w mq Z)⁻¹ * blk h w m X) * y) := by group
    rw [e1, hf _ (inv_mem hk'), CtLevel.blk_inv, blk_mul]
  unfold phi3
  rw [hab]
  congr 1
  simp_rw [hstep]
  exact hint_mul_right_comm (intMat a b w)
    (fun Y => f (x⁻¹ * blk h w (mq⁻¹ * m) (Multiplicative.toAdd Y) * y)) (Multiplicative.ofAdd T)

theorem parab_blk {n a b : ℕ} (h : a + b = n) (w : Pl E) (p : GLw n w)
    (hp : p ∈ GlobalTheory.SmGL.parab (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))) :
    ∃ Z, p = blk h w ((GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm
      (GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) ⟨p, hp⟩)) Z := by
  set A := (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm
    (GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) ⟨p, hp⟩) with hA
  refine ⟨(A.1⁻¹).val * (Matrix.of fun i j => p.val (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inr j))), ?_⟩
  apply Units.ext
  rw [CtLevel.blk_val, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  refine Matrix.ext fun i j => ?_
  obtain ⟨s, rfl⟩ := (CtLevel.blkEq h).surjective i
  obtain ⟨t, rfl⟩ := (CtLevel.blkEq h).surjective j
  rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases s with s | s <;> rcases t with t | t
  · rfl
  · rfl
  · have h1 : GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) (CtLevel.blkEq h (Sum.inr s)) = true :=
      GlobalTheory.SmGL.blk_apply (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) true s
    have h2 : GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) (CtLevel.blkEq h (Sum.inl t)) = false :=
      GlobalTheory.SmGL.blk_apply (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) false t
    exact GlobalTheory.SmGL.mem_parab.1 hp (CtLevel.blkEq h (Sum.inr s)) (CtLevel.blkEq h (Sum.inl t))
      (by rw [h1, h2]; decide)
  · rfl

theorem deltaHalf_int {a b : ℕ} (w : Pl E) (m : GLw a w × GLw b w) (h1 : m.1 ∈ GlobalTheory.LFun.KGL w a)
    (h2 : m.2 ∈ GlobalTheory.LFun.KGL w b) :
    (GlobalTheory.SmGL.deltaHalf (w.adicCompletion E) (GlobalTheory.SmGL.Two (Fin a) (Fin b))
      (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m) : ℂ) = 1 := by
  have hg : ∀ x : Bool, (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m) x ∈
      GlobalTheory.SplitWeil.KO (w.adicCompletion E) (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) := by
    intro x
    cases x
    · show m.1 ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin a)
      rw [← GlobalTheory.CompanionTheory.IwLevels.KGL_eq_KO]; exact h1
    · show m.2 ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin b)
      rw [← GlobalTheory.CompanionTheory.IwLevels.KGL_eq_KO]; exact h2
  rw [GlobalTheory.SatInd.deltaHalf_eq_one hg, Units.val_one]

end PositivityTheory.Rg.BcB.F.Tail.B

end
end

