import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0268
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0277
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0332
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalUnitaryGroupStructure
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNeZeroVacuumBesselLineLatticeRankZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.LineZero

variable {D : D7}

theorem rat_mul_mem_latO_neg {V T T' : HSp D} {LS : Set (Fin V.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {LT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)} {P : HeightOneSpectrum (𝓞 D.host.F) → Prop}
    (q : Matrix (Fin T'.rank) (Fin T.rank) D.host.E) (hq : ∀ t ∈ LT, q *ᵥ t ∈ LT') :
    ∀ x ∈ latO (negSp V) T LS LT P, rat q ⬝ x ∈ latO V T' LS (LT' : Set _) P := by
  intro x hx
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, hv, a, ha, s, hs, t, ht, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨α, hα, hv, a, ha, s, hs, -(q *ᵥ t), neg_mem (hq t ht), ?_⟩
    ext i j
    simp only [Matrix.mul_apply, rat, Matrix.map_apply, Matrix.of_apply]
    have e : ∀ (e : D.host.E) (u : AF D.host.F) (c : D.host.E), incA D e * (u ⊗ₜ[D.host.F] c) = u ⊗ₜ[D.host.F] (e * c) := by
      intro e u c
      show (Algebra.TensorProduct.includeRight e : AF D.host.F ⊗[D.host.F] D.host.E) * _ = _
      rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    simp only [e, ← TensorProduct.tmul_sum]
    congr 1
    have hX : ∑ k, star (s k) * (negSp V).gram k j = -∑ k, star (s k) * V.gram k j := by
      simp only [negSp_gram, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib]
    rw [hX]
    generalize (∑ k, star (s k) * V.gram k j) = X
    simp only [Matrix.mulVec, dotProduct, Pi.neg_apply, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

theorem exists_vacG_lineLat_zero : OnStd fun {D} _ _ _ {G} W F => ∃ Φ₀, VacG W.ψ _ _ (lineLat F 0) Φ₀ ∧ Φ₀ ≠ 0 := by
  intro D hq T L μ0 hL sc G W M hM F hF
  have hq0 : ∀ t ∈ (G.Λ (.core 0) : Set (Fin (G.V (.core 0)).rank → D.host.E)),
      F.oz.qB *ᵥ t ∈ Submodule.span (𝓞 D.host.E) {F.ζ 0} := by
    intro t ht
    have ht' : t ∈ G.sp.dec0.lat (L.ΛY 0) fun _ => 1 := by rw [← G.sp.lat0]; exact ht
    obtain ⟨y, -, u, hu, rfl⟩ := ht'
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 (hu 0)
    have ha : G.sp.dec0.a *ᵥ u = u 0 • (F.oz.iB *ᵥ F.ζ 0) := by
      rw [hF.zB]
      funext i
      simp [Matrix.mulVec, dotProduct, mul_comm]
    rw [Matrix.mulVec_add, ha, Matrix.mulVec_smul, ← hF.zA, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, F.oz.qB_iA,
      F.oz.qB_iB, Matrix.one_mulVec, Matrix.zero_mulVec, zero_add, ← hr, algebraMap_smul]
    exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self _)
  have hLT : IsSelfDualC (negSp F.Lz) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) := by
    have hs : Subsingleton (Fin F.Lz.rank) := by rw [F.rk]; infer_instance
    have hne : Nonempty (Fin F.Lz.rank) := ⟨⟨0, by rw [F.rk]; omega⟩⟩
    let B : Matrix (Fin F.Lz.rank) (Fin F.Lz.rank) D.host.E := Matrix.of fun i _ => F.ζ 0 i
    let f : Fin F.Lz.rank → Fin 1 := fun _ => 0
    have hiB : F.oz.iB * B = G.sp.dec0.a.submatrix id f := by
      refine Matrix.ext fun i j => ?_
      have := congrFun hF.zB i
      simp only [Matrix.mulVec, dotProduct] at this
      simp only [Matrix.mul_apply, B, Matrix.of_apply, Matrix.submatrix_apply, id, f]
      exact this
    have hB : Bᴴ * F.Lz.gram * B = 1 := by
      rw [← F.oz.isoB]
      have e : Bᴴ * (F.oz.iBᴴ * (G.V (.core 0)).gram * F.oz.iB) * B =
          (F.oz.iB * B)ᴴ * (G.V (.core 0)).gram * (F.oz.iB * B) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [e, hiB]
      refine (G.sp.dec0.gram_sub f f).trans (Matrix.ext fun i j => ?_)
      rw [Subsingleton.elim i j]
      simp [antiDiagonalSignGramMatrix, f]
    have hB' : B * (Bᴴ * F.Lz.gram) = 1 := mul_eq_one_comm.1 hB
    let Bg : GL (Fin F.Lz.rank) D.host.E := ⟨B, Bᴴ * F.Lz.gram, hB', hB⟩
    have hc : IsSelfDualC F.Lz (Formalism.L2.DIV.colLat Bg) :=
      GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal F.Lz Bg hB
    have hcs : Formalism.L2.DIV.colLat Bg = Submodule.span (𝓞 D.host.E) {F.ζ 0} := by
      unfold Formalism.L2.DIV.colLat
      congr 1
      ext v
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨j, rfl⟩; rfl
      · rintro rfl; exact ⟨Classical.arbitrary _, rfl⟩
    rw [hcs] at hc
    exact isSelfDualC_neg hc
  have hLS : IsSelfDualC (G.V (.core 1)) (G.Λ (.core 1)) := (G.sp.P_is 1 (by have := D.R.two_le_m; omega)).sd
  have hle : lineLat F 0 ≤ latO (G.V (.core 1)) (negSp F.Lz) (G.Λ (.core 1) : Set _)
      (Submodule.span (𝓞 D.host.E) {F.ζ 0} : Set _) (fun _ => True) := by
    intro b hb
    rw [lineLat] at hb
    have hb' : F.oz.jA ⬝ (0 : WO (G.V (.core 1)) (Yc D 0)) + F.oz.jB ⬝ b ∈ latCore G 0 := hb
    have e : b = rat F.oz.qB ⬝ (F.oz.jA ⬝ (0 : WO (G.V (.core 1)) (Yc D 0)) + F.oz.jB ⬝ b) := by
      rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
      change b = F.oz.pB ⬝ F.oz.jA ⬝ (0 : WO (G.V (.core 1)) (Yc D 0)) + F.oz.pB ⬝ F.oz.jB ⬝ b
      rw [OrthDec.pB_jA, OrthDec.pB_jB, Matrix.mul_zero, zero_add, Matrix.one_mul]
    rw [e]
    exact rat_mul_mem_latO_neg (V := G.V (.core 1)) F.oz.qB hq0 _ hb'.1
  exact GlobalTheory.AscFin.VacSub.exists_vacG_ne_zero D W.ψ W.ψ_std _ _ _ _ hLS hLT _ hle

end GlobalTheory.AscFin.LineZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPosIntegralHalfAdelicMatrixLeftMulEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage

theorem integral_leftMul_eq_smul : ∀ (D : D7) (a : AE D) (m n : ℕ) (M M' : Matrix (Fin m) (Fin m) (AE D)),
    M * M' = 1 → M' * M = 1 → ∃ κ : ℝ, 0 < κ ∧ ∀ φ : halfMx a m n → ℂ,
      ∫ t, φ (leftMul a M t) ∂haarHalf a m n = κ * ∫ t, φ t ∂haarHalf a m n := by
  intro D a m n M M' h1 h2
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  haveI : SecondCountableTopology (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.2.1
  haveI : SecondCountableTopology (Mx D m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → AE D))
  haveI : SecondCountableTopology (halfMx a m n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  have hc : ∀ N : Matrix (Fin m) (Fin m) (AE D), Continuous (leftMul a (n := n) N) := fun N =>
    (continuous_const.matrix_mul continuous_subtype_val).subtype_mk _
  let e : halfMx a m n ≃ₜ+ halfMx a m n :=
    { toFun := leftMul a M
      invFun := leftMul a M'
      left_inv := fun t => Subtype.ext (by
        rw [leftMul_coe, leftMul_coe, ← Matrix.mul_assoc, h2, Matrix.one_mul])
      right_inv := fun t => Subtype.ext (by
        rw [leftMul_coe, leftMul_coe, ← Matrix.mul_assoc, h1, Matrix.one_mul])
      map_add' := fun x y => Subtype.ext (by
        rw [AddSubgroup.coe_add, leftMul_coe, leftMul_coe, leftMul_coe, AddSubgroup.coe_add, Matrix.mul_add])
      continuous_toFun := hc M
      continuous_invFun := hc M' }
  haveI : ((haarHalf a m n).map e).IsAddHaarMeasure := e.isAddHaarMeasure_map _
  have heq := Measure.isAddLeftInvariant_eq_smul ((haarHalf a m n).map e) (haarHalf a m n)
  refine ⟨(Measure.addHaarScalarFactor ((haarHalf a m n).map e) (haarHalf a m n) : ℝ),
    by exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _, fun φ => ?_⟩
  let em : halfMx a m n ≃ᵐ halfMx a m n := e.toHomeomorph.toMeasurableEquiv
  have h3 : ∫ t, φ (leftMul a M t) ∂haarHalf a m n = ∫ t, φ t ∂((haarHalf a m n).map e) := by
    have := integral_map_equiv (μ := haarHalf a m n) em φ
    exact this.symm
  have h4 := congrArg (fun μ : Measure (halfMx a m n) => ∫ t, φ t ∂μ) heq
  rw [h3, h4, integral_smul_nnreal_measure]
  simp [Complex.real_smul, NNReal.smul_def]

end GlobalTheory.HalfAverage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalDualComplementSandwich
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PerfectCompl

open GlobalTheory.MixModel

theorem exists_left_inv {K : Type} [Field K] {n a : ℕ} (M : Matrix (Fin n) (Fin a) K) (h : M.rank = a) :
    ∃ L : Matrix (Fin a) (Fin n) K, L * M = 1 := by
  have hk : LinearMap.ker M.mulVecLin = ⊥ := by
    have e := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    have e2 : Module.finrank K (LinearMap.range M.mulVecLin) = a := h
    rw [e2, Module.finrank_fin_fun] at e
    exact Submodule.finrank_eq_zero.1 (by omega)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hk
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this

variable {D : D7} (V W : HSp D)

def pr {a b : ℕ} (A : Matrix (Fin W.rank) (Fin a) D.host.E) (B : Matrix (Fin b) (Fin V.rank) D.host.E) (x : WO V W) :
    Mx D a b :=
  rat Aᴴ * gA W * x * giA V * rat Bᴴ

theorem hO_emb_right {a b : ℕ} (A : Matrix (Fin W.rank) (Fin a) D.host.E) (B : Matrix (Fin b) (Fin V.rank) D.host.E)
    (x : WO V W) (y : Mx D a b) : hO V W x (GlobalTheory.IsoMean.emb V W A B y) = (adj y * pr V W A B x).trace := by
  rw [hO_eq_trace]
  have e : adj (GlobalTheory.IsoMean.emb V W A B y) = rat Bᴴ * (adj y * rat Aᴴ) := by
    show adj (rat A * y * rat B) = _
    rw [adj_mul, adj_mul, ← rat_conjTranspose, ← rat_conjTranspose]
  rw [e, pr]
  rw [show giA V ⬝ (rat Bᴴ ⬝ (adj y ⬝ rat Aᴴ) ⬝ (gA W ⬝ x)) =
      (giA V ⬝ rat Bᴴ) ⬝ (adj y ⬝ (rat Aᴴ ⬝ gA W ⬝ x)) by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem hO_emb_left {a b : ℕ} (A : Matrix (Fin W.rank) (Fin a) D.host.E) (B : Matrix (Fin b) (Fin V.rank) D.host.E)
    (s : Mx D a b) (z : WO V W) : hO V W (GlobalTheory.IsoMean.emb V W A B s) z = (adj (pr V W A B z) * s).trace := by
  change hO V W (rat A * s * rat B) z = _
  rw [hO_eq_trace]
  have e : adj (pr V W A B z) = rat B * (giA V * (adj z * (gA W * rat A))) := by
    rw [pr]
    simp only [adj_mul, adj_giA, adj_gA, ← rat_conjTranspose, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e]
  rw [show giA V ⬝ (adj z ⬝ (gA W ⬝ (rat A ⬝ s ⬝ rat B))) =
      (giA V ⬝ (adj z ⬝ (gA W ⬝ rat A)) ⬝ s) ⬝ rat B by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem pr_emb {a b : ℕ} {P P' : Matrix (Fin W.rank) (Fin a) D.host.E} {Q Q' : Matrix (Fin b) (Fin V.rank) D.host.E}
    (hA : Pᴴ * W.gram * P' = 1) (hB : Q' * V.gram⁻¹ * Qᴴ = 1) (s : Mx D a b) :
    pr V W P Q (GlobalTheory.IsoMean.emb V W P' Q' s) = s := by
  change rat Pᴴ ⬝ gA W ⬝ (rat P' ⬝ s ⬝ rat Q') ⬝ giA V ⬝ rat Qᴴ = s
  have e1 : rat Pᴴ ⬝ gA W ⬝ rat P' = 1 := by rw [gA, ← rat_mul, ← rat_mul, hA, rat_one]
  have e2 : rat Q' ⬝ giA V ⬝ rat Qᴴ = 1 := by rw [giA, ← rat_mul, ← rat_mul, hB, rat_one]
  calc _ = (rat Pᴴ ⬝ gA W ⬝ rat P') ⬝ s ⬝ (rat Q' ⬝ giA V ⬝ rat Qᴴ) := by simp only [Matrix.mul_assoc]
    _ = s := by rw [e1, e2, Matrix.one_mul, Matrix.mul_one]

theorem pr_sub {a b : ℕ} (A : Matrix (Fin W.rank) (Fin a) D.host.E) (B : Matrix (Fin b) (Fin V.rank) D.host.E)
    (x x' : WO V W) : pr V W A B (x - x') = pr V W A B x - pr V W A B x' := by
  simp only [pr, Matrix.mul_sub, Matrix.sub_mul]

theorem pr_rat {a b : ℕ} (A : Matrix (Fin W.rank) (Fin a) D.host.E) (B : Matrix (Fin b) (Fin V.rank) D.host.E)
    {x : WO V W} (hx : x ∈ ratMx D W.rank V.rank) : pr V W A B x ∈ ratMx D a b := by
  obtain ⟨M, rfl⟩ := mem_ratMx.1 hx
  exact ⟨Aᴴ * W.gram * M * V.gram⁻¹ * Bᴴ, by show rat _ = _; simp only [pr, gA, giA, rat_mul]⟩

theorem trace_adj_mul {a b : ℕ} (y s : Mx D a b) : (adj y * s).trace = ∑ i, ∑ j, cA D (y i j) * s i j := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, adj, Matrix.transpose_apply, Matrix.map_apply]
  exact Finset.sum_comm

end GlobalTheory.PerfectCompl

namespace GlobalTheory.PerfectCompl

open GlobalTheory.MixModel

variable {D : D7}

theorem trace_nondeg (z : AE D) (h : ∀ w : AE D, Algebra.trace (AF D.host.F) (AE D) (w * z) = 0) : z = 0 := by
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  obtain ⟨e0, he0⟩ := GlobalTheory.RatAnnih.tensor_rat (R := AF D.host.F) z fun e => ⟨0, by rw [map_zero]; exact h _⟩
  subst he0
  by_cases hne : e0 = 0
  · rw [hne, TensorProduct.tmul_zero]
  · exfalso
    have h1 := h ((1 : AF D.host.F) ⊗ₜ[D.host.F] e0⁻¹)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hne, GlobalTheory.SymplecticOrthogonalSesquilinear.trace_one_tmul,
      ← map_one (algebraMap D.host.F D.host.E), Algebra.trace_algebraMap, D.sp.cm.deg2] at h1
    have := NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F (h1.trans (map_zero _).symm)
    norm_num at this

theorem sum_single_left {a b : ℕ} (i : Fin a) (j : Fin b) (t : AE D) (s : Mx D a b) :
    ∑ i', ∑ j', cA D (Matrix.single i j t i' j') * s i' j' = cA D t * s i j := by
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j, Matrix.single_apply_same]
  · intro d _ hd
    rw [Matrix.single_apply_of_col_ne _ _ hd.symm, map_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro c _ hc
    exact Finset.sum_eq_zero fun d _ => by rw [Matrix.single_apply_of_row_ne hc.symm, map_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sum_single_right {a b : ℕ} (i : Fin a) (j : Fin b) (u : AE D) (y : Mx D a b) :
    ∑ i', ∑ j', cA D (y i' j') * Matrix.single i j u i' j' = cA D (y i j) * u := by
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j, Matrix.single_apply_same]
  · intro d _ hd
    rw [Matrix.single_apply_of_col_ne _ _ hd.symm, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro c _ hc
    exact Finset.sum_eq_zero fun d _ => by rw [Matrix.single_apply_of_row_ne hc.symm, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

variable (V W : HSp D)

theorem symplO_emb {a b : ℕ} {P P' : Matrix (Fin W.rank) (Fin a) D.host.E} {Q Q' : Matrix (Fin b) (Fin V.rank) D.host.E}
    (hA : Pᴴ * W.gram * P' = 1) (hB : Q' * V.gram⁻¹ * Qᴴ = 1) (s y : Mx D a b) :
    symplO V W (GlobalTheory.IsoMean.emb V W P' Q' s) (GlobalTheory.IsoMean.emb V W P Q y) =
      Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * ∑ i, ∑ j, cA D (y i j) * s i j) := by
  rw [symplO_eq, hO_emb_right, pr_emb V W hA hB, trace_adj_mul]

theorem symplO_emb_any {a b : ℕ} {P P' : Matrix (Fin W.rank) (Fin a) D.host.E}
    {Q Q' : Matrix (Fin b) (Fin V.rank) D.host.E}
    (hA : Pᴴ * W.gram * P' = 1) (hB : Q' * V.gram⁻¹ * Qᴴ = 1) (s : Mx D a b) (z : WO V W) :
    symplO V W (GlobalTheory.IsoMean.emb V W P' Q' s) z =
      symplO V W (GlobalTheory.IsoMean.emb V W P' Q' s) (GlobalTheory.IsoMean.emb V W P Q (pr V W P' Q' z)) := by
  rw [symplO_eq, symplO_eq, hO_emb_left, hO_emb_right, pr_emb V W hA hB]

theorem emb_rat {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E)
    (γ : Matrix (Fin a) (Fin b) D.host.E) :
    GlobalTheory.IsoMean.emb V W P Q ((incA D).toAddMonoidHom.mapMatrix γ) = ratW W V (P * γ * Q) := by
  simp [GlobalTheory.IsoMean.emb, ratW, Matrix.map_mul]

end GlobalTheory.PerfectCompl

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.PerfectCompl.exists_dual_complement : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∃ (P' : Matrix (Fin W.rank) (Fin a) D.host.E) (Q' : Matrix (Fin b) (Fin V.rank) D.host.E), (∀ x : WO V W, ∃ s : Mx D a b, ∀ y : Mx D a b, symplO V W (x - GlobalTheory.IsoMean.emb V W P' Q' s) (GlobalTheory.IsoMean.emb V W P Q y) = 0) ∧ (∀ s : Mx D a b, (∀ y : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P' Q' s) (GlobalTheory.IsoMean.emb V W P Q y) = 0) → s = 0) ∧ (∀ s : Mx D a b, (∀ γ ∈ GlobalTheory.MixModel.ratMx D a b, ψ (symplO V W (GlobalTheory.IsoMean.emb V W P' Q' s) (GlobalTheory.IsoMean.emb V W P Q γ)) = 1) ↔ s ∈ GlobalTheory.MixModel.ratMx D a b) ∧ (∀ γ ∈ GlobalTheory.MixModel.ratMx D a b, (∀ s : Mx D a b, ψ (symplO V W (GlobalTheory.IsoMean.emb V W P' Q' s) (GlobalTheory.IsoMean.emb V W P Q γ)) = 1) → γ = 0) := by
  intro D V W a b P Q hP hQ ψ hψ
  haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  obtain ⟨L, hL⟩ := GlobalTheory.PerfectCompl.exists_left_inv P hP
  obtain ⟨L', hL'⟩ := GlobalTheory.PerfectCompl.exists_left_inv Qᵀ (by rw [Matrix.rank_transpose]; exact hQ)
  have hR : Q * L'ᵀ = 1 := by
    have := congrArg Matrix.transpose hL'
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have hA : Pᴴ * W.gram * (W.gram⁻¹ * Lᴴ) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (GlobalTheory.MixModel.gram_isUnit_det W), ← conjTranspose_mul, hL,
      conjTranspose_one]
  have hB : (L'ᵀ)ᴴ * V.gram * V.gram⁻¹ * Qᴴ = 1 := by
    rw [Matrix.mul_nonsing_inv_cancel_right _ _ (GlobalTheory.MixModel.gram_isUnit_det V), ← conjTranspose_mul, hR, conjTranspose_one]
  clear hL hL' hR
  obtain ⟨P', Q', hA, hB⟩ : ∃ (P' : Matrix (Fin W.rank) (Fin a) D.host.E) (Q' : Matrix (Fin b) (Fin V.rank) D.host.E),
      Pᴴ * W.gram * P' = 1 ∧ Q' * V.gram⁻¹ * Qᴴ = 1 := ⟨_, _, hA, hB⟩
  refine ⟨P', Q', ?_, ?_, ?_, ?_⟩
  · intro x
    refine ⟨GlobalTheory.PerfectCompl.pr V W P Q x, fun y => ?_⟩
    rw [GlobalTheory.MixModel.symplO_eq, GlobalTheory.PerfectCompl.hO_emb_right, GlobalTheory.PerfectCompl.pr_sub, GlobalTheory.PerfectCompl.pr_emb V W hA hB, sub_self,
      Matrix.mul_zero, Matrix.trace_zero, mul_zero, map_zero]
  · intro s hs
    ext i j
    rw [Matrix.zero_apply]
    apply GlobalTheory.PerfectCompl.trace_nondeg
    intro w
    have h := hs (Matrix.single i j (cA D (incA D D.host.xi0⁻¹ * w)))
    rw [GlobalTheory.PerfectCompl.symplO_emb V W hA hB, GlobalTheory.PerfectCompl.sum_single_left, cA_cA] at h
    rw [← h]
    congr 1
    rw [← mul_assoc, ← mul_assoc, ← map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_mul]
  · intro s
    constructor
    · intro h
      have hx : GlobalTheory.IsoMean.emb V W P' Q' s ∈ ratL W V := by
        refine (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ V W _).1 fun z hz => ?_
        rw [GlobalTheory.PerfectCompl.symplO_emb_any V W hA hB]
        exact h _ (GlobalTheory.PerfectCompl.pr_rat V W _ _ hz)
      have := GlobalTheory.PerfectCompl.pr_rat V W P Q hx
      rwa [GlobalTheory.PerfectCompl.pr_emb V W hA hB] at this
    · rintro ⟨s0, rfl⟩ γ ⟨γ0, rfl⟩
      rw [GlobalTheory.PerfectCompl.emb_rat, GlobalTheory.PerfectCompl.emb_rat]
      obtain ⟨c, hc⟩ := GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_rat D V W (P' * s0 * Q') (P * γ0 * Q)
      rw [hc]
      exact hψ.1.2.2.1 c
  · rintro γ ⟨g, rfl⟩ h
    by_contra hne
    have hex : ∃ i j, g i j ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hne
      ext i j
      show incA D (g i j) = 0
      rw [hall i j, map_zero]
    obtain ⟨i, j, hij⟩ := hex
    obtain ⟨x0, hx0⟩ := hψ.1.2.2.2
    apply hx0
    have hc : star (g i j) ≠ 0 := star_ne_zero.2 hij
    have h1 := h (Matrix.single i j
      (x0 • incA D (D.host.xi0⁻¹ * (star (g i j))⁻¹ * algebraMap D.host.F D.host.E (1 / 2))))
    rw [GlobalTheory.PerfectCompl.symplO_emb V W hA hB, GlobalTheory.PerfectCompl.sum_single_right] at h1
    have e0 : ((incA D).toAddMonoidHom.mapMatrix (m := Fin a) (n := Fin b) g) i j = incA D (g i j) := rfl
    rw [e0] at h1
    have e3 : incA D D.host.xi0 * (cA D (incA D (g i j)) *
        x0 • incA D (D.host.xi0⁻¹ * (star (g i j))⁻¹ * algebraMap D.host.F D.host.E (1 / 2))) =
        x0 • incA D (algebraMap D.host.F D.host.E (1 / 2)) := by
      rw [GlobalTheory.DualPairCheck.cA_incA, mul_smul_comm, mul_smul_comm, ← map_mul, ← map_mul]
      congr 2
      field_simp [GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D, hc]
    have t : Algebra.trace (AF D.host.F) (AE D) (incA D (algebraMap D.host.F D.host.E (1 / 2))) = 1 := by
      have := GlobalTheory.SymplecticOrthogonalSesquilinear.trace_one_tmul (F := D.host.F) (E := D.host.E) (AF D.host.F)
        (algebraMap D.host.F D.host.E (1 / 2))
      rw [Algebra.trace_algebraMap, D.sp.cm.deg2] at this
      refine this.trans ?_
      norm_num
    rw [e3, map_smul, t, smul_eq_mul, mul_one] at h1
    exact h1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalImageRationalPointMulVec
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer

theorem ratPt_mulVec_ratV : ∀ (D : D7) (V : HSp D) (γ : GA D V), γ ∈ GQ V → ∀ y : Fin V.rank → D.host.E,
    ∃ z : Fin V.rank → D.host.E, mt V γ *ᵥ ratV y = ratV z := by
  intro D V γ hγ y
  obtain ⟨e, he⟩ := GlobalTheory.Ker.Grp.exists_equiv V
  have h : mt V γ = ((e.symm ⟨γ, hγ⟩).1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D) := by
    have := he (e.symm ⟨γ, hγ⟩)
    rw [Equiv.apply_symm_apply] at this
    exact this
  refine ⟨((e.symm ⟨γ, hγ⟩).1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ y, ?_⟩
  rw [h]
  funext i
  simp only [ratV]
  exact (RingHom.map_mulVec (incA D) _ y i).symm

end GlobalTheory.SepPer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalTestMatrixIsolatesEntry
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EntryTest

theorem exists_left_inv {K : Type} [Field K] {m n : ℕ} (P : Matrix (Fin m) (Fin n) K) (h : P.rank = n) :
    ∃ P' : Matrix (Fin n) (Fin m) K, P' * P = 1 := by
  have hker : LinearMap.ker P.mulVecLin = ⊥ := by
    have e := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
    rw [← Matrix.rank, h, Module.finrank_fin_fun] at e
    exact Submodule.finrank_eq_zero.1 (by omega)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective P.mulVecLin hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' P, ← LinearMap.toMatrix'_comp]
  rw [show Matrix.toLin' P = P.mulVecLin from rfl, hg, LinearMap.toMatrix'_id]

theorem exists_right_inv {K : Type} [Field K] {m n : ℕ} (Q : Matrix (Fin m) (Fin n) K) (h : Q.rank = m) :
    ∃ Q' : Matrix (Fin n) (Fin m) K, Q * Q' = 1 := by
  have hrange : LinearMap.range Q.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, h, Module.finrank_fin_fun]
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective Q.mulVecLin hrange
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' Q, ← LinearMap.toMatrix'_comp]
  rw [show Matrix.toLin' Q = Q.mulVecLin from rfl, hg, LinearMap.toMatrix'_id]

variable {D : D7}

theorem hO_test (V W : HSp D) (N : Matrix (Fin V.rank) (Fin W.rank) D.host.E) (x : WO V W) :
    hO V W x ((Matrix.of fun c b => star ((V.gram * N * W.gram⁻¹) b c) :
      Matrix (Fin W.rank) (Fin V.rank) D.host.E).map (incA D)) = ∑ a, ∑ d, incA D (N a d) * x d a := by
  have h1 : V.gram⁻¹ * (V.gram * N * W.gram⁻¹) * W.gram = N := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit W), Matrix.mul_one,
      Matrix.nonsing_inv_mul_cancel_left _ _ (GlobalTheory.LatVac.gram_det_isUnit V)]
  have hc : ∀ b c, cA D (((Matrix.of fun c b => star ((V.gram * N * W.gram⁻¹) b c) :
      Matrix (Fin W.rank) (Fin V.rank) D.host.E).map (incA D)) c b) = incA D ((V.gram * N * W.gram⁻¹) b c) := by
    intro b c
    rw [Matrix.map_apply, GlobalTheory.DualPairCheck.cA_incA, Matrix.of_apply, star_star]
  unfold hO
  simp only [hc]
  generalize V.gram * N * W.gram⁻¹ = M at h1
  subst h1
  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]

theorem sum_emb_single (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (N : Matrix (Fin V.rank) (Fin W.rank) D.host.E) (i : Fin a) (j : Fin b)
    (e : D.host.E) (hN : Q * N * P = Matrix.single j i e) (y : Mx D a b) :
    ∑ k, ∑ l, incA D (N k l) * GlobalTheory.IsoMean.emb V W P Q y l k = incA D e * y i j := by
  have h1 : ∑ k, ∑ l, incA D (N k l) * GlobalTheory.IsoMean.emb V W P Q y l k =
      (N.map (incA D) * GlobalTheory.IsoMean.emb V W P Q y).trace := by
    simp [Matrix.trace, Matrix.mul_apply]
  have h2 : N.map (incA D) * GlobalTheory.IsoMean.emb V W P Q y =
      N.map (incA D) * (P.map (incA D) * y) * Q.map (incA D) := by
    simp only [GlobalTheory.IsoMean.emb, Matrix.mul_assoc]
  rw [h1, h2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, hN]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and]

theorem entry : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ (i : Fin a) (j : Fin b) (c : D.host.E), ∃ m : Matrix (Fin W.rank) (Fin V.rank) D.host.E, ∀ (y : Mx D a b) (r : AF D.host.F), symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (r • m.map (incA D)) = r * Algebra.trace (AF D.host.F) (AE D) (incA D c * y i j) := by
  intro D V W a b P Q hP hQ i j c
  obtain ⟨P', hP'⟩ := exists_left_inv P hP
  obtain ⟨Q', hQ'⟩ := exists_right_inv Q hQ
  set N := Q' * Matrix.single j i (D.host.xi0⁻¹ * c) * P' with hNdef
  have hN : Q * N * P = Matrix.single j i (D.host.xi0⁻¹ * c) := by
    rw [hNdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ', Matrix.one_mul, Matrix.mul_assoc, hP', Matrix.mul_one]
  refine ⟨Matrix.of fun q p => star ((V.gram * N * W.gram⁻¹) p q), fun y r => ?_⟩
  rw [← GlobalTheory.SplitScalar.symplOH_add_self, GlobalTheory.FinTranslate.symplOH_smul_right, ← mul_add,
    GlobalTheory.SplitScalar.symplOH_add_self]
  congr 1
  rw [symplO, hO_test, sum_emb_single V W P Q N i j _ hN y, ← mul_assoc, ← map_mul,
    mul_inv_cancel_left₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)]

end GlobalTheory.EntryTest
end
end

