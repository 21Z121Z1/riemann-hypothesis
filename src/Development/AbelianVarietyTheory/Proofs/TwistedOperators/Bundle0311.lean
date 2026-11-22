import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0278
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0238
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0268
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0284
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0285

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumProductWeightsLeOfSeparatedGeometricMean
section
open GlobalTheory.SepPer Finset

namespace GlobalTheory.SepSum

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

theorem hsn_eq_norm {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : hsn X = ‖X‖ := by
  rw [Matrix.frobenius_norm_def, hsn, Real.sqrt_eq_rpow]
  congr 1
  simp only [Real.rpow_two]

theorem hsn_nonneg {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsn X := Real.sqrt_nonneg _

theorem finrank_mat (n : ℕ) : Module.finrank ℝ (Matrix (Fin n) (Fin n) ℂ) = 2 * n ^ 2 := by
  rw [Module.finrank_matrix, Complex.finrank_real_complex]
  simp only [Fintype.card_fin]
  ring

theorem dyadic (x : ℝ) (hx : 0 ≤ x) :
    (2 : ℝ) ^ Nat.log 2 ⌊1 + x⌋₊ ≤ 1 + x ∧ 1 + x < (2 : ℝ) ^ (Nat.log 2 ⌊1 + x⌋₊ + 1) := by
  have h0 : ⌊1 + x⌋₊ ≠ 0 := (Nat.floor_pos.mpr (by linarith)).ne'
  constructor
  · have h1 := Nat.pow_log_le_self 2 h0
    have h2 : ((2 ^ Nat.log 2 ⌊1 + x⌋₊ : ℕ) : ℝ) ≤ (⌊1 + x⌋₊ : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact h2.trans (Nat.floor_le (by linarith))
  · have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ⌊1 + x⌋₊
    have h2 : ((⌊1 + x⌋₊ + 1 : ℕ) : ℝ) ≤ ((2 ^ (Nat.log 2 ⌊1 + x⌋₊).succ : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    exact (Nat.lt_floor_add_one _).trans_le h2

theorem sum_prod_inv_two_le {ι : Type} [Fintype ι] [DecidableEq ι] (T : Finset (ι → ℕ)) :
    ∑ j ∈ T, ∏ v, ((2 : ℝ) ^ j v)⁻¹ ≤ 2 ^ Fintype.card ι := by
  set M := T.sup fun j => univ.sup j
  have hsub : T ⊆ Fintype.piFinset fun _ : ι => range (M + 1) := by
    intro j hj
    rw [Fintype.mem_piFinset]
    intro v
    rw [mem_range, Nat.lt_succ_iff]
    exact (le_sup (f := j) (mem_univ v)).trans (le_sup (f := fun j => univ.sup j) hj)
  refine (sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => by positivity).trans ?_
  rw [← Finset.prod_univ_sum (fun _ : ι => range (M + 1)) (fun _ k => ((2 : ℝ) ^ k)⁻¹)]
  calc ∏ v : ι, ∑ k ∈ range (M + 1), ((2 : ℝ) ^ k)⁻¹ ≤ ∏ _v : ι, (2 : ℝ) :=
        prod_le_prod (fun _ _ => by positivity) fun v _ => by
          have := sum_geometric_two_le (M + 1)
          simpa [one_div, inv_pow] using this
    _ = 2 ^ Fintype.card ι := by simp

theorem card_box_le {ι : Type} [Fintype ι] [Nonempty ι] (n : ℕ) (hn : n ≠ 0) (la : ℝ) (hla : 0 < la) (hla1 : la ≤ 1)
    (T : Finset (ι → Matrix (Fin n) (Fin n) ℂ))
    (hT : ∀ s ∈ T, ∀ s' ∈ T, s ≠ s' → la ^ Fintype.card ι ≤ ∏ v, hsn (s v - s' v))
    (j : ι → ℕ) (hj : ∀ s ∈ T, ∀ v, hsn (s v) ≤ (2 : ℝ) ^ (j v + 1)) :
    (T.card : ℝ) ≤ 6 ^ (2 * n ^ 2 * Fintype.card ι) * la⁻¹ ^ (2 * n ^ 2 * Fintype.card ι) *
      (∏ v, (2 : ℝ) ^ j v) ^ (2 * n ^ 2) := by
  set f := Fintype.card ι with hf
  set N := 2 * n ^ 2 with hN
  have hf0 : f ≠ 0 := Fintype.card_ne_zero
  have hN1 : 1 ≤ N := by have : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hn); omega
  have hP := GlobalTheory.packing_geometric_mean_separated ι (fun _ => Matrix (Fin n) (Fin n) ℂ) N hN1
    (fun _ => finrank_mat n) la (T : Set _) (fun v => (2 : ℝ) ^ (j v + 1)) hla (fun v => by positivity) ?sep
  case sep =>
    intro s hs s' hs' hne
    have h := hT s hs s' hs' hne
    simp only [← hsn_eq_norm]
    calc la = (la ^ f) ^ ((1 : ℝ) / f) := by rw [one_div, Real.pow_rpow_inv_natCast hla.le hf0]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) h (by positivity)
  have hset : {s ∈ (T : Set (ι → Matrix (Fin n) (Fin n) ℂ)) | ∀ v, ‖s v‖ ≤ (2 : ℝ) ^ (j v + 1)} = (T : Set _) := by
    ext s
    simp only [Set.mem_setOf_eq, Finset.mem_coe, and_iff_left_iff_imp]
    intro hs v
    rw [← hsn_eq_norm]
    exact hj s hs v
  have hc := hP.2
  rw [hset, Set.ncard_coe_finset] at hc
  set Pr : ℝ := ∏ v, (2 : ℝ) ^ (j v + 1) with hPr
  have hPr' : Pr = (∏ v, (2 : ℝ) ^ j v) * 2 ^ f := by
    simp only [hPr, pow_succ, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hf]
  have hPr1 : 1 ≤ Pr := by
    rw [hPr, Finset.prod_pow_eq_pow_sum]
    exact one_le_pow₀ (by norm_num)
  have hPr0 : 0 ≤ Pr := by linarith
  set G : ℝ := Pr ^ ((1 : ℝ) / f) with hG
  have hGf : G ^ f = Pr := by rw [hG, one_div, Real.rpow_inv_natCast_pow hPr0 hf0]
  have hG1 : 1 ≤ G := Real.one_le_rpow hPr1 (by positivity)
  have h3 : 1 + 2 * G / la ≤ 3 * G / la := by
    have : G ≤ G / la := le_div_self (by linarith) hla hla1
    have e : 3 * G / la = G / la + 2 * G / la := by ring
    rw [e]; linarith
  calc (T.card : ℝ) ≤ (1 + 2 * G / la) ^ (N * f) := hc
    _ ≤ (3 * G / la) ^ (N * f) := pow_le_pow_left₀ (by positivity) h3 _
    _ = 3 ^ (N * f) * la⁻¹ ^ (N * f) * (G ^ f) ^ N := by
      rw [div_eq_mul_inv, mul_pow, mul_pow, ← pow_mul, mul_comm f N]; ring
    _ = 3 ^ (N * f) * la⁻¹ ^ (N * f) * Pr ^ N := by rw [hGf]
    _ = _ := by
      rw [hPr', show (6 : ℝ) = 3 * 2 by norm_num, mul_pow, mul_pow, ← pow_mul]
      ring

theorem sum_weights_le_of_separated : ∀ (ι : Type) [Fintype ι] [Nonempty ι] (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ la : ℝ, 0 < la → la ≤ 1 → ∀ S : Finset (ι → Matrix (Fin n) (Fin n) ℂ),
      (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → la ^ Fintype.card ι ≤ ∏ v, hsn (s v - s' v)) →
      ∑ s ∈ S, ∏ v, ((1 + hsn (s v)) ^ (2 * n ^ 2 + 1))⁻¹ ≤ C * la⁻¹ ^ (2 * n ^ 2 * Fintype.card ι) := by
  intro ι _ _ n
  classical
  refine ⟨6 ^ (2 * n ^ 2 * Fintype.card ι) * 2 ^ Fintype.card ι, by positivity, ?_⟩
  intro la hla hla1 S hS
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hcard : S.card ≤ 1 :=
      Finset.card_le_one.mpr fun a _ b _ => funext fun v => Matrix.ext fun i _ => i.elim0
    have hterm : ∀ s ∈ S, ∏ v, ((1 + hsn (s v)) ^ (2 * 0 ^ 2 + 1))⁻¹ ≤ (1 : ℝ) := fun s _ =>
      Finset.prod_le_one (fun v _ => by have := hsn_nonneg (s v); positivity)
        fun v _ => inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [hsn_nonneg (s v)]))
    calc _ ≤ ∑ s ∈ S, (1 : ℝ) := sum_le_sum hterm
      _ = S.card := by simp
      _ ≤ 1 := by exact_mod_cast hcard
      _ ≤ _ := by
        have : (1 : ℝ) ≤ 2 ^ Fintype.card ι := one_le_pow₀ (by norm_num)
        simpa using this
  · set N := 2 * n ^ 2 with hN
    set f := Fintype.card ι with hf
    let jf : (ι → Matrix (Fin n) (Fin n) ℂ) → ι → ℕ := fun s v => Nat.log 2 ⌊1 + hsn (s v)⌋₊
    rw [← Finset.sum_fiberwise_of_maps_to (g := jf) (t := S.image jf) (fun s hs => Finset.mem_image_of_mem jf hs)]
    have hbox : ∀ j ∈ S.image jf, ∑ s ∈ S.filter (fun s => jf s = j), ∏ v, ((1 + hsn (s v)) ^ (N + 1))⁻¹ ≤
        6 ^ (N * f) * la⁻¹ ^ (N * f) * ∏ v, ((2 : ℝ) ^ j v)⁻¹ := by
      intro j _
      have hb : ∀ s ∈ S.filter (fun s => jf s = j),
          ∏ v, ((1 + hsn (s v)) ^ (N + 1))⁻¹ ≤ ∏ v, (((2 : ℝ) ^ j v) ^ (N + 1))⁻¹ := by
        intro s hs
        rw [Finset.mem_filter] at hs
        refine prod_le_prod (fun v _ => by have := hsn_nonneg (s v); positivity) fun v _ => ?_
        have hd := (dyadic _ (hsn_nonneg (s v))).1
        rw [← hs.2]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hd _)
      have hcard := card_box_le n hn.ne' la hla hla1 (S.filter (fun s => jf s = j))
        (fun s hs s' hs' hne => hS s (mem_filter.1 hs).1 s' (mem_filter.1 hs').1 hne) j (by
          intro s hs v
          rw [mem_filter] at hs
          have hd := (dyadic _ (hsn_nonneg (s v))).2
          rw [← hs.2]
          linarith)
      calc _ ≤ ∑ s ∈ S.filter (fun s => jf s = j), ∏ v, (((2 : ℝ) ^ j v) ^ (N + 1))⁻¹ := sum_le_sum hb
        _ = (S.filter (fun s => jf s = j)).card * ∏ v, (((2 : ℝ) ^ j v) ^ (N + 1))⁻¹ := by
          rw [sum_const, nsmul_eq_mul]
        _ ≤ (6 ^ (N * f) * la⁻¹ ^ (N * f) * (∏ v, (2 : ℝ) ^ j v) ^ N) * ∏ v, (((2 : ℝ) ^ j v) ^ (N + 1))⁻¹ :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by
          rw [mul_assoc, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
          congr 1
          refine Finset.prod_congr rfl fun v _ => ?_
          have h2 : ((2 : ℝ) ^ j v) ≠ 0 := by positivity
          rw [pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ h2), one_mul]
    calc _ ≤ ∑ j ∈ S.image jf, 6 ^ (N * f) * la⁻¹ ^ (N * f) * ∏ v, ((2 : ℝ) ^ j v)⁻¹ := sum_le_sum hbox
      _ = 6 ^ (N * f) * la⁻¹ ^ (N * f) * ∑ j ∈ S.image jf, ∏ v, ((2 : ℝ) ^ j v)⁻¹ := by rw [mul_sum]
      _ ≤ 6 ^ (N * f) * la⁻¹ ^ (N * f) * 2 ^ f :=
        mul_le_mul_of_nonneg_left (sum_prod_inv_two_le _) (by positivity)
      _ = _ := by ring

end GlobalTheory.SepSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticHalfIsotropicPartsAddSelfEqTrace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IsoPartPairing

open GlobalTheory.MixModel

theorem hO_isoPart {D : D7} (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (hC : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1) (u y : Mx D W.rank r) :
    hO V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) =
      (GlobalTheory.MixModel.adj y ⬝ (GlobalTheory.MixModel.gA W ⬝ u)).trace := by
  have hC0 : Cᴴ * V.gram * C' = 1 := hC
  have hC1 : C'ᴴ * V.gram * C = 1 := by
    have h := congrArg Matrix.conjTranspose hC0
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      GlobalTheory.MixModel.gram_conjTranspose, Matrix.conjTranspose_one, ← Matrix.mul_assoc] at h
  have hx : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u = u ⬝ rat (C'ᴴ * V.gram) := rfl
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y = y ⬝ rat (Cᴴ * V.gram) := rfl
  have hg : giA V ⬝ adj (rat (Cᴴ * V.gram)) = rat C := by
    rw [← rat_conjTranspose, Matrix.conjTranspose_mul, GlobalTheory.MixModel.gram_conjTranspose,
      Matrix.conjTranspose_conjTranspose, giA, ← rat_mul, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul]
  rw [hx, hz, hO_eq_trace, adj_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (giA V), hg]
  rw [show rat C ⬝ (adj y ⬝ (gA W ⬝ (u ⬝ rat (C'ᴴ * V.gram)))) = (rat C ⬝ adj y ⬝ gA W ⬝ u) ⬝ rat (C'ᴴ * V.gram) by
    simp only [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← rat_mul, hC1, rat_one,
    Matrix.one_mul, Matrix.mul_assoc]

theorem trHalf_add_self {D : D7} (z : AE D) :
    trHalf D z + trHalf D z = Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * z) := by
  show algebraMap D.host.F (AF D.host.F) (1 / 2) * _ + algebraMap D.host.F (AF D.host.F) (1 / 2) * _ = _
  rw [← add_mul, ← map_add, add_halves, map_one, one_mul]

theorem symplOH_isoPart_add_self : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1 → ∀ u y : Mx D W.rank r, symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) + symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) = Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (HMul.hMul (GlobalTheory.MixModel.adj y) (HMul.hMul (GlobalTheory.MixModel.gA W) u)).trace) := by
  intro D V W r C C' hC u y
  rw [symplOH_eq, hO_isoPart V W C C' hC u y, trHalf_add_self]

end GlobalTheory.IsoPartPairing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIdeleAbsDetUnitaryAdelicEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.UnitaryDetAbs

open GlobalTheory.MixModel

theorem absE_det_matHom (D : D7) (W : HSp D) (h : GA D W) :
    GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (matHom W h)) = 1 := by
  have hM := GlobalTheory.MixModel.mt_unitary W h
  have hdet := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hadj : (GlobalTheory.MixModel.adj (mt W h)).det = cA D (mt W h).det := by
    rw [GlobalTheory.MixModel.adj, Matrix.det_transpose, RingHom.map_det]; rfl
  have hG : IsUnit (GlobalTheory.MixModel.gA W).det := by
    have e : (GlobalTheory.MixModel.gA W).det = incA D W.gram.det := by
      rw [GlobalTheory.MixModel.gA, GlobalTheory.MixModel.rat, RingHom.map_det]; rfl
    rw [e]
    exact (GlobalTheory.MixModel.gram_isUnit_det W).map _
  rw [hadj] at hdet
  have key : cA D (mt W h).det * (mt W h).det = 1 := by
    have e2 : cA D (mt W h).det * (mt W h).det * (GlobalTheory.MixModel.gA W).det = 1 * (GlobalTheory.MixModel.gA W).det := by
      rw [one_mul]; nth_rewrite 2 [← hdet]; ring
    exact hG.mul_right_cancel e2
  have hu : GlobalTheory.Doubling.conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det (matHom W h)) *
      Matrix.GeneralLinearGroup.det (matHom W h) = 1 := by
    ext
    exact key
  have h2 := congrArg (GlobalTheory.Doubling.absE D.host.F D.host.E) hu
  rw [map_mul, GlobalTheory.Doubling.absE_conjUnit, map_one, ← sq] at h2
  exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 h2

end GlobalTheory.UnitaryDetAbs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondencePairingLawOfTensorLaw
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.PairOfTens

open GlobalTheory.InvPairingTensor (exists_real_parts)
open GlobalTheory.ArchRec.PairTensor

variable {p q r s : ℕ} {T : GrpData p q} (R : DSRep T)

theorem ctr_map {U U' : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U'] (g : U →ₗ[ℂ] U')
    (v : R.HK.V) (z : R.HK.V ⊗[ℂ] U) :
    ctr R U' v (TensorProduct.map LinearMap.id g z) = g (ctr R U v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [TensorProduct.map_tmul, ctr_tmul, ctr_tmul, map_smul, LinearMap.id_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mem_hwSub {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ)
    (v : V) : v ∈ hwSub act μ ↔
      (∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v) ∧ ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem ctr_ne_zero {U : Type} [AddCommGroup U] [Module ℂ U] (Λ : Ix p q → ℚ)
    (h1 : Module.finrank ℂ ↥(hwSub R.HK.act Λ) = 1) (z : R.HK.V ⊗[ℂ] U) (hz : z ≠ 0)
    (hw : ∀ a, TensorProduct.map (R.HK.act (Eab a a)) LinearMap.id z = ((Λ a : ℚ) : ℂ) • z)
    (hn : ∀ a b, posC a b → TensorProduct.map (R.HK.act (Eab a b)) LinearMap.id z = 0)
    (v : R.HK.V) (hv : IsHW R.HK.act Λ v) : ctr R U v z ≠ 0 := by
  intro h0
  apply hz
  refine eq_zero_of_ctr R U z fun w => ?_
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  let d : R.HK.V ⊗[ℂ] U →ₗ[ℂ] R.HK.V :=
    (TensorProduct.rid ℂ R.HK.V).toLinearMap ∘ₗ TensorProduct.map LinearMap.id l
  have hd : ∀ a b, d (a ⊗ₜ b) = l b • a := fun a b => by simp [d]
  have hdA : ∀ (A : Module.End ℂ R.HK.V) y, d (TensorProduct.map A LinearMap.id y) = A (d y) := by
    intro A y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [TensorProduct.map_tmul, hd, hd, map_smul, LinearMap.id_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hdc : ∀ u y, l (ctr R U u y) = ⟪R.ι u, R.ι (d y)⟫_ℂ := by
    intro u y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [ctr_tmul, hd, map_smul, map_smul, inner_smul_right, smul_eq_mul, mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy, inner_add_right]
  have hmem : d z ∈ hwSub R.HK.act Λ := by
    rw [mem_hwSub]
    exact ⟨fun a => by rw [← hdA, hw, map_smul], fun a b hab => by rw [← hdA, hn a b hab, map_zero]⟩
  have hv0 : (⟨v, hv.2⟩ : hwSub R.HK.act Λ) ≠ 0 := fun h => hv.1 (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hv0).1 h1 ⟨d z, hmem⟩
  have hc' : c • v = d z := congrArg Subtype.val hc
  have h2 := hdc v z
  rw [h0, map_zero, ← hc', map_smul, inner_smul_right] at h2
  have hvv : ⟪R.ι v, R.ι v⟫_ℂ ≠ 0 := fun h =>
    hv.1 (R.ι_inj (by rw [map_zero]; exact inner_self_eq_zero.1 h))
  have hc0 : c = 0 := (mul_eq_zero.1 h2.symm).resolve_right hvv
  rw [hdc, ← hc', hc0, zero_smul, map_zero, inner_zero_right]

variable {σ : Type} {a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)}
  {a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)}

theorem exists_tintw (h₁ : IsGK a₁) (hA : AdmGK R.HK) (M : GKMod r s)
    (B : MvPolynomial σ ℂ →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] M.V) (hB : PLift a₁ a₂ R (fun Z => M.act Z) B) :
    ∃ f, TIntw a₁ a₂ R.HK M f ∧ ∀ P v, B P v = ctr R M.V v (f P) := by
  obtain ⟨f, hf, hBf⟩ := exists_map R a₁ h₁ hA B hB.1
  refine ⟨f, ⟨hf, fun Z => ?_⟩, hBf⟩
  have hreal : ∀ X ∈ upq r s, ∀ P, f (a₂ X P) = TensorProduct.map LinearMap.id (M.act X) (f P) := by
    intro X hX P
    refine ext_ctr R _ _ _ fun y => ?_
    rw [ctr_map, ← hBf, ← hBf]
    exact hB.2 X hX P y
  obtain ⟨X, Y, hX, hY, -, rfl⟩ := exists_real_parts Z
  refine LinearMap.ext fun P => ?_
  simp only [LinearMap.comp_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    TensorProduct.map_add_right, TensorProduct.map_smul_right, hreal X hX, hreal Y hY]

theorem exists_tintw_inc (h₁ : IsGK a₁) (hA : AdmGK R.HK) (M : GKMod r s) {U : Type} [AddCommGroup U] [Module ℂ U]
    (b : Mat r s → Module.End ℂ U) (inc : M.V →ₗ[ℂ] U) (hi : Function.Injective inc)
    (he : ∀ Z ∈ upq r s, ∀ y, inc (M.act Z y) = b Z (inc y))
    (B : MvPolynomial σ ℂ →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U) (hB : PLift a₁ a₂ R b B)
    (hr : ∀ P v, B P v ∈ LinearMap.range inc) :
    ∃ f, TIntw a₁ a₂ R.HK M f ∧ ∀ P v, B P v = inc (ctr R M.V v (f P)) := by
  obtain ⟨g, hg⟩ := inc.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hi)
  let B₀ : MvPolynomial σ ℂ →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] M.V :=
    { toFun := fun P =>
        { toFun := fun v => g (B P v)
          map_add' := fun v w => by rw [map_add, map_add]
          map_smul' := fun c v => by rw [LinearMap.map_smulₛₗ, map_smul] }
      map_add' := fun P Q => by ext v; simp
      map_smul' := fun c P => by ext v; simp }
  have h0 : ∀ P v, inc (B₀ P v) = B P v := by
    intro P v
    obtain ⟨y, hy⟩ := hr P v
    change inc (g (B P v)) = _
    rw [← hy]
    exact congrArg inc (LinearMap.congr_fun hg y)
  obtain ⟨f, hf, hBf⟩ := exists_tintw (a₂ := a₂) R h₁ hA M B₀
    ⟨fun Z hZ P v => hi (by rw [map_add, h0, h0, map_zero]; exact hB.1 Z hZ P v),
     fun Z hZ P v => hi (by rw [h0, he Z hZ, h0]; exact hB.2 Z hZ P v)⟩
  exact ⟨f, hf, fun P v => by rw [← hBf, h0]⟩

theorem exists_both (h₁ : IsGK a₁) (h₂ : IsGK a₂) (hA : AdmGK R.HK) {U : Type} [NormedAddCommGroup U]
    [InnerProductSpace ℂ U] (b : Mat r s → Module.End ℂ U) (hb : IsUAct b)
    (B B' : MvPolynomial σ ℂ →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] U) (hB : PLift a₁ a₂ R b B) (hB' : PLift a₁ a₂ R b B') :
    ∃ (MM : UGKMod r s) (inc : MM.M.V →ₗ[ℂ] U) (f f' : MvPolynomial σ ℂ →ₗ[ℂ] R.HK.V ⊗[ℂ] MM.M.V),
      Function.Injective inc ∧ (∀ Z ∈ upq r s, ∀ y, inc (MM.M.act Z y) = b Z (inc y)) ∧
      TIntw a₁ a₂ R.HK MM.M f ∧ TIntw a₁ a₂ R.HK MM.M f' ∧
      (∀ P v, B P v = inc (ctr R _ v (f P))) ∧ ∀ P v, B' P v = inc (ctr R _ v (f' P)) := by
  obtain ⟨MM, inc, hi, hr, he⟩ := GlobalTheory.T.exists_unitary_module_onto_span_of_intertwining r s (MvPolynomial σ ℂ) U (R.HK.V ⊕ R.HK.V) a₂ b
    (Sum.elim (fun v => B.flip v) (fun v => B'.flip v)) h₂ hb (by
      rintro (v | v) Z hZ P
      · exact hB.2 Z hZ P v
      · exact hB'.2 Z hZ P v)
  obtain ⟨f, hf, hBf⟩ := exists_tintw_inc R h₁ hA MM.M b inc hi he B hB fun P v => by
    rw [hr]; exact Submodule.subset_span ⟨Sum.inl v, P, rfl⟩
  obtain ⟨f', hf', hBf'⟩ := exists_tintw_inc R h₁ hA MM.M b inc hi he B' hB' fun P v => by
    rw [hr]; exact Submodule.subset_span ⟨Sum.inr v, P, rfl⟩
  exact ⟨MM, inc, f, f', hi, he, hf, hf', hBf, hBf'⟩

theorem pairLaw_of_tensLaw : ∀ (p q r s : ℕ) (T₁ : GrpData p q) (σ : Type) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (R₁ : DSRep T₁) (T₂ : GrpData r s) (R₂ : DSRep T₂) (Λ₁ : Ix p q → ℚ) (Λ₂ : Ix r s → ℚ), IsGK a₁ → IsGK a₂ → AdmGK R₁.HK → Module.finrank ℂ ↥(hwSub R₁.HK.act Λ₁) = 1 → TensLaw a₁ a₂ R₁ R₂ Λ₁ Λ₂ → PairLaw a₁ a₂ R₁ R₂ Λ₁ Λ₂ := by
  intro p q r s T₁ σ a₁ a₂ R₁ T₂ R₂ Λ₁ Λ₂ h₁ h₂ hA h1 hT
  refine ⟨hT.ex, hT.uniq, fun U _ _ b hb B hB hB0 => ?_, ?_⟩
  · have hne : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (inc : M →ₗ[ℂ] U)
        (f : MvPolynomial σ ℂ →ₗ[ℂ] R₁.HK.V ⊗[ℂ] M), (∀ P v, B P v = inc (ctr R₁ _ v (f P))) → f ≠ 0 := by
      intro M _ _ inc f hf h0
      apply hB0
      refine LinearMap.ext fun P => LinearMap.ext fun v => ?_
      rw [hf, h0]
      simp
    refine ⟨?_, fun Φ hΦ => ⟨fun v hv => ?_, fun B' hB' hΦ' => ?_⟩⟩
    · obtain ⟨MM, inc, f, -, hi, he, hf, -, hBf, -⟩ := exists_both R₁ h₁ h₂ hA b hb B B hB hB
      obtain ⟨⟨N, e, hee, hrf⟩, -⟩ := hT.unit MM f hf (hne inc f hBf)
      refine ⟨inc ∘ₗ N.subtype ∘ₗ e.toLinearMap, hi.comp (Subtype.val_injective.comp e.injective),
        fun Z hZ x => ?_, le_antisymm ?_ ?_⟩
      · change inc (e (R₂.HK.act Z x) : N) = b Z (inc (e x : N))
        rw [hee, he Z hZ]
      · rintro _ ⟨x, rfl⟩
        haveI : Nontrivial (hwSub R₁.HK.act Λ₁) := Module.nontrivial_of_finrank_eq_succ h1
        obtain ⟨⟨v, hvm⟩, hv⟩ := exists_ne (0 : hwSub R₁.HK.act Λ₁)
        have hvv : ⟪R₁.ι v, R₁.ι v⟫_ℂ ≠ 0 := fun h =>
          hv (Subtype.ext (R₁.ι_inj (by rw [ZeroMemClass.coe_zero, map_zero]; exact inner_self_eq_zero.1 h)))
        have hm : TensorProduct.map LinearMap.id N.subtype (v ⊗ₜ[ℂ] e x) ∈ LinearMap.range f := by
          rw [hrf]; exact LinearMap.mem_range_self _ _
        obtain ⟨P, hP⟩ := hm
        have h3 : B P v = ⟪R₁.ι v, R₁.ι v⟫_ℂ • inc (e x : N) := by
          rw [hBf, hP, ctr_map, ctr_tmul, map_smul, map_smul]; rfl
        have h4 : (inc ∘ₗ N.subtype ∘ₗ e.toLinearMap) x = (⟪R₁.ι v, R₁.ι v⟫_ℂ)⁻¹ • B P v := by
          rw [h3, inv_smul_smul₀ hvv]; rfl
        rw [h4]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨P, v, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨P, v, rfl⟩
        have hm : f P ∈ LinearMap.range (TensorProduct.map LinearMap.id N.subtype) := by
          rw [← hrf]; exact LinearMap.mem_range_self _ _
        obtain ⟨z, hz⟩ := hm
        refine ⟨e.symm (ctr R₁ N v z), ?_⟩
        rw [hBf, ← hz, ctr_map]
        simp
    · obtain ⟨MM, inc, f, -, hi, he, hf, -, hBf, -⟩ := exists_both R₁ h₁ h₂ hA b hb B B hB hB
      obtain ⟨-, hj⟩ := hT.unit MM f hf (hne inc f hBf)
      have hΦw := (mem_hwSub _ _ _).1 hΦ.2.1.2
      have hcomm : ∀ X, TensorProduct.map (R₁.HK.act X) LinearMap.id (f Φ) = f (a₁ X Φ) :=
        fun X => (LinearMap.congr_fun (hf.1 X) Φ).symm
      rw [hBf, ← map_zero inc]
      exact hi.ne (ctr_ne_zero R₁ Λ₁ h1 (f Φ) (hj Φ hΦ).1 (fun a => by rw [hcomm, hΦw.1, map_smul])
        (fun a c hac => by rw [hcomm, hΦw.2 a c hac, map_zero]) v hv.1)
    · obtain ⟨MM, inc, f, f', hi, he, hf, hf', hBf, hBf'⟩ := exists_both R₁ h₁ h₂ hA b hb B B' hB hB'
      obtain ⟨-, hj⟩ := hT.unit MM f hf (hne inc f hBf)
      have hff : f' = f := (hj Φ hΦ).2 f' hf' (ext_ctr R₁ _ _ _ fun v => hi (by rw [← hBf, ← hBf', hΦ']))
      refine LinearMap.ext fun P => LinearMap.ext fun v => ?_
      rw [hBf, hBf', hff]
  · obtain ⟨f₀, hf₀, hf0, hall⟩ := hT.line
    obtain ⟨B₀, hB₀, hBf⟩ := exists_pairing R₁ a₁ f₀ hf₀.1
    refine ⟨B₀, fun h0 => hf0 ?_, ⟨hB₀, fun Z hZ P v => ?_⟩, fun B hB => ?_⟩
    · refine LinearMap.ext fun P => eq_zero_of_ctr R₁ _ _ fun v => ?_
      rw [← hBf, h0]; rfl
    · have := LinearMap.congr_fun (hf₀.2 Z) P
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at this
      rw [hBf, hBf, this, ctr_map]
    · obtain ⟨f, hf, hBf'⟩ := exists_tintw R₁ h₁ hA R₂.HK B hB
      obtain ⟨c, rfl⟩ := hall f hf
      refine ⟨c, LinearMap.ext fun P => LinearMap.ext fun v => ?_⟩
      rw [hBf', LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, hBf, map_smul]

end GlobalTheory.ArchRec.PairOfTens
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceTensorLawBothOrdersOfCoversStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCorrespondenceTensorLaw_both_orders_of_covers : ∀ (X : ProvA) (p q r s : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ), ARi X lam lam' → ARiiiUp X lam lam' → ARiiiDown X lam lam' → ARiiiLine X lam lam' → TensLaw (fockAct1 p q r s) (fockAct2 p q r s) (X.ds p q lam) (X.ds r s lam') (blattner lam) (blattner lam') ∧ TensLaw (fockAct2 p q r s) (fockAct1 p q r s) (X.ds r s lam') (X.ds p q lam) (blattner lam') (blattner lam) := by
  first | exact @GlobalTheory.ArchRec.TensLawOf.tensLaw_of | exact GlobalTheory.ArchRec.TensLawOf.tensLaw_of | (intros; apply GlobalTheory.ArchRec.TensLawOf.tensLaw_of <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitianStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_inner_product_hermitian : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsCovolOne (ratL T S) μ 𝓕 → ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IntegrableOn (fun w => f w * (starRingEnd ℂ) (g w)) 𝓕 μ ∧ ipO μ 𝓕 g f = (starRingEnd ℂ) (ipO μ 𝓕 f g) ∧ (∀ c : ℂ, ipO μ 𝓕 (c • f) g = c * ipO μ 𝓕 f g ∧ ipO μ 𝓕 f (c • g) = (starRingEnd ℂ) c * ipO μ 𝓕 f g) ∧ (∀ f', IsThetaFunO ψ S T f' → ipO μ 𝓕 (f + f') g = ipO μ 𝓕 f g + ipO μ 𝓕 f' g ∧ ipO μ 𝓕 g (f + f') = ipO μ 𝓕 g f + ipO μ 𝓕 g f') ∧ ipO μ 𝓕 f f = (nrm2 μ 𝓕 f : ℂ) ∧ (nrm2 μ 𝓕 f = 0 → f = 0) ∧ (∀ w, ipO μ 𝓕 (heisO ψ S T w f) (heisO ψ S T w g) = ipO μ 𝓕 f g ∧ ipO μ 𝓕 (heisO ψ S T w f) g = ipO μ 𝓕 f (heisO ψ S T (-w) g)) ∧ ∀ μ' 𝓕', IsCovolOne (ratL T S) μ' 𝓕' → ipO μ' 𝓕' f g = ipO μ 𝓕 f g := by
  first | exact @GlobalTheory.ThetaPairingLaws.ipO_laws | exact GlobalTheory.ThetaPairingLaws.ipO_laws | (intros; apply GlobalTheory.ThetaPairingLaws.ipO_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaProductMeanContinuousPeriodicDualVariableStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaProductMean_continuous_periodic_dualVariable : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ P G, IsThetaFunO ψ V W P → IsThetaFunO ψ V W G → Continuous (fun t : Mx D W.rank r => ∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ) ∧ ∀ γ ∈ ratMx D W.rank r, ∀ t : Mx D W.rank r, (∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' (γ + t) + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' (γ + t) + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ) = ∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ := by
  first | exact @GlobalTheory.TwistThetaMean.mean_continuous_periodic | exact GlobalTheory.TwistThetaMean.mean_continuous_periodic | (intros; apply GlobalTheory.TwistThetaMean.mean_continuous_periodic <;> assumption)
end

