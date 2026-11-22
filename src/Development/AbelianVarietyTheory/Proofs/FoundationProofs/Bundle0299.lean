import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.PolarLatticePairs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardPairLatticeLocallyOrthonormalBasis
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0274
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedWeylLatticeHermitianDuality
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PtHomInjective
section
open NumberField IsDedekindDomain Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs
open scoped Pointwise

noncomputable section

namespace GlobalTheory.ThetaLatticePoints

def ptHom (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a d : ℕ) :
    Matrix (Fin d) (Fin a) D.host.E →+ VC D a d :=
  AddMonoidHom.mk' (pt D (tor0 D cc δ) δ) fun y y' => by
    funext τ i j
    simp [pt, embV, tor0, mul_add]

theorem ptHom_apply (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a d : ℕ)
    (z : Matrix (Fin d) (Fin a) D.host.E) : ptHom D cc δ a d z = pt D (tor0 D cc δ) δ z := rfl

theorem ptHom_injective (D : D7) (cc : Ideal (𝓞 D.host.K)) {δ : ℂ} (hδ : δ ≠ 0) (a d : ℕ) :
    Function.Injective (ptHom D cc δ a d) := by
  intro y y' h
  refine Matrix.ext fun i j => ?_
  have h1 : δ * embT D (D.eTau.symm 1) (y i j) = δ * embT D (D.eTau.symm 1) (y' i j) :=
    congrFun (congrFun (congrFun h (D.eTau.symm 1)) i) j
  exact (embT D _).injective (mul_left_cancel₀ hδ h1)

theorem ptHom_smul (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a d : ℕ) (c : 𝓞 D.host.K)
    (y : Matrix (Fin d) (Fin a) D.host.E) :
    ptHom D cc δ a d (((c : D.host.K) : D.host.E) • y) =
      (δ * D.host.φ₀ ((c : D.host.K) : D.host.E)) • embV D (tor0 D cc δ) y := by
  funext τ i j
  simp only [ptHom_apply, pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul,
    GlobalTheory.InducedType.restrict_K D τ, mul_assoc]

theorem single_mem (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a d : ℕ) (i : Fin d) (j : Fin a)
    {t : D.host.E} (ht : t ∈ coefLat D cc) (r : 𝓞 D.host.E) :
    ptHom D cc δ a d (Matrix.single i j (r • t)) ∈ La0 D (tor0 D cc δ) a d := by
  induction ht using Submodule.span_induction generalizing r with
  | mem t ht =>
    obtain ⟨c, hc, m, hm, rfl⟩ := ht
    refine AddSubgroup.subset_closure ⟨δ * D.host.φ₀ ((c : D.host.K) : D.host.E),
      AddSubgroup.subset_closure ⟨c, hc, rfl⟩, Matrix.single i j (r • m), ?_, ?_⟩
    · refine (GlobalTheory.OddGenus.mem_iff_entries D a d _).2 fun k l => ?_
      rw [Matrix.single_apply]
      split_ifs
      · exact (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E).smul_mem r hm
      · exact D.host.AA0.zero_mem
    · rw [← ptHom_smul, Matrix.smul_single, smul_eq_mul, mul_smul_comm]
  | zero => rw [smul_zero, Matrix.single_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add, Matrix.single_add, map_add]; exact add_mem (hx r) (hy r)
  | smul s x _ hx => rw [smul_smul]; exact hx _

theorem La0_eq_map (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a d : ℕ) :
    La0 D (tor0 D cc δ) a d = (lat0 D cc a d).map (ptHom D cc δ a d) := by
  apply le_antisymm
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, A, hA, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (GlobalTheory.CurveLattice.mem_lamOf D cc δ w).1 hw
    refine ⟨((c : D.host.K) : D.host.E) • A, fun i j => ?_, ptHom_smul D cc δ a d c A⟩
    exact Submodule.subset_span ⟨c, hc, A i j, (GlobalTheory.OddGenus.mem_iff_entries D a d A).1 hA i j, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [Matrix.matrix_eq_sum_single z, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_sum]
    refine sum_mem fun j _ => ?_
    simpa using single_mem D cc δ a d i j (hz i j) 1

theorem pt_mem_iff : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a d : ℕ), Crv D cc δ → ∀ z : Matrix (Fin d) (Fin a) D.host.E, pt D (tor0 D cc δ) δ z ∈ La0 D (tor0 D cc δ) a d ↔ z ∈ lat0 D cc a d := by
  intro D cc δ a d h z
  have hδ : δ ≠ 0 :=
    (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h).2.1
  rw [La0_eq_map, ← ptHom_apply]
  exact AddSubgroup.mem_map_iff_mem (ptHom_injective D cc hδ a d)

end GlobalTheory.ThetaLatticePoints
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarMulSqEqProdKernelQuotients
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

open Filter Topology

noncomputable section

namespace GlobalTheory.EvenTheta.MulLat

variable {Λ : AddSubgroup ℂ}

theorem trFac_ne (z ω : ℂ) : GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ≠ 0 := Complex.exp_ne_zero _

theorem differentiable_trFac (ω : ℂ) : Differentiable ℂ fun z => GlobalTheory.EvenTheta.Fibres.trFac Λ z ω := by
  unfold GlobalTheory.EvenTheta.Fibres.trFac
  fun_prop

theorem exists_sg_mul_sq (h : IsLat Λ) {β : ℂ} (hβ : ∀ ω ∈ Λ, β * ω ∈ Λ) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ z, sgStar Λ (β * z) ^ 2 = sgStar Λ z ^ 2 * G z := by
  have hσ := h.differentiable
  have hne : ∀ z ∉ Λ, sgStar Λ z ≠ 0 := fun z hz => (h.sg_eq_zero z).not.2 hz
  set u := dslope (sgStar Λ) 0 with hu_def
  have hU : Differentiable ℂ u :=
    differentiableOn_univ.1 ((Complex.differentiableOn_dslope Filter.univ_mem).2 hσ.differentiableOn)
  have hu0 : u 0 = 1 := by
    rw [hu_def, dslope_same, (GlobalTheory.OddTheta.sgStar_laws Λ h).1.2.1]
  have eu : ∀ z, sgStar Λ z = z * u z := fun z => by
    have := sub_smul_dslope (sgStar Λ) 0 z
    rw [(h.sg_eq_zero 0).2 Λ.zero_mem] at this
    simpa using this.symm
  refine exists_entire_of_locally_dvd (F := fun z => sgStar Λ (β * z) ^ 2) (S := fun z => sgStar Λ z ^ 2)
    (h.dense_compl.mono fun z hz => pow_ne_zero 2 (hne z hz)) fun w => ?_
  by_cases hw : w ∈ Λ
  · have hT := differentiable_trFac (Λ := Λ) w
    have hT' := differentiable_trFac (Λ := Λ) (β * w)
    set D : ℂ → ℂ := fun z => u (z - w) ^ 2 * GlobalTheory.EvenTheta.Fibres.trFac Λ (β * (z - w)) (β * w) ^ 2
      with hD_def
    have hD : Differentiable ℂ D := by
      rw [hD_def]
      have h1 : Differentiable ℂ fun z => u (z - w) := hU.comp (by fun_prop)
      have h2 : Differentiable ℂ fun z => GlobalTheory.EvenTheta.Fibres.trFac Λ (β * (z - w)) (β * w) :=
        hT'.comp (by fun_prop)
      fun_prop
    have hD0 : D w ≠ 0 := by
      simp only [hD_def, sub_self, hu0]
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (trFac_ne _ _))
    set N : ℂ → ℂ := fun z => β ^ 2 * u (β * (z - w)) ^ 2 * GlobalTheory.EvenTheta.Fibres.trFac Λ (z - w) w ^ 2
      with hN_def
    have hN : Differentiable ℂ N := by
      rw [hN_def]
      have h1 : Differentiable ℂ fun z => u (β * (z - w)) := hU.comp (by fun_prop)
      have h2 : Differentiable ℂ fun z => GlobalTheory.EvenTheta.Fibres.trFac Λ (z - w) w :=
        hT.comp (by fun_prop)
      fun_prop
    refine ⟨fun z => N z / D z, (hN.analyticAt w).div (hD.analyticAt w) hD0, ?_⟩
    filter_upwards [hD.continuous.continuousAt.eventually_ne hD0] with z hz
    have hz1 : u (z - w) ≠ 0 := fun h0 => hz (by simp [hD_def, h0])
    have e1 := GlobalTheory.EvenTheta.Fibres.sg_sq h hw (z - w)
    have e2 := GlobalTheory.EvenTheta.Fibres.sg_sq h (hβ w hw) (β * (z - w))
    rw [sub_add_cancel] at e1
    rw [show β * (z - w) + β * w = β * z by ring] at e2
    have t1 := trFac_ne (Λ := Λ) (z - w) w
    have t2 := trFac_ne (Λ := Λ) (β * (z - w)) (β * w)
    simp only [hN_def, hD_def]
    rw [eu (z - w)] at e1
    rw [eu (β * (z - w))] at e2
    have hz' : u (z - w) ^ 2 * GlobalTheory.EvenTheta.Fibres.trFac Λ (β * (z - w)) (β * w) ^ 2 ≠ 0 := hz
    rw [mul_div_assoc', eq_div_iff hz']
    linear_combination u (z - w) ^ 2 * e2 - β ^ 2 * u (β * (z - w)) ^ 2 * e1
  · refine ⟨fun z => sgStar Λ (β * z) ^ 2 / sgStar Λ z ^ 2,
      (((hσ.comp (by fun_prop : Differentiable ℂ fun z => β * z)).pow 2).analyticAt w).div
        ((hσ.analyticAt w).pow 2) (pow_ne_zero 2 (hne w hw)), ?_⟩
    filter_upwards [hσ.continuous.continuousAt.eventually_ne (hne w hw)] with y hy
    field_simp

end GlobalTheory.EvenTheta.MulLat

namespace GlobalTheory.EvenTheta.MulLat

variable {Λ : AddSubgroup ℂ}

theorem val_zero (h : IsLat Λ) {β : ℂ} {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (eG : ∀ z, sgStar Λ (β * z) ^ 2 = sgStar Λ z ^ 2 * G z) : G 0 = β ^ 2 := by
  have hσ := h.differentiable
  set u := dslope (sgStar Λ) 0 with hu_def
  have hU : Differentiable ℂ u :=
    differentiableOn_univ.1 ((Complex.differentiableOn_dslope Filter.univ_mem).2 hσ.differentiableOn)
  have hu0 : u 0 = 1 := by
    rw [hu_def, dslope_same, (GlobalTheory.OddTheta.sgStar_laws Λ h).1.2.1]
  have eu : ∀ z, sgStar Λ z = z * u z := fun z => by
    have := sub_smul_dslope (sgStar Λ) 0 z
    rw [(h.sg_eq_zero 0).2 Λ.zero_mem] at this
    simpa using this.symm
  have hGc := hG.continuous
  have hUc := hU.continuous
  have key := congrFun (Continuous.ext_on (dense_compl_singleton (0 : ℂ))
    (f := fun z => u z ^ 2 * G z) (g := fun z => β ^ 2 * u (β * z) ^ 2) (by fun_prop)
    (by fun_prop) fun z hz => by
      have hz : z ≠ 0 := hz
      have e := eG z
      rw [eu, eu z] at e
      refine mul_left_cancel₀ (pow_ne_zero 2 hz) ?_
      beta_reduce
      linear_combination -e) 0
  simpa [hu0] using key

theorem sg_mul_sq : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ (β : ℂ) (k : ℕ), (∀ ω ∈ Λ, β * ω ∈ Λ) → β * starRingEnd ℂ β = ((k + 1 : ℕ) : ℂ) → ∃ Q : Fin k → ℂ, (∀ i, Q i ∉ Λ ∧ β * Q i ∈ Λ) ∧ ∀ z, sgStar Λ (β * z) ^ 2 = β ^ 2 * sgStar Λ z ^ 2 * ∏ i, sqTh Λ (Q i) z := by
  intro Λ h β k hβ hN
  have hβ0 : β ≠ 0 := by
    rintro rfl
    norm_num at hN
    exact Nat.cast_add_one_ne_zero k hN.symm
  have hσ := h.differentiable
  have hσc := hσ.continuous
  have hne : ∀ z ∉ Λ, sgStar Λ z ≠ 0 := fun z hz => (h.sg_eq_zero z).not.2 hz
  obtain ⟨G, hG, eG⟩ := exists_sg_mul_sq h hβ
  have hGc := hG.continuous
  have hG0 := val_zero h hG eG
  have hev : ∀ z, G (-z) = G z := fun z => by
    refine congrFun (Continuous.ext_on h.dense_compl (f := fun z => G (-z)) (by fun_prop) hGc
      fun z hz => ?_) z
    refine mul_left_cancel₀ (pow_ne_zero 2 (hne z hz)) ?_
    have h1 := eG (-z)
    rw [h.sg_neg, neg_sq, mul_neg, h.sg_neg, neg_sq] at h1
    exact h1.symm.trans (eG z)
  have hlaw : ∀ ω ∈ Λ, ∀ z, G (z + ω) * GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ^ (2 * k) = G z := by
    intro ω hω z
    have hTc : Continuous fun z => GlobalTheory.EvenTheta.Fibres.trFac Λ z ω :=
      (differentiable_trFac ω).continuous
    refine congrFun (Continuous.ext_on h.dense_compl
      (f := fun z => G (z + ω) * GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ^ (2 * k)) (by fun_prop) hGc
      fun z hz => ?_) z
    refine mul_left_cancel₀ (pow_ne_zero 2 (hne z hz)) ?_
    have ea := GlobalTheory.EvenTheta.Fibres.sg_sq h hω z
    have eb := GlobalTheory.EvenTheta.Fibres.sg_sq h (hβ ω hω) (β * z)
    rw [GlobalTheory.EvenTheta.Fibres.trFac_mul hN] at eb
    have egz := eG z
    have egw := eG (z + ω)
    rw [mul_add] at egw
    beta_reduce
    linear_combination egz + eb - GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ^ (2 * k + 2) * egw -
      G (z + ω) * GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ^ (2 * k) * ea
  obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.EvenTheta.exists_eq_prod_sqTh Λ h k (fun z => G z / β ^ 2)
    (hG.div_const _) (fun z => by simp only [hev]) (by simp only [hG0]; exact div_self (pow_ne_zero 2 hβ0))
    (fun ω hω z => GlobalTheory.EvenTheta.Fibres.law_of_fac h (F := fun z => G z / β ^ 2) (k := k) hω z (by
      show G (z + ω) / β ^ 2 * _ = G z / β ^ 2
      rw [div_mul_eq_mul_div, hlaw ω hω z]))
  have hfac : ∀ z, sgStar Λ (β * z) ^ 2 = β ^ 2 * sgStar Λ z ^ 2 * ∏ i, sqTh Λ (Q i) z := fun z => by
    rw [eG z, ← hQe z]
    field_simp
  refine ⟨Q, fun i => ⟨hQ i, ?_⟩, hfac⟩
  refine (h.sg_eq_zero _).1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ?_)
  rw [hfac, Finset.prod_eq_zero (Finset.mem_univ i)
    ((h.sqTh_eq_zero (hQ i) _).2 (Or.inr (by rw [sub_self]; exact Λ.zero_mem))), mul_zero]

end GlobalTheory.EvenTheta.MulLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumNormEntriesLeSumSingularValues
section
namespace GlobalTheory.CartanInt.Frob
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

theorem sq_col_le {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (a : Fin n) : (∑ i, ‖U i a‖) ^ 2 ≤ n := by
  have h1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have h2 := congrFun (congrFun h1 a) a
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.star_def,
    Complex.conj_mul'] at h2
  have h3 : ∑ i, ‖U i a‖ ^ 2 = 1 := by exact_mod_cast h2
  have h4 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖U i a‖)
  simpa [h3] using h4

theorem sum_diag (p q : ℕ) (s : ℕ → ℝ) :
    ∑ a : Fin p, ∑ b : Fin q, (if (a : ℕ) = (b : ℕ) then s a else 0) =
      ∑ i ∈ Finset.range (min p q), s i := by
  rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin q, (if a = (b : ℕ) then s a else 0)) p]
  have h : ∀ a : ℕ, ∑ b : Fin q, (if a = (b : ℕ) then s a else 0) =
      if a ∈ Finset.range q then s a else 0 := fun a => by
    rw [Fin.sum_univ_eq_sum_range (fun b => if a = b then s a else 0) q, Finset.sum_ite_eq]
  simp only [h]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

theorem sum_norm_le_sum_singVal : ∀ (p q : ℕ) (B : Matrix (Fin p) (Fin q) ℂ),
    ∑ i, ∑ j, ‖B i j‖ ≤
      (((p + q : ℕ) : ℝ) + 1) / 2 * ∑ i ∈ Finset.range (min p q), singVal B i := by
  intro p q B
  obtain ⟨U, hU, V, hV, hB⟩ := GlobalTheory.RectSVD.exists_svd_singularValues p q B
  set d : Fin p → Fin q → ℝ := fun a b => if (a : ℕ) = (b : ℕ) then singVal B a else 0 with hd
  have hd0 : ∀ a b, 0 ≤ d a b := fun a b => by
    simp only [hd]; split_ifs
    · exact singVal_nonneg _ _
    · exact le_rfl
  have h1 : ∀ i j, ‖B i j‖ ≤ ∑ b, ∑ a, ‖U i a‖ * d a b * ‖V j b‖ := by
    intro i j
    have e := congrFun (congrFun hB i) j
    rw [e, Matrix.mul_apply]
    refine norm_sum_le_of_le _ fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine norm_sum_le_of_le _ fun a _ => le_of_eq ?_
    rw [norm_mul, norm_mul, Matrix.conjTranspose_apply, norm_star, Matrix.of_apply]
    congr 2
    simp only [hd]
    split_ifs
    · rw [Complex.norm_real]; exact Real.norm_of_nonneg (singVal_nonneg B a)
    · simp
  calc ∑ i, ∑ j, ‖B i j‖ ≤ ∑ i, ∑ j, ∑ b, ∑ a, ‖U i a‖ * d a b * ‖V j b‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
    _ = ∑ b, ∑ a, ((∑ i, ‖U i a‖) * ∑ j, ‖V j b‖) * d a b := by
        simp only [Finset.sum_mul_sum, Finset.sum_mul]
        simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin q))) (t := (Finset.univ : Finset (Fin q))) (f := fun j b => ∑ a, ‖U _ a‖ * d a b * ‖V j b‖)]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin q))) (t := (Finset.univ : Finset (Fin p))) (f := fun j a => ‖U _ a‖ * d a b * ‖V j b‖)]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum]; ring
    _ ≤ ∑ b, ∑ a, (((p + q : ℕ) : ℝ) + 1) / 2 * d a b := by
        refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_right ?_ (hd0 a b)
        have := sq_col_le hU a
        have := sq_col_le hV b
        push_cast
        nlinarith [sq_nonneg ((∑ i, ‖U i a‖) - ∑ j, ‖V j b‖)]
    _ = _ := by
        rw [← sum_diag, Finset.sum_comm]
        simp only [Finset.mul_sum, hd]

end GlobalTheory.CartanInt.Frob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumNormSqExpHermSubOneLeBlockMat
section
noncomputable section
namespace GlobalTheory.CartanLip
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius

section
variable {n : Type} [Fintype n] [DecidableEq n]

theorem frob_sq (A : Matrix n n ℂ) : ‖A‖ ^ 2 = ∑ a, ∑ b, ‖A a b‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp

theorem frob_sq_trace (A : Matrix n n ℂ) : ‖A‖ ^ 2 = (Matrix.trace (A * Aᴴ)).re := by
  rw [frob_sq]
  simp [Matrix.trace, Matrix.mul_apply, Complex.sq_norm, Complex.normSq_apply]

theorem frob_unitary (U A V : Matrix n n ℂ) (hU : Uᴴ * U = 1) (hV : V * Vᴴ = 1) :
    ‖U * A * V‖ = ‖A‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), frob_sq_trace, frob_sq_trace]
  congr 1
  calc trace (U * A * V * (U * A * V)ᴴ) = trace (U * (A * (V * Vᴴ) * Aᴴ * Uᴴ)) := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = trace (A * Aᴴ * (Uᴴ * U)) := by
        rw [hV, trace_mul_comm]; simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = _ := by rw [hU, Matrix.mul_one]

theorem exp_skew (X : Matrix n n ℂ) (hX : Xᴴ = -X) :
    (NormedSpace.exp X)ᴴ * NormedSpace.exp X = 1 ∧ NormedSpace.exp X * (NormedSpace.exp X)ᴴ = 1 := by
  rw [← Matrix.exp_conjTranspose, hX]
  constructor
  · rw [← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_left]; simp
  · rw [← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_right]; simp

theorem norm_exp_mul_exp_sub_one (X Y : Matrix n n ℂ) (hX : Xᴴ = -X) (hY : Yᴴ = -Y) :
    ‖NormedSpace.exp X * NormedSpace.exp Y - 1‖ ≤ ‖X + Y‖ := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun t : ℝ => NormedSpace.exp (t • X) * NormedSpace.exp (t • Y))
    (f' := fun t : ℝ => NormedSpace.exp (t • X) * (X + Y) * NormedSpace.exp (t • Y)) (C := ‖X + Y‖)
    (fun t _ => by
      have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X t).fun_mul
        (hasDerivAt_exp_smul_const' (𝕂 := ℝ) Y t)
      refine (h1.congr_deriv ?_).hasDerivWithinAt
      rw [mul_add, add_mul, mul_assoc _ Y]
      rfl)
    (fun t _ => le_of_eq (frob_unitary _ _ _
      (exp_skew _ (by simp [hX])).1 (exp_skew _ (by simp [hY])).2))
  simpa using h

theorem sum_sq_le (H H' : Matrix n n ℂ) (hH : Hᴴ = H) (hH' : H'ᴴ = H') :
    ∑ a, ∑ b, ‖(NormedSpace.exp (-(Complex.I • H')) * NormedSpace.exp (Complex.I • H) - 1) a b‖ ^ 2 ≤
      ∑ a, ∑ b, ‖(H - H') a b‖ ^ 2 := by
  rw [← frob_sq, ← frob_sq]
  have h := norm_exp_mul_exp_sub_one (-(Complex.I • H')) (Complex.I • H)
    (by simp [hH']) (by simp [hH])
  have e : -(Complex.I • H') + Complex.I • H = Complex.I • (H - H') := by
    rw [smul_sub]; abel
  rw [e, norm_smul, Complex.norm_I, one_mul] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

end

theorem exp_mul_exp_sub_one_le : ∀ (p q : ℕ) (H H' : Mat p q), Hᴴ = H → H'ᴴ = H' → ∑ a, ∑ b, ‖(NormedSpace.exp (-(Complex.I • H')) * NormedSpace.exp (Complex.I • H) - 1) a b‖ ^ 2 ≤ ∑ a, ∑ b, ‖(H - H') a b‖ ^ 2 :=
  fun _ _ H H' hH hH' => sum_sq_le H H' hH hH'

end GlobalTheory.CartanLip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleConstantEqOneDistributive
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.DistTriple

theorem bc_eq_one {D : D7} {T : Tor D} {N N' : ℕ} {A₁ A₂ A₃ : AddSubgroup (VC D N N')}
    (h₁ : Nice D T A₁) (h₂ : Nice D T A₂) (h₃ : Nice D T A₃) (hd : Dist A₁ A₂ A₃)
    {x y : VC D N N'} (hx : x ∈ A₂) (hy : y ∈ A₃) (hxy : y + x ∈ A₁) : bc D T y x = 1 := by
  have hm := hd x hx y hy (by rwa [add_comm])
  obtain ⟨x₁, hx₁, x₃, hx₃, rfl⟩ := AddSubgroup.mem_sup.1 hm
  have hy₃ : y + x₃ ∈ A₁ := by
    have := A₁.sub_mem hxy hx₁.1
    have e : y + (x₁ + x₃) - x₁ = y + x₃ := by abel
    rwa [e] at this
  have e1 := h₁.2.1 _ hy₃ _ hx₁.1
  rw [bc_add_left, h₂.2.1 _ hx₃.1 _ hx₁.2, mul_one] at e1
  rw [bc_add_right, e1, h₃.2.1 _ hy _ hx₃.2, mul_one]

theorem const_eq_one : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ A₃ : AddSubgroup (VC D N N'))
    (e : VC D N N' → ℂ) (μ : ℂ), Trip D T A₁ A₂ A₃ e μ → Dist A₁ A₂ A₃ → μ = 1 := by
  intro D T N N' A₁ A₂ A₃ e μ ht hd
  obtain ⟨r, hr, hs⟩ := GlobalTheory.T.thetaTripleConstant_eq_cocycle_sum D T N N' A₁ A₂ A₃ e μ ht
  obtain ⟨h₁, h₂, h₃, -, -, -, -, -, h8, -⟩ := ht
  have key : ∃ s : ℝ, 0 ≤ s ∧ μ * (r : ℂ) = (s : ℂ) := by
    rw [hs]
    refine finsum_induction (fun z : ℂ => ∃ s : ℝ, 0 ≤ s ∧ z = (s : ℂ)) ⟨0, le_rfl, by simp⟩ ?_ ?_
    · rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a + b, add_nonneg ha hb, by push_cast; rfl⟩
    · intro p
      split_ifs with h
      · exact ⟨1, zero_le_one, by
          rw [bc_eq_one h₁ h₂ h₃ hd (Quotient.out p.2 : A₂).2 (Quotient.out p.1 : A₃).2 h]; simp⟩
      · exact ⟨0, le_rfl, by simp⟩
  obtain ⟨s, hs0, hμ⟩ := key
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hμ' : μ = ((s / r : ℝ) : ℂ) := by
    push_cast; rw [eq_div_iff hr', hμ]
  rw [hμ'] at h8 ⊢
  have h8' : (s / r) ^ 8 = 1 := by exact_mod_cast h8
  have := (pow_eq_one_iff_of_nonneg (div_nonneg hs0 hr.le) (by norm_num)).1 h8'
  rw [this]; simp

end GlobalTheory.DistTriple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedWeylLatticeHermitianDualityStatement
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transported_weylLattice_hermitianDuality : NabDelDual := by
  first | exact @GlobalTheory.TransDual.nabDelDual | exact GlobalTheory.TransDual.nabDelDual | (intros; apply GlobalTheory.TransDual.nabDelDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilPairingGaloisEquivariantCmTorsionStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_galois_equivariant_cm_torsion : ∀ D : D7, WeilPairingGaloisAlt D := by
  first | exact @GlobalTheory.WeilPairingGalois.weilPairingGalois_all | exact GlobalTheory.WeilPairingGalois.weilPairingGalois_all | (intros; apply GlobalTheory.WeilPairingGalois.weilPairingGalois_all <;> assumption)
end

