import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0050
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0288
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1213
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrIdxProof2
section
section
open GlobalTheory.PsCo.PcEG

noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open Formalism.REAL (KG toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat Poly ev)

namespace GlobalTheory.PsCo.PcEF

theorem StrIdx_proof2 : StrIdx := by
  intro n ε P
  choose Qm hQm using fun s s' : Finset (Fin (n * n)) => ffMat_poly (ε := ε) s s'
  set Q : Poly n := ∑ s ∈ Finset.univ.filter (IsPhysSet ε), ((-1 : ℂ) ^ s.card) • Qm s s with hQdef
  have hQ : ∀ m : Mat n, ev m Q = physDet ε m := by
    intro m
    show MvPolynomial.eval (entVar m) Q = _
    rw [← strPhys_eq_physDet, strPhys, hQdef, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [MvPolynomial.smul_eval, hQm]
    rfl
  obtain ⟨d2, hd2⟩ : ∃ d2 : ℕ, ∀ s s' : Finset (Fin (n * n)), (P * Qm s s').totalDegree ≤ d2 :=
    ⟨∑ s, ∑ s', (P * Qm s s').totalDegree, fun s s' =>
      le_trans (Finset.single_le_sum (f := fun s' => (P * Qm s s').totalDegree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ s'))
      (Finset.single_le_sum (f := fun s => ∑ s', (P * Qm s s').totalDegree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ s))⟩
  refine ⟨max (P * Q).totalDegree d2, ?_⟩
  intro H _ _ _ σ D E hσ hD L _ hLK hLd Y _ hY0Y hYP hG hK B hB
  have hdeg1 : (P * Q).totalDegree ≤ max (P * Q).totalDegree d2 := le_max_left _ _
  have hdeg2 : ∀ s s', (P * Qm s s').totalDegree ≤ max (P * Q).totalDegree d2 := fun s s' =>
    (hd2 s s').trans (le_max_right _ _)
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  have : SecondCountableTopology (KG ε) := hemb.isInducing.secondCountableTopology
  have hφc : Continuous (fun k : KG ε => toMK k) := hemb.continuous
  have hφK : ∀ g : KG ε, toMK g ∈ Kset ε := fun g => g.2
  have hent : ∀ R : Poly n, Continuous fun k : KG ε => ev (toMK k) R := by
    intro R
    refine (MvPolynomial.continuous_eval R).comp (continuous_pi fun p => ?_)
    rcases p with p | p
    · exact (continuous_apply p.2).comp ((continuous_apply p.1).comp hφc)
    · exact continuous_star.comp ((continuous_apply p.2).comp ((continuous_apply p.1).comp hφc))
  have hBL : ∀ w, B w ∈ L.map D.subtype := by
    intro w
    rw [hB]
    have := hLd (P * Q) hdeg1 w
    simpa only [map_mul, hQ] using this
  refine ⟨hBL, ?_⟩
  have hAL : ∀ k : KG ε, ∀ x ∈ L.map D.subtype, σ (toMK k) x ∈ L.map D.subtype := by
    rintro k _ ⟨y, hy, rfl⟩
    exact ⟨sigD hD (hφK k) y, hLK _ (hφK k) y hy, rfl⟩
  have hAc : ∀ v, Continuous fun k : KG ε => σ (toMK k) v := fun v =>
    (hσ.2.2 v).comp_continuous hφc fun g => kset_mem_UJset (hφK g)
  have hcont : Continuous fun k : KG ε => ev (toMK k) P * physDet ε (toMK k) := by
    have := hent (P * Q)
    simpa only [map_mul, hQ] using this
  rw [trace_integral_restrict (μ := muK ε) (L.map D.subtype) hcont (fun k => σ (toMK k)) hAc hAL B hB
    (fun x _ => hBL x)]
  have hY0G : ∀ y ∈ tensFock (n := n) L ⊓ physicalSubspace (N := D) ε, gradT y ∈ tensFock (n := n) L ⊓ physicalSubspace (N := D) ε :=
    fun y hy => ⟨tensFock_lTensor_stable _ hy.1, (physSub_stable ε E).2.2.2.2 y hy.2⟩
  have hY0K : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ tensFock (n := n) L ⊓ physicalSubspace (N := D) ε,
      wK hD hk y ∈ tensFock (n := n) L ⊓ physicalSubspace (N := D) ε := fun k hk y hy =>
    ⟨wK_tensFock hD hk (hLK k hk) hy.1, wK_physSub hD hk hy.2⟩
  have hpt : ∀ k : KG ε, ev (toMK k) P * physDet ε (toMK k) *
      LinearMap.trace ℂ (L.map D.subtype) (((σ (toMK k) : H →L[ℂ] H) : H →ₗ[ℂ] H).restrict (hAL k)) =
      ev (toMK k) P * LinearMap.trace ℂ ↥(tensFock (n := n) L ⊓ physicalSubspace (N := D) ε)
        ((gradT ∘ₗ wK hD (hφK k)).restrict (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))) := by
    intro k
    rw [trace_map_subtype (sigD hD (hφK k)) (fun x hx => hLK _ (hφK k) x hx) _ _ (fun x => rfl)]
    have := str_tensFock_physSub hD (hφK k) (fun x hx => hLK _ (hφK k) x hx)
      (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))
    rw [show LinearMap.trace ℂ ↥(tensFock (n := n) L ⊓ physicalSubspace (N := D) ε)
        ((gradT ∘ₗ wK hD (hφK k)).restrict (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))) = _ from this]
    ring
  simp_rw [hpt]
  have hcP := hent P
  have hrange := fun y => btot_range (μ := muK ε) hσ hD hK (L := L) hφc hφK hcP
    (fun s s' u => by
      have h1 := hLd (P * Qm s s') (hdeg2 s s') u
      have h2 : ∫ k : KG ε, (ev (toMK k) P * ffMat ε (toMK k) s s') • σ (toMK k) u ∂(muK ε) =
          ∫ k : KG ε, ev (toMK k) (P * Qm s s') • σ (toMK k) u ∂(muK ε) := by
        congr 1
        funext k
        rw [map_mul, hQm]
        rfl
      rw [h2]
      exact h1) hYP y
  exact (int_str_eq (μ := muK ε) hσ hD hY0Y hK hY0K hG hY0G hφc hφK hcP hrange).symm

end GlobalTheory.PsCo.PcEF

end
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubBundleCurvatureRankOne
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

namespace GlobalTheory.LineRankTwo

theorem chernOne_sub_quot_line {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m]
    [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsPosFrame U H)
    (hz : z ∈ U) (hm : Fintype.card m = 1) (hl : Fintype.card l = 1)
    (hg : ∀ ξ η, curv (gramS H) z ξ η = blockSS (H z) (curv H z ξ η) +
      wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ η)
    (hc : ∀ ξ η, chernOne H z ξ η = chernOne (gramS H) z ξ η + chernOne (gramQ H) z ξ η)
    (u : m → ℂ) (hu : u ≠ 0) (ξ η : V) :
    chernOne (gramS H) z ξ η = lineCurv H z (incl m l *ᵥ u) ξ η - extTrace H z ξ η ∧
    chernOne (gramQ H) z ξ η =
      chernOne H z ξ η - lineCurv H z (incl m l *ᵥ u) ξ η + extTrace H z ξ η := by
  have hzH : (H z).PosDef := h.posDef z hz
  have hS : (subGram (H z)).PosDef := posDef_subGram hzH
  have hsu : IsUnit (subGram (H z)).det := (isUnit_iff_isUnit_det _).1 hS.isUnit
  have hSu : form (subGram (H z)) u u ≠ 0 := ((posDef_iff.1 hS).2 u hu).ne'
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.1 hm
  have hvec : ∀ M : Matrix m m ℂ, M *ᵥ u = M.trace • u := by
    intro M
    funext i
    rw [ha i]
    simp only [mulVec, dotProduct, trace, diag, Pi.smul_apply, smul_eq_mul]
    rw [Fintype.sum_eq_single a (fun j hj => absurd (ha j) hj),
      Fintype.sum_eq_single a (fun j hj => absurd (ha j) hj)]
  have hline : lineCurv H z (incl m l *ᵥ u) ξ η = kappa * (blockSS (H z) (curv H z ξ η)).trace := by
    have e1 : curv H z ξ η *ᵥ (incl m l *ᵥ u) = incl m l *ᵥ (blockSS (H z) (curv H z ξ η) *ᵥ u) +
        orthLift (H z) *ᵥ (quotMap m l *ᵥ (curv H z ξ η *ᵥ (incl m l *ᵥ u))) := by
      conv_lhs => rw [← Matrix.one_mulVec (curv H z ξ η *ᵥ _), ← incl_mul_orthProj_add (H z)]
      simp only [Matrix.add_mulVec, mulVec_mulVec, blockSS, Matrix.mul_assoc, Matrix.add_mul]
    rw [lineCurv, e1, form_add_left, form_orthLift_incl hsu, add_zero, form_incl, form_incl, hvec,
      form_smul_left, mul_div_assoc, div_self hSu, mul_one]
  have hp : ∀ᶠ x in 𝓝 z, (H x).PosDef :=
    Filter.eventually_of_mem (h.isOpen.mem_nhds hz) fun x hx => h.posDef x hx
  have hext : extTrace H z ξ η = kappa * (secondForm H z ξ * secondFormAdj H z η).trace :=
    extTrace_eq (h.isHermFrame.one hz) hp ξ η
  have h1 : chernOne (gramS H) z ξ η =
      lineCurv H z (incl m l *ᵥ u) ξ η - extTrace H z ξ η := by
    rw [chernOne, hg, hline, hext, wedgeAntiHol, trace_add, trace_neg,
      trace_mul_comm (secondFormAdj H z η)]
    ring
  refine ⟨h1, ?_⟩
  rw [hc ξ η, h1]
  ring

end GlobalTheory.LineRankTwo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubbundleCurvatureFormula
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section

namespace GlobalTheory.SubGauss

variable {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

theorem orthProj_transpose_mul_subGram (K : Matrix (m ⊕ l) (m ⊕ l) ℂ)
    (hs : IsUnit (subGram K).det) : (orthProj K)ᵀ * subGram K = K * incl m l := by
  have hc : (orthCoeff K)ᵀ = K.toBlocks₂₁ * K.toBlocks₁₁⁻¹ := by
    simp [orthCoeff, transpose_nonsing_inv]
  rw [orthProj, transpose_fromCols, transpose_one, fromRows_mul, hc,
    subGram, nonsing_inv_mul_cancel_right K.toBlocks₁₁ _ hs]
  conv_rhs => rw [← fromBlocks_toBlocks K]
  simp [incl, fromBlocks_mul_fromRows, subGram]

theorem incl_transpose_mul_mul (M : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    (incl m l)ᵀ * M * incl m l = M.toBlocks₁₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  simp [incl, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

theorem conn_gramS {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {x : V} (hu : IsUnit (H x).det)
    (hs : IsUnit (subGram (H x)).det) (ξ : V) :
    conn (gramS H) x ξ = orthProj (H x) * (conn H x ξ * incl m l) := by
  refine (eq_conn_of_compatible (H := gramS H) hs ?_).symm
  have e : mdel (gramS H) x ξ = (mdel H x ξ).toBlocks₁₁ := by ext a b; rfl
  rw [e, ← incl_transpose_mul_mul, ← conn_transpose_mul hu, transpose_mul, transpose_mul,
    Matrix.mul_assoc, Matrix.mul_assoc, gramS, orthProj_transpose_mul_subGram _ hs]
  simp only [Matrix.mul_assoc]

theorem mContDiffAt_orthProj {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} {k : WithTop ℕ∞}
    (h : MContDiffAt k H z) (hs : IsUnit (subGram (H z)).det) :
    MContDiffAt k (fun x => orthProj (H x)) z := by
  have hc : MContDiffAt k (fun x => orthCoeff (H x)) z :=
    (h.subGram.transpose.inv (by rwa [det_transpose])).mul (h.submatrix Sum.inr Sum.inl).transpose
  rintro a (b | b)
  · simpa [orthProj] using (contDiffAt_const : ContDiffAt ℝ k (fun _ : V => (1 : Matrix m m ℂ) a b) z)
  · simpa [orthProj] using hc a b

theorem mdbar_orthProj {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : MContDiffAt 1 H z)
    (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian) (hu : IsUnit (H z).det)
    (hs : IsUnit (subGram (H z)).det) (η : V) :
    mdbar (fun x => orthProj (H x)) z η = secondFormAdj H z η * quotMap m l := by
  have e1 : mdbar (fun x => orthProj (H x)) z η =
      fromCols 0 (mdbar (fun x => orthCoeff (H x)) z η) := by
    ext a (b | b) <;> simp [orthProj]
  have e2 : mdbar (fun x => orthCoeff (H x)) z η = secondFormAdj H z η := by
    rw [← neg_neg (mdbar _ z η), ← extForm_eq_neg_mdbar, extForm_eq_neg_secondFormAdj h hh hu hs,
      neg_neg]
  rw [e1, e2, quotMap, mul_fromCols]
  simp

theorem curv_gramS {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H)
    (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V) :
    curv (gramS H) z ξ η = blockSS (H z) (curv H z ξ η) +
      wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ η := by
  have hU : U ∈ 𝓝 z := h.isOpen.mem_nhds hz
  have h2 := h.two hz
  have h1 := h.one hz
  have hθ : MContDiffAt 1 (fun x => conn H x ξ) z :=
    h2.conn (h.isUnit z hz) (by norm_num) ξ
  have hP : MContDiffAt 1 (fun x => orthProj (H x)) z := mContDiffAt_orthProj h1 (hs z hz)
  have he : (fun x => conn (gramS H) x ξ) =ᶠ[𝓝 z]
      fun x => orthProj (H x) * (conn H x ξ * incl m l) :=
    Filter.mem_of_superset hU fun x hx => conn_gramS (h.isUnit x hx) (hs x hx) ξ
  have hB : mdbar (fun x => conn H x ξ * incl m l) z η = mdbar (fun x => conn H x ξ) z η * incl m l := by
    rw [mdbar_mul hθ (mContDiffAt_const _), mdbar_const, Matrix.mul_zero, zero_add]
  rw [curv, mdbar_congr he, mdbar_mul hP (hθ.mul (mContDiffAt_const _)), hB,
    mdbar_orthProj h1 (h.eventually_herm hz) (h.isUnit z hz) (hs z hz), blockSS, curv,
    wedgeAntiHol, secondForm, blockQS]
  simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, neg_add]

end GlobalTheory.SubGauss
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageLinearTranslateConst
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.AvgLin

theorem avg_linear_translate_const : ∀ (H : Type) [Group H] (u v : H → ℂ) (c : ℂ) (g : H), (rStab u).index ≠ 0 → (rStab v).index ≠ 0 → avg (u + v) = avg u + avg v ∧ avg (c • u) = c * avg u ∧ avg (fun x => u (g * x)) = avg u ∧ avg (fun _ : H => c) = c := by
  intro H _ u v c g hu hv
  set S : Subgroup H := rStab u ⊓ rStab v with hS
  have hSi : S.index ≠ 0 := Subgroup.index_inf_ne_zero hu hv
  haveI : S.FiniteIndex := ⟨hSi⟩
  haveI : (rStab u).FiniteIndex := ⟨hu⟩
  have hSu : S ≤ rStab u := inf_le_left
  have hSv : S ≤ rStab v := inf_le_right
  have hSuv : S ≤ rStab (u + v) := by
    intro k hk x
    simp only [Pi.add_apply]
    rw [hSu hk x, hSv hk x]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [GlobalTheory.T.avg_eq_of_le_rightStabiliser H (u + v) S hSuv hSi, GlobalTheory.T.avg_eq_of_le_rightStabiliser H u S hSu hSi, GlobalTheory.T.avg_eq_of_le_rightStabiliser H v S hSv hSi,
      ← mul_add]
    congr 1
    simp only [Pi.add_apply]
    exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)
  · have hc : rStab u ≤ rStab (c • u) := by
      intro k hk x
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hk x]
    rw [GlobalTheory.T.avg_eq_of_le_rightStabiliser H (c • u) (rStab u) hc hu, GlobalTheory.T.avg_eq_of_le_rightStabiliser H u (rStab u) le_rfl hu]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_finsum]
    ring
  · have ht : rStab u ≤ rStab (fun x => u (g * x)) := by
      intro k hk x
      simp only
      rw [← mul_assoc, hk (g * x)]
    rw [GlobalTheory.T.avg_eq_of_le_rightStabiliser H _ (rStab u) ht hu, GlobalTheory.T.avg_eq_of_le_rightStabiliser H u (rStab u) le_rfl hu]
    congr 1
    have key : ∀ q : H ⧸ rStab u, u (g * q.out) = u (g • q).out := by
      intro q
      have : g • q = (QuotientGroup.mk (g * q.out) : H ⧸ rStab u) := by
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      rw [this]
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (rStab u) (g * q.out)
      rw [hh, h.2]
    simp_rw [key]
    exact finsum_comp_equiv (MulAction.toPerm g : Equiv.Perm (H ⧸ rStab u)) (f := fun q => u q.out)
  · have htop : (⊤ : Subgroup H) ≤ rStab (fun _ : H => c) := by
      intro k _ x
      rfl
    rw [GlobalTheory.T.avg_eq_of_le_rightStabiliser H _ ⊤ htop (by simp)]
    simp only [Subgroup.index_top, Nat.cast_one, inv_one, one_mul]
    rw [finsum_eq_single (fun _ => c) (1 : H ⧸ (⊤ : Subgroup H))]
    intro x hx
    exact absurd (QuotientGroup.subsingleton_quotient_top.elim x 1) hx

end GlobalTheory.AvgLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageProdMulEqMul
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.AvgProd

lemma apply_out_rStab {H : Type} [Group H] (u : H → ℂ) (x : H) :
    u ((x : H ⧸ rStab u).out) = u x := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (rStab u) x
  rw [hk]
  have hk' : ∀ y, u (y * (k : H)) = u y := k.2
  exact hk' x

theorem avg_prod : ∀ (H H' : Type) [Group H] [Group H'] (u : H → ℂ) (v : H' → ℂ), (rStab u).index ≠ 0 →
    (rStab v).index ≠ 0 → avg (fun x : H × H' => u x.1 * v x.2) = avg u * avg v := by
  intro H H' _ _ u v hu hv
  set S : Subgroup (H × H') := (rStab u).prod (rStab v) with hS
  have hle : S ≤ rStab (fun x : H × H' => u x.1 * v x.2) := by
    intro p hp
    rw [hS, Subgroup.mem_prod] at hp
    have ha : ∀ y, u (y * p.1) = u y := hp.1
    have hb : ∀ y, v (y * p.2) = v y := hp.2
    intro x
    simp only [Prod.fst_mul, Prod.snd_mul]
    rw [ha x.1, hb x.2]
  have hSi : S.index = (rStab u).index * (rStab v).index := Subgroup.index_prod _ _
  have hS0 : S.index ≠ 0 := by rw [hSi]; exact mul_ne_zero hu hv
  rw [GlobalTheory.T.avg_eq_of_le_rightStabiliser _ _ S hle hS0]
  haveI : (rStab u).FiniteIndex := ⟨hu⟩
  haveI : (rStab v).FiniteIndex := ⟨hv⟩
  haveI : S.FiniteIndex := ⟨hS0⟩
  letI : Fintype (H ⧸ rStab u) := Fintype.ofFinite _
  letI : Fintype (H' ⧸ rStab v) := Fintype.ofFinite _
  letI : Fintype ((H × H') ⧸ S) := Fintype.ofFinite _
  let f : (H × H') ⧸ S → (H ⧸ rStab u) × (H' ⧸ rStab v) :=
    fun q => ((q.out.1 : H ⧸ rStab u), (q.out.2 : H' ⧸ rStab v))
  have hf : Function.Bijective f := by
    constructor
    · intro q q' h
      simp only [f, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [QuotientGroup.eq] at h1 h2
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]
      exact (Subgroup.mem_prod (H := rStab u) (K := rStab v)).2 ⟨by simpa using h1, by simpa using h2⟩
    · rintro ⟨a, b⟩
      induction a using QuotientGroup.induction_on with | H x => ?_
      induction b using QuotientGroup.induction_on with | H y => ?_
      refine ⟨((x, y) : (H × H') ⧸ S), ?_⟩
      have h := QuotientGroup.out_eq' ((x, y) : (H × H') ⧸ S)
      rw [QuotientGroup.eq] at h
      replace h := (Subgroup.mem_prod (H := rStab u) (K := rStab v)).1 h
      simp only [f, Prod.mk.injEq]
      rw [QuotientGroup.eq, QuotientGroup.eq]
      exact ⟨by simpa using h.1, by simpa using h.2⟩
  have hsum : ∑ᶠ q : (H × H') ⧸ S, (fun x : H × H' => u x.1 * v x.2) q.out =
      (∑ᶠ a : H ⧸ rStab u, u a.out) * ∑ᶠ b : H' ⧸ rStab v, v b.out := by
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.sum_mul_sum,
      ← Fintype.sum_prod_type']
    refine Fintype.sum_bijective f hf _ _ ?_
    intro q
    simp only [f, apply_out_rStab]
  rw [hsum]
  unfold avg
  rw [hSi]
  push_cast
  rw [mul_inv]
  ring

end GlobalTheory.AvgProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupertraceCarriedByDiracKernel
section
noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open GlobalTheory.PsCo.Pc1 (Mat)

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

set_option maxHeartbeats 1000000 in
theorem supertrace_carriedBy_diracKernel : StrKer := by
  intro n ε H _ _ σ D E hσ hD Y _ hY hG hK
  classical
  let Z : Submodule ℂ (TensorProduct ℂ D (Fock n)) := Y ⊓ LinearMap.ker (dD ε E)
  have hZY : Z ≤ Y := inf_le_left
  haveI hZf : FiniteDimensional ℂ Z := Submodule.finiteDimensional_of_le hZY
  have hZK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Z, wK hD hk y ∈ Z := by
    intro k hk y hy
    refine ⟨hK k hk y hy.1, ?_⟩
    have h0 : dD ε E y = 0 := hy.2
    show dD ε E (wK hD hk y) = 0
    rw [← wK_D hσ hD hk, h0, map_zero]
  have hZG : ∀ y ∈ Z, gradT y ∈ Z := by
    intro y hy
    refine ⟨hG y hy.1, ?_⟩
    have h0 : dD ε E y = 0 := hy.2
    show dD ε E (gradT y) = 0
    have := gradT_D (ε := ε) E y
    rw [h0, map_zero] at this
    exact neg_eq_zero.1 this.symm
  let Γ : TSub Z →ₗ[ℂ] TSub Z := ((gradT.restrict hZG : Z →ₗ[ℂ] Z) : TSub Z →ₗ[ℂ] TSub Z)
  refine ⟨Z, hZf, hZK, Γ, hZY, fun y hy => hy.2, fun k hk => ?_⟩
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  let Dl : TSub Y →ₗ[ℂ] TSub Y := (((dD ε E).restrict hY : Y →ₗ[ℂ] Y) : TSub Y →ₗ[ℂ] TSub Y)
  let Γy : TSub Y →ₗ[ℂ] TSub Y := ((gradT.restrict hG : Y →ₗ[ℂ] Y) : TSub Y →ₗ[ℂ] TSub Y)
  let B : TSub Y →ₗ[ℂ] TSub Y := (((wK hD hk).restrict (hK k hk) : Y →ₗ[ℂ] Y) : TSub Y →ₗ[ℂ] TSub Y)
  obtain ⟨hker, htr⟩ := str_eq_str_ker Dl Γy B
    (fun x y => by rw [tsub_inner, tsub_inner]; exact tform_D hU _ _)
    (fun x => Subtype.ext (gradT_D E _)) (fun x => Subtype.ext (wK_D hσ hD hk _))
  have h1 : LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD hk).restrict (fun y hy => hG _ (hK k hk y hy))) =
      LinearMap.trace ℂ (TSub Y) (Γy ∘ₗ B) := rfl
  rw [h1, htr]
  have hmemZ : ∀ x : LinearMap.ker Dl, tsubVal Y (x : TSub Y) ∈ Z := by
    intro x
    have hx : Dl (x : TSub Y) = 0 := x.2
    exact ⟨tsubVal_mem (x : TSub Y), congrArg (tsubVal Y) hx⟩
  let f : LinearMap.ker Dl →ₗ[ℂ] TSub Z :=
    { toFun := fun x => ((⟨tsubVal Y (x : TSub Y), hmemZ x⟩ : Z) : TSub Z)
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have : tsubVal Y (x : TSub Y) = tsubVal Y (y : TSub Y) := congrArg (tsubVal Z) hxy
      exact Subtype.ext (tsubVal_injective this)
    · intro z
      have hzY : tsubVal Z z ∈ Y := hZY (tsubVal_mem z)
      let x : TSub Y := ((⟨tsubVal Z z, hzY⟩ : Y) : TSub Y)
      have hx : x ∈ LinearMap.ker Dl := by
        rw [LinearMap.mem_ker]
        apply tsubVal_injective
        rw [map_zero]
        exact (tsubVal_mem z).2
      exact ⟨⟨x, hx⟩, rfl⟩
  let e := LinearEquiv.ofBijective f hf
  rw [← LinearMap.trace_conj' _ e]
  congr 1
  apply LinearMap.ext
  intro z
  rw [LinearEquiv.conj_apply_apply]
  apply tsubVal_injective
  obtain ⟨x, rfl⟩ := e.surjective z
  rw [LinearEquiv.symm_apply_apply]
  show tsubVal Z (f ((Γy ∘ₗ B).restrict hker x)) = tsubVal Z (Γ (tOp hD hZK k (f x)))
  have hΓ : ∀ w : TSub Z, tsubVal Z (Γ w) = gradT (tsubVal Z w) := fun w => rfl
  rw [hΓ, tOp_apply hD hZK hk]
  rfl

end GlobalTheory.PsCo.PcEF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimGen
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Vert GlobalTheory.Vert.Model GlobalTheory.VB

namespace GlobalTheory.Vert.Model

theorem topologicalKrullDim_gen : ∀ (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Z : Model O), topologicalKrullDim Z.gen.toScheme = Z.relDim := by
  intro O _ _ _ Z
  obtain ⟨q, H⟩ := Z.exists_isPullback_gen (FractionRing O)
  obtain ⟨d, hd, -⟩ := exists_topologicalKrullDim_fibres_eq_of_isPullback Z.str (FractionRing O)
    (IsLocalRing.ResidueField O) IsLocalRing.residue_surjective (IsPullback.of_hasPullback _ _) H
  rw [hd, relDim_eq_iff.2
    (IntModel.topologicalKrullDim_eq_succ (IsDiscreteValuationRing.not_isField O) H hd)]

end GlobalTheory.Vert.Model
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceFormGramAsymmetryForcesBetaRelationStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceFormGram_asymmetry_forces_beta_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A) (u β : B.A), (Algebra.traceForm K.E B.A).Nondegenerate → IsUnit (GlobalTheory.TwLat.gram e b β) → (cj w).mapMatrix (GlobalTheory.TwLat.gram e b β) = (-1 : w.adicCompletion E) ^ (m - 1) • ((GlobalTheory.TwLat.gram e b β)ᵀ * GlobalTheory.TwLat.mulMat e b u) → B.σ β = β * ((-1) ^ (m - 1) * u) ∧ IsUnit β := by
  first | exact @GlobalTheory.TwLat.betaSym | exact GlobalTheory.TwLat.betaSym | (intros; apply GlobalTheory.TwLat.betaSym <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffHolomorphicFrameChangeStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transgressionTopCoeff_holomorphic_frame_change : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (ρ : V n → ℝ) {G₀ G₁ A : V n → Matrix r r ℂ} {v : V n}, MContDiffAt 2 G₀ v → IsUnit (G₀ v).det → MContDiffAt 2 G₁ v → IsUnit (G₁ v).det → MContDiffAt 2 A v → IsUnit (A v).det → (∀ᶠ x in 𝓝 v, ∀ η, mdbar A x η = 0) → corrC ρ (fun x => (A x)ᵀ * G₀ x * (A x)ᴴᵀ) (fun x => (A x)ᵀ * G₁ x * (A x)ᴴᵀ) v = corrC ρ G₀ G₁ v := by
  first | exact @GlobalTheory.GoodTop.corrC_changeFrame | exact GlobalTheory.GoodTop.corrC_changeFrame | (intros; apply GlobalTheory.GoodTop.corrC_changeFrame <;> assumption)
end

