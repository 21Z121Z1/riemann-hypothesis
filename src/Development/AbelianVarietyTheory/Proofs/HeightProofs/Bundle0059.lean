import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0057
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0234
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0351
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0236
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0070

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CasimirUnitaryGroupActsByScalarSmoothVectors
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TypeSum.CasBasis

theorem casimir_scalar : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ χ : ℂ, ∀ v, Sm ε σ v → ∑ b, dRep σ (pB ε b) (dRep σ (pB ε b) v) = χ • v + ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) v) := by
  intro n ε H _ _ _ σ h
  obtain ⟨hX, hY⟩ := GlobalTheory.T.orthonormalBases_mem_unitaryLieAlgebra n ε
  have hG := GlobalTheory.T.casimirDifferenceOperator_equivariant n ε H σ h
  obtain ⟨u, χ, hu, hu0, hχ⟩ := GlobalTheory.T.exists_smooth_eigenvector_casimirDifferenceOperator n ε H σ _ _ (kB ε) (pB ε) h hX hY fun k hk v hv => hG k (K_le_UJ hk) v hv
  have hχr : (starRingEnd ℂ) χ = χ := by
    have e := inner_casOp h.1 hX hY hu hu
    rw [hχ, inner_smul_left, inner_smul_right] at e
    have hne : ⟪u, u⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hu0
    exact (mul_right_cancel₀ hne e).symm
  refine ⟨χ, fun v hv => ?_⟩
  have hws : Sm ε σ (casOp σ (kB ε) (pB ε) v - χ • v) :=
    (smooth (Jm ε) σ).sub_mem (sm_casOp h.1 hX hY hv) ((smooth (Jm ε) σ).smul_mem χ hv)
  have h0 : ∀ g ∈ UJset ε,
      ((innerSL ℂ (casOp σ (kB ε) (pB ε) v - χ • v) : H →L[ℂ] ℂ) : H →ₗ[ℂ] ℂ) (σ g u) = 0 := by
    intro g hg
    have hgu := hu.translate h.1 hg
    simp only [ContinuousLinearMap.coe_coe, innerSL_apply_apply, inner_sub_left, inner_smul_left, hχr]
    rw [← inner_casOp h.1 hX hY hv hgu, hG g hg u hu, hχ, map_smul, inner_smul_right, sub_self]
  have hz := h.eq_zero_of_orbit (sobCont_inner _) hu hu0 h0 hws
  simp only [ContinuousLinearMap.coe_coe, innerSL_apply_apply, inner_self_eq_zero] at hz
  simp only [casOp, sub_sub, sub_eq_zero] at hz
  rw [hz, add_comm]

end GlobalTheory.TypeSum.CasBasis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CoefBoundTwoFinSum
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TypeSum

open GlobalTheory.LowTypeDetermined

section SobSum

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem sobCont_zero_form : Sobolev₂ (lieSet ε) σ (0 : H →ₗ[ℂ] ℂ) :=
  ⟨[], 0, by simp, fun w _ => by simp⟩

theorem sobCont_add_form {ℓ ℓ' : H →ₗ[ℂ] ℂ} (h : Sobolev₂ (lieSet ε) σ ℓ) (h' : Sobolev₂ (lieSet ε) σ ℓ') :
    Sobolev₂ (lieSet ε) σ (ℓ + ℓ') := by
  obtain ⟨S, C, hS, hC⟩ := h
  obtain ⟨S', C', hS', hC'⟩ := h'
  refine ⟨S ++ S', |C| + |C'|, words_append hS hS', fun w hw => ?_⟩
  have n1 := sobNorm_nonneg σ S w
  have n2 := sobNorm_nonneg σ S' w
  have b1 : ‖ℓ w‖ ≤ C * sobNorm σ S w := hC w hw
  have b2 : ‖ℓ' w‖ ≤ C' * sobNorm σ S' w := hC' w hw
  show ‖ℓ w + ℓ' w‖ ≤ (|C| + |C'|) * sobNorm σ (S ++ S') w
  rw [sobNorm_append]
  have a1 : C * sobNorm σ S w ≤ |C| * sobNorm σ S w := mul_le_mul_of_nonneg_right (le_abs_self C) n1
  have a2 : C' * sobNorm σ S' w ≤ |C'| * sobNorm σ S' w := mul_le_mul_of_nonneg_right (le_abs_self C') n2
  have a3 := abs_nonneg C
  have a4 := abs_nonneg C'
  calc ‖ℓ w + ℓ' w‖ ≤ ‖ℓ w‖ + ‖ℓ' w‖ := norm_add_le _ _
    _ ≤ _ := by nlinarith

theorem sobCont_smul_form (c : ℂ) {ℓ : H →ₗ[ℂ] ℂ} (h : Sobolev₂ (lieSet ε) σ ℓ) :
    Sobolev₂ (lieSet ε) σ (c • ℓ) := by
  obtain ⟨S, C, hS, hC⟩ := h
  refine ⟨S, ‖c‖ * C, hS, fun w hw => ?_⟩
  have b : ‖ℓ w‖ ≤ C * sobNorm σ S w := hC w hw
  show ‖c • ℓ w‖ ≤ ‖c‖ * C * sobNorm σ S w
  rw [norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left b (norm_nonneg c)

theorem sobCont_sum_form {ι : Type} (s : Finset ι) (f : ι → H →ₗ[ℂ] ℂ) (h : ∀ i, Sobolev₂ (lieSet ε) σ (f i)) :
    Sobolev₂ (lieSet ε) σ (∑ i ∈ s, f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using (sobCont_zero_form (ε := ε) (σ := σ) (H := H))
  · intro i s hi ih
    rw [Finset.sum_insert hi]
    exact sobCont_add_form (h i) ih

end SobSum

theorem coefBound_two_finSum : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → CoefBound ε σ → ∀ N : ℕ, ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ (p : ℕ) (ℓ : Fin p → (H →ₗ[ℂ] ℂ)) (x : Fin p → H), (∀ j, Sobolev₂ (lieSet ε) σ (ℓ j)) → (∀ j, Sm ε σ (x j)) → ∀ M : ℝ, 0 ≤ M → (∀ y ∈ UJset ε, ‖∑ j, ℓ j (σ y (x j))‖ ≤ M * (1 + hs y) ^ N) → ∀ b w, Sm ε σ b → Sm ε σ w → ‖∑ j, ⟪b, x j⟫_ℂ * ℓ j w‖ ≤ C * M * sobNorm σ S b * sobNorm σ S w := by
  intro n ε H _ _ _ σ h hB N
  have hσ := h.1
  obtain ⟨a, c, ha0, hc0, haK, hcK, Z, C₀, hZ, hZU, hC₀, hA⟩ := exists_rank_one_isAvg n ε H σ h
  have ha : Sm ε σ a := h.2.2.1 a haK
  have hc : Sm ε σ c := h.2.2.1 c hcK
  obtain ⟨S, C₁, hS, hC₁, hb2⟩ := coefBound_two n ε H σ h hB a c ha ha0 hc hc0 N
  obtain ⟨K₀, hK₀⟩ := hZ.exists_bound_of_continuousOn
    (f := fun y : Mx n => (1 + hs y) ^ N) ((continuous_const.add continuous_hs).pow N).continuousOn
  set K := max K₀ 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hK : ∀ y ∈ Z, (1 + hs y) ^ N ≤ K := fun y hy =>
    ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hK₀ y hy)).trans (le_max_left _ _)
  refine ⟨S, C₁ * C₀ * K, hS, mul_nonneg (mul_nonneg hC₁ hC₀) hK0, ?_⟩
  intro p ℓ x hℓ hx M hM hgr b w hb hw
  let γ : H → H → ℂ := fun b w => ∑ j, ⟪b, x j⟫_ℂ * ℓ j w
  have h1 : ∀ b, Sm ε σ b → SobFun ε σ (γ b) := by
    intro b _
    have hL := sobCont_sum_form (ε := ε) (σ := σ) Finset.univ (fun j => ⟪b, x j⟫_ℂ • ℓ j)
      (fun j => sobCont_smul_form _ (hℓ j))
    have e : γ b = ⇑(∑ j, ⟪b, x j⟫_ℂ • ℓ j) := by
      funext w
      simp [γ, LinearMap.sum_apply]
    rw [e]
    exact sobFun_of_sobCont hL
  have h2 : ∀ w, Sm ε σ w → SobFun ε σ (fun b => star (γ b w)) := by
    intro w _
    have hL := sobCont_sum_form (ε := ε) (σ := σ) Finset.univ
      (fun j => star (ℓ j w) • (innerSL ℂ (x j) : H →ₗ[ℂ] ℂ)) (fun j => sobCont_smul_form _ (sobCont_inner _))
    have e : (fun b => star (γ b w)) = ⇑(∑ j, star (ℓ j w) • (innerSL ℂ (x j) : H →ₗ[ℂ] ℂ)) := by
      funext b
      simp only [γ, star_sum, LinearMap.sum_apply, LinearMap.smul_apply,
        ContinuousLinearMap.coe_coe, innerSL_apply_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [star_mul', mul_comm, ← inner_conj_symm, starRingEnd_apply, star_star]
    rw [e]
    exact sobFun_of_sobCont hL
  have h3 : ∀ g ∈ UJset ε, ∀ g' ∈ UJset ε,
      ‖γ (σ g' c) (σ g a)‖ ≤ (C₀ * K * M) * (1 + hs g) ^ N * (1 + hs g') ^ N := by
    intro g hg g' hg'
    have hg'i := inv_mem_UJ hg'
    have hinv : g'⁻¹⁻¹ = g' :=
      Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_UJ hg'))
    have e : γ (σ g' c) (σ g a) =
        ∑ j, (ℓ j ∘ₗ (σ g : H →ₗ[ℂ] H)) ((fun v => ⟪c, v⟫_ℂ • a) (σ g'⁻¹ (x j))) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have hi := inner_sigma hσ hg'i c (x j)
      rw [hinv] at hi
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, map_smul, smul_eq_mul]
      rw [hi]
    have P0 : 0 ≤ (1 + hs g) ^ N := pow_nonneg (by linarith [hs_nonneg g]) N
    have P1 : 0 ≤ (1 + hs g') ^ N := pow_nonneg (by linarith [hs_nonneg g']) N
    have hbd : ∀ y ∈ Z, ‖∑ j, (ℓ j ∘ₗ (σ g : H →ₗ[ℂ] H)) (σ y (σ g'⁻¹ (x j)))‖ ≤
        M * K * (1 + hs g) ^ N * (1 + hs g') ^ N := by
      intro y hy
      have hyU := hZU hy
      have hm : g * y * g'⁻¹ ∈ UJset ε := mul_mem_UJ (mul_mem_UJ hg hyU) hg'i
      have e2 : ∀ j, (ℓ j ∘ₗ (σ g : H →ₗ[ℂ] H)) (σ y (σ g'⁻¹ (x j))) = ℓ j (σ (g * y * g'⁻¹) (x j)) := fun j => by
        simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
        rw [sigma_mul hσ (mul_mem_UJ hg hyU) hg'i, sigma_mul hσ hg hyU]
      simp only [e2]
      refine (hgr _ hm).trans ?_
      have q1 := one_add_hs_mul_le (g * y) g'⁻¹
      have q2 := one_add_hs_mul_le g y
      rw [hs_inv hg'] at q1
      have hy0 := hs_nonneg y
      have hgg := hs_nonneg g
      have hgg' := hs_nonneg g'
      have q : 1 + hs (g * y * g'⁻¹) ≤ (1 + hs g) * (1 + hs y) * (1 + hs g') :=
        q1.trans (mul_le_mul_of_nonneg_right q2 (by linarith))
      have qN : (1 + hs (g * y * g'⁻¹)) ^ N ≤ (1 + hs g) ^ N * (1 + hs y) ^ N * (1 + hs g') ^ N := by
        rw [← mul_pow, ← mul_pow]
        exact pow_le_pow_left₀ (by linarith [hs_nonneg (g * y * g'⁻¹)]) q N
      have hKy := hK y hy
      calc M * (1 + hs (g * y * g'⁻¹)) ^ N ≤ M * ((1 + hs g) ^ N * (1 + hs y) ^ N * (1 + hs g') ^ N) :=
            mul_le_mul_of_nonneg_left qN hM
        _ ≤ M * ((1 + hs g) ^ N * K * (1 + hs g') ^ N) := by gcongr
        _ = _ := by ring
    have key := avgBd_sobCont n ε H σ h (fun v => ⟪c, v⟫_ℂ • a) Z C₀ hZ hZU hC₀ hA (Fin p)
      (fun j => ℓ j ∘ₗ (σ g : H →ₗ[ℂ] H)) (fun j => σ g'⁻¹ (x j))
      (fun j => sobCont_translate hσ (hℓ j) hg) (fun j => (hx j).translate hσ hg'i)
      (fun j => sm_iff.2 ((smooth (Jm ε) σ).smul_mem _ (sm_iff.1 ha)))
      (M * K * (1 + hs g) ^ N * (1 + hs g') ^ N)
      (mul_nonneg (mul_nonneg (mul_nonneg hM hK0) P0) P1) hbd
    rw [e]
    exact key.trans (le_of_eq (by ring))
  have fin := hb2 γ h1 h2 (C₀ * K * M) (mul_nonneg (mul_nonneg hC₀ hK0) hM) h3 b w hb hw
  calc ‖∑ j, ⟪b, x j⟫_ℂ * ℓ j w‖ = ‖γ b w‖ := rfl
    _ ≤ _ := fin
    _ = _ := by ring

end GlobalTheory.TypeSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.DeepSubMulSecNorm
section
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

namespace GlobalTheory.FinalJoin

section

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (n : SecNorm B)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem hypC_secNorm (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR Bx CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) :
    HypC large₂ (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) H C2 A2 CR Bx CT (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S)
        ka wL wF T nP nW h0 nus ↔
      HypC large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus := Iff.rfl

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem deepSubMul_secNorm : DeepSubMul (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) ↔ DeepSubMul X := Iff.rfl

end

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem baseIn_secNorm : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (n : SecNorm B), BaseIn large₂ X K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → BaseIn large₂ (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) K H Ch Ah Cq Aq C2 A2 CR CT (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) ka wL wF Tn nP nW h0 nus := by
  intro D B P j X large₂ K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus n h
  obtain ⟨a1, a2, a3, a4, a5⟩ := h
  exact ⟨(hypC_secNorm X n large₂ H C2 A2 CR 0 CT S ka wL wF Tn nP nW h0 nus).2 a1,
    (latAt_N n.N n.h0 n.h1 n.h2 n.h3 n.h4).2 a2,
    (lamwAt_N n.N n.h0 n.h1 n.h2 n.h3 n.h4 large₂ K.CL K.AL).2 a3,
    fun hj => (qAt_N n.N n.h0 n.h1 n.h2 n.h3 n.h4 large₂ _ _ _ _ _ _ _ _).2 (a4 hj),
    (deepSubMul_secNorm X n).2 a5⟩

end GlobalTheory.FinalJoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFormFamilyHypothesesChangedSecondNorm
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

namespace GlobalTheory.NormMove

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (n : SecNorm B) {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

abbrev xT (X : PJ D B P j) : PJ D n.base P j := PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X

abbrev sT (S : Scal B) : Scal n.base := scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S

def gT (G : GlobalFamilyData X ka wL wF) : GlobalFamilyData (xT n X) ka wL wF where
  N := G.N
  w := G.w
  del := G.del
  th' := G.th'
  rz := G.rz
  alz := G.alz
  th0 := G.th0
  zc := G.zc
  rq := G.rq
  th := G.th
  iet := G.iet
  et := G.et
  mx := G.mx

section Structural

set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local irreducible]
  _root_.NumberField.RingOfIntegers _root_.CommRing.toCommSemiring _root_.NumberField.instCommRingRingOfIntegers _root_.AddCommGroup.toAddCommMonoid
  _root_.Submodule.span _root_.Set.range _root_.Submodule.map _root_.RingHom.id
  _root_.Semiring.toNonAssocSemiring _root_.instHSMul _root_.LinearMap.instSMul _root_.DistribMulAction.toDistribSMul
  _root_.CommRing.toCommMonoid _root_.LinearMap.id _root_.SetLike.instMembership _root_.Submodule.setLike
  _root_.Real.instLE _root_.Real.log _root_.Nat.cast _root_.Real.instNatCast
  _root_.instHMul _root_.Real.instMul _root_.instHSub _root_.Real.instSub
  Formalism.MainNotions.WeightFamilies.Wt.size _root_.One.toOfNat1 _root_.Real.instOne _root_.Semifield.toDivisionSemiring
  _root_.Field.toSemifield _root_.Complex.instSemiring _root_.instHDiv _root_.Real.instDivInvMonoid
  _root_.Finset.sum _root_.Real.instAddCommMonoid _root_.Finset.univ _root_.NumberField.Embeddings.instFintypeRingHom
  _root_.Complex.instField _root_.Fintype.card _root_.instHPow _root_.NPow.toPow
  _root_.Ring.toAddGroupWithOne _root_.instMulNat _root_.instOfNatNat _root_.Fin.instOfNat
  Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.r _root_.instLTNat Formalism.MainNotions.Gaps.EtaleWeightGaps.etWt
  _root_.Zero.toOfNat0 _root_.SubNegZeroMonoid.toNegZeroClass _root_.SubtractionMonoid.toSubNegZeroMonoid _root_.AddCommGroup.toDivisionAddCommMonoid
  _root_.instDistribOfSemiring _root_.Algebra.toModule _root_.LinearMap.instFunLike _root_.instMulZeroClassOfSemiring
  Formalism.MainNotions.WeightFamilies.PPv _root_.instHAdd _root_.Real.instAdd _root_.Set.instMembership
  _root_.Set.instInsert _root_.Set.instSingletonSet _root_.instOfNatAtLeastTwo Formalism.BasicNotions.Scale.L
  _root_.Real.instMax _root_.Module.finrank _root_.Rat.semiring _root_.Rat.commSemiring
  _root_.DivisionRing.toRatAlgebra _root_.Field.toDivisionRing _root_.abs _root_.Real.lattice
  _root_.Real.instAddGroup _root_.Int.cast _root_.Real.instIntCast _root_.NumberField.discr
  _root_.IntermediateField.toField _root_.Rat.instField
  _root_.IntermediateField.module' _root_.instSMulOfMul _root_.Rat.instMul Formalism.MainNotions.WeightAlgebra.lamStar
  Formalism.MainNotions.WeightAlgebra.Zb Formalism.MainNotions.Gaps.EtaleWeightGaps.PageGq Formalism.MainNotions.Gaps.EtaleWeightGaps.ShareRd _root_.Submodule.addCommMonoid
  _root_.Submodule.module _root_.FractionRing _root_.Localization.AtPrime _root_.MvPolynomial
  Formalism.MainNotions.Gaps.EtaleWeightGaps.Idx _root_.NumberField.RingOfIntegers.instAlgebra_1 _root_.IsFractionRing _root_.IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  _root_.ValuationSubring.instSetLike _root_.IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers _root_.SubsemiringClass.toCommSemiring _root_.NonAssocRing.toNonAssocSemiring
  _root_.CommRing.toNonAssocCommRing _root_.AddMonoidAlgebra.commSemiring _root_.Nat.instMulZeroClass _root_.Finsupp.instAddCommMonoid
  _root_.Nat.instAddCommMonoid Formalism.DV.gaussIdeal _root_.ValuationSubring.instCommRingSubtypeMem _root_.Ideal
  _root_.AddMonoidAlgebra.semiring _root_.Finsupp.instAddMonoid _root_.Nat.instAddMonoid _root_.AddMonoidAlgebra.commRing
  _root_.Ideal.primeCompl _root_.OreLocalization.oreSetComm _root_.CommSemiring.toCommMonoid _root_.Semiring.toModule
  _root_.Semiring.toMonoidWithZero _root_.MulZeroOneClass.toMulZeroClass _root_.MonoidWithZero.toMulZeroOneClass _root_.Monoid.toMulAction
  _root_.NSMul.toSMul _root_.instAddNat _root_.OreLocalization.smul _root_.Monoid.toMulOneClass
  _root_.OreLocalization.npow _root_.Nat.unaryCast _root_.OreLocalization _root_.OreLocalization.instMonoidWithZero
  _root_.OreLocalization.instAddCommMonoidOreLocalization _root_.AddGroupWithOne.toAddGroup _root_.SubNegMonoid.sub' _root_.OreLocalization.instAddMonoid
  _root_.OreLocalization.instNegOreLocalization _root_.ZSMul.toSMul _root_.instOfNat _root_.instNatCastInt
  _root_.Int.castDef _root_.OreLocalization.instSemiring _root_.OreLocalization.instAddGroupOreLocalization _root_.TensorProduct
  _root_.IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion _root_.Algebra.id _root_.nonZeroDivisors _root_.DivInvMonoid.div'
  _root_.OreLocalization.inv' _root_.zpowRec _root_.npowRec _root_.ZPow.toPow
  _root_.NNRat.castRec _root_.OreLocalization.instRing _root_.GroupWithZero.toDivInvMonoid _root_.OreLocalization.instGroupWithZeroNonZeroDivisors
  _root_.NNRat _root_.Rat.castRec _root_.NNRat.cast _root_.NNRat.num
  _root_.NNRat.den _root_.OreLocalization.instDivisionRingNonZeroDivisors _root_.Rat.cast _root_.TensorProduct.addCommMonoid
  _root_.RingHom.toAlgebra _root_.IsFractionRing.lift _root_.ValuationSubring.instAlgebraSubtypeMem _root_.RingHom.comp
  _root_.OreLocalization.numeratorRingHom _root_.RingHom.instFunLike _root_.AddMonoidAlgebra.algebra _root_.TensorProduct.leftModule
  _root_.instAddTensorProduct._aux_1 _root_.Algebra.TensorProduct.instCommSemiring _root_.Algebra.TensorProduct.leftAlgebra _root_.instZeroTensorProduct._aux_1
  _root_.TensorProduct.leftHasSMul _root_.Nat.instMonoid _root_.Nat.instSemiring _root_.AddCommMonoid.toNatModule
  _root_.TensorProduct.instModule _root_.LinearMap.addCommMonoid _root_.LinearMap.module _root_.TensorProduct.tmul
  _root_.AddCommMonoidWithOne.toAddCommMonoid _root_.NonAssocSemiring.toAddCommMonoidWithOne _root_.npowRecAuto _root_.NonAssocSemiring.toMulZeroOneClass
  _root_.Algebra.TensorProduct.instNonAssocSemiring _root_.Ring.toAddCommGroup _root_.TensorProduct.Neg.aux _root_.TensorProduct.neg
  _root_.Int.instMonoid _root_.Int.instSemiring _root_.AddCommGroup.toIntModule _root_.AddCommGroupWithOne.toAddCommMonoidWithOne
  _root_.NonAssocRing.toAddCommGroupWithOne _root_.Ring.toNonAssocRing _root_.AddCommGroupWithOne.toAddGroupWithOne _root_.Algebra.TensorProduct.instSemiring
  _root_.Algebra.TensorProduct.includeLeftRingHom _root_.Set.ofPred Formalism.MainNotions.WeightFamilies.dimY Formalism.MainNotions.WeightAlgebra.wadd
  Formalism.MainNotions.WeightAlgebra.wsmul _root_.Fin.fintype Formalism.MainNotions.Gaps.EtaleWeightGaps.a0 _root_.Finset.prod
  _root_.MvPolynomial.X _root_.Algebra.TensorProduct.includeRight _root_.Algebra.TensorProduct.instAlgebra _root_.Fin.succ
  _root_.Real.instMonoid Formalism.MainNotions.Gaps.EtaleWeightGaps.ShareRhoP _root_.Submodule.hasQuotient _root_.Submodule.addCommGroup
  _root_.Submodule.comap _root_.Submodule.subtype _root_.Submodule.restrictScalars _root_.AddMonoid.toAddZeroClass
  _root_.iInf _root_.Submodule.instInfSet Formalism.MainNotions.WeightFamilies.rho _root_.Pi.addCommMonoid
  _root_.Pi.Function.module Formalism.MainNotions.WeightFamilies.dualZ _root_.Pi.instZero _root_.ZeroMemClass.zero
  _root_.IntermediateField.instSetLike Formalism.MainNotions.WeightFamilies.trF Formalism.MainNotions.WeightFamilies.hform Formalism.MainNotions.WeightFamilies.c1
  _root_.LinearMap.ker _root_.Submodule.Quotient.addCommMonoid _root_.Submodule.Quotient.module Formalism.MainNotions.WeightAlgebra.cc
  _root_.Real.instZero Formalism.MainNotions.WeightFamilies.PP0v _root_.Real.instPow Formalism.MainNotions.WeightFamilies.RRv
  Formalism.BasicNotions.Host.rdE Formalism.MainNotions.WeightAlgebra.PO _root_.LinearIndependent _root_.Localization.Away
  _root_.Submonoid.powers _root_.Subalgebra.instSetLike _root_.Algebra.adjoin Formalism.MainNotions.Gaps.EtaleWeightGaps.addL
  _root_.IsLocalization.Away.invSelf _root_.IsLocalization.Away Formalism.MainNotions.Gaps.EtaleWeightGaps.wt0 _root_.Subalgebra.toSemiring
  _root_.Subalgebra.moduleLeft _root_.Subalgebra.toRing _root_.Submodule.instSMul _root_.Submodule.smul
  _root_.Ideal.span Formalism.MainNotions.Gaps.EtaleWeightGaps.frMap _root_.Submodule.instTop _root_.Submodule.Quotient.addMonoid._aux_1
  _root_.Subalgebra.instMulActionSubtypeMem _root_.Quotient.mk'' _root_.Submodule.quotientRel _root_.Submodule.Quotient.instSMul'
  _root_.Submodule.Quotient.addCommGroup._aux_1 _root_.Submodule.Quotient.addCommGroup._aux_3 _root_.Quotient.map' _root_.Submodule.module'
  _root_.Subalgebra.algebra _root_.Subalgebra.instSMulSubtypeMem _root_.AddCommSemigroup.toAddCommMagma _root_.AddCommMonoid.toAddCommSemigroup
  _root_.LinearMap.comp _root_.LinearMap.restrictScalars _root_.Submodule.mkQ _root_.LinearMap.codRestrict
  _root_.LinearMap.domRestrict _root_.Submodule.instPartialOrder _root_.Set.image _root_.Set.instUnion
  _root_.instSubNat _root_.EReal _root_.instPartialOrderEReal _root_.instZeroEReal
  _root_.instTopEReal _root_.instInfSetEReal _root_.Real.toEReal _root_.EReal.toReal
  _root_.instLENat _root_.FiniteDimensional _root_.Ideal.instHasQuotient_1 _root_.Subalgebra.toCommRing
  _root_.Ideal.Quotient.ring._aux_1 _root_.Submodule.Quotient.mk _root_.Ideal.Quotient.ring._aux_6 _root_.Ideal.Quotient.ring._aux_14
  _root_.Ideal.Quotient.ring._aux_23 _root_.Ideal.instHasQuotient _root_.Ideal.Quotient.ring _root_.Ideal.Quotient.mk
  Formalism.MainNotions.Gaps.EtaleWeightGaps.IsGen _root_.Submodule.Quotient.addCommGroup _root_.AddMonoidHom.instFunLike _root_.QuotientAddGroup.instHasQuotientAddSubgroup
  _root_.Submodule.toAddSubgroup _root_.QuotientAddGroup.Quotient.addGroup _root_.AddMonoidHom.instAddCommGroup _root_.QuotientAddGroup.lift
  _root_.smulAddHom Formalism.MainNotions.Gaps.EtaleWeightGaps.Pts _root_.instBotEReal Formalism.MainNotions.Gaps.EtaleWeightGaps.ep
  _root_.Classical.choose _root_.EReal.instMul _root_.instAddCommMonoidWithOneEReal Formalism.MainNotions.Gaps.EtaleWeightGaps.toE
  Formalism.MainNotions.Gaps.EtaleWeightGaps.ord _root_.AlgHom.funLike _root_.Ideal.Quotient.mkₐ _root_.EReal.instSubNegZeroMonoid
  Formalism.MainNotions.Gaps.EtaleWeightGaps.ordV _root_.WithTop _root_.Module.compHom Formalism.MainNotions.Gaps.EtaleWeightGaps.ballO
  _root_.Submodule.instPowNat _root_.Subalgebra.toCommSemiring _root_.Finsupp.sum _root_.OreLocalization.instModuleOfIsScalarTower
  Formalism.MainNotions.Gaps.EtaleWeightGaps.Tay.hs _root_.OreLocalization.instCommRing _root_.OreLocalization.instAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps.Tay.loc
  _root_.IsLocalization _root_.Localization _root_.OreLocalization.instCommSemiring _root_.Algebra.TensorProduct.instCommRing
  _root_.MvPowerSeries.instSemiring _root_.MvPowerSeries.instAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps.Tay.tens _root_.IsLocalization.AtPrime
  Formalism.MainNotions.Gaps.EtaleWeightGaps.Tay.pol _root_.AddMonoidAlgebra.nonAssocSemiring _root_.Finsupp.instAddZeroClass Formalism.MainNotions.Gaps.EtaleWeightGaps.Tay.IsTay
  Formalism.MainNotions.Gaps.EtaleWeightGaps.Tay.IsCst _root_.WithTop.instPreorder _root_.ConditionallyCompleteLattice.toConditionallyCompletePartialOrder _root_.Int.instConditionallyCompleteLinearOrder
  _root_.WithTop.some _root_.Int.instNegInt _root_.ENat _root_.Module.length
  _root_.instTopENat _root_.Summable _root_.Real.pseudoMetricSpace _root_.ENat.toNat
  Formalism.BasicNotions.lw _root_.SummationFilter.unconditional _root_.tsum Formalism.MainNotions.Gaps.EtaleWeightGaps.fdeg
  Formalism.MainNotions.WeightAlgebra.g0

def qT {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) : LocalPointData (gT n G) la where
  y := Q.y
  g0 := Q.g0
  c := Q.c

variable (G : GlobalFamilyData X ka wL wF) (S : Scal B)

set_option maxHeartbeats 4000000 in
theorem shareRhoR_iff (T d : ℕ) : ShareRhoR (gT n G) (sT n S) T d ↔ ShareRhoR G S T d := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem inBasis_iff (la : HeightOneSpectrum (𝓞 B.KO)) : InBasis (gT n G) la ↔ InBasis G la := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem inContainMR_iff (la : HeightOneSpectrum (𝓞 B.KO)) (CRm : ℝ) (T : ℕ) (c : ℝ) :
    InContainMR (gT n G) la (sT n S) CRm T c ↔ InContainMR G la S CRm T c := Iff.rfl

variable {G}

set_option maxHeartbeats 4000000 in
theorem inCurve_iff {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) : (qT n Q).InCurve ↔ Q.InCurve := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem inTie_iff {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) : (qT n Q).InTie (sT n S) ↔ Q.InTie S := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem inLift_iff {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) (T : ℕ) : (qT n Q).InLift T ↔ Q.InLift T := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem heights_iff (Qf : ∀ la, LocalPointData G la) (Gc PH Prw Pet : ℝ) :
    Heights (fun la => qT n (Qf la)) Gc PH Prw Pet ↔ Heights Qf Gc PH Prw Pet := Iff.rfl

end Structural

variable (G : GlobalFamilyData X ka wL wF) (S : Scal B)

set_option maxHeartbeats 4000000 in
theorem tiedW_iff (Gc Prw : ℝ) : (gT n G).TiedW (sT n S) Gc Prw ↔ G.TiedW S Gc Prw := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem tiedTh_iff (Gc : ℝ) : (gT n G).TiedTh (sT n S) Gc ↔ G.TiedTh S Gc := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem tiedEt_iff (large₂ : SizeData₂ D) (Cf Af : ℝ) : (gT n G).TiedEt large₂ Cf Af ↔ G.TiedEt large₂ Cf Af := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem combBound_iff (c : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) :
    CombBound (gT n G) (sT n S) c nus ↔ CombBound G S c nus := Iff.rfl

variable {G} in
theorem inLiftC_of {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) (Gc Prw : ℝ) (T : ℕ) (h : Q.InLiftC S Gc Prw T) :
    (qT n Q).InLiftC (sT n S) Gc Prw T := fun a b c =>
  (inLift_iff n Q T).2 (h ((tiedW_iff n G S Gc Prw).1 a) ((inCurve_iff n Q).1 b) ((inTie_iff n S Q).1 c))

set_option maxHeartbeats 4000000 in

theorem famIn_move (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR : ℝ) (Tn : ℕ) (Gc PH Prw Pet Pd : ℝ)
    (h : FamIn large₂ K H Ch Ah Cq Aq C2 A2 CR S Tn G Gc PH Prw Pet Pd) :
    FamIn large₂ K H Ch Ah Cq Aq C2 A2 CR (sT n S) Tn (gT n G) Gc PH Prw Pet Pd := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  exact ⟨(tiedW_iff n G S Gc Prw).2 a1, (tiedTh_iff n G S Gc).2 a2, (tiedEt_iff n G large₂ _ _).2 a3, a4, a5, a6, a7,
    (shareRhoR_iff n G S _ _).2 a8, a9, a10, fun la => (inBasis_iff n G la).2 (a11 la),
    fun la => (inContainMR_iff n G S la _ _ _).2 (a12 la)⟩

set_option maxHeartbeats 4000000 in

theorem ptIn_move (Tn : ℕ) (c Gc PH Prw Pet : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (h : PtIn S Tn G c Gc PH Prw Pet nus) : PtIn (sT n S) Tn (gT n G) c Gc PH Prw Pet nus := by
  obtain ⟨a1, Qf, a2, a3, a4, a5⟩ := h
  exact ⟨(combBound_iff n G S c nus).2 a1, fun la => qT n (Qf la), fun la => (inCurve_iff n (Qf la)).2 (a2 la),
    fun la => (inTie_iff n S (Qf la)).2 (a3 la), fun la => inLiftC_of n S (Qf la) Gc Prw Tn (a4 la),
    (heights_iff n Qf Gc PH Prw Pet).2 a5⟩

set_option maxHeartbeats 4000000 in
set_option linter.unusedVariables false in

theorem exists_famIn_ptIn : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (n : SecNorm B) (G : GlobalFamilyData X ka wL wF) (Gc PH Prw Pet Pd c : ℝ), FamIn large₂ K H Ch Ah Cq Aq C2 A2 CR S Tn G Gc PH Prw Pet Pd → PtIn S Tn G c Gc PH Prw Pet nus → ∃ G' : GlobalFamilyData (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) ka wL wF, FamIn large₂ K H Ch Ah Cq Aq C2 A2 CR (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) Tn G' Gc PH Prw Pet Pd ∧ PtIn (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) Tn G' c Gc PH Prw Pet nus :=
  fun _ _ _ _ _ large₂ K H Ch Ah Cq Aq C2 A2 CR _ S _ _ _ Tn _ _ _ nus n G Gc PH Prw Pet Pd c hF hP =>
    ⟨gT n G, famIn_move n G S large₂ K H Ch Ah Cq Aq C2 A2 CR Tn Gc PH Prw Pet Pd hF, ptIn_move n G S Tn c Gc PH Prw Pet nus hP⟩

end GlobalTheory.NormMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IndexBoundChosenFamilyOfIntrinsicHypotheses
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.FinalJoin

theorem inputs4_of_inputsR : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (X : WeightAlgebra.Prov D B P) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ), InputsR large₂ (X j h1 h2) K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → PageSupp D large₂ B C2 A2 nW S wL → Inputs4 large₂ (X j h1 h2) K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus := by
  intro D B P X j h1 h2 large₂ K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF T nP nW h0 nus hI hTC hPA hPS
  obtain ⟨⟨hH, hLat, hLAM, hQ, hSub⟩, hSup, hHerm, G, Gc, PH, Prw, Pet, Pd, hLogD,
    ⟨hW, hTh, hEt, hPGd, hPG4, hPGq, hRd, hRho, hRhoP, hPoly, hB, hM⟩, hComb, Qf, hC, hTie, hLift, hHt⟩ := hI
  have hSet := hH.2.1
  have hH2 := hH.2.2.2.2.1
  obtain ⟨hS0, hSK⟩ := shortG_of_scalB hH.2.2.1 hPG4
  have hDT : WeightFamilies.dimY D j ≤ T := hSet.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hwt : SizeBoundsAlt.wtIter wadd wL ((X j h1 h2).wF0 wL wF) (a0 D j T) = ka := by
    rw [iterated_weight_at_vanishingOrder (X j h1 h2) wL wF T hDT]; exact (ka_eq_addL_of_setC hSet).symm
  obtain ⟨rz, alz, th0, zc, hTZ, hZ⟩ := exists_global_family_zero_choice G S T Gc hwt hS0 hH2.2.2.1
  obtain ⟨th, hTQ⟩ := exists_global_family_quotient_bounded
    ({ G with rz := rz, alz := alz, th0 := th0, zc := zc } : GlobalFamilyData (X j h1 h2) ka wL wF) large₂ S K.CRm T
    (cc D large₂ C2 A2 CR wL) (Gc * ka.size) Ch Ah hSK hH2.2.2.2
    (mul_le_mul_of_nonneg_right hPGq (by linarith [ka.one_le_size]))
  obtain ⟨hR1, hR2⟩ := GlobalTheory.shareRho_and_shareRhoT_of_shareRhoR D B P j (X j h1 h2) ka wL wF
    (G.setZQ rz alz th0 zc _ th) S T _ Gc hRho hTZ hZ
  have hM' : ∀ la, InContainM (G.setZQ rz alz th0 zc _ th) la K.CRm T (cc D large₂ C2 A2 CR wL) :=
    fun la => inContainM_of _ la S _ T _ (hM la) (hZ la)
  have hLift' : ∀ la, ((Qf la).tr G rz alz th0 zc _ th).InLiftC S Gc Prw T :=
    fun la => tr_InLiftC G rz alz th0 zc _ th (Qf la) S Gc Prw T (hLift la)
  refine ⟨hH, hLat, hSup, hLAM, hQ, hTC, hPA, hPS, G.setZQ rz alz th0 zc _ th, Gc, PH, Prw, Pet, Pd,
    hW, hTh, hTZ, hTQ, hEt, hHerm, hSub, hLogD, pageGd4_iff.mpr hPGd, hRd, hR2, hRhoP, polyDom4_iff.mpr hPoly, hZ, hM',
    fun hj => ⟨fun la => (Qf la).tr G rz alz th0 zc _ th, hB, hC, hTie, hLift',
      combBound4_of hj (tr_CombBound G rz alz th0 zc _ th S _ nus hComb) _, hHt⟩,
    fun hj => depthAtM_of hj hComb, fun _ _ => ?_,
    fun _ => ⟨fun la => (Qf la).tr G rz alz th0 zc _ th, hB, hC, hTie, hLift', hHt⟩⟩
  exact theorem_zero_of_named_inputs large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus hH hLat hSup hLAM hQ
    (G.setZQ rz alz th0 zc _ th) Gc PH Prw Pet Pd (fun la => (Qf la).tr G rz alz th0 zc _ th)
    hW hTh hTZ hTQ hEt hHerm hSub hLogD hPGd hRd hR1 hRhoP hPoly hB hC hTie hLift' hZ hM' hComb hHt

end GlobalTheory.FinalJoin
end

