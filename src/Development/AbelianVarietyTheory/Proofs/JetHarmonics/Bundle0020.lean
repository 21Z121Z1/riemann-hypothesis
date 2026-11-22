import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HStable
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0016
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0012
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmThetaOperatorInvariantOfLiftCongrOne
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCmThetaEqSumProdTranslates
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0017
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsOrthogonalFrameNormsCoprimeOfUnimodular
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MultiplicativeShiftEqTranslateBySmallPoint
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0018

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BilinPartEigenMemRange
section
set_option autoImplicit false

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem bilinPart_eigen_mem_range : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (a : O) (u u' : Fin d → R) (α α' : R), (dAct k B a).mulVec (fun i => algebraMap R k (u i)) = algebraMap R k α • (fun i => algebraMap R k (u i)) → (dAct k B (star a)).mulVec (fun i => algebraMap R k (u' i)) = algebraMap R k α' • (fun i => algebraMap R k (u' i)) → IsUnit (α - α') → dotProduct (fun i => algebraMap R k (u i)) ((bilinPart k h).mulVec (fun i => algebraMap R k (u' i))) ∈ (algebraMap R k).range := by
  intro R _ d O _ _ k _ _ _ B h hc a u u' α α' hu hu' hα
  choose M hM using fun i j => WickVanishing.M_int B h hc a i j
  set v : Fin d → k := fun i => algebraMap R k (u i) with hv
  set v' : Fin d → k := fun i => algebraMap R k (u' i) with hv'
  have hS : sg1 k h = -(bilinPart k h).transpose := by
    ext i j
    simp only [WickVanishing.gaugeBilinearTerm_eq_neg_double_sum, Matrix.neg_apply, Matrix.transpose_apply, bilinPart]
  have e1 : dotProduct v' ((sg1 k h * dAct k B a - (dAct k B (star a)).transpose * sg1 k h).mulVec v) =
      -(algebraMap R k (α - α') * dotProduct v ((bilinPart k h).mulVec v')) := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hu, dotProduct_sub,
      Matrix.dotProduct_mulVec v' (dAct k B (star a)).transpose, Matrix.vecMul_transpose, hu', Matrix.mulVec_smul,
      dotProduct_smul, smul_dotProduct, hS, Matrix.neg_mulVec, dotProduct_neg,
      Matrix.dotProduct_mulVec v', Matrix.vecMul_transpose, dotProduct_comm _ v, map_sub]
    simp only [smul_eq_mul]
    ring
  have e2 : dotProduct v' ((sg1 k h * dAct k B a - (dAct k B (star a)).transpose * sg1 k h).mulVec v) =
      algebraMap R k (∑ i, u' i * ∑ j, M i j * u j) := by
    simp only [map_sum, map_mul, hM, dotProduct, Matrix.mulVec, hv, hv']
  obtain ⟨w, hw⟩ := hα.exists_left_inv
  refine ⟨-(w * ∑ i, u' i * ∑ j, M i j * u j), ?_⟩
  rw [map_neg, map_mul, ← e2, e1, mul_neg, neg_neg, ← mul_assoc, ← map_mul, hw, map_one, one_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChainLowerBound
section
open Finset

namespace GlobalTheory.WigSh

private theorem strictAnti_of_box {n : ℕ} {L : Fin (n+1) → ℤ} {M : Fin n → ℤ}
    (h : ∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc) : StrictAnti L :=
  Fin.strictAnti_iff_succ_lt.2 fun j => (h j).1.trans_le (h j).2

private theorem chain_prod_le {n₀ : ℕ} {D : ℝ} (hD : 1 ≤ D) (f : ℕ → ℝ)
    (hf : ∀ j < n₀, (D ^ 2)⁻¹ ≤ f j) : (D ^ (2 * n₀))⁻¹ ≤ ∏ j ∈ Finset.range n₀, f j := by
  have h1 : (D ^ (2 * n₀))⁻¹ = ∏ _j ∈ Finset.range n₀, (D ^ 2)⁻¹ := by
    rw [Finset.prod_const, Finset.card_range, pow_mul, inv_pow]
  rw [h1]
  exact Finset.prod_le_prod (fun _ _ => by positivity)
    (fun j hj => hf j (Finset.mem_range.1 hj))

theorem chain_lower_bound : ∀ (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (i : Fin n) (n₀ : ℕ) (b : ℝ), StrictAnti L → (∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc) → L i.succ + 2 * (n₀ : ℤ) + 1 ≤ L i.castSucc → 1 ≤ b → (n₀ : ℝ) ≤ b → ((L 0 : ℝ) - L (Fin.last n) ≤ 2 * b) → (((3 * b) ^ (2 * n₀))⁻¹ ≤ ∏ j ∈ Finset.range n₀, GlobalTheory.WigSh.wP (Function.update L i.succ (L i.succ + (j : ℤ))) M i.succ) ∨ (((3 * b) ^ (2 * n₀))⁻¹ ≤ ∏ j ∈ Finset.range n₀, GlobalTheory.WigSh.wM (Function.update L i.castSucc (L i.castSucc - (j : ℤ))) M i.castSucc) := by
  intro n L M i n₀ b hL hbox hgap hb hn hspan
  have hD : (1 : ℝ) ≤ 3 * b := by linarith
  have h0 : ∀ k, (L k : ℝ) ≤ L 0 := fun k => by
    exact_mod_cast hL.antitone (Fin.zero_le k)
  have hl : ∀ k, (L (Fin.last n) : ℝ) ≤ L k := fun k => by
    exact_mod_cast hL.antitone (Fin.le_last k)
  have hlt : ∀ k : Fin n, k < i → L i.castSucc < M k := fun k hk =>
    lt_of_le_of_lt (hL.antitone (by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; exact hk)) (hbox k).1
  have hgt : ∀ k : Fin n, i < k → M k ≤ L i.succ := fun k hk =>
    le_trans (hbox k).2 (hL.antitone (by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; exact hk))
  by_cases hc : L i.succ + n₀ + 1 ≤ M i
  · left
    refine chain_prod_le hD _ fun j hj => ?_
    have hjZ : (j : ℤ) < n₀ := by exact_mod_cast hj
    have hjR : (j : ℝ) ≤ b := le_trans (by exact_mod_cast hj.le) hn
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hbox' : ∀ k : Fin n, Function.update L i.succ (L i.succ + (j : ℤ)) k.succ < M k ∧
        M k ≤ Function.update L i.succ (L i.succ + (j : ℤ)) k.castSucc := by
      intro k
      constructor
      · by_cases hk : k = i
        · subst hk
          rw [Function.update_self]; omega
        · rw [Function.update_of_ne (fun h => hk (Fin.succ_injective _ h))]
          exact (hbox k).1
      · by_cases hk : k.castSucc = i.succ
        · have := (hbox k).2
          rw [hk] at this ⊢
          rw [Function.update_self]; omega
        · rw [Function.update_of_ne hk]
          exact (hbox k).2
    refine GlobalTheory.T.inv_sq_le_wignerCoeffSqRaising n _ M i.succ (3 * b) (strictAnti_of_box hbox') hbox' ?_ hD ?_ ?_
    · intro k
      rw [Function.update_self]
      rcases lt_trichotomy k i with hk | hk | hk
      · have := hlt k hk; omega
      · subst hk; omega
      · have := hgt k hk; omega
    · rw [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero i).symm]
      push_cast
      have := hl i.succ
      linarith
    · rw [Function.update_self]
      by_cases hk : Fin.last n = i.succ
      · rw [hk, Function.update_self]; linarith
      · rw [Function.update_of_ne hk]
        push_cast
        have := h0 i.succ
        linarith
  · right
    refine chain_prod_le hD _ fun j hj => ?_
    have hjZ : (j : ℤ) < n₀ := by exact_mod_cast hj
    have hjR : (j : ℝ) ≤ b := le_trans (by exact_mod_cast hj.le) hn
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hbox' : ∀ k : Fin n,
        Function.update L i.castSucc (L i.castSucc - (j : ℤ)) k.succ < M k ∧
        M k ≤ Function.update L i.castSucc (L i.castSucc - (j : ℤ)) k.castSucc := by
      intro k
      constructor
      · by_cases hk : k.succ = i.castSucc
        · have hki : k < i := by
            have := congrArg Fin.val hk
            simp only [Fin.val_succ, Fin.val_castSucc] at this
            rw [Fin.lt_def]; omega
          have := hlt k hki
          rw [hk, Function.update_self]; omega
        · rw [Function.update_of_ne hk]
          exact (hbox k).1
      · by_cases hk : k = i
        · subst hk
          rw [Function.update_self]; omega
        · rw [Function.update_of_ne (fun h => hk (Fin.castSucc_injective _ h))]
          exact (hbox k).2
    refine GlobalTheory.T.inv_sq_le_wignerCoeffSqLowering n _ M i.castSucc (3 * b) (strictAnti_of_box hbox') hbox' ?_ hD ?_ ?_
    · intro k
      rw [Function.update_self]
      rcases lt_trichotomy k i with hk | hk | hk
      · have := hlt k hk; omega
      · subst hk; omega
      · have := hgt k hk; omega
    · rw [Function.update_self]
      by_cases hk : 0 = i.castSucc
      · rw [hk, Function.update_self]; linarith
      · rw [Function.update_of_ne hk]
        push_cast
        have := hl i.castSucc
        linarith
    · rw [Function.update_self, Function.update_of_ne (Fin.castSucc_lt_last i).ne']
      push_cast
      have := h0 i.castSucc
      linarith

end GlobalTheory.WigSh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmThetaOperatorInvariantOfLiftCongrOneStatement
section
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmThetaOperator_invariant_of_lift_congr_one : ∀ (q : ℕ) [Fact q.Prime] (lam : Qbar →+* ℂ_[q]) (g : ℕ) (S : Setup g) (r : ℕ) (b : Fin r → Fin g → ℂ) (e : (Fin g → ℂ) → ℂ) (t : Fin g → ℂ) (n m s : ℕ) (eps : ℂ) (y : Fin r → Fin (q ^ n)), S.Ok → (∀ i, b i ∈ S.La) → S.IsTheta e → IsIdem lam S.d m eps → 2 * n ≤ m → (∀ i, ∃ z : ℤ, (hf S.Hm (eps • b i) t).im = z) → s ≡ 1 [MOD q ^ n] → opW S.d S.Hm ((s : ℂ) • liftY q n eps b y) (opU S.Hm t e) = opW S.d S.Hm (liftY q n eps b y) (opU S.Hm t e) ∧ ∀ v ∈ S.La, kap S.Hm v ((s : ℂ) • liftY q n eps b y) = kap S.Hm v (liftY q n eps b y) := by
  first | exact @GlobalTheory.MomOne.lift_change | exact GlobalTheory.MomOne.lift_change | (intros; apply GlobalTheory.MomOne.lift_change <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesMultiplicativeChart
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

lemma hatmul_DT_C_mul {q : ℕ} [Fact q.Prime] (c : ℂ_[q]) (f : ℂ_[q]⟦X⟧) :
    DT (C c * f) = C c * DT f := by
  unfold DT
  rw [← smul_eq_C_mul, Derivation.map_smul, smul_eq_C_mul]
  ring

lemma hatmul_const_log {q : ℕ} [Fact q.Prime] (ω : ℂ_[q]) :
    constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
  have : constantCoeff (logS : ℂ_[q]⟦X⟧) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [logS]
  simp [this]

lemma hatmul_DT_hat {q : ℕ} [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ)
    (hG : AnalyticAt ℂ G 0) :
    DT (hat ι (C ω * logS) G) = C ω * hat ι (C ω * logS) (deriv G) := by
  obtain ⟨-, -, -, -, hd, -, -⟩ := GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q ι _ (hatmul_const_log ω)
  obtain ⟨-, -, -, -, hl, -⟩ := GlobalTheory.T.cpBinomialPowerSubOneSeries_integrality_composition_log q
  have h1 : DT (C ω * logS : ℂ_[q]⟦X⟧) = C ω := by rw [hatmul_DT_C_mul, hl, mul_one]
  unfold DT at h1 ⊢
  rw [hd G hG, ← mul_assoc, h1]

lemma hatmul_iter {q : ℕ} [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (k : ℕ) :
    ∀ (G : ℂ → ℂ), AnalyticAt ℂ G 0 →
      DT^[k] (hat ι (C ω * logS) G) = C (ω ^ k) * hat ι (C ω * logS) (iteratedDeriv k G) := by
  induction k with
  | zero => intro G _; simp
  | succ k ih =>
    intro G hG
    have hk : AnalyticAt ℂ (iteratedDeriv k G) 0 := by
      rw [iteratedDeriv_eq_iterate]
      exact hG.iterated_deriv k
    rw [Function.iterate_succ_apply', ih G hG, hatmul_DT_C_mul, hatmul_DT_hat ι ω _ hk,
      iteratedDeriv_succ, pow_succ, map_mul, mul_assoc]

lemma hatmul_subst {q : ℕ} [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ) (a : ℤ_[q]) :
    hat ι (C (ω * zc a) * logS) G = (hat ι (C ω * logS) G).subst (mulS a : ℂ_[q]⟦X⟧) := by
  obtain ⟨-, -, -, -, -, -, hs⟩ := GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q ι _ (hatmul_const_log ω)
  obtain ⟨hm, -⟩ := GlobalTheory.T.cpBinomialPowerSubOneSeries_integrality_composition_log q
  obtain ⟨-, h0, -, hl⟩ := hm a
  have hsub : HasSubst (mulS a : ℂ_[q]⟦X⟧) := HasSubst.of_constantCoeff_zero' h0
  rw [hs G _ h0, ← smul_eq_C_mul (a := ω), subst_smul hsub, hl, smul_eq_C_mul, map_mul, mul_assoc]

theorem hat_multiplicative_chart : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ), AnalyticAt ℂ G 0 → (DT (hat ι (C ω * logS) G) = C ω * hat ι (C ω * logS) (deriv G)) ∧ (∀ k : ℕ, constantCoeff (DT^[k] (hat ι (C ω * logS) G)) = ω ^ k * ι (iteratedDeriv k G 0)) ∧ (∀ (α : ℂ) (a : ℤ_[q]), ι α = zc a → hat ι (C ω * logS) (fun z => G (α * z)) = (hat ι (C ω * logS) G).subst (mulS a : ℂ_[q]⟦X⟧)) ∧ ∀ a : ℤ_[q], hat ι (C (ω * zc a) * logS) G = (hat ι (C ω * logS) G).subst (mulS a : ℂ_[q]⟦X⟧) := by
  intro q _ ι ω G hG
  refine ⟨hatmul_DT_hat ι ω G hG, fun k => ?_, fun α a ha => ?_, hatmul_subst ι ω G⟩
  · obtain ⟨-, -, -, hc, -⟩ := GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q ι _ (hatmul_const_log ω)
    rw [hatmul_iter ι ω k G hG, map_mul, hc, constantCoeff_C]
  · obtain ⟨-, -, -, -, -, hα, -⟩ := GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q ι _ (hatmul_const_log ω)
    rw [hα G α hG, ← hatmul_subst, ha, map_mul, ← mul_assoc, mul_comm (C (zc a))]

end GlobalTheory.MomOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCmThetaEqSumProdTranslatesStatement
section
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmTheta_eq_sum_prod_translates : ∀ (q : ℕ) (g : ℕ) (S : Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ) (θ : ℂ → ℂ), q.Prime → S.Ok → (∀ i, x i ∈ S.La) → (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) → (∀ i, 0 < a i ∧ Nat.Coprime (a i) q) → IsTh S.d θ → ∃ (m : ℕ) (r : Fin m → ℂ) (t : Fin m → Fin g → ℂ) (Θ : (Fin g → ℂ) → ℂ), S.IsTheta Θ ∧ Θ ≠ 0 ∧ (∀ j, r j ∈ Qbar) ∧ (∀ j i, PrimeTo S.d q (t j i)) ∧ ∀ z : Fin g → ℂ, Θ (∑ i, z i • x i) = ∑ j, r j * ∏ i, U1 S.d (t j i) θ (z i) ^ a i := by
  first | exact @GlobalTheory.MomOne.exists_theta_eq_sum_prod | exact GlobalTheory.MomOne.exists_theta_eq_sum_prod | (intros; apply GlobalTheory.MomOne.exists_theta_eq_sum_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEllipticFunctionMulProdEqXyStatement
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ellipticFunction_mul_prod_eq_xy : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (φ : ℂ → ℂ), M.Ok → Ell M.L φ → ∃ (m : ℕ) (P : Fin m → ℂ) (A B : Polynomial ℂ), (∀ i, P i ∉ M.L.lattice ∧ meromorphicOrderAt φ (P i) < 0) ∧ ∀ z₀ : ℂ, ∀ᶠ z in 𝓝[≠] z₀, φ z * (∏ i, (Polynomial.X - Polynomial.C (M.x (P i)))).eval (M.x z) = A.eval (M.x z) + B.eval (M.x z) * M.y z := by
  first | exact @GlobalTheory.EllipticModel.exists_mul_prod_eq_xy | exact GlobalTheory.EllipticModel.exists_mul_prod_eq_xy | (intros; apply GlobalTheory.EllipticModel.exists_mul_prod_eq_xy <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGroupedOfSublist
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.ExpCong

section Abstract

variable {A k ι : Type} [CommRing A] [CommRing k] (D : ι → A → A) (c : A →+* k)

def along (w : List ι) (f : A) : A := w.foldl (fun g a => D a g) f

theorem along_nil (f : A) : along D [] f = f := rfl

theorem along_cons (a : ι) (w : List ι) (f : A) : along D (a :: w) f = along D w (D a f) := rfl

theorem along_add (hadd : ∀ a f g, D a (f + g) = D a f + D a g) (w : List ι) (f g : A) :
    along D w (f + g) = along D w f + along D w g := by
  induction w generalizing f g with
  | nil => rfl
  | cons a w ih => rw [along_cons, along_cons, along_cons, hadd, ih]

theorem along_mul_mem (hadd : ∀ a f g, D a (f + g) = D a f + D a g)
    (hmul : ∀ a f g, D a (f * g) = f * D a g + g * D a f) (S : Set k) (J : AddSubgroup k)
    (hSJ : ∀ s ∈ S, ∀ j ∈ J, s * j ∈ J) (w : List ι) (f g : A)
    (hf : ∀ v, v.Sublist w → c (along D v f) ∈ S) (hg : ∀ v, v.Sublist w → c (along D v g) ∈ J) :
    c (along D w (f * g)) ∈ J := by
  induction w generalizing f g with
  | nil =>
    rw [along_nil, map_mul]
    exact hSJ _ (hf [] (List.Sublist.refl _)) _ (hg [] (List.Sublist.refl _))
  | cons a w ih =>
    rw [along_cons, hmul, along_add D hadd, map_add, mul_comm g]
    refine J.add_mem (ih _ _ ?_ ?_) (ih _ _ ?_ ?_)
    · exact fun v hv => hf v (hv.cons a)
    · exact fun v hv => hg (a :: v) (hv.cons_cons a)
    · exact fun v hv => hf (a :: v) (hv.cons_cons a)
    · exact fun v hv => hg v (hv.cons a)

theorem along_mul_exp (hadd : ∀ a f g, D a (f + g) = D a f + D a g)
    (hmul : ∀ a f g, D a (f * g) = f * D a g + g * D a f) (S : Set k) (J : AddSubgroup k)
    (hSJ : ∀ s ∈ S, ∀ j ∈ J, s * j ∈ J) (hJS : ∀ j ∈ J, j ∈ S) (E φ : A) (hE : ∀ a, D a E = E * D a φ)
    (hE1 : c E = 1) (w : List ι) (f : A)
    (hf : ∀ v, v.Sublist w → c (along D v f) ∈ S) (hφ : ∀ v, v.Sublist w → c (along D v φ) ∈ J) :
    c (along D w (f * E)) - c (along D w f) ∈ J := by
  induction w generalizing f with
  | nil =>
    rw [along_nil, along_nil, map_mul, hE1, mul_one, sub_self]
    exact J.zero_mem
  | cons a w ih =>
    have hφ' : ∀ v, v.Sublist w → c (along D v φ) ∈ J := fun v hv => hφ v (hv.cons a)
    have h1 : ∀ v, v.Sublist w → c (along D v (f * D a φ)) ∈ J := fun v hv =>
      along_mul_mem D c hadd hmul S J hSJ v f (D a φ)
        (fun v' hv' => hf v' ((hv'.trans hv).cons a))
        (fun v' hv' => hφ (a :: v') ((hv'.trans hv).cons_cons a))
    have h2 := ih (f * D a φ) (fun v hv => hJS _ (h1 v hv)) hφ'
    have h3 := ih (D a f) (fun v hv => hf (a :: v) (hv.cons_cons a)) hφ'
    have h4 := J.add_mem (J.add_mem h2 (h1 w (List.Sublist.refl _))) h3
    rw [along_cons, along_cons, hmul, hE, along_add D hadd, map_add,
      show f * (E * D a φ) = f * D a φ * E by ring, mul_comm E]
    convert h4 using 1
    ring

def grouped (L : List ι) (m : ι → ℕ) : List ι := L.flatMap fun l => List.replicate (m l) l

theorem grouped_cons (a : ι) (L : List ι) (m : ι → ℕ) :
    grouped (a :: L) m = List.replicate (m a) a ++ grouped L m := by
  simp [grouped]

theorem exists_grouped_of_sublist {L : List ι} (hL : L.Nodup) (m : ι → ℕ) (v : List ι)
    (hv : v.Sublist (grouped L m)) : ∃ m' : ι → ℕ, v = grouped L m' := by
  classical
  induction L generalizing v with
  | nil => exact ⟨m, by simpa [grouped] using hv⟩
  | cons a L ih =>
    rw [grouped_cons, List.sublist_append_iff] at hv
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := hv
    obtain ⟨n, -, rfl⟩ := List.sublist_replicate_iff.1 h₁
    rw [List.nodup_cons] at hL
    obtain ⟨m', rfl⟩ := ih hL.2 v₂ h₂
    refine ⟨Function.update m' a n, ?_⟩
    rw [grouped_cons, Function.update_self]
    congr 1
    unfold grouped
    refine List.flatMap_congr fun l hl => ?_
    rw [Function.update_of_ne]
    rintro rfl
    exact hL.1 hl

theorem foldr_replicate (a : ι) (n : ℕ) (g : A) :
    (List.replicate n a).foldr (fun a g => D a g) g = (D a)^[n] g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.foldr_cons, ih, Function.iterate_succ_apply']

theorem along_reverse_grouped (L : List ι) (m : ι → ℕ) (f : A) :
    along D (grouped L m).reverse f = L.foldr (fun l g => (D l)^[m l] g) f := by
  unfold along
  rw [List.foldl_reverse]
  induction L with
  | nil => rfl
  | cons a L ih => rw [grouped_cons, List.foldr_append, ih, foldr_replicate, List.foldr_cons]

end Abstract

variable {k : Type} [CommRing k] {d : ℕ} (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)

theorem dmonOf_eq_along (m : ι →₀ ℕ) (f : PS k 1 d) :
    DmonOf F u m f =
      along (fun l => Dof F (u l)) (grouped (Finset.univ : Finset ι).toList m).reverse f :=
  (along_reverse_grouped _ _ _ _).symm

theorem exists_along_eq_dmonOf (m : ι →₀ ℕ) (v : List ι)
    (hv : v.Sublist (grouped (Finset.univ : Finset ι).toList m).reverse) :
    ∃ m' : ι →₀ ℕ, ∀ f : PS k 1 d, along (fun l => Dof F (u l)) v f = DmonOf F u m' f := by
  obtain ⟨m', hm'⟩ := exists_grouped_of_sublist (Finset.nodup_toList _) m v.reverse
    (by simpa using hv.reverse)
  refine ⟨Finsupp.equivFunOnFinite.symm m', fun f => ?_⟩
  rw [dmonOf_eq_along, Finsupp.coe_equivFunOnFinite_symm, ← hm', List.reverse_reverse]

end GlobalTheory.ExpCong

namespace GlobalTheory

theorem dmonOf_mul_expS_congr : ∀ (R : Type) [CommRing R] (d : ℕ) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (F : Fin d → PS R 2 d) (I : Ideal R) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (φ : PS k 1 d), constantCoeff φ = 0 → (∀ m : ι →₀ ℕ, ∃ r ∈ I, constantCoeff (DmonOf (fun i => MvPowerSeries.map (algebraMap R k) (F i)) (fun l i => algebraMap R k (u l i)) m φ) = algebraMap R k r) → ∀ (f : PS R 1 d) (m : ι →₀ ℕ), ∃ r ∈ I, constantCoeff (DmonOf (fun i => MvPowerSeries.map (algebraMap R k) (F i)) (fun l i => algebraMap R k (u l i)) m (FB.toK k f * FB.expS k φ)) = algebraMap R k (constantCoeff (DmonOf F u m f) + r) := by
  intro R _ d k _ _ _ F I ι _ u φ hφ0 hφ f m
  set F' : Fin d → PS k 2 d := fun i => MvPowerSeries.map (algebraMap R k) (F i) with hF'
  set u' : ι → Fin d → k := fun l i => algebraMap R k (u l i) with hu'
  have hmap : ∀ m' : ι →₀ ℕ, constantCoeff (DmonOf F' u' m' (FB.toK k f)) =
      algebraMap R k (constantCoeff (DmonOf F u m' f)) := fun m' => by
    rw [hF', hu', FB.toK, ← map_dmonOf, constantCoeff_map]
  have key := ExpCong.along_mul_exp (fun l => Dof F' (u' l)) (constantCoeff : PS k 1 d →+* k)
    (fun a => GE.dof_add F' (u' a)) (fun a => GE.dof_mul F' (u' a)) (Set.range (algebraMap R k))
    (I.toAddSubgroup.map (algebraMap R k).toAddMonoidHom)
    (by
      rintro _ ⟨s, rfl⟩ _ ⟨j, hj, rfl⟩
      exact ⟨s * j, I.mul_mem_left s hj, map_mul (algebraMap R k) s j⟩)
    (by
      rintro _ ⟨j, -, rfl⟩
      exact ⟨j, rfl⟩)
    (FB.expS k φ) φ (fun a => NablaExpConj.Dof_expS k F' (u' a) hφ0) (WickVanishing.constantCoeff_exp hφ0)
    (ExpCong.grouped (Finset.univ : Finset ι).toList m).reverse (FB.toK k f)
    (fun v hv => by
      obtain ⟨m', hm'⟩ := ExpCong.exists_along_eq_dmonOf F' u' m v hv
      exact ⟨_, by rw [hm', hmap]⟩)
    (fun v hv => by
      obtain ⟨m', hm'⟩ := ExpCong.exists_along_eq_dmonOf F' u' m v hv
      obtain ⟨r, hr, e⟩ := hφ m'
      exact ⟨r, hr, by rw [hm', e]; rfl⟩)
  rw [← ExpCong.dmonOf_eq_along, ← ExpCong.dmonOf_eq_along, hmap] at key
  obtain ⟨r, hr, e⟩ := key
  refine ⟨r, hr, ?_⟩
  have e' : algebraMap R k r = _ := e
  rw [map_add, e']
  ring

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLimitPowerSeriesAgreeOnAnnulusPointsStatement
section
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_limit_powerSeries_agree_on_annulus_points : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (G : ℕ → Finset K) (r : ℝ), 0 < r → r ≤ 1 → Monotone G → (∀ n, ∀ x ∈ G n, r ≤ ‖x‖ ∧ ‖x‖ < 1) → Filter.Tendsto (fun n => ∏ x ∈ G n, ‖x‖) Filter.atTop (nhds 0) → ∀ g : ℕ → PowerSeries K, (∀ n, Intg (g n)) → (∀ n, ∀ x ∈ G n, ev1 (g (n + 1)) x = ev1 (g n) x) → ∃ f : PowerSeries K, Intg f ∧ (∀ k, Filter.Tendsto (fun n => PowerSeries.coeff k (g n)) Filter.atTop (nhds (PowerSeries.coeff k f))) ∧ ∀ n, ∀ x ∈ G n, ev1 f x = ev1 (g n) x := by
  first | exact @GlobalTheory.ConvSer.exists_limit_of_agree_on_points | exact GlobalTheory.ConvSer.exists_limit_of_agree_on_points | (intros; apply GlobalTheory.ConvSer.exists_limit_of_agree_on_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsOrthogonalFrameNormsCoprimeOfUnimodularStatement
section
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_frame_norms_coprime_of_unimodular : ∀ (q g : ℕ) (S : Setup g), q.Prime → S.Ok → ¬ q ∣ S.d → ∃ (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ), (∀ i, x i ∈ S.La) ∧ (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) ∧ ∀ i, 0 < a i ∧ Nat.Coprime (a i) q := by
  first | exact @GlobalTheory.MomOne.exists_orthFrame | exact GlobalTheory.MomOne.exists_orthFrame | (intros; apply GlobalTheory.MomOne.exists_orthFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPadicIntFrameChangeEtaleBasisStatement
section
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicInt_frame_change_etale_basis : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (g : ℕ) (S : Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ) (r : ℕ) (b : Fin r → Fin g → ℂ), S.Ok → Split S.d q → (∀ i, x i ∈ S.La) → (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) → (∀ i, 0 < a i ∧ Nat.Coprime (a i) q) → S.NNBasis q b → ∃ T : (Fin r → ℤ_[q]) ≃ₜ (Fin g → ℤ_[q]), ∀ A i, GlobalTheory.MomOne.zc (T A i) = ∑ j, GlobalTheory.MomOne.zc (A j) * ι (beta S.d S.Hm (x i) (b j)) := by
  first | exact @GlobalTheory.MomOne.frameChange | exact GlobalTheory.MomOne.frameChange | (intros; apply GlobalTheory.MomOne.frameChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MultiplicativeShiftEqTranslateBySmallPointStatement
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicativeShift_eq_translate_by_small_point : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω ζ : ℂ_[q]) (p : ℂ), M.MChart ω → M.At ω ζ p → hat M.ι (C ω * logS) (fun z => M.u (z + p)) = shiftS ζ (hat M.ι (C ω * logS) M.u) ∧ hat M.ι (C ω * logS) (fun z => M.w (z + p)) = shiftS ζ (hat M.ι (C ω * logS) M.w) := by
  first | exact @GlobalTheory.MomOne.SmallTranslate.shift_eq_translate | exact GlobalTheory.MomOne.SmallTranslate.shift_eq_translate | (intros; apply GlobalTheory.MomOne.SmallTranslate.shift_eq_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesConvergentSubstIsRingHomOnBoundedStatement
section
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeriesConvergentSubst_isRingHom_on_bounded : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (σ τ : Type) [Fintype σ] (s : σ → MvPowerSeries τ K), (∀ i, Small (s i)) → (∀ S T : MvPowerSeries σ K, Bdd S → Bdd T → csub s (S + T) = csub s S + csub s T ∧ csub s (S - T) = csub s S - csub s T ∧ csub s (S * T) = csub s S * csub s T) ∧ (∀ a : K, csub s (MvPowerSeries.C a) = MvPowerSeries.C a) ∧ (∀ i, csub s (MvPowerSeries.X i) = s i) ∧ (∀ (S : MvPowerSeries σ K) (n : ℕ), Bdd S → csub s (S ^ n) = csub s S ^ n) ∧ (∀ (ι : Type) (t : Finset ι) (f : ι → MvPowerSeries σ K), (∀ i ∈ t, Bdd (f i)) → csub s (∏ i ∈ t, f i) = ∏ i ∈ t, csub s (f i)) ∧ (∀ (k ι : Type) [CommRing k] (φ : k →+* K) (a : ι → MvPowerSeries σ K) (A : MvPolynomial ι k), (∀ j, Bdd (a j)) → csub s (MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries σ K).comp φ) a A) = MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries τ K).comp φ) (fun j => csub s (a j)) A) := by
  first | exact @GlobalTheory.ConvSer.csub_ring_map | exact GlobalTheory.ConvSer.csub_ring_map | (intros; apply GlobalTheory.ConvSer.csub_ring_map <;> assumption)
end

