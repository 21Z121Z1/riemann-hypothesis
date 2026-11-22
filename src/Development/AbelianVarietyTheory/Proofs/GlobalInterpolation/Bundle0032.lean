import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0024
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0027
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerronIntegralShiftPrimitiveLFunction
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimeCountRelativeErrorOfPsiRelativeError
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0022
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0028
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0001
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0030

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsProdAndSum
section
noncomputable section

namespace GlobalTheory.MomN

open GlobalTheory.MomOne

variable {q : ℕ} [Fact q.Prime]

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem momInt_mul (ι : ℂ ≃+* ℂ_[q]) {κ : Type} [Fintype κ] (v : κ → V) {F G : V → ℂ}
    (hF : ContDiff ℂ ⊤ F) (hG : ContDiff ℂ ⊤ G) (mF : MomInt ι v F) (mG : MomInt ι v G) :
    MomInt ι v (fun z => F z * G z) := by
  classical
  have cF := (GlobalTheory.T.mahlerCoefficient_norm_le_one_iff_jets_boundedMeasureMoments q ι V κ v F hF).1 mF
  have cG := (GlobalTheory.T.mahlerCoefficient_norm_le_one_iff_jets_boundedMeasureMoments q ι V κ v G hG).1 mG
  refine (GlobalTheory.T.mahlerCoefficient_norm_le_one_iff_jets_boundedMeasureMoments q ι V κ v _ (hF.mul hG)).2 fun n => ?_
  rw [GlobalTheory.T.mahlerJetCoefficient_mul V κ v F G hF hG n, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [map_mul, norm_mul]
  exact mul_le_one₀ (cF k) (norm_nonneg _) (cG _)

theorem momInt_add (ι : ℂ ≃+* ℂ_[q]) {κ : Type} [Fintype κ] (v : κ → V) {F G : V → ℂ}
    (hF : ContDiff ℂ ⊤ F) (hG : ContDiff ℂ ⊤ G) (mF : MomInt ι v F) (mG : MomInt ι v G) :
    MomInt ι v (fun z => F z + G z) := by
  obtain ⟨μ, hμ, eμ⟩ := mF
  obtain ⟨ν, hν, eν⟩ := mG
  refine ⟨μ + ν, ?_, fun k j f hf => ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    rw [one_mul, ContinuousLinearMap.add_apply]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · simpa using μ.le_of_opNorm_le hμ f
    · simpa using ν.le_of_opNorm_le hν f
  · have h : iteratedFDeriv ℂ k (fun z => F z + G z) 0 =
        iteratedFDeriv ℂ k F 0 + iteratedFDeriv ℂ k G 0 :=
      iteratedFDeriv_add_apply (hF.contDiffAt.of_le (by exact_mod_cast le_top))
        (hG.contDiffAt.of_le (by exact_mod_cast le_top))
    rw [h, ContinuousMultilinearMap.add_apply, map_add, eμ k j f hf, eν k j f hf,
      ContinuousLinearMap.add_apply]

theorem momInt_const_mul (ι : ℂ ≃+* ℂ_[q]) {κ : Type} [Fintype κ] (v : κ → V) {c : ℂ} {G : V → ℂ}
    (hG : ContDiff ℂ ⊤ G) (hc : ‖ι c‖ ≤ 1) (mG : MomInt ι v G) :
    MomInt ι v (fun z => c * G z) := by
  obtain ⟨μ, hμ, eμ⟩ := mG
  refine ⟨ι c • μ, ?_, fun k j f hf => ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    rw [one_mul, ContinuousLinearMap.smul_apply, norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (μ.le_of_opNorm_le hμ f |>.trans (by simp))
  · have h : iteratedFDeriv ℂ k (fun z => c * G z) 0 = c • iteratedFDeriv ℂ k G 0 := by
      have := iteratedFDeriv_const_smul_apply (𝕜 := ℂ) (a := c) (f := G) (i := k) (x := (0 : V))
        (hG.contDiffAt.of_le (by exact_mod_cast le_top))
      simpa [Pi.smul_def, smul_eq_mul] using this
    rw [h, ContinuousMultilinearMap.smul_apply, smul_eq_mul, map_mul, eμ k j f hf,
      ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem latInt_mul (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (Λ : AddSubgroup V) {F G : V → ℂ}
    (hF : ContDiff ℂ ⊤ F) (hG : ContDiff ℂ ⊤ G) (mF : LatInt ι ω Λ F) (mG : LatInt ι ω Λ G) :
    LatInt ι ω Λ (fun z => F z * G z) :=
  fun κ _ v hv => momInt_mul ι _ hF hG (mF κ v hv) (mG κ v hv)

theorem latInt_add (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (Λ : AddSubgroup V) {F G : V → ℂ}
    (hF : ContDiff ℂ ⊤ F) (hG : ContDiff ℂ ⊤ G) (mF : LatInt ι ω Λ F) (mG : LatInt ι ω Λ G) :
    LatInt ι ω Λ (fun z => F z + G z) :=
  fun κ _ v hv => momInt_add ι _ hF hG (mF κ v hv) (mG κ v hv)

theorem latInt_const_mul (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (Λ : AddSubgroup V) {c : ℂ} {G : V → ℂ}
    (hG : ContDiff ℂ ⊤ G) (hc : ‖ι c‖ ≤ 1) (mG : LatInt ι ω Λ G) :
    LatInt ι ω Λ (fun z => c * G z) :=
  fun κ _ v hv => momInt_const_mul ι _ hG hc (mG κ v hv)

theorem latInt_prod_sum : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (ω : ℂ_[q]) (Λ : AddSubgroup V),
    (∀ (m : Type) [Fintype m] (G : m → V → ℂ), (∀ j, ContDiff ℂ ⊤ (G j)) → (∀ j, LatInt ι ω Λ (G j)) →
      LatInt ι ω Λ fun z => ∏ j, G j z) ∧
    ∀ (m : Type) (s : Finset m) (c : m → ℂ) (G : m → V → ℂ), (∀ j ∈ s, ContDiff ℂ ⊤ (G j)) →
      (∀ j ∈ s, ‖ι (c j)‖ ≤ 1) → (∀ j ∈ s, LatInt ι ω Λ (G j)) →
      LatInt ι ω Λ fun z => ∑ j ∈ s, c j * G j z := by
  intro q _ ι V _ _ ω Λ
  classical
  refine ⟨fun m _ G hd hl => ?_, fun m s c G hd hc hl => ?_⟩
  · have key : ∀ s : Finset m, ContDiff ℂ ⊤ (fun z => ∏ j ∈ s, G j z) ∧
        LatInt ι ω Λ (fun z => ∏ j ∈ s, G j z) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using ⟨contDiff_const, latInt_one ι ω Λ⟩
      | insert a s ha ih =>
        simp only [Finset.prod_insert ha]
        exact ⟨(hd a).mul ih.1, latInt_mul ι ω Λ (hd a) ih.1 (hl a) ih.2⟩
    exact (key Finset.univ).2
  · have key : ∀ t : Finset m, t ⊆ s → ContDiff ℂ ⊤ (fun z => ∑ j ∈ t, c j * G j z) ∧
        LatInt ι ω Λ (fun z => ∑ j ∈ t, c j * G j z) := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
        intro _
        simpa using ⟨contDiff_const, latInt_zero ι ω Λ⟩
      | insert a t ha ih =>
        intro hts
        have hat : a ∈ s := hts (by simp)
        obtain ⟨h1, h2⟩ := ih fun x hx => hts (by simp [hx])
        simp only [Finset.sum_insert ha]
        have h3 : ContDiff ℂ ⊤ (fun z => c a * G a z) := contDiff_const.mul (hd a hat)
        exact ⟨h3.add h1, latInt_add ι ω Λ h3 h1
          (latInt_const_mul ι ω Λ (hd a hat) (hc a hat) (hl a hat)) h2⟩
    exact (key s subset_rfl).2

end GlobalTheory.MomN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsPullback
section
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.MomN

private def zcRing (q : ℕ) [Fact q.Prime] : ℤ_[q] →+* ℂ_[q] :=
  (algebraMap ℚ_[q] ℂ_[q]).comp PadicInt.Coe.ringHom

private theorem zc_eq (q : ℕ) [Fact q.Prime] (a : ℤ_[q]) : zc a = zcRing q a := rfl

private theorem isUnit_of_coprime (q : ℕ) [hq : Fact q.Prime] (s : ℕ) (h : Nat.Coprime s q) : IsUnit (s : ℤ_[q]) := by
  refine PadicInt.isUnit_iff.2 (le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => ?_))
  have h1 : ‖((s : ℤ) : ℤ_[q])‖ < 1 := by simpa using hlt
  have h2 : (q : ℤ) ∣ (s : ℤ) := (PadicInt.norm_int_lt_one_iff_dvd _).1 h1
  have h3 : q ∣ s := Int.natCast_dvd_natCast.1 h2
  exact (Nat.Prime.coprime_iff_not_dvd hq.out).1 h.symm h3

theorem latInt_pull : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (V' : Type) [NormedAddCommGroup V'] [NormedSpace ℂ V'] (ω : ℂ_[q]) (Λ : AddSubgroup V) (Λ' : AddSubgroup V') (g : V' →L[ℂ] V) (G : V → ℂ), ContDiff ℂ ⊤ G → (∀ x ∈ Λ', ∃ s : ℕ, Nat.Coprime s q ∧ s • g x ∈ Λ) → LatInt ι ω Λ G → LatInt ι ω Λ' fun z => G (g z) := by
  classical
  intro q _ ι V _ _ V' _ _ ω Λ Λ' g G hG hg hL κ _ v hv
  choose s hs hsΛ using fun i => hg (v i) (hv i)
  have hs0 : ∀ i, (s i : ℂ) ≠ 0 := by
    intro i h0
    have h1 : s i = 0 := by exact_mod_cast h0
    have h2 := hs i
    rw [h1, Nat.coprime_zero_left] at h2
    exact (Fact.out : q.Prime).one_lt.ne' h2
  choose u hu using fun i => isUnit_of_coprime q (s i) (hs i)
  have hM := hL κ (fun i => s i • g (v i)) hsΛ
  have hP : MomInt ι (fun i => ι.symm ω • g (v i)) G := by
    refine GlobalTheory.T.jetsAreBoundedMeasureMoments_padicInt_matrix_change q ι V κ κ (fun i => ι.symm ω • s i • g (v i)) (fun i => ι.symm ω • g (v i))
      (fun i j => if i = j then (s i : ℂ)⁻¹ else 0) (fun i j => if i = j then ((u i)⁻¹ : ℤ_[q]ˣ).1 else 0) G ?_ ?_ hM
    · intro i j
      by_cases hij : i = j
      · subst hij
        simp only [if_true, map_inv₀, map_natCast, zc_eq]
        have e : zcRing q ((u i)⁻¹ : ℤ_[q]ˣ).1 * (s i : ℂ_[q]) = 1 := by
          have e1 : (s i : ℂ_[q]) = zcRing q (u i).1 := by rw [hu i, map_natCast]
          rw [e1, ← map_mul, Units.inv_mul, map_one]
        exact (eq_inv_of_mul_eq_one_left e).symm
      · simp [hij, zc_eq]
    · intro i
      simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_comm (ι.symm ω) (s i : ℂ), smul_smul, inv_mul_cancel₀ (hs0 i), one_smul]
  obtain ⟨μ, hμ, hm⟩ := hP
  refine ⟨μ, hμ, fun k j f hf => ?_⟩
  rw [← hm k j f hf]
  congr 1
  have e := g.iteratedFDeriv_comp_right hG 0 (i := k) le_top
  have e2 : iteratedFDeriv ℂ k (fun z => G (g z)) 0 = iteratedFDeriv ℂ k (G ∘ g) 0 := rfl
  rw [e2, e]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, Function.comp_def, map_smul]

end GlobalTheory.MomN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientMulOfDisjointSupport
section
open GlobalTheory.MomN

namespace GlobalTheory

theorem mahler_mul_of_disjoint_support :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ι' : Type) [Fintype ι'] [DecidableEq ι']
      (u : ι' → V) (F H : V → ℂ), ContDiff ℂ ⊤ F → ContDiff ℂ ⊤ H → ∀ (S T : Finset ι'), Disjoint S T →
      (∀ k : ι' → ℕ, (∃ p, p ∉ S ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u F k = 0) →
      (∀ k : ι' → ℕ, (∃ p, p ∉ T ∧ k p ≠ 0) → GlobalTheory.MomN.mahler u H k = 0) →
      (∀ N : ι' → ℕ, (∃ p, p ∉ S ∪ T ∧ N p ≠ 0) → GlobalTheory.MomN.mahler u (fun z => F z * H z) N = 0) ∧
      (∀ N : ι' → ℕ, (∀ p, p ∉ S ∪ T → N p = 0) →
        GlobalTheory.MomN.mahler u (fun z => F z * H z) N =
          GlobalTheory.MomN.mahler u F (fun p => if p ∈ S then N p else 0) *
            GlobalTheory.MomN.mahler u H (fun p => if p ∈ T then N p else 0)) := by
  intro V _ _ ι' _ _ u F H hF hH S T hST hFS hHT
  constructor
  · intro N ⟨p, hp, hNp⟩
    rw [GlobalTheory.T.mahlerJetCoefficient_mul V ι' u F H hF hH N]
    apply Finset.sum_eq_zero
    intro k _
    have hpS : p ∉ S := fun h => hp (Finset.mem_union_left _ h)
    have hpT : p ∉ T := fun h => hp (Finset.mem_union_right _ h)
    by_cases hk : k p = 0
    · rw [hHT _ ⟨p, hpT, by simp [hk, hNp]⟩, mul_zero]
    · rw [hFS _ ⟨p, hpS, hk⟩, zero_mul]
  · intro N hN
    rw [GlobalTheory.T.mahlerJetCoefficient_mul V ι' u F H hF hH N]
    rw [Finset.sum_eq_single (fun p => if p ∈ S then N p else 0)]
    · have hfun : (fun i => N i - (fun p => if p ∈ S then N p else 0) i) =
          (fun p => if p ∈ T then N p else 0) := by
        funext p
        by_cases hS : p ∈ S
        · have hT : p ∉ T := Finset.disjoint_left.mp hST hS
          simp only [hS, hT, if_true, if_false, Nat.sub_self]
        · by_cases hT : p ∈ T
          · simp only [hS, hT, if_true, if_false, Nat.sub_zero]
          · have h0 : N p = 0 := hN p (by simp [hS, hT])
            simp only [hS, hT, if_false, h0, Nat.sub_zero]
      exact congrArg (fun g => GlobalTheory.MomN.mahler u F (fun p => if p ∈ S then N p else 0) *
        GlobalTheory.MomN.mahler u H g) hfun
    · intro k hk hne
      by_contra hprod
      have h1 : GlobalTheory.MomN.mahler u F k ≠ 0 := left_ne_zero_of_mul hprod
      have h2 : GlobalTheory.MomN.mahler u H (fun i => N i - k i) ≠ 0 := right_ne_zero_of_mul hprod
      apply hne
      funext p
      rw [Fintype.mem_piFinset] at hk
      have hkp : k p ≤ N p := Nat.lt_succ_iff.mp (Finset.mem_range.mp (hk p))
      by_cases hS : p ∈ S
      · have hT : p ∉ T := Finset.disjoint_left.mp hST hS
        have : N p - k p = 0 := by
          by_contra h
          exact h2 (hHT _ ⟨p, hT, h⟩)
        simp only [hS, if_true]
        omega
      · simp only [hS, if_false]
        by_contra h
        exact h1 (hFS _ ⟨p, hS, h⟩)
    · intro h
      exfalso
      apply h
      rw [Fintype.mem_piFinset]
      intro p
      rw [Finset.mem_range]
      split_ifs <;> omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NegReLogDerivPrincipalLFunctionLeStatement
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.neg_re_logDeriv_principalLFunction_le : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (σ t : ℝ), 1 < σ → σ ≤ 2 → -(deriv (LFunction (1 : DirichletCharacter ℂ q)) (σ + t * I) / LFunction (1 : DirichletCharacter ℂ q) (σ + t * I)).re ≤ (1 / ((σ : ℂ) + t * I - 1)).re + C * Real.log (q * (|t| + 2)) := by
  first | exact @GlobalTheory.PrincipalLogDeriv.neg_re_logDeriv_le | exact GlobalTheory.PrincipalLogDeriv.neg_re_logDeriv_le | (intros; apply GlobalTheory.PrincipalLogDeriv.neg_re_logDeriv_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerronIntegralShiftPrimitiveLFunctionStatement
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perron_integral_shift_primitive_LFunction : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ u T : ℝ, 2 ≤ T → T ≤ u → ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧ ‖(1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ in (-T')..T', (-(deriv (LFunction χ) (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) / LFunction χ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I)) * (u : ℂ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) / (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I))) - (if N = 1 then (u : ℂ) else 0) + ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) + ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖) := by
  first | exact @GlobalTheory.PerronShift.perron_shift | exact GlobalTheory.PerronShift.perron_shift | (intros; apply GlobalTheory.PerronShift.perron_shift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimeCountRelativeErrorOfPsiRelativeErrorStatement
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primeCount_relative_error_of_psi_relative_error : ∀ c₂ c₃ C cS : ℝ, 0 < c₂ → 0 < c₃ → 0 < C → 0 < cS → ∃ c₂' c₃' C' : ℝ, 0 < c₂' ∧ 0 < c₃' ∧ 0 < C' ∧ ∀ (B φ β : ℝ) (θ : ℤ) (P : ℕ → Prop), 3 ≤ B → 1 ≤ φ → φ ≤ B → (θ = 0 ∨ ((θ = 1 ∨ θ = -1) ∧ 7 / 8 ≤ β ∧ cS / B ^ 3 ≤ 1 - β)) → (∀ u : ℝ, B ^ c₂ ≤ u → |φ * (∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter P, Λ n) - (u - θ * (u ^ β / β))| ≤ C * (Real.exp (-c₃ * Real.log u / Real.log B) + Real.exp (-Real.sqrt (c₃ * Real.log u))) * (u - θ * (u ^ β / β))) → ∀ X : ℝ, B ^ c₂' ≤ X → |φ * (((Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ P p)).card : ℝ) - Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X| ≤ C' * (Real.exp (-c₃' * Real.log X / Real.log B) + Real.exp (-Real.sqrt (c₃' * Real.log X))) * Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X := by
  first | exact @GlobalTheory.Lin.pi_rel_of_psi_rel | exact GlobalTheory.Lin.pi_rel_of_psi_rel | (intros; apply GlobalTheory.Lin.pi_rel_of_psi_rel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QBinomialFiniteStatement
section
open Complex
open scoped Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_range_one_add_mul_pow_two_mul_eq_sum_qBinom : ∀ (s X : ℂ), ‖s‖ < 1 → ∀ m : ℕ, ∏ k ∈ Finset.range m, (1 + X * s ^ (2 * k)) = ∑ k ∈ Finset.range (m + 1), GlobalTheory.JacobiTriple.qBinom (s ^ 2) m k * s ^ (k * (k - 1)) * X ^ k := by
  first | exact @GlobalTheory.JacobiTriple.QBinomial.qBinomial_finite | exact GlobalTheory.JacobiTriple.QBinomial.qBinomial_finite | (intros; apply GlobalTheory.JacobiTriple.QBinomial.qBinomial_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadricPointGaugePolarCoordinatesCompareTangentGStatement
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadricPointGauge_polarCoordinates_compare_tangentGauge : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ), 1 < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ u : ℝ × Sp P' Q', u.1 ∈ Set.Ioo (-Real.pi) Real.pi → (tanGauge u < t⁻¹ * r → ptGauge e (polarPt e u) < r) ∧ (ptGauge e (polarPt e u) < r → tanGauge u < t * r) := by
  first | exact @GlobalTheory.PolarCompare.polar_compare | exact GlobalTheory.PolarCompare.polar_compare | (intros; apply GlobalTheory.PolarCompare.polar_compare <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadricPointGaugeSectionMulBlockCompareStatement
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadricPointGauge_section_mul_block_compare : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (j : UpqT P' Q' → UpqT P Q), IsBlockEmb e j → ∀ t : ℝ, 1 < t → ∃ δ : ℝ, 0 < δ ∧ ∀ (y : Sp P Q) (a : UpqT P Q), ptGauge e y < δ → act a (baseVec e) = y → (∀ b, ‖UpqT.mat a (e none) (e (some b))‖ = ‖y (e (some b))‖) → (∀ i b, ‖(UpqT.mat a - 1) (e (some i)) (e (some b))‖ = ‖y (e (some i))‖ * ‖y (e (some b))‖ / ‖1 + y (e none)‖) → ∀ g : UpqT P' Q', ptGauge e y + gauge g ≤ t * gauge (a * j g) ∧ gauge (a * j g) ≤ t * (ptGauge e y + gauge g) := by
  first | exact @GlobalTheory.SectionGaugeCompare.gauge_section_mul_block | exact GlobalTheory.SectionGaugeCompare.gauge_section_mul_block | (intros; apply GlobalTheory.SectionGaugeCompare.gauge_section_mul_block <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientInvariantMeasureExistsUniqueUnimodularStatement
section
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientInvariantMeasure_exists_unique_unimodular : InvariantMeasureClause := by
  first | exact @GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular.invariantMeasureClause | exact GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular.invariantMeasureClause | (intros; apply GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular.invariantMeasureClause <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionFamilyLogDerivPositivity
section
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.LFamPos

theorem norm_lamChi_le (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (n : ℕ) : ‖𝓕.lamChi χ n‖ ≤ 2 * Λ n := by
  refine le_trans ?_ (𝓕.lam_le n)
  unfold LFam.lamChi
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => ?_)
  rw [norm_mul, AddChar.norm_apply, one_mul, Complex.norm_real, Real.norm_of_nonneg (𝓕.lam_nonneg g n)]

theorem summable_lamChi (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (𝓕.lamChi χ) s := by
  have h := (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).smul (2 : ℂ)
  refine Summable.of_norm_bounded h.norm fun n => ?_
  refine LSeries.norm_term_le s ?_
  refine (norm_lamChi_le 𝓕 χ n).trans (le_of_eq ?_)
  simp [abs_of_nonneg vonMangoldt_nonneg]

theorem hasSum_re (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (σ : ℝ) (u : ℂ) (hs : 1 < σ) (hu : u.re = 0) :
    HasSum (fun n : ℕ => ∑ g, (if n = 0 then 0 else 𝓕.lam g n * (n : ℝ) ^ (-σ)) * (χ g * (n : ℂ) ^ (-u)).re)
      (LSeries (𝓕.lamChi χ) (σ + u)).re := by
  have h := (summable_lamChi 𝓕 χ (s := σ + u) (by simpa [hu] using hs)).hasSum
  have h2 := Complex.hasSum_re h
  convert h2 using 2 with n
  · by_cases hn : n = 0
    · simp [hn]
    · have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      rw [LSeries.term_of_ne_zero hn, LFam.lamChi, Finset.sum_div, Complex.re_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [if_neg hn, ← Complex.re_ofReal_mul]
      congr 1
      rw [div_eq_mul_inv, ← cpow_neg, neg_add, cpow_add _ _ hn']
      push_cast
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
      push_cast
      ring
  · rfl

theorem hasSum_re₀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (σ : ℝ) (hs : 1 < σ) :
    HasSum (fun n : ℕ => ∑ g, (if n = 0 then 0 else 𝓕.lam g n * (n : ℝ) ^ (-σ)) * (χ g).re)
      (LSeries (𝓕.lamChi χ) σ).re := by
  simpa using hasSum_re 𝓕 χ σ 0 hs rfl

theorem w_nonneg (𝓕 : LFam) (σ : ℝ) (n : ℕ) (g : 𝓕.G) :
    0 ≤ (if n = 0 then 0 else 𝓕.lam g n * (n : ℝ) ^ (-σ)) := by
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (𝓕.lam_nonneg g n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem pm_one {G : Type} [AddCommGroup G] (χ : AddChar G ℂ) (h : χ * χ = 1) (g : G) :
    χ g = 1 ∨ χ g = -1 := by
  have : χ g * χ g = 1 := by
    have := congrArg (fun φ : AddChar G ℂ => φ g) h
    simpa using this
  exact mul_self_eq_one_iff.mp this

theorem trig (z : ℂ) (hz : ‖z‖ = 1) : 0 ≤ 3 + 4 * z.re + (z * z).re := by
  have h : z.re * z.re + z.im * z.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz]; norm_num
  rw [Complex.mul_re]
  nlinarith [sq_nonneg (z.re + 1)]

theorem positivity : ∀ (𝓕 : LFam) (χ ψ : AddChar 𝓕.G ℂ) (σ t : ℝ), 1 < σ → 0 ≤ 3 * (LSeries (𝓕.lamChi 1) σ).re + 4 * (LSeries (𝓕.lamChi χ) (σ + t * I)).re + (LSeries (𝓕.lamChi (χ * χ)) (σ + 2 * t * I)).re ∧ 0 ≤ (LSeries (𝓕.lamChi 1) σ).re ∧ (χ * χ = 1 → ψ * ψ = 1 → 0 ≤ (LSeries (𝓕.lamChi 1) σ).re + (LSeries (𝓕.lamChi χ) σ).re ∧ 0 ≤ (LSeries (𝓕.lamChi 1) σ).re + (LSeries (𝓕.lamChi χ) σ).re + (LSeries (𝓕.lamChi ψ) σ).re + (LSeries (𝓕.lamChi (χ * ψ)) σ).re) := by
  intro 𝓕 χ ψ σ t hσ
  have h1 := hasSum_re₀ 𝓕 1 σ hσ
  refine ⟨?_, ?_, fun hχ hψ => ⟨?_, ?_⟩⟩
  · have h2 := hasSum_re 𝓕 χ σ (t * I) hσ (by simp)
    have h3 := hasSum_re 𝓕 (χ * χ) σ (2 * t * I) hσ (by simp)
    refine HasSum.nonneg (fun n => ?_) (((h1.mul_left 3).add (h2.mul_left 4)).add h3)
    by_cases hn : n = 0
    · simp [hn]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun g _ => ?_
    have hz : ‖χ g * (n : ℂ) ^ (-(t * I))‖ = 1 := by
      rw [norm_mul, AddChar.norm_apply, one_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp
    have ht := trig _ hz
    have he : (χ * χ) g * (n : ℂ) ^ (-(2 * t * I)) = (χ g * (n : ℂ) ^ (-(t * I))) * (χ g * (n : ℂ) ^ (-(t * I))) := by
      rw [show -(2 * (t : ℂ) * I) = -(t * I) + -(t * I) by ring, cpow_add _ _ hn', AddChar.mul_apply]
      ring
    rw [he, AddChar.one_apply, Complex.one_re]
    have := mul_nonneg (w_nonneg 𝓕 σ n g) ht
    linarith
  · refine HasSum.nonneg (fun n => Finset.sum_nonneg fun g _ => ?_) h1
    rw [AddChar.one_apply, Complex.one_re, mul_one]
    exact w_nonneg 𝓕 σ n g
  · refine HasSum.nonneg (fun n => ?_) (h1.add (hasSum_re₀ 𝓕 χ σ hσ))
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun g _ => ?_
    have hw := w_nonneg 𝓕 σ n g
    rw [AddChar.one_apply]
    rcases pm_one χ hχ g with h | h <;> rw [h] <;> simp only [one_re, neg_re] <;> linarith
  · refine HasSum.nonneg (fun n => ?_) (((h1.add (hasSum_re₀ 𝓕 χ σ hσ)).add (hasSum_re₀ 𝓕 ψ σ hσ)).add (hasSum_re₀ 𝓕 (χ * ψ) σ hσ))
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun g _ => ?_
    have hw := w_nonneg 𝓕 σ n g
    rw [AddChar.one_apply, AddChar.mul_apply]
    rcases pm_one χ hχ g with h | h <;> rcases pm_one ψ hψ g with h' | h' <;> rw [h, h'] <;>
      simp only [one_re, neg_re, mul_one, mul_neg, neg_neg] <;> linarith

end GlobalTheory.Hk.LFamPos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TendstoSublevelDensityProdMeasureStatement
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_sublevel_density_prod_measure : ∀ (A₁ E₁ A₂ E₂ : Type) [MeasurableSpace A₁] [MeasurableSpace E₁] [MeasurableSpace A₂] [MeasurableSpace E₂] (m₁ : Measure A₁) (l₁ : Measure E₁) (m₂ : Measure A₂) (l₂ : Measure E₂) [SFinite m₁] [SFinite l₁] [SFinite m₂] [SFinite l₂] (n₁ : A₁ → ℝ) (N₁ : E₁ → ℝ) (n₂ : A₂ → ℝ) (N₂ : E₂ → ℝ) (c₁ c₂ : ℝ≥0∞), Measurable n₁ → Measurable N₁ → Measurable n₂ → Measurable N₂ → (∀ x, 0 ≤ n₁ x) → (∀ x, 0 ≤ N₁ x) → (∀ x, 0 ≤ n₂ x) → (∀ x, 0 ≤ N₂ x) → c₁ ≠ ⊤ → c₂ ≠ ⊤ → (∀ r : ℝ, 0 < r → l₁ {x | N₁ x < r} ≠ 0 ∧ l₁ {x | N₁ x < r} ≠ ⊤) → (∀ r : ℝ, 0 < r → l₂ {x | N₂ x < r} ≠ 0 ∧ l₂ {x | N₂ x < r} ≠ ⊤) → Tendsto (fun r : ℝ => m₁ {x | n₁ x < r} / l₁ {x | N₁ x < r}) (𝓝[>] 0) (𝓝 c₁) → Tendsto (fun r : ℝ => m₂ {x | n₂ x < r} / l₂ {x | N₂ x < r}) (𝓝[>] 0) (𝓝 c₂) → Tendsto (fun r : ℝ => (m₁.prod m₂) {p | n₁ p.1 + n₂ p.2 < r} / (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r}) (𝓝[>] 0) (𝓝 (c₁ * c₂)) := by
  first | exact @GlobalTheory.SublevelDensity.tendsto_prod_density | exact GlobalTheory.SublevelDensity.tendsto_prod_density | (intros; apply GlobalTheory.SublevelDensity.tendsto_prod_density <;> assumption)
end

