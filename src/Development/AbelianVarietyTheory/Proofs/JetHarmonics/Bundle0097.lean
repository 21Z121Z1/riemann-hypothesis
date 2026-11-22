import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0094
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0088
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0082
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerStepRaisingUnitaryComplementStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0080
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0050
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0045
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0059
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0054
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0058
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsWignerContractionChainLoweringStatement
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wignerContraction_chain_lowering : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)) (n₀ : ℕ), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → IsFrameOf (n + 1) r [z] B → (∀ j, j > l → L j < L l - (n₀ : ℤ)) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) - (n₀ : ℝ))) ∧ GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π n₀ A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA (EB π B)) (shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((∏ j ∈ Finset.range n₀, GlobalTheory.WigSh.wM (Function.update L l (L l - (j : ℤ))) M l : ℝ) : ℂ) • v := by
  first | exact @GlobalTheory.WigSh.exists_wigMap_chain_lowering | exact GlobalTheory.WigSh.exists_wigMap_chain_lowering | (intros; apply GlobalTheory.WigSh.exists_wigMap_chain_lowering <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsWignerContractionChainRaising
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem chain_raise : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)) (n₀ : ℕ), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → IsFrameOf (n + 1) r [z] B → (∀ j, j < l → L l + (n₀ : ℤ) < L j) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + (n₀ : ℝ))) ∧ GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π n₀ A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA (EB π B)) (shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((∏ j ∈ Finset.range n₀, GlobalTheory.WigSh.wP (Function.update L l (L l + (j : ℤ))) M l : ℝ) : ℂ) • v := by
  intro V _ _ _ n r z π u β L B l n₀ hz hT hπ hL hu hB
  induction n₀ with
  | zero =>
    intro _
    refine ⟨V, inferInstance, inferInstance, inferInstance, π, fun _ => ContinuousLinearMap.id ℂ V, ?_, ?_, ?_⟩
    · simpa using hπ
    · exact wigMap_zero_of_contraction V V (n + 1) r z π π _ (fun v => le_rfl) (fun h _ v => rfl)
    · intro M v _
      simp [ContinuousLinearMap.adjoint_id]
  | succ m ih =>
    intro hreg
    obtain ⟨V₂, i1, i2, i3, π₂, A, hπ₂, hA, hAA⟩ := ih (fun j hj => by
      have := hreg j hj
      push_cast at this
      omega)
    have hm0 : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
    have hL' : StrictAnti (Function.update L l (L l + (m : ℤ))) := by
      intro a b hab
      have h1 := hL hab
      by_cases ha : a = l
      · have hb : b ≠ l := fun hb => hab.ne (ha.trans hb.symm)
        subst ha
        rw [Function.update_self, Function.update_of_ne hb]
        omega
      · by_cases hb : b = l
        · subst hb
          rw [Function.update_self, Function.update_of_ne ha]
          have := hreg a hab
          push_cast at this
          omega
        · rw [Function.update_of_ne ha, Function.update_of_ne hb]
          exact h1
    have hu' : ∀ j : Fin (n + 1),
        ((Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + (m : ℝ)) ((j : ℕ) + 1) : ℝ) : ℂ) -
          ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + ((Function.update L l (L l + (m : ℤ)) j : ℤ) : ℂ) := by
      intro j
      by_cases hj : j = l
      · subst hj
        rw [Function.update_self, Function.update_self]
        have := hu j
        push_cast at this ⊢
        linear_combination this
      · have hj' : (j : ℕ) + 1 ≠ (l : ℕ) + 1 := fun h => hj (Fin.ext (by omega))
        rw [Function.update_of_ne hj, Function.update_of_ne hj']
        exact hu j
    have hreg' : ∀ j, Function.update L l (L l + (m : ℤ)) j ≠ Function.update L l (L l + (m : ℤ)) l + 1 := by
      intro j
      rw [Function.update_self]
      rcases lt_trichotomy j l with hj | hj | hj
      · rw [Function.update_of_ne hj.ne]
        have := hreg j hj
        push_cast at this
        omega
      · subst hj
        rw [Function.update_self]
        omega
      · rw [Function.update_of_ne hj.ne']
        have := hL hj
        omega
    obtain ⟨V₃, j1, j2, j3, π₃, a, hπ₃, ha, haa⟩ :=
      GlobalTheory.T.wigner_step_raising_unitary_complement V₂ n r z π₂ _ β _ B l hz hT hπ₂ hL' hu' hB hreg'
    refine ⟨V₃, j1, j2, j3, π₃, fun ω => (A ω).comp (a ω), ?_,
      wigMap_comp V V₂ V₃ (n + 1) r z π π₂ π₃ m 1 A a hA ha, ?_⟩
    · rw [Function.update_self, Function.update_idem] at hπ₃
      have e : u ((l : ℕ) + 1) + ((m + 1 : ℕ) : ℝ) = u ((l : ℕ) + 1) + (m : ℝ) + 1 := by
        push_cast
        ring
      rw [e]
      exact hπ₃
    · intro M v hv
      have hc := GlobalTheory.adjoint_mem_CapSp_subA V V₂ n r z π π₂ B (A (B (Fin.last n))) (shf β M)
        ⟨hπ.2.1, hπ.2.2.1⟩ ⟨hπ₂.2.1, hπ₂.2.2.1⟩ hπ.2.2.2.1 hπ₂.2.2.2.1 hB
        (fun h hh he => by
          have := hA.2.1 h hh (B (Fin.last n))
          rwa [he] at this) v hv
      have h2 := haa M _ hc
      show A (B (Fin.last n)) (a (B (Fin.last n))
        (ContinuousLinearMap.adjoint ((A (B (Fin.last n))).comp (a (B (Fin.last n)))) v)) = _
      rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply, h2, map_smul, hAA M v hv,
        smul_smul, Finset.prod_range_succ]
      push_cast
      rw [mul_comm]

end GlobalTheory.WigSh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupBesselGrowth
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomMass

theorem integrand_eq {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {d : ℝ} (hd : 0 ≤ d) (v : Wp) :
    ENNReal.ofReal (1 * (d * ‖v‖ ^ 2)) = ((‖((Real.sqrt d : ℝ) : ℂ) • v‖₊ : ENNReal)) ^ 2 := by
  rw [← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal]
  congr 1
  push_cast
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hd, one_mul]

theorem mom_mass : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν ≤ q0 → (∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (‖w‖ ^ 2)) ∧ (NzOn (R ν) (l ν) → IsIsoB (R ν) z π νq (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • l ν w) ∧ ∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = ENNReal.ofReal (‖w‖ ^ 2)) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν
  obtain ⟨hNum, hFam, hSide, hSF⟩ := hS
  obtain ⟨⟨-, -, -, -, hOK⟩, hfam⟩ := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum
  obtain ⟨-, -, hgap, -⟩ := hfam ν hν
  have hDS := hFam ν hν
  obtain ⟨hBe, hpos, hdeg⟩ := hSF ν hν
  have key : NzOn (R ν) (l ν) → IsIsoB (R ν) z π νq (fun w => ((Real.sqrt (dg ν) : ℝ) : ℂ) • l ν w) ∧
      ∀ w ∈ (R ν).sm, ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq =
        ENNReal.ofReal (‖w‖ ^ 2) := by
    intro hnz
    have hiso := GlobalTheory.T.isIsoB_sqrt_fdeg_smul_of_gap hH k r _ _ (h / 2) (R ν) Wp z π u μW μN μG νq (l ν) (dg ν) hDS hgap hOK hSide hBe
      hdeg hnz
    refine ⟨hiso, fun w hw => ?_⟩
    rw [← hiso.2 w hw]
    unfold PI.BesselPeriodGGP.l2SG
    exact lintegral_congr fun x => integrand_eq hpos.le _
  refine ⟨fun w hw => ?_, key⟩
  by_cases hnz : NzOn (R ν) (l ν)
  · exact ((key hnz).2 w hw).le
  · have hz : ∀ v ∈ (R ν).sm, l ν v = 0 := by
      intro v hv
      by_contra hne
      exact hnz ⟨v, hv, hne⟩
    obtain ⟨-, -, -, hsm, -⟩ := GlobalTheory.rep_basic_of_isDS hH.1.2.2.1 k r _ _ (R ν) hDS
    obtain ⟨-, -, -, -, hW, hN, hG, hq⟩ := hSide
    obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
    have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 h0 h1 hq
    have : ∫⁻ x, ENNReal.ofReal (1 * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq = 0 := by
      rw [← lintegral_zero (μ := νq)]
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [hz _ (hsm _ hx w hw)]
      simp
    rw [this]
    exact bot_le

end GlobalTheory.MomMass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupMomentGrowth
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.DualStepBound

theorem lOneNorm_sub_single_one_le {n : ℕ} (ν : Fin n → ℤ) (s : Fin n) :
    n1 (ν - Pi.single s 1 : Fin n → ℤ) ≤ n1 ν + 1 := by
  unfold n1
  have h1 : ∑ i, ((Pi.single s 1 : Fin n → ℤ) i).natAbs = 1 := by
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  rw [← h1, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by
    simpa using Int.natAbs_sub_le (ν i) ((Pi.single s 1 : Fin n → ℤ) i)

theorem sum_mem_sm {k r : ℕ} (R : Rep k r) {ι : Type} [Fintype ι] (x : ι → R.H) (hx : ∀ c, x c ∈ R.sm) :
    ∑ c, x c ∈ R.sm :=
  R.smSub.sum_mem (fun c _ => hx c)

theorem dual_step_bound : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν + 1 ≤ q0 → ∀ io pr ep, TensH dualM (Formalism.QuantumDeterminants.Hpk k r) (R ν) (fun s => R (ν - Pi.single s 1)) io pr ep → NzOn (R ν) (l ν) → ∀ (s : Fin (2 * r + k + 1)) (κ₀ : ℂ), (∀ v ∈ (R ν).sm, l (ν - Pi.single s 1) (∑ c, pr s c (tm (R ν) (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v c)) = κ₀ • l ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν - Pi.single s 1) ≤ Formalism.QuantumDeterminants.Tz k r z * b ^ 4 := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν io pr ep hT hnz s κ₀ hκ
  obtain ⟨hNum, hFam, hSide, hSF⟩ := hS
  have hν0 : n1 ν ≤ q0 := by omega
  have hν1 : ∀ t, n1 (ν - Pi.single t 1 : Fin (2 * r + k + 1) → ℤ) ≤ q0 :=
    fun t => (lOneNorm_sub_single_one_le ν t).trans hν
  have hDS : (R ν).IsDS _ _ := hFam ν hν0
  have hDS1 : ∀ t, (R (ν - Pi.single t 1)).IsDS (PI.BesselPeriodGGP.eps48 k r)
      (fun a => lam a + ((ν - Pi.single t 1 : Fin (2 * r + k + 1) → ℤ) a : ℝ)) := fun t => hFam _ (hν1 t)
  have hpar : ∀ t, (fun a => lam a + ((ν - Pi.single t 1 : Fin (2 * r + k + 1) → ℤ) a : ℝ))
      = (fun a => lam a + (ν a : ℝ)) - Pi.single t 1 := by
    intro t
    funext a
    by_cases hat : a = t
    · subst hat
      simp
      ring
    · simp [Pi.single_eq_of_ne hat]
  have hDS2 : ∀ t, (R (ν - Pi.single t 1)).IsDS (PI.BesselPeriodGGP.eps48 k r)
      ((fun a => lam a + (ν a : ℝ)) - Pi.single t 1) := fun t => hpar t ▸ hDS1 t
  obtain ⟨hBe, hdg, hdeg⟩ := hSF ν hν0
  obtain ⟨hBe1, hdg1, hdeg1⟩ := hSF _ (hν1 s)
  obtain ⟨c, hc, hcv⟩ := GlobalTheory.T.dual_tensor_bessel_moment hH k r _ _ (R ν) (fun s => R (ν - Pi.single s 1)) io pr Wp z π u
    μW μN μG νq (l ν) hNum.1 hDS hDS2 hT.raw hSide hBe.1 s
  have hdual := (GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hH k r _ _ dualM (Formalism.QuantumDeterminants.Hpk k r) 1 (R ν) (fun s => R (ν - Pi.single s 1))
    io pr ep _ _ _ Wp z π u μW μN μG νq (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) (l ν) hDS hDS2
    (GlobalTheory.isFRep_dualM k r) hT hSide
    (fun g hg => (GlobalTheory.FlagFix.fixes_wedge_and_form k r z hSide.1 g hg).2) hBe hnz s
    (l (ν - Pi.single s 1)) hBe1).2 κ₀ hκ
  obtain ⟨v, hv, hv0⟩ := hnz
  have hy : ∑ d, pr s d (tm (R ν) (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v d) ∈ (R (ν - Pi.single s 1)).sm :=
    sum_mem_sm _ _ fun d => (hT.raw.pr_sm s d).mem _ ((R ν).smSub.smul_mem _ hv)
  have e1 := hdual _ hy
  rw [hcv v hv, hκ v hv, smul_smul] at e1
  have e2 : c = (ep s : ℂ) * star κ₀ * κ₀ := smul_left_injective ℂ hv0 e1
  have hep : ‖(ep s : ℂ)‖ = 1 := by
    rcases hT.ep_sq s with h' | h' <;> simp [h']
  have e3 : ‖κ₀‖ ^ 2 = ‖c‖ := by
    rw [e2, norm_mul, norm_mul, hep, norm_star]; ring
  obtain ⟨c₀, hc₀, hdegs⟩ := GlobalTheory.BesselDegree.schur_fdeg hH k r (PI.BesselPeriodGGP.eps48 k r) μG
    hSide.2.2.2.2.2.2.1
  have hKS : PI.KFinSmooth := hH.1.2.2.1
  have d0 : dg ν = c₀ * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) := by
    obtain ⟨w, hw, -⟩ := (GlobalTheory.rep_basic_of_isDS hKS k r _ _ _ hDS).2.2.2.2.2.2.2.1
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    rw [← hdeg w hw0, (hdegs _ _ hDS).1 w hw0]
  have d1 : dg (ν - Pi.single s 1) = c₀ * Formalism.QuantumDeterminants.fdegHC
      (fun a => lam a + ((ν - Pi.single s 1 : Fin (2 * r + k + 1) → ℤ) a : ℝ)) := by
    obtain ⟨w, hw, -⟩ := (GlobalTheory.rep_basic_of_isDS hKS k r _ _ _ (hDS1 s)).2.2.2.2.2.2.2.1
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    rw [← hdeg1 w hw0, (hdegs _ _ (hDS1 s)).1 w hw0]
  have hratio := (GlobalTheory.FamilyDegreeRatio.degree_ratios k r lam u b bv ga h q0 hNum ν hν0).2.2 s
  have hp7 := GlobalTheory.PieriBound.lowering_bound k r lam u b bv ga h q0 hNum ν hν0 s
  have hgap := ((GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum).2 ν hν0).2.2.2
  have hB : (∏ t ∈ univ.erase s, |lam s + (ν s : ℝ) - (lam t + (ν t : ℝ))|) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun t ht => abs_ne_zero.2 ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase ht) with h' | h'
    · have := hgap t s h'
      linarith
    · have := hgap s t h'
      linarith
  rw [Finset.prod_div_distrib] at hratio
  have hq : dg ν / dg (ν - Pi.single s 1)
      = (∏ t ∈ univ.erase s, |lam s + (ν s : ℝ) - (lam t + (ν t : ℝ))|) /
        ∏ t ∈ univ.erase s, |lam s + (ν s : ℝ) - 1 - (lam t + (ν t : ℝ))| := by
    rw [d0, d1, mul_div_mul_left _ _ hc₀.ne', ← inv_div, hratio, inv_div]
  rw [mul_div_assoc, hq, e3, hc, mul_assoc, div_mul_div_cancel₀ hB]
  exact mul_le_mul_of_nonneg_left hp7 hSide.2.1.le

end GlobalTheory.DualStepBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GermBoxProductEqProdGerms
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm.BoxGerm
open GlobalTheory.BoxFamily GlobalTheory.PowGerm.FrameN

section General

variable {X X' Y Y₀ Y₁ Z : Scheme.{0}} {M : LB X}

theorem gs_stalkMap (r : Z ⟶ X') (β : X' ⟶ X) (z : Z) (U : X.Opens) (h : β (r z) ∈ U) (a : Γ(X, U)) :
    (r.stalkMap z).hom (gs β (r z) U a) = gs (r ≫ β) z U a := by
  rw [← gs_pull r β z U h, gs_eq β _ U h, gs_eq r z _ h]
  exact Scheme.Hom.germ_stalkMap_apply r (β ⁻¹ᵁ U) z h _

theorem sval_along (hM : M.IsLB) (g : Y₁ ⟶ X) (z : Y ⟶ Y₁) (x : Y₀ ⟶ X) (s : Y ⟶ Y₀) (hzg : z ≫ g = s ≫ x) (q : ℕ)
    (σ : LB.Sec (LB.LinComb M (K := Fin 1) (fun _ => g) (fun _ => (q : ℤ))))
    (τ : LB.Gen (LB.LinComb M (K := Fin 1) (fun _ => x) (fun _ => (1 : ℤ)))) (a : Γ(Y, ⊤))
    (H : ∀ y J, Good M y J → sval σ z y J = gs (𝟙 Y) y ⊤ a * (val τ s y J ^ q).val)
    (r : Z ⟶ Y) (y : Z) (J) (hJ : Good M y J) :
    sval σ (r ≫ z) y J = gs r y ⊤ a * (val τ (r ≫ s) y J ^ q).val := by
  have m₀ : (z ≫ g) (r y) ∈ M.U (J (r ≫ z ≫ g)) := hJ (r ≫ z ≫ g)
  obtain ⟨J₀, hJ₀, e⟩ := exists_good M hM (r y) (fun _ : PUnit => z ≫ g) (fun _ => J (r ≫ z ≫ g)) (fun _ _ _ => rfl)
    (fun _ => m₀)
  have e' : J₀ (z ≫ g) = J (r ≫ z ≫ g) := e PUnit.unit
  have h := congrArg (r.stalkMap y).hom (H (r y) J₀ hJ₀)
  have m₁ : z (r y) ∈ LB.wchart M (fun _ : Fin 1 => g) (fun _ => J (r ≫ z ≫ g)) := Set.mem_iInter.2 fun _ => m₀
  have m₂ : s (r y) ∈ LB.wchart M (fun _ : Fin 1 => x) (fun _ => J (r ≫ z ≫ g)) :=
    Set.mem_iInter.2 fun _ => (show (s ≫ x) (r y) ∈ M.U (J (r ≫ z ≫ g)) from hzg ▸ m₀)
  rw [sval_of σ z _ J₀ (fun _ => J (r ≫ z ≫ g)) (fun _ => e'),
    val_of τ s _ J₀ (fun _ => J (r ≫ z ≫ g)) (fun _ => by rw [← hzg]; exact e'), map_mul,
    gs_stalkMap r (𝟙 Y) y ⊤ trivial, Category.comp_id, Units.val_pow_eq_pow_val, map_pow] at h
  rw [sval_of σ (r ≫ z) y J (fun _ => J (r ≫ z ≫ g)) (fun _ => by rw [Category.assoc]),
    val_of τ (r ≫ s) y J (fun _ => J (r ≫ z ≫ g)) (fun _ => by rw [Category.assoc, ← hzg]),
    Units.val_pow_eq_pow_val]
  refine (gs_stalkMap r z y _ m₁ _).symm.trans (h.trans (congrArg (fun u => gs r y ⊤ a * u ^ q) ?_))
  exact (congrArg (r.stalkMap y).hom (gs_unit s _ _ m₂ _).symm).trans
    ((gs_stalkMap r s y _ m₂ _).trans (gs_unit (r ≫ s) y _ m₂ _))

theorem gs_spMap {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (y : Sp B) (a : A) :
    gs (spMap φ) y ⊤ (toΓ A a) = gs (𝟙 (Sp B)) y ⊤ (toΓ B (φ a)) := by
  have e : (spMap φ).appTop.hom (toΓ A a) = toΓ B (φ a) :=
    (congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm
  rw [← e]
  exact ((gs_pull (𝟙 _) (spMap φ) y ⊤ trivial _).trans (by rw [Category.id_comp])).symm

end General

theorem psJet_boxSer {F : Type} [CommRing F] {n d : ℕ} (m : ℕ) (f : Fin n → PS F 1 d) :
    psJet m (boxSer f) = ∏ i, jetCopy (S := F) d m i (psJet m (f i)) := by
  have hp : ∀ (S : Finset (Fin n)) (g : Fin n → PS F n d), psJet m (∏ i ∈ S, g i) = ∏ i ∈ S, psJet m (g i) := by
    intro S g
    induction S using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.prod_empty, FBIdJet.psJet_one]
    | insert a S ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, FBIdJet.psJet_mul, ih]
  rw [boxSer, hp]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [MvPowerSeries.rename_eq_subst, FBIdJet.psJet_subst m _ (fun p => by simp)]
  refine DFunLike.congr_fun (GermD.jet_hom_ext fun p => ?_) _
  rw [jetCopy, GermD.jetMap_mk, GermD.jetMap_mk, MvPolynomial.aeval_X, MvPolynomial.aeval_X, Function.comp_apply,
    ← MvPolynomial.coe_X, FBIdJet.psTrunc_eq, FBIdJet.mk_trunc_coe]

theorem exists_lift {V : Type} [CommRing V] [IsDomain V] (G : Over (Sp V)) (F : Type) [Field F]
    [Algebra (FractionRing V) F] {Y : Scheme.{0}} (a : Y ⟶ (TFK (R := V) F).left) (b : Y ⟶ G.left)
    (h : b ≫ G.hom = a ≫ (TFK (R := V) F).hom ≫ jK V) :
    ∃ z : Y ⟶ (UnifPre.GF (R := V) (G := G) F).left,
      z ≫ (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left = a ∧
      z ≫ UnifPre.gFK (R := V) (G := G) F = b := by
  let T : Over (TK V).left := Over.mk (a ≫ (TFK (R := V) F).hom)
  let u : T ⟶ TFK (R := V) F := Over.homMk a rfl
  let w : T ⟶ (Over.pullback (jK V)).obj G :=
    Over.homMk (pullback.lift b (a ≫ (TFK (R := V) F).hom) (by rw [h, Category.assoc])) (pullback.lift_snd _ _ _)
  refine ⟨(lift u w).left, congrArg (fun q => q.left) (lift_fst u w), ?_⟩
  have e : (lift u w).left ≫ (snd (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left = w.left :=
    congrArg (fun q => q.left) (lift_snd u w)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans (pullback.lift_fst _ _ _))

end GlobalTheory.PowGerm.BoxGerm

namespace GlobalTheory.PowGerm
open GlobalTheory.BoxFamily FrameN BoxGerm

set_option maxHeartbeats 1000000 in

theorem boxGermSt_holds : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → BoxGermSt := by
  intro h₁ h₂ h₄ hT E _ _ _ H V _ _ _ _ t P d FT act ph1 ph2 sy ad tg xT eT wPT hch hfr hpr τ₁ g₁ el n D' A' G' _ _
    pD pA pG U' PU F _ _ _ _ q hq σ s f σ' S hσ hS hE' m
  have hM : P.U.LG.L.IsLB := P.U.LG.isLB
  have hM' : U'.LG.L.IsLB := U'.LG.isLB
  obtain ⟨τ, hτ, hv₀⟩ := exists_boxPull_gen (pr := fun i => (pG.pr i).left) PU.wL PU.wL_gen hM hM' (K := Fin 1)
      (φ' := fun _ => (zV pG xT m).left) (φ := fun _ _ => (xT m).left) (ε := fun _ => 1) (cpy V n d m)
      (fun i _ => zV_pr pG xT m i) (fun _ => τ₁ m) (fun _ => g₁ m)
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp (Jet V (Fin n × Fin d) m)) (y : Z) (J J'), Good P.U.LG.L y J →
      Good U'.LG.L y J' →
      om PU.wL y J J' (r ≫ (zV pG xT m).left) * val τ r y J' = ∏ i, val (τ₁ m) (r ≫ cpy V n d m i) y J := by
    intro Z r y J J' hJ hJ'
    have := hv₀ Z r y J J' hJ hJ'
    rwa [Fin.prod_univ_one, zpow_one] at this
  obtain ⟨z, h₀, hzg⟩ := exists_lift G' F (spMap (algebraMap F (Jet F (Fin n × Fin d) m)))
    (spMap (jetCoef (algebraMap V F) (Fin n × Fin d) m) ≫ (zV pG xT m).left) (by
      rw [Category.assoc _ (zV pG xT m).left, Over.w (zV pG xT m)]
      symm
      show spMap _ ≫ spMap (algebraMap (FractionRing V) F) ≫ spMap (algebraMap V (FractionRing V)) =
        spMap _ ≫ spMap (algebraMap V (Jet V (Fin n × Fin d) m)) ≫ 𝟙 _
      simp only [spMap, Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [JetTr.jetCoef_alg, ← IsScalarTower.algebraMap_eq])
  have hp : ∀ i, z ≫ UnifPre.gFK (R := V) (G := G') F ≫ (pG.pr i).left = jptN xT F n m i := fun i => by
    rw [← Category.assoc, hzg, Category.assoc, zV_pr, ← Category.assoc, coef_cpy, jptN]
  choose zi hz₀ hz₁ hz₂ using fun i => (hσ i).2 m
  have hc : ∀ i, cpy F n d m i ≫ spMap (jetCoef (algebraMap V F) (Fin 1 × Fin d) m) = jcN V F d n m i := fun i => by
    rw [jcN]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have main := GlobalTheory.BoxSectionValues.main h₁ h₂ h₄ hT V n P.D D' P.A A' t.G G' pD pA pG U' P.U PU F q hq σ s σ' S
    (fun i => (hσ i).1) hS hE' _ z (fun i => cpy F n d m i ≫ zi i)
    (fun i => by rw [hp, Category.assoc, hz₁, ← Category.assoc, hc, jptN])
    (fun i => by
      rw [h₀, Category.assoc, hz₀]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [AlgHom.comp_algebraMap])
  have core := core_iff (pr := fun i => (pG.pr i).left) hM hM' PU.wL PU.wL_gen (τ₁ m) (g₁ m) (cpy V n d m)
      (zV_pr pG xT m) τ hτ hv (spMap (jetCoef (algebraMap V F) (Fin n × Fin d) m))
      (UnifPre.gFK (R := V) (G := G') F) z hzg q
      (genCast (congrArg RigLB.L P.bundle).symm _ _ (GeneratorPullback.finProdGen t.PP.L (J := Fin n) _ _ fun i =>
        LB.pullGen t.PP.L _ _ (genPowG t _ _ (eLG t (𝟙 (Sp V)) d xT act eT wPT m) q) (jcN V F d n m i)))
      (fun y J hJ => (val_cast_prod t _ _ _ _ _ q _ y J hJ).trans (Finset.prod_congr rfl fun i _ => by
        rw [coef_cpy]
        have := val_along hM _ _ _ _ (el m) (jcN V F d n m i) y J hJ
        rw [Category.comp_id] at this
        exact congrArg (· ^ q) this.symm)) σ' (toΓ _ (psJet m (boxSer f)))
  obtain ⟨a, b, k₂, k₃, k₄⟩ := core.2 fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good_at hM y
    have e₁ : (om PU.wL y J J' (z ≫ UnifPre.gFK (R := V) (G := G') F) ^ q).val * sval σ' z y J' =
        ∏ i, sval (σ i) (cpy F n d m i ≫ zi i) y J := main y J J' hJ hJ'
    have e₂ : ∀ i, sval (σ i) (cpy F n d m i ≫ zi i) y J =
        gs (𝟙 _) y ⊤ (toΓ _ (jetCopy (S := F) d m i (psJet m (f i)))) *
          (val (τ₁ m) (spMap (jetCoef (algebraMap V F) (Fin n × Fin d) m) ≫ cpy V n d m i) y J ^ q).val := fun i => by
      rw [sval_along hM _ (zi i) _ _ (hz₁ i) q (σ i) (τ₁ m) _ (hz₂ i) (cpy F n d m i) y J hJ, hc, coef_cpy, gs_spMap]
      rfl
    have e₃ := hv _ (spMap (jetCoef (algebraMap V F) (Fin n × Fin d) m)) y J J' hJ hJ'
    rw [← hzg] at e₃
    rw [Finset.prod_congr rfl fun i _ => e₂ i, Finset.prod_mul_distrib, ← Units.coe_prod, Finset.prod_pow, ← e₃,
      mul_pow, Units.val_mul, mul_left_comm, ← gs_prod _ y ⊤ trivial, ← map_prod, ← psJet_boxSer] at e₁
    exact (Units.mul_right_inj _).1 e₁
  exact ⟨z, a, b, h₀, hp, k₂, (corr_genCast _ _ _).2 k₃, k₄⟩

end GlobalTheory.PowGerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GermExistsUniqueLinearBis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_existsUnique_linear : AGermSt := by
  first | exact @GlobalTheory.GermBasic.main | exact GlobalTheory.GermBasic.main | (intros; apply GlobalTheory.GermBasic.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ListProdHatLettersMemNormalFormProductSpanStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.list_prod_hatLetters_mem_normalFormProductSpan : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ (T : Set A) (a : ℕ), (∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1) → ∀ H : List A, (∀ h ∈ H, h ∈ hats d.L) → H.prod ∈ nfSpan d T 0 (a * H.length) H.length := by
  first | exact @GlobalTheory.HatNF.hats_prod_mem_nfSpan | exact GlobalTheory.HatNF.hats_prod_mem_nfSpan | (intros; apply GlobalTheory.HatNF.hats_prod_mem_nfSpan <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemSpanBoxFamilyPowerDegDataStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_boxFamily_powerDegData : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ S : Fam D'.toPre F k, S ∈ Submodule.span F {S' | ∃ s : Fin j → Fam D.toPre F k, IsBoxFam pD F k S' s} := by
  first | exact @GlobalTheory.mem_span_boxFam | exact GlobalTheory.mem_span_boxFam | (intros; apply GlobalTheory.mem_span_boxFam <;> assumption)
end

