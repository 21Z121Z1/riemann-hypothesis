import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralMulOfSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0061
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0065

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselStepPositionOneFinite
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.PosOne.quotInt_one_comb : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ') (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (e : GL (n' ⊕ Fin (c + 1)) k →₀ ℂ) (_ : SrcComb ψ ν P ρ' Φ e) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ P σ B) (F : A) (z : GL (n' ⊕ Fin (c + 1)) k → ℂ), (∀ g ∈ e.support, IsQuotInt ν μX μG P (tInt ψ ν μ P σ B F (om μ g 1 Φ.1)) (z g)) → IsQuotInt ν μX μG 1 (tIntOne ψ ν μ P σ B F Φ.1) (comb e z) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c P hP hPc ψ hψ hψ1 ν hν μ hμ μX _ μG _ ρ' hρ' Φ e he A _ _ σ hσ B hB F z hz
  haveI : ν.IsAddHaarMeasure := hν.1
  obtain ⟨Rr, hRr, hRrN⟩ := GlobalTheory.T.exists_linear_isQuotInt_tInt_alt k n n' c P hP hPc ψ hψ hψ1 ν μ hμ μX μG A σ hσ B hB F ρ' hρ'
  have hone := GlobalTheory.T.isQuotientInvariantIntegral_exchange_toPositionOne k n n' c P hP hPc ψ hψ hψ1 ν hν μ hμ μX μG A σ hσ B hB F ρ' hρ' Rr hRr Φ
  have hcomb : toOne ν ρ' P Rr Φ = comb e fun g => Rr (ρ' g Φ) := he Rr hRrN
  have heq : comb e z = comb e fun g => Rr (ρ' g Φ) := by
    unfold comb
    refine Finsupp.sum_congr fun g hg => ?_
    congr 1
    have h1 := hRr (ρ' g Φ)
    rw [hρ' g Φ] at h1
    exact ((GlobalTheory.QuotInt.quotInt_unique_exists k n c P hP hPc ν μX μG _).1 _ _ (hz g hg) h1)
  rw [heq, ← hcomb]
  exact hone
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExchangeToPositionOneUniformInLevelStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exchangeToPositionOne_uniform_in_level : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (U : Subgroup (GL (n ⊕ Fin c) k)) (_ : IsOpen (U : Set (GL (n ⊕ Fin c) k))), ∃ e e' : GL (n ⊕ Fin c) k →₀ ℂ, ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), IsNEquiv ψ P σ l → (∀ u ∈ U, σ u v = v) → toOne ν σ P l v = comb e (fun g => l (σ g v)) ∧ l v = comb e' fun g => toOne ν σ P l (σ g v) := by
  first | exact @GlobalTheory.PosOne.toOne_uniform | exact GlobalTheory.PosOne.toOne_uniform | (intros; apply GlobalTheory.PosOne.toOne_uniform <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBilinearPositionMiddleVertex
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

noncomputable section
namespace GlobalTheory.PosOne.MidVertex

theorem exists_bilPos_mid : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ) (_ : c + 1 = 2 * ρ) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ₁ μ₂ : kˣ →* ℂˣ) (_ : IsOpen (μ₁.ker : Set kˣ)) (_ : IsOpen (μ₂.ker : Set kˣ)) (m₁ : Measure (GL n₁ k)) [m₁.IsHaarMeasure] (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) [G₁.IsHaarMeasure] (m₂ : Measure (GL n₂ k)) [m₂.IsHaarMeasure] (G₂ : Measure (GL (n₂ ⊕ Fin c) k)) [G₂.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : TriPos ψ μ₁ μ₂ ρ σ T) (F : A) (ρ₁ : Representation ℂ (GL (n₁ ⊕ Fin (c + 1)) k) (SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k))) (_ : IsSrc μ₂ ρ₁), ∃ b : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ, BilPos ψ μ₁ ρ ρ₁ b ∧ (∀ Ψ (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)), IsQuotInt ν m₂ G₂ ρ (tInt ψ ν μ₂ ρ σ (T Ψ) F Φ₂.1) (b Ψ Φ₂)) ∧ ∀ Ψ (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)), IsQuotInt ν m₂ G₂ 1 (tIntOne ψ ν μ₂ ρ σ (T Ψ) F Φ₂.1) (toOne ν ρ₁ ρ (b Ψ) Φ₂) := by
  intro k _ _ _ _ _ _ n₀ n₁ n₂ _ _ _ _ _ _ c ρ hc ψ hψc hψ1 ν hsd μ₁ μ₂ hk₁ hk₂ m₁ _ G₁ _ m₂ _ G₂ _ A _ _ σ hσ T hT F ρ₁ hsrc
  haveI : ν.IsAddHaarMeasure := hsd.1
  have h1 : 1 ≤ ρ := by omega
  have h2 : ρ ≤ c := by omega
  have hR := fun Ψ => GlobalTheory.T.exists_linear_isQuotInt_tInt_alt k n₂ n₁ c ρ h1 h2 ψ hψc hψ1 ν μ₂ hk₂ m₂ G₂ A σ hσ (T Ψ) (hT.1 Ψ) F ρ₁ hsrc
  choose R hQ hN using hR
  have uniq : ∀ (f : GL (n₂ ⊕ Fin c) k → ℂ) (z z' : ℂ), IsQuotInt ν m₂ G₂ ρ f z → IsQuotInt ν m₂ G₂ ρ f z' → z = z' :=
    fun f z z' => (GlobalTheory.QuotInt.quotInt_unique_exists k n₂ c ρ h1 h2 ν m₂ G₂ f).1 z z'
  have lin := fun f f' a z z' => GlobalTheory.RootEx.QuotLinear.isQuotInt_linear k n₂ c ρ h1 h2 ν m₂ G₂ f f' a z z'
  have key : ∀ (a : ℂ) Ψ Ψ' Φ, R (a • Ψ + Ψ') Φ = a * R Ψ Φ + R Ψ' Φ := by
    intro a Ψ Ψ' Φ
    have h := lin _ _ a _ _ (hQ Ψ Φ) (hQ Ψ' Φ)
    have hf : (fun h => a * tInt ψ ν μ₂ ρ σ (T Ψ) F Φ.1 h + tInt ψ ν μ₂ ρ σ (T Ψ') F Φ.1 h) =
        tInt ψ ν μ₂ ρ σ (T (a • Ψ + Ψ')) F Φ.1 := by
      funext h
      simp only [tInt, app, map_add, map_smul]
      split_ifs <;> simp
    rw [hf] at h
    exact uniq _ _ _ (hQ _ Φ) h
  have hz : ∀ Φ, R 0 Φ = 0 := by
    intro Φ
    have := key 1 0 0 Φ
    simp only [one_smul, add_zero, one_mul] at this
    linear_combination -this
  let b : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ :=
    { toFun := R
      map_add' := fun Ψ Ψ' => by
        ext Φ
        have := key 1 Ψ Ψ' Φ
        simpa using this
      map_smul' := fun a Ψ => by
        ext Φ
        have := key a Ψ 0 Φ
        simp only [add_zero] at this
        simp [this, hz] }
  refine ⟨b, ⟨fun Ψ => hN Ψ, ?_⟩, fun Ψ Φ₂ => hQ Ψ Φ₂, fun Ψ Φ₂ =>
    GlobalTheory.T.isQuotientInvariantIntegral_exchange_toPositionOne k n₂ n₁ c ρ h1 h2 ψ hψc hψ1 ν hsd μ₂ hk₂ m₂ G₂ A σ hσ (T Ψ) (hT.1 Ψ) F ρ₁ hsrc (R Ψ) (hQ Ψ) Φ₂⟩
  intro g Ψ Ψ₁ v hΨ
  show R Ψ₁ (ρ₁ (embX (c + 1) g) v) = _ * R Ψ v
  set s : ℂ := ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 2) / 2 - ρ) : ℝ) : ℂ) with hs
  have hexp : ((((c + 1 : ℕ) : ℝ) + 1) / 2 - (ρ : ℝ)) = ((c : ℝ) + 2) / 2 - ρ := by push_cast; ring
  rw [hexp]
  have hfun : tInt ψ ν μ₂ ρ σ (T Ψ₁) F (ρ₁ (embX (c + 1) g) v).1 =
      fun h => (s - 1) * tInt ψ ν μ₂ ρ σ (T Ψ) F v.1 h + tInt ψ ν μ₂ ρ σ (T Ψ) F v.1 h := by
    funext h
    have hv : ((ρ₁ (embX (c + 1) g) v : SB _) : Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k → ℂ) =
        om μ₂ (embX (c + 1) g) 1 v.1 := hsrc _ _
    have hcomm : om μ₂ 1 h (om μ₂ (embX (c + 1) g) 1 v.1) = om μ₂ (embX (c + 1) g) 1 (om μ₂ 1 h v.1) := by
      rw [← om_mul, ← om_mul, one_mul, mul_one, mul_one, one_mul]
    have hΦ' : om μ₂ 1 h v.1 ∈ SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k) := om_mem_SB μ₂ 1 h v.2
    have hX := (GlobalTheory.RootEx.opE_SB_and_linear k n₂ n₁ c ρ ψ hψc ν).1 _ hΦ'
    have hE' := (GlobalTheory.RootEx.opE_om_embX k n₂ n₁ c ρ h1 h2 ψ ν μ₂ (om μ₂ 1 h v.1)).2 g
    have hX' : om μ₂ g 1 (opE ψ ν ρ (om μ₂ 1 h v.1)) ∈ SB (Matrix n₂ n₁ k) := om_mem_SB μ₂ g 1 hX
    have hinv := hT.2 g Ψ Ψ₁ ⟨_, hX⟩ ⟨_, hX'⟩ hΨ rfl
    simp only [tInt]
    rw [hv, hcomm, hE']
    have e1 : ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 2) / 2 - ρ) : ℝ) : ℂ) •
        om μ₂ g 1 (opE ψ ν ρ (om μ₂ 1 h v.1)) = ((s • (⟨_, hX'⟩ : SB (Matrix n₂ n₁ k)) : SB _) : Matrix n₂ n₁ k → ℂ) := by
      rfl
    have e2 : app (T Ψ) (opE ψ ν ρ (om μ₂ 1 h v.1)) = T Ψ ⟨_, hX⟩ := GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe _ ⟨_, hX⟩
    rw [e1, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe, e2, map_smul, hinv]
    simp only [LinearMap.smul_apply, smul_eq_mul]
    ring
  have h := lin _ _ (s - 1) _ _ (hQ Ψ v) (hQ Ψ v)
  rw [← hfun] at h
  rw [uniq _ _ _ (hQ Ψ₁ _) h]
  ring

end GlobalTheory.PosOne.MidVertex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiTargetBilinearFormIntegral
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
open Filter Topology

noncomputable section
namespace GlobalTheory.PosOne.FJTarget
open GlobalTheory.RootEx.Unfolding (omR omR_val omR_mul omR_smooth orbit_locallyConstant opL)

theorem exists_isQuotInt_tInt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] {c p : ℕ} (hp : 1 ≤ p) (hpc : p ≤ c) {ψ : AddChar k Circle} (hψ : Continuous ψ)
    (hψ1 : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (hμ : IsOpen (μ.ker : Set kˣ))
    (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure]
    {A : Type} [AddCommGroup A] [Module ℂ A] {σ : Representation ℂ (GL (n ⊕ Fin c) k) A} (hσ : IsSmoothRep σ)
    {B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ} (hB : BilPos ψ μ p σ B) (F : A)
    (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    ∃ z, IsQuotInt ν μX μG p (tInt ψ ν μ p σ B F Φ.1) z := by
  have hE := (opE_SB_and_linear k n n' c p ψ hψ ν).1
  let E : GL (n ⊕ Fin c) k → SB (Matrix n n' k) := fun h =>
    ⟨opE ψ ν p (om μ 1 h Φ.1), hE _ (om_mem_SB μ 1 h Φ.2)⟩
  have hfE : ∀ h, tInt ψ ν μ p σ B F Φ.1 h = B (E h) (σ h F) := fun h => by
    unfold tInt
    rw [show opE ψ ν p (om μ 1 h Φ.1) = ((E h : SB (Matrix n n' k)) : Matrix n n' k → ℂ) from rfl,
      GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe]
  have hmul : ∀ (g h : GL (n ⊕ Fin c) k) (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ),
      om μ 1 (g * h) Ψ = om μ 1 g (om μ 1 h Ψ) := fun g h Ψ => by
    rw [← om_mul, one_mul]
  refine (GlobalTheory.QuotInt.quotInt_unique_exists k n c p hp hpc ν μX μG _).2 ?_ ?_ ?_
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro h
    have hU : IsOpen ({u : GL (n ⊕ Fin c) k | om μ 1 u Φ.1 = Φ.1} ∩ {u | σ u F = F}) :=
      ((isOpen_stabilizer_om hμ Φ.2).preimage (Continuous.prodMk_right 1)).inter (hσ F)
    have ht : Filter.Tendsto (fun y : GL (n ⊕ Fin c) k => h⁻¹ * y) (𝓝 h) (𝓝 1) := by
      simpa using (continuous_const_mul h⁻¹).tendsto h
    filter_upwards [ht.eventually (hU.mem_nhds ⟨om_one μ _, by simp⟩)] with y hy
    obtain ⟨u, rfl⟩ : ∃ u, y = h * u := ⟨h⁻¹ * y, by simp⟩
    rw [inv_mul_cancel_left] at hy
    have h1 : om μ 1 u Φ.1 = Φ.1 := hy.1
    have h2 : σ u F = F := hy.2
    unfold tInt
    rw [hmul, h1, map_mul, Module.End.mul_apply, h2]
  · obtain ⟨Λ, hΛ, hΛ'⟩ := GlobalTheory.RootEx.sb_matrix_exists_isOpen_addSubgroup k _ _ Φ.1 Φ.2
    obtain ⟨Ω, hΩ, H⟩ := opE_support_compact_mod_R k n n' c p hp hpc ψ hψ hψ1 ν (tsupport Φ.1)
      Φ.2.2 Λ hΛ
    refine ⟨Ω, hΩ, fun h hh => ?_⟩
    have hne : E h ≠ 0 := fun h0 => hh (by rw [hfE, h0]; simp)
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, opE ψ ν p (om μ 1 h Φ.1) x₀ ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hne (Subtype.ext (funext hc))
    exact H μ Φ.1 (subset_tsupport _) hΛ' (fun _ => 1) (IsLocallyConstant.const 1) h x₀
      (by simpa using hx₀)
  · intro x u hu h
    set a : ℂ := ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) with ha
    let Ψ : SB (Matrix n n' k) := ⟨om μ 1 x (E h).1, om_mem_SB μ 1 x (E h).2⟩
    have h1 : E (embX c x * u * h) = (a * (ψ (-simpleSum u) : ℂ)) • Ψ := by
      apply Subtype.ext
      show opE ψ ν p (om μ 1 (embX c x * u * h) Φ.1) =
        (a * (ψ (-simpleSum u) : ℂ)) • om μ 1 x (opE ψ ν p (om μ 1 h Φ.1))
      rw [mul_assoc, hmul, (opE_om_embX k n n' c p hp hpc ψ ν μ _).1, hmul,
        opE_om_target_unipotent k n n' c p hp hpc ψ ν μ _ u hu]
      funext y
      simp only [om, Pi.smul_apply, smul_eq_mul, ha]
      ring
    have h3 : (ψ (-simpleSum u) : ℂ) * (ψ (simpleSum u) : ℂ) = 1 := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]; simp
    have h4 : a * a =
        ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) : ℂ) := by
      rw [ha, ← Complex.ofReal_mul, ← Real.rpow_add (nabs_pos _ _)]
      congr 2
      ring
    have h5 := hB.1 (E h) u hu (σ h F)
    have h6 := hB.2 x (E h) Ψ (σ u (σ h F)) rfl
    rw [hfE, hfE, h1, map_smul, LinearMap.smul_apply, map_mul, map_mul, Module.End.mul_apply,
      Module.End.mul_apply, h6, h5, ← h4, ← ha, smul_eq_mul]
    linear_combination (a * a * B (E h) (σ h F)) * h3

theorem target_bilinear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : c = 2 * ρ) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (fj : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : Represents ψ ν ρ σ fj B) (_ : BilPos ψ μ (ρ + 1) σ B) (F : A) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (z : ℂ), IsQuotInt ν μX μG (ρ + 1) (tInt ψ ν μ (ρ + 1) σ B F Φ.1) z ↔ FJInt ψ ν μX μG μ ρ (fun h Ψ Φ₀ => fj Ψ (σ h F) Φ₀) Φ.1 z := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c ρ h1 hc ψ hψ hψ1 ν hν μ hμ μX _ μG _ A _ _ σ hσ fj B hb hp F Φ z
  have h2 : ρ < c := by omega
  have := hν.1
  have := secondCountable k
  have := t2Space k
  have e : ∀ h β, app B (fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) (σ (colE c (ρ + 1) β) (σ h F)) =
      tInt ψ ν μ (ρ + 1) σ B F Φ.1 (colE c (ρ + 1) β * h) := by
    intro h β
    have := om_mul μ 1 1 (colE c (ρ + 1) β) h Φ.1
    rw [one_mul] at this
    unfold tInt
    rw [this, map_mul]
    rfl
  obtain ⟨z₀, hz₀⟩ := exists_isQuotInt_tInt (p := ρ + 1) (by omega) (by omega) hψ hψ1 ν μ hμ μX μG hσ hp F Φ
  have W := GlobalTheory.T.weil_formula_rootExchange_parabolic_quotient k n c ρ h1 h2 ν μX μG (tInt ψ ν μ (ρ + 1) σ B F Φ.1)
  have val : ∀ h w, HasTensorVal (fun Ψ Φ₀ => fj Ψ (σ h F) Φ₀) (fl ψ ν μ ρ (om μ 1 h Φ.1)) w ↔
      w = ∫ β : n → k, app B (fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) (σ (colE c (ρ + 1) β) (σ h F))
        ∂(Measure.pi fun _ => ν) := by
    intro h
    have v1 : ∀ w, HasTensorVal (fun Ψ Φ₀ => fj Ψ (σ h F) Φ₀) (fl ψ ν μ ρ (om μ 1 h Φ.1)) w →
        w = ∫ β : n → k, app B (fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) (σ (colE c (ρ + 1) β) (σ h F))
          ∂(Measure.pi fun _ => ν) := by
      rintro w ⟨m, Ψ, Φ₀, hd, rfl⟩
      simp only [(hb.2 _ _ _).2]
      rw [← integral_finset_sum _ fun i _ => (hb.2 _ _ _).1]
      congr 1; funext β
      have : (fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) = (∑ i, (Φ₀ i).1 β • Ψ i : SB (Matrix n n' k)).1 := by
        funext x₀
        simp [hd, mul_comm]
      rw [this, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe]
      simp
    let T : (n → k) → SB (Matrix n n' k) := fun β =>
      opL hψ ν (ρ + 1) (omR μ (1, colE c (ρ + 1) β) (omR μ (1, h) Φ))
    have hT : IsLocallyConstant T :=
      ((orbit_locallyConstant (omR_smooth hμ) (omR μ (1, h) Φ)).comp_continuous
        (continuous_const.prodMk ExchangeSupport.continuous_colE)).comp fun Ψ => opL hψ ν (ρ + 1) Ψ
    obtain ⟨K, hK, HK⟩ := ColumnSupport.opE_colE_eq_zero k n n' c ρ h2 ψ ν μ _ (omR μ (1, h) Φ).2
    obtain ⟨m, Ψ, Φ₀, hd⟩ := GlobalTheory.T.exists_sum_smul_of_locallyConstant_compactSupport (n → k) _ T hT K hK fun β hβ => Subtype.ext (by
      have := HK β hβ fun _ => 1
      simp only [one_mul] at this
      exact this)
    have v2 : HasTensorVal (fun Ψ Φ₀ => fj Ψ (σ h F) Φ₀) (fl ψ ν μ ρ (om μ 1 h Φ.1)) _ :=
      ⟨m, Ψ, Φ₀, fun x y => by
        have := congrArg (fun t : SB (Matrix n n' k) => t.1 x) (hd y)
        refine Eq.trans this ?_
        simp [mul_comm], rfl⟩
    exact fun w => ⟨v1 w, fun hw => by rw [hw, ← v1 _ v2]; exact v2⟩
  have i1 : IsQuotInt ν μX μG (ρ + 1) (tInt ψ ν μ (ρ + 1) σ B F Φ.1) z ↔
        IsQuotIntFJ ν μX μG ρ (fun h => ∫ β : n → k,
          app B (fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) (σ (colE c (ρ + 1) β) (σ h F))
            ∂(Measure.pi fun _ => ν)) z := by
    simp only [e]
    exact ⟨fun hz => (W z hz).2, fun hz => GlobalTheory.T.eq_of_isQuotIntFJ_of_isQuotIntFJ k n c ρ h1 h2 ν μX μG _ _ _ (W z₀ hz₀).2 hz ▸ hz₀⟩
  refine i1.trans ⟨fun hz => ⟨_, fun h => (val h _).2 rfl, hz⟩, ?_⟩
  rintro ⟨f, hf, hz⟩
  rwa [show f = _ from funext fun h => (val h _).1 (hf h)] at hz

end GlobalTheory.PosOne.FJTarget
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelReductionExtendEvaluatedIntegrated
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory.FlatFactor.KerRedStep

theorem mul_sum_law : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (S : Finset (m × m')), (∀ e ∈ S, ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) → ∀ (b : m × m' → k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (∑ e ∈ S, b e * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν m m' _ _ _ _ M _ _ l β S hS b
  have hlc := GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar ψ hψc
  induction S using Finset.induction_on with
  | empty =>
    intro Θ Θ' h
    congr 1
    exact Subtype.ext (funext fun t => by simp [h])
  | insert j S hj ih =>
    intro Θ Θ' h
    have hc : Continuous fun t : Matrix m m' k => ∑ e ∈ S, b e * (t e.1 e.2 - β e.1 e.2) :=
      continuous_finset_sum _ fun e _ => continuous_const.mul
        ((continuous_id.matrix_elem _ _).sub continuous_const)
    let Θm : SB (Matrix m m' k) := ⟨fun t => (ψ (∑ e ∈ S, b e * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t,
      (hlc.comp_continuous hc).mul Θ.2.1, Θ.2.2.mul_left⟩
    have h1 : l Θ' = l Θm := hS j (Finset.mem_insert_self j S) (b j) Θm Θ' fun t => by
      rw [h t, Finset.sum_insert hj, AddChar.map_add_eq_mul, Circle.coe_mul, mul_assoc]
    rw [h1]
    exact ih (fun e he => hS e (Finset.mem_insert_of_mem he)) Θ Θm fun t => rfl

theorem trans_sum_law : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (S : Finset (m × m')), (∀ e ∈ S, ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) → ∀ (a : m × m' → k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + ∑ e ∈ S, Matrix.single e.1 e.2 (a e))) → l Θ' = l Θ := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν m m' _ _ _ _ M _ _ l β S hS a
  induction S using Finset.induction_on with
  | empty =>
    intro Θ Θ' h
    congr 1
    exact Subtype.ext (funext fun t => by simp [h])
  | insert j S hj ih =>
    intro Θ Θ' h
    let c : Matrix m m' k := ∑ e ∈ S, Matrix.single e.1 e.2 (a e)
    let Θm : SB (Matrix m m' k) := ⟨fun t => Θ.1 (t + c),
      Θ.2.1.comp_continuous (continuous_id.add continuous_const),
      Θ.2.2.comp_homeomorph (Homeomorph.addRight c)⟩
    have h1 : l Θ' = l Θm := hS j (Finset.mem_insert_self j S) (a j) Θm Θ' fun t => by
      rw [h t, Finset.sum_insert hj, ← add_assoc]
    rw [h1]
    exact ih (fun e he => hS e (Finset.mem_insert_of_mem he)) Θ Θm fun t => rfl

theorem kerRed_extend : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (m m' : Type) [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (M : Type) [AddCommGroup M] [Module ℂ M] (l : SB (Matrix m m' k) →ₗ[ℂ] M) (β : Matrix m m' k) (ev it ev' it' : Finset (m × m')), ev ⊆ ev' → it ⊆ it' → Disjoint ev' it' → GlobalTheory.FlatFactor.KerRed ν ev it β l → (∀ e ∈ ev', e ∉ ev → ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) → (∀ e ∈ it', e ∉ it → ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) → GlobalTheory.FlatFactor.KerRed ν ev' it' β l := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν m m' _ _ _ _ M _ _ l β ev it ev' it' hev hit hd hK hmul htr
  have hd0 : Disjoint ev it := Finset.disjoint_of_subset_left hev (Finset.disjoint_of_subset_right hit hd)
  have L1 : (∀ e ∈ ev, ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) := by
    intro e he b Θ Θ' h
    have he' : e ∉ it := Finset.disjoint_left.mp hd0 he
    have h0 : l (Θ' - Θ) = 0 := hK _ fun t => by
      unfold GlobalTheory.FlatFactor.red
      have hz : ∀ a, (Θ' - Θ).1 (GlobalTheory.FlatFactor.fill ev it β t a) = 0 := by
        intro a
        have hf : GlobalTheory.FlatFactor.fill ev it β t a e.1 e.2 = β e.1 e.2 := by
          simp [GlobalTheory.FlatFactor.fill, he, he']
        simp [h, hf]
      simp [hz]
    rwa [map_sub, sub_eq_zero] at h0
  have hM : (∀ e ∈ ev', ∀ (b : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = (ψ (b * (t e.1 e.2 - β e.1 e.2)) : ℂ) * Θ.1 t) → l Θ' = l Θ) := by
    intro e he
    by_cases h : e ∈ ev
    · exact L1 e h
    · exact hmul e he h
  have hT : (∀ e ∈ it', ∀ (a : k) (Θ Θ' : SB (Matrix m m' k)), (∀ t, Θ'.1 t = Θ.1 (t + Matrix.single e.1 e.2 a)) → l Θ' = l Θ) := by
    intro e he
    by_cases h : e ∈ it
    · exact GlobalTheory.T.linearMap_killing_partialEvalIntegralKernel_translation_invariant k ψ ν hψc hψ1 hν m m' M l β ev it hd0 hK e h
    · exact htr e he h
  exact GlobalTheory.T.linearMap_kills_partialEvalIntegralKernel_of_laws k ψ ν hψc hψ1 hν m m' M l β ev' it' hd
    (mul_sum_law k ψ ν hψc hψ1 hν m m' M l β ev' hM) (trans_sum_law k ψ ν hψc hψ1 hν m m' M l β it' hT)

end GlobalTheory.FlatFactor.KerRedStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatSelfAverageHeisenberg
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
open Filter Topology
open GlobalTheory.RootEx.Unfolding (omR omR_val omR_mul omR_smooth orbit_locallyConstant opL ev)

noncomputable section
namespace GlobalTheory.PosOne

theorem avg_self_and_props : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∃ Φ₀ : SB (n' → k), GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ p Φ₀.1 Φ.1 = Φ.1) ∧ ∀ Φ₀ : SB (n' → k), GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ p Φ₀.1 Φ.1 ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) ∧ (∀ h, opE ψ ν p (om μ 1 h (GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ p Φ₀.1 Φ.1)) = opEFJ ψ ν p Φ₀.1 (om μ 1 h Φ.1)) ∧ ∀ (ρ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) (SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))) (_ : IsSrc μ ρ') (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ), app L (GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ p Φ₀.1 Φ.1) = ∫ u, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ₀.1 u * L (ρ' (rowE (c + 1) p u) Φ) ∂(Measure.pi fun _ => ν) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp1 hpc ψ hψ hψ1 ν hν μ hμ' Φ
  have := hν.1
  have := secondCountable k
  have := t2Space k
  have hF := GlobalTheory.T.schwartzFourierTransformPi_surjective_schwartzBruhat k n' ψ hψ hψ1 ν hν
  have main : ∀ Φ₀ : SB (n' → k),
      ∃ w : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ p Φ₀.1 Φ.1 = w.1 ∧
      (∀ h, opE ψ ν p (om μ 1 h w.1) = opEFJ ψ ν p Φ₀.1 (om μ 1 h Φ.1)) ∧
      ∀ L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ,
        L w = ∫ u, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ₀.1 u * L (omR μ (rowE (c + 1) p u, 1) Φ) ∂(Measure.pi fun _ => ν) := by
    intro Φ₀
    have hh := hF.1 Φ₀
    let T : (n' → k) → SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) := fun u =>
      GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ₀.1 u • omR μ (rowE (c + 1) p u, 1) Φ
    have hT : IsLocallyConstant T :=
      (hh.1.prodMk ((orbit_locallyConstant (omR_smooth hμ') Φ).comp_continuous
        (ExchangeSupport.continuous_rowE.prodMk continuous_const))).comp fun z => z.1 • z.2
    obtain ⟨w, hw⟩ := GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact (n' → k)
      (Measure.pi fun _ => ν) _ T hT _ hh.2 fun u hu => by
        simp only [T, image_eq_zero_of_notMem_tsupport hu, zero_smul]
    refine ⟨w, funext fun x => (hw (ev x)).symm, fun h => funext fun x₀ => ?_, fun L => ?_⟩
    · refine (hw ((ev x₀).comp ((opL hψ ν p).comp (omR μ (1, h))))).trans ?_
      rw [opEFJ]
      congr 1; funext u
      simp only [T, LinearMap.comp_apply, map_smul, smul_eq_mul]
      congr 1
      have := GlobalTheory.T.rootExchangeOperator_weil_rowUnipotent k n n' c p hp1 hpc ψ hψ ν μ (omR μ (1, h) Φ) u x₀
      rw [← omR_val, omR_mul, one_mul, mul_one] at this
      rw [omR_mul, one_mul, mul_one]
      exact this
    · rw [hw L]
      congr 1; funext u
      simp only [T, map_smul, smul_eq_mul]
  refine ⟨?_, fun Φ₀ => ?_⟩
  · have hU : {u : n' → k | omR μ (rowE (c + 1) p u, 1) Φ = Φ} ∈ 𝓝 (0 : n' → k) :=
      ((omR_smooth hμ' Φ).preimage (ExchangeSupport.continuous_rowE.prodMk continuous_const)).mem_nhds (by
        change omR μ (rowE (c + 1) p 0, 1) Φ = Φ
        rw [ExchangeSupport.rowE_zero, ← Prod.one_eq_mk, map_one, Module.End.one_apply])
    obtain ⟨g, a, a1⟩ := GlobalTheory.T.exists_schwartzBruhat_supported_nhds_integral_one k n' ν _ hU
    obtain ⟨Φ₀, h0⟩ := hF.2 g
    refine ⟨Φ₀, funext fun x => ?_⟩
    rw [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg, h0, GlobalTheory.RootEx.FourierJacobi.integral_mul_of_support (z := Φ.1 x) a, a1, one_mul]
    intro u hu
    exact congrArg (fun t : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) => t.1 x) hu
  · obtain ⟨w, e1, e2, e3⟩ := main Φ₀
    refine ⟨e1 ▸ w.2, fun h => e1 ▸ e2 h, fun ρ' hρ' L => ?_⟩
    rw [e1, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe, e3 L]
    congr 1; funext u
    congr 2
    exact Subtype.ext ((hρ' _ Φ).trans (omR_val μ _ 1 Φ).symm).symm

end GlobalTheory.PosOne
end
end

