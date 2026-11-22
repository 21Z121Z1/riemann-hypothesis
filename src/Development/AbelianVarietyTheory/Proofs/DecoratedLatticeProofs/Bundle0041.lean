import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0040
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0044
import Formalism.TorsionNormIteration.InverseIntegralClasses.SigmaNormLeOne
import Formalism.GaussJetBounds.GaussJetProofs.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormSubLeMaxOfUltrametricField
section
noncomputable section

namespace GlobalTheory.Honda.TwistedDivision

variable {K : Type} [NormedField K]

theorem norm_sub_le_max_of_ultrametric_field [IsUltrametricDist K] (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max x (-y)).trans_eq (by rw [norm_neg])

theorem norm_pow_apply (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (i : ℕ) (x : K) :
    ‖(τ ^ i) x‖ = ‖x‖ := by
  induction i generalizing x with
  | zero => simp
  | succ i ih => rw [pow_succ, RingHom.mul_def, RingHom.comp_apply, ih, hτ]

noncomputable def step (τ : K →+* K) (π : K) (c : ℕ → K) (t : ℕ → K) : ℕ → K
  | 0 => 1
  | m + 1 => (π * t (m + 2) - ∑ i : Fin (m + 1), step τ π c t i * (τ ^ (i : ℕ)) (c (m + 1 - i))) /
      (τ ^ (m + 1)) (c 0)
termination_by m => m
decreasing_by exact i.isLt

theorem step_zero (τ : K →+* K) (π : K) (c : ℕ → K) (t : ℕ → K) : step τ π c t 0 = 1 := by
  rw [step]

theorem step_succ (τ : K →+* K) (π : K) (c : ℕ → K) (t : ℕ → K) (m : ℕ) :
    step τ π c t (m + 1) = (π * t (m + 2) - ∑ i ∈ Finset.range (m + 1), step τ π c t i * (τ ^ i) (c (m + 1 - i))) /
      (τ ^ (m + 1)) (c 0) := by
  rw [step, Fin.sum_univ_eq_sum_range (fun i => step τ π c t i * (τ ^ i) (c (m + 1 - i)))]

variable (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (π : K) (c : ℕ → K) (hc0 : ‖c 0‖ = 1) (hc : ∀ i, ‖c i‖ ≤ 1)
include hτ hc0

include hc in
theorem step_bound [IsUltrametricDist K] (hπ : ‖π‖ ≤ 1) (t : ℕ → K) (ht : ∀ j, ‖t j‖ ≤ 1) (m : ℕ) : ‖step τ π c t m‖ ≤ 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero => simp [step_zero]
    | succ m =>
      rw [step_succ, norm_div, norm_pow_apply τ hτ, hc0, div_one]
      refine (norm_sub_le_max_of_ultrametric_field _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]; exact mul_le_one₀ hπ (norm_nonneg _) (ht _)
      · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i hi => ?_
        rw [norm_mul, norm_pow_apply τ hτ]
        exact mul_le_one₀ (ih i (Finset.mem_range.1 hi)) (norm_nonneg _) (hc _)

include hc in
theorem step_diff [IsUltrametricDist K] (t t' : ℕ → K) (ε : ℝ) (hε : 0 ≤ ε) (h : ∀ j, ‖t j - t' j‖ ≤ ε) (m : ℕ) :
    ‖step τ π c t m - step τ π c t' m‖ ≤ ‖π‖ * ε := by
  have hπε : 0 ≤ ‖π‖ * ε := mul_nonneg (norm_nonneg _) hε
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero => simpa [step_zero] using hπε
    | succ m =>
      rw [step_succ, step_succ, ← sub_div, norm_div, norm_pow_apply τ hτ, hc0, div_one]
      have key : (π * t (m + 2) - ∑ i ∈ Finset.range (m + 1), step τ π c t i * (τ ^ i) (c (m + 1 - i))) -
          (π * t' (m + 2) - ∑ i ∈ Finset.range (m + 1), step τ π c t' i * (τ ^ i) (c (m + 1 - i))) =
          π * (t (m + 2) - t' (m + 2)) -
            ∑ i ∈ Finset.range (m + 1), (step τ π c t i - step τ π c t' i) * (τ ^ i) (c (m + 1 - i)) := by
        simp only [sub_mul, Finset.sum_sub_distrib]; ring
      rw [key]
      refine (norm_sub_le_max_of_ultrametric_field _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (h _) (norm_nonneg _)
      · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hπε fun i hi => ?_
        rw [norm_mul, norm_pow_apply τ hτ]
        have hi' : i < m + 1 := Finset.mem_range.1 hi
        calc ‖step τ π c t i - step τ π c t' i‖ * ‖c (m + 1 - i)‖ ≤ (‖π‖ * ε) * 1 :=
              mul_le_mul (ih i hi') (hc _) (norm_nonneg _) hπε
          _ = ‖π‖ * ε := mul_one _

theorem step_eq (t : ℕ → K) (m : ℕ) :
    π * t (m + 2) = ∑ i ∈ Finset.range (m + 2), step τ π c t i * (τ ^ i) (c (m + 2 - 1 - i)) := by
  have hu : (τ ^ (m + 1)) (c 0) ≠ 0 := by
    intro h0; have := norm_pow_apply τ hτ (m + 1) (c 0); rw [h0, norm_zero, hc0] at this; exact zero_ne_one this
  rw [Finset.sum_range_succ, step_succ]
  have h1 : m + 2 - 1 - (m + 1) = 0 := by omega
  rw [h1, div_mul_cancel₀ _ hu]
  have h2 : ∑ i ∈ Finset.range (m + 1), step τ π c t i * (τ ^ i) (c (m + 2 - 1 - i)) =
      ∑ i ∈ Finset.range (m + 1), step τ π c t i * (τ ^ i) (c (m + 1 - i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have : m + 2 - 1 - i = m + 1 - i := by omega
    rw [this]
  rw [h2]; ring

end GlobalTheory.Honda.TwistedDivision

namespace GlobalTheory.Honda

open PowerSeries Filter Topology

theorem exists_twisted_division : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (τ : K →+* K),
    (∀ x, ‖τ x‖ = ‖x‖) → ∀ π : K, ‖π‖ < 1 → ∀ c : ℕ → K, ‖c 0‖ = 1 → (∀ i, ‖c i‖ ≤ 1) →
    ∃ t : ℕ → K, t 0 = 1 ∧ (∀ n, ‖t n‖ ≤ 1) ∧
      ∀ n, 2 ≤ n → π * t n = ∑ i ∈ Finset.range n, t i * (τ ^ i) (c (n - 1 - i)) := by
  intro K _ _ _ τ hτ π hπ c hc0 hc
  let T : ℕ → ℕ → K := fun k => (TwistedDivision.step τ π c)^[k] (fun _ => 1)
  have hTs : ∀ k, T (k + 1) = TwistedDivision.step τ π c (T k) := fun k =>
    Function.iterate_succ_apply' _ _ _
  have hπ1 : ‖π‖ ≤ 1 := hπ.le
  have hB : ∀ k j, ‖T k j‖ ≤ 1 := by
    intro k
    induction k with
    | zero => intro j; simp [T]
    | succ k ih => intro j; rw [hTs]; exact TwistedDivision.step_bound τ hτ π c hc0 hc hπ1 _ ih j
  have hD : ∀ k j, ‖T (k + 1) j - T k j‖ ≤ ‖π‖ ^ k := by
    intro k
    induction k with
    | zero => intro j; simpa using (TwistedDivision.norm_sub_le_max_of_ultrametric_field _ _).trans (max_le (hB 1 j) (hB 0 j))
    | succ k ih =>
      intro j
      have := TwistedDivision.step_diff τ hτ π c hc0 hc (T (k + 1)) (T k) _ (pow_nonneg (norm_nonneg _) _) ih j
      rw [← hTs (k + 1), ← hTs k, ← pow_succ'] at this
      exact this
  have hC : ∀ j, ∃ x, Tendsto (fun k => T k j) atTop (𝓝 x) := fun j =>
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric ‖π‖ 1 hπ fun k => by
      rw [dist_eq_norm, norm_sub_rev, one_mul]; exact hD k j)
  choose t ht using hC
  refine ⟨t, ?_, ?_, ?_⟩
  · have h0 : ∀ k, T k 0 = 1 := by
      intro k; cases k with
      | zero => rfl
      | succ k => rw [hTs]; exact TwistedDivision.step_zero _ _ _ _
    have : Tendsto (fun k => T k 0) atTop (𝓝 1) := by simp only [h0]; exact tendsto_const_nhds
    exact tendsto_nhds_unique (ht 0) this
  · intro j
    exact le_of_tendsto' (ht j).norm fun k => hB k j
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hL : Tendsto (fun k => π * T k (m + 2)) atTop (𝓝 (π * t (m + 2))) := (ht _).const_mul π
    have hR : Tendsto (fun k => ∑ i ∈ Finset.range (m + 2), T (k + 1) i * (τ ^ i) (c (m + 2 - 1 - i))) atTop
        (𝓝 (∑ i ∈ Finset.range (m + 2), t i * (τ ^ i) (c (m + 2 - 1 - i)))) :=
      tendsto_finsetSum _ fun i _ => (((ht i).comp (tendsto_add_atTop_nat 1)).mul_const _)
    have hEq : (fun k => π * T k (m + 2)) =
        fun k => ∑ i ∈ Finset.range (m + 2), T (k + 1) i * (τ ^ i) (c (m + 2 - 1 - i)) := by
      funext k; rw [hTs]; exact TwistedDivision.step_eq τ hτ π c hc0 _ m
    rw [hEq] at hL
    exact tendsto_nhds_unique hL hR

end GlobalTheory.Honda
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PositionOneOfSymmetricDoubleIntegralFinite
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

theorem GlobalTheory.PosOne.exUp_bilPos : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (μ : kˣ →* ℂˣ) (b : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), BilPos ψ μ p σ b → ∃ B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ, (∀ Ψ v, B Ψ v = exUp ν p σ (b Ψ) v) ∧ BilPos ψ μ (p + 1) σ B := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp hpc ψ hψ hψ1 ν _ A _ _ σ hσ μ b hb
  have H := GlobalTheory.RootEx.ExchangeSupport.exchange_support k n c p hp hpc ψ hψ hψ1 ν A σ hσ
  have E := GlobalTheory.RootEx.Exchange.exchange_isPos k n c p hp hpc ψ hψ hψ1 ν A σ hσ
  refine ⟨GlobalTheory.RootEx.Exchange.avg₂ ν (fun u => σ (rowE c p u)) b fun Ψ v => ((H (b Ψ) v).1 (hb.1 Ψ)).1,
    fun Ψ v => rfl, fun Ψ => ?_, fun g Ψ Ψ₁ v hΨ => ?_⟩
  · obtain ⟨l', hl', hN⟩ := E.1 (b Ψ) (hb.1 Ψ)
    have : (⇑((GlobalTheory.RootEx.Exchange.avg₂ ν (fun u => σ (rowE c p u)) b
        fun Ψ v => ((H (b Ψ) v).1 (hb.1 Ψ)).1) Ψ) : A → ℂ) = ⇑l' := by
      funext v; rw [hl']; rfl
    rw [this]; exact hN
  · change ∫ u, b Ψ₁ (σ (rowE c p u) (σ (embX c g) v)) ∂(Measure.pi fun _ => ν) =
      _ * ∫ u, b Ψ (σ (rowE c p u) v) ∂(Measure.pi fun _ => ν)
    let m : GL n k := ⟨g.valᵀ, (g⁻¹).valᵀ, by rw [← transpose_mul, Units.inv_mul, transpose_one],
      by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩
    have hm : Matrix.GeneralLinearGroup.det m = Matrix.GeneralLinearGroup.det g := by
      ext; simp [m]
    have step : ∀ u, b Ψ₁ (σ (rowE c p u) (σ (embX c g) v)) =
        ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) *
          b Ψ (σ (rowE c p (m.val.mulVec u)) v) := fun u => by
      rw [← Module.End.mul_apply, ← map_mul, GlobalTheory.RootEx.Exchange.rowE_mul_embX, map_mul, Module.End.mul_apply,
        hb.2 g Ψ Ψ₁ _ hΨ]
    simp only [step]
    rw [integral_const_mul, (GlobalTheory.SplitWeil.linear_change_of_variables k n n ν).1 m
      (fun u => b Ψ (σ (rowE c p u) v)), hm, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
      ← Real.rpow_neg_one, ← Real.rpow_add (GlobalTheory.SplitWeil.nabs_pos k _)]
    congr 3
    push_cast; ring

theorem GlobalTheory.PosOne.exUp_represents : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (P : Type) [AddCommGroup P] [Module ℂ P] (b B : P →ₗ[ℂ] A →ₗ[ℂ] ℂ), (∀ φ, IsNEquiv ψ p σ (b φ)) → (∀ φ v, B φ v = exUp ν p σ (b φ) v) → ∃ fj : P →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ, Represents ψ ν p σ fj B ∧ ∀ φ v (Φ₀ : SB (n → k)), fj φ v Φ₀ = ∫ u, GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν (Φ₀ : (n → k) → ℂ) u * b φ (σ (rowE c p u) v) ∂(Measure.pi fun _ => ν) := by
  intro k _ _ _ _ _ _ n _ _ c p hp hpc ψ hψ hψ1 ν _ A _ _ σ hσ P _ _ b B hbN hB
  haveI : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  have H := GlobalTheory.RootEx.ExchangeSupport.exchange_support k n c p hp hpc ψ hψ hψ1 ν A σ hσ
  have E := GlobalTheory.RootEx.Exchange.exchange_isPos k n c p hp hpc ψ hψ hψ1 ν A σ hσ
  have hBN : ∀ φ, IsNEquiv ψ (p + 1) σ (B φ) := fun φ => by
    obtain ⟨l', hl', hN⟩ := E.1 (b φ) (hbN φ)
    have : (⇑(B φ) : A → ℂ) = ⇑l' := by funext v; rw [hl', hB]
    rw [this]; exact hN
  have integ : ∀ φ v (Φ₀ : SB (n → k)), Integrable (fun β => (Φ₀ : (n → k) → ℂ) β *
      B φ (σ (colE c (p + 1) β) v)) (Measure.pi fun _ => ν) := fun φ v Φ₀ => by
    have hS := ((H (B φ) v).2 (hBN φ)).1
    exact GlobalTheory.RootEx.Exchange.integrable_of_mem_SB ν ⟨Φ₀.2.1.mul hS.1, Φ₀.2.2.mul_right⟩
  let fj : P →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => LinearMap.mk₂ ℂ
        (fun v Φ₀ => ∫ β, (Φ₀ : (n → k) → ℂ) β * B φ (σ (colE c (p + 1) β) v) ∂(Measure.pi fun _ => ν))
        (fun v₁ v₂ Φ₀ => by
          simp only [map_add, mul_add]
          exact integral_add (integ φ v₁ Φ₀) (integ φ v₂ Φ₀))
        (fun a v Φ₀ => by
          simp only [map_smul, smul_eq_mul, mul_left_comm _ a]
          exact integral_const_mul a _)
        (fun v Φ₀ Φ₀' => by
          simp only [Submodule.coe_add, Pi.add_apply, add_mul]
          exact integral_add (integ φ v Φ₀) (integ φ v Φ₀'))
        (fun a v Φ₀ => by
          simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
          exact integral_const_mul a _)
      map_add' := fun φ φ' => by
        ext v Φ₀
        simp only [LinearMap.mk₂_apply, LinearMap.add_apply, map_add, mul_add]
        exact integral_add (integ φ v Φ₀) (integ φ' v Φ₀)
      map_smul' := fun a φ => by
        ext v Φ₀
        simp only [LinearMap.mk₂_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply,
          mul_left_comm _ a]
        exact integral_const_mul a _ }
  refine ⟨fj, ⟨hBN, fun φ v Φ₀ => ⟨integ φ v Φ₀, rfl⟩⟩, fun φ v Φ₀ => ?_⟩
  have hg := (H (b φ) v).1 (hbN φ)
  change ∫ β, (Φ₀ : (n → k) → ℂ) β * B φ (σ (colE c (p + 1) β) v) ∂(Measure.pi fun _ => ν) = _
  simp only [hB, hg.2.2]
  simp only [← integral_const_mul]
  rw [integral_integral_swap]
  · simp only [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat, ← integral_mul_const]
    congr 1; funext u; congr 1; funext β; ring
  · have h1 := GlobalTheory.RootEx.Exchange.integrable_of_mem_SB ν Φ₀.2
    have h2 := GlobalTheory.RootEx.Exchange.integrable_of_mem_SB ν hg.1
    refine (h1.mul_prod h2).norm.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · apply Continuous.aestronglyMeasurable
      exact (Φ₀.2.1.continuous.comp continuous_fst).mul
        (((continuous_induced_dom.comp hψ).comp
          ((continuous_snd.dotProduct continuous_fst))).mul (hg.1.1.continuous.comp continuous_snd))
    · obtain ⟨β, u⟩ := z
      simp only [Function.uncurry_apply_pair, norm_mul, Circle.norm_coe, one_mul, norm_norm, le_refl]

noncomputable section
namespace GlobalTheory.PosOne

theorem om_one_comp {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (g : GL a k)
    (h : GL b k) (Φ : Matrix b a k → ℂ) : om μ 1 h (om μ g 1 Φ) = om μ g h Φ := by
  funext x
  simp only [om, map_one, inv_one, Units.val_one, mul_one, one_mul, Matrix.mul_one, Matrix.one_mul]
  have : nabs k (1 : kˣ) = 1 := by simp [nabs]
  simp only [this, Real.one_rpow, Complex.ofReal_one, mul_one, one_mul, Matrix.mul_assoc]
  ring

open Classical in

theorem app_eq_dite {X V : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℂ V] (l : SB X →ₗ[ℂ] V)
    (f : X → ℂ) : app l f = l (if h : f ∈ SB X then ⟨f, h⟩ else 0) := by
  unfold app; split_ifs <;> simp

theorem oneDbl_of_symDbl : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ) (_ : c + 1 = 2 * ρ) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν) (μ₁ μ₂ : kˣ →* ℂˣ) (_ : IsOpen (μ₁.ker : Set kˣ)) (_ : IsOpen (μ₂.ker : Set kˣ)) (m₁ : Measure (GL n₁ k)) [m₁.IsHaarMeasure] (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) [G₁.IsHaarMeasure] (m₂ : Measure (GL n₂ k)) [m₂.IsHaarMeasure] (G₂ : Measure (GL (n₂ ⊕ Fin c) k)) [G₂.IsHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : TriPos ψ μ₁ μ₂ ρ σ T) (F : A) (ρ₀ : Representation ℂ (GL (n₀ ⊕ Fin (c + 1 + 1)) k) (SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k))) (_ : IsSrc μ₁ ρ₀) (Φ₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)) (e : GL (n₀ ⊕ Fin (c + 1 + 1)) k →₀ ℂ) (_ : SrcComb ψ ν (ρ + 1) ρ₀ Φ₁ e) (z : GL (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ), (∀ g ∈ e.support, SymDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ σ T F (om μ₁ g 1 Φ₁.1) Φ₂.1 (z g)) → OneDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ σ T F Φ₁.1 Φ₂.1 (comb e z) := by
  intro k _ _ _ _ _ _ n₀ n₁ n₂ _ _ _ _ _ _ c ρ hcρ ψ hψ hψ1 ν hν μ₁ μ₂ hμ₁ hμ₂ m₁ _ G₁ _ m₂ _ G₂ _ A _ _ σ hσ T hT
    F ρ₀ hρ₀ Φ₁ Φ₂ e he z hz
  haveI : ν.IsAddHaarMeasure := hν.1
  have hρ1 : 1 ≤ ρ := by omega
  obtain ⟨⟨ρ₁, hρ₁⟩, hsm⟩ := GlobalTheory.T.exists_weilSourceAction_and_smooth k (n₁ ⊕ Fin (c + 1)) (n₂ ⊕ Fin c) μ₂ hμ₂
  have hρ₁s : IsSmoothRep ρ₁ := hsm ρ₁ hρ₁
  obtain ⟨b, hb, hb2, hb3⟩ := GlobalTheory.T.exists_bilinear_position_middle_vertex k n₀ n₁ n₂ c ρ hcρ ψ hψ hψ1 ν hν μ₁ μ₂ hμ₁ hμ₂ m₁ G₁ m₂ G₂ A σ hσ T hT
    F ρ₁ hρ₁
  obtain ⟨B, hB, hBpos⟩ := GlobalTheory.PosOne.exUp_bilPos k n₁ n₀ (c + 1) ρ hρ1 (by omega) ψ hψ hψ1 ν _ ρ₁ hρ₁s μ₁ b hb
  obtain ⟨fj, hrep, hfj⟩ := GlobalTheory.PosOne.exUp_represents k n₁ (c + 1) ρ hρ1 (by omega) ψ hψ hψ1 ν _ ρ₁ hρ₁s _ b B hb.1 hB
  obtain ⟨-, hpos⟩ := GlobalTheory.T.exchangeToPositionOne_isPositionOne k n₁ n₀ (c + 1) ρ hρ1 (by omega) ψ hψ hψ1 ν _ ρ₁ hρ₁s
  obtain ⟨B₁, hB₁, -⟩ := hpos μ₁ hμ₁ b hb
  have hstep : ∀ g ∈ e.support, IsQuotInt ν m₁ G₁ (ρ + 1)
      (tInt ψ ν μ₁ (ρ + 1) ρ₁ B Φ₂ (om μ₁ g 1 Φ₁.1)) (z g) := by
    intro g hg
    obtain ⟨w', hw', hFJ⟩ := hz g hg
    have hΦ' : ((ρ₀ g Φ₁ : SB _) : Matrix _ _ k → ℂ) = om μ₁ g 1 Φ₁.1 := hρ₀ g Φ₁
    have key : w' = fun h Ψ Φ₀ => fj Ψ (ρ₁ h Φ₂) Φ₀ := by
      funext h Ψ Φ₀
      have hV : ((ρ₁ h Φ₂ : SB _) : Matrix _ _ k → ℂ) = om μ₂ h 1 Φ₂.1 := hρ₁ h Φ₂
      obtain ⟨-, hav⟩ := GlobalTheory.T.schwartzBruhat_self_average_heisenberg k n₂ n₁ c ρ hρ1 (by omega) ψ hψ hψ1 ν hν μ₂ hμ₂ (ρ₁ h Φ₂)
      obtain ⟨hmem, hE, hL⟩ := hav Φ₀
      have h1 := hb2 Ψ ⟨_, hmem⟩
      have h2 := hw' h Ψ Φ₀
      have hf : tInt ψ ν μ₂ ρ σ (T Ψ) F (GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν μ₂ ρ Φ₀.1 (ρ₁ h Φ₂).1) =
          fun h' => app (T Ψ) (opEFJ ψ ν ρ Φ₀.1 (om μ₂ h h' Φ₂.1)) (σ h' F) := by
        funext h'
        simp only [tInt]
        rw [hE h', hV, om_one_comp]
      rw [hf] at h1
      have heq := (GlobalTheory.QuotInt.quotInt_unique_exists k n₂ c ρ hρ1 (by omega) ν m₂ G₂ _).1 _ _ h2 h1
      rw [heq, hfj, ← GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe (b Ψ) ⟨_, hmem⟩]
      exact hL ρ₁ hρ₁ (b Ψ)
    rw [key, ← hΦ'] at hFJ
    have := (GlobalTheory.T.fourierJacobi_target_bilinear_form_integral k n₁ n₀ (c + 1) ρ hρ1 hcρ ψ hψ hψ1 ν hν μ₁ hμ₁ m₁ G₁ _ ρ₁ hρ₁s fj B hrep hBpos Φ₂
      (ρ₀ g Φ₁) (z g)).2 hFJ
    rwa [hΦ'] at this
  have hone := GlobalTheory.T.bessel_step_position_one_finite k n₁ n₀ (c + 1) (ρ + 1) (by omega) (by omega) ψ hψ hψ1 ν hν μ₁ hμ₁ m₁ G₁ ρ₀ hρ₀ Φ₁ e he
    _ ρ₁ hρ₁s B hBpos Φ₂ z hstep
  refine ⟨fun h => B₁.flip (ρ₁ h Φ₂), fun h Ψ => ?_, ?_⟩
  · have := hb3 Ψ (ρ₁ h Φ₂)
    rw [hρ₁ h Φ₂] at this
    simpa [hB₁] using this
  · convert hone using 1
    funext h
    obtain ⟨q, rfl⟩ : ∃ q, ρ = q + 1 := ⟨ρ - 1, by omega⟩
    simp only [tIntOne, app_eq_dite]
    rw [toOne_succ]
    classical
    set Ψf := (if hf : opE ψ ν 1 (om μ₁ 1 h Φ₁.1) ∈ SB (Matrix n₁ n₀ k) then ⟨_, hf⟩ else 0 : SB (Matrix n₁ n₀ k))
    have hd : exDown ν (q + 1) ρ₁ (fun v => B Ψf v) = fun v => b Ψf v := by
      funext v
      simp only [exDown, hB]
      exact (GlobalTheory.RootEx.exDown_exUp_and_exUp_exDown k n₁ (c + 1) (q + 1) hρ1 (by omega) ψ hψ hψ1 ν hν _ ρ₁ hρ₁s
        (b Ψf) v).1 (hb.1 Ψf)
    rw [hd, LinearMap.flip_apply, hB₁]

end GlobalTheory.PosOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SubstCongrModPrimeOfIntegralDerivative
section
open PowerSeries

noncomputable section

namespace GlobalTheory.Honda

theorem subst_congr_of_derivative_integral :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime → ‖(l : K)‖ < 1 →
    ∀ (f : K⟦X⟧), CoefLe 1 (derivative K f) → ∀ (s : Type) (A B : MvPowerSeries s K),
    MvPowerSeries.constantCoeff A = 0 → MvPowerSeries.constantCoeff B = 0 →
    (∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1) → (∀ m, ‖MvPowerSeries.coeff m B‖ ≤ 1) →
    (∀ m, ‖MvPowerSeries.coeff m (A - B)‖ ≤ ‖(l : K)‖) →
    ∀ m, ‖MvPowerSeries.coeff m (f.subst A - f.subst B)‖ ≤ ‖(l : K)‖ := by
  intro K _ _ _ l hl hlt f hf s A B hA0 hB0 hA hB hAB m
  have hsA : HasSubst A := HasSubst.of_constantCoeff_zero hA0
  have hsB : HasSubst B := HasSubst.of_constantCoeff_zero hB0

  have hterm : ∀ d : ℕ, ‖coeff d f * MvPowerSeries.coeff m (A ^ d - B ^ d)‖ ≤ ‖(l : K)‖ := by
    intro d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    have hcong := Formalism.LT.PowCongr_valid K s l hl A B hA hB 1 le_rfl
      (by intro e; simpa using hAB e) (padicValNat l d) (d / l ^ padicValNat l d) m
    have hdecomp : l ^ padicValNat l d * (d / l ^ padicValNat l d) = d :=
      Nat.mul_div_cancel' pow_padicValNat_dvd
    rw [hdecomp, norm_pow, pow_add, pow_one] at hcong
    have hnd : ‖(d : K)‖ = ‖(l : K)‖ ^ padicValNat l d :=
      Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat hl hlt hd.ne'
    have hder : ‖coeff d f‖ * ‖(d : K)‖ ≤ 1 := by
      obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
      have := hf k
      rw [coeff_derivative, norm_mul] at this
      simpa using this
    rw [norm_mul]
    calc ‖coeff d f‖ * ‖MvPowerSeries.coeff m (A ^ d - B ^ d)‖
        ≤ ‖coeff d f‖ * (‖(l : K)‖ * ‖(d : K)‖) := by
          rw [hnd]; exact mul_le_mul_of_nonneg_left hcong (norm_nonneg _)
      _ = ‖(l : K)‖ * (‖coeff d f‖ * ‖(d : K)‖) := by ring
      _ ≤ ‖(l : K)‖ * 1 := mul_le_mul_of_nonneg_left hder (norm_nonneg _)
      _ = ‖(l : K)‖ := mul_one _
  rw [map_sub, coeff_subst hsA, coeff_subst hsB,
    ← finsum_sub_distrib (coeff_subst_finite hsA f m) (coeff_subst_finite hsB f m)]
  have heq : (fun d : ℕ => coeff d f • MvPowerSeries.coeff m (A ^ d) - coeff d f • MvPowerSeries.coeff m (B ^ d))
      = fun d => coeff d f * MvPowerSeries.coeff m (A ^ d - B ^ d) := by
    funext d; rw [map_sub, smul_eq_mul, smul_eq_mul, mul_sub]
  have hfin : (Function.support fun d : ℕ => coeff d f * MvPowerSeries.coeff m (A ^ d - B ^ d)).Finite := by
    rw [← heq]
    exact ((coeff_subst_finite hsA f m).union (coeff_subst_finite hsB f m)).subset
      (Function.support_sub _ _)
  rw [heq, finsum_eq_sum _ hfin]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun d _ => hterm d

end GlobalTheory.Honda
end
end

