import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0148
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0147
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0154
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0149
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0100
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0153
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0002
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0005
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0004
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0150

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameChangeUnitaryStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_frame_change_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ) (A A' : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), R.form = F.form → C.IsAdapted R A → (∀ τ, (A' τ)ᴴ * C.sgr τ * A' τ = sgI j j') → (C.IsAdapted R A' ↔ ∀ τ, (C.cinv (A τ) τ * A' τ)ᴴ * (C.cinv (A τ) τ * A' τ) = 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Change.isAdapted_iff_unitary | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Change.isAdapted_iff_unitary | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Change.isAdapted_iff_unitary <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameDeterminesLatticeStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_frame_determines_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R R' : RiemLat E g Λ) (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), R.form = F.form → R'.form = F.form → C.IsAdapted R A → C.IsAdapted R' A → R.EqvBy R' 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.adapted_eqvBy | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.adapted_eqvBy | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.adapted_eqvBy <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameHermitianProduct
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F) (R : RiemLat E g Λ)

open Classical in

theorem perExt_I_of_pBar {τ : Ψ} {y : Fin (j + j') → ℂ} (h : C.pBar R τ y = 0) :
    C.perExt R (Pi.single τ (Complex.I • y)) = Complex.I • C.perExt R (Pi.single τ y) := by
  ext k
  have hk := congrFun h k
  simp only [LatEmb.pBar, Pi.smul_apply, Pi.add_apply, Pi.zero_apply, smul_eq_mul] at hk ⊢
  linear_combination (-2 * Complex.I) * hk +
    ((C.perExt R (Pi.single τ (Complex.I • y))) k) * Complex.I_mul_I

open Classical in

theorem pPart_of_pBar {τ : Ψ} {y : Fin (j + j') → ℂ} (h : C.pBar R τ y = 0) :
    C.pPart R τ y = C.perExt R (Pi.single τ y) := by
  have h1 := perExt_I_of_pBar C R h
  ext k
  simp only [LatEmb.pPart, h1, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  linear_combination (-(1 / 2 : ℂ) * (C.perExt R (Pi.single τ y)) k) * Complex.I_mul_I

open Classical in

theorem Fm_single (τ : Ψ) (y x : Fin (j + j') → ℂ) :
    C.Fm (Pi.single τ y) (Pi.single τ x) =
      2 * (embOf (F.σ τ) C.xi * (star x ⬝ᵥ (C.gr τ *ᵥ y))).re := by
  unfold LatEmb.Fm
  rw [Finset.sum_eq_single τ]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ τ) h

theorem xi_block {A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ} (hA : C.IsAdapted R A) (τ : Ψ)
    (x y : Fin j' → ℂ) :
    embOf (F.σ τ) C.xi * (star (A τ *ᵥ Sum.elim 0 x) ⬝ᵥ (C.gr τ *ᵥ (A τ *ᵥ Sum.elim 0 y))) =
      -(Complex.I * (C.c : ℂ) * (star x ⬝ᵥ y)) := by
  have hs : star (A τ *ᵥ Sum.elim 0 x) ⬝ᵥ (C.sgr τ *ᵥ (A τ *ᵥ Sum.elim 0 y)) = -(star x ⬝ᵥ y) := by
    have h1 : star (A τ *ᵥ Sum.elim 0 x) ⬝ᵥ (C.sgr τ *ᵥ (A τ *ᵥ Sum.elim 0 y)) =
        star (Sum.elim 0 x : Sg j j' → ℂ) ⬝ᵥ (((A τ)ᴴ * C.sgr τ * A τ) *ᵥ Sum.elim 0 y) := by
      rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      simp only [Matrix.dotProduct_mulVec]
    rw [h1, hA.unit τ]
    simp only [sgI, Matrix.fromBlocks_mulVec]
    simp [dotProduct, Fintype.sum_sum_type, Matrix.neg_mulVec]
  have hg : C.sgr τ = ((C.eps τ : ℝ) : ℂ) • C.gr τ := rfl
  rw [hg, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hs
  rw [C.xi_eq τ]
  push_cast
  linear_combination (Complex.I * (C.c : ℂ)) * hs

theorem gram_last_block : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ) (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), (∀ y y', (C.perExt R y ⬝ᵥ R.Hm *ᵥ star (C.perExt R y')).im = C.Fm y y') → C.IsAdapted R A → ∀ (τ : Ψ) (x y : Fin j' → ℂ), R.ip (C.pPart R τ (A τ *ᵥ Sum.elim 0 x)) (C.pPart R τ (A τ *ᵥ Sum.elim 0 y)) = ((2 * C.c : ℝ) : ℂ) * (star x ⬝ᵥ y) := by
  classical
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C R A hF hA τ x y
  have hx := pPart_of_pBar C R (hA.kerBar τ x)
  have hy := pPart_of_pBar C R (hA.kerBar τ y)
  have hiy := perExt_I_of_pBar C R (hA.kerBar τ y)
  have h1 := hF (Pi.single τ (A τ *ᵥ Sum.elim 0 y)) (Pi.single τ (A τ *ᵥ Sum.elim 0 x))
  have h2 := hF (Pi.single τ (Complex.I • (A τ *ᵥ Sum.elim 0 y))) (Pi.single τ (A τ *ᵥ Sum.elim 0 x))
  rw [Fm_single, xi_block C R hA] at h1
  rw [Fm_single, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, mul_left_comm, xi_block C R hA, hiy,
    smul_dotProduct, smul_eq_mul] at h2
  rw [RiemLat.ip, hx, hy]
  set H := C.perExt R (Pi.single τ (A τ *ᵥ Sum.elim 0 y)) ⬝ᵥ
    R.Hm *ᵥ star (C.perExt R (Pi.single τ (A τ *ᵥ Sum.elim 0 x))) with hH
  set w := star x ⬝ᵥ y with hw
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im] at h1 h2 ⊢
    linarith
  · simp [Complex.mul_re, Complex.mul_im] at h1 h2 ⊢
    linarith

end

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameInversePropertiesStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_frame_inverse_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (τ : Ψ) (A : Matrix (Fin (j + j')) (Sg j j') ℂ), Aᴴ * C.sgr τ * A = sgI j j' → C.cinv A τ * A = 1 ∧ A * C.cinv A τ = 1 ∧ ((C.cinv A τ)ᴴ * C.cinv A τ).PosDef ∧ ((C.cinv A τ)ᴴ * C.cinv A τ) * (C.gr τ)⁻¹ * ((C.cinv A τ)ᴴ * C.cinv A τ) = C.gr τ ∧ (∀ a ai : Matrix (Fin (j + j')) (Fin (j + j')) ℂ, a * ai = 1 → aᴴ * C.gr τ * a = C.gr τ → (a * A)ᴴ * C.sgr τ * (a * A) = sgI j j' ∧ C.cinv (a * A) τ = C.cinv A τ * ai ∧ IsSgU (C.cinv A τ * (a * A)) ∧ ((C.cinv A τ * (a * A))ᴴ * (C.cinv A τ * (a * A)) = 1 ↔ aᴴ * ((C.cinv A τ)ᴴ * C.cinv A τ) * a = (C.cinv A τ)ᴴ * C.cinv A τ)) ∧ ∀ A' : Matrix (Fin (j + j')) (Sg j j') ℂ, A'ᴴ * C.sgr τ * A' = sgI j j' → (A' * C.cinv A τ)ᴴ * C.gr τ * (A' * C.cinv A τ) = C.gr τ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.cinv_facts | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.cinv_facts | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.cinv_facts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameOfEquivalentStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_frame_of_equivalent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R R' : RiemLat E g Λ) (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), C.IsAdapted R A → R.EqvBy R' 1 → C.IsAdapted R' A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.isAdapted_of_eqvBy | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.isAdapted_of_eqvBy | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.isAdapted_of_eqvBy <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AgreementPositive
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

def agreeRate (t : ℝ) : ℝ := Real.log (Real.log (1 / t)) ^ 2 / Real.log (1 / t)

theorem agree_exp_le_sq {s : ℝ} (hs : 0 < s) : Real.exp (-(s ^ 2)⁻¹) ≤ s ^ 2 := by
  have hx : 0 < (s ^ 2)⁻¹ := by positivity
  have h1 : (s ^ 2)⁻¹ ≤ Real.exp ((s ^ 2)⁻¹) := by linarith [Real.add_one_le_exp ((s ^ 2)⁻¹)]
  rw [Real.exp_neg]
  calc (Real.exp (s ^ 2)⁻¹)⁻¹ ≤ ((s ^ 2)⁻¹)⁻¹ := inv_anti₀ hx h1
    _ = s ^ 2 := inv_inv _

theorem agreeRate_nonneg (s : ℝ) (hs : 0 < s) : 0 ≤ agreeRate (Real.exp (-(s ^ 2)⁻¹)) := by
  unfold agreeRate
  rw [limRate_log_inv_exp]
  have : 0 < (s ^ 2)⁻¹ := by positivity
  positivity

theorem agree_cauchy (hI : Inputs) (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (h0 : 0 < S.t₀) :
    ∃ C' t₁ : ℝ, 0 < t₁ ∧ t₁ ≤ S.t₀ ∧
    ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (Re : Realis S P)
      (w : Fin (D + 1) → σ) (t t' : ℝ), 0 < t' → t' ≤ t → t ≤ t₁ →
      |Re.num II t w - Re.num II t' w| ≤ ((D : ℝ) + 1) * (|C'| * |agreeRate t|) := by
  obtain ⟨C', t₁, ht₁, ht₁0, hb⟩ := GlobalTheory.T.monge_ampere_regularization_log_log_bound hI.convergenceRate D σ S h0
  refine ⟨C', t₁, ht₁, ht₁0, ?_⟩
  intro II hII K _ ι _ P Re w t t' ht' htt ht
  have ht0 : 0 < t := lt_of_lt_of_le ht' htt
  rw [GlobalTheory.T.intersection_difference_telescoping_integral hI II hII K ι D σ S P Re t t' w ht0 (ht.trans ht₁0) ht' ((htt.trans ht).trans ht₁0)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hr : ∀ r : Fin (D + 1), |mInt S.A (fun i => S.potT (w (r.succAbove i)) (if r.succAbove i < r then t else t'))
      (fun x => S.phT (w r) t x - S.phT (w r) t' x)| ≤ |C'| * |agreeRate t| := by
    intro r
    have := hb t t' ht' htt ht (w r) (fun i => w (r.succAbove i)) (fun i => decide (r.succAbove i < r))
    simp only [decide_eq_true_eq] at this
    refine this.trans ?_
    rw [mul_div_assoc]
    exact (le_abs_self _).trans (by rw [abs_mul]; rfl)
  refine (Finset.sum_le_sum fun r _ => hr r).trans ?_
  simp

theorem agreementPos : AgreementPos := by
  intro hI D σ _ S abelian₂ h0
  obtain ⟨C', t₁, ht₁, ht₁0, hc⟩ := agree_cauchy hI D σ S h0
  obtain ⟨hlim, hrate, -, -⟩ := limRate
  refine ⟨|abelian₂| ^ (D + 1) * (((D : ℝ) + 1) * (|C'| * 4)), min 1 t₁, lt_min one_pos ht₁, ?_⟩
  intro II hII K _ ι _ P Re
  have hδ : Tendsto (fun t => ((D : ℝ) + 1) * (|C'| * |agreeRate t|)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t => |agreeRate t|) (𝓝[>] 0) (𝓝 0) := by
      have h2 := hlim.abs
      rw [abs_zero] at h2
      exact h2
    simpa using (this.const_mul |C'|).const_mul ((D : ℝ) + 1)
  have hL := fun w => tendsto_limUnder_of_cauchy_rate (fun t => Re.num II t w)
    (fun t => ((D : ℝ) + 1) * (|C'| * |agreeRate t|)) t₁ ht₁ hδ (hc II hII K ι P Re w)
  refine ⟨fun w => (hL w).1, fun s hs hss => ?_⟩
  have hs1 : s ≤ 1 := hss.trans (min_le_left _ _)
  have hst : s ≤ t₁ := hss.trans (min_le_right _ _)
  have hT : Real.exp (-(s ^ 2)⁻¹) ≤ t₁ := by
    refine (agree_exp_le_sq hs).trans ?_
    nlinarith
  refine ⟨hT.trans ht₁0, fun c hcL => ?_⟩
  set t := Real.exp (-(s ^ 2)⁻¹)
  have hM : ∀ w, |Re.num II t w - Re.limNum II w| ≤ ((D : ℝ) + 1) * (|C'| * |agreeRate t|) :=
    fun w => (hL w).2 t (Real.exp_pos _) hT
  have hb := (formPoly_sub_bound σ (D + 1) (Re.num II t) (Re.limNum II) _ hM).2 c
  have hr : |agreeRate t| ≤ 4 * s := by
    rw [abs_of_nonneg (agreeRate_nonneg s hs)]
    exact hrate s hs hs1
  have hsum : (∑ a, |c a|) ^ (D + 1) ≤ |abelian₂| ^ (D + 1) :=
    pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) (hcL.trans (le_abs_self _)) _
  have hD : (0 : ℝ) ≤ (D : ℝ) + 1 := by positivity
  calc |eval c (Re.FT II t) - eval c (Re.PB II)|
      ≤ (∑ a, |c a|) ^ (D + 1) * (((D : ℝ) + 1) * (|C'| * |agreeRate t|)) := hb
    _ ≤ |abelian₂| ^ (D + 1) * (((D : ℝ) + 1) * (|C'| * (4 * s))) := by
      gcongr
    _ = |abelian₂| ^ (D + 1) * (((D : ℝ) + 1) * (|C'| * 4)) * s := by ring

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AlternatingFormHermitianDescentStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alternating_form_hermitian_descent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (N : ℕ) (e : Λ →+ (Fin N → E)), Function.Injective e → (∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x) → (∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v) → ∀ form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ, (∀ x, form x x = 0) → Function.Bijective form → (∀ a a' : 𝓞 E, (a' : E) = IsCMField.complexConj E (a : E) → ∀ x y, form (a • x) y = form x (a' • y)) → ∃ B : LinearMap.BilinForm ℚ (Fin N → E), (∀ x y, B (e x) (e y) = ((form x y : ℤ) : ℚ)) ∧ (∀ (a : E) u v, B (a • u) v = B u (IsCMField.complexConj E a • v)) ∧ (∀ u v, B u v = - B v u) ∧ ∀ u, (∀ v, B v u = 0) → u = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatBil.exists_rat_bilin | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatBil.exists_rat_bilin | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatBil.exists_rat_bilin <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AlternatingFormLatticeCompatibleStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alternating_form_lattice_compatible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (N : ℕ) (e : Λ →+ (Fin N → E)), Function.Injective e → ∀ form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ, Function.Bijective form → ∀ B : LinearMap.BilinForm ℚ (Fin N → E), (∀ x y, B (e x) (e y) = ((form x y : ℤ) : ℚ)) → (∀ u v, B u v = - B v u) → (∀ u, (∀ v, B v u = 0) → u = 0) → (∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v) → ∀ (h : HermitianForm (maximalRealSubfield E) E (Fin N → E)) (m : ℕ), m ≠ 0 → (∀ (a : E) u v, Algebra.trace ℚ E (a * (((m : E) * (H.rt : E))⁻¹ * h.toSesq v u)) = B (a • u) v) → e.range.relIndex (dualLattice h e.range) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.latEmb_relIndex_dual_ne_zero | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.latEmb_relIndex_dual_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.latEmb_relIndex_dual_ne_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchimedeanActionOnLatticeVectorsStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_action_on_lattice_vectors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (γ : C.h.unitaryGroup) (x : Λ) (τ : Ψ), C.tm (archEmbed C.h (Pi.basisFun E (Fin (j + j'))) γ) τ *ᵥ C.vec x τ = fun i => embOf (F.σ τ) (((γ : C.h.unitaryGroup) : (Fin (j + j') → E) ≃ₗ[E] (Fin (j + j') → E)) (C.e x) i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.tm_archEmbed_mulVec_vec | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.tm_archEmbed_mulVec_vec | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.tm_archEmbed_mulVec_vec <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchimedeanUnitaryRepresentationStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_unitary_representation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F), (∀ (a b : C.Arch) τ, C.tm (a * b) τ = C.tm a τ * C.tm b τ) ∧ (∀ τ, C.tm 1 τ = 1) ∧ (∀ (a : C.Arch) τ, (C.tm a τ)ᴴ * C.gr τ * C.tm a τ = C.gr τ) ∧ ∀ τ, Continuous fun a : C.Arch => C.tm a τ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TmBasic.tm_basic | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TmBasic.tm_basic | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TmBasic.tm_basic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchimedeanUnitarySurjectiveStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_unitary_surjective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (b : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ), (∀ τ, (b τ)ᴴ * C.gr τ * b τ = C.gr τ) → ∃ a : C.Arch, ∀ τ, C.tm a τ = b τ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.tm_surj | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.tm_surj | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.tm_surj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallAutomorphismInverseExistsStatement
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ball_automorphism_inverse_exists : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (Z : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ Z (ballDom q) → Set.BijOn Z (ballDom q) (ballDom q) → DifferentiableOn ℂ G (ballDom q) → (∀ t ∈ ballDom q, ballPot q (Z t) = ballPot q t + (G t).re) → ∃ Y : (Fin n → ℂ) → Fin n → ℂ, DifferentiableOn ℂ Y (ballDom q) ∧ ∀ t ∈ ballDom q, Y t ∈ ballDom q ∧ Z (Y t) = t ∧ Y (Z t) = t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BallInverse.exists_inverse | exact GlobalTheory.CompanionTheory.Ar.Cusp.BallInverse.exists_inverse | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BallInverse.exists_inverse <;> assumption)
end

