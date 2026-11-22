import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0136
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1835
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1119
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1825
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1744
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasInfinityExponentOfFinitePartPower
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormExact.InfExp

open IsDedekindDomain

theorem finAdEquiv_one_tmul (D : D7) (k : D.host.E) :
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] k) =
      GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.inc D k) := by
  apply FiniteAdeleRing.ext
  intro w
  rw [GlobalTheory.LFun.finAdEquiv_tmul]
  simp only [GlobalTheory.BotFormula.toFinE, Formalism.MainNotions.StandardLatticesGL3.inc, Formalism.UG.inclE, RingEquiv.trans_apply,
    AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.includeLeftRingHom_apply,
    Algebra.TensorProduct.comm_tmul]
  rw [GlobalTheory.LFun.finAdEquiv_tmul]
  simp

theorem eq_inf {D : D7} {N : ℕ} (c : HeckeU D N) (e : ℤ) (χ : (AE D)ˣ →* Circle) (hχ : IsHeckeChar D χ)
    (hf : HasFinPart χ c e) (k : D.host.Eˣ) (x y : (AE D)ˣ) (hxy : Units.map (incA D).toMonoidHom k = x * y)
    (hy : infPart D (y : AE D) = 1) (hy' : finPart D (y : AE D) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (k : D.host.E)) :
    ((χ x : Circle) : ℂ) =
      ∏ τ, (embT D τ (k : D.host.E) / ((‖embT D τ (k : D.host.E)‖ : ℝ) : ℂ)) ^ (e * c.n τ) := by
  have hfin : ((χ y : Circle) : ℂ) = ((c.f (Units.map (Formalism.MainNotions.StandardLatticesGL3.inc D).toMonoidHom k) ^ e : ℂˣ) : ℂ) :=
    hf y _ ⟨hy, by rw [hy']; exact finAdEquiv_one_tmul D k⟩
  have h5 : ((χ x : Circle) : ℂ) * ((χ y : Circle) : ℂ) = 1 := by
    rw [← Circle.coe_mul, ← map_mul, ← hxy, hχ.2 k, Circle.coe_one]
  have haut := c.aut k
  set F : ℂ := ((c.f (Units.map (Formalism.MainNotions.StandardLatticesGL3.inc D).toMonoidHom k) : ℂˣ) : ℂ) with hF
  have hF0 : F ≠ 0 := (c.f _).ne_zero
  have hP : ∏ τ, (embT D τ (k : D.host.E) / ((‖embT D τ (k : D.host.E)‖ : ℝ) : ℂ)) ^ (c.n τ) = F⁻¹ :=
    eq_inv_of_mul_eq_one_right haut
  rw [Units.val_zpow_eq_zpow_val, ← hF] at hfin
  rw [hfin] at h5
  have hx : ((χ x : Circle) : ℂ) = (F ^ e)⁻¹ := eq_inv_of_mul_eq_one_left h5
  rw [hx, ← inv_zpow, ← hP, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_mul, mul_comm]

set_option maxHeartbeats 1000000 in
open Formalism.MainNotions Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host GlobalTheory.FockCompare GlobalTheory.HeckeFinTrivial in

theorem hasInfExp_of_hasFinPart : ∀ {D : D7} {N : ℕ} (c : HeckeU D N) (e : ℤ) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ →
    HasFinPart χ c e → ∀ τ, HasInfExp D χ τ ((e : ℚ) * (c.n τ : ℚ) / 2) := by
  intro D N c e χ hχ hf τ₀
  obtain ⟨⟨θ', hθ'⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  refine ⟨e * c.n τ₀, by push_cast; ring, ⟨fun τ => θ' (tauE D τ), fun τ => hθ' _⟩, fun θ hθ => ?_⟩
  obtain ⟨ρ, hρ, r1, r0⟩ := exists_real_chart D θ hθ (GlobalTheory.CMTypePlaces.places_bijective D)
  obtain ⟨s, hs⟩ := RealChart.exists_chart D θ hθ ρ hρ r1 r0
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  haveI : Nonempty D.what₂.Tau := ⟨τ₀⟩
  have ext : ∀ a b : AE D, finPart D a = finPart D b → (∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) → a = b := by
    intro a b h1 h2
    rw [← sub_eq_zero]
    exact hs.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
      rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]
  let t : (D.what₂.Tau → ℂˣ) → AE D := fun z => s (fun τ => (z τ : ℂ)) + (1 - s 1)
  have tf : ∀ z, finPart D (t z) = 1 := fun z => by
    simp only [t, RingHom.map_add, RingHom.map_sub, RingHom.map_one, hs.fin, zero_add, sub_zero]
  have ti : ∀ z τ, θ τ (infPart D (t z)) = z τ := fun z τ => by
    simp only [t, RingHom.map_add, RingHom.map_sub, RingHom.map_one, hs.comp, Pi.one_apply, sub_self, add_zero]
  have tc : Continuous t :=
    (hs.cont.comp (continuous_pi fun τ => Units.continuous_val.comp (continuous_apply τ))).add continuous_const
  let T : (D.what₂.Tau → ℂˣ) →* AE D :=
    { toFun := t
      map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by
        rw [ti, RingHom.map_one, RingHom.map_one]; rfl
      map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by
        rw [RingHom.map_mul, RingHom.map_mul, ti, ti, ti]; rfl }
  have Tc : Continuous T.toHomUnits := Units.continuous_iff.2 ⟨tc, tc.comp continuous_inv⟩
  have hT : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 →
      x = T.toHomUnits fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x := fun x hx =>
    Units.ext (ext _ _ (hx.trans (tf _).symm) fun τ =>
      (ti (fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom x) τ).symm)
  have hd : DenseRange fun (k : D.host.E) τ => tauE D τ k := by
    intro z
    have := mem_closure_range (tauE D) θ (fun τ => (hθ τ).1) (fun τ => (hθ τ).2) (infPart D (s z))
    rwa [show (fun i => θ i (infPart D (s z))) = z from funext fun τ => hs.comp z τ] at this
  have key : ∀ z : D.what₂.Tau → ℂˣ,
      ((χ (T.toHomUnits z) : Circle) : ℂ) = ∏ τ, ((z τ : ℂ) / ((‖(z τ : ℂ)‖ : ℝ) : ℂ)) ^ (e * c.n τ) := by
    intro z
    refine (denseRange_units (tauE D) hd).induction_on z (isClosed_eq
      (continuous_subtype_val.comp (hχ.1.comp Tc)) (continuous_finset_prod _ fun τ _ => ?_)) fun k => ?_
    · have h1 : Continuous fun z : D.what₂.Tau → ℂˣ => (z τ : ℂ) := Units.continuous_val.comp (continuous_apply τ)
      have h2 : ∀ z : D.what₂.Tau → ℂˣ, ((‖(z τ : ℂ)‖ : ℝ) : ℂ) ≠ 0 := fun z =>
        Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (z τ).ne_zero)
      exact (h1.div (Complex.continuous_ofReal.comp h1.norm) h2).zpow₀ _ fun z =>
        Or.inl (div_ne_zero (z τ).ne_zero (h2 z))
    · refine Eq.trans ?_ (GlobalTheory.NormExact.InfExp.eq_inf c e χ hχ hf k _ _ (hab _) (hb _).1 (hb _).2)
      rw [hT _ (ha (Units.map (incA D).toMonoidHom k)).2]
      congr 3
      funext τ
      exact Units.ext ((congrArg (θ τ) (ha (Units.map (incA D).toMonoidHom k)).1).trans ((hθ τ).1 k)).symm
  intro x hx hx'
  refine (congrArg (fun u => ((χ u : Circle) : ℂ)) (hT x hx)).trans ((key _).trans ?_)
  refine Finset.prod_eq_single τ₀ (fun τ _ hτ => ?_) (fun h => absurd (Finset.mem_univ _) h)
  have : ((Units.map ((θ τ).comp (infPart D)).toMonoidHom x : ℂˣ) : ℂ) = 1 := hx' τ hτ
  rw [this, norm_one, Complex.ofReal_one, div_one, one_zpow]

end GlobalTheory.NormExact.InfExp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumDiagonalIntegralRationalHeisenberg
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open scoped FourierTransform

noncomputable section
namespace GlobalTheory.ThetaRatSum
open MeasureTheory GroundTheory.Automorphic.GJMatrix

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem char_eq (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (x : AF F) :
    ψ x = (GroundTheory.Global.adelicChar F x : ℂ) := GlobalTheory.T.standardTraceAdelicAddChar_apply_eq_adelicChar F ψ hψ x

theorem glue_integral : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ H : (κ → AF F) → ℂ,
    (Integrable (fun p => H (GlobalTheory.DiagForm.glue p)) (GlobalTheory.DiagForm.mu F κ) ↔ Integrable H (adeleMeasurePi F)) ∧
    ∫ p, H (GlobalTheory.DiagForm.glue p) ∂(GlobalTheory.DiagForm.mu F κ) = c₀ * ∫ t, H t ∂(adeleMeasurePi F) := GlobalTheory.T.integral_diagonalCoords_eq_pos_mul_adeleHaar F κ

theorem shift_mem {φ : (κ ⊕ κ → AF F) → ℂ} (hφ : φ ∈ schA F (κ ⊕ κ)) (u : κ → AF F) :
    (fun t : κ → AF F => φ (Sum.elim (t + u) t)) ∈ schwartzBruhatPi F κ := GlobalTheory.T.adelicSchwartz_restrict_translated_diagonal_mem F κ φ hφ u

theorem schA_le (ι : Type) [Fintype ι] : schA F ι ≤ schwartzBruhatPi F ι := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, g, hg, rfl⟩
  have e : pureA F f g = schwartzBruhatTensorPi f g := rfl
  rw [e]
  exact schwartzBruhatTensorPi_mem f ((mem_finiteSchwartzBruhatPi F).2 ⟨hg.1, hg.2⟩)

theorem summable_four {φ : (κ ⊕ κ → AF F) → ℂ} (hφ : φ ∈ schA F (κ ⊕ κ)) :
    Summable fun uv : (κ → F) × (κ → F) => ‖adelicFourierPi F
      (fun t : κ → AF F => φ (Sum.elim (t + fun i => algebraMap F (AF F) (uv.1 i)) t))
      (fun i => algebraMap F (AF F) (uv.2 i))‖ := GlobalTheory.T.summable_partialFourier_adelicSchwartz_rationalPairs F κ φ hφ

abbrev rv (u : κ → F) : κ → AF F := fun i => algebraMap F (AF F) (u i)

theorem dot_elim_left (a b : κ → AF F) : Sum.elim a a ⬝ᵥ Sum.elim b 0 = ∑ i, a i * b i := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem dot_elim_rat (u v : κ → F) :
    Sum.elim (rv u) 0 ⬝ᵥ Sum.elim (rv v) (0 : κ → AF F) = algebraMap F (AF F) (u ⬝ᵥ v) := by
  simp [dotProduct, Fintype.sum_sum_type, rv, map_sum, map_mul]

theorem term_eq (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {c₀ : ℝ}
    (hB : ∀ H : (κ → AF F) → ℂ,
      (Integrable (fun p => H (GlobalTheory.DiagForm.glue p)) (GlobalTheory.DiagForm.mu F κ) ↔ Integrable H (adeleMeasurePi F)) ∧
      ∫ p, H (GlobalTheory.DiagForm.glue p) ∂(GlobalTheory.DiagForm.mu F κ) = c₀ * ∫ t, H t ∂(adeleMeasurePi F))
    {φ : (κ ⊕ κ → AF F) → ℂ} (hφ : φ ∈ schA F (κ ⊕ κ)) (u v : κ → F) :
    GlobalTheory.DiagForm.lDiag F κ (schr ψ (Sum.elim (rv u) 0, Sum.elim (rv v) 0) φ) =
      c₀ * adelicFourierPi F (fun t : κ → AF F => φ (Sum.elim (t + rv u) t)) (rv v) := by
  set H : (κ → AF F) → ℂ := fun t => φ (Sum.elim (t + rv u) t) *
    (GroundTheory.Global.adelicChar F (∑ i, t i * rv v i) : ℂ) with hH
  have hint : Integrable H (adeleMeasurePi F) :=
    integrable_mul_adelicChar_pi (integrable_of_mem_schwartzBruhatPi (shift_mem hφ _)) _
  have key : GlobalTheory.DiagForm.resD F κ (schr ψ (Sum.elim (rv u) 0, Sum.elim (rv v) 0) φ) =
      fun p => H (GlobalTheory.DiagForm.glue p) := by
    funext p
    show ψ (Sum.elim (GlobalTheory.DiagForm.glue p) (GlobalTheory.DiagForm.glue p) ⬝ᵥ Sum.elim (rv v) 0 +
        ⅟(2 : AF F) * (Sum.elim (rv u) 0 ⬝ᵥ Sum.elim (rv v) 0)) *
        φ (Sum.elim (GlobalTheory.DiagForm.glue p) (GlobalTheory.DiagForm.glue p) + Sum.elim (rv u) 0) = _
    have h2 : ⅟(2 : AF F) * (Sum.elim (rv u) 0 ⬝ᵥ Sum.elim (rv v) (0 : κ → AF F)) =
        algebraMap F (AF F) (⅟(2 : F) * (u ⬝ᵥ v)) := by
      rw [dot_elim_rat, map_mul]
      congr 1
    have h3 : Sum.elim (GlobalTheory.DiagForm.glue p) (GlobalTheory.DiagForm.glue p) + Sum.elim (rv u) 0 =
        Sum.elim (GlobalTheory.DiagForm.glue p + rv u) (GlobalTheory.DiagForm.glue p) := by
      funext i; cases i <;> simp
    rw [dot_elim_left, h2, AddChar.map_add_eq_mul, hψ.2.1, mul_one, h3, char_eq ψ hψ, hH, mul_comm]
  rw [GlobalTheory.DiagForm.lDiag, LinearMap.comp_apply, key,
    GlobalTheory.DiagForm.Lext_apply _ (((hB H).1).2 hint), (hB H).2, adelicFourierPi]

theorem hasSum_lDiag_schr_rat : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ], ∃ c : ℂ, c ≠ 0 ∧ ∀ φ ∈ schA F (κ ⊕ κ),
      HasSum (fun uv : (κ → F) × (κ → F) => GlobalTheory.DiagForm.lDiag F κ (schr ψ
        (Sum.elim (fun i => algebraMap F (AF F) (uv.1 i)) 0, Sum.elim (fun i => algebraMap F (AF F) (uv.2 i)) 0) φ))
        (c * thetaSum F φ) := by
  intro F _ _ ψ hψ κ _
  obtain ⟨c₀, hc₀, hB⟩ := glue_integral (F := F) (κ := κ)
  refine ⟨(c₀ : ℂ), by exact_mod_cast hc₀.ne', fun φ hφ => ?_⟩
  set f : (κ → F) → (κ → AF F) → ℂ := fun u t => φ (Sum.elim (t + rv u) t) with hf
  have hT : (fun uv : (κ → F) × (κ → F) => GlobalTheory.DiagForm.lDiag F κ (schr ψ
        (Sum.elim (fun i => algebraMap F (AF F) (uv.1 i)) 0, Sum.elim (fun i => algebraMap F (AF F) (uv.2 i)) 0) φ)) =
      fun uv => (c₀ : ℂ) * adelicFourierPi F (f uv.1) (rv uv.2) :=
    funext fun uv => term_eq ψ hψ hB hφ uv.1 uv.2
  rw [hT]
  have hs : Summable fun uv : (κ → F) × (κ → F) => (c₀ : ℂ) * adelicFourierPi F (f uv.1) (rv uv.2) :=
    (summable_four hφ).of_norm.mul_left _
  have hP : ∀ u : κ → F, HasSum (fun v => (c₀ : ℂ) * adelicFourierPi F (f u) (rv v))
      ((c₀ : ℂ) * ∑' η : κ → F, φ (Sum.elim (rv η + rv u) (rv η))) := by
    intro u
    obtain ⟨-, h2, h3⟩ := poisson_of_mem_schwartzBruhatPi (shift_mem hφ (rv u))
    refine HasSum.mul_left _ ?_
    have e := h2.of_norm.hasSum
    rw [← h3] at e
    exact e
  have hθ : HasSum (fun uη : (κ → F) × (κ → F) => φ (Sum.elim (rv uη.2 + rv uη.1) (rv uη.2))) (thetaSum F φ) := by
    let e : (κ → F) × (κ → F) ≃ (κ ⊕ κ → F) :=
      { toFun := fun uη => Sum.elim (uη.2 + uη.1) uη.2
        invFun := fun ξ => (ξ ∘ Sum.inl - ξ ∘ Sum.inr, ξ ∘ Sum.inr)
        left_inv := fun uη => by ext i <;> simp
        right_inv := fun ξ => by funext i; cases i <;> simp }
    obtain ⟨h1, -, -⟩ := poisson_of_mem_schwartzBruhatPi (schA_le (F := F) (κ ⊕ κ) hφ)
    have h := h1.of_norm.hasSum
    rw [← e.hasSum_iff] at h
    have hfe : (fun uη : (κ → F) × (κ → F) => φ (Sum.elim (rv uη.2 + rv uη.1) (rv uη.2))) =
        (fun ξ : κ ⊕ κ → F => φ fun i => algebraMap F (AF F) (ξ i)) ∘ e := by
      funext uη
      simp only [Function.comp_apply]
      congr 1
      funext i; cases i <;> simp [e, rv, map_add]
    rw [hfe]
    exact h
  have h4 : HasSum (fun u : κ → F => (c₀ : ℂ) * ∑' η : κ → F, φ (Sum.elim (rv η + rv u) (rv η)))
      ((c₀ : ℂ) * thetaSum F φ) :=
    (hθ.prod_fiberwise fun u => (hθ.summable.prod_factor u).hasSum).mul_left _
  have h5 := hs.hasSum.prod_fiberwise hP
  rw [← h5.unique h4]
  exact hs.hasSum

end GlobalTheory.ThetaRatSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantFormVanishesLagrangianTest
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.InertLagUniq

open GlobalTheory.LatVac GlobalTheory.InertVacLag

theorem finrank_le_of_isotropic {K : Type} [Field K] {κ : Type} [Fintype κ] (Λ : Submodule K ((κ → K) × (κ → K)))
    (h : ∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) : Module.finrank K Λ ≤ Fintype.card κ := by
  classical
  let B : LinearMap.BilinForm K ((κ → K) × (κ → K)) :=
    LinearMap.mk₂ K (fun a b => a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2)
      (fun a a' b => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
      (fun c a b => by simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
      (fun a b b' => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
      (fun c a b => by simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
  have hB : ∀ a b, B a b = a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2 := fun _ _ => rfl
  have hker : LinearMap.ker B = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    have ha' : ∀ b, B a b = 0 := fun b => by rw [LinearMap.mem_ker.1 ha]; rfl
    refine (Submodule.mem_bot _).2 (Prod.ext (funext fun k => ?_) (funext fun k => ?_))
    · have := ha' (0, Pi.single k 1)
      simpa [hB] using this
    · have := ha' (Pi.single k 1, 0)
      simpa [hB] using this
  have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := B) Λ
  rw [hker, inf_bot_eq, finrank_bot, add_zero, Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at h1
  have h2 : Λ ≤ B.orthogonal Λ := fun b hb a ha => by
    show B a b = 0
    rw [hB, h a ha b hb, sub_self]
  have h3 := Submodule.finrank_mono h2
  omega

theorem finrank_eq_of_isotropic {K : Type} [Field K] {κ : Type} [Fintype κ] (Λ Λ' : Submodule K ((κ → K) × (κ → K)))
    (h : ∀ a ∈ Λ, ∀ b ∈ Λ, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) (h' : ∀ a ∈ Λ', ∀ b ∈ Λ', a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2)
    (hs : Λ ⊔ Λ' = ⊤) : Module.finrank K Λ = Fintype.card κ := by
  have h1 := finrank_le_of_isotropic Λ h
  have h2 := finrank_le_of_isotropic Λ' h'
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq Λ Λ'
  rw [hs, finrank_top, Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at h3
  omega

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_psiAt (ψ : AddChar (AF F) ℂ) (v : Pl F) (h : PsiUnr ψ v) : Continuous (psiAt ψ v) := by
  have hker : ∀ y ∈ v.adicCompletionIntegers F, psiAt ψ v y = 1 := fun y hy => by
    have := (h 1).2 (one_mem _) y hy
    rwa [one_mul] at this
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  rw [← map_add_left_nhds_zero, Filter.eventually_map]
  filter_upwards [hO.mem_nhds (zero_mem _)] with s hs
  rw [AddChar.map_add_eq_mul, hker s hs, mul_one]

theorem psiAt_ne_one (ψ : AddChar (AF F) ℂ) (v : Pl F) (h : PsiUnr ψ v) : psiAt ψ v ≠ 1 := by
  intro h1
  have hall : ∀ x : Fv F v, x ∈ v.adicCompletionIntegers F := fun x => (h x).1 fun y _ => by
    rw [← psiAt_apply, h1]; rfl
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have h2 := hall (algebraMap F (Fv F v) π⁻¹)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h2
  erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h2
  rw [map_inv₀, map_inv₀, Algebra.algebraMap_self_apply, hπ, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h2
  omega

theorem liftV_one_smul {M : Type} [AddCommGroup M] [Module (AF F) M] (v : Pl F) (u : M) (hu : At (evFin F v) u) :
    liftV v (1 : Fv F v) • u = u := by
  have h := hu (1 - liftV v 1) (by rw [map_sub, map_one, evFin_liftV, sub_self])
  rw [sub_smul, one_smul] at h
  exact (sub_eq_zero.1 h).symm

theorem liftV_one_mul (v : Pl F) (x : AF F) : liftV v (1 : Fv F v) * x = liftV v (evFin F v x) := by
  have h := at_liftV v (1 : Fv F v) (x - liftV v (evFin F v x)) (by rw [map_sub, evFin_liftV, sub_self])
  have h2 := liftV_one_smul v _ (at_liftV v (evFin F v x))
  rw [smul_eq_mul] at h h2
  linear_combination h + h2

theorem liftV_one_smul_eq_zero (v : Pl F) (a : AE F E) (ha : compFin F E v a = 0) : liftV v (1 : Fv F v) • a = 0 := by
  have key : ∀ a : AE F E, liftV v (1 : Fv F v) • a = (liftV v).rTensor E (compFin F E v a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul x e =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, liftV_one_mul]
      simp [compFin]
    | add x y hx hy => rw [smul_add, hx, hy, map_add, map_add]
  rw [key, ha, map_zero]

theorem exists_map_compFin (v : Pl F) {α β : Type} (A : Matrix α β (Fv F v ⊗[F] E)) :
    ∃ C : Matrix α β (AE F E), C.map (compFin F E v) = A := by
  refine ⟨A.map ((liftV v).rTensor E), ?_⟩
  ext i j
  simp only [Matrix.map_apply]
  induction A i j using TensorProduct.induction_on with
  | zero => simp
  | tmul x e => simp [compFin, evFin_liftV]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem mul_eq_self {n d : ℕ} (v : Pl F) (u : Matrix (Fin n) (Fin d) (AE F E)) (hu : At (evFin F v) u)
    (N : Matrix (Fin d) (Fin d) (AE F E)) (hN : N.map (compFin F E v) = 1) : u * N = u := by
  have h0 : liftV v (1 : Fv F v) • (N - 1) = 0 := by
    ext i j
    refine liftV_one_smul_eq_zero v _ ?_
    have := congrFun (congrFun hN i) j
    rw [Matrix.map_apply] at this
    rw [Matrix.sub_apply, map_sub, this]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  have h1 : u * (N - 1) = 0 := by
    rw [← liftV_one_smul v u hu, Matrix.smul_mul, ← Matrix.mul_smul, h0, Matrix.mul_zero]
  rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h1

theorem at_mul {α β γ : Type} [Fintype β] (v : Pl F) (u : Matrix α β (AE F E)) (hu : At (evFin F v) u)
    (A : Matrix β γ (AE F E)) : At (evFin F v) (u * A) := fun t ht => by
  rw [← Matrix.smul_mul, hu t ht, Matrix.zero_mul]

theorem exists_compl (σ : E →ₐ[F] E) {d m : ℕ} (W : Spc F E d) (v : Pl F) (C : Matrix (Fin d) (Fin m) (AE F E))
    (hC : IsLagrAt σ W v C) (n : ℕ) : ∃ C' : Matrix (Fin d) (Fin m) (AE F E), IsLagrAt σ W v C' ∧
      ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) u → ∃ x ∈ lagAt v C, ∃ y ∈ lagAt v C', u = x + y := by
  obtain ⟨h0, Cx, M, hx, h1, h2⟩ := hC
  obtain ⟨C', hC'⟩ := exists_map_compFin v Cx
  obtain ⟨M₁, hM₁⟩ := exists_map_compFin v M.toRows₁
  obtain ⟨M₂, hM₂⟩ := exists_map_compFin v M.toRows₂
  rw [← Matrix.fromRows_toRows M] at h1 h2
  rw [Matrix.fromCols_mul_fromRows] at h1
  rw [Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at h2
  refine ⟨C', ⟨by rw [hC']; exact hx, _, Matrix.fromRows M.toRows₂ M.toRows₁, h0, ?_, ?_⟩, fun u hu => ?_⟩
  · rw [hC', Matrix.fromCols_mul_fromRows, add_comm, h1]
  · rw [hC', Matrix.fromRows_mul_fromCols, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2, Matrix.fromBlocks_one]
  · have hN : ((C * M₁ + C' * M₂)ᵀ).map (compFin F E v) = 1 := by
      rw [Matrix.transpose_map, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, hC', hM₁, hM₂, h1,
        Matrix.transpose_one]
    refine ⟨u * M₁ᵀ * Cᵀ, ⟨at_mul v _ (at_mul v u hu _) _, _, rfl⟩, u * M₂ᵀ * C'ᵀ,
      ⟨at_mul v _ (at_mul v u hu _) _, _, rfl⟩, ?_⟩
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, ← Matrix.transpose_mul, ← Matrix.transpose_mul,
      ← Matrix.transpose_add, mul_eq_self v u hu _ hN]

theorem exists_at_locCo {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (v : Pl F) (p : (κ → Fv F v) × (κ → Fv F v)) :
    ∃ u : W, At (evFin F v) u ∧ locCo co v u = p := by
  refine ⟨co.e.symm (fun k => liftV v (p.1 k), fun k => liftV v (p.2 k)), ?_, ?_⟩
  · intro r hr
    rw [← LinearEquiv.map_smul]
    have h0 : r • ((fun k => liftV v (p.1 k), fun k => liftV v (p.2 k)) : (κ → AF F) × (κ → AF F)) = 0 :=
      Prod.ext (funext fun k => at_liftV v (p.1 k) r hr) (funext fun k => at_liftV v (p.2 k) r hr)
    rw [h0, map_zero]
  · show ((fun k => evFin F v ((co.e _).1 k)), fun k => evFin F v ((co.e _).2 k)) = p
    rw [LinearEquiv.apply_symm_apply]
    exact Prod.ext (funext fun k => evFin_liftV v _) (funext fun k => evFin_liftV v _)

variable {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def lagCo (M : Model σ X W) (v : Pl F) {m : ℕ} (C : Matrix (Fin d) (Fin m) (AE F E)) :
    Submodule (Fv F v) ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) where
  carrier := locCo M.co v '' lagAt v C
  zero_mem' := ⟨0, ⟨fun u _ => smul_zero u, 0, by simp⟩, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨_, ⟨hx, z, rfl⟩, rfl⟩ ⟨_, ⟨hy, z', rfl⟩, rfl⟩
    exact ⟨_, ⟨fun u hu => by rw [smul_add, hx u hu, hy u hu, add_zero], z + z', by rw [Matrix.add_mul]⟩, map_add _ _ _⟩
  smul_mem' := by
    rintro a _ ⟨_, ⟨hx, z, rfl⟩, rfl⟩
    refine ⟨liftV v a • (z * Cᵀ), ⟨fun u hu => by rw [smul_comm, hx u hu, smul_zero], liftV v a • z,
      by rw [Matrix.smul_mul]⟩, ?_⟩
    ext k <;> simp [locCo, evFin_liftV, -Matrix.smul_mul]

theorem lagCo_isotropic (M : Model σ X W) (v : Pl F) {m : ℕ} (C : Matrix (Fin d) (Fin m) (AE F E))
    (hC : IsLagrAt σ W v C) : ∀ a ∈ lagCo M v C, ∀ b ∈ lagCo M v C, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2 := by
  rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
  have h0 := GlobalTheory.T.symplecticForm_eq_zero_of_lagrangianAtPlace σ X.J W v C hC (-1) u u' hu hu'
  rw [M.co.form] at h0
  have h1 := congrArg (evFin F v) h0
  rw [← sub_eq_zero]
  simpa [locCo, dotProduct, map_sum, map_mul, map_sub] using h1

theorem finrank_lagCo (M : Model σ X W) (v : Pl F) {m : ℕ} (C : Matrix (Fin d) (Fin m) (AE F E))
    (hC : IsLagrAt σ W v C) : Module.finrank (Fv F v) (lagCo M v C) = Fintype.card (Fin n × Fin d) := by
  obtain ⟨C', hC', hdec⟩ := exists_compl σ W v C hC n
  refine finrank_eq_of_isotropic _ (lagCo M v C') (lagCo_isotropic M v C hC) (lagCo_isotropic M v C' hC') ?_
  rw [eq_top_iff]
  intro p _
  obtain ⟨u, hu, rfl⟩ := exists_at_locCo M.co v p
  obtain ⟨x, hx, y, hy, rfl⟩ := hdec u hu
  rw [map_add]
  exact Submodule.add_mem_sup ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩

theorem exists_test : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F), PsiUnr ψ v →
    ∀ (m : ℕ) (C : Matrix (Fin d) (Fin m) (AE F E)), GlobalTheory.InertVacLag.IsLagrAt σ W v C →
    ∃ φ₀ ∈ SB (Fin n × Fin d → Fv F v), ∀ l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      GlobalTheory.InertVacLag.HeisInv M ψ v C l → l φ₀ = 0 → ∀ φ ∈ SB (Fin n × Fin d → Fv F v), l φ = 0 := by
  intro F E _ _ _ _ _ σ n d X W M ψ v hψ m C hC
  have hc := continuous_psiAt ψ v hψ
  have hinv : ∀ l, HeisInv M ψ v C l → ∀ w ∈ lagCo M v C, ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      l (schr (psiAt ψ v) w φ) = l φ := by
    rintro l hl _ ⟨u, hu, rfl⟩ φ hφ
    exact hl u hu φ hφ _ (GlobalTheory.SchrSBFin.schr_mem_SB v _ hc _ φ hφ) (GlobalTheory.VacBridge.rho_acts_locCo M.co ψ v u hu.1 φ)
  by_cases hex : ∃ l₂, HeisInv M ψ v C l₂ ∧ ∃ φ ∈ SB (Fin n × Fin d → Fv F v), l₂ φ ≠ 0
  · obtain ⟨l₂, hl₂, φ₀, hφ₀, hne⟩ := hex
    refine ⟨φ₀, hφ₀, fun l hl h0 φ hφ => ?_⟩
    obtain ⟨c, hcl⟩ := GlobalTheory.T.lagrangian_invariant_forms_proportional_finitePlace F v (psiAt ψ v) hc (psiAt_ne_one ψ v hψ) _ (lagCo M v C) (lagCo_isotropic M v C hC)
      (finrank_lagCo M v C hC) l l₂ (hinv l hl) (hinv l₂ hl₂) ⟨φ₀, hφ₀, hne⟩
    have hc0 : c = 0 := (mul_eq_zero.1 ((hcl φ₀ hφ₀).symm.trans h0)).resolve_right hne
    rw [hcl φ hφ, hc0, zero_mul]
  · refine ⟨0, zero_mem _, fun l hl _ φ hφ => ?_⟩
    by_contra hne
    exact hex ⟨l, hl, φ, hφ, hne⟩

end GlobalTheory.InertLagUniq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentBlockUnipotentIdentityStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_block_unipotent_identity : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) (β : Type) [Fintype β] [DecidableEq β]
    (J : Matrix β β A), IsUnit J.det → ∀ e : R, e * e = e → ∀ g k : UG c J,
    (1 - e) • ((g.1.1 : Matrix β β A) - 1) = 0 → (1 - e) • ((k.1.1 : Matrix β β A) - 1) = 0 →
    ∀ a b : Matrix β β A, e • a = a → e • b = b →
    a * (1 - (k.1.1 : Matrix β β A)) = e • (1 : Matrix β β A) → (1 - (k.1.1 : Matrix β β A)) * a = e • (1 : Matrix β β A) →
    b * (1 - ((g⁻¹ * k).1.1 : Matrix β β A)) = e • (1 : Matrix β β A) →
    (1 - ((g⁻¹ * k).1.1 : Matrix β β A)) * b = e • (1 : Matrix β β A) →
    ∀ gd kd : UG c (dbl J), (gd.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) = Matrix.fromBlocks (g.1.1 : Matrix β β A) 0 0 1 →
    (kd.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) = Matrix.fromBlocks (k.1.1 : Matrix β β A) 0 0 1 →
    ∃ (p₁ p₂ : UG c (dbl J)) (t₁ t₂ : GL β A), (1 - e) • ((p₁.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 ∧
      (1 - e) • ((p₂.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) - 1) = 0 ∧
      (p₁.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) * diagCols β = diagCols β * t₁.val ∧
      (p₂.1.1 : Matrix (β ⊕ β) (β ⊕ β) A) * diagCols β = diagCols β * t₂.val ∧ gd = kd * p₁ * kd⁻¹ * p₂ := by
  first | exact @GlobalTheory.SiegelDiagDecomp.diag_decomp | exact GlobalTheory.SiegelDiagDecomp.diag_decomp | (intros; apply GlobalTheory.SiegelDiagDecomp.diag_decomp <;> assumption)
end

