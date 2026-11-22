import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedHecke
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0113
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.Bundle0005
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0003
import Formalism.GaussJetBounds.GaussJetProofs.LogarithmWeightComparison
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.Bundle0002
import Formalism.GaussJetBounds.GaussJetProofs.Bundle0008
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetDegreeBound.JetTdegEqDegree
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralOrbitSeries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0003
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.Bundle0002
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
import Formalism.LocalRingCardinality.FactDelDualNabla

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinTypInvariantFormOfIsotIn
section
open Formalism.BasicNotions Formalism.L2 Formalism.L2.NG Formalism.AUTREP Formalism.IndefR.principalLevelFrame

namespace GlobalTheory

theorem finTyp_invariant_form_of_isotIn : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (B : A → A → ℂ), (∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z) → (∀ x ∈ C, ∀ y ∈ C, B x y = starRingEnd ℂ (B y x)) → (∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) → (∀ h, ∀ x ∈ C, ρ h x ∈ C) → (∀ h, ∀ x ∈ C, ∀ y ∈ C, B (ρ h x) (ρ h y) = B x y) → ∀ π : FinTyp D.host.E n, isotIn (D := D) ρ C π ≠ ⊥ → ∃ B' : π.S → π.S → ℂ, (∀ x y z (c : ℂ), B' x (y + c • z) = B' x y + c * B' x z) ∧ (∀ x y, B' x y = starRingEnd ℂ (B' y x)) ∧ (∀ x, x ≠ 0 → 0 < (B' x x).re) ∧ ∀ h (x y x' y' : π.S), (x' : GAf D.host.E n → ℂ) = rt D.host.E n h x → (y' : GAf D.host.E n → ℂ) = rt D.host.E n h y → B' x' y' = B' x y := by
  intro D n A _ _ ρ C B hlin hherm hpos _hstab hinv π hne

  obtain ⟨Φ, ⟨hΦe, hΦC⟩, hΦne⟩ : ∃ Φ : π.S →ₗ[ℂ] A, (IsEqvA ρ π Φ ∧ LinearMap.range Φ ≤ C) ∧ LinearMap.range Φ ≠ ⊥ := by
    by_contra hcon
    push_neg at hcon
    apply hne
    unfold isotIn
    refine iSup_eq_bot.2 fun Φ => iSup_eq_bot.2 fun hΦ => hcon Φ hΦ
  have hmemC : ∀ x : π.S, Φ x ∈ C := fun x => hΦC (LinearMap.mem_range_self Φ x)

  let S' : Submodule ℂ (GAf D.host.E n → ℂ) := (LinearMap.ker Φ).map π.S.subtype
  have hS'le : S' ≤ π.S := by
    rintro f ⟨k, _, rfl⟩
    exact k.2
  have hS'st : ∀ h, ∀ f ∈ S', rt D.host.E n h f ∈ S' := by
    rintro h f ⟨k, hk, rfl⟩
    refine ⟨⟨rt D.host.E n h k, π.stable h k k.2⟩, ?_, rfl⟩
    have hk' : Φ k = 0 := hk
    show Φ _ = 0
    rw [hΦe h k, hk', map_zero]
  have hinj : ∀ x : π.S, Φ x = 0 → x = 0 := by
    intro x hx
    rcases π.irr S' hS'le hS'st with h0 | hall
    · have : (x : GAf D.host.E n → ℂ) ∈ S' := ⟨x, hx, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact Subtype.ext this
    · exfalso
      apply hΦne
      rw [eq_bot_iff]
      rintro a ⟨y, rfl⟩
      have : (y : GAf D.host.E n → ℂ) ∈ S' := by rw [hall]; exact y.2
      obtain ⟨k, hk, hky⟩ := this
      have : k = y := Subtype.ext hky
      subst this
      have hk' : Φ k = 0 := hk
      exact (Submodule.mem_bot ℂ).2 hk'
  refine ⟨fun x y => B (Φ x) (Φ y), ?_, ?_, ?_, ?_⟩
  · intro x y z c
    simp only [map_add, map_smul]
    exact hlin _ (hmemC x) _ (hmemC y) _ (hmemC z) c
  · intro x y
    exact hherm _ (hmemC x) _ (hmemC y)
  · intro x hx
    exact hpos _ (hmemC x) (fun h0 => hx (hinj x h0))
  · intro h x y x' y' hx hy
    have ex : x' = ⟨rt D.host.E n h x, π.stable h x x.2⟩ := Subtype.ext hx
    have ey : y' = ⟨rt D.host.E n h y, π.stable h y y.2⟩ := Subtype.ext hy
    simp only
    rw [ex, ey, hΦe h x, hΦe h y]
    exact hinv h _ (hmemC x) _ (hmemC y)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharFiniteOrderUnitIdele
section
noncomputable section

namespace GlobalTheory.HeckeFin

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

variable {L : Type} [Field L] [NumberField L]

theorem circle_pow (ψ : Ideles L →* Circle) (hψ : Continuous ψ) :
    ∃ m : ℕ, 0 < m ∧ ∀ u : Ideles L, IsFinIdele u → u ∈ unitIdl L → ψ u ^ m = 1 := by
  obtain ⟨-, -, -, m, hm, h⟩ := GlobalTheory.CharFin.finite_order_of_small (R := AdeleRing (𝓞 L) L)
    (RingHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)) (RingHom.snd _ _) id continuous_id (fun _ => rfl)
    (GlobalTheory.UnUnitCmp.Val.intFin L) (fun W hW => GlobalTheory.AdLat.OpenLat.exists_nsmul_adele L W hW)
    GlobalTheory.UnUnitCmp.Val.finite_quot ψ hψ
  exact ⟨m, hm, fun u h1 h2 => h u ⟨funext h1, fun v => (h2 v).le, fun v => ((unitIdl L).inv_mem h2 v).le⟩⟩

theorem norm_ne (χ : HChar L) (x : Ideles L) : ‖((χ.1 x : ℂˣ) : ℂ)‖ ≠ 0 :=
  norm_ne_zero_iff.2 (Units.ne_zero _)

theorem continuous_norm_val (χ : HChar L) : Continuous fun x : Ideles L => ‖((χ.1 x : ℂˣ) : ℂ)‖ :=
  (Units.continuous_val.comp χ.2.1).norm

def twist (χ : HChar L) (c : ℝ) : Ideles L →* Circle where
  toFun x := Circle.exp (c * Real.log ‖((χ.1 x : ℂˣ) : ℂ)‖)
  map_one' := by simp
  map_mul' x y := by
    rw [χ.1.map_mul, Units.val_mul, norm_mul, Real.log_mul (norm_ne χ x) (norm_ne χ y), mul_add, Circle.exp_add]

theorem continuous_twist (χ : HChar L) (c : ℝ) : Continuous (twist χ c) :=
  Circle.exp.continuous.comp (continuous_const.mul ((continuous_norm_val χ).log (norm_ne χ)))

theorem norm_eq_one (χ : HChar L) (a : Ideles L) (h1 : IsFinIdele a) (h2 : a ∈ unitIdl L) :
    ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := by
  by_contra hne
  have ht : Real.log ‖((χ.1 a : ℂˣ) : ℂ)‖ ≠ 0 := by
    intro h0
    rcases Real.log_eq_zero.1 h0 with h | h | h
    · exact norm_ne χ a h
    · exact hne h
    · linarith [norm_nonneg ((χ.1 a : ℂˣ) : ℂ)]
  set t := Real.log ‖((χ.1 a : ℂˣ) : ℂ)‖ with htdef
  obtain ⟨m, hm, h⟩ := circle_pow (twist χ (2 * Real.pi * √2 / t)) (continuous_twist χ _)
  have e := h a h1 h2
  have e1 : twist χ (2 * Real.pi * √2 / t) a = Circle.exp (2 * Real.pi * √2) := by
    change Circle.exp (2 * Real.pi * √2 / t * Real.log ‖((χ.1 a : ℂˣ) : ℂ)‖) = _
    rw [← htdef, div_mul_cancel₀ _ ht]
  rw [e1, ← Circle.exp_nsmul] at e
  have e2 := congrArg (fun z : Circle => (z : ℂ)) e
  simp only [Circle.coe_exp, Circle.coe_one] at e2
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 e2
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e3 : (m : ℂ) * (√2 : ℝ) = n := by
    have : ((m : ℂ) * (√2 : ℝ)) * (2 * Real.pi * Complex.I) = n * (2 * Real.pi * Complex.I) := by
      rw [← hn]; push_cast; simp only [nsmul_eq_mul]; push_cast; ring
    exact mul_right_cancel₀ (by simp [hpi, Complex.I_ne_zero]) this
  have e4 : (m : ℝ) * √2 = n := by exact_mod_cast e3
  exact (irrational_sqrt_two.natCast_mul hm.ne').ne_int n e4

def unitPart (χ : HChar L) : Ideles L →* Circle where
  toFun x := ⟨((χ.1 x : ℂˣ) : ℂ) / ‖((χ.1 x : ℂˣ) : ℂ)‖, by
    simp [Submonoid.unitSphere, norm_ne χ x]⟩
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    change ((χ.1 (x * y) : ℂˣ) : ℂ) / ‖((χ.1 (x * y) : ℂˣ) : ℂ)‖ =
      (((χ.1 x : ℂˣ) : ℂ) / ‖((χ.1 x : ℂˣ) : ℂ)‖) * (((χ.1 y : ℂˣ) : ℂ) / ‖((χ.1 y : ℂˣ) : ℂ)‖)
    rw [χ.1.map_mul, Units.val_mul, norm_mul]
    push_cast
    rw [mul_div_mul_comm]

theorem continuous_unitPart (χ : HChar L) : Continuous (unitPart χ) := by
  refine Continuous.subtype_mk ?_ _
  exact (Units.continuous_val.comp χ.2.1).div (Complex.continuous_ofReal.comp (continuous_norm_val χ))
    (fun x => by simpa using norm_ne χ x)

theorem finite_order : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (a : Ideles L), IsFinIdele a →
    (∀ v, Valued.v ((a : AdeleRing (𝓞 L) L).2 v) = 1) → ∃ n : ℕ, 0 < n ∧ χ.1 a ^ n = 1 := by
  intro L _ _ χ a h1 h2
  have h2' : a ∈ unitIdl L := h2
  obtain ⟨m, hm, h⟩ := circle_pow (unitPart χ) (continuous_unitPart χ)
  refine ⟨m, hm, Units.ext ?_⟩
  have e := congrArg (fun z : Circle => (z : ℂ)) (h a h1 h2')
  have e1 : ((unitPart χ a : Circle) : ℂ) = ((χ.1 a : ℂˣ) : ℂ) := by
    change ((χ.1 a : ℂˣ) : ℂ) / ‖((χ.1 a : ℂˣ) : ℂ)‖ = _
    rw [norm_eq_one χ a h1 h2']; simp
  simpa [e1] using e

end GlobalTheory.HeckeFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicPairAdditiveCoordsLinearForms
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open MvPowerSeries
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)
noncomputable section

namespace GlobalTheory.KerStd.HypOrbit

open Formalism.InvariantFactorPaths.G7 (lgF at1)

theorem lg_flin {p : ℕ} [Fact p.Prime] (hl : 2 ≤ p) {τ m : Type} [Fintype m] (c : m → ℂ_[p]) (v : m → MvPowerSeries τ ℂ_[p])
    (hv : ∀ k, constantCoeff (v k) = 0) :
    PowerSeries.subst (Formalism.L2.Th1.C.flin (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) c v) (lgF ℂ_[p] p) =
      ∑ k, C (c k) * PowerSeries.subst (v k) (lgF ℂ_[p] p) := by
  unfold Formalism.L2.Th1.C.flin
  have hA : constantCoeff (∑ k, C (c k) * PowerSeries.subst (v k) (lgF ℂ_[p] p)) = 0 := by
    simp only [map_sum, map_mul, constantCoeff_C]
    exact Finset.sum_eq_zero fun k _ => by
      rw [PowerSeries.constantCoeff_subst_eq_zero (hv k) _ (Formalism.L2.Th1.D.Pair.cc_lgF hl), mul_zero]
  rw [← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (Formalism.L2.Th1.D.expSpec ℂ_[p] p hl).1)
    (PowerSeries.HasSubst.of_constantCoeff_zero hA), (Formalism.L2.Th1.D.expSpec ℂ_[p] p hl).2.1,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hA)]

theorem cc_flin {p : ℕ} [Fact p.Prime] (hl : 2 ≤ p) {τ m : Type} [Fintype m] (c : m → ℂ_[p]) (v : m → MvPowerSeries τ ℂ_[p])
    (hv : ∀ k, constantCoeff (v k) = 0) :
    constantCoeff (Formalism.L2.Th1.C.flin (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) c v) = 0 := by
  unfold Formalism.L2.Th1.C.flin
  have hA : constantCoeff (∑ k, C (c k) * PowerSeries.subst (v k) (lgF ℂ_[p] p)) = 0 := by
    simp only [map_sum, map_mul, constantCoeff_C]
    exact Finset.sum_eq_zero fun k _ => by
      rw [PowerSeries.constantCoeff_subst_eq_zero (hv k) _ (Formalism.L2.Th1.D.Pair.cc_lgF hl), mul_zero]
  exact PowerSeries.constantCoeff_subst_eq_zero hA _ (Formalism.L2.Th1.D.expSpec ℂ_[p] p hl).1

theorem hypZ_of_inHyp : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {M N N' r : ℕ} (eA : Fin M ≃ R × Fin N)
    (f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p) (Θ : MvPowerSeries (Fin r) ℂ_[p]), subst (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (Formalism.L2.Th1.D.thetaInZ (d := nP D p) p (MaximalUnramifiedExtension p).subtype σ om oms
        (subst (fun x : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' =>
            (X (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2) :
              MvPowerSeries (Bool × Fin (nP D p / 2) × Fin M × Fin N') ℂ_[p]))
          (Formalism.L2.Th1.Top.inHyp p f f'
            (subst (fun i : Fin r => (Formalism.InvariantFactorPaths.G7.at1 i (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p])) Θ)))) =
      subst (hypZ D p σ om oms R f f') Θ := by
  intro D p _ hp σ om oms R M N N' r eA f f' Θ
  have hl : 2 ≤ p := by omega
  have hcl : PowerSeries.constantCoeff (lgF ℂ_[p] p) = 0 := Formalism.L2.Th1.D.Pair.cc_lgF hl
  have hA0 : HasSubst (fun i : Fin r => (at1 i (lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero fun i => Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero i hcl
  have hu : ∀ k : ((R × Fin (nP D p / 2)) × Fin N × Fin N') ⊕ ((R × Fin (nP D p / 2)) × Fin N × Fin N'),
      constantCoeff ((Sum.elim (fun e => (X (false, e) : MvPowerSeries (Bool × ((R × Fin (nP D p / 2)) × Fin N × Fin N')) ℂ_[p]))
        (fun e => X (true, e))) k) = 0 := by
    intro k; cases k <;> simp
  have hhc : HasSubst (Formalism.L2.Th1.E.hypCoord (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) (MaximalUnramifiedExtension p).subtype f f') :=
    hasSubst_of_constantCoeff_zero fun i => cc_flin hl _ _ hu

  have hL : ∀ i : Fin r, subst (Formalism.L2.Th1.E.hypCoord (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) (MaximalUnramifiedExtension p).subtype f f')
      (at1 i (lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p]) =
      ∑ e : (R × Fin (nP D p / 2)) × Fin N × Fin N',
        (C ((f e i : MaximalUnramifiedExtension p) : ℂ_[p]) * at1 (false, e) (lgF ℂ_[p] p) +
          C ((f' e i : MaximalUnramifiedExtension p) : ℂ_[p]) * at1 (true, e) (lgF ℂ_[p] p)) := by
    intro i
    rw [Formalism.L2.Th1.D.Pair.subst_single_var hhc]
    unfold Formalism.L2.Th1.E.hypCoord
    rw [lg_flin hl _ _ hu, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    rfl

  set ren1 := (fun x : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' =>
            (X (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2) :
              MvPowerSeries (Bool × Fin (nP D p / 2) × Fin M × Fin N') ℂ_[p])) with hren1
  set Y := (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) with hYdef
  have hR : HasSubst ren1 := hasSubst_of_constantCoeff_zero fun x => constantCoeff_X _
  have hX : HasSubst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms) :=
    hasSubst_of_constantCoeff_zero (CofactorConverse.cc_xOfZ hl _ σ om oms)
  have hY : HasSubst Y := hasSubst_of_constantCoeff_zero fun y => constantCoeff_X _
  have hRX0 : ∀ x, constantCoeff (subst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms) (ren1 x)) = 0 :=
    fun x => constantCoeff_subst_eq_zero hX (CofactorConverse.cc_xOfZ hl _ σ om oms) (constantCoeff_X _)
  have hRX : HasSubst (fun x => subst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms) (ren1 x)) :=
    hasSubst_of_constantCoeff_zero hRX0
  set W := (fun x : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' => subst Y
    (subst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms) (ren1 x))) with hWdef
  have hW : HasSubst W := hasSubst_of_constantCoeff_zero fun x =>
    constantCoeff_subst_eq_zero hY (fun y => constantCoeff_X _) (hRX0 x)
  have hcomp : ∀ g : MvPowerSeries (Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N') ℂ_[p], subst Y (subst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms)
      (subst ren1 g)) = subst W g := by
    intro g
    rw [subst_comp_subst_apply hR hX, subst_comp_subst_apply hRX hY]
  have hLf : HasSubst (fun i : Fin r => subst (Formalism.L2.Th1.E.hypCoord (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) (MaximalUnramifiedExtension p).subtype f f')
      (at1 i (lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero fun i => constantCoeff_subst_eq_zero hhc (fun i => cc_flin hl _ _ hu)
      (Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero i hcl)

  have hWx : ∀ (c : Bool) (e : (R × Fin (nP D p / 2)) × Fin N × Fin N'), subst W (at1 (c, e) (lgF ℂ_[p] p)) =
      ∑ s : ZMod (nP D p), C ((MaximalUnramifiedExtension p).subtype (Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY σ om oms (c, e.1.2) s)) *
        (X (OrbitPlaces.orbMap D p e.1.1 s, e.2.1, e.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) := by
    intro c e
    rw [Formalism.L2.Th1.D.Pair.subst_single_var hW]
    simp only [hWdef, hren1]
    rw [subst_X hX]
    have ha : PowerSeries.HasSubst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms
        (c, e.1.2, eA.symm (e.1.1, e.2.1), e.2.2)) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (CofactorConverse.cc_xOfZ hl _ σ om oms _)
    rw [← Formalism.L2.Th1.D.Pair.subst_subst1 hY ha]
    have hlog := CofactorConverse.log_xOfZ (d := nP D p) hl (MaximalUnramifiedExtension p).subtype σ om oms (eA.symm (e.1.1, e.2.1)) e.2.2 (c, e.1.2)
    simp only at hlog
    rw [hlog]
    unfold CofactorConverse.linP
    rw [← coe_substAlgHom hY]
    simp only [map_sum, map_mul]
    simp only [coe_substAlgHom hY, subst_C]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [subst_X hY]
    simp only [hYdef, Equiv.apply_symm_apply]
  have hEv : ∀ (k : Fin (nP D p / 2)) (q : OrbitPlaces.Pl D) (a : Fin N) (b : Fin N'),
      (∑ s : ZMod (nP D p), C ((MaximalUnramifiedExtension p).subtype (Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY σ om oms (false, k) s)) *
        (X (OrbitPlaces.orbMap D p q s, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) =
      linEv D p σ (oms k) q a b := by
    intro k q a b
    unfold linEv
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY
    by_cases hs : s.val % 2 = 0 <;> simp [hs]
  have hOd : ∀ (k : Fin (nP D p / 2)) (q : OrbitPlaces.Pl D) (a : Fin N) (b : Fin N'),
      (∑ s : ZMod (nP D p), C ((MaximalUnramifiedExtension p).subtype (Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY σ om oms (true, k) s)) *
        (X (OrbitPlaces.orbMap D p q s, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) =
      linOd D p σ (om k) q a b := by
    intro k q a b
    unfold linOd
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY
    by_cases hs : s.val % 2 = 0 <;> simp [hs]
  unfold Formalism.L2.Th1.D.thetaInZ Formalism.L2.Th1.Top.inHyp
  rw [hcomp, subst_comp_subst_apply hA0 hhc, subst_comp_subst_apply hLf hW]
  congr 1
  funext i
  rw [hL i]

  rw [← coe_substAlgHom hW]
  simp only [map_sum, map_add, map_mul]
  simp only [coe_substAlgHom hW, subst_C, hWx, hEv, hOd]
  rfl

end GlobalTheory.KerStd.HypOrbit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaInvolutionRealPlacePairs
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

namespace GlobalTheory.InertiaPairs

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

section HostLemmas

variable {R : Ranks} (H : Host R)

theorem sigmaOf_mul (g h : R.GG) : H.sigmaOf (g * h) = H.sigmaOf g * H.sigmaOf h := by
  unfold Host.sigmaOf
  exact map_mul _ g h

theorem sigmaOf_one : H.sigmaOf 1 = 1 := by
  unfold Host.sigmaOf
  exact map_one _

theorem galE_sigmaOf (g : R.GG) : H.galE (H.sigmaOf g) = g := by
  unfold Host.sigmaOf
  exact MulEquiv.apply_symm_apply _ _

theorem sigmaOf_sqrt_neg (g : R.GG) (h : g.1.2 = -1) : H.sigmaOf g H.sqrtMinusD = -H.sqrtMinusD := by
  have := H.galE_bE (H.sigmaOf g)
  rw [galE_sigmaOf, h] at this
  unfold Host.sqrtMinusD
  rw [this]
  simp

theorem sigmaOf_sqrt_pos (g : R.GG) (h : g.1.2 = 1) : H.sigmaOf g H.sqrtMinusD = H.sqrtMinusD := by
  have := H.galE_bE (H.sigmaOf g)
  rw [galE_sigmaOf, h] at this
  unfold Host.sqrtMinusD
  rw [this]
  simp

theorem sqrt_sq : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
  exact H.sqd_sq

theorem emb_sigmaOf (g h : R.GG) (x : H.E) : H.emb g (H.sigmaOf h x) = H.emb (g * h) x := by
  unfold Host.emb
  rw [sigmaOf_mul]
  rfl

end HostLemmas

end GlobalTheory.InertiaPairs

namespace GlobalTheory.InertiaPairs

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Polynomial
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

section KurLemmas

variable {p : ℕ} [Fact p.Prime]

theorem mem_Kur_of_pow {x : ℂ_[p]} (n : ℕ) (hn : 0 < n) (hd : ¬ p ∣ n) (hx : x ^ n = 1) : x ∈ MaximalUnramifiedExtension p :=
  Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨n, hn, hd, hx⟩)

variable {R : Ranks} (H : Host R) (J : H.E →+* ℂ_[p])

end KurLemmas

end GlobalTheory.InertiaPairs

namespace GlobalTheory.InertiaPairs

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

section Fixed

variable {R : Ranks} (H : Host R)

def sInv (R : Ranks) : R.GG := ((1, -1), 1)

end Fixed

end GlobalTheory.InertiaPairs

namespace GlobalTheory.InertiaPairs

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.MainNotions.G (plGG)

theorem embT_tauPl (D : D7) (z : Bool × HH D) : TaylorLogMetric.embT D (tauPl D z) = D.host.emb (plGG D z) := by
  unfold TaylorLogMetric.embT tauPl
  rw [Equiv.apply_symm_apply]

theorem eTau_tauPl (D : D7) (z : Bool × HH D) : (D.eTau (tauPl D z) : D.R.GG) = plGG D z := by
  unfold tauPl
  rw [Equiv.apply_symm_apply]

theorem tauSg_tauPl (D : D7) (b : Bool) (t : HH D) : TaylorLogMetric.tauSg D (tauPl D (b, t)) = tauPl D (!b, t) := by
  have hm : plGG D (b, t) * TaylorLogMetric.sgm D = plGG D (!b, t) := by
    cases b <;> refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [plGG, Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2, TaylorLogMetric.sgm]
  have hmem : (D.eTau (tauPl D (b, t)) : D.R.GG) * TaylorLogMetric.sgm D ∈ D.R.Psi := by
    rw [eTau_tauPl, hm]; exact plGG_mem_Psi D _
  rw [show TaylorLogMetric.tauSg D (tauPl D (b, t)) = D.eTau.symm ⟨_, hmem⟩ from dif_pos hmem]
  refine (Equiv.symm_apply_eq _).2 (Subtype.ext ?_)
  simp only [eTau_tauPl, hm]

theorem inertia_pairs : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ ι : ℂ ≃+* ℂ_[p],
    ∃ (cE s : D.host.E ≃+* D.host.E) (δ : D.host.E), (∀ y, cE y = D.host.conj y) ∧ δ ^ 2 = -(p : D.host.E) ∧
    cE δ = -δ ∧ s δ = -δ ∧ (∀ y, s (s y) = y) ∧ (∀ y, s (cE y) = cE (s y)) ∧
    Function.Injective (fun z : Bool × HH D => TaylorLogMetric.embT D (tauPl D z)) ∧
    (∀ τ ρ, TaylorLogMetric.embT D τ δ = TaylorLogMetric.embT D ρ δ) ∧
    (∀ (t : HH D) y, TaylorLogMetric.embT D (tauPl D (true, t)) y = TaylorLogMetric.embT D (tauPl D (false, t)) (s (cE y))) ∧
    (∀ τ y, s y = y → ι (TaylorLogMetric.embT D τ y) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) ∧ Function.Bijective (tauPl D) ∧
    ∀ t : HH D, TaylorLogMetric.tauSg D (tauPl D (false, t)) = tauPl D (true, t) ∧
      TaylorLogMetric.tauSg D (tauPl D (true, t)) = tauPl D (false, t) := by
  intro D p _ hp ι
  have hp2 : p ≠ 2 := by rw [hp]; exact D.host.hypOdd.2.2.2.2
  have hpq : D.host.q ≠ p := by rw [hp]; exact D.host.hypOdd.2.2.1
  refine ⟨D.host.conj.toRingEquiv, (D.host.sigmaOf (sInv D.R)).toRingEquiv, D.host.sqrtMinusD, fun y => rfl, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, tauPl_bij D, fun t => ⟨tauSg_tauPl D false t, tauSg_tauPl D true t⟩⟩
  · rw [sqrt_sq, hp]
  · exact sigmaOf_sqrt_neg D.host (D.R.cc) rfl
  · exact sigmaOf_sqrt_neg D.host (sInv D.R) rfl
  · intro y
    change D.host.sigmaOf (sInv D.R) (D.host.sigmaOf (sInv D.R) y) = y
    rw [← AlgEquiv.mul_apply, ← sigmaOf_mul]
    have : sInv D.R * sInv D.R = 1 := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [sInv]
    rw [this, sigmaOf_one]
    rfl
  · intro y
    change D.host.sigmaOf (sInv D.R) (D.host.sigmaOf (D.R.cc) y) = D.host.sigmaOf (D.R.cc) (D.host.sigmaOf (sInv D.R) y)
    rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← sigmaOf_mul, ← sigmaOf_mul, mul_comm]
  · intro z z' h
    have h' : ∀ x, D.host.φ₀ (D.host.sigmaOf (plGG D z) x) = D.host.φ₀ (D.host.sigmaOf (plGG D z') x) := fun x => by
      have := RingHom.congr_fun h x
      simp only [embT_tauPl] at this
      exact this
    have hs : D.host.sigmaOf (plGG D z) = D.host.sigmaOf (plGG D z') :=
      AlgEquiv.ext fun x => D.host.φ₀.injective (h' x)
    have hg : plGG D z = plGG D z' := by
      unfold Host.sigmaOf at hs
      exact (D.host.gal).symm.injective hs
    apply (tauPl_bij D).1
    unfold tauPl
    congr 1
    exact Subtype.ext hg
  · intro τ ρ
    change D.host.φ₀ (D.host.sigmaOf (D.eTau τ : D.R.GG) D.host.sqrtMinusD) =
      D.host.φ₀ (D.host.sigmaOf (D.eTau ρ : D.R.GG) D.host.sqrtMinusD)
    rw [sigmaOf_sqrt_pos D.host _ (D.eTau τ).2, sigmaOf_sqrt_pos D.host _ (D.eTau ρ).2]
  · intro t y
    change D.host.emb _ y = D.host.emb _ (D.host.sigmaOf (sInv D.R) (D.host.sigmaOf (D.R.cc) y))
    rw [eTau_tauPl, eTau_tauPl, emb_sigmaOf, emb_sigmaOf]
    have hg : plGG D (false, t) * sInv D.R * D.R.cc = plGG D (true, t) := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_ <;> simp [plGG, Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2, sInv, Formalism.HC.Frame.cc, c0]
    rw [hg]
  · intro τ y hy
    have hy' : D.host.sigmaOf (sInv D.R) y = y := hy
    exact UpperTheory.Ram.image_mem_of_fixed_iod D.host ((ι : ℂ →+* ℂ_[p]).comp (TaylorLogMetric.embT D τ)) (MaximalUnramifiedExtension p)
      (fun z hz => mem_Kur_of_pow _ (Nat.mul_pos D.host.QS_pos D.host.hyp.1.pos)
        (by rw [hp]; exact D.host.toHostRaw.d_not_dvd_QSq) hz) y hy'

end GlobalTheory.InertiaPairs
end
end

