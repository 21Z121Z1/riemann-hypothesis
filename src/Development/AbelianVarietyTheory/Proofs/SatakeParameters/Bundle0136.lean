import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
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
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0123
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0911
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0040
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0130
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NrmIdNonneg
section
namespace GlobalTheory.KerJ.CharVal

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField

theorem lamC_mem' {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {x : ℂ} (h : x ∈ Qbar) :
    lamC lam x = lam ⟨x, h⟩ := by
  unfold lamC; rw [dif_pos h]

theorem embT_mem (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : embT D τ x ∈ Qbar := by
  have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have : IsAlgebraic ℚ ((embT D τ).toRatAlgHom x) := hx.algHom _
  exact (mem_algebraicClosure_iff).2 this

theorem chi_pow (D : D7) (t : D.Dt) (h : ℕ) (z : letI := D.host.cmStar; unitary D.host.E)
    (hp : PowRat D t h z) :
    ((D.chiD t : ℂˣ) : ℂ) ^ h = ∏ τ, (embT D τ (z : D.host.E))⁻¹ := by
  obtain ⟨-, k, hk, e⟩ := hp
  have h1 : D.chiD t ^ h = D.chiD (D.e1Dt z) := by
    rw [← map_pow, e, map_mul, D.chiD_UO k hk, mul_one]
  rw [← Units.val_pow_eq_pow_val, h1]
  exact D.rest_detCharacter_on_unitary_eq z

theorem chi_mem (D : D7) (t : D.Dt) (h : ℕ) (z : letI := D.host.cmStar; unitary D.host.E)
    (hp : PowRat D t h z) : ((D.chiD t : ℂˣ) : ℂ) ∈ Qbar := by
  have h0 : ((D.chiD t : ℂˣ) : ℂ) ^ h ∈ Qbar := by
    rw [chi_pow D t h z hp]
    exact prod_mem fun τ _ => inv_mem (embT_mem D τ _)
  exact (mem_algebraicClosure_iff).2 (((mem_algebraicClosure_iff).1 h0).of_pow hp.1)

theorem chiVal_holds (D : D7) : chiVal D := by
  intro p _ lam t h z hp
  refine ⟨chi_pow D t h z hp, ?_⟩
  have hm := chi_mem D t h z hp
  have e : (⟨((D.chiD t : ℂˣ) : ℂ), hm⟩ : Qbar) ^ h = ∏ τ, (⟨embT D τ (z : D.host.E), embT_mem D τ _⟩ : Qbar)⁻¹ := by
    apply Subtype.ext
    push_cast
    exact chi_pow D t h z hp
  rw [lamC_mem' lam hm, ← norm_pow, ← map_pow, e, map_prod, norm_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_inv₀, norm_inv, lamC_mem' lam (embT_mem D τ _)]

theorem key_norm {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {ι : Type*} [Fintype ι] (y κ : Qbar) (w : ι → Qbar)
    (s : ι → ℤ) (h n : ℕ) (hn : 0 < n) (e : y ^ h = (∏ τ, w τ ^ s τ) * κ) (hκ : κ ^ n = 1) :
    ‖lam y‖ ^ h = ∏ τ, ‖lam (w τ)‖ ^ s τ := by
  have h1 : ‖lam κ‖ = 1 := by
    have : ‖lam κ‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, hκ, map_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  rw [← norm_pow, ← map_pow, e, map_mul, norm_mul, h1, mul_one, map_prod, norm_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_zpow₀, norm_zpow]

theorem val_of (D : D7) (ρ : D.Dt →* ℂˣ) (s : D.what₂.Tau → ℤ) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    (t : D.Dt) (h : ℕ) (z : letI := D.host.cmStar; unitary D.host.E) (hp : PowRat D t h z)
    (ha : ((ρ t : ℂˣ) : ℂ) ∈ Qbar) (hU : ∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ ρ k ^ n = 1)
    (hz : ((ρ (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E)) ^ (s τ)) :
    ‖lamC lam ((ρ t : ℂˣ) : ℂ)‖ ^ h = ∏ τ, ‖lamC lam (embT D τ (z : D.host.E))‖ ^ (s τ) := by
  obtain ⟨-, k, hk, e⟩ := hp
  obtain ⟨n, hn, h1⟩ := hU k hk
  have h1' : ((ρ k : ℂˣ) : ℂ) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, h1]; rfl
  have hkm : ((ρ k : ℂˣ) : ℂ) ∈ Qbar :=
    (mem_algebraicClosure_iff).2 (((mem_algebraicClosure_iff).1 (h1' ▸ one_mem Qbar)).of_pow hn)
  have e2 : ((ρ t : ℂˣ) : ℂ) ^ h = (∏ τ, (embT D τ (z : D.host.E)) ^ (s τ)) * ((ρ k : ℂˣ) : ℂ) := by
    rw [← hz, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← map_pow, e, map_mul]
  have := key_norm lam (⟨_, ha⟩ : Qbar) ⟨_, hkm⟩ (fun τ => ⟨embT D τ (z : D.host.E), embT_mem D τ _⟩) s h n hn
    (by
      apply (algebraMap Qbar ℂ).injective
      simp only [map_pow, map_mul, map_prod, map_zpow₀]
      exact e2)
    (by
      apply (algebraMap Qbar ℂ).injective
      simp only [map_pow, map_one]
      exact h1')
  rw [lamC_mem' lam ha, this]
  exact Finset.prod_congr rfl fun τ _ => by rw [lamC_mem' lam (embT_mem D τ _)]

theorem rhoVal_holds (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ)
    (hR : rhoThreeOf D C mt) : rhoValOf D C mt := by
  intro p _ lam t h z hp i hi
  obtain ⟨a, b, c⟩ := hR i hi
  obtain ⟨⟨a1, -⟩, ⟨a2, -⟩⟩ := a t h z hp
  exact ⟨val_of D _ _ lam t h z hp a1 (fun k hk => by obtain ⟨n, hn, x, -⟩ := b k hk; exact ⟨n, hn, x⟩) (c z).1,
    val_of D _ _ lam t h z hp a2 (fun k hk => by obtain ⟨n, hn, -, x⟩ := b k hk; exact ⟨n, hn, x⟩) (c z).2⟩

theorem isUltra (p : ℕ) [Fact p.Prime] : IsUltrametricDist ℂ_[p] :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (PadicComplex.isNonarchimedean p)

theorem norm_le_one_of_int {K : Type} [NormedField K] [IsUltrametricDist K] (x : K)
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := K)).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := K))).mem_of_integral h1
  have h3 : NormedField.valuation x ≤ 1 := h2
  rw [NormedField.valuation_apply] at h3
  exact_mod_cast h3

section Nu

variable {E : Type} [Field E] [NumberField E] {K : Type} [NormedField K] [IsUltrametricDist K] (ψ : E →+* K)

theorem psi_int (a : 𝓞 E) : ‖ψ (a : E)‖ ≤ 1 :=
  norm_le_one_of_int _ ((RingOfIntegers.isIntegral_coe a).map (ψ : E →+* K).toIntAlgHom)

theorem pow_bound (𝔞 : Submodule (𝓞 E) E) (B : ℝ) (hB : ∀ x ∈ 𝔞, ‖ψ x‖ ≤ B) (hB0 : 0 ≤ B) :
    ∀ (n : ℕ), ∀ y ∈ 𝔞 ^ n, ‖ψ y‖ ≤ B ^ n
  | 0, y, hy => by
    rw [pow_zero, Submodule.mem_one] at hy
    obtain ⟨a, rfl⟩ := hy
    rw [pow_zero]
    exact psi_int ψ a
  | n + 1, y, hy => by
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy (fun m hm k hk => ?_) (fun x y hx hy => ?_)
    · rw [map_mul, norm_mul, pow_succ]
      exact mul_le_mul (pow_bound 𝔞 B hB hB0 n m hm) (hB k hk) (norm_nonneg _) (pow_nonneg hB0 n)
    · rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)

theorem nu_pow (𝔞 : Submodule (𝓞 E) E) (h : ℕ) (h0 : h ≠ 0) (z : E)
    (e : 𝔞 ^ h = Submodule.span (𝓞 E) {z}) :
    sSup ((fun x : E => ‖ψ x‖) '' (𝔞 : Set E)) ^ h = ‖ψ z‖ := by
  set S := (fun x : E => ‖ψ x‖) '' (𝔞 : Set E) with hS
  have hne : S.Nonempty := ⟨_, 0, 𝔞.zero_mem, rfl⟩
  have hpow : ∀ x ∈ 𝔞, ‖ψ x‖ ^ h ≤ ‖ψ z‖ := by
    intro x hx
    have : x ^ h ∈ Submodule.span (𝓞 E) {z} := e ▸ Submodule.pow_mem_pow 𝔞 hx h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
    rw [← norm_pow, ← map_pow, ← ha, Algebra.smul_def, map_mul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (psi_int ψ a)
  set b : ℝ := ‖ψ z‖ ^ ((h : ℝ)⁻¹) with hb
  have hb0 : 0 ≤ b := Real.rpow_nonneg (norm_nonneg _) _
  have hbh : b ^ h = ‖ψ z‖ := Real.rpow_inv_natCast_pow (norm_nonneg _) h0
  have hle : ∀ x ∈ 𝔞, ‖ψ x‖ ≤ b := fun x hx =>
    (pow_le_pow_iff_left₀ (norm_nonneg _) hb0 h0).1 (hbh ▸ hpow x hx)
  have hbd : BddAbove S := ⟨b, by rintro _ ⟨x, hx, rfl⟩; exact hle x hx⟩
  have hs0 : 0 ≤ sSup S := Real.sSup_nonneg (by rintro _ ⟨x, -, rfl⟩; exact norm_nonneg _)
  apply le_antisymm
  · rw [← hbh]
    exact pow_le_pow_left₀ hs0 (csSup_le hne (by rintro _ ⟨x, hx, rfl⟩; exact hle x hx)) h
  · have hz : z ∈ 𝔞 ^ h := e ▸ Submodule.mem_span_singleton_self z
    exact pow_bound ψ 𝔞 (sSup S) (fun x hx => le_csSup hbd ⟨x, hx, rfl⟩) hs0 h z hz

end Nu

noncomputable def psiT (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) : D.host.E →+* ℂ_[p] :=
  lam.comp ((embT D τ).codRestrict Qbar (embT_mem D τ))

theorem lamC_embT (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (x : D.host.E) :
    lamC lam (embT D τ x) = psiT D lam τ x := lamC_mem' lam (embT_mem D τ x)

theorem nrmId_pow (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (𝔞 : IdE D) (h : ℕ) (h0 : h ≠ 0)
    (z : D.host.E) (e : 𝔞 ^ h = Submodule.span (𝓞 D.host.E) {z}) :
    nrmId D lam τ 𝔞 ^ h = ‖lamC lam (embT D τ z)‖ := by
  unfold nrmId
  simp only [lamC_embT]
  haveI := isUltra p
  exact nu_pow (psiT D lam τ) 𝔞 h h0 z e

theorem nrmId_nonneg (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (𝔞 : IdE D) :
    0 ≤ nrmId D lam τ 𝔞 :=
  Real.sSup_nonneg (by rintro _ ⟨x, -, rfl⟩; exact norm_nonneg _)

theorem root_eq {ι : Type*} [Fintype ι] (a : ℝ) (ha : 0 ≤ a) (ν f : ι → ℝ) (hν : ∀ τ, 0 ≤ ν τ) (s : ι → ℤ) (h : ℕ) (h0 : h ≠ 0)
    (hf : ∀ τ, ν τ ^ h = f τ) (e : a ^ h = ∏ τ, f τ ^ s τ) : a = ∏ τ, ν τ ^ s τ := by
  refine (pow_left_inj₀ ha (Finset.prod_nonneg fun τ _ => zpow_nonneg (hν τ) _) h0).1 ?_
  rw [e, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← hf τ, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem brRho_holds (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u))
    (mt : ℕ → D.Dt →* ℂˣ) (hR : rhoThreeOf D C mt) : brRhoOf D C mt := by
  intro idl hpin p _ lam t
  obtain ⟨k, z, hp⟩ := powRatAll_of D idl hpin (GlobalTheory.KernelScalarUnit.normOne_pow D) t
  obtain ⟨-, -, hmul, hz, -⟩ := hpin
  have h0 : k ≠ 0 := Nat.pos_iff_ne_zero.1 hp.1
  have hid : idl (QuotientGroup.mk t) ^ k = Submodule.span (𝓞 D.host.E) {(z : D.host.E)} := by
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    obtain ⟨-, c, hc, e⟩ := hp
    rw [← idl_pow hmul, ← hz z]
    congr 1
    rw [← QuotientGroup.mk_pow, e]
    exact QuotientGroup.mk_mul_of_mem _ hc
  have hf : ∀ τ, nrmId D lam τ (idl (QuotientGroup.mk t)) ^ k = ‖lamC lam (embT D τ (z : D.host.E))‖ :=
    fun τ => nrmId_pow D lam τ _ k h0 _ hid
  have hν : ∀ τ, 0 ≤ nrmId D lam τ (idl (QuotientGroup.mk t)) := fun τ => nrmId_nonneg D lam τ _
  refine ⟨?_, fun i hi => ?_⟩
  · have e := (chiVal_holds D p lam t k z hp).2
    have := root_eq _ (norm_nonneg _) _ _ hν (fun _ => (-1 : ℤ)) k h0 hf (by simpa only [zpow_neg_one] using e)
    simpa only [zpow_neg_one] using this
  · obtain ⟨x, y⟩ := rhoVal_holds D C mt hR p lam t k z hp i hi
    exact ⟨root_eq _ (norm_nonneg _) _ _ hν _ k h0 hf x, root_eq _ (norm_nonneg _) _ _ hν _ k h0 hf y⟩

end GlobalTheory.KerJ.CharVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitIdentityAllOfIntegralClassHostLog
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd
namespace IntegralSeriesSubstitution
open MvPowerSeries
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)

theorem orb_bijective (D : D7) (p : ℕ) (R : Finset (OrbitPlaces.Pl D)) (hR : OrbitPlaces.IsReps D p R) :
    Function.Bijective (fun x : R × ZMod (nP D p) => OrbitPlaces.orbMap D p x.1 x.2) := by
  constructor
  · rintro ⟨⟨r, hr⟩, s⟩ ⟨⟨r', hr'⟩, s'⟩ h
    simp only at h
    have h1 : ∃ e : ℕ, posPl D p r e = OrbitPlaces.orbMap D p r s := ⟨s.val, rfl⟩
    have h2 : ∃ e : ℕ, posPl D p r' e = OrbitPlaces.orbMap D p r s := ⟨s'.val, h.symm⟩
    obtain ⟨r0, -, huniq⟩ := hR (OrbitPlaces.orbMap D p r s)
    have hrr : r = r' := (huniq r ⟨hr, h1⟩).trans (huniq r' ⟨hr', h2⟩).symm
    subst hrr
    have hs : s = s' := PI.OrbJet.OrbW.orbMap_inj D p r h
    subst hs
    rfl
  · intro z
    obtain ⟨r, ⟨hr, e, he⟩, -⟩ := hR z
    refine ⟨(⟨r, hr⟩, (e : ZMod (nP D p))), ?_⟩
    show OrbitPlaces.orbMap D p r (e : ZMod (nP D p)) = z
    exact (PI.OrbJet.OrbW.posPl_eq_orbMap D p r e).symm.trans he

theorem subst_entLog_orb (D : D7) (p : ℕ) [Fact p.Prime] {M N N' : ℕ} (κ : Fin M → OrbitPlaces.Pl D × Fin N)
    (y : ZV (nP D p) M N') :
    subst (fun y' : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (κ y'.2.1).1 y'.1, (κ y'.2.1).2, y'.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (entLog (K := ℂ_[p]) p y) = OrbitPlaces.logPl D p (OrbitPlaces.orbMap D p (κ y.2.1).1 y.1, (κ y.2.1).2, y.2.2) := by
  obtain ⟨s, a', b⟩ := y
  have hY : HasSubst (fun s' : ZMod (nP D p) => (X (s', a', b) : MvPowerSeries (ZV (nP D p) M N') ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hπ : HasSubst (fun y' : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (κ y'.2.1).1 y'.1, (κ y'.2.1).2, y'.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hY2 : HasSubst (fun s' : ZMod (nP D p) => (X (s', (κ a').2, b) : MvPowerSeries (ZV (nP D p) N N') ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hP : HasSubst (X ∘ ⇑(PI.OrbJet.AU.pE D p (κ a').1 (Fin N × Fin N')) :
      ZMod (nP D p) × Fin N × Fin N' → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hE := PI.OrbJet.AU.rename_jet D p (β := Fin N × Fin N') (κ a').1 (s, (κ a').2, b)
  rw [Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel.jetLogG_eq_entLog p (nP D p) N N' (s, (κ a').2, b),
    GlobalTheory.KerStd.CofactorConverse.entLog_eq_letLog, MvPowerSeries.rename_eq_subst,
    subst_comp_subst_apply hY2 hP] at hE
  show _ = PI.OrbJet.logPl D p (PI.OrbJet.AU.pE D p (κ a').1 (Fin N × Fin N') (s, (κ a').2, b))
  rw [← hE, GlobalTheory.KerStd.CofactorConverse.entLog_eq_letLog, subst_comp_subst_apply hY hπ]
  congr 1
  funext s'
  rw [subst_X hπ, subst_X hP]
  rfl

theorem integral_subst_X_of_injective {K : Type} [NormedField K] {σ τ : Type} [Finite σ] (φ : σ → τ)
    (hφ : Function.Injective φ) {U : MvPowerSeries σ K} (hU : Integral U) :
    Integral (subst (fun x => (X (φ x) : MvPowerSeries τ K)) U) := by
  classical
  let e : σ ↪ τ := ⟨φ, hφ⟩
  have h : subst (fun x => (X (φ x) : MvPowerSeries τ K)) U = rename e U := by
    rw [rename_eq_subst]; rfl
  intro n
  rw [h]
  by_cases hn : ∃ m, Finsupp.embDomain e m = n
  · obtain ⟨m, rfl⟩ := hn
    rw [coeff_embDomain_rename]
    exact hU m
  · rw [coeff_rename_eq_zero]
    · simp
    · rintro ⟨m, hm⟩
      exact hn ⟨m, by rw [Finsupp.embDomain_eq_mapDomain]; exact hm⟩

theorem sumE_reindex {K : Type} [Field K] {R ι : Type} [Fintype R] [Fintype ι] {M N N' : ℕ} (eA : Fin M ≃ R × Fin N)
    (be : MvPowerSeries (Fin 2) K) :
    subst (fun x : Bool × (R × ι) × Fin N × Fin N' =>
        (X (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2) : MvPowerSeries (Bool × ι × Fin M × Fin N') K))
      (Formalism.L2.Th1.D.sumE (ι := R × ι) (N0 := N) (N1 := N') be) = Formalism.L2.Th1.D.sumE (ι := ι) (N0 := M) (N1 := N') be := by
  have hρ : HasSubst (fun x : Bool × (R × ι) × Fin N × Fin N' =>
      (X (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2) : MvPowerSeries (Bool × ι × Fin M × Fin N') K)) :=
    hasSubst_of_constantCoeff_zero fun x => constantCoeff_X _
  unfold Formalism.L2.Th1.D.sumE
  rw [← coe_substAlgHom hρ, map_sum]
  let E : (R × ι) × Fin N × Fin N' ≃ ι × Fin M × Fin N' :=
    { toFun := fun e => (e.1.2, eA.symm (e.1.1, e.2.1), e.2.2)
      invFun := fun e => (((eA e.2.1).1, e.1), (eA e.2.1).2, e.2.2)
      left_inv := fun ⟨⟨r, k⟩, a, b⟩ => by simp
      right_inv := fun ⟨k, a, b⟩ => by simp }
  refine Fintype.sum_equiv E _ _ fun e => ?_
  rw [coe_substAlgHom, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun a => constantCoeff_X _) hρ]
  congr 1
  funext a
  rw [subst_X hρ]
  split_ifs <;> rfl

theorem orbitIdentity_all_of_integralClass_hostLog : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → OrbitPlaces.OrbOK D p → ∀ (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (ζ : MaximalUnramifiedExtension p), BeData p (nP D p) σ F (cob F (phFF p g2 g3 s2 ε)) om oms ζ → ∀ (R : Finset (OrbitPlaces.Pl D)), OrbitPlaces.IsReps D p R → ∀ (N N' r : ℕ) (f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p), HypPair σ f f' → ∀ (Θ : MvPowerSeries (Fin r) ℂ_[p]), HostLog p g2 g3 s2 ε Θ → ∀ (ep : ℂ_[p]) (Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst (hypZ D p σ om oms R f f') Θ → OrbitPlaces.ThetaExpansionAllPlaces D p R ep (fun _ => -1) (fun _ => beOf p (nP D p) σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ) Th := by
  intro D p _ g2 g3 s2 ε σ F hC hO om oms ζ hB R hR N N' r f f' hH Θ hΘ ep Th hTh
  obtain ⟨h5, hg2, hg3, hε, hth, hσ, hF, hN⟩ := hC
  have hBd := hB
  obtain ⟨-, -, hF1, hF2, hOw, hTr, hζ⟩ := hB
  have hI := (HostLog.iff_phSum p g2 g3 s2 ε Θ).1 hΘ
  obtain ⟨U0, Φ, hU0, hΦ0, hsim, hEq⟩ := Formalism.L2.Th1.Top.HypShape_of Formalism.L2.Th1.Top.CalcC_proof p h5 g2 g3 ε s2
    hg2 hg3 hε hth σ hσ F hF hN N N' (R × Fin (nP D p / 2)) (Fin r) f f' hH _ hI

  let M := Fintype.card R * N
  let eA : Fin M ≃ R × Fin N :=
    finProdFinEquiv.symm.trans ((Fintype.equivFin R).symm.prodCongr (Equiv.refl _))
  let rv : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' → Bool × Fin (nP D p / 2) × Fin M × Fin N' :=
    fun x => (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2)
  have hrv : Function.Injective rv := by
    rintro ⟨c, ⟨a1, k⟩, a2, b⟩ ⟨c', ⟨a1', k'⟩, a2', b'⟩ h
    simp only [rv, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    have h3' := congrArg eA h3
    simp only [Equiv.apply_symm_apply, Prod.mk.injEq] at h3'
    rw [h1, h2, h3'.1, h3'.2, h4]
  let ρs : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' → MvPowerSeries (Bool × Fin (nP D p / 2) × Fin M × Fin N') ℂ_[p] :=
    fun x => X (rv x)
  have hρs : HasSubst ρs := hasSubst_of_constantCoeff_zero fun x => constantCoeff_X _
  have hU0' : Integral (subst ρs U0) := integral_subst_X_of_injective rv hrv hU0
  have hΦ0' : constantCoeff (subst ρs Φ) = 0 :=
    constantCoeff_subst_eq_zero hρs (fun x => constantCoeff_X _) hΦ0
  have hsE := sumE_reindex (ι := Fin (nP D p / 2)) (N' := N') eA (map (MaximalUnramifiedExtension p).subtype (cob F (phFF p g2 g3 s2 ε)))
  have hρe : ρs = fun x : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' =>
      (X (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2) : MvPowerSeries (Bool × Fin (nP D p / 2) × Fin M × Fin N') ℂ_[p]) := rfl
  rw [← hρe] at hsE
  have hsim' : Formalism.InvariantFactorPaths.G7.Simeq (subst ρs Φ)
      (Formalism.L2.Th1.D.sumE (ι := Fin (nP D p / 2)) (N0 := M) (N1 := N') (map (MaximalUnramifiedExtension p).subtype (cob F (phFF p g2 g3 s2 ε)))) := by
    rw [← hsE]
    refine ⟨?_, ?_⟩
    · rw [← subst_sub hρs]
      exact constantCoeff_subst_eq_zero hρs (fun x => constantCoeff_X _) hsim.1
    · rw [← subst_sub hρs, ← Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hρs hsim.1]
      exact integral_subst_X_of_injective rv hrv hsim.2
  obtain ⟨U, hU, hUeq⟩ := Formalism.L2.Th1.D.b0 (MaximalUnramifiedExtension p) ℂ_[p] p (nP D p) M N' σ (MaximalUnramifiedExtension p).subtype hσ (fun a => rfl)
    hO.two hO.even F hF _ hF1 hF2 (Fin (nP D p / 2)) om oms hOw hTr ζ hζ (subst ρs U0) (subst ρs Φ) hU0' hΦ0' hsim'

  obtain ⟨g, hg0, hg1, hg2⟩ := Formalism.DworkPowerSeriesWeights.generalized_log_inverse.{0, 0} ℂ_[p] p (Fact.out)
    (ZV (nP D p) M N') (fun y => (y.1 - 2, y.2.1, y.2.2))
  have hent := (Formalism.DworkPowerSeriesWeights.logarithm_weight_comparison.{0} ℂ_[p] p (nP D p) M N').2.1
  have hgE : ∀ y, subst g (entLog (K := ℂ_[p]) p y) = X y := fun y => by rw [hent]; exact hg1 y
  have hfun : entLog (K := ℂ_[p]) (d := nP D p) (N0 := M) (N1 := N') p =
      Formalism.DworkPowerSeriesWeights.genLog p (fun y : ZV (nP D p) M N' => (y.1 - 2, y.2.1, y.2.2)) := funext hent
  have hEg : ∀ y, subst (entLog (K := ℂ_[p]) (d := nP D p) (N0 := M) (N1 := N') p) (g y) = X y := fun y => by
    rw [hfun]; exact hg2 y
  have hZ := hUeq g hg0 hgE
  have hR1 : mvExp (-subst ρs Φ) * subst ρs U0 = subst ρs (Formalism.L2.Th1.Top.inHyp p f f'
      (subst (fun i : Fin r => (Formalism.InvariantFactorPaths.G7.at1 i (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p])) Θ)) := by
    rw [hEq, subst_mul hρs, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hρs (by rw [map_neg, hΦ0, neg_zero]),
      Formalism.L2.Th1.D.BiextensionSums.subst_neg' hρs]

  let πv : ZV (nP D p) M N' → OrbitPlaces.Pl D × Fin N × Fin N' :=
    fun y => (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2)
  have hπv : Function.Injective πv := by
    rintro ⟨s, a, b⟩ ⟨s', a', b'⟩ h
    simp only [πv, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have hb := (orb_bijective D p R hR).1 (a₁ := ((eA a).1, s)) (a₂ := ((eA a').1, s')) h1
    simp only [Prod.mk.injEq] at hb
    have ha : eA a = eA a' := Prod.ext hb.1 h2
    rw [hb.2, eA.injective ha, h3]
  let πs : ZV (nP D p) M N' → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] := fun y => X (πv y)
  have hπs : HasSubst πs := hasSubst_of_constantCoeff_zero fun x => constantCoeff_X _
  have hgs : HasSubst g := hasSubst_of_constantCoeff_zero hg0
  have hbe0 : constantCoeff (beOf p (nP D p) σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ) = 0 :=
    Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel.constant_coeff_zero_of_vanishing_alt p (nP D p) (GlobalTheory.KerStd.bHyps_of_beStd p (nP D p) _ h5 hO.two hO.even
      ⟨σ, F, _, om, oms, ζ, hBd, rfl⟩).2.2.1
  have hπe : πs = fun y : ZV (nP D p) M N' =>
      (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) := rfl
  have hc := GlobalTheory.T.orbitPlaces_thetaSeries_subst_orbMap_eq D p h5 σ om oms R eA f f' Θ
  rw [← hρe, ← hπe] at hc
  have hA := congrArg (subst πs) hZ
  rw [hR1, hc] at hA
  rw [Formalism.DworkPowerSeriesWeights.thetaZ, subst_mul hπs] at hA
  have hlin : subst (Formalism.DworkPowerSeriesWeights.linSub Formalism.DworkPowerSeriesWeights.idM) (subst g U) = subst g U := by
    have : (Formalism.DworkPowerSeriesWeights.linSub Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → MvPowerSeries (ZV (nP D p) M N') ℂ_[p]) = X :=
      funext fun x => Formalism.DworkPowerSeriesWeights.OrbMul.linSub_idM x
    rw [this, subst_self]; rfl
  rw [hlin, subst_comp_subst_apply hgs hπs] at hA
  have hexp := GlobalTheory.T.expFactor_allOrbits_eq_prod_orbits D p R (N' := N') eA (beOf p (nP D p) σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ) hbe0
  rw [← hπe] at hexp
  rw [show (MvPowerSeries.map (MaximalUnramifiedExtension p).subtype (Formalism.L2.Th1.D.beMean p σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ)) =
    beOf p (nP D p) σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ from rfl] at hA
  rw [hexp] at hA

  have hlog : HasSubst (OrbitPlaces.logPl D p (β := Fin N × Fin N')) :=
    hasSubst_of_constantCoeff_zero (PI.OrbJet.AU.cc_log D p)
  refine ⟨subst πs U, integral_subst_X_of_injective πv hπv hU, ?_⟩
  have hCX : HasSubst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
      (C ep * X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero fun v => by simp
  have h1 : subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => C ep * OrbitPlaces.logPl D p v) Th =
      subst (OrbitPlaces.logPl D p (β := Fin N × Fin N')) (subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
        (C ep * X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th) := by
    rw [subst_comp_subst_apply hCX hlog]
    congr 1
    funext v
    rw [subst_mul hlog, subst_C, subst_X hlog]
  rw [h1, hTh, hA, subst_mul hlog]
  congr 1
  have hπg : HasSubst (fun y => subst πs (g y)) :=
    hasSubst_of_constantCoeff_zero fun y => constantCoeff_subst_eq_zero hπs (fun x => constantCoeff_X _) (hg0 y)
  rw [subst_comp_subst_apply hπg hlog]
  congr 1
  funext y
  have hlgE : HasSubst (entLog (K := ℂ_[p]) (d := nP D p) (N0 := M) (N1 := N') p) := by
    exact hasSubst_of_constantCoeff_zero fun v => by
      rw [← Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel.jetLogG_eq_entLog]
      exact Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel.cc_jetLogG p (nP D p) v
  rw [subst_comp_subst_apply hπs hlog]
  have e : (fun y' => subst (OrbitPlaces.logPl D p (β := Fin N × Fin N')) (πs y')) =
      fun y' => subst πs (entLog (K := ℂ_[p]) p y') := by
    funext y'
    rw [subst_X hlog]
    exact (subst_entLog_orb D p (N' := N') (fun a => ((eA a).1, (eA a).2)) y').symm
  rw [e, ← subst_comp_subst_apply hlgE hπs, hEg, subst_X hπs]

end IntegralSeriesSubstitution
end GlobalTheory.KerStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowerOfAbelianSchemeProjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace GlobalTheory.KS

theorem isProjOver_pow : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R),
    IsProjOver s → ∀ (A : Over X) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB →
    Out.RelAmple A L → ∀ k : ℕ, IsProjOver ((GlobalTheory.KS.pow A k).hom ≫ s) := by
  intro R _ _ X s hs A _ _ hA L hL hamp k
  obtain ⟨hsp, H, hH⟩ := (GlobalTheory.isProjOver_iff_isProper_and_exists_isAmpleLB s).1 hs
  have p := Out.powIsPowGrp A k
  have hrel : Out.RelAmple (Out.powObj A k) (Out.boxLB L p.pr) :=
    GlobalTheory.relAmple_boxLB X (Out.powObj A k) A k p L hL hamp
  obtain ⟨-, N, hN⟩ := GlobalTheory.RelAmpleQProj.isProper_and_exists_isAmpleLB (Out.powObj A k)
    (LB.isLB_linComb hL _ _) hrel hH
  let e : GlobalTheory.KS.pow A k ≅ Out.powObj A k :=
    IsLimit.conePointUniqueUpToIso (limit.isLimit _) (Out.powIsLimit A k)
  have hpA : IsProper A.hom := hA.proper
  have : IsProper (GlobalTheory.KS.pow A k).hom := GlobalTheory.KS.Leray.isProper_pow_hom A hpA k
  have : IsIso e.hom.left := ((Over.forget X).mapIso e).isIso_hom
  have := hsp
  exact (hN.pull_of_isAffineHom e.hom.left).isProjOver _

end GlobalTheory.KS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitThetaCorrespondenceOfLocalPairings
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.RowTie

theorem split_theta_correspondence_of_local_pairings : ∀ D : D7, (∀ i, PairLift D.nd D.naut i) → Formalism.MainNotions.SumRepresentations.adm3 D := by
  intro D h i σ P hθ w hw
  exact GlobalTheory.RowTie.splitLift_of_pairLift _ _ _ D.nd D.naut i (h i) σ P hθ w hw

end GlobalTheory.RowTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedShiftFixedRatioConstDomainStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedShift_fixed_ratio_const_domain : ∀ {B G : Type} [CommRing B] [IsDomain B] [CharZero B] (σ : G → B ≃+* B) (τ : G → B),
  (∀ d d' : B, d ≠ 0 → ¬ ∀ g, d * σ g d' - σ g d * d' = d * σ g d * τ g) →
  ∀ p q : Polynomial B, q ≠ 0 →
  (∀ g, q * (p.map (σ g : B →+* B)).comp (X + C (τ g)) = (q.map (σ g : B →+* B)).comp (X + C (τ g)) * p) →
  ∃ d d' : B, d ≠ 0 ∧ C d * p = C d' * q ∧ ∀ g, d * σ g d' = σ g d * d' := by
  first | exact @GlobalTheory.InvRatFun.fixed_ratio_const | exact GlobalTheory.InvRatFun.fixed_ratio_const | (intros; apply GlobalTheory.InvRatFun.fixed_ratio_const <;> assumption)
end

