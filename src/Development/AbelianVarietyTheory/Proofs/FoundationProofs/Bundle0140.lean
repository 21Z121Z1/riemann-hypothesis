import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import GroundTheory.GlobalFields.ComplexMultiplication.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0135
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0115
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0181
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonLthPowerReductionAlmostAllPrimes
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0037
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0026
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0136
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JInvariantEqualSl2Orbit
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.JOrbit

open GroundTheory.Global.Elliptic

theorem exists_smul_of_homothetic (τ σ : ℍ) {c : ℂ} (hc : c ≠ 0)
    (h : ((latticeOfTau τ).lattice : Set ℂ) = (c * ·) '' (latticeOfTau σ).lattice) :
    ∃ γ : SL(2, ℤ), τ = γ • σ := by
  have m1 : (τ : ℂ) ∈ (c * ·) '' ((latticeOfTau σ).lattice : Set ℂ) := by
    rw [← h]; exact (latticeOfTau τ).ω₁_mem_lattice
  have m2 : (1 : ℂ) ∈ (c * ·) '' ((latticeOfTau σ).lattice : Set ℂ) := by
    rw [← h]; exact (latticeOfTau τ).ω₂_mem_lattice
  have m3 : c * σ ∈ ((latticeOfTau τ).lattice : Set ℂ) := by
    rw [h]; exact ⟨σ, (latticeOfTau σ).ω₁_mem_lattice, rfl⟩
  have m4 : c * 1 ∈ ((latticeOfTau τ).lattice : Set ℂ) := by
    rw [h]; exact ⟨1, (latticeOfTau σ).ω₂_mem_lattice, rfl⟩
  obtain ⟨z, hz, h1⟩ := m1
  obtain ⟨w, hw, h2⟩ := m2
  obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.1 hz
  obtain ⟨e, f, rfl⟩ := PeriodPair.mem_lattice.1 hw
  obtain ⟨p, q, h3⟩ := PeriodPair.mem_lattice.1 m3
  obtain ⟨r, s, h4⟩ := PeriodPair.mem_lattice.1 m4
  simp only [latticeOfTau_ω₁, latticeOfTau_ω₂, mul_one] at h1 h2 h3 h4
  have k1 : (σ : ℂ) = p * (a * σ + b) + q * (e * σ + f) := by
    apply mul_left_cancel₀ hc
    linear_combination -h3 - p * h1 - q * h2
  have k2 : (1 : ℂ) = r * (a * σ + b) + s * (e * σ + f) := by
    apply mul_left_cancel₀ hc
    linear_combination -h4 - r * h1 - s * h2
  have k3 : (τ : ℂ) * (e * σ + f) = a * σ + b := by
    apply mul_left_cancel₀ hc
    linear_combination (τ : ℂ) * h2 - h1
  have hy : 0 < σ.im := σ.im_pos
  have hv : 0 < τ.im := τ.im_pos
  have k1i := congrArg Complex.im k1
  have k1r := congrArg Complex.re k1
  have k2i := congrArg Complex.im k2
  have k2r := congrArg Complex.re k2
  have k3i := congrArg Complex.im k3
  have k3r := congrArg Complex.re k3
  simp at k1i k1r k2i k2r k3i k3r
  have e1 : ((p * a + q * e : ℤ) : ℝ) = (1 : ℤ) := by
    apply mul_right_cancel₀ hy.ne'
    push_cast; linear_combination -k1i
  have e3 : ((r * a + s * e : ℤ) : ℝ) = (0 : ℤ) := by
    apply mul_right_cancel₀ hy.ne'
    push_cast; linear_combination -k2i
  have e2 : ((p * b + q * f : ℤ) : ℝ) = (0 : ℤ) := by
    push_cast at e1 ⊢; linear_combination -k1r - σ.re * e1
  have e4 : ((r * b + s * f : ℤ) : ℝ) = (1 : ℤ) := by
    push_cast at e3 ⊢; linear_combination -k2r - σ.re * e3
  have e1' : p * a + q * e = 1 := by exact_mod_cast e1
  have e2' : p * b + q * f = 0 := by exact_mod_cast e2
  have e3' : r * a + s * e = 0 := by exact_mod_cast e3
  have e4' : r * b + s * f = 1 := by exact_mod_cast e4
  have hdet : (a * f - b * e) * (p * s - q * r) = 1 := by
    linear_combination (r * b + s * f) * e1' + e4' - (r * a + s * e) * e2'
  have him : τ.im * ((e * σ.re + f) ^ 2 + (e * σ.im) ^ 2) = σ.im * ((a * f - b * e : ℤ) : ℝ) := by
    push_cast
    linear_combination (e * σ.re + f) * k3i - (e * σ.im) * k3r
  have hnn : (0 : ℝ) ≤ ((a * f - b * e : ℤ) : ℝ) := by
    have : 0 ≤ σ.im * ((a * f - b * e : ℤ) : ℝ) := by rw [← him]; positivity
    exact (mul_nonneg_iff_of_pos_left hy).1 this
  have hnn' : 0 ≤ a * f - b * e := by exact_mod_cast hnn
  have hD : a * f - b * e = 1 := Int.eq_one_of_mul_eq_one_right hnn' hdet
  have hne : (e : ℂ) * σ + f ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h2
    exact zero_ne_one h2
  let γ : SL(2, ℤ) := ⟨!![a, b; e, f], by rw [Matrix.det_fin_two_of]; exact hD⟩
  refine ⟨γ, ?_⟩
  ext
  rw [coe_specialLinearGroup_apply γ σ]
  simp [γ]
  rw [eq_div_iff hne, k3]

theorem exists_smul_of_E₄_E₆ :
    ∀ τ σ : ℍ, E₄ τ ^ 3 * E₆ σ ^ 2 = E₆ τ ^ 2 * E₄ σ ^ 3 → ∃ γ : SL(2, ℤ), τ = γ • σ := by
  intro τ σ h
  have hj : modularJ σ = modularJ τ := by
    have h1 := ModularForm.discriminant_ne_zero τ
    have h2 := ModularForm.discriminant_ne_zero σ
    rw [modularJ, modularJ, div_eq_div_iff h2 h1,
      ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ,
      ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq σ]
    linear_combination h / 1728
  obtain ⟨c, hc, hl⟩ := (modularJ_eq_iff σ τ).1 hj
  exact exists_smul_of_homothetic τ σ hc hl

end GlobalTheory.JOrbit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCharactersEqOnPrincipalCongruenceStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerCharacters_eqOn_principalCongruence : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (x : X.Khat l) (χ χ' : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Kum X l n x χ' → Near χ χ' := by
  first | exact @GlobalTheory.KZ.H3.kum_near | exact GlobalTheory.KZ.H3.kum_near | (intros; apply GlobalTheory.KZ.H3.kum_near <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionFractionFieldOfQExpansions
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_of_qexp : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs, a (mob (ofSL γ) z) = a z) → (∀ γ : SL(2, ℤ), ∃ (c : ℤ → Ω) (n0 : ℤ), (∀ n < n0, c n = 0) ∧ ∀ z ∈ Hs, HasSum (fun n : ℤ => ε (c n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z / M)) (a (mob (ofSL γ) z))) → ∃ f : T.K, T.an f = (a : Mero) := by
  intro Ω _ _ _ ε T a M hM _ hinv hexp
  have hHs : ∀ τ : ℍ, (τ : ℂ) ∈ Hs := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict.2.2.2.2
  have hmob : ∀ (γ : SL(2, ℤ)) (τ : ℍ), mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ) := GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties.2.2.2.1
  set f : ℍ → ℂ := fun τ => a τ with hf
  have hinvf : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, f (γ • τ) = f τ := by
    intro γ hγ τ
    simp only [hf]
    rw [← hmob γ τ]
    exact hinv γ hγ τ (hHs τ)
  have hw : ∀ γ : SL(2, ℤ), ∃ w : ℕ, QAll (· ∈ ε.range) M fun τ => DD τ ^ w * f (γ • τ) := by
    intro γ
    obtain ⟨c, n0, hc0, hs⟩ := hexp γ
    refine (GlobalTheory.T.exists_deltaPow_qExpansion_iff_laurentSeries ε.range M (fun τ => f (γ • τ)) hM).2 ⟨fun n => ε (c n), n0, fun n => ⟨c n, rfl⟩, ?_, ?_⟩
    · intro n hn
      simp [hc0 n hn]
    · intro τ
      have := hs τ (hHs τ)
      simp only [hf]
      rw [← hmob γ τ]
      exact this
  obtain ⟨w, hLv⟩ := GlobalTheory.T.exists_Lv_of_invariant_Gamma_of_forall_QAll ε.range M f hM hinvf hw
  have hmem : f ∈ ring ε.range := mem_ring_of_inR ⟨M, w, hM, hLv⟩
  refine ⟨T.io ⟨f, hmem⟩, ?_⟩
  rw [T.an_io]
  exact GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict.2.2.2.1 a

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOver
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN.RingMem

theorem inR_const (E : Subring ℂ) (c : ℂ) (hc : c ∈ E) : InR E fun _ => c := by
  refine ⟨1, 0, one_pos, fun _ _ _ => rfl, fun γ => ?_⟩
  have h := GlobalTheory.QFam.QAllSubring.const (R := E) (N := 1) hc
  simpa only [pow_zero, one_mul] using h

theorem lv_lift {E : Subring ℂ} {f : ℍ → ℂ} {N w : ℕ} (N₂ : ℕ) (hN₂ : 0 < N₂) (w' : ℕ) (hw : w ≤ w')
    (hN : 0 < N) (h : Lv E N w f) : Lv E (N * N₂) w' f :=
  GlobalTheory.T.lv_mono_of_dvd_of_le E N (N * N₂) w w' f (Nat.mul_pos hN hN₂) (dvd_mul_right N N₂) hw h

theorem lv_lift' {E : Subring ℂ} {f : ℍ → ℂ} {N w : ℕ} (N₁ : ℕ) (hN₁ : 0 < N₁) (w' : ℕ) (hw : w ≤ w')
    (hN : 0 < N) (h : Lv E N w f) : Lv E (N₁ * N) w' f :=
  GlobalTheory.T.lv_mono_of_dvd_of_le E N (N₁ * N) w w' f (Nat.mul_pos hN₁ hN) (dvd_mul_left N N₁) hw h

theorem inR_add {E : Subring ℂ} {f g : ℍ → ℂ} (hf : InR E f) (hg : InR E g) : InR E (f + g) := by
  obtain ⟨N₁, w₁, hN₁, hf⟩ := hf
  obtain ⟨N₂, w₂, hN₂, hg⟩ := hg
  have hf' := lv_lift N₂ hN₂ (max w₁ w₂) (le_max_left _ _) hN₁ hf
  have hg' := lv_lift' N₁ hN₁ (max w₁ w₂) (le_max_right _ _) hN₂ hg
  refine ⟨N₁ * N₂, max w₁ w₂, Nat.mul_pos hN₁ hN₂, fun γ hγ τ => ?_, fun γ => ?_⟩
  · simp only [Pi.add_apply, hf'.1 γ hγ τ, hg'.1 γ hγ τ]
  · have h := GlobalTheory.QFam.QAllSubring.add (hf'.2 γ) (hg'.2 γ)
    refine (congrArg (QAll (· ∈ E) (N₁ * N₂)) (funext fun τ => ?_)).mp h
    simp only [Pi.add_apply]; ring

theorem inR_mul {E : Subring ℂ} {f g : ℍ → ℂ} (hf : InR E f) (hg : InR E g) : InR E (f * g) := by
  obtain ⟨N₁, w₁, hN₁, hf⟩ := hf
  obtain ⟨N₂, w₂, hN₂, hg⟩ := hg
  have hf' := lv_lift N₂ hN₂ w₁ le_rfl hN₁ hf
  have hg' := lv_lift' N₁ hN₁ w₂ le_rfl hN₂ hg
  refine ⟨N₁ * N₂, w₁ + w₂, Nat.mul_pos hN₁ hN₂, fun γ hγ τ => ?_, fun γ => ?_⟩
  · simp only [Pi.mul_apply, hf'.1 γ hγ τ, hg'.1 γ hγ τ]
  · have h := GlobalTheory.QFam.QAllSubring.mul (hf'.2 γ) (hg'.2 γ)
    refine (congrArg (QAll (· ∈ E) (N₁ * N₂)) (funext fun τ => ?_)).mp h
    simp only [Pi.mul_apply]; ring

theorem inR_neg {E : Subring ℂ} {f : ℍ → ℂ} (hf : InR E f) : InR E (-f) := by
  obtain ⟨N, w, hN, hf⟩ := hf
  refine ⟨N, w, hN, fun γ hγ τ => ?_, fun γ => ?_⟩
  · simp only [Pi.neg_apply, hf.1 γ hγ τ]
  · have h := GlobalTheory.QFam.QAllSubring.sub (GlobalTheory.QFam.QAllSubring.const (R := E) (N := N) E.zero_mem) (hf.2 γ)
    refine (congrArg (QAll (· ∈ E) N) (funext fun τ => ?_)).mp h
    simp only [Pi.neg_apply]; ring

def inRSubring (E : Subring ℂ) : Subring (ℍ → ℂ) where
  carrier := {f | InR E f}
  mul_mem' := inR_mul
  one_mem' := inR_const E 1 E.one_mem
  add_mem' := inR_add
  zero_mem' := inR_const E 0 E.zero_mem
  neg_mem' := inR_neg

end GlobalTheory.FN.RingMem

theorem GlobalTheory.FN.mem_ring_iff_inR :
    ∀ E : Subring ℂ, (∀ f : ℍ → ℂ, f ∈ GlobalTheory.FN.ring E ↔ InR E f) ∧ ∀ c ∈ E, InR E fun _ => c := by
  intro E
  refine ⟨fun f => ⟨fun h => ?_, mem_ring_of_inR⟩, fun c hc => GlobalTheory.FN.RingMem.inR_const E c hc⟩
  have hle : GlobalTheory.FN.ring E ≤ GlobalTheory.FN.RingMem.inRSubring E :=
    (Subring.closure_le).mpr fun g hg => hg
  exact hle h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTowerUnionAdjoinOfGaloisFixed
section
noncomputable section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.K5.TowerFix

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem exists_eq_of_isIntegral_div (h : IsClo p Ω) (T : Tower p Ω) {n : ℕ} (hn : 1 ≤ n)
    (ι : On p n →ₐ[O0 p] Ω) (hι : IsEmb T n ι) (wb wc : On p n) (hc : ι wc ≠ 0) {x : Ω}
    (hx : IsIntegral (O0 p) x) (hxe : x = ι wb / ι wc) : ∃ w : On p n, ι w = x := by
  have hinj : Function.Injective ι := GlobalTheory.T.tower_embedding_injective p Ω h T n hn ι hι
  obtain ⟨hdom, hdvr, -⟩ := GlobalTheory.K5.OnDVR.isDVR_On p n hn
  let K := FractionRing (On p n)
  let φ : K →+* Ω := IsFractionRing.lift (g := ι.toRingHom) hinj
  have hφ : ∀ w : On p n, φ (algebraMap (On p n) K w) = ι w := fun w =>
    IsFractionRing.lift_algebraMap _ _
  let φa : K →ₐ[O0 p] Ω :=
    { φ with
      commutes' := fun r => by
        have : algebraMap (O0 p) K r = algebraMap (On p n) K (algebraMap (O0 p) (On p n) r) :=
          IsScalarTower.algebraMap_apply _ _ _ r
        show φ (algebraMap (O0 p) K r) = _
        rw [this, hφ, AlgHom.commutes] }
  have hwc0 : wc ≠ 0 := fun h0 => hc (by rw [h0, map_zero])
  let z : K := algebraMap (On p n) K wb / algebraMap (On p n) K wc
  have hz : φa z = x := by
    show φ z = x
    simp only [z, map_div₀, hφ, hxe]
  have hzi : IsIntegral (O0 p) z := by
    rw [← isIntegral_algHom_iff φa φa.toRingHom.injective, hz]; exact hx
  have hzi' : IsIntegral (On p n) z := hzi.tower_top
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 hzi'
  refine ⟨w, ?_⟩
  rw [← hφ, hw]
  exact hz

end GlobalTheory.K5.TowerFix

theorem GlobalTheory.K5.mem_towerAlg_of_fixed :
    ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
      ∀ (T : Tower p Ω) (x : (integralClosure (O0 p) Ω)),
        (∀ g ∈ ⨅ n, Gn T n, g (x : Ω) = x) → x ∈ towerAlg T := by
  intro p _ Ω _ _ h T x hx
  haveI := h.clo
  haveI := h.alg
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo h
  rw [GlobalTheory.T.mem_towerUnionAdjoinIntegralClosure_iff p Ω T x]
  set B := Algebra.adjoin (O0 p) (Set.range T.ζ ∪ Set.range T.qq)
  obtain ⟨b, hb, c, hc, hc0, hbc⟩ := GlobalTheory.mem_adjoin_div_of_fixed (O0 p) Ω h.inj
    (Set.range T.ζ ∪ Set.range T.qq) (x : Ω) (fun g hg => hx g (by
      rw [Subgroup.mem_iInf]
      intro n
      exact ⟨hg _ (Or.inl ⟨n, rfl⟩), hg _ (Or.inr ⟨n, rfl⟩)⟩))
  obtain ⟨m, hm⟩ := GlobalTheory.K5.Level.exists_mem_bn T hb
  obtain ⟨k, hk⟩ := GlobalTheory.K5.Level.exists_mem_bn T hc
  set N := max m k + 1
  have hN : 1 ≤ N := Nat.le_add_left 1 _
  have hbN : b ∈ GlobalTheory.K5.Level.Bn T N :=
    GlobalTheory.K5.Level.bn_mono T (le_trans (le_max_left m k) (Nat.le_succ _)) hm
  have hcN : c ∈ GlobalTheory.K5.Level.Bn T N :=
    GlobalTheory.K5.Level.bn_mono T (le_trans (le_max_right m k) (Nat.le_succ _)) hk
  obtain ⟨ι, hι⟩ := GlobalTheory.K5.Basic.exists_isEmb T N
  obtain ⟨wb, hwb⟩ := GlobalTheory.K5.Level.bn_le_range T N ι hι hbN
  obtain ⟨wc, hwc⟩ := GlobalTheory.K5.Level.bn_le_range T N ι hι hcN
  obtain ⟨w, hw⟩ := GlobalTheory.K5.TowerFix.exists_eq_of_isIntegral_div h T hN ι hι wb wc
    (by rw [show ι wc = c from hwc]; exact hc0) x.2
    (by rw [hbc, show ι wb = b from hwb, show ι wc = c from hwc])
  rw [← hw]
  exact GlobalTheory.K5.Level.bn_le_B T N (GlobalTheory.K5.Level.range_le_bn T N ι hι w)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerMemAdjoinJOfSlTwoIntInvariantStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularTower_mem_adjoin_j_of_slTwoInt_invariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ f : X.K, (∀ γ : SL(2, ℤ), X.sl (ofSL γ) f = f) → f ∈ IntermediateField.adjoin Ω {X.jK} := by
  first | exact @GlobalTheory.KZ.LevelOneFrac.mem_adjoin_of_sl_inv | exact GlobalTheory.KZ.LevelOneFrac.mem_adjoin_of_sl_inv | (intros; apply GlobalTheory.KZ.LevelOneFrac.mem_adjoin_of_sl_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonLthPowerReductionAlmostAllPrimesStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonLthPower_reduction_almost_all_primes : ∀ {F : Type} [Field F] [CharZero F] [IsAlgClosed F] [Algebra.IsAlgebraic ℚ F] {K : Type} [Field K] [Algebra F K] (t : K), Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) K → ∀ (l : ℕ), l.Prime → ∀ (s : K), (∀ u : K, u ^ l ≠ s) → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F, ((q : ℕ) : F) ∈ V.nonunits → ∀ W : ValuationSubring K, ((∀ a : F, algebraMap F K a ∈ W ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1)) → ∀ (h : K) (c : F), h ≠ 0 → c ≠ 0 → c ∈ V → c⁻¹ ∈ V → ¬ W.valuation (s * h ^ l - algebraMap F K c) < 1 := by
  first | exact @GlobalTheory.LthPowRed.not_valuation_lt_one | exact GlobalTheory.LthPowRed.not_valuation_lt_one | (intros; apply GlobalTheory.LthPowRed.not_valuation_lt_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaProductSiegelModularSTransform
section
open Complex
open UpperHalfPlane hiding I
open scoped Real MatrixGroups

noncomputable section

namespace GlobalTheory.Sieg.ThInv

open GlobalTheory.ThetaWeberRoad GlobalTheory.ThetaWeberRoad.OddDeriv

theorem exp_pi_I_half : cexp (π * I / 2) = I := by
  rw [show (π : ℂ) * I / 2 = π / 2 * I by ring, Complex.exp_pi_div_two_mul_I]

theorem oddTheta_eq (τ : ℍ) (z : ℂ) : oddTheta τ z = I * ModularForm.eta (τ : ℂ) * th z τ := by
  have hB := hasProd_tailProd τ (cexp (2 * π * I * z))
  have hC := hasProd_tailProd τ (cexp (-(2 * π * I * z)))
  have hP : ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * ee z) * (1 - ee (τ : ℂ) ^ (n + 1) * (ee z)⁻¹) =
      tailProd τ (cexp (2 * π * I * z)) * tailProd τ (cexp (-(2 * π * I * z))) := by
    rw [← (hB.mul hC).tprod_eq]
    refine tprod_congr fun n => ?_
    rw [ModularForm.eta_q_eq_pow, Complex.exp_neg]
    rfl
  have hT1 : tailProd τ 1 = ∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) := by
    simp [tailProd]
  have h1 : cexp (π * I * (τ : ℂ) / 4 + π * I * (z + 1 / 2)) =
      I * Function.Periodic.qParam 24 (τ : ℂ) * ee ((τ : ℂ) / 12) * ee (z / 2) := by
    rw [Function.Periodic.qParam, ee, ee]
    conv_rhs => rw [← exp_pi_I_half]
    rw [exp_pi_I_half]
    nth_rewrite 3 [← exp_pi_I_half]
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; push_cast; ring
  have h2 : ee (-z / 2) = ee (z / 2) * cexp (-(2 * π * I * z)) := by
    rw [ee, ee, ← Complex.exp_add]
    congr 1; ring
  rw [oddTheta, jacobiTheta₂_shift GlobalTheory.JacobiTriple.tripleProduct, th, hP, ModularForm.eta, ← hT1, h1, h2]
  ring

theorem sqrt_eq (τ : ℍ) : (Complex.sqrt I)⁻¹ * Complex.sqrt (τ : ℂ) = (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have h0 : -I * (τ : ℂ) ≠ 0 := mul_ne_zero (neg_ne_zero.2 I_ne_zero) hτ
  have hre : 0 < (-I * (τ : ℂ)).re := by simpa using τ.im_pos
  have ha := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre))
  have hl : log (I * (-I * (τ : ℂ))) = log I + log (-I * (τ : ℂ)) := by
    rw [Complex.log_mul_eq_add_log_iff I_ne_zero h0, Complex.arg_I]
    constructor <;> linarith [ha.1, ha.2, Real.pi_pos]
  rw [show I * (-I * (τ : ℂ)) = τ by linear_combination (-(τ : ℂ)) * I_sq] at hl
  rw [Complex.sqrt, Complex.sqrt, Complex.cpow_def_of_ne_zero I_ne_zero, Complex.cpow_def_of_ne_zero hτ,
    Complex.cpow_def_of_ne_zero h0, hl,
    ← Complex.exp_neg, ← Complex.exp_add]
  congr 1; ring

theorem eta_S (τ : ℍ) :
    ModularForm.eta (-1 / (τ : ℂ)) = (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * ModularForm.eta (τ : ℂ) := by
  have h := ModularForm.eta_comp_eq_csqrt_I_inv τ.2
  rw [← sqrt_eq, mul_assoc]
  simpa using h

theorem coe_S_smul (τ : ℍ) : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / (τ : ℂ) := by
  rw [UpperHalfPlane.modular_S_smul]
  simp [neg_div]

theorem oddTheta_S (τ : ℍ) (z : ℂ) :
    oddTheta (ModularGroup.S • τ) (z / (τ : ℂ)) =
      -I * (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * ee (z ^ 2 / (2 * (τ : ℂ))) * oddTheta τ z := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have h0 : (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => mul_ne_zero (neg_ne_zero.2 I_ne_zero) hτ h.1
  have hI : -I = cexp (-(π * I / 2)) := by
    rw [Complex.exp_neg, exp_pi_I_half, Complex.inv_I]
  rw [oddTheta, oddTheta, coe_S_smul, jacobiTheta₂_functional_equation (z + ((τ : ℂ) + 1) / 2) τ,
    show z / (τ : ℂ) + (-1 / (τ : ℂ) + 1) / 2 = (z + ((τ : ℂ) + 1) / 2) / τ + -1 / (τ : ℂ) by
      field_simp; ring, jacobiTheta₂_add_left']
  generalize jacobiTheta₂ ((z + ((τ : ℂ) + 1) / 2) / τ) (-1 / (τ : ℂ)) = J
  generalize (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) = s at h0 ⊢
  have hE : ∀ A B C D : ℂ, cexp A * s * cexp B * (cexp C * (1 / s * cexp D * J)) =
      cexp (A + B + C + D) * J := by
    intro A B C D
    simp only [Complex.exp_add]
    field_simp
  rw [ee]
  conv_rhs => rw [hI]
  rw [hE, ← mul_assoc, ← Complex.exp_add]
  congr 2
  field_simp
  ring

theorem th_S : ∀ (τ : ℍ) (z : ℂ), th (z / (τ : ℂ)) (ModularGroup.S • τ) =
    -Complex.I * ee (z ^ 2 / (2 * (τ : ℂ))) * th z τ := by
  intro τ z
  have h := oddTheta_S τ z
  rw [oddTheta_eq, oddTheta_eq] at h
  have hne : I * ModularForm.eta ((ModularGroup.S • τ : ℍ) : ℂ) ≠ 0 :=
    mul_ne_zero I_ne_zero (ModularForm.eta_ne_zero (ModularGroup.S • τ).2)
  refine mul_left_cancel₀ hne ?_
  rw [h, coe_S_smul, eta_S]
  ring

end GlobalTheory.Sieg.ThInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveHahnSeriesNotZeroDivisorModPrimePow
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory

theorem primCan_mul_dvd {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (c : Ω) (a b : HahnSeries ℚ Ω)
    (ha : ∀ r, a.coeff r ∈ A) (hb : ∀ r, ∃ z ∈ A, b.coeff r = c * z) :
    ∀ r, ∃ z ∈ A, (a * b).coeff r = c * z := by
  intro r
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_induction _ (fun x => ∃ z ∈ A, x = c * z) ?_ ?_ ?_
  · rintro x y ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨z + w, A.add_mem _ _ hz hw, by ring⟩
  · exact ⟨0, A.zero_mem, by simp⟩
  · intro ij _
    obtain ⟨z, hz, e⟩ := hb ij.2
    exact ⟨a.coeff ij.1 * z, A.mul_mem _ _ (ha _) hz, by rw [e]; ring⟩

theorem primCan : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω),
    ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n L : ℕ) (P φ : HahnSeries ℚ Ω), 0 < L → Prim A P →
    (∀ r : ℚ, P.coeff r ≠ 0 → (r * L).den = 1) → (∀ r, φ.coeff r ∈ A) →
    (∀ r, CgA A l n ((φ * P).coeff r) 0) → ∀ r, CgA A l n (φ.coeff r) 0 := by
  intro Ω _ _ _ l _ A hl n L P φ hL hP hden hφ hφP
  obtain ⟨Q, hQ, -, hQP⟩ := GlobalTheory.T.primitive_hahnSeries_invertible_mod_prime_pow l A hl n L P hL hP hden
  have h1 : ∀ r, ∃ z ∈ A, (Q * P - 1).coeff r = (l : Ω) ^ n * z := by
    intro r
    obtain ⟨z, hz, e⟩ := hQP r
    exact ⟨z, hz, by rw [HahnSeries.coeff_sub]; exact e⟩
  have h2 := primCan_mul_dvd A _ φ _ hφ h1
  have h3 : ∀ r, ∃ z ∈ A, (Q * (φ * P)).coeff r = (l : Ω) ^ n * z := by
    refine primCan_mul_dvd A _ Q _ hQ ?_
    intro r
    obtain ⟨z, hz, e⟩ := hφP r
    exact ⟨z, hz, by rw [← e, sub_zero]⟩
  intro r
  obtain ⟨z, hz, ez⟩ := h3 r
  obtain ⟨w, hw, ew⟩ := h2 r
  have hid : φ = Q * (φ * P) - φ * (Q * P - 1) := by ring
  refine ⟨z - w, sub_mem hz hw, ?_⟩
  rw [sub_zero, hid, HahnSeries.coeff_sub, ez, ew]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankLevelIdempotentLowerBoundGenericStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_levelIdempotent_lower_bound_generic : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), IsGeneric ρ → ∀ L : Lev g N, (1 - 1 / (g : ℝ)) * (g : ℝ) ^ (if L.sharp = true then L.k else 0) ≤ (rk ρ L.e : ℝ) := by
  first | exact @GlobalTheory.BadShare.rk_lev_lower | exact GlobalTheory.BadShare.rk_lev_lower | (intros; apply GlobalTheory.BadShare.rk_lev_lower <;> assumption)
end

