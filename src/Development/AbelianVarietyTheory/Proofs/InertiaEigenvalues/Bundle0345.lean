import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0178
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0198
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0324
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0069
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import GroundTheory.LocalFields.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeAinfSandwichInvertPi
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0323
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0206

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesEqPolynomialModPrime
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PolyRoot

theorem key_exp (l : ℕ) [Fact l.Prime] (h : ℕ) (P : ℝ) (hP : 0 < P) (k : ℤ) :
    P ^ ((l:ℝ) ^ k) * P ^ (((l:ℝ) ^ h - 1) * (l:ℝ) ^ k) = P ^ ((l:ℝ) ^ (k + h)) := by
  have hl : (l:ℝ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  rw [← Real.rpow_add hP, zpow_add₀ hl, zpow_natCast]
  congr 1; ring

theorem rho_pow (l : ℕ) [Fact l.Prime] (h D n : ℕ) (P : ℝ) (hP : 0 ≤ P) :
    (P ^ (((l:ℝ) ^ h - 1) / (l:ℝ) ^ D)) ^ (l ^ n) = P ^ (((l:ℝ) ^ h - 1) * (l:ℝ) ^ ((n:ℤ) - D)) := by
  have hl : (l:ℝ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  rw [← Real.rpow_natCast, ← Real.rpow_mul hP, zpow_sub₀ hl, zpow_natCast, zpow_natCast]
  congr 1; push_cast; ring

theorem poly_root_mod_l : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]) (σ : Fl l), 1 ≤ h → μ ≠ 0 → sh σ = l → ∃ (t : ℂ_[l]) (D E M : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ), t ≠ 0 ∧ M + h ≤ E ∧ (∀ k, k ≤ E → ‖a k‖ ≤ 1) ∧ ‖a (M + h)‖ = 1 ∧ ‖(l : ℂ_[l])‖ ≤ ρ ∧ ρ < 1 ∧ ‖(l : ℂ_[l])‖ * ρ ^ l ^ D = ‖(l : ℂ_[l])‖ ^ l ^ h ∧ ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ ∧ (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) ∧ ∀ u : Fl l, ‖∑ i : Fin h, μ i * lam h i (σ * u ^ l ^ D) - t * ∑ k ∈ Finset.range (E + 1), a k * sh u ^ l ^ k‖ ≤ ‖(l : ℂ_[l])‖ * ‖t‖ := by
  intro l _ h μ σ h1 hμ hσ
  obtain ⟨pwadd, pwmul, pwzero, pwcomp, pwnat, pwpow, pwnorm⟩ := GlobalTheory.T.tiltFrobeniusIntegerPower_laws l
  obtain ⟨sh1, sh0, shmul, shpow, shle, shsurj, shadd, shneg⟩ := GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l
  obtain ⟨m, hm, ⟨k0, hk0⟩, hsum⟩ := GlobalTheory.T.exists_coeff_hasSum_untiltFrobeniusCombination l h μ h1 hμ
  obtain ⟨P, hPd⟩ : ∃ P : ℝ, P = ‖(l : ℂ_[l])‖ := ⟨_, rfl⟩
  rw [← hPd]
  have hP0 : 0 < P := hPd ▸ norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  have hP1 : P < 1 := hPd ▸ GlobalTheory.RingBasics.norm_p_lt
  have hσn : ‖sh σ‖ = P := by rw [hσ, hPd]
  obtain ⟨α, hα⟩ : ∃ α : ℤ → ℂ_[l], ∀ k, α k = m k * sh (pw k σ) := ⟨_, fun _ => rfl⟩
  obtain ⟨β, hβd⟩ : ∃ β : ℤ → ℝ, ∀ k, β k = ‖α k‖ := ⟨_, fun _ => rfl⟩
  have hshσ : ∀ k : ℤ, ‖sh (pw k σ)‖ = P ^ ((l:ℝ) ^ k) := fun k => by rw [pwnorm, hσn]
  have hβ : ∀ k, β k = ‖m k‖ * P ^ ((l:ℝ) ^ k) := fun k => by
    rw [hβd, hα, norm_mul, hshσ]
  have hkey : ∀ k : ℤ, β k * P ^ (((l:ℝ) ^ h - 1) * (l:ℝ) ^ k) = P * β (k + h) := fun k => by
    rw [hβ, hβ, hm k, norm_mul, ← hPd, ← key_exp l h P hP0 k]; ring
  have hσlt : ‖sh σ‖ < 1 := hσn ▸ hP1
  have hαsum : Summable α := by
    have := (hsum σ hσlt).summable
    rwa [show (fun k : ℤ => m k * sh (pw k σ)) = α from funext fun k => (hα k).symm] at this
  have hβt : Filter.Tendsto β Filter.cofinite (nhds 0) := by
    have := (hαsum.tendsto_cofinite_zero).norm
    rw [norm_zero] at this
    rwa [show (fun k => ‖α k‖) = β from funext fun k => (hβd k).symm] at this
  have hβne : ∃ k, β k ≠ 0 := ⟨k0, by
    rw [hβ]; exact mul_ne_zero (norm_ne_zero_iff.2 hk0) (Real.rpow_pos_of_pos hP0 _).ne'⟩
  have hβ0 : ∀ k, 0 ≤ β k := fun k => by rw [hβd]; exact norm_nonneg _
  obtain ⟨D, E, M, hD, hME, hpos, hmax, hstrict, htail⟩ :=
    GlobalTheory.T.window_around_last_max_null_sequence β P h hP0 hβ0 hβne hβt
  obtain ⟨N, hN⟩ : ∃ N : ℤ, N = ((M + h : ℕ) : ℤ) - D := ⟨_, rfl⟩
  rw [← hN] at hpos hmax hstrict htail
  have htn : ‖α N‖ = β N := (hβd N).symm
  have ht0 : α N ≠ 0 := by intro h0; rw [← norm_eq_zero, htn] at h0; linarith
  have hl2 : (2:ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have hlD : (0:ℝ) < (l:ℝ) ^ D := by positivity
  have hnorm_a : ∀ k : ℕ, ‖α ((k:ℤ) - D) / α N‖ = β ((k:ℤ) - D) / β N := fun k => by
    rw [norm_div, htn, ← hβd]
  have hprod : ∀ k : ℕ, ‖α ((k:ℤ) - D) / α N‖ * (P ^ (((l:ℝ) ^ h - 1) / (l:ℝ) ^ D)) ^ (l ^ k)
      = P * β ((k:ℤ) - D + h) / β N := fun k => by
    rw [hnorm_a, rho_pow l h D k P hP0.le, div_mul_eq_mul_div, hkey]
  refine ⟨α N, D, E, M, fun k : ℕ => α ((k:ℤ) - D) / α N, P ^ (((l:ℝ) ^ h - 1) / (l:ℝ) ^ D),
    ht0, hME, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k _
    show ‖α ((k:ℤ) - D) / α N‖ ≤ 1
    rw [hnorm_a, div_le_one hpos]; exact hmax _
  · show ‖α (((M + h : ℕ) : ℤ) - D) / α N‖ = 1
    rw [← hN, div_self ht0, norm_one]
  · have he : ((l:ℝ) ^ h - 1) / (l:ℝ) ^ D ≤ 1 := by
      rw [div_le_one hlD]
      have : (l:ℝ) ^ h ≤ (l:ℝ) ^ D := pow_le_pow_right₀ (by linarith) hD
      linarith
    calc P = P ^ (1:ℝ) := (Real.rpow_one P).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hP0 hP1.le he
  · have hq : (l:ℝ) ≤ (l:ℝ) ^ h := le_self_pow₀ (by linarith) (by omega)
    exact Real.rpow_lt_one hP0.le hP1 (div_pos (by linarith) hlD)
  · rw [rho_pow l h D D P hP0.le, sub_self, zpow_zero, mul_one, ← Real.rpow_natCast P (l ^ h)]
    rw [show P * P ^ ((l:ℝ) ^ h - 1) = P ^ ((1:ℝ) + ((l:ℝ) ^ h - 1)) by
      rw [Real.rpow_add hP0, Real.rpow_one]]
    congr 1; push_cast; ring
  · show ‖α ((M:ℤ) - D) / α N‖ * _ = P
    rw [hprod, show (M:ℤ) - D + h = N by rw [hN]; push_cast; ring, mul_div_assoc,
      div_self hpos.ne', mul_one]
  · intro k hk _
    show ‖α ((k:ℤ) - D) / α N‖ * _ < P
    rw [hprod, div_lt_iff₀ hpos]
    exact mul_lt_mul_of_pos_left (hstrict _ (by omega)) hP0
  · intro u
    have hx : ‖sh (σ * u ^ l ^ D)‖ < 1 := by
      rw [shmul, shpow, norm_mul, norm_pow, hσn]
      calc P * ‖sh u‖ ^ l ^ D ≤ P * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) (shle u)) hP0.le
        _ < 1 := by rw [mul_one]; exact hP1
    have hS := hsum _ hx
    have hf : ∀ k : ℤ, m k * sh (pw k (σ * u ^ l ^ D)) = α k * sh (pw (k + D) u) := fun k => by
      rw [hα, pwmul, ← pwnat D u, ← pwcomp, shmul]; ring
    rw [show (fun k : ℤ => m k * sh (pw k (σ * u ^ l ^ D))) = fun k => α k * sh (pw (k + D) u)
      from funext hf] at hS
    have htr := GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le ℂ_[l] ℤ (fun k => α k * sh (pw (k + D) u)) _
      ((Finset.range (E + 1)).image (fun k : ℕ => (k:ℤ) - D)) (P * ‖α N‖)
      (mul_nonneg hP0.le (norm_nonneg _)) hS (by
        intro j hj
        have hj' : j < -(D:ℤ) ∨ (E:ℤ) - D < j := by
          by_contra hc
          push_neg at hc
          apply hj
          rw [Finset.mem_image]
          exact ⟨(j + D).toNat, Finset.mem_range.2 (by omega), by omega⟩
        show ‖α j * sh (pw (j + D) u)‖ ≤ P * ‖α N‖
        rw [norm_mul, ← hβd, htn]
        exact (mul_le_of_le_one_right (hβ0 j) (shle _)).trans (htail j hj'))
    have heq : ∑ j ∈ (Finset.range (E + 1)).image (fun k : ℕ => (k:ℤ) - D), α j * sh (pw (j + D) u)
        = α N * ∑ k ∈ Finset.range (E + 1), α ((k:ℤ) - D) / α N * sh u ^ l ^ k := by
      rw [Finset.sum_image (fun x _ y _ hxy => by simpa using hxy), Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sub_add_cancel, pwnat, shpow]
      field_simp
    rw [heq] at htr
    exact htr

end GlobalTheory.PolyRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperRamificationGroupOneEqTopOfExponentPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem ringChar_residue_eq_of_ordIs (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p e : ℕ) (hp : p.Prime) (he : 0 < e) (h : OrdIs F p e) :
    ringChar 𝓀[F] = p := by
  have hnu : ¬ IsUnit (p : 𝒪[F]) := by
    intro hu
    have := (IsDiscreteValuationRing.addVal_eq_zero_of_unit (hu.unit))
    unfold OrdIs at h
    simp at this
    rw [this] at h
    norm_cast at h
    omega
  have hm : (p : 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F] := hnu
  have h0 : ((p : ℕ) : 𝓀[F]) = 0 := by
    rw [← map_natCast (IsLocalRing.residue 𝒪[F]), IsLocalRing.residue_eq_zero_iff]
    exact hm
  have hd : ringChar 𝓀[F] ∣ p := (ringChar.spec 𝓀[F] p).mp h0
  rcases (Nat.dvd_prime hp).mp hd with h1 | h1
  · exact absurd h1 CharP.ringChar_ne_one
  · exact h1

theorem upperRamificationGroup_one_eq_top_of_exponent :
    ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M]
      [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M]
      [FiniteDimensional F M] [IsGalois F M] (p e : ℕ), p.Prime → 0 < e → OrdIs F p e →
      upperRamificationGroup F M 0 = ⊤ → (∀ σ : M ≃ₐ[F] M, σ ^ p = 1) → upperRamificationGroup F M 1 = ⊤ := by
  intro F M _ _ _ _ _ _ _ _ _ _ _ _ p e hp he hord h0 hexp
  rw [upperRamificationGroup_zero] at h0
  have hchar := ringChar_residue_eq_of_ordIs F p e hp he hord
  have hcop := coprime_card_lowerRamificationGroup_zero_quotient F M
  rw [hchar] at hcop
  have h1 : lowerRamificationGroup F M 1 = ⊤ := by
    rw [eq_top_iff]
    intro σ _
    have hσ0 : σ ∈ lowerRamificationGroup F M 0 := by rw [h0]; trivial
    set q : lowerRamificationGroup F M 0 ⧸
        (lowerRamificationGroup F M 1).subgroupOf (lowerRamificationGroup F M 0) :=
      QuotientGroup.mk ⟨σ, hσ0⟩ with hq
    have hqp : q ^ p = 1 := by
      rw [hq, ← QuotientGroup.mk_pow]
      have : (⟨σ, hσ0⟩ : lowerRamificationGroup F M 0) ^ p = 1 := Subtype.ext (by simpa using hexp σ)
      rw [this, QuotientGroup.mk_one]
    have hqc : q ^ Nat.card (lowerRamificationGroup F M 0 ⧸
        (lowerRamificationGroup F M 1).subgroupOf (lowerRamificationGroup F M 0)) = 1 := pow_card_eq_one'
    have hg : q ^ Nat.gcd _ p = 1 := pow_gcd_eq_one.mpr ⟨hqc, hqp⟩
    rw [hcop, pow_one, hq, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hg
    exact hg
  have hphi0 : herbrandPhi F M 0 = 0 := by simp [herbrandPhi]
  have hphi1 : herbrandPhi F M 1 = 1 := by
    have := herbrandPhi_of_mem_Icc (K := F) (L := M) 0 (u := 1) (by norm_num)
    have h1' : lowerRamificationGroup F M (((0 : ℕ) : ℤ) + 1) = ⊤ := by simpa using h1
    rw [h1', Subgroup.relIndex_top_left] at this
    simpa [hphi0] using this
  rw [← hphi1, upperRamificationGroup_herbrandPhi, ← Nat.cast_one, lowerRamificationGroupReal_natCast]
  simpa using h1
end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet

namespace GlobalTheory.NewPrime

section General

def rect {Λ B : Type} [CommRing Λ] [AddCommGroup B] [Module Λ B] {r a : ℕ} (Z : Matrix (Fin r) (Fin a) Λ) (x : Fin a → B) :
    Fin r → B := fun c => ∑ j, Z c j • x j

abbrev what₂ {Λ μ ν : Type} [CommRing Λ] (Z : μ → ν → Λ) : Submodule Λ (ν → Λ) := Submodule.span Λ (Set.range Z)

def Cob {Γ Λ M : Type} [Group Γ] [CommRing Λ] [AddCommGroup M] [Module Λ M] (ρ : Representation Λ Γ M) (f : Γ → M) : Prop :=
  ∃ m, ∀ g, f g = ρ g m - m

variable (Λ : Type) [CommRing Λ] {Y Y' : Type} [AddCommGroup Y] [Module Λ Y] [AddCommGroup Y'] [Module Λ Y'] {n : ℕ}

def Bal (β : Y →+ Y' →+ ZMod n) : Prop := ∀ (a : Λ) y y', β (a • y) y' = β y (a • y')

def Perf (β : Y →+ Y' →+ ZMod n) : Prop :=
  Bal Λ β ∧ (∀ y, (∀ y', β y y' = 0) → y = 0) ∧ ∀ y', (∀ y, β y y' = 0) → y' = 0

def vecPair (r : ℕ) (β : Y →+ Y' →+ ZMod n) : (Fin r → Y) →+ (Fin r → Y') →+ ZMod n :=
  ∑ c : Fin r, ((β.comp (Pi.evalAddMonoidHom (fun _ => Y) c)).flip.comp (Pi.evalAddMonoidHom (fun _ => Y') c)).flip

theorem vecPair_apply (r : ℕ) (β : Y →+ Y' →+ ZMod n) (x : Fin r → Y) (y : Fin r → Y') :
    vecPair r β x y = ∑ c, β (x c) (y c) := by
  simp [vecPair, AddMonoidHom.finset_sum_apply]

def CupB {Γ M M' : Type} [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [AddCommGroup M'] (χ : Γ → ZMod n)
    (act : Γ → M' → M') (P : M →+ M' →+ ZMod n) (x : Γ → M) (y : Γ → M') : Prop :=
  ∃ f : Γ → ZMod n, IsLocallyConstant f ∧ ∀ g h, P (x g) (act g (y h)) = χ g * f h - f (g * h) + f g

end General

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i)

def Kills (A : Type) [CommRing A] [Algebra (X.O0 i) A] : Prop := ∀ x ∈ idl i, algebraMap (X.O0 i) A x = 0

section Coef

variable {Λ : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)

def SelC (Y : Type) [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y] (Q : Finset (PlE D.host))
    (f : GE N → Fin D.R.r → Y) : Prop :=
  ∃ z : Z1 (repOn (Tgl i s) κ Y), z.1 = f ∧ Submodule.Quotient.mk z ∈ selOn bkP i (Tgl i s) κ Y Q

def Univ (Q : Finset (PlE D.host)) {a : ℕ} (Φ : Matrix (Fin a) (Fin a) Λ) (Z : GE N → Matrix (Fin D.R.r) (Fin a) Λ) : Prop :=
  ∀ (Y : Type) [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y],
    (∀ x : Fin a → Y, matAct Φ x = 0 → SelC bkP i s κ Y Q fun g => rect (Z g) x) ∧
    (∀ x : Fin a → Y, matAct Φ x = 0 → Cob (repOn (Tgl i s) κ Y) (fun g => rect (Z g) x) → x = 0) ∧
    ∀ f, SelC bkP i s κ Y Q f → ∃ x : Fin a → Y, matAct Φ x = 0 ∧
      Cob (repOn (Tgl i s) κ Y) fun g => f g - rect (Z g) x

variable (ρ : GE N →* GL (Fin D.R.r) (X.O0 i))

section Dual

variable {Y Y' : Type} [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y]
  [AddCommGroup Y'] [Module Λ Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1)))
  (Q : Finset (PlE D.host))

def DualSel (y : Z1 (repOn ρ κ⁻¹ Y')) : Prop :=
  (∀ v, v ∉ placesOver D.host.E (X.l i) → v ∉ Spl i → v ∉ Q → ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 v), y.1 τ = 0) ∧
  (∀ v, v ∈ Spl i ∨ v ∈ Q → ∃ m, ∀ g ∈ DecV N v, y.1 g = repOn ρ κ⁻¹ Y' g m - m) ∧
  ∀ v ∈ placesOver D.host.E (X.l i), ∀ x : Z1 ((repOn (Tgl i s) κ Y).comp (DecV N v).subtype),
    Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) κ Y v →
    CupB (fun g : DecV N v => ((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g.1 : (ZMod (X.l i ^ (nu X i + 1)))ˣ) :
        ZMod (X.l i ^ (nu X i + 1))))
      (fun g m => repOn ρ κ⁻¹ Y' g.1 m) (vecPair D.R.r β) x.1 (fun g => y.1 g.1)

def DualCl : Set (H1 (repOn ρ κ⁻¹ Y')) := {c | ∃ y, DualSel bkP i s κ ρ β Q y ∧ c = Submodule.Quotient.mk y}

end Dual

def OrderFormula (Q : Finset (PlE D.host)) : Prop :=
  ∀ (Y Y' : Type) [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    [AddCommGroup Y'] [Module Λ Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] [Finite Y']
    (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1))), Perf Λ β →
    Finite (DualCl bkP i s κ ρ β Q) ∧ Nat.card (selOn bkP i (Tgl i s) κ Y Q) =
      Nat.card (DualCl bkP i s κ ρ β Q) * ∏ v ∈ Q, Nat.card (H0 ((repOn ρ κ⁻¹ Y').comp (DecV N v).subtype))

def NoInvDual : Prop := ∀ (Y' : Type) [AddCommGroup Y'] [Module Λ Y'] (m : Fin D.R.r → Y'),
  (∀ g, repOn ρ κ⁻¹ Y' g m = m) → m = 0

def LocCountFin : Prop :=
  ∀ (Y : Type) [AddCommGroup Y] [Module Λ Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y],
    ∏ᶠ v ∈ placesOver D.host.E (X.l i), Nat.card (bkOn bkP i (Tgl i s) κ Y v) =
      (∏ᶠ v ∈ placesOver D.host.E (X.l i), Nat.card (H0 ((repOn (Tgl i s) κ Y).comp (DecV N v).subtype))) *
        Nat.card Y ^ (D.R.f * D.R.r)

omit [Algebra (X.O0 i) Λ] in

def IsChar {M : ℕ} {ι : Type} [Fintype ι] (ξ : ι → Λ) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) : Prop :=
  ∀ g, ((κ g : Λˣ) : Λ) * ∏ q, (1 + ξ q) ^ (Multiplicative.toAdd (d q g)).val = 1

def bform (x y : GE N → Fin D.R.r → Λ) (h : GE N) : Λ := x h ⬝ᵥ y h - x (cConj X h) ⬝ᵥ y (cConj X h)

end Coef

def NewPl (M : ℕ) (L : Subgroup (GE N)) (p : PlE D.host) (d : GE N →* Multiplicative (ZMod (X.l i ^ M))) (σ γ : GE N) : Prop :=
  (∀ v, Over p v → v ∉ X.S0 i) ∧ IsSplitPl D.host p ∧ normV p % (2 * X.l i ^ M) = 1 ∧ DecV N p ≤ L ∧
    IsOpen (d.ker : Set (GE N)) ∧ IsFrob (N.plOm.1 p) (normV p) σ ∧ γ ∈ Ine (F := D.host.E) (N.plOm.1 p) ∧
    d γ = Multiplicative.ofAdd 1

variable (X) in

def two (g : GE N) : Bool → GE N := fun b => if b then cConj X g else g

end GlobalTheory.NewPrime
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionLayerIoCommutesFrobeniusGaloisStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachInclusionLayer_io_commutes_frobenius_galois : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R) (S : Type) [CommRing S] (f f' : RA LL →+* S), ((∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] WittVector.frobenius w)) → ∀ a, f (I.io (letφ R.φ₀ a)) = f' (I.io a)) ∧ ∀ g : ↥(GK K), (∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] AI.actW (g : GQ l) w)) → ∀ a, f (I.io (letγ (R.γ₀ (Γ.resΓ g)) a)) = f' (I.io a) := by
  first | exact @GlobalTheory.HWL.IoComm.main | exact GlobalTheory.HWL.IoComm.main | (intros; apply GlobalTheory.HWL.IoComm.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeAinfSandwichInvertPiStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachLattice_ainf_sandwich_invert_pi : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (E : WEt I) (Mo : NS E) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ → ∃ m : ℕ, Sand Mo T ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (AI.π₁ ^ m) : RA LL) := by
  first | exact @GlobalTheory.HWL.SandProof.sandwich | exact GlobalTheory.HWL.SandProof.sandwich | (intros; apply GlobalTheory.HWL.SandProof.sandwich <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLetterRingFrobeniusDecomposition
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.PhiDec

theorem phi_dec : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ a : AA K LL, ∃ c : Fin l → AA K LL, a = ∑ j : Fin l, (fun _ => ((1 : PowerSeries ↥(OL LL)) + PowerSeries.X) ^ (j : ℕ) : AA K LL) * W.φA (c j) := by
  intro D HW l _ K s LL h W a
  obtain ⟨χ, -, hφ, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  obtain ⟨hdvr, hcomp, hl0, hlu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  choose z hz using fun i : Let K => (GlobalTheory.Cyc.phi_free l ↥(OL LL) hl0 hlu (a i)).exists
  refine ⟨fun j i => z (i + 1) j, ?_⟩
  funext i
  rw [Finset.sum_apply]
  have hi : a i = a (i - 1 + 1) := by rw [sub_add_cancel]
  rw [hi, hz]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.mul_apply, LocWach.φA, letφ, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply]
  show _ = _ * ((HW l).W K s LL h).φ₀ _
  rw [hφ]

end GlobalTheory.NL.PhiDec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildLowerRamificationGroupAntitoneEventuallyBot
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem wild_antitone_and_eventually_bot :
    ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L], Antitone (wild K L) ∧ ∃ m, wild K L m = ⊥ := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _
  refine ⟨fun i j hij ↦ ?_, ?_⟩
  · exact lowerRamificationGroup_antitone K L (by simp only [add_le_add_iff_right, Nat.cast_le]; exact hij)
  · obtain ⟨n, hn⟩ := exists_lowerRamificationGroup_eq_bot K L
    exact ⟨n, hn _ (by omega)⟩

end GlobalTheory.PMon.Ram
end

