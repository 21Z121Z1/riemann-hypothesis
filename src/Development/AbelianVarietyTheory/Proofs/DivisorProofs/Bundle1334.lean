import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1101
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0210
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPairFormRatioLocalScalarNorm
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CxRegPair

variable {p : ℕ} [Fact p.Prime]

theorem sh_mul_sh_inv (G : HTGroup p) (c : G.Cˣ) : sh G (c : G.C) * sh G ((c⁻¹ : G.Cˣ) : G.C) = 1 := by
  simp only [sh]
  rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]

theorem commute_mul_inv_of_sim (G : HTGroup p) (β β₁ γ : G.Cˣ) (c : ℚ)
    (h : (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c * β)
    (h₁ : (γ : G.C) * β₁ * sh G γ = algebraMap ℚ G.C c * β₁) :
    Commute ((β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C)) (γ : G.C) := by
  have key : (γ : G.C) * ((β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C)) * ((β₁ : G.C) * sh G γ) =
      (β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C) * γ * ((β₁ : G.C) * sh G γ) := by
    calc (γ : G.C) * ((β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C)) * ((β₁ : G.C) * sh G γ)
        = (γ : G.C) * β * (((β₁⁻¹ : G.Cˣ) : G.C) * β₁) * sh G γ := by simp only [mul_assoc]
      _ = algebraMap ℚ G.C c * β := by rw [Units.inv_mul, mul_one, h]
      _ = (β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C c * β₁) := by
          rw [mul_assoc, ← mul_assoc ((β₁⁻¹ : G.Cˣ) : G.C), ← Algebra.commutes, mul_assoc, Units.inv_mul, mul_one, Algebra.commutes]
      _ = _ := by rw [← h₁]; simp only [mul_assoc]
  have hinv : ((β₁ : G.C) * sh G γ) * (sh G ((γ⁻¹ : G.Cˣ) : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C)) = 1 := by
    rw [mul_assoc, ← mul_assoc (sh G γ), sh_mul_sh_inv, one_mul, Units.mul_inv]
  show (β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C) * γ = γ * ((β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C))
  have := congrArg (· * (sh G ((γ⁻¹ : G.Cˣ) : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C))) key
  simp only [mul_assoc] at this hinv
  simp only [mul_assoc]
  rw [hinv, mul_one, mul_one] at this
  exact this.symm

theorem glue_pair (G : HTGroup p) (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) P.β x t) (g : G.GAf) (w : AwayP p) :
    ∃ (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) (lam : (w.1.adicCompletion ℚ)ˣ),
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) (P.γ : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = ((((compL G w (g⁻¹ * P.toAf x t hx P.self * g) : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) ((P.γ⁻¹ : G.Cˣ) : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = (((((compL G w (g⁻¹ * P.toAf x t hx P.self * g) : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ)⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) (P.β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop = algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (lam : w.1.adicCompletion ℚ) := by
  let φ := Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C)
  let u : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ :=
    ((compL G w g : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1
  let ν : (w.1.adicCompletion ℚ)ˣ :=
    ((compL G w g : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).2
  let xw : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ := Units.map (φ : AfP p ⊗[ℚ] G.C →* w.1.adicCompletion ℚ ⊗[ℚ] G.C) x
  let mY : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ := Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom P.γ
  let tw : (w.1.adicCompletion ℚ)ˣ := Units.map (AfP.eval w : AfP p →* w.1.adicCompletion ℚ) t
  have hT : ((compL G w (P.toAf x t hx P.self) : UPts G.star (w.1.adicCompletion ℚ)) :
      (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 = xw * mY * xw⁻¹ := by
    apply Units.ext
    show φ ((x : AfP p ⊗[ℚ] G.C) * inC G (AfP p) (P.γ : G.C) * ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) = _
    rw [map_mul, map_mul, glueL_evalT_inC]
    rfl
  have E : ((compL G w (g⁻¹ * P.toAf x t hx P.self * g) : UPts G.star (w.1.adicCompletion ℚ)) :
      (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 = (u⁻¹ * xw) * mY * (u⁻¹ * xw)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    change u⁻¹ * ((compL G w (P.toAf x t hx P.self) : UPts G.star (w.1.adicCompletion ℚ)) :
      (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 * u = _
    rw [hT]
    group
  refine ⟨u⁻¹ * xw, tw * ν⁻¹, ?_, ?_, ?_⟩
  · rw [E]; rfl
  · rw [E, show (u⁻¹ * xw * mY * (u⁻¹ * xw)⁻¹)⁻¹ = (u⁻¹ * xw) * mY⁻¹ * (u⁻¹ * xw)⁻¹ by group]
    rfl
  · have hu : ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
        (starT G.star (w.1.adicCompletion ℚ) ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C)).unop =
        algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) ((ν⁻¹ : (w.1.adicCompletion ℚ)ˣ) : w.1.adicCompletion ℚ) :=
      ((compL G w g)⁻¹).2
    have hxw : φ (x : AfP p ⊗[ℚ] G.C) * inC G (w.1.adicCompletion ℚ) (P.β : G.C) *
        (starT G.star (w.1.adicCompletion ℚ) (φ (x : AfP p ⊗[ℚ] G.C))).unop =
        algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (tw : w.1.adicCompletion ℚ) := by
      have h := congrArg φ hx
      rw [map_mul, map_mul, glueL_evalT_inC, glueL_evalT_starT, glueL_evalT_algebraMap] at h
      exact h
    have hk : (((u⁻¹ * xw : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ)) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
        ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) * φ (x : AfP p ⊗[ℚ] G.C) := rfl
    rw [hk, RingHom.map_mul (starT G.star (w.1.adicCompletion ℚ)), MulOpposite.unop_mul]
    calc _ = ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
          (φ (x : AfP p ⊗[ℚ] G.C) * inC G (w.1.adicCompletion ℚ) (P.β : G.C) *
          (starT G.star (w.1.adicCompletion ℚ) (φ (x : AfP p ⊗[ℚ] G.C))).unop) *
          (starT G.star (w.1.adicCompletion ℚ) ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C)).unop := by
          simp only [mul_assoc]
      _ = algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (tw : w.1.adicCompletion ℚ) *
          (((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
          (starT G.star (w.1.adicCompletion ℚ) ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C)).unop) := by
          rw [hxw, ← mul_assoc, ← Algebra.commutes, mul_assoc]
      _ = _ := by rw [hu, ← map_mul, Units.val_mul]

theorem local_pair_scalar_norm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → (∀ g, f g ≠ 0 → RegAf G g) → ∀ P₁ : Pair G, ∃ S : Finset ℕ, ∀ (P : Pair G), P.γ = P₁.γ → P.c = P₁.c → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (g : G.GAf), f (g⁻¹ * P.toAf x t hx P.self * g) ≠ 0 → ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ), Commute (z : ℚ_[ℓ] ⊗[ℚ] G.C) (inC G ℚ_[ℓ] (P₁.γ : G.C)) ∧ inC G ℚ_[ℓ] ((P.β : G.C) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] G.C) (u : ℚ_[ℓ]) * ((z : ℚ_[ℓ] ⊗[ℚ] G.C) * inC G ℚ_[ℓ] (P₁.β : G.C) * (starT G.star ℚ_[ℓ] (z : ℚ_[ℓ] ⊗[ℚ] G.C)).unop * inC G ℚ_[ℓ] ((P₁.β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G L f hf _ P₁
  have hdeg := P₁.reg.1
  have hsep := P₁.reg.2
  obtain ⟨Ω, hΩc, hΩ⟩ := GlobalTheory.T.exists_compact_support_twistedHeckeTestFunction p G L f hf
  have hev := eventually_compL_mem_intPts p G Ω hΩc
  have hlat := GlobalTheory.T.eventually_kottwitz_lattice_separable_minpoly p G P₁.γ hsep hdeg
  have hnorm := GlobalTheory.T.eventually_tauFixed_unit_centralizer_is_norm p G P₁.β P₁.sym P₁.γ (P₁.c : ℚ) P₁.sim hsep hdeg
  have hstab := GlobalTheory.FinClsLoc.intC_stab p G P₁.β
  obtain ⟨S, hS⟩ := GlobalTheory.FinClsLoc.exists_finset_forall_prime_awayP_padic p _ (hev.and (hlat.and (hnorm.and hstab)))
  refine ⟨S, fun P hγ hc x t hx g hfy ℓ _ hℓ => ?_⟩
  obtain ⟨w, ⟨hev', hlat', hnorm', hmul, hstar, hβi, hβi'⟩, ⟨e⟩⟩ := hS ℓ hℓ
  apply GlobalTheory.T.localTwistedNormConclusion_transfer_ringEquiv p G (w.1.adicCompletion ℚ) ℚ_[ℓ] e
  have hint := hev' _ (hΩ _ hfy)
  obtain ⟨k, lam, hk1, hk2, hk3⟩ := GlobalTheory.CxRegPair.glue_pair G P x t hx g w
  rw [hγ] at hk1 hk2
  obtain ⟨z, m, hz, hm, hm', hkzm⟩ := hlat' k (by rw [hk1]; exact hint.1) (by rw [hk2]; exact hint.2.1)
  have hcm : Commute ((P.β : G.C) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) (P₁.γ : G.C) := by
    have h := P.sim
    rw [hγ, hc] at h
    exact GlobalTheory.CxRegPair.commute_mul_inv_of_sim G P.β P₁.β P₁.γ (P₁.c : ℚ) h P₁.sim
  have hinv := starT_invol G (w.1.adicCompletion ℚ)
  have hbb : inC G (w.1.adicCompletion ℚ) ((P₁.β⁻¹ : G.Cˣ) : G.C) * inC G (w.1.adicCompletion ℚ) (P₁.β : G.C) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hβ' : (starT G.star (w.1.adicCompletion ℚ) (inC G (w.1.adicCompletion ℚ) (P₁.β : G.C))).unop = inC G (w.1.adicCompletion ℚ) (P₁.β : G.C) := by
    show (starT G.star (w.1.adicCompletion ℚ) ((1 : w.1.adicCompletion ℚ) ⊗ₜ (P₁.β : G.C))).unop = (1 : w.1.adicCompletion ℚ) ⊗ₜ (P₁.β : G.C)
    rw [starT_tmul]
    exact congrArg (TensorProduct.tmul ℚ (1 : w.1.adicCompletion ℚ)) P₁.sym
  have hY' : inC G (w.1.adicCompletion ℚ) (P₁.γ : G.C) * inC G (w.1.adicCompletion ℚ) (P₁.β : G.C) *
      (starT G.star (w.1.adicCompletion ℚ) (inC G (w.1.adicCompletion ℚ) (P₁.γ : G.C))).unop =
      algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (algebraMap ℚ (w.1.adicCompletion ℚ) (P₁.c : ℚ)) * inC G (w.1.adicCompletion ℚ) (P₁.β : G.C) := by
    have h := congrArg (inC G (w.1.adicCompletion ℚ)) P₁.sim
    rw [map_mul, map_mul, map_mul] at h
    have e1 : inC G (w.1.adicCompletion ℚ) (sh G (P₁.γ : G.C)) =
        (starT G.star (w.1.adicCompletion ℚ) (inC G (w.1.adicCompletion ℚ) (P₁.γ : G.C))).unop :=
      (starT_tmul G.star (w.1.adicCompletion ℚ) 1 _).symm
    have e2 : inC G (w.1.adicCompletion ℚ) (algebraMap ℚ G.C (P₁.c : ℚ)) =
        algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (algebraMap ℚ (w.1.adicCompletion ℚ) (P₁.c : ℚ)) := by
      rw [← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] w.1.adicCompletion ℚ ⊗[ℚ] G.C).commutes _
    rw [e1, e2] at h
    exact h
  have hk3' : (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * (inC G (w.1.adicCompletion ℚ) ((P.β : G.C) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) * inC G (w.1.adicCompletion ℚ) (P₁.β : G.C)) * (starT G.star (w.1.adicCompletion ℚ) (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop = algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (lam : w.1.adicCompletion ℚ) := by
    rw [← map_mul, mul_assoc (P.β : G.C), Units.inv_mul, mul_one]
    exact hk3
  have hN : ∀ m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = m * (starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((P₁.β⁻¹ : G.Cˣ) : G.C) →
      Commute (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (P₁.γ : G.C)) →
      inC G (w.1.adicCompletion ℚ) (P₁.β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((P₁.β⁻¹ : G.Cˣ) : G.C) = m' →
      ∃ v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (P₁.γ : G.C)) ∧
        (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = v * (inC G (w.1.adicCompletion ℚ) (P₁.β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((P₁.β⁻¹ : G.Cˣ) : G.C)) := by
    intro m' hm'v hcm' hτ
    have hss : (starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * (starT G.star (w.1.adicCompletion ℚ) ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop = 1 := by
      rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
    have h1 : (m' : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * (inC G (w.1.adicCompletion ℚ) (P₁.β : G.C) * (starT G.star (w.1.adicCompletion ℚ) ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop *
        ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) = 1 := by
      rw [hm'v]
      calc _ = (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * ((starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop *
            (inC G (w.1.adicCompletion ℚ) ((P₁.β⁻¹ : G.Cˣ) : G.C) * inC G (w.1.adicCompletion ℚ) (P₁.β : G.C)) *
            (starT G.star (w.1.adicCompletion ℚ) ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop) * ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) := by
            simp only [mul_assoc]
        _ = 1 := by rw [hbb, mul_one, hss, mul_one, Units.mul_inv]
    have hinv' := Units.inv_eq_of_mul_eq_one_right h1
    refine hnorm' m' hcm' ?_ ?_ hτ
    · rw [hm'v]; exact hmul _ _ (hmul _ _ hm (hstar _ hm)) hβi'
    · rw [hinv']; exact hmul _ _ (hmul _ _ hβi (hstar _ hm')) hm'
  have halg := GlobalTheory.twisted_norm_local_step (starT G.star (w.1.adicCompletion ℚ)) hinv
    (Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom P₁.β)
    (Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom P₁.γ) k z m
    (inC G (w.1.adicCompletion ℚ) ((P.β : G.C) * ((P₁.β⁻¹ : G.Cˣ) : G.C)))
    lam (Units.map (algebraMap ℚ (w.1.adicCompletion ℚ)).toMonoidHom P₁.c) hβ' hY'
    (hcm.map (inC G (w.1.adicCompletion ℚ))) hk3' hkzm hz hN
  obtain ⟨z', hz', hz'eq⟩ := halg
  exact ⟨lam, z', hz', hz'eq⟩

end GlobalTheory.CxRegPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSubgroupAdjointScalar
section
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

namespace GlobalTheory.IwasawaTriv

theorem absE_eigen_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ (a : GL (Fin n) (AF F ⊗[F] E)) (x : Matrix (Fin n) (Fin 1) E) (pL : Matrix (Fin 1) (Fin n) E), pL * x = 1 → ∀ k ∈ levelAll σ J L a, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J k).1 * adMat F x = l.1 • adMat F x → absE F E l = 1 := by
  intro F E _ _ _ _ _ σ hσ n J L hL a x pL hpx k hk l hkl
  haveI := hL
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  set X := adMat F x with hX
  set Y := pL.map (inclR (F := F) (AF F)) with hY
  have hYX : Y * X = 1 := by
    rw [hX, hY, adMat, ← Matrix.map_mul, hpx]
    simp
  let M : GAd σ J → Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := fun g => (matHom _ σ J g).1
  have hMc : Continuous M := Units.continuous_val.comp (isEmbedding_matHom (AF F) σ J).continuous
  have hMmul : ∀ g h, M (g * h) = M g * M h := fun g h => by simp [M]
  have hMinv : ∀ g, M g⁻¹ * M g = 1 := fun g => by simp [M]
  have hM1 : M 1 = 1 := by simp [M]
  let φ : GAd σ J → AF F ⊗[F] E := fun g => (Y * M g * X) 0 0
  have hφc : Continuous φ := by
    have : Continuous fun g => Y * M g * X := (continuous_const.matrix_mul hMc).matrix_mul continuous_const
    exact (continuous_apply 0).comp ((continuous_apply 0).comp this)
  have hdet : ∀ g (c : AF F ⊗[F] E), M g * X = c • X → φ g = c := by
    intro g c h
    simp only [φ, Matrix.mul_assoc, h, Matrix.mul_smul, hYX]
    simp

  have hφ1 : φ 1 = 1 := hdet 1 1 (by rw [hM1, one_smul, Matrix.one_mul])
  have hstep : ∀ g h (c d : AF F ⊗[F] E), M g * X = c • X → M h * X = d • X → M (g * h) * X = (d * c) • X := by
    intro g h c d hg hh
    rw [hMmul, Matrix.mul_assoc, hh, Matrix.mul_smul, hg, smul_smul]
  have hmem : ∀ g, (∃ c : AF F ⊗[F] E, M g * X = c • X) → M g * X = φ g • X := by
    rintro g ⟨c, h⟩
    rw [hdet g c h]; exact h
  let S : Set (GAd σ J) := {g | M g * X = φ g • X ∧ M g⁻¹ * X = φ g⁻¹ • X}
  have hinvφ : ∀ g ∈ S, φ g * φ g⁻¹ = 1 := by
    intro g hg
    have e := hstep g⁻¹ g _ _ hg.2 hg.1
    rw [inv_mul_cancel] at e
    rw [← hdet 1 _ e, hφ1]
  let P : Subgroup (GAd σ J) :=
    { carrier := S
      one_mem' := ⟨by rw [hM1, hφ1, one_smul, Matrix.one_mul], by rw [inv_one, hM1, hφ1, one_smul, Matrix.one_mul]⟩
      mul_mem' := fun {g h} hg hh => ⟨hmem _ ⟨_, hstep _ _ _ _ hg.1 hh.1⟩,
        hmem _ ⟨_, by rw [_root_.mul_inv_rev]; exact hstep _ _ _ _ hh.2 hg.2⟩⟩
      inv_mem' := fun {g} hg => ⟨hg.2, by rw [inv_inv]; exact hg.1⟩ }
  have hP : IsClosed (P : Set (GAd σ J)) := by
    show IsClosed S
    exact (isClosed_eq (hMc.matrix_mul continuous_const) (hφc.smul continuous_const)).inter
      (isClosed_eq ((hMc.comp continuous_inv).matrix_mul continuous_const) ((hφc.comp continuous_inv).smul continuous_const))
  let u : P →* (AF F ⊗[F] E)ˣ :=
    { toFun := fun p => ⟨φ p, φ (p : GAd σ J)⁻¹, hinvφ p p.2, by rw [mul_comm]; exact hinvφ p p.2⟩
      map_one' := Units.ext (by
        change φ ((1 : P) : GAd σ J) = 1
        rw [OneMemClass.coe_one]; exact hφ1)
      map_mul' := fun p q => Units.ext (by
        change φ ((p * q : P) : GAd σ J) = φ p * φ q
        rw [Subgroup.coe_mul, hdet _ _ (hstep _ _ _ _ p.2.1 q.2.1), mul_comm]) }
  have hu : Continuous u := Units.continuous_iff.2
    ⟨hφc.comp continuous_subtype_val, (hφc.comp continuous_inv).comp continuous_subtype_val⟩
  have hδ : Continuous ((absE F E).comp u) := (GlobalTheory.Doubling.continuous_absE (F := F) (E := E)).comp hu
  have h2 : M k⁻¹ * X = ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • X := by
    have e : M k⁻¹ * (M k * X) = X := by rw [← Matrix.mul_assoc, hMinv, Matrix.one_mul]
    have hkl' : M k * X = (l : AF F ⊗[F] E) • X := hkl
    rw [hkl', Matrix.mul_smul] at e
    conv_rhs => rw [← e]
    rw [smul_smul, Units.inv_mul, one_smul]
  have hkP : k ∈ P := ⟨hmem k ⟨_, hkl⟩, hmem _ ⟨_, h2⟩⟩
  have key := GlobalTheory.Doubling.triv_of_isCompact (δ := (absE F E).comp u) (K := levelAll σ J L a) hP hδ
    (GlobalTheory.Doubling.isCompact_levelAll hσ J L a) ⟨k, hkP⟩ hk
  have hul : u ⟨k, hkP⟩ = l := Units.ext (hdet k l hkl)
  change absE F E (u ⟨k, hkP⟩) = 1 at key
  rwa [hul] at key

end GlobalTheory.IwasawaTriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockRepEquivFirst
section
open GlobalTheory.PRep GlobalTheory.SmGL Matrix GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.DiagCell

theorem mem_parab_of_single {R : Type} [CommRing R] {β : Type} [LinearOrder β] {n : β → ℕ} {t : Type}
    [Fintype t] [DecidableEq t]
    (e : (Σ j, Fin (n j)) ≃ t) (a₀ : β) (h0 : ∀ j, j ≠ a₀ → n j = 0) (x : GL t R) :
    x ∈ parab R e := by
  refine mem_parab_iff.2 fun a b i j hab => ?_
  by_cases ha : a = a₀
  · have hb : b ≠ a₀ := fun e => by rw [e, ha] at hab; exact lt_irrefl _ hab
    exact absurd j.2 (by have := j.2; have := h0 b hb; omega)
  · exact absurd i.2 (by have := i.2; have := h0 a ha; omega)

theorem eq_one_of_mem_unipRad_single {R : Type} [CommRing R] {β : Type} [Fintype β] [LinearOrder β]
    {n : β → ℕ} {t : Type} [Fintype t] [DecidableEq t] (e : (Σ j, Fin (n j)) ≃ t) (a₀ : β)
    (h0 : ∀ j, j ≠ a₀ → n j = 0) {g : GL t R} (hg : g ∈ unipRad R e) : g = 1 := by
  obtain ⟨-, h2⟩ := mem_unipRad.1 hg
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective y
  by_cases ha : a = a₀
  · by_cases hb : b = a₀
    · obtain rfl : b = a := hb.trans ha.symm
      rw [h2 b i j]
      simp [Matrix.one_apply]
    · exact absurd j.2 (by have := j.2; have := h0 b hb; omega)
  · exact absurd i.2 (by have := i.2; have := h0 a ha; omega)

end GlobalTheory.DiagCell

namespace GlobalTheory.DiagCell

theorem cellFunctor_diag_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {m : Type} [Fintype m] [DecidableEq m] (b : SizeMatrix (Two (Fin 1) m) (Two (Fin 1) m)),
    b.1 false true = 0 → b.1 true false = 0 →
    ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k (Two (Fin 1) m)) W), IsSmooth ρ →
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin 1) m i) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin 1) m j),
      Nonempty ((cellFunctor f g ρ).Equiv ρ) := by
  intro k _ _ _ _ m _ _ b h01 h10 W _ _ ρ hsm
  have hrz : ∀ i j, j ≠ i → b.1 i j = 0 := by
    intro i j hj
    cases i <;> cases j <;> simp_all
  have hcz : ∀ j i, i ≠ j → b.1 i j = 0 := fun j i hi => hrz i j (Ne.symm hi)
  have hcard : ∀ i, Fintype.card (Fin (b.1 i i)) = Fintype.card (Two (Fin 1) m i) := by
    intro i
    have r := b.2.1 i
    rw [Fintype.sum_bool] at r
    cases i <;> simp_all
  let E : ∀ i, Fin (b.1 i i) ≃ Two (Fin 1) m i := fun i => Fintype.equivOfCardEq (hcard i)
  let f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin 1) m i := fun i =>
    (OneBlockCell.valEquiv (n := fun j => b.1 i j) i rfl (fun j hj => hrz i j hj)).trans (E i)
  let g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Two (Fin 1) m j := fun j =>
    (OneBlockCell.valEquiv (n := fun i => b.1 i j) j rfl (fun i hi => hcz j i hi)).trans (E j)
  refine ⟨f, g, ?_⟩
  have hbot : twKer ρ (relUnip k f) 1 = ⊥ := by
    refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
    rintro _ ⟨n, v, rfl⟩
    have : (n : Levi k (Two (Fin 1) m)) = 1 := funext fun i =>
      eq_one_of_mem_unipRad_single (f i) i (fun j hj => hrz i j hj) (n.2 i trivial)
    simp [this]
  have hδ : ∀ z, relDeltaHalf k (fun i j => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun i _ =>
      OneBlockCell.deltaHalf_eq_one_of_single i (fun j hj => hrz i j hj) (z i)
  have hδ' : ∀ z, relDeltaHalf k (fun j i => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun j _ =>
      OneBlockCell.deltaHalf_eq_one_of_single j (fun i hi => hcz j i hi) (z j)
  have hP : ∀ x, x ∈ relParab k g := fun x j _ =>
    mem_parab_of_single (g j) j (fun i hi => hcz j i hi) (x j)
  have hfg : ∀ i (t : Fin (b.1 i i)), f i ⟨i, t⟩ = g i ⟨i, t⟩ := fun i t => rfl
  have hγ : ∀ (p : relParab k g),
      relEmb k f (swapBlocks k (fun i j => Fin (b.1 i j)) (relProj k g p)) =
        (p : Levi k (Two (Fin 1) m)) := by
    intro p
    funext i
    rw [relEmb_apply]
    refine Units.ext (Matrix.ext fun x y => ?_)
    obtain ⟨⟨a, t⟩, rfl⟩ := (f i).surjective x
    obtain ⟨⟨a', s⟩, rfl⟩ := (f i).surjective y
    have ha : a = i := by
      by_contra hne
      have h1 := hrz i a hne
      have h2 := t.2
      omega
    have ha' : a' = i := by
      by_contra hne
      have h1 := hrz i a' hne
      have h2 := s.2
      omega
    subst ha
    subst ha'
    rw [leviEmb_apply_same, hfg, hfg]
    rfl
  let Ψ : W ≃ₗ[ℂ] Jacquet ρ (relUnip k f) := (Submodule.quotEquivOfEqBot _ hbot).symm
  have hΨ : ∀ u, Ψ u = Submodule.Quotient.mk u := fun u => rfl
  let τ := (twist ((relJac f ρ).comp (swapBlocks k (fun i j => Fin (b.1 i j))))
        (relDeltaHalf k (fun j i => Fin (b.1 i j)))).comp (relProj k g)
  have law : ∀ (p : relParab k g) u, τ p (Ψ u) = Ψ (ρ p u) := by
    intro p u
    rw [MonoidHom.comp_apply, twist_apply, MonoidHom.comp_apply, hΨ, relJac_mk, hδ, hδ', hΨ, hγ p]
    simp only [inv_one, Units.val_one, one_smul]
  let F : ρ.IntertwiningMap (cellFunctor f g ρ) :=
    { toFun := fun u => ⟨⟨fun x => Ψ (ρ x u), fun p x => by
          show Ψ (ρ (↑p * x) u) = _
          rw [map_mul, Module.End.mul_apply]
          exact (law p _).symm⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hsm u).mem_nhds (by simp)) fun x hx => by
          have hx' : ρ x u = u := hx
          refine Subtype.ext (funext fun y => ?_)
          show Ψ (ρ (y * x) u) = Ψ (ρ y u)
          rw [map_mul, Module.End.mul_apply, hx'])⟩
      map_add' := fun u w => Subtype.ext (Subtype.ext (funext fun x => by simp))
      map_smul' := fun c u => Subtype.ext (Subtype.ext (funext fun x => by simp))
      isIntertwining' := fun h => LinearMap.ext fun u => Subtype.ext (Subtype.ext (funext fun x => by
        show Ψ (ρ x (ρ h u)) = Ψ (ρ (x * h) u)
        rw [map_mul, Module.End.mul_apply])) }
  refine ⟨(LocGL.equivOfBijective F ⟨fun u w hw => ?_, fun φ => ⟨Ψ.symm (φ.1.1 1),
    Subtype.ext (Subtype.ext (funext fun x => ?_))⟩⟩).symm⟩
  · have h1 : Ψ (ρ 1 u) = Ψ (ρ 1 w) := congrArg (fun φ => φ.1.1 1) hw
    simpa using h1
  · show Ψ (ρ x (Ψ.symm (φ.1.1 1))) = φ.1.1 x
    refine (law ⟨x, hP x⟩ (Ψ.symm (φ.1.1 1))).symm.trans ?_
    refine (congrArg (τ ⟨x, hP x⟩) (Ψ.apply_symm_apply (φ.1.1 1))).trans ?_
    refine (φ.1.2 ⟨x, hP x⟩ 1).symm.trans ?_
    exact congrArg φ.1.1 (mul_one x)

end GlobalTheory.DiagCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLocalUnitsAlongNilpotentThickening
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FormalAlg

theorem lift_localUnits_of_thickening :
    ∀ (R : Type) [CommRing R] (J : Ideal R) (X X₀ : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (γ : X₀ ⟶ X) (q : X₀ ⟶ Spec (CommRingCat.of (R ⧸ J))), IsPullback γ q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → Surjective γ → ∀ (L : LB X), L.IsLB → ∀ D : X.Opens, IsAffineOpen D → ∀ u : ∀ m : L.ι, Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, (∀ z m m', γ z ∈ D ⊓ L.U m → γ z ∈ D ⊓ L.U m' → gm (𝟙 X₀) z _ (u m) = gm γ z _ (L.g m m') * gm (𝟙 X₀) z _ (u m')) → ∃ τ : ∀ m : L.ι, Γ(X, D ⊓ L.U m)ˣ, (∀ m, (γ.app (D ⊓ L.U m)).hom (τ m).val = (u m).val) ∧ ∀ x m m', x ∈ D ⊓ L.U m → x ∈ D ⊓ L.U m' → gm (𝟙 X) x _ (τ m) = gm (𝟙 X) x _ (L.g m m') * gm (𝟙 X) x _ (τ m') := by
  intro R _ J X X₀ f γ q hpb hsurj L hL D hD u hu
  have hLp := LB.isLB_pull hL γ
  let O : L.ι → X₀.Opens := fun m => γ ⁻¹ᵁ (D ⊓ L.U m)
  have hO : ∀ m, O m ≤ γ ⁻¹ᵁ D := fun m => γ.preimage_mono inf_le_left
  have hc : γ ⁻¹ᵁ D ≤ ⨆ m, O m := by
    intro z hz
    obtain ⟨m, hm⟩ := exists_chart hL (γ z)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨m, show γ z ∈ D ⊓ L.U m from ⟨hz, hm⟩⟩
  have hU : ∀ m, O m ≤ (L.pull γ).U (fun _ => m) := fun m z hz => mem_pull.2 hz.2

  have hg : ∀ z a b, γ z ∈ L.U a → γ z ∈ L.U b →
      gm (𝟙 X₀) z ((L.pull γ).U (fun _ => a) ⊓ (L.pull γ).U (fun _ => b))
        ((L.pull γ).g (fun _ => a) (fun _ => b)) = gm γ z _ (L.g a b) := by
    intro z a b ha hb
    have hp : (𝟙 X₀) z ∈ (L.pull γ).U (fun _ => a) ⊓ (L.pull γ).U (fun _ => b) :=
      ⟨mem_pull.2 ha, mem_pull.2 hb⟩
    show gm (𝟙 X₀) z _ (∏ _k : PUnit, (res _ (pullU γ _ (L.g a b))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    refine (gm_res (𝟙 X₀) z _ hp _).trans ((gm_pull (𝟙 X₀) γ z (L.U a ⊓ L.U b) ⟨ha, hb⟩ _).trans ?_)
    rw [Category.id_comp]
  have hcomp : ∀ a b, rs X₀ (inf_le_left : O a ⊓ O b ≤ O a) (u a).val =
      rs X₀ (inf_le_inf (hU a) (hU b)) ((L.pull γ).g (fun _ => a) (fun _ => b)).val *
        rs X₀ (inf_le_right : O a ⊓ O b ≤ O b) (u b).val := by
    intro a b
    have e : res (inf_le_left : O a ⊓ O b ≤ O a) (u a) =
        res (inf_le_inf (hU a) (hU b)) ((L.pull γ).g (fun _ => a) (fun _ => b)) *
          res (inf_le_right : O a ⊓ O b ≤ O b) (u b) := by
      apply unit_ext
      intro z hz
      have hz' : (𝟙 X₀) z ∈ O a ⊓ O b := hz
      rw [map_mul, gm_res _ z _ hz', gm_res _ z _ hz', gm_res _ z _ hz',
        hg z a b hz.1.2 hz.2.2]
      exact hu z a b hz.1 hz.2
    have e' := congrArg Units.val e
    simp only [Units.val_mul, GlobalTheory.LB.val_res] at e'
    exact e'
  obtain ⟨t, ht, -⟩ := SecOn.existsUnique_of_local hLp O hO hc (fun m _ => m) hU
    (fun m => (u m).val) hcomp
  obtain ⟨s, hs⟩ := secOn_pull_surjective_of_surjective R (R ⧸ J) (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective X X₀ f q γ hpb L hL D hD t
  have hcoord : ∀ m, (γ.app (D ⊓ L.U m)).hom (GlobalTheory.LB.coord s m) = (u m).val := by
    intro m
    have e := ht m
    rw [← hs] at e
    erw [SecOn.coord_pull γ s (fun _ => m), GlobalTheory.LB.resG_appLE] at e
    rw [Scheme.Hom.app_eq_appLE]
    exact e
  have hunit : ∀ m, IsUnit (GlobalTheory.LB.coord s m) := by
    intro m
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    obtain ⟨z, rfl⟩ := γ.surjective x
    apply isUnit_of_map_unit (γ.stalkMap z).hom
    erw [Scheme.Hom.germ_stalkMap_apply γ (D ⊓ L.U m) z hx, hcoord m]
    exact (u m).isUnit.map _
  refine ⟨fun m => (hunit m).unit, fun m => hcoord m, ?_⟩
  intro x m m' hx hx'
  have hi : D ⊓ L.U m ⊓ L.U m' ≤ D ⊓ L.U m := inf_le_left
  have hj : D ⊓ L.U m ⊓ L.U m' ≤ D ⊓ L.U m' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hij : D ⊓ L.U m ⊓ L.U m' ≤ L.U m ⊓ L.U m' :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have e : res hi (hunit m).unit = res hij (L.g m m') * res hj (hunit m').unit := by
    apply Units.ext
    simp only [Units.val_mul, GlobalTheory.LB.val_res, IsUnit.unit_spec]
    exact SecOn.compat s m m' hi hj hij
  have hxx : (𝟙 X) x ∈ D ⊓ L.U m ⊓ L.U m' := ⟨hx, hx'.2⟩
  have e' := congrArg (gm (𝟙 X) x _) e
  rw [map_mul, gm_res _ x _ hxx, gm_res _ x _ hxx, gm_res _ x _ hxx] at e'
  exact e'

end GlobalTheory.FormalAlg
end

