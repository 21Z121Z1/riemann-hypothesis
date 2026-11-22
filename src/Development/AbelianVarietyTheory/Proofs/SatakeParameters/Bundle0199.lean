import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0186
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0061
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0038
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0046

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondOfDefinite
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DesignBC

open Formalism.FrobeniusOrbits

variable (D : D7)

theorem conj_sqrtMinusD : D.host.conj D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  apply D.host.φ₀.injective
  have h2 := D.host.conjE_apply D.host.φ₀ D.host.sqrtMinusD
  have h3 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  rw [h2, map_neg, h3]
  simp

theorem sqrtMinusD_mul_self : D.host.sqrtMinusD * D.host.sqrtMinusD = -((D.host.d : ℕ) : D.host.E) := by
  rw [← sq]
  exact D.host.sqd_sq

theorem conj_conj (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [D.host.conjE_apply, D.host.conjE_apply, Complex.conj_conj]

theorem mem_F_iff (x : D.host.E) : x ∈ D.host.F ↔ D.host.conj x = x :=
  D.host.conjE_mem_hostF_iff x

theorem d_ne_zero : ((D.host.d : ℕ) : D.host.E) ≠ 0 :=
  Nat.cast_ne_zero.mpr D.host.hyp.2.1.ne_zero

theorem sqrtMinusD_ne_zero : D.host.sqrtMinusD ≠ 0 := by
  intro h
  have := sqrtMinusD_mul_self D
  rw [h, zero_mul, eq_comm, neg_eq_zero] at this
  exact d_ne_zero D this

end GlobalTheory.DesignBC

namespace GlobalTheory.DesignBC

open Formalism.FrobeniusOrbits

variable (D : D7)

theorem hypEFK : Formalism.MainNotions.SphericalInertData.HypEFK D := by
  rw [Formalism.MainNotions.SphericalInertData.HypEFK, eq_top_iff]
  intro x _
  set c := D.host.conj
  set s := D.host.sqrtMinusD
  have hs : s ≠ 0 := sqrtMinusD_ne_zero D
  have hcs : c s = -s := conj_sqrtMinusD D
  have hcc : c (c x) = x := conj_conj D x
  have hu : (x + c x) / 2 ∈ D.host.F := by
    rw [mem_F_iff]
    show c ((x + c x) / 2) = _
    rw [map_div₀, map_add, hcc, map_ofNat, add_comm]
  have hv : (x - c x) / (2 * s) ∈ D.host.F := by
    rw [mem_F_iff]
    show c ((x - c x) / (2 * s)) = _
    rw [map_div₀, map_sub, map_mul, hcc, map_ofNat, hcs]
    field_simp
    ring
  have hK : s ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
  have hx : x = (x + c x) / 2 + (x - c x) / (2 * s) * s := by
    field_simp
    ring
  rw [hx]
  refine add_mem (Subfield.subset_closure (Or.inl hu))
    (mul_mem (Subfield.subset_closure (Or.inl hv)) (Subfield.subset_closure (Or.inr hK)))

theorem two_le_finrank : 2 ≤ Module.finrank ℚ D.host.F := by
  have h := D.host.finrank_hostF
  show 2 ≤ Module.finrank ℚ (D.host.F)
  rw [h]
  have := D.R.ord_pos
  omega

end GlobalTheory.DesignBC

namespace GlobalTheory.DesignBC

open Formalism.FrobeniusOrbits Polynomial

variable (D : D7)

theorem d_eq : ∃ m : ℕ, D.host.d + 1 = 8 * m := ⟨(D.host.d + 1) / 8, by
  have := D.host.hyp.2.2.2.1; omega⟩

theorem isIntegral_half (y : D.host.E) (hy : y * y = -((D.host.d : ℕ) : D.host.E)) :
    IsIntegral ℤ ((1 + y) / 2) := by
  obtain ⟨m, hm⟩ := d_eq D
  refine ⟨X ^ 2 - X + C (2 * (m : ℤ)), ?_, ?_⟩
  · have : (X ^ 2 - X + C (2 * (m : ℤ)) : ℤ[X]) = X ^ 2 + (C (2 * (m : ℤ)) - X) := by ring
    rw [this]
    refine (monic_X_pow 2).add_of_left ?_
    refine lt_of_le_of_lt (degree_sub_le _ _) ?_
    rw [degree_X_pow, degree_X]
    refine max_lt (lt_of_le_of_lt degree_C_le (by norm_num)) (by norm_num)
  · have hd : ((D.host.d : ℕ) : D.host.E) = 8 * (m : D.host.E) - 1 := by
      have : ((D.host.d + 1 : ℕ) : D.host.E) = ((8 * m : ℕ) : D.host.E) := by rw [hm]
      push_cast at this
      linear_combination this
    simp only [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C]
    simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, algebraMap_int_eq, eq_intCast]
    push_cast
    rw [hd] at hy
    linear_combination (1/4 : D.host.E) * hy

end GlobalTheory.DesignBC

namespace GlobalTheory.DesignBC

open Formalism.FrobeniusOrbits

variable (D : D7)

theorem isSplitPl_of_two_mem (w : PlE D.host) (h2 : ((2 : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    IsSplitPl D.host w := by
  set s := D.host.sqrtMinusD
  have hss : s * s = -((D.host.d : ℕ) : D.host.E) := sqrtMinusD_mul_self D
  have hss' : (-s) * (-s) = -((D.host.d : ℕ) : D.host.E) := by rw [neg_mul_neg]; exact hss
  have hcs : D.host.conj s = -s := conj_sqrtMinusD D
  obtain ⟨m, hm⟩ := d_eq D
  let α : 𝓞 D.host.E := ⟨(1 + s) / 2, isIntegral_half D s hss⟩
  let β : 𝓞 D.host.E := ⟨(1 + -s) / 2, isIntegral_half D (-s) hss'⟩
  have hα : ((α : 𝓞 D.host.E) : D.host.E) = (1 + s) / 2 := rfl
  have hβ : ((β : 𝓞 D.host.E) : D.host.E) = (1 + -s) / 2 := rfl
  have hsum : α + β = 1 := by
    apply RingOfIntegers.ext
    show (1 + s) / 2 + (1 + -s) / 2 = ((1 : 𝓞 D.host.E) : D.host.E)
    push_cast
    ring
  have hprod : α * β = ((2 : ℕ) : 𝓞 D.host.E) * (m : 𝓞 D.host.E) := by
    apply RingOfIntegers.ext
    have key : ((((2 : ℕ) : 𝓞 D.host.E) * (m : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E) = 2 * (m : D.host.E) := by
      exact (map_mul (algebraMap (𝓞 D.host.E) D.host.E) _ _).trans (by rw [map_natCast, map_natCast]; norm_num)
    show (1 + s) / 2 * ((1 + -s) / 2) = ((((2 : ℕ) : 𝓞 D.host.E) * (m : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E)
    rw [key]
    have hd : ((D.host.d : ℕ) : D.host.E) = 8 * (m : D.host.E) - 1 := by
      have : ((D.host.d + 1 : ℕ) : D.host.E) = ((8 * m : ℕ) : D.host.E) := by rw [hm]
      push_cast at this
      linear_combination this
    rw [hd] at hss
    linear_combination (-1/4 : D.host.E) * hss
  have hcα : D.host.conj ((α : 𝓞 D.host.E) : D.host.E) = ((β : 𝓞 D.host.E) : D.host.E) := by
    rw [hα, hβ, map_div₀, map_add, map_one, hcs, map_ofNat]
  have hcβ : D.host.conj ((β : 𝓞 D.host.E) : D.host.E) = ((α : 𝓞 D.host.E) : D.host.E) := by
    rw [← hcα, conj_conj]
  have hne : ∀ x y : 𝓞 D.host.E, x + y = 1 → x ∈ w.asIdeal → y ∉ w.asIdeal := by
    intro x y hxy hx hy
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hxy ▸ add_mem hx hy))
  have hmem : α * β ∈ w.asIdeal := by
    rw [hprod]; exact Ideal.mul_mem_right _ _ h2
  rcases w.isPrime.mem_or_mem hmem with ha | hb
  · refine ⟨α, ha, fun y hy => ?_⟩
    have : y = β := RingOfIntegers.coe_injective (hy.trans hcα)
    rw [this]; exact hne α β hsum ha
  · refine ⟨β, hb, fun y hy => ?_⟩
    have : y = α := RingOfIntegers.coe_injective (hy.trans hcβ)
    rw [this]; exact hne β α (by rw [add_comm]; exact hsum) hb

end GlobalTheory.DesignBC

namespace GlobalTheory.DesignBC

theorem jointCond_of_definite : ∀ D : D7, (∀ j, 1 ≤ j → j ≤ D.R.m → (letI := D.host.cmStar; (D.sp.V j).IsDefinite)) →
    GlobalDatumCompatibility D := by
  intro D hdef
  refine ⟨hypEFK D, ⟨two_le_finrank D, fun w hw h2 => hw (isSplitPl_of_two_mem D w h2)⟩, hdef⟩

end GlobalTheory.DesignBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearFormsHyperbolicCoordinatesEqTarget
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

noncomputable section

namespace GlobalTheory.KerStd.HypCoord

theorem sum_coef_fOf (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {N N' r : ℕ} (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p)
    (hdual : ∀ s t : ZMod (nP D p), s.val % 2 = t.val % 2 →
      ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0)
    (r₀ : R) (a : Fin N) (b : Fin N') (i : Fin r) (s : ZMod (nP D p)) :
    ∑ k, (if s.val % 2 = 0 then fOf D p σ om R g ((r₀, k), a, b) i * σ^[s.val] (oms k)
      else fOf' D p σ oms R g ((r₀, k), a, b) i * σ^[s.val] (om k)) = g (OrbitPlaces.orbMap D p r₀ s) a b i := by
  by_cases hs : s.val % 2 = 0
  · simp only [hs, if_true, fOf, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_eq_single s]
    · simp only [hs, if_true]
      have h := hdual s s rfl
      rw [if_pos rfl] at h
      calc ∑ k, σ^[s.val] (om k) * g (OrbitPlaces.orbMap D p r₀ s) a b i * σ^[s.val] (oms k)
          = g (OrbitPlaces.orbMap D p r₀ s) a b i * ∑ k, σ^[s.val] (om k) * σ^[s.val] (oms k) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        _ = _ := by rw [h, mul_one]
    · intro t _ hts
      by_cases ht : t.val % 2 = 0
      · simp only [ht, if_true]
        have h := hdual t s (by rw [ht, hs])
        rw [if_neg hts] at h
        calc ∑ k, σ^[t.val] (om k) * g (OrbitPlaces.orbMap D p r₀ t) a b i * σ^[s.val] (oms k)
            = g (OrbitPlaces.orbMap D p r₀ t) a b i * ∑ k, σ^[t.val] (om k) * σ^[s.val] (oms k) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
          _ = 0 := by rw [h, mul_zero]
      · simp [ht]
    · intro h; exact absurd (Finset.mem_univ s) h
  · simp only [hs, if_false, fOf', Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_eq_single s]
    · simp only [hs, if_false]
      have h := hdual s s rfl
      rw [if_pos rfl] at h
      calc ∑ k, σ^[s.val] (oms k) * g (OrbitPlaces.orbMap D p r₀ s) a b i * σ^[s.val] (om k)
          = g (OrbitPlaces.orbMap D p r₀ s) a b i * ∑ k, σ^[s.val] (om k) * σ^[s.val] (oms k) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        _ = _ := by rw [h, mul_one]
    · intro t _ hts
      by_cases ht : t.val % 2 = 0
      · simp [ht]
      · simp only [ht, if_false]
        have h := hdual s t (by omega)
        rw [if_neg (Ne.symm hts)] at h
        calc ∑ k, σ^[t.val] (oms k) * g (OrbitPlaces.orbMap D p r₀ t) a b i * σ^[s.val] (om k)
            = g (OrbitPlaces.orbMap D p r₀ t) a b i * ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
          _ = 0 := by rw [h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ s) h

theorem hypZ_term (D : D7) (p : ℕ) [Fact p.Prime] {N0 N1 : ℕ} (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {n : Type} (f f' : (R × Fin (nP D p / 2)) × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension p) (i : n)
    (e : (R × Fin (nP D p / 2)) × Fin N0 × Fin N1) :
    MvPowerSeries.C (f e i : ℂ_[p]) * linEv D p σ (oms e.1.2) e.1.1 e.2.1 e.2.2 +
      MvPowerSeries.C (f' e i : ℂ_[p]) * linOd D p σ (om e.1.2) e.1.1 e.2.1 e.2.2 =
    ∑ s : ZMod (nP D p), MvPowerSeries.C (((if s.val % 2 = 0 then f e i * σ^[s.val] (oms e.1.2)
      else f' e i * σ^[s.val] (om e.1.2) : MaximalUnramifiedExtension p)) : ℂ_[p]) * MvPowerSeries.X (OrbitPlaces.orbMap D p e.1.1 s, e.2.1, e.2.2) := by
  unfold linEv linOd
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : s.val % 2 = 0
  · simp [hs, map_mul, mul_assoc]
  · simp [hs, map_mul, mul_assoc]

theorem bijective_orbMap (D : D7) (p : ℕ) (R : Finset (OrbitPlaces.Pl D)) (hR : OrbitPlaces.IsReps D p R) :
    Function.Bijective (fun y : R × ZMod (nP D p) => OrbitPlaces.orbMap D p y.1 y.2) := by
  constructor
  · rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ h
    simp only at h
    have hr : (r₁ : OrbitPlaces.Pl D) = r₂ := by
      obtain ⟨r0, _, hu⟩ := hR (OrbitPlaces.orbMap D p r₁ s₁)
      have e1 := hu r₁ ⟨r₁.2, s₁.val, rfl⟩
      have e2 := hu r₂ ⟨r₂.2, s₂.val, h.symm⟩
      rw [e1, e2]
    have hr' : r₁ = r₂ := Subtype.ext hr
    subst hr'
    have hs : s₁ = s₂ := ZMod.val_injective _ (posPl_inj D p r₁ _ _ (ZMod.val_lt s₁) (ZMod.val_lt s₂) h)
    rw [hs]
  · intro z
    obtain ⟨r0, ⟨hr0, e, he⟩, _⟩ := hR z
    refine ⟨(⟨r0, hr0⟩, (e : ZMod (nP D p))), ?_⟩
    show posPl D p r0 (e : ZMod (nP D p)).val = z
    rw [ZMod.val_natCast, posPl_mod, he]

end GlobalTheory.KerStd.HypCoord

namespace GlobalTheory.KerStd.HypCoord

theorem hypZ_fOf (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {N N' r : ℕ} (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p)
    (hR : OrbitPlaces.IsReps D p R)
    (hdual : ∀ s t : ZMod (nP D p), s.val % 2 = t.val % 2 →
      ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0) (i : Fin r) :
    hypZ D p σ om oms R (fOf D p σ om R g) (fOf' D p σ oms R g) i =
      ∑ j : OrbitPlaces.Pl D × Fin N × Fin N', MvPowerSeries.C ((g j.1 j.2.1 j.2.2 i : MaximalUnramifiedExtension p) : ℂ_[p]) * MvPowerSeries.X j := by
  set F : (R × Fin (nP D p / 2)) × Fin N × Fin N' → ZMod (nP D p) → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] :=
    fun e s => MvPowerSeries.C (((if s.val % 2 = 0 then fOf D p σ om R g e i * σ^[s.val] (oms e.1.2)
      else fOf' D p σ oms R g e i * σ^[s.val] (om e.1.2) : MaximalUnramifiedExtension p)) : ℂ_[p]) *
        MvPowerSeries.X (OrbitPlaces.orbMap D p e.1.1 s, e.2.1, e.2.2) with hF
  have hB : Function.Bijective (fun y : (R × ZMod (nP D p)) × Fin N × Fin N' => ((OrbitPlaces.orbMap D p y.1.1 y.1.2, y.2) :
      OrbitPlaces.Pl D × Fin N × Fin N')) :=
    (bijective_orbMap D p R hR).prodMap Function.bijective_id
  let eqv : ((R × ZMod (nP D p)) × Fin N × Fin N') × Fin (nP D p / 2) ≃
      ((R × Fin (nP D p / 2)) × Fin N × Fin N') × ZMod (nP D p) :=
    { toFun := fun y => (((y.1.1.1, y.2), y.1.2), y.1.1.2)
      invFun := fun x => (((x.1.1.1, x.2), x.1.2), x.1.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold hypZ
  calc ∑ e, (MvPowerSeries.C (fOf D p σ om R g e i : ℂ_[p]) * linEv D p σ (oms e.1.2) e.1.1 e.2.1 e.2.2 +
        MvPowerSeries.C (fOf' D p σ oms R g e i : ℂ_[p]) * linOd D p σ (om e.1.2) e.1.1 e.2.1 e.2.2)
      = ∑ e, ∑ s, F e s := Finset.sum_congr rfl fun e _ => hypZ_term D p σ om oms R _ _ i e
    _ = ∑ x : ((R × Fin (nP D p / 2)) × Fin N × Fin N') × ZMod (nP D p), F x.1 x.2 := (Fintype.sum_prod_type' F).symm
    _ = ∑ y : ((R × ZMod (nP D p)) × Fin N × Fin N') × Fin (nP D p / 2), F ((y.1.1.1, y.2), y.1.2) y.1.1.2 :=
        (Fintype.sum_equiv eqv _ _ fun _ => rfl).symm
    _ = ∑ y : (R × ZMod (nP D p)) × Fin N × Fin N', ∑ k, F ((y.1.1, k), y.2) y.1.2 :=
        Fintype.sum_prod_type' (fun (y : (R × ZMod (nP D p)) × Fin N × Fin N') (k : Fin (nP D p / 2)) => F ((y.1.1, k), y.2) y.1.2)
    _ = ∑ y : (R × ZMod (nP D p)) × Fin N × Fin N',
          MvPowerSeries.C ((g (OrbitPlaces.orbMap D p y.1.1 y.1.2) y.2.1 y.2.2 i : MaximalUnramifiedExtension p) : ℂ_[p]) *
            MvPowerSeries.X ((OrbitPlaces.orbMap D p y.1.1 y.1.2, y.2) : OrbitPlaces.Pl D × Fin N × Fin N') := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← sum_coef_fOf D p σ om oms R g hdual y.1.1 y.2.1 y.2.2 i y.1.2, hF]
        simp only [← Finset.sum_mul, ← map_sum]
        congr 2
        push_cast
        rfl
    _ = _ := hB.sum_comp (fun j : OrbitPlaces.Pl D × Fin N × Fin N' =>
          MvPowerSeries.C ((g j.1 j.2.1 j.2.2 i : MaximalUnramifiedExtension p) : ℂ_[p]) * MvPowerSeries.X j)

theorem linForm_hypZ : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (κ : Type) (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p) (Λ : κ → Fin r → ℂ_[p]) (T : κ → OrbitPlaces.Pl D × Fin N × Fin N' → ℂ_[p]), OrbitPlaces.OrbOK D p → OrbitPlaces.IsReps D p R → (∀ s t : ZMod (nP D p), s.val % 2 = t.val % 2 → ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0) → (∀ q z a b, ∑ i, Λ q i * ((g z a b i : MaximalUnramifiedExtension p) : ℂ_[p]) = T q (z, a, b)) → ∀ q, ∑ i, MvPowerSeries.C (Λ q i) * hypZ D p σ om oms R (fOf D p σ om R g) (fOf' D p σ oms R g) i = ∑ j, MvPowerSeries.C (T q j) * MvPowerSeries.X j := by
  intro D p _ σ om oms R N N' r κ g Λ T _ hR hdual hT q
  simp only [hypZ_fOf D p σ om oms R g hR hdual, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hT q j.1 j.2.1 j.2.2, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, mul_assoc]

end GlobalTheory.KerStd.HypCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MultiProdCompCongr
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead
open scoped TensorProduct

namespace GlobalTheory.ProdReorder

section Eqv

variable {G V W U : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G U}

theorem eqv_trans (h₁ : Nonempty (ρ.Equiv σ)) (h₂ : Nonempty (σ.Equiv τ)) : Nonempty (ρ.Equiv τ) :=
  h₁.elim fun a => h₂.elim fun b => ⟨a.trans b⟩

theorem eqv_symm (h : Nonempty (ρ.Equiv σ)) : Nonempty (σ.Equiv ρ) := h.map Representation.Equiv.symm

theorem eqv_refl (ρ : Representation ℂ G V) : Nonempty (ρ.Equiv ρ) := ⟨Representation.Equiv.refl ρ⟩

end Eqv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem multiProd_placing {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e e' : (Σ a, m a) ≃ n) {X : α → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (m a) k) (X a)) :
    Nonempty ((multiProd e π).Equiv (multiProd e' π)) :=
  (Placing.parInd_jac_placing k α n m e e' _).1 _

theorem ind₂_congr {r t N : ℕ} (h : r + t = N) {V V' W W' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {π₁ : Representation ℂ (GL (Fin r) k) V} {σ₁ : Representation ℂ (GL (Fin r) k) V'}
    {π₂ : Representation ℂ (GL (Fin t) k) W} {σ₂ : Representation ℂ (GL (Fin t) k) W'}
    (φ₁ : Nonempty (π₁.Equiv σ₁)) (φ₂ : Nonempty (π₂.Equiv σ₂)) :
    Nonempty ((ind₂ (stdSum h) (extTensor π₁ π₂)).Equiv (ind₂ (stdSum h) (extTensor σ₁ σ₂))) := by
  subst h
  exact φ₁.elim fun a => φ₂.elim fun b => ⟨LocGL.prod₂Equiv a b⟩

theorem ind₂_assoc' {r s t M M' N : ℕ} (h₁ : r + s = M) (h₂ : M + t = N) (h₃ : s + t = M')
    (h₄ : r + M' = N) {V₁ V₂ V₃ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup V₃] [Module ℂ V₃] (π₁ : Representation ℂ (GL (Fin r) k) V₁)
    (π₂ : Representation ℂ (GL (Fin s) k) V₂) (π₃ : Representation ℂ (GL (Fin t) k) V₃)
    (s₁ : IsSmooth π₁) (s₂ : IsSmooth π₂) (s₃ : IsSmooth π₃) :
    Nonempty ((ind₂ (stdSum h₂) (extTensor (ind₂ (stdSum h₁) (extTensor π₁ π₂)) π₃)).Equiv
      (ind₂ (stdSum h₄) (extTensor π₁ (ind₂ (stdSum h₃) (extTensor π₂ π₃))))) := by
  subst h₁ h₃ h₂
  exact Stages.prod₂_assoc k r s t V₁ V₂ V₃ π₁ π₂ π₃ s₁ s₂ s₃

theorem multiProd_head {s : ℕ} {d : Fin (s + 1) → ℕ} {X : Fin (s + 1) → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) {T N : ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin N) (h : d 0 + T = N) (e' : (Σ a : Fin s, Fin (d a.succ)) ≃ Fin T) :
    Nonempty ((multiProd e π).Equiv
      (ind₂ (stdSum h) (extTensor (π 0) (multiProd e' fun a : Fin s => π a.succ)))) := by
  have hT : T = ∑ a : Fin s, d a.succ := by
    have := Fintype.card_congr e'
    simp only [Fintype.card_sigma, Fintype.card_fin] at this
    exact this.symm
  subst hT h
  have A := MultiIrr.nonempty_prod₂_equiv_multiProd_succ (k := k) d (Fin.sum_univ_succ d) π
  have B := multiProd_placing (k := k) e (stdBlocks d (Fin.sum_univ_succ d)) π
  have C := multiProd_placing (k := k) (stdBlocks (fun i : Fin s => d i.succ) rfl) e' fun a => π a.succ
  exact A.elim fun A => B.elim fun B => C.elim fun C =>
    ⟨B.trans (A.symm.trans (LocGL.prod₂Equiv (Representation.Equiv.refl (π 0)) C))⟩

theorem multiProd_empty {d d' : Fin 0 → ℕ} {X X' : Fin 0 → Type} [iX : ∀ a, AddCommGroup (X a)]
    [mX : ∀ a, Module ℂ (X a)] [iX' : ∀ a, AddCommGroup (X' a)] [mX' : ∀ a, Module ℂ (X' a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (π' : ∀ a, Representation ℂ (GL (Fin (d' a)) k) (X' a))
    {t : ℕ} (e : (Σ a, Fin (d a)) ≃ Fin t) (e' : (Σ a, Fin (d' a)) ≃ Fin t) :
    Nonempty ((multiProd e π).Equiv (multiProd e' π')) := by
  obtain rfl : d = d' := funext fun a => a.elim0
  obtain rfl : X = X' := funext fun a => a.elim0
  obtain rfl : iX = iX' := funext fun a => a.elim0
  obtain rfl : mX = mX' := funext fun a => a.elim0
  obtain rfl : π = π' := funext fun a => a.elim0
  exact multiProd_placing e e' π

theorem ind₂_unit_right {r t : ℕ} (h : r + t = r) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin r) k) V) (hπ : IsSmooth π) {d : Fin 0 → ℕ} {X : Fin 0 → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (τ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (e : (Σ a, Fin (d a)) ≃ Fin t) :
    Nonempty ((ind₂ (stdSum h) (extTensor π (multiProd e τ))).Equiv π) := by
  let f : (Σ _ : Fin 1, Fin r) ≃ Fin r :=
    { toFun := Sigma.snd
      invFun := fun i => ⟨0, i⟩
      left_inv := fun ⟨a, i⟩ => by obtain rfl := Subsingleton.elim a 0; rfl
      right_inv := fun _ => rfl }
  let e' : (Σ a : Fin 0, Fin r) ≃ Fin t :=
    (Equiv.equivOfIsEmpty (Σ a : Fin 0, Fin r) (Σ a, Fin (d a))).trans e
  have A := LocGL.nonempty_equiv_multiProd_one hπ f fun _ _ => rfl
  have B := multiProd_head (k := k) (d := fun _ : Fin 1 => r) (fun _ => π) f h e'
  have C := ind₂_congr h (eqv_refl π) (multiProd_empty (k := k) (fun a : Fin 0 => π) τ e' e)
  exact eqv_symm (eqv_trans A (eqv_trans B C))

theorem multiProd_comp_congr {s u : ℕ} {d : Fin s → ℕ} (σ : ∀ a, Irr k (d a)) {f g : Fin u → Fin s} (hfg : f = g)
    {T : ℕ} (e : (Σ i, Fin (d (f i))) ≃ Fin T) (e' : (Σ i, Fin (d (g i))) ≃ Fin T) :
    Nonempty ((multiProd e fun i => (σ (f i)).π).Equiv (multiProd e' fun i => (σ (g i)).π)) := by
  subst hfg
  exact multiProd_placing e e' _

def sigmaPart {s s₁ s₂ : ℕ} (d : Fin s → ℕ) (ι₁ : Fin s₁ → Fin s) (ι₂ : Fin s₂ → Fin s)
    (hb : Function.Bijective (Sum.elim ι₁ ι₂)) :
    (Σ a, Fin (d a)) ≃ (Σ i, Fin (d (ι₁ i))) ⊕ (Σ j, Fin (d (ι₂ j))) :=
  (Equiv.sigmaCongrLeft (β := fun a => Fin (d a)) (Equiv.ofBijective _ hb)).symm.trans
    (Equiv.sumSigmaDistrib fun x => Fin (d (Sum.elim ι₁ ι₂ x)))

def Commutes {p q : ℕ} (x : Irr k p) (y : Irr k q) : Prop :=
  ∀ (N : ℕ) (h₁ : p + q = N) (h₂ : q + p = N),
    Nonempty ((ind₂ (stdSum h₁) (extTensor x.π y.π)).Equiv (ind₂ (stdSum h₂) (extTensor y.π x.π)))

theorem Commutes.symm {p q : ℕ} {x : Irr k p} {y : Irr k q} (h : Commutes x y) : Commutes y x :=
  fun N h₁ h₂ => (h N h₂ h₁).map Representation.Equiv.symm

end GlobalTheory.ProdReorder
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionPreservesSubquotient
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.ParIndSubquot

theorem parInd_isSubquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (ρ : Representation ℂ (Levi k m) W) (ρ' : Representation ℂ (Levi k m) W'), IsSmooth ρ' → IsSubquotient ρ ρ' → IsSubquotient (parInd e ρ) (parInd e ρ') := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e W W' _ _ _ _ ρ ρ' hρ' h
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨-, -, -, -, -, hcont, hP, -, hPK⟩ := GlobalTheory.SmGL.LeviInt.levi_integral_facts k α n m e
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let ι : S.toRepresentation.IntertwiningMap ρ' :=
    { toLinearMap := S.toSubmodule.subtype, isIntertwining' := fun _ => rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  have hS : IsSmooth S.toRepresentation := (IsSubquotient.of_injective ι hι).isSmooth hρ'
  have hinj : Function.Injective (parIndMap e ι) := by
    intro φ ψ hφψ
    refine Subtype.ext (Subtype.ext (funext fun g => hι ?_))
    exact congrFun (congrArg (fun χ : IndSp e ρ' => χ.1.1) hφψ) g
  let σ₀ : Representation ℂ (parab k e) S.toSubmodule := (twist S.toRepresentation (deltaHalf k m)).comp (leviProj k e)
  let z : Representation.IntertwiningMap σ₀ σ₀ :=
    { toLinearMap := 0, isIntertwining' := fun _ => by ext; simp }
  have hsurj : Function.Surjective (parIndMap e f) := by
    refine (GlobalTheory.SmGL.IndCoinv.smInd_coinvariants (GL n k) (parab k e) (KO k n) hP SplitFlip.isCompact_KO
      hPK (GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k n) _ _ _ _
      (isSmooth_comp (isSmooth_twist hS (isSmoothChar_deltaHalf k)) _ hcont)
      (compMap (twistMap f _) _) Unit (fun _ => z) hf ?_).1
    intro x _
    refine Submodule.subset_span ⟨(), -x, ?_⟩
    show x = (0 : _) - -x
    simp
  exact (IsSubquotient.of_surjective (parIndMap e f) hsurj).trans (IsSubquotient.of_injective (parIndMap e ι) hinj)

end GlobalTheory.ParIndSubquot
end

