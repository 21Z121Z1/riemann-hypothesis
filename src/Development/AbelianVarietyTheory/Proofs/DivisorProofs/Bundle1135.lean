import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitNormBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedEigenvaluesClasses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1096
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMemConj
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatesSeparableMatrixCompactModCentralizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0971
import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BtOrderEmbeddingOpenImmersion
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.PadicPolys

theorem minpoly_coeff_bdd : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ),
    IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ β : G.Cˣ, ∃ B : ℝ, ∀ (y : grp G β) (h : Gr G 1),
      f' (h⁻¹ * toP1 G β y * h) ≠ 0 → ∀ (φ : G.F →+* PadicAlgCl p) (k : ℕ),
        ‖φ ((minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).coeff k)‖ ≤ B := by
  intro p _ G K' f' hf β
  obtain ⟨k0, hk0⟩ := GlobalTheory.AtPBd.main p G 1 K' f' one_pos hf
  set R : ℝ := (p : ℝ) ^ k0 with hR
  have hR1 : 1 ≤ R := one_le_pow₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  refine ⟨max (R * R) 1 ^ (G.n ^ 2) * ((G.n ^ 2).choose (G.n ^ 2 / 2) : ℝ), ?_⟩
  intro y h hy φ k
  have hnrm : IsNrm G 1 (locC G (y : G.Cˣ × ℚˣ)) (h⁻¹ * toP1 G β y * h) h := by
    show nrmG (sigG G 1) 1 _ = _
    simp [nrmG]
    rfl
  obtain ⟨hs, -, hrt, hrti⟩ := hk0 (locC G (y : G.Cˣ × ℚˣ)) (h⁻¹ * toP1 G β y * h) h 1 hnrm (by simpa using hy)
  set yC : G.C := (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) with hyC
  have hint : IsIntegral G.F yC := Algebra.IsIntegral.isIntegral _
  have hmon : (minpoly G.F yC).Monic := minpoly.monic hint
  have hsn : ‖(((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p)‖ ≤ R := by
    rw [← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends]
    exact hs
  have hs0 : (((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p) ≠ 0 := by
    exact_mod_cast ((y : G.Cˣ × ℚˣ).2).ne_zero
  have hroot : ∀ μ ∈ ((minpoly G.F yC).map φ).roots, ‖μ‖ ≤ R * R := by
    intro μ hμ
    have hμ' : ((minpoly G.F yC).map φ).IsRoot μ := Polynomial.isRoot_of_mem_roots hμ
    rcases GlobalTheory.GlobEig.liesOver_or_conj G φ with hφ | hφ
    · obtain ⟨i, ν, hν, hνr⟩ := GlobalTheory.GlobEig.exists_root_rho G φ hφ yC μ hμ'
      rw [← hν]
      exact (hrt i ν hνr).trans (le_mul_of_one_le_left (by linarith) hR1)
    · have h2 := GlobalTheory.GlobEig.isRoot_minpoly_sh G yC φ μ hμ'
      obtain ⟨i, ν, hν, hνr⟩ := GlobalTheory.GlobEig.exists_root_rho G _ hφ (sh G yC) μ h2
      have h3 := GlobalTheory.GlobEig.isRoot_inv G i β (y : G.Cˣ × ℚˣ).1 (y : G.Cˣ × ℚˣ).2 y.2.1 ν hνr
      have h4 := hrti i _ h3
      rw [← hν]
      have e : ν = ν * (((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p)⁻¹ * (((y : G.Cˣ × ℚˣ).2 : ℚ) : PadicAlgCl p) := by
        field_simp
      rw [e, norm_mul]
      exact mul_le_mul h4 hsn (norm_nonneg _) (by linarith)
  have hdeg : (minpoly G.F yC).natDegree ≤ G.n ^ 2 := G.rankC ▸ minpoly.natDegree_le yC
  rw [← Polynomial.coeff_map]
  exact Polynomial.coeff_bdd_of_roots_le φ hmon (IsAlgClosed.splits _) hdeg hroot k

end GlobalTheory.LKCx.PadicPolys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BtOrderEqTopOfEtale
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.FinPtsAway

theorem supp_compact (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ)
    (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f) :
    ∃ Q : Set G.GAf, IsCompact Q ∧ ∀ g, f g ≠ 0 → g ∈ Q := by
  obtain ⟨-, -, -, S, hS⟩ := hf
  refine ⟨⋃ s ∈ S, (fun k : G.GAf × G.GAf => k.1 * s * k.2) '' ((L.K : Set G.GAf) ×ˢ (L.K : Set G.GAf)), ?_, ?_⟩
  · exact S.isCompact_biUnion fun s _ => (L.compact.prod L.compact).image (by fun_prop)
  · intro g hg
    obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩ := hS g hg
    exact Set.mem_iUnion₂.2 ⟨s, hs, (k₁, k₂), ⟨hk₁, hk₂⟩, rfl⟩

theorem coeff_continuous (p : ℕ) [Fact p.Prime] (G : HTGroup p) (k : ℕ) :
    Continuous fun g : G.GAf => (LinearMap.charpoly (LinearMap.mulLeft (AfP p)
      (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C))).coeff k :=
  GlobalTheory.T.continuous_charpoly_coeff_mulLeft_finiteAdeles_awayP p G k

theorem bdd_at_places (p : ℕ) [Fact p.Prime] (Q : Set (AfP p)) (hQ : IsCompact Q) :
    ∃ D : ℕ, 0 < D ∧ ∀ a ∈ Q, ∀ v : AwayP p, AfP.eval v ((D : AfP p) * a) ∈ v.1.adicCompletionIntegers ℚ :=
  GlobalTheory.T.compact_finiteAdelesAwayP_bounded_denominators p Q hQ

theorem rat_of_integral_away (p : ℕ) [Fact p.Prime] (q : ℚ)
    (hq : ∀ v : AwayP p, algebraMap ℚ (v.1.adicCompletion ℚ) q ∈ v.1.adicCompletionIntegers ℚ) :
    ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * q = z :=
  GlobalTheory.T.exists_prime_pow_mul_rat_eq_int_of_integral_away p q hq

theorem bdd_denom (p : ℕ) [Fact p.Prime] (Q : Set (AfP p)) (hQ : IsCompact Q) :
    ∃ D : ℕ, 0 < D ∧ ∀ q : ℚ, algebraMap ℚ (AfP p) q ∈ Q → ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * D * q = z := by
  obtain ⟨D, hD, hQD⟩ := bdd_at_places p Q hQ
  refine ⟨D, hD, fun q hq => ?_⟩
  obtain ⟨m, z, hz⟩ := rat_of_integral_away p (D * q) fun v => by
    have := hQD _ hq v
    rwa [← map_natCast (algebraMap ℚ (AfP p)), ← map_mul, (AfP.eval v).commutes] at this
  exact ⟨m, z, by rw [← hz, mul_assoc]⟩

theorem charpoly_conj_tmul (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (A : Type) [CommRing A]
    [Algebra ℚ A] (y : C) (u : (A ⊗[ℚ] C)ˣ) :
    LinearMap.charpoly (LinearMap.mulLeft A ((u : A ⊗[ℚ] C) * ((1 : A) ⊗ₜ[ℚ] y) * ((u⁻¹ : (A ⊗[ℚ] C)ˣ) : A ⊗[ℚ] C))) =
      (LinearMap.charpoly (LinearMap.mulLeft ℚ y)).map (algebraMap ℚ A) := by
  let e : (A ⊗[ℚ] C) ≃ₗ[A] (A ⊗[ℚ] C) :=
    { LinearMap.mulLeft A (u : A ⊗[ℚ] C) with
      invFun := fun z => ((u⁻¹ : (A ⊗[ℚ] C)ˣ) : A ⊗[ℚ] C) * z
      left_inv := fun z => by simp [← mul_assoc]
      right_inv := fun z => by simp [← mul_assoc] }
  have h1 : LinearMap.mulLeft A ((u : A ⊗[ℚ] C) * ((1 : A) ⊗ₜ[ℚ] y) * ((u⁻¹ : (A ⊗[ℚ] C)ˣ) : A ⊗[ℚ] C)) =
      e.conj (LinearMap.mulLeft A ((1 : A) ⊗ₜ[ℚ] y)) := by
    ext z
    simp [e, LinearEquiv.conj_apply, mul_assoc]
  have h2 : LinearMap.mulLeft A ((1 : A) ⊗ₜ[ℚ] y) = (LinearMap.mulLeft ℚ y).baseChange A := by
    ext c
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [h1, LinearEquiv.charpoly_conj, h2, LinearMap.charpoly_baseChange]

theorem integral_of_charpoly (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (y : C) (p D : ℕ)
    (h : ∀ i, ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * D * (LinearMap.charpoly (LinearMap.mulLeft ℚ y)).coeff i = z) :
    ∃ m : ℕ, IsIntegral ℤ ((p : C) ^ m * D * y) := by
  choose m z hz using h
  set χ := LinearMap.charpoly (LinearMap.mulLeft ℚ y) with hχ
  set N := χ.natDegree
  set M := ∑ i ∈ Finset.range N, m i
  refine ⟨M, ?_⟩
  set s : ℚ := (p : ℚ) ^ M * D with hs
  have hχy : Polynomial.aeval y χ = 0 := by
    have e := LinearMap.aeval_self_charpoly (LinearMap.mulLeft ℚ y)
    have e2 : Polynomial.aeval (LinearMap.mulLeft ℚ y) χ = Algebra.lmul ℚ C (Polynomial.aeval y χ) := by
      rw [← Polynomial.aeval_algHom_apply]; rfl
    rw [e2] at e
    have := congrArg (fun f : Module.End ℚ C => f 1) e
    simpa using this
  have hlift : χ.scaleRoots s ∈ Polynomial.lifts (algebraMap ℤ ℚ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy i N with hi | hi | hi
    · have hmi : m i ≤ M := Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_range.2 hi)
      refine ⟨(p : ℤ) ^ (M - m i) * z i * ((p : ℤ) ^ M * D) ^ (N - i - 1), ?_⟩
      have e1 : s ^ (N - i) = s * s ^ (N - i - 1) := by
        rw [← pow_succ']; congr 1; omega
      have e2 : s * χ.coeff i = (p : ℚ) ^ (M - m i) * z i := by
        rw [← hz i, hs, ← mul_assoc, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hmi]
      simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      rw [e1, ← mul_assoc, mul_comm (χ.coeff i) s, e2, hs]
    · subst hi
      refine ⟨1, ?_⟩
      rw [Nat.sub_self, pow_zero, mul_one, ← Polynomial.leadingCoeff, LinearMap.charpoly_monic]; simp
    · refine ⟨0, ?_⟩
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi]; simp
  obtain ⟨P, hP, hPdeg, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift
    ((Polynomial.monic_scaleRoots_iff s).2 (LinearMap.charpoly_monic _))
  refine ⟨P, hPm, ?_⟩
  have e3 : Polynomial.eval₂ (algebraMap ℤ C) ((p : C) ^ M * D * y) P =
      Polynomial.aeval ((p : C) ^ M * D * y) (χ.scaleRoots s) := by
    rw [← hP, Polynomial.aeval_map_algebraMap, Polynomial.aeval_def]
  rw [e3, Polynomial.aeval_def]
  have e4 : (p : C) ^ M * D * y = algebraMap ℚ C s * y := by
    rw [hs]; simp
  rw [e4, Polynomial.scaleRoots_eval₂_mul_of_commute _ _ _ (Algebra.commutes _ _) (fun a b => Algebra.commutes _ _),
    ← Polynomial.aeval_def, hχy, mul_zero]

theorem minpoly_coeff_integral (F : Type) [Field F] (S : Type) [Ring S] [Algebra F S] (y : S) (c : F)
    (hc : IsIntegral ℤ (algebraMap F S c * y)) (hy : IsIntegral F y) (k : ℕ) :
    IsIntegral ℤ (c ^ ((minpoly F y).natDegree - k) * (minpoly F y).coeff k) := by
  by_cases hc0 : c = 0
  · subst hc0
    rcases lt_trichotomy k (minpoly F y).natDegree with hk | hk | hk
    · rw [zero_pow (by omega), zero_mul]; exact isIntegral_zero
    · rw [hk, Nat.sub_self, pow_zero, one_mul, ← Polynomial.leadingCoeff, minpoly.monic hy, ]; exact isIntegral_one
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk, mul_zero]; exact isIntegral_zero
  obtain ⟨P, hPm, hP⟩ := hc
  set Pm := P.map (algebraMap ℤ F)
  have hPz : Polynomial.eval₂ (algebraMap F S) (algebraMap F S c * y) Pm = 0 := by
    rw [Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq]; exact hP
  have h1 : Polynomial.aeval y (Pm.scaleRoots c⁻¹) = 0 := by
    have e := Polynomial.scaleRoots_eval₂_mul_of_commute (p := Pm) (algebraMap F S) (algebraMap F S c * y) c⁻¹
      (Algebra.commutes _ _) (fun a b => Algebra.commutes _ _)
    rw [hPz, mul_zero, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul] at e
    rw [Polynomial.aeval_def]; exact e
  have h2 : minpoly F y ∣ Pm.scaleRoots c⁻¹ := minpoly.dvd F y h1
  have h3 : (minpoly F y).scaleRoots c ∣ Pm := by
    have := Polynomial.scaleRoots_dvd _ _ (r := c) h2
    rwa [← Polynomial.scaleRoots_mul, inv_mul_cancel₀ hc0, Polynomial.scaleRoots_one] at this
  have h4 := Polynomial.isIntegral_coeff_of_dvd P _ hPm ((Polynomial.monic_scaleRoots_iff c).2 (minpoly.monic hy)) h3 k
  rw [Polynomial.coeff_scaleRoots, mul_comm] at h4
  exact h4

theorem exists_den_minpoly_coeff : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), ∃ D : ℕ, 0 < D ∧ ∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → ∀ k : ℕ, ∃ m : ℕ, IsIntegral ℤ ((p : G.F) ^ m * D * (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).coeff k) := by
  intro p _ G L f hf β x t hx
  obtain ⟨Q, hQc, hQ⟩ := supp_compact p G L f hf
  set N := Module.finrank ℚ G.C
  let cf : ℕ → G.GAf → AfP p := fun k g => (LinearMap.charpoly (LinearMap.mulLeft (AfP p)
      (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C))).coeff k
  have hQ'c : IsCompact (⋃ k ∈ Finset.range (N + 1), cf k '' Q) :=
    (Finset.range (N + 1)).isCompact_biUnion fun k _ => hQc.image (coeff_continuous p G k)
  obtain ⟨D', hD'0, hD'⟩ := bdd_denom p _ hQ'c
  refine ⟨D' ^ Module.finrank G.F G.C, pow_pos hD'0 _, ?_⟩
  intro y h hfy k
  set yc : G.C := (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) with hyc
  have hg := hQ _ hfy

  set u : (AfP p ⊗[ℚ] G.C)ˣ := ((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ * x with hu
  have hrep : ((((h⁻¹ * toAfF G β x t hx y * h : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) =
      (u : AfP p ⊗[ℚ] G.C) * ((1 : AfP p) ⊗ₜ[ℚ] yc) * ((u⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := by
    have e : (((h⁻¹ * toAfF G β x t hx y * h : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) =
        u * Units.map (inC G (AfP p)).toMonoidHom ((y : G.Cˣ × ℚˣ).1) * u⁻¹ := by
      have e0 : (((h⁻¹ * toAfF G β x t hx y * h : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) =
          ((h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)⁻¹ * (x * Units.map (inC G (AfP p)).toMonoidHom ((y : G.Cˣ × ℚˣ).1) * x⁻¹) *
            (h : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 := rfl
      rw [e0, hu]; group
    rw [e]; simp only [Units.val_mul]; rfl
  have hchar : LinearMap.charpoly (LinearMap.mulLeft (AfP p)
      ((((h⁻¹ * toAfF G β x t hx y * h : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) =
      (LinearMap.charpoly (LinearMap.mulLeft ℚ yc)).map (algebraMap ℚ (AfP p)) := by
    rw [hrep]; exact charpoly_conj_tmul G.C (AfP p) yc u
  have hcoef : ∀ i, ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * D' * (LinearMap.charpoly (LinearMap.mulLeft ℚ yc)).coeff i = z := by
    intro i
    by_cases hi : i ≤ N
    · apply hD'
      refine Set.mem_iUnion₂.2 ⟨i, Finset.mem_range.2 (Nat.lt_succ_of_le hi), _, hg, ?_⟩
      simp only [cf]
      rw [hchar, Polynomial.coeff_map]
    · refine ⟨0, 0, ?_⟩
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [LinearMap.charpoly_natDegree]; omega)]
      simp
  obtain ⟨M, hM⟩ := integral_of_charpoly G.C yc p D' hcoef
  have hint : IsIntegral ℤ (algebraMap G.F G.C ((p : G.F) ^ M * D') * yc) := by
    convert hM using 2
    simp [map_mul, map_pow, map_natCast]
  have hI := minpoly_coeff_integral G.F G.C yc _ hint (Algebra.IsIntegral.isIntegral _) k
  set d := (minpoly G.F yc).natDegree
  have hd : d ≤ Module.finrank G.F G.C := minpoly.natDegree_le yc
  by_cases hk : k ≤ d
  · refine ⟨M * (d - k), ?_⟩
    have e : (p : G.F) ^ (M * (d - k)) * ((D' ^ Module.finrank G.F G.C : ℕ) : G.F) * (minpoly G.F yc).coeff k =
        (D' : G.F) ^ (Module.finrank G.F G.C - (d - k)) *
          (((p : G.F) ^ M * D') ^ (d - k) * (minpoly G.F yc).coeff k) := by
      rw [mul_pow, ← pow_mul, Nat.cast_pow]
      have : Module.finrank G.F G.C = (Module.finrank G.F G.C - (d - k)) + (d - k) := by omega
      conv_lhs => rw [this, pow_add]
      ring
    rw [e]
    have hD : IsIntegral ℤ (D' : G.F) := by
      simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ G.F (D' : ℤ)))
    exact (hD.pow _).mul hI
  · refine ⟨0, ?_⟩
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
    exact isIntegral_zero

end GlobalTheory.FinPtsAway
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellVarietyDimensionCountsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_variety_dimension_counts : ∀ (ι : Type) [Fintype ι] (N : ℕ), Nat.card (CellVar (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd) = dimFl ι N ∧ (∀ j : Fin (N + 1), Nat.card (CellVar (id : ι → ι) (fun _ => j)) = dimGr ι N j) ∧ ∀ x : ι × Fin (N + 1), 0 < (x.2 : ℕ) → (x.2 : ℕ) < N → Nat.card (CellVar (fun y : {y // y ≠ x} => y.1.1) (fun y => y.1.2)) + 1 = dimFl ι N := by
  first | exact @GlobalTheory.FlagZ.Count.card_cellVar | exact GlobalTheory.FlagZ.Count.card_cellVar | (intros; apply GlobalTheory.FlagZ.Count.card_cellVar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerElementPadicBounded
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_element_padic_bounded : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (r : ℕ) (z : Gr G r) (K : Subgroup (Gr G r)) (g : Gr G r), 0 < r → Subgroup.Commensurable K (KHT p G.m G.n r G.Fw) → ∀ w : P.cent, P.toQr r z w ∈ K.map (MulAut.conj g).toMonoidHom → ∀ (a : FM P), jM P a = ((w : G.Cˣ × ℚˣ).1 : G.C) → ∀ τ : FM P →+* PadicAlgCl p, LiesOver G.Kq G.u (τ.comp (algebraMap G.F (FM P))) → ‖τ a‖ ≤ 1 := by
  first | (exact @GlobalTheory.StabFin.norm_le_one_at_u) | (exact GlobalTheory.StabFin.norm_le_one_at_u) | (intros; apply GlobalTheory.StabFin.norm_le_one_at_u  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerFiniteDecomposition
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.OrbFinP

def FinConj {H : Type} [Group H] (U : Subgroup H) (a : H) : Prop :=
  ∀ E : Finset H, ∃ D : Finset H, ∀ x : H, (∃ e ∈ E, ∃ k ∈ U, x⁻¹ * a * x = e * k) →
    ∃ t : H, t * a = a * t ∧ ∃ d ∈ D, ∃ k ∈ U, x = t * d * k

theorem finConj_of_central {H : Type} [Group H] (U : Subgroup H) (a : H) (ha : ∀ x, x * a = a * x) :
    FinConj U a :=
  fun _ => ⟨{1}, fun x _ => ⟨x, ha x, 1, Finset.mem_singleton_self _, 1, U.one_mem, by simp⟩⟩

theorem finConj_prod {H₁ H₂ : Type} [Group H₁] [Group H₂] (U₁ : Subgroup H₁) (U₂ : Subgroup H₂) (a₁ : H₁)
    (a₂ : H₂) (h₁ : FinConj U₁ a₁) (h₂ : FinConj U₂ a₂) : FinConj (U₁.prod U₂) (a₁, a₂) := by
  intro E
  obtain ⟨D₁, hD₁⟩ := h₁ (E.image Prod.fst)
  obtain ⟨D₂, hD₂⟩ := h₂ (E.image Prod.snd)
  refine ⟨D₁ ×ˢ D₂, fun x ⟨e, he, k, hk, hx⟩ => ?_⟩
  have hk' := Subgroup.mem_prod.1 hk
  obtain ⟨t₁, ht₁, d₁, hd₁, k₁, hk₁, hx₁⟩ :=
    hD₁ x.1 ⟨e.1, Finset.mem_image_of_mem _ he, k.1, hk'.1, congrArg Prod.fst hx⟩
  obtain ⟨t₂, ht₂, d₂, hd₂, k₂, hk₂, hx₂⟩ :=
    hD₂ x.2 ⟨e.2, Finset.mem_image_of_mem _ he, k.2, hk'.2, congrArg Prod.snd hx⟩
  exact ⟨(t₁, t₂), Prod.ext ht₁ ht₂, (d₁, d₂), Finset.mem_product.2 ⟨hd₁, hd₂⟩, (k₁, k₂),
    Subgroup.mem_prod.2 ⟨hk₁, hk₂⟩, Prod.ext hx₁ hx₂⟩

theorem finConj_pi {ι : Type} [Fintype ι] {H : ι → Type} [∀ i, Group (H i)] (U : ∀ i, Subgroup (H i))
    (a : ∀ i, H i) (h : ∀ i, FinConj (U i) (a i)) : FinConj (Subgroup.pi Set.univ U) a := by
  intro E
  choose D hD using fun i => h i (E.image fun e => e i)
  refine ⟨Fintype.piFinset D, fun x ⟨e, he, k, hk, hx⟩ => ?_⟩
  choose t ht d hd k' hk' hxe using fun i =>
    hD i (x i) ⟨e i, Finset.mem_image_of_mem _ he, k i, hk i (Set.mem_univ i), congrFun hx i⟩
  exact ⟨t, funext ht, d, Fintype.mem_piFinset.2 hd, k', fun i _ => hk' i, funext hxe⟩

theorem finConj_map {H H' : Type} [Group H] [Group H'] (ψ : H ≃* H') (U : Subgroup H) (U' : Subgroup H')
    (hU : ∀ k, k ∈ U ↔ ψ k ∈ U') (a : H) (h : FinConj U' (ψ a)) : FinConj U a := by
  intro E
  obtain ⟨D, hD⟩ := h (E.image ψ)
  refine ⟨D.image ψ.symm, fun x ⟨e, he, k, hk, hx⟩ => ?_⟩
  obtain ⟨t, ht, d, hd, k', hk', hxe⟩ := hD (ψ x) ⟨ψ e, Finset.mem_image_of_mem _ he, ψ k, (hU k).1 hk,
    by rw [← map_inv, ← map_mul, ← map_mul, hx, map_mul]⟩
  refine ⟨ψ.symm t, ?_, ψ.symm d, Finset.mem_image_of_mem _ hd, ψ.symm k', (hU _).2 (by simpa using hk'), ?_⟩
  · apply ψ.injective; simp [map_mul, ht]
  · apply ψ.injective; simp [map_mul, hxe]

theorem finConj_field {k : Type} [NontriviallyNormedField k] {n : ℕ} (U : Subgroup (GL (Fin n) k))
    (hUo : IsOpen (U : Set (GL (Fin n) k))) (hUc : IsCompact (U : Set (GL (Fin n) k))) (a : GL (Fin n) k)
    (ha : (a : Matrix (Fin n) (Fin n) k).charpoly.Separable) : FinConj U a := by
  intro E
  set Z : Set (Matrix (Fin n) (Fin n) k) := (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k)) ''
    (⋃ e ∈ E, (fun u => e * u) '' (U : Set (GL (Fin n) k))) with hZdef
  have hZ : IsCompact Z := (E.isCompact_biUnion fun e _ =>
    hUc.image (continuous_const.mul continuous_id)).image Units.continuous_val
  obtain ⟨C, hC, hCg⟩ := GlobalTheory.OrbCpt.gl_orbit_cpt (a : Matrix (Fin n) (Fin n) k) ha Z hZ
  have hCi : IsCompact ((fun c => c⁻¹) '' C) := hC.image continuous_inv
  obtain ⟨D, hD⟩ := hCi.elim_finite_subcover (fun d : GL (Fin n) k => (fun u => d * u) '' (U : Set _))
    (fun d => isOpenMap_mul_left d _ hUo)
    (fun y _ => Set.mem_iUnion.2 ⟨y, 1, U.one_mem, mul_one y⟩)
  refine ⟨D, fun x ⟨e, he, u, hu, hx⟩ => ?_⟩
  have hxZ : ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * a *
      ((x⁻¹⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈ Z :=
    ⟨x⁻¹ * a * x, Set.mem_iUnion₂.2 ⟨e, he, u, hu, hx.symm⟩, by simp [inv_inv]⟩
  obtain ⟨c, hc, t, ht, hxct⟩ := hCg x⁻¹ hxZ
  obtain ⟨d, hdD, v, hv, hdv⟩ := Set.mem_iUnion₂.1 (hD ⟨c, hc, rfl⟩)
  have ht' : t * a = a * t := Units.ext ht
  refine ⟨t⁻¹, ?_, d, hdD, v, hv, ?_⟩
  · calc t⁻¹ * a = t⁻¹ * (a * t) * t⁻¹ := by group
      _ = t⁻¹ * (t * a) * t⁻¹ := by rw [ht']
      _ = a * t⁻¹ := by group
  · have hdv' : d * v = c⁻¹ := hdv
    rw [mul_assoc, hdv', ← _root_.mul_inv_rev, ← hxct, inv_inv]

def glPi {R S : Type} [CommRing R] [CommRing S] (k n : ℕ) (e : R ≃+* (Fin k → S)) :
    GL (Fin n) R ≃* (Fin k → GL (Fin n) S) :=
  (Units.mapEquiv (e.mapMatrix.trans (matPiEquiv S n k)).toMulEquiv).trans MulEquiv.piUnits

theorem glPi_mem_iff {R S : Type} [CommRing R] [CommRing S] (k n : ℕ) (e : R ≃+* (Fin k → S))
    (A : Subring R) (B : Subring S) (hAB : ∀ x : R, x ∈ A ↔ ∀ i, e x i ∈ B) (g : GL (Fin n) R) :
    g ∈ (GeneralLinearGroup.map (n := Fin n) A.subtype).range ↔
      glPi k n e g ∈ Subgroup.pi Set.univ (fun _ => (GeneralLinearGroup.map (n := Fin n) B.subtype).range) := by
  rw [Subgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, mem_range_map_subtype_iff, hAB]
  constructor
  · rintro ⟨h1, h2⟩ i
    exact ⟨fun a b => h1 a b i, fun a b => h2 a b i⟩
  · intro h
    exact ⟨fun a b i => (h i).1 a b, fun a b i => (h i).2 a b⟩

variable (p : ℕ) [Fact p.Prime]

theorem finConj_res_split (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [hK : FiniteDimensional ℚ_[p] K] (n r : ℕ)
    (k m : ℕ) (hm : 0 < m) (e : KQ p K r ≃+* (Fin k → ReciprocityTheory.DiscreteGroups.LocalClassField.Kn p K m))
    (hint : ∀ x : KQ p K r, x ∈ intKQ p K r ↔ ∀ i, e x i ∈ GlobalTheory.LKLoc.intR p K m)
    (g : GL (Fin n) K) (hg : (g : Matrix (Fin n) (Fin n) K).charpoly.Separable) :
    FinConj (Kres p K n r) (GeneralLinearGroup.map (inclK p K r).toRingHom g) := by
  have hp0 : ‖algebraMap ℚ_[p] (ReciprocityTheory.DiscreteGroups.LocalClassField.Kn p K m) p‖ = (p : ℝ)⁻¹ := by
    show ‖algebraMap ℚ_[p] (PadicAlgCl p) p‖ = _
    rw [PadicAlgCl.norm_extends, Padic.norm_p]
  have hp1 : (p : ℝ)⁻¹ ≠ 1 := inv_ne_one.2 (by exact_mod_cast (Fact.out : p.Prime).one_lt.ne')
  have hp2 : (p : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  letI : NontriviallyNormedField (ReciprocityTheory.DiscreteGroups.LocalClassField.Kn p K m) :=
    NontriviallyNormedField.ofNormNeOne ⟨algebraMap ℚ_[p] (ReciprocityTheory.DiscreteGroups.LocalClassField.Kn p K m) p, ?_, ?_⟩
  rotate_left
  · intro h; rw [h, norm_zero] at hp0; exact hp2 hp0.symm
  · rw [hp0]; exact hp1
  refine finConj_map (glPi _ n e) _ _ (fun k => glPi_mem_iff _ n e _ _ hint k) _ ?_
  refine finConj_pi _ _ fun i => ?_
  refine finConj_field _ (GlobalTheory.LKLoc.isOpen_Kint p K n m) (GlobalTheory.LKLoc.isCompact_Kint p K hK n m hm) _ ?_
  have hmat : ((glPi _ n e (GeneralLinearGroup.map (inclK p K r).toRingHom g) i : GL (Fin n) _) :
      Matrix (Fin n) (Fin n) _) = (g : Matrix (Fin n) (Fin n) K).map
        (((Pi.evalRingHom _ i).comp e.toRingHom).comp (inclK p K r).toRingHom) := by
    ext a b; rfl
  rw [hmat, Matrix.charpoly_map]
  exact hg.map

theorem finConj_res (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [hK : FiniteDimensional ℚ_[p] K] (n r : ℕ)
    (hr : 0 < r) (g : GL (Fin n) K) (hg : (g : Matrix (Fin n) (Fin n) K).charpoly.Separable) :
    FinConj (Kres p K n r) (GeneralLinearGroup.map (inclK p K r).toRingHom g) := by
  obtain ⟨e, τ, -, -, -, -, -, hint⟩ :=
    GlobalTheory.T.unramified_extension_product_decomposition p K hK (ReciprocityTheory.DiscreteGroups.LocalClassField.fK p K) r (ReciprocityTheory.DiscreteGroups.LocalClassField.qK_eq_pow_fK p K hK) hr
  exact finConj_res_split p K n r _ _ (Nat.div_pos (Nat.gcd_le_right _ hr) (Nat.gcd_pos_of_pos_right _ hr))
    e hint g hg

end GlobalTheory.OrbFinP

namespace GlobalTheory.OrbFinP

theorem orbit_fin_p : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → ∀ γ : Gp G, regular₂ G γ →
    ∀ E : Finset (Gr G r), ∃ D : Finset (Gr G r), ∀ x : Gr G r,
      (∃ e ∈ E, ∃ k ∈ KHT p G.m G.n r G.Fw, x⁻¹ * inclG G r γ * x = e * k) →
      ∃ t : Gr G r, t * inclG G r γ = inclG G r γ * t ∧ ∃ d ∈ D, ∃ k ∈ KHT p G.m G.n r G.Fw, x = t * d * k := by
  intro p _ G r hr γ hγ
  have key : FinConj (KHT p G.m G.n r G.Fw) (inclG G r γ) := by
    show FinConj ((GlobalTheory.LKLoc.Kint p (Q0 p) 1 r).prod (Subgroup.pi Set.univ fun i => Kres p (G.Fw i) G.n r))
      (GeneralLinearGroup.scalar (Fin 1) (Units.map (algebraMap ℚ_[p] (Qr p r)).toMonoidHom γ.1),
        fun w => GeneralLinearGroup.map (inclK p (G.Fw w) r).toRingHom (γ.2 w))
    refine finConj_prod _ _ _ _ (finConj_of_central _ _ fun x => ?_)
      (finConj_pi _ _ fun w => finConj_res p (G.Fw w) G.n r hr (γ.2 w) (hγ w))
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [Matrix.mul_apply, mul_comm]
  exact key

end GlobalTheory.OrbFinP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChangeOfFrameHolomorphicInvertibleHolomorphicCha
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem analyticAt_ratVal_holoChart {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F}
    {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} (he : IsHoloChart e) {y : CxPts X.str σ} (hy : y ∈ e.source)
    {g : X.Fn} (hg : RegAt (under y) g) : AnalyticAt ℂ (fun v => ratVal g (e.symm v)) (e y) := by
  obtain ⟨U, hU, a, rfl⟩ := hg.exists_fnOf
  have hn : e.target ∩ e.symm ⁻¹' ptsIn X.str σ U ∈ 𝓝 (e y) := by
    refine Filter.inter_mem (e.open_target.mem_nhds (e.map_source hy)) ?_
    exact (e.tendsto_symm hy) ((isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU))
  exact GlobalTheory.SCV.analyticAt_of_differentiableOn ((he U a).congr fun w hw => ratVal_fnOf hw.2 _ a) hn

theorem changeFrame_holoChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {y : CxPts X.str σ}, y ∈ e.source → ∀ {A A' : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → A' ∈ E.S (under y) → MContDiffAt 2 (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ) (e y) ∧ IsUnit (((A' * A⁻¹).map (ratVal · (e.symm (e y))) ())ᵀ).det ∧ ∀ᶠ x in 𝓝 (e y), ∀ η, mdbar (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ) x η = 0 := by
  intro F _ σ X m E e he y hy A A' hA hA'
  have hP : Par 0 ((ratOf X).O (under y)).toSubring (A' * A⁻¹) := (Fr.mem_iff hA).1 hA'
  have han (i j : Fin m) : AnalyticAt ℂ (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ i j) (e y) :=
    analyticAt_ratVal_holoChart he hy (mem_O_ratOf.1 ((hP ()).1 j i))
  refine ⟨fun i j => ((han i j).contDiffAt (n := 2)).restrict_scalars ℝ, ?_, ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_ratVal_hom y
    rw [Matrix.det_transpose, e.left_inv hy]
    exact ((hP.map_of (ratVal · y) ψ hψ).det_ne ()).isUnit
  · have h : ∀ᶠ x in 𝓝 (e y), ∀ i j : Fin m,
        AnalyticAt ℂ (fun v => ((A' * A⁻¹).map (ratVal · (e.symm v)) ())ᵀ i j) x :=
      eventually_all.2 fun i => eventually_all.2 fun j => (han i j).eventually_analyticAt
    filter_upwards [h] with x hx η
    ext i j
    rw [mdbar_apply, GlobalTheory.dbar_eq_zero (hx i j).differentiableAt]
    rfl

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralOneEqMongeAmpereIntegral
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
namespace GlobalTheory

theorem chernInt_one_eq_mInt : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → φ.ChernIntegrableOn Y.dim Set.univ (fun _ => 1) ∧ ∀ A : FinHolAtlas Y.dim (CxPts Y.str (RingHom.id ℂ)), IsAlgAtlas A → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = mInt A (fun _ => φ.locPot) (fun _ => 1) := by
  intro Y L φ h
  haveI : CompactSpace (CxPts Y.str (RingHom.id ℂ)) := CxPts.compactSpace _ Y.isProjOver
  haveI : T2Space (CxPts Y.str (RingHom.id ℂ)) := t2Space_cxPts_of_isProjOver _ Y.isProjOver
  haveI : SecondCountableTopology (CxPts Y.str (RingHom.id ℂ)) :=
    secondCountableTopology_of_isProjOver _ Y.isProjOver
  have hA₀ := AnRead.isAlgAtlas_finAtlas (AnRead.all Y.str (RingHom.id ℂ) Y.dim)
  have hi : φ.ChernIntegrableOn Y.dim Set.univ (fun _ => 1) :=
    (h.chernInt_eq_mInt_of_isAlgAtlas hA₀ measurable_const).1.2
      (mIntegrableCont _ _
        (fun _ => ((Weight.isCInf_iff_isSmooth hA₀.anRead).1 h).isPotential hA₀) _ continuous_const)
  exact ⟨hi, fun A hA => (h.chernInt_eq_mInt_of_isAlgAtlas hA measurable_const).2 hi⟩

end GlobalTheory
end

