import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianLocalRingFixedFieldInertia
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open Polynomial

namespace GlobalTheory

theorem isUnit_of_sub_mem_maximalIdeal' {A : Type*} [CommRing A] [IsLocalRing A] {x y : A}
    (h : x - y ∈ maximalIdeal A) (hy : IsUnit y) : IsUnit x := by
  by_contra hx
  have hx' : x ∈ maximalIdeal A := (mem_maximalIdeal x).2 hx
  have hy' : y ∈ maximalIdeal A := by
    have := Ideal.sub_mem _ hx' h
    simpa using this
  exact (mem_maximalIdeal y).1 hy' hy

theorem eq_of_isRoot_of_sub_mem_maximalIdeal {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    {f : A[X]} {a₀ b b' : A} (hu : IsUnit (f.derivative.eval a₀)) (hb : f.IsRoot b) (hb' : f.IsRoot b')
    (h1 : b - a₀ ∈ maximalIdeal A) (h2 : b' - a₀ ∈ maximalIdeal A) : b' = b := by
  set h := f /ₘ (X - C b) with hh
  have hf : f = (X - C b) * h := (mul_divByMonic_eq_iff_isRoot.2 hb).symm
  have hd : f.derivative.eval b = h.eval b := by
    rw [hf]
    simp [derivative_mul]
  have hub : IsUnit (h.eval b) := by
    rw [← hd]
    refine isUnit_of_sub_mem_maximalIdeal' ?_ hu
    obtain ⟨c, hc⟩ := sub_dvd_eval_sub b a₀ f.derivative
    rw [hc]
    exact Ideal.mul_mem_right _ _ h1
  have hub' : IsUnit (h.eval b') := by
    refine isUnit_of_sub_mem_maximalIdeal' ?_ hub
    obtain ⟨c, hc⟩ := sub_dvd_eval_sub b' b h
    rw [hc]
    apply Ideal.mul_mem_right
    have := Ideal.sub_mem _ h2 h1
    simpa using this
  have e : (b' - b) * h.eval b' = 0 := by
    have := hb'
    rw [IsRoot, hf] at this
    simpa using this
  rcases mul_eq_zero.1 e with e | e
  · exact sub_eq_zero.1 e
  · exact absurd e hub'.ne_zero

end GlobalTheory

namespace GlobalTheory

theorem henselianLocalRing_of_isSepClosed {Ω : Type} [Field Ω] [IsSepClosed Ω] (V : ValuationSubring Ω) :
    HenselianLocalRing V := by
  classical
  obtain ⟨W, rfl⟩ := exists_valuationSubring_comap_eq V (algebraMap Ω (AlgebraicClosure Ω))
  refine @HenselianLocalRing.mk _ _ inferInstance ?_
  intro f hf a₀ h₁ h₂
  set ψ := comapToValuationSubring W (algebraMap Ω (AlgebraicClosure Ω))
  set ιW := algebraMap W (AlgebraicClosure Ω)
  set G := f.map ψ with hG
  set F := G.map ιW with hF
  have hFm : F.Monic := (hf.map ψ).map ιW
  have hint : ∀ r ∈ F.roots, ∃ r' : W, ιW r' = r := by
    intro r hr
    have hi : IsIntegral W r := ⟨G, hf.map ψ, by
      rw [← Polynomial.eval_map]
      exact (mem_roots hFm.ne_zero).1 hr⟩
    exact IsIntegrallyClosed.isIntegral_iff.1 hi
  have hψm : ψ (f.eval a₀) ∈ maximalIdeal W :=
    (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 h₁ (IsUnit.of_map ψ _ hu)

  obtain ⟨r, hr, hrv⟩ : ∃ r ∈ F.roots, W.valuation (ιW (ψ a₀) - r) < 1 := by
    by_contra hne
    push_neg at hne
    have hprod : F.eval (ιW (ψ a₀)) = (F.roots.map fun r => ιW (ψ a₀) - r).prod := by
      conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hFm
        IsAlgClosed.card_roots_eq_natDegree]
      rw [eval_multiset_prod, Multiset.map_map]
      simp
    have h1 : W.valuation (F.eval (ιW (ψ a₀))) = 1 := by
      rw [hprod, map_multiset_prod, Multiset.map_map]
      apply Multiset.prod_eq_one
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
      have hle := hne y hy
      obtain ⟨y', rfl⟩ := hint y hy
      refine le_antisymm ?_ hle
      simp only [Function.comp_apply]
      rw [← map_sub]
      exact W.valuation_le_one (ψ a₀ - y')
    have h2 : W.valuation (F.eval (ιW (ψ a₀))) < 1 := by
      rw [hF, Polynomial.eval_map, eval₂_at_apply, hG, Polynomial.eval_map, eval₂_at_apply]
      exact (W.valuation_lt_one_iff _).1 hψm
    exact absurd h1 h2.ne
  obtain ⟨r', rfl⟩ := hint r hr
  have hr'm : r' - ψ a₀ ∈ maximalIdeal W := by
    rw [← neg_sub, Ideal.neg_mem_iff, W.valuation_lt_one_iff]
    simpa [ιW] using hrv
  have hGd : IsUnit (G.derivative.eval r') := by
    refine isUnit_of_sub_mem_maximalIdeal' ?_ (y := G.derivative.eval (ψ a₀)) ?_
    · obtain ⟨c, hc⟩ := sub_dvd_eval_sub r' (ψ a₀) G.derivative
      rw [hc]
      exact Ideal.mul_mem_right _ _ hr'm
    · rw [hG, derivative_map, Polynomial.eval_map, eval₂_at_apply]
      exact h₂.map ψ
  have hFd : F.derivative.eval (ιW r') ≠ 0 := by
    rw [hF, derivative_map, Polynomial.eval_map, eval₂_at_apply]
    exact fun e => hGd.ne_zero ((injective_iff_map_eq_zero ιW).1 (FaithfulSMul.algebraMap_injective W (AlgebraicClosure Ω)) _ e)
  have hιinj : Function.Injective ιW := FaithfulSMul.algebraMap_injective W (AlgebraicClosure Ω)
  have hψinj : Function.Injective ψ := fun x y e =>
    Subtype.ext ((algebraMap Ω (AlgebraicClosure Ω)).injective (congrArg Subtype.val e))

  set F₀ : Polynomial Ω := f.map (W.comap (algebraMap Ω (AlgebraicClosure Ω))).subtype with hF₀
  have hF₀F : F₀.map (algebraMap Ω (AlgebraicClosure Ω)) = F := by
    rw [hF₀, hF, hG, Polynomial.map_map, Polynomial.map_map]
    rfl
  have hintΩ : IsIntegral Ω (ιW r') := Algebra.IsIntegral.isIntegral _
  have hroot0 : aeval (ιW r') F₀ = 0 := by
    rw [aeval_def, ← Polynomial.eval_map, hF₀F]
    exact (mem_roots hFm.ne_zero).1 hr
  obtain ⟨h, hh⟩ := minpoly.dvd Ω (ιW r') hroot0
  have hq : aeval (ιW r') (derivative (minpoly Ω (ιW r'))) ≠ 0 := by
    intro e
    apply hFd
    have : aeval (ιW r') (derivative F₀) = 0 := by
      rw [hh, derivative_mul, map_add, map_mul, map_mul, e, minpoly.aeval]
      ring
    rw [aeval_def, ← Polynomial.eval_map, ← Polynomial.derivative_map, hF₀F] at this
    exact this
  have hsep : (minpoly Ω (ιW r')).Separable :=
    (Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible hintΩ)).2 (fun e => hq (by rw [e, map_zero]))
  have hdeg := IsSepClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hintΩ) hsep
  obtain ⟨b, hb⟩ := minpoly.natDegree_eq_one_iff.1 (natDegree_eq_of_degree_eq_some hdeg)
  have hbW : b ∈ W.comap (algebraMap Ω (AlgebraicClosure Ω)) := by
    rw [ValuationSubring.mem_comap, hb]
    exact r'.2
  have hψb : ψ ⟨b, hbW⟩ = r' := Subtype.ext hb
  have hGr : G.eval r' = 0 := by
    apply hιinj
    rw [map_zero, ← eval₂_at_apply, ← Polynomial.eval_map, ← hF]
    exact (mem_roots hFm.ne_zero).1 hr
  refine ⟨⟨b, hbW⟩, ?_, ?_⟩
  · apply hψinj
    rw [map_zero, ← eval₂_at_apply, ← Polynomial.eval_map, hψb, ← hG]
    exact hGr
  · refine (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 hr'm ?_
    have := hu.map ψ
    rwa [map_sub, hψb] at this

end GlobalTheory

namespace GlobalTheory

theorem henselianLocalRing_comap_fixedField_inertia (K : Type) {Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    [IsSepClosed Ω] (V : ValuationSubring Ω) :
    HenselianLocalRing (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) := by
  classical
  haveI := henselianLocalRing_of_isSepClosed V
  set K' := IntermediateField.fixedField (inertia K V)
  set j := comapToValuationSubring V (algebraMap K' Ω)
  have hjinj : Function.Injective j := fun x y e =>
    Subtype.ext ((algebraMap K' Ω).injective (congrArg (fun z : V => (z : Ω)) e))
  refine @HenselianLocalRing.mk _ _ inferInstance ?_
  intro f hf a₀ h₁ h₂
  have h₁' : (f.map j).eval (j a₀) ∈ maximalIdeal V := by
    rw [Polynomial.eval_map, eval₂_at_apply]
    exact (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 h₁ (IsUnit.of_map j _ hu)
  have h₂' : IsUnit ((f.map j).derivative.eval (j a₀)) := by
    rw [derivative_map, Polynomial.eval_map, eval₂_at_apply]
    exact h₂.map j
  obtain ⟨b, hb, hba⟩ := HenselianLocalRing.is_henselian (f.map j) (hf.map j) (j a₀) h₁' h₂'

  set κ : V.comap (algebraMap K' Ω) →+* Ω := V.subtype.comp j with hκ
  have hbΩ : f.eval₂ κ (b : Ω) = 0 := by
    have : V.subtype ((f.map j).eval b) = 0 := by rw [hb.eq_zero, map_zero]
    rw [Polynomial.eval_map, hom_eval₂] at this
    exact this
  have hfix : ∀ σ ∈ inertia K V, σ (b : Ω) = b := by
    intro σ hσ
    obtain ⟨hσV, hσv⟩ := (mem_inertia_iff V σ).1 hσ
    have hmem : σ (b : Ω) ∈ V := by
      have := ValuationSubring.smul_mem_pointwise_smul σ (b : Ω) V b.2
      rwa [hσV] at this
    have hσκ : (σ : Ω →+* Ω).comp κ = κ := by
      ext x
      exact (IntermediateField.mem_fixedField_iff _ _).1 (x : K').2 σ hσ
    have hc : (f.map j).IsRoot ⟨σ b, hmem⟩ := by
      apply V.subtype_injective
      rw [map_zero, Polynomial.eval_map, hom_eval₂]
      have e := congrArg (σ : Ω →+* Ω) hbΩ
      rw [map_zero, hom_eval₂, hσκ] at e
      exact e
    have hcm : (⟨σ b, hmem⟩ : V) - j a₀ ∈ maximalIdeal V := by
      have hd : (⟨σ b, hmem⟩ : V) - b ∈ maximalIdeal V := by
        rw [V.valuation_lt_one_iff]
        exact hσv b b.2
      have := Ideal.add_mem _ hd hba
      simpa using this
    have := eq_of_isRoot_of_sub_mem_maximalIdeal h₂' hb hc hba hcm
    exact congrArg Subtype.val this
  have hbK : (b : Ω) ∈ K' := (IntermediateField.mem_fixedField_iff _ _).2 hfix
  have hbV : (⟨b, hbK⟩ : K') ∈ V.comap (algebraMap K' Ω) := b.2
  have hjb : j ⟨⟨b, hbK⟩, hbV⟩ = b := Subtype.ext rfl
  refine ⟨⟨⟨b, hbK⟩, hbV⟩, ?_, ?_⟩
  · apply hjinj
    rw [map_zero, ← eval₂_at_apply, ← Polynomial.eval_map, hjb]
    exact hb
  · refine (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 hba ?_
    have := hu.map j
    rwa [map_sub, hjb] at this

theorem henselianLocalRing_fixedField_inertia : ∀ (R K Ω : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring →
    HenselianLocalRing (V.comap (algebraMap (IntermediateField.fixedField (inertia K V)) Ω)) := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V _
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  exact henselianLocalRing_comap_fixedField_inertia K V

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaConjMemSmul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem inertia_conj_mem_smul : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω)
    (g σ : Ω ≃ₐ[K] Ω), σ ∈ inertia K V → g * σ * g⁻¹ ∈ inertia K (g • V) := by
  intro K Ω _ _ _ V g σ hσ
  rw [mem_inertia_iff] at hσ ⊢
  obtain ⟨h1, h2⟩ := hσ

  have hn : ∀ z : Ω, V.valuation z < 1 → (g • V).valuation (g z) < 1 := by
    intro z hz
    rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or] at hz ⊢
    rcases hz with hz | hz
    · left; simp [hz]
    · right
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      intro h
      apply hz
      have : (g⁻¹ • (g z)⁻¹) = z⁻¹ := by
        change g⁻¹ ((g z)⁻¹) = z⁻¹
        rw [map_inv₀]
        simp
      rwa [this] at h
  refine ⟨?_, ?_⟩
  · rw [mul_smul, mul_smul, inv_smul_smul, h1]
  · intro x hx
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hx
    set y := g⁻¹ • x with hy
    have hxy : x = g y := by simp [hy]
    have : (g * σ * g⁻¹) x - x = g (σ y - y) := by
      rw [map_sub, hxy]
      simp
    rw [this]
    exact hn _ (h2 y hx)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaLiftOfPurelyInseparable
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InertiaLift

theorem mem_iff_pow_mem {F : Type} [Field F] (A : ValuationSubring F) {m : ℕ} (hm : 0 < m) (y : F) :
    y ∈ A ↔ y ^ m ∈ A := by
  rw [← A.valuation_le_one_iff, ← A.valuation_le_one_iff, map_pow]
  exact (pow_le_one_iff_of_nonneg zero_le' hm.ne').symm

theorem nonunit_of_pow {F : Type} [Field F] (A : ValuationSubring F) {m : ℕ} (hm : 0 < m) (z : F)
    (h : A.valuation (z ^ m) < 1) : A.valuation z < 1 := by
  rw [map_pow] at h
  by_contra h'
  push_neg at h'
  exact absurd h (not_lt.2 (one_le_pow₀ h'))

end GlobalTheory.InertiaLift

open GlobalTheory.InertiaLift in
theorem GlobalTheory.inertia_lift_of_purelyInseparable : ∀ (K L Ω Ω' : Type) [Field K] [Field L] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra L Ω'] [Algebra K Ω'] (j : Ω →ₐ[K] Ω'), (∀ y : Ω', ∃ (m : ℕ) (x : Ω), 0 < m ∧ y ^ m = j x ∧ ∀ a b : Ω', (a - b) ^ m = a ^ m - b ^ m) → ∀ (V' : ValuationSubring Ω') (σ : Ω ≃ₐ[K] Ω) (σ' : Ω' ≃ₐ[L] Ω'), (∀ x, σ' (j x) = j (σ x)) → σ ∈ inertia K (V'.comap (j : Ω →+* Ω')) → σ' ∈ inertia L V' := by
  intro K L Ω Ω' _ _ _ _ _ _ _ j hpi V' σ σ' hcomm hσ
  rw [mem_inertia_iff] at hσ ⊢
  obtain ⟨hσV, hσv⟩ := hσ
  set V := V'.comap (j : Ω →+* Ω') with hV
  have hmemV : ∀ x, j x ∈ V' ↔ x ∈ V := fun x => Iff.rfl
  have hσmem : ∀ x, σ x ∈ V ↔ x ∈ V := by
    intro x
    constructor
    · intro h
      have h2 : σ x ∈ σ • V := by rw [hσV]; exact h
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at h2
      simpa using h2
    · intro h
      have h2 : σ • x ∈ σ • V := ValuationSubring.smul_mem_pointwise_smul σ x V h
      rw [hσV] at h2
      exact h2
  have hσ'mem : ∀ y, σ' y ∈ V' ↔ y ∈ V' := by
    intro y
    obtain ⟨m, x, hm, hyx, -⟩ := hpi y
    rw [mem_iff_pow_mem V' hm, mem_iff_pow_mem V' hm y, ← map_pow, hyx, hcomm, hmemV, hmemV, hσmem]
  have hlt : ∀ w, V.valuation w < 1 → V'.valuation (j w) < 1 := by
    intro w hw
    rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or] at hw ⊢
    rcases hw with hw | hw
    · left; simp [hw]
    · right
      rw [← map_inv₀]
      exact hw
  refine ⟨?_, ?_⟩
  · ext z
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    have := hσ'mem (σ'⁻¹ • z)
    simp only [AlgEquiv.smul_def] at this ⊢
    rw [← this]
    simp
  · intro y hy
    obtain ⟨m, x, hm, hyx, hfrob⟩ := hpi y
    have hx : x ∈ V := by rw [← hmemV, ← hyx]; exact (mem_iff_pow_mem V' hm y).1 hy
    apply nonunit_of_pow V' hm
    rw [hfrob, ← map_pow, hyx, hcomm, ← map_sub]
    exact hlt _ (hσv x hx)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtSection
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SectionLattice

def IntegralAtSection {W K' : Type} [CommRing W] [Field K'] [Algebra W K'] {G : Scheme.{0}}
    (p : G ⟶ Sp W) {P M : LB G} {N : LB (pullback p (spMap (algebraMap W K')))}
    (w : LB.Iso (M.pull (pullback.fst p (spMap (algebraMap W K')))) N)
    (w₁ : LB.Iso (P.pull (pullback.fst p (spMap (algebraMap W K')))) N) : Prop :=
  ∃ (e₀ : Sp W ⟶ G) (_ : e₀ ≫ p = 𝟙 _) (x : Sp K' ⟶ pullback p (spMap (algebraMap W K')))
    (_ : x ≫ pullback.fst p (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀)
    (_ : x ≫ pullback.snd p (spMap (algebraMap W K')) = 𝟙 _)
    (i : P.ι) (m : M.ι) (n : N.ι) (_ : ⊤ ≤ e₀ ⁻¹ᵁ P.U i) (_ : ⊤ ≤ e₀ ⁻¹ᵁ M.U m)
    (h₁ : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (P.pull (pullback.fst p (spMap (algebraMap W K')))).U (fun _ => i)))
    (h₂ : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (M.pull (pullback.fst p (spMap (algebraMap W K')))).U (fun _ => m)))
    (a : W),
    (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h₁).hom (w₁.s (n, fun _ => i)).val) =
      algebraMap W K' a * (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom
        ((x.appLE _ ⊤ h₂).hom (w.s (n, fun _ => m)).val)

end GlobalTheory.SectionLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralReTopDegreeDensityDbarEqZero
section
set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm

theorem integrable_dbar_integral_eq_zero {n : ℕ} {G : V n → ℂ} (hG : ContDiff ℝ 1 G)
    (hc : HasCompactSupport G) (u : V n) :
    Integrable (fun v => dbar G v u) ∧ ∫ v, dbar G v u = 0 := by
  have hint : ∀ w : V n, Integrable (fun y => fderiv ℝ G y w) := fun w =>
    ((hG.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) w)
  refine ⟨?_, ?_⟩
  · simp only [dbar_apply, smul_eq_mul]
    exact ((hint _).add ((hint _).const_mul _)).const_mul _
  · simp only [dbar_apply, smul_eq_mul]
    rw [integral_const_mul, integral_add (hint _) ((hint _).const_mul _), integral_const_mul,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n G hG hc,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n G hG hc]
    simp

theorem dens_dbarAt_eq_sum {n : ℕ} (F : V n → Alt n) (v : V n) :
    dens (dbarAt F v) = ∑ a, ∑ S, dbar (fun x => (bas n).repr (F x) S) v (coordVec a) * dens (dzb a * bas n S) := by
  simp only [dens, dbarAt, coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.finset_sum_apply,
    Finsupp.smul_apply, smul_eq_mul, Finset.sum_div, mul_div_assoc]

theorem integral_re_dens_dbarAt_eq_zero {n : ℕ} (F : V n → Alt n)
    (hF : ∀ S, ContDiff ℝ 1 (fun v => (bas n).repr (F v) S)) (hc : HasCompactSupport F) :
    ∫ v, (dens (dbarAt F v)).re = 0 := by
  have h (a : Fin n) (S : Finset (Fin (n + n))) :=
    integrable_dbar_integral_eq_zero (hF S)
      (hc.comp_left (g := fun α : Alt n => (bas n).repr α S) (by simp)) (coordVec a)
  have hi (a : Fin n) (S : Finset (Fin (n + n))) :
      Integrable fun v => dbar (fun x => (bas n).repr (F x) S) v (coordVec a) * dens (dzb a * bas n S) :=
    (h a S).1.mul_const _
  have hD : Integrable fun v => dens (dbarAt F v) := by
    simp only [dens_dbarAt_eq_sum]
    exact integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun S _ => hi a S
  have h0 : ∫ v, dens (dbarAt F v) = 0 := by
    simp only [dens_dbarAt_eq_sum]
    rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun S _ => hi a S]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [integral_finset_sum _ fun S _ => hi a S]
    refine Finset.sum_eq_zero fun S _ => ?_
    rw [integral_mul_const, (h a S).2, zero_mul]
  have := Complex.reCLM.integral_comp_comm hD
  simp only [Complex.reCLM_apply] at this
  rw [this, h0, Complex.zero_re]

end GlobalTheory.CxForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSqLeSumLintegralEnormSqOfPointwise
section
open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory

theorem sq_le_sum_enorm_sq_lintegral_bound
    (E : Type) [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] (μ : MeasureTheory.Measure E)
    (ι : Type) [Fintype ι] (f : E → ℝ) (g : ι → E → ℂ) (C : ℝ) (hg : ∀ a, Continuous (g a))
    (hfg : ∀ x, f x ^ 2 ≤ C * ∑ a, ‖g a x‖ ^ 2) :
    ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) ≤ ENNReal.ofReal C * ∑ a, ∫⁻ x, ‖g a x‖ₑ ^ 2 ∂μ := by
  by_cases hi : MeasureTheory.Integrable (fun x => f x ^ 2) μ
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hi
      (MeasureTheory.ae_of_all _ (fun x => sq_nonneg (f x)))]
    have hm : ∀ a, Measurable (fun x => ‖g a x‖ₑ ^ 2) := fun a =>
      ((hg a).measurable.enorm).pow_const 2
    calc ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ
        ≤ ∫⁻ x, ENNReal.ofReal C * ∑ a, ‖g a x‖ₑ ^ 2 ∂μ := by
          refine MeasureTheory.lintegral_mono (fun x => ?_)
          calc ENNReal.ofReal (f x ^ 2) ≤ ENNReal.ofReal (C * ∑ a, ‖g a x‖ ^ 2) :=
                ENNReal.ofReal_le_ofReal (hfg x)
            _ = ENNReal.ofReal C * ENNReal.ofReal (∑ a, ‖g a x‖ ^ 2) :=
                ENNReal.ofReal_mul' (Finset.sum_nonneg (fun a _ => sq_nonneg _))
            _ = ENNReal.ofReal C * ∑ a, ‖g a x‖ₑ ^ 2 := by
                rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => sq_nonneg _)]
                congr 1
                refine Finset.sum_congr rfl (fun a _ => ?_)
                rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
      _ = ENNReal.ofReal C * ∑ a, ∫⁻ x, ‖g a x‖ₑ ^ 2 ∂μ := by
          rw [MeasureTheory.lintegral_const_mul _ (Finset.measurable_sum _ (fun a _ => hm a)),
            MeasureTheory.lintegral_finset_sum _ (fun a _ => hm a)]
  · rw [MeasureTheory.integral_undef hi, ENNReal.ofReal_zero]
    exact zero_le

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeBaseChangeFieldAndComm
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.AbVarRed

theorem isAbelianScheme_baseChange_field_and_comm : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → IsAbelianScheme ((Over.pullback (spMap (algebraMap K L))).obj A) ∧ IsCommMonObj ((Over.pullback (spMap (algebraMap K L))).obj A) := by
  intro K L _ _ _ A _ _ hA
  have hB := GlobalTheory.isAbelianScheme_pullback_obj (spMap (algebraMap K L)) A hA
  exact ⟨hB, hB.comm⟩

end GlobalTheory.Published.AbVarRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogPeriodChowlaSelbergStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanLogPeriod_chowlaSelberg : GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod := by
  first | exact @GlobalTheory.MeanPeriodClosed.meanPeriod | exact GlobalTheory.MeanPeriodClosed.meanPeriod | (intros; apply GlobalTheory.MeanPeriodClosed.meanPeriod <;> assumption)
end

