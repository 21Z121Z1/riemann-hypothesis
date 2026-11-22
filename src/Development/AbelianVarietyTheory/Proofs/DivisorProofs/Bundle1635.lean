import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransitiveOnValuationRings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1606
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CotangentBidualToTangentFunctionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LieEig
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixedPosValuationDvdUniformiser
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

open IsDedekindDomain

namespace GlobalTheory.InertiaUnram

theorem valuationSubring_valuation_lt_one_iff {L : Type} [Field L] {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) (x : L) : v.valuationSubring.valuation x < 1 ↔ v x < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or,
    Valuation.mem_valuationSubring_iff]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [map_inv₀, not_le]
    constructor
    · rintro (h | h)
      · exact absurd h hx
      · exact (one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx))).1 h
    · intro h
      exact Or.inr ((one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx))).2 h)

theorem mem_iff_valuation_le_one (L S : Type) [Field L] [CommRing S] [IsDomain S] [IsDedekindDomain S]
    [Algebra S L] [IsFractionRing S L] (W : ValuationSubring L) (hS : ∀ s : S, algebraMap S L s ∈ W)
    (P : HeightOneSpectrum S) (hP : P.asIdeal = GlobalTheory.ProlongConj.primeBelow S W hS) (x : L) :
    x ∈ W ↔ P.valuation L x ≤ 1 := by
  have hS' : ∀ s : S, algebraMap S L s ∈ (P.valuation L).valuationSubring := fun s =>
    (Valuation.mem_valuationSubring_iff _ _).2 (P.valuation_le_one s)
  have key : ∀ s : S, W.valuation (algebraMap S L s) < 1 ↔
      (P.valuation L).valuationSubring.valuation (algebraMap S L s) < 1 := by
    intro s
    rw [valuationSubring_valuation_lt_one_iff, ← GlobalTheory.ProlongConj.mem_primeBelow S hS, ← hP]
    exact (P.valuation_lt_one_iff_mem s).symm
  have hW : W = (P.valuation L).valuationSubring :=
    le_antisymm (GlobalTheory.ProlongConj.le_of_valuation_lt_one_iff S hS hS' key)
      (GlobalTheory.ProlongConj.le_of_valuation_lt_one_iff S hS' hS fun s => (key s).symm)
  rw [hW, Valuation.mem_valuationSubring_iff]

theorem mem_inertia_of_mem_inertia (K L S : Type) [Field K] [Field L] [Algebra K L] [CommRing S] [IsDomain S]
    [IsDedekindDomain S] [Algebra S L] [IsFractionRing S L] [MulSemiringAction (L ≃ₐ[K] L) S]
    (hact : ∀ (g : L ≃ₐ[K] L) (s : S), algebraMap S L (g • s) = g (algebraMap S L s))
    (P : HeightOneSpectrum S) (W : ValuationSubring L) (hW : ∀ x, x ∈ W ↔ P.valuation L x ≤ 1)
    (σ : L ≃ₐ[K] L) (hσ : σ ∈ P.asIdeal.inertia (L ≃ₐ[K] L)) : σ ∈ inertia K W := by
  set v := P.valuation L with hv
  have hWeq : W = v.valuationSubring := by
    ext x
    rw [hW, Valuation.mem_valuationSubring_iff]
  have hS : ∀ s : S, algebraMap S L s ∈ W := fun s => (hW _).2 (P.valuation_le_one s)
  have aux : ∀ τ ∈ P.asIdeal.inertia (L ≃ₐ[K] L), ∀ x, v x ≤ 1 → v (τ x) ≤ 1 ∧ v (τ x - x) < 1 := by
    intro τ hτ x hx
    have hτ' := AddSubgroup.mem_inertia.mp hτ
    obtain ⟨s, t, hs1, e⟩ := GlobalTheory.ProlongConj.exists_den S W hS ((hW x).2 hx)
    have hsP : s ∉ P.asIdeal := by
      intro hm
      have h1 : W.valuation (algebraMap S L s) < 1 := by
        rw [hWeq, valuationSubring_valuation_lt_one_iff]
        exact (P.valuation_lt_one_iff_mem s).2 hm
      rw [hs1] at h1
      exact lt_irrefl _ h1
    have va : v (algebraMap S L s) = 1 :=
      le_antisymm (P.valuation_le_one s) (not_lt.1 fun h => hsP ((P.valuation_lt_one_iff_mem s).1 h))
    have hdiff : ∀ u : S, v (τ (algebraMap S L u) - algebraMap S L u) < 1 := by
      intro u
      rw [← hact, ← map_sub]
      exact (P.valuation_lt_one_iff_mem _).2 (hτ' u)
    have va' : v (τ (algebraMap S L s)) = 1 := by
      have h := Valuation.map_add_eq_of_lt_right v (x := τ (algebraMap S L s) - algebraMap S L s)
        (y := algebraMap S L s) (by rw [va]; exact hdiff s)
      rw [sub_add_cancel, va] at h
      exact h
    have hs0 : algebraMap S L s ≠ 0 := fun h => by rw [h, map_zero] at va; exact zero_ne_one va
    have hs0' : τ (algebraMap S L s) ≠ 0 := fun h => by rw [h, map_zero] at va'; exact zero_ne_one va'
    have hx' : x = algebraMap S L t / algebraMap S L s := by rw [← e]; field_simp
    have hτx : τ x = τ (algebraMap S L t) / τ (algebraMap S L s) := by rw [hx', map_div₀]
    constructor
    · rw [hτx, map_div₀, va', div_one, ← hact]
      exact P.valuation_le_one _
    · have : τ x - x = ((τ (algebraMap S L t) - algebraMap S L t) * algebraMap S L s -
          algebraMap S L t * (τ (algebraMap S L s) - algebraMap S L s)) /
          (τ (algebraMap S L s) * algebraMap S L s) := by
        rw [hτx, hx']; field_simp; ring
      rw [this, map_div₀, map_mul v (τ _), va, va', _root_.mul_one, div_one]
      refine Valuation.map_sub_lt v ?_ ?_
      · rw [map_mul, va, _root_.mul_one]; exact hdiff t
      · rw [map_mul]
        calc v (algebraMap S L t) * v (τ (algebraMap S L s) - algebraMap S L s)
            ≤ 1 * v (τ (algebraMap S L s) - algebraMap S L s) :=
              mul_le_mul_left (P.valuation_le_one t) _
          _ < 1 := by rw [_root_.one_mul]; exact hdiff s
  rw [mem_inertia_iff]
  refine ⟨?_, fun x hx => ?_⟩
  · ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, hW, hW]
    constructor
    · intro h
      have h2 := (aux σ hσ _ h).1
      rwa [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at h2
    · intro h
      exact (aux σ⁻¹ (inv_mem hσ) x h).1
  · rw [hWeq, valuationSubring_valuation_lt_one_iff]
    exact (aux σ hσ x ((hW x).1 hx)).2

theorem valuation_le_of_fixed (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Algebra R L] [IsScalarTower R K L] [SMulCommClass (L ≃ₐ[K] L) R L]
    [IsDedekindDomain (integralClosure R L)] [IsFractionRing (integralClosure R L) L]
    (P : HeightOneSpectrum (integralClosure R L)) (π : R) (hπ : Irreducible π) (y : L)
    (hy : ∀ σ ∈ P.asIdeal.inertia (L ≃ₐ[K] L), σ y = y) (hlt : P.valuation L y < 1) :
    P.valuation L y ≤ P.valuation L (algebraMap K L (algebraMap R K π)) := by
  rw [GlobalTheory.T.valuation_uniformizer_integralClosure_eq_exp_neg_ramificationIdx R K L P π hπ, ← GlobalTheory.T.card_inertia_eq_ramificationIdx_of_perfect_residue R K L P]
  exact GlobalTheory.T.valuation_le_exp_neg_card_inertia_of_inertia_fixed R K L P y hy hlt

theorem div_uniformiser_mem : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (W : ValuationSubring L), IsAbove R K W.toSubring →
    ∀ π : R, Irreducible π → ∀ y : L, (∀ τ ∈ inertia K W, τ y = y) → y ∈ W.nonunits →
    y / algebraMap K L (algebraMap R K π) ∈ W := by
  intro R K L _ _ _ _ _ _ _ _ _ _ _ W hW π hπ y hy hyW
  letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hc : SMulCommClass (L ≃ₐ[K] L) R L := ⟨fun g r x => by
    rw [← IsScalarTower.algebraMap_smul K r x, ← IsScalarTower.algebraMap_smul K r (g • x)]
    exact map_smul g _ _⟩
  haveI : IsDedekindDomain (integralClosure R L) := integralClosure.isDedekindDomain R K L
  haveI : IsFractionRing (integralClosure R L) L := integralClosure.isFractionRing_of_finite_extension K L
  have hR : ∀ r : R, algebraMap R L r ∈ W := by
    intro r
    have : algebraMap R K r ∈ W.toSubring.comap (algebraMap K L) := by rw [hW]; exact ⟨r, rfl⟩
    exact this
  have hS : ∀ s : integralClosure R L, algebraMap (integralClosure R L) L s ∈ W :=
    fun s => GlobalTheory.ProlongConj.mem_of_isIntegral W hR s.2
  set c : L := algebraMap K L (algebraMap R K π) with hc_def
  have hc0 : c ≠ 0 := by
    rw [hc_def, map_ne_zero_iff _ (algebraMap K L).injective,
      map_ne_zero_iff _ (IsFractionRing.injective R K)]
    exact hπ.ne_zero
  have hcW : W.valuation c < 1 := by
    rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]
    right
    intro hinv
    have h1 : (algebraMap R K π)⁻¹ ∈ W.toSubring.comap (algebraMap K L) := by
      change algebraMap K L _ ∈ W
      rw [map_inv₀]; exact hinv
    rw [hW] at h1
    obtain ⟨s, hs⟩ := h1
    apply hπ.not_isUnit
    refine IsUnit.of_mul_eq_one s (IsFractionRing.injective R K ?_)
    rw [map_mul, hs, map_one, mul_inv_cancel₀]
    exact (map_ne_zero_iff _ (algebraMap K L).injective).1 (by rw [← hc_def]; exact hc0)
  set P0 := GlobalTheory.ProlongConj.primeBelow (integralClosure R L) W hS
  have hP0 : P0 ≠ ⊥ := by
    intro h
    have hm : algebraMap R (integralClosure R L) π ∈ P0 := by
      rw [GlobalTheory.ProlongConj.mem_primeBelow, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply R K L]
      exact hcW
    rw [h, Ideal.mem_bot] at hm
    apply hc0
    rw [hc_def, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R (integralClosure R L) L, hm,
      map_zero]
  let P : HeightOneSpectrum (integralClosure R L) := ⟨P0, inferInstance, hP0⟩
  have hWv := mem_iff_valuation_le_one L (integralClosure R L) W hS P rfl
  have hI : ∀ σ ∈ P.asIdeal.inertia (L ≃ₐ[K] L), σ ∈ inertia K W :=
    mem_inertia_of_mem_inertia K L (integralClosure R L) (fun _ _ => rfl) P W hWv
  have hlt : P.valuation L y < 1 := by
    rcases (ValuationSubring.mem_nonunits_iff_or W).1 hyW with h | h
    · rw [h, map_zero]; exact zero_lt_one
    · by_contra hge
      push_neg at hge
      apply h
      rw [hWv, map_inv₀]
      have h1 : P.valuation L y ≤ 1 := (hWv y).1 ((W.valuation_le_one_iff y).1 (le_of_lt (W.mem_nonunits_iff.1 hyW)))
      rw [le_antisymm h1 hge, inv_one]
  have key := valuation_le_of_fixed R K L P π hπ y (fun σ hσ => hy σ (hI σ hσ)) hlt
  rw [hWv, map_div₀]
  have hv0 : P.valuation L c ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
  rw [div_le_one₀ (zero_lt_iff.2 hv0)]
  exact key

end GlobalTheory.InertiaUnram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralTwistedComparisonAtFixedSection
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SectionLattice

theorem mem_pull_chart_iff {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (j : (L.pull f).ι) (y : Y) :
    y ∈ (L.pull f).U j ↔ f.base y ∈ L.U (j PUnit.unit) :=
  ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩

theorem exists_chart_of_isLocalRing {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}}
    (L : LB X) (hL : L.IsLB) (e : Spec (CommRingCat.of R) ⟶ X) : ∃ m : L.ι, ⊤ ≤ e ⁻¹ᵁ L.U m := by
  have h : e.base (IsLocalRing.closedPoint R) ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
  obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 h
  refine ⟨m, ?_⟩
  have := (IsLocalRing.closedPoint_mem_iff (R := R) (e ⁻¹ᵁ L.U m)).1 hm
  exact this.ge

theorem integralAtSection_of_conj : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) (σ : K' ≃+* K') (τ : W →+* W), (∀ l : K', l ≠ 0 → ∃ a : W, σ l = algebraMap W K' a * l) → ∀ (φ : G.left ⟶ G.left) (e₀ : Sp W ⟶ G.left), e₀ ≫ G.hom = 𝟙 _ → e₀ ≫ φ = spMap τ ≫ e₀ → ∀ (ρ : pullback G.hom (spMap (algebraMap W K')) ⟶ pullback G.hom (spMap (algebraMap W K'))) (x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K'))), x ≫ pullback.fst G.hom (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀ → x ≫ pullback.snd G.hom (spMap (algebraMap W K')) = 𝟙 _ → x ≫ ρ = spMap (σ : K' →+* K') ≫ x → ∀ (M : LB G.left) (N : LB (pullback G.hom (spMap (algebraMap W K')))), M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N) (w₁ : LB.Iso ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), (∀ (n : N.ι) (i : ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))).ι) (h : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))).U i)) (h' : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i PUnit.unit PUnit.unit))), (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h).hom (w₁.s (n, i)).val) = σ ((Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h').hom (w.s (n, fun _ => i PUnit.unit PUnit.unit)).val))) → GlobalTheory.SectionLattice.IntegralAtSection G.hom w w₁ := by
  intro W K' _ _ _ _ _ _ G σ τ hσ φ e₀ he₀ hφ ρ x hx₁ hx₂ _ M N hM hN w w₁ H
  obtain ⟨m, hm⟩ := exists_chart_of_isLocalRing M hM e₀
  obtain ⟨n, hn⟩ := exists_chart_of_isLocalRing N hN x
  have hi : ⊤ ≤ e₀ ⁻¹ᵁ (M.pull φ).U (fun _ => m) := by
    intro y _
    change e₀.base y ∈ (M.pull φ).U (fun _ => m)
    refine (mem_pull_chart_iff _ _ _ _).2 ?_
    have h1 : φ.base (e₀.base y) = e₀.base ((spMap τ).base y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hφ]
    rw [h1]
    exact hm (TopologicalSpace.Opens.mem_top _)
  have key : ∀ (P : LB G.left) (i : P.ι), ⊤ ≤ e₀ ⁻¹ᵁ P.U i →
      ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i)) := by
    intro P i hP y hy
    refine ⟨hn hy, ?_⟩
    change x.base y ∈ (P.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i)
    refine (mem_pull_chart_iff _ _ _ _).2 ?_
    have h1 : (pullback.fst G.hom (spMap (algebraMap W K'))).base (x.base y) =
        e₀.base ((spMap (algebraMap W K')).base y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hx₁]
    rw [h1]
    exact hP (TopologicalSpace.Opens.mem_top _)
  have h₁ := key (M.pull φ) (fun _ => m) hi
  have h₂ := key M m hm
  have hw := H n (fun _ _ => m) h₁ h₂
  have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom
      ((x.appLE _ ⊤ h₂).hom (w.s (n, fun _ => m)).val)) :=
    ((Units.isUnit _).map _).map _
  obtain ⟨a, ha⟩ := hσ _ hu.ne_zero
  exact ⟨e₀, he₀, x, hx₁, hx₂, fun _ => m, m, n, hi, hm, h₁, h₂, a, hw.trans ha⟩

end GlobalTheory.SectionLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteDualNumber
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HTLat GlobalTheory.EigenSplit
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat.OmegaRank

theorem mem_pow_iff {R : Type} [CommRing R] (a : R) (n : ℕ) (x : R) :
    x ∈ (Ideal.span {a} ^ n • ⊤ : Submodule R R) ↔ a ^ n ∣ x := by
  rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]

theorem dual_dvd_iff {O : Type} [CommRing O] (p n : ℕ) (x : DualNumber O) :
    (p : DualNumber O) ^ n ∣ x ↔ (p : O) ^ n ∣ x.fst ∧ (p : O) ^ n ∣ x.snd := by
  have e : (p : DualNumber O) ^ n = TrivSqZeroExt.inl ((p : O) ^ n) := by
    rw [← TrivSqZeroExt.inl_pow, TrivSqZeroExt.inl_natCast]
  rw [e]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y.fst, by simp⟩, ⟨y.snd, by simp⟩⟩
  · rintro ⟨⟨a, ha⟩, b, hb⟩
    exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, by ext <;> simp [ha, hb]⟩

theorem isAdicComplete_dualNumber {O : Type} [CommRing O] (p : ℕ)
    [h : IsAdicComplete (Ideal.span {(p : O)}) O] :
    IsAdicComplete (Ideal.span {(p : DualNumber O)}) (DualNumber O) where
  haus' x hx := by
    simp only [SModEq.zero, mem_pow_iff, dual_dvd_iff] at hx
    refine TrivSqZeroExt.ext (h.haus' x.fst fun n => ?_) (h.haus' x.snd fun n => ?_)
    · rw [SModEq.zero, mem_pow_iff]; exact (hx n).1
    · rw [SModEq.zero, mem_pow_iff]; exact (hx n).2
  prec' f hf := by
    simp only [SModEq.sub_mem, mem_pow_iff, dual_dvd_iff] at hf ⊢
    obtain ⟨a, ha⟩ := h.prec' (fun n => (f n).fst) fun {m n} hmn => by
      rw [SModEq.sub_mem, mem_pow_iff]; exact (hf hmn).1
    obtain ⟨b, hb⟩ := h.prec' (fun n => (f n).snd) fun {m n} hmn => by
      rw [SModEq.sub_mem, mem_pow_iff]; exact (hf hmn).2
    simp only [SModEq.sub_mem, mem_pow_iff] at ha hb
    exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, fun n => ⟨by simpa using ha n, by simpa using hb n⟩⟩

theorem finrank_omega_of_param {O : Type} [CommRing O] [Nontrivial O] {H : Over (Sp O)} [GrpObj H] {n : ℕ}
    (e : (Fin n → O) ≃ LieG H) (hadd : ∀ c d, (e (c + d)).1 = (e c).1 * (e d).1)
    (hsmul : ∀ (a : O) c, (e (a • c)).1 = ptMap (dualScale a) ≫ (e c).1) :
    Module.finrank O (omega H) = n := by
  let F : omega H ≃ₗ[O] Module.Dual O (Fin n → O) :=
    { toFun := fun f =>
        { toFun := fun c => f.1 (e c)
          map_add' := fun c d => (congrArg f.1 (Subtype.ext (hadd c d))).trans
            (omega_lieAdd f (e c) (e d))
          map_smul' := fun a c => (congrArg f.1 (Subtype.ext (hsmul a c))).trans
            (omega_lieScale f a (e c)) }
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun l => ⟨fun x => l (e.symm x), fun x y h => by
          obtain ⟨c, rfl⟩ := e.surjective x
          obtain ⟨d, rfl⟩ := e.surjective y
          rw [show (⟨_, h⟩ : LieG H) = e (c + d) from Subtype.ext (hadd c d).symm]
          simp, fun a x h => by
          obtain ⟨c, rfl⟩ := e.surjective x
          rw [show (⟨_, h⟩ : LieG H) = e (a • c) from Subtype.ext (hsmul a c).symm]
          simp⟩
      left_inv := fun f => Subtype.ext (funext fun x => congrArg f.1 (e.apply_symm_apply x))
      right_inv := fun l => LinearMap.ext fun c => congrArg l (e.symm_apply_apply c) }
  rw [F.finrank_eq, ← (Pi.basisFun O (Fin n)).toDualEquiv.finrank_eq, Module.finrank_fin_fun]

theorem exists_param {O : Type} [CommRing O] [IsLocalRing O] (H : Over (Sp O)) [GrpObj H] {n : ℕ}
    (hH : SmoothOfRelativeDimension n H.hom) :
    ∃ e : (Fin n → O) ≃ LieG H, (∀ c d, (e (c + d)).1 = (e c).1 * (e d).1) ∧
      ∀ (a : O) c, (e (a • c)).1 = ptMap (dualScale a) ≫ (e c).1 := by
  obtain ⟨x, hx⟩ := KeyPow.exists_isUnivChart H hH
  refine ⟨⟨fun c => ⟨Chart.tvec (x := x) c, Chart.isTan_tvec hx c⟩, fun w => Chart.tcoord hx w.1 w.2,
    fun c => Chart.tcoord_tvec hx c, fun w => Subtype.ext (Chart.tcoord_spec hx w.1 w.2).symm⟩,
    fun c d => Chart.tvec_add hx c d, fun a c => Chart.tvec_smul hx a c⟩

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem smoothDim_model : SmoothOfRelativeDimension P.A.g P.G.hom := by
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  have := P.semi.smooth
  have := P.semi.geomConnected
  have : ConnectedSpace P.G.left := GeometricallyConnected.connectedSpace P.G.hom P.G.hom.isOpenMap
  obtain ⟨n, hn⟩ := exists_dim_of_preconnected P.G.hom (Classical.arbitrary _)
  have h₁ : SmoothOfRelativeDimension n P.A.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback P.gen_pull.1 hn
  rwa [← H1.dim_unique _ h₁ P.A.smoothDim (η[P.A.A].left (IsLocalRing.closedPoint C))]

section Lim

variable {R : Type} [CommRing R] [Algebra O R]

variable (p O R) in

abbrev redR (m : ℕ) : R →ₐ[O] R ⧸ Ideal.span {(p : R) ^ m} := Ideal.Quotient.mkₐ O _

omit [Fact p.Prime] in
theorem nilpR (m : ℕ) : IsNilpotent (p : R ⧸ Ideal.span {(p : R) ^ m}) := ⟨m, by
  rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _⟩

omit [Fact p.Prime] in
theorem factor_redR (m : ℕ) : ptMap (Ideal.Quotient.factorₐ O (Ideal.span_singleton_le_span_singleton.mpr
    (pow_dvd_pow (p : R) (Nat.le_succ m)))) ≫ ptMap (redR p O R (m + 1)) = ptMap (redR p O R m) := by
  rw [TangentPow.ptMap_comp_ptMap]
  rfl

def Corr (x : specO O R ⟶ P.Gt) (y : specO O R ⟶ P.G) : Prop :=
  ∀ m, ptMap (redR p O R m) ≫ y = P.cmp _ (nilpR m) (ptMap (redR p O R m) ≫ x)

variable {P}

theorem Corr.mul {x x' : specO O R ⟶ P.Gt} {y y' : specO O R ⟶ P.G} (h : Corr P x y) (h' : Corr P x' y') :
    Corr P (x * x') (y * y') := fun m => by
  rw [MonObj.comp_mul, MonObj.comp_mul, map_mul, h, h']

theorem Corr.one : Corr P (1 : specO O R ⟶ P.Gt) 1 := fun m => by
  rw [MonObj.comp_one, MonObj.comp_one, map_one]

theorem Corr.comp {R' : Type} [CommRing R'] [Algebra O R'] (φ : R →ₐ[O] R') {x : specO O R ⟶ P.Gt}
    {y : specO O R ⟶ P.G} (h : Corr P x y) : Corr P (ptMap φ ≫ x) (ptMap φ ≫ y) := fun m => by
  let ψ : (R ⧸ Ideal.span {(p : R) ^ m}) →ₐ[O] R' ⧸ Ideal.span {(p : R') ^ m} :=
    Ideal.quotientMapₐ _ φ (by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow, map_natCast]
      exact Ideal.mem_span_singleton_self _)
  have e : ptMap (redR p O R' m) ≫ ptMap φ = ptMap ψ ≫ ptMap (redR p O R m) := by
    rw [TangentPow.ptMap_comp_ptMap, TangentPow.ptMap_comp_ptMap]
    rfl
  rw [← Category.assoc, ← Category.assoc, e, Category.assoc, Category.assoc, h,
    P.cmp_nat _ _ (nilpR m) (nilpR m)]

variable [IsLocalRing R] (hp : ¬ IsUnit (p : R)) (hc : IsAdicComplete (Ideal.span {(p : R)}) R)
include hp hc

theorem existsUnique_right (x : specO O R ⟶ P.Gt) : ∃! y, Corr P x y :=
  AdicPt.existsUnique_lim O R (p : R) hp hc P.G _
    fun m => by rw [← P.cmp_nat _ _ (nilpR (m + 1)) (nilpR m), ← Category.assoc, factor_redR]

theorem existsUnique_left (y : specO O R ⟶ P.G) : ∃! x, Corr P x y := by
  have h := AdicPt.existsUnique_lim O R (p : R) hp hc P.Gt
    (fun m => (P.cmp _ (nilpR m)).symm (ptMap (redR p O R m) ≫ y)) fun m =>
      (P.cmp _ (nilpR m)).injective (by
        rw [P.cmp_nat _ _ (nilpR (m + 1)) (nilpR m), MulEquiv.apply_symm_apply,
          MulEquiv.apply_symm_apply, ← Category.assoc, factor_redR])
  obtain ⟨x, hx, hu⟩ := h
  refine ⟨x, fun m => by rw [hx, MulEquiv.apply_symm_apply], fun x' hx' => hu x' fun m => ?_⟩
  rw [hx' m, MulEquiv.symm_apply_apply]

end Lim

theorem exists_lieEquiv [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] :
    ∃ e : LieG P.G ≃ LieG P.Gt, (∀ x y z : LieG P.G, z.1 = x.1 * y.1 → (e z).1 = (e x).1 * (e y).1) ∧
      ∀ (a : O) (x z : LieG P.G), z.1 = ptMap (dualScale a) ≫ x.1 →
        (e z).1 = ptMap (dualScale a) ≫ (e x).1 := by
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp₀ : ¬ IsUnit (p : O) := Fact.out
  have hp : ¬ IsUnit (p : DualNumber O) := fun h => hp₀ (by
    simpa using h.map (TrivSqZeroExt.fstHom O O O))
  have hc := isAdicComplete_dualNumber (O := O) p
  have hl := existsUnique_left (P := P) hp hc
  have hr := existsUnique_right (P := P) hp hc
  let f : LieG P.G → LieG P.Gt := fun y => ⟨(hl y.1).choose,
    (existsUnique_left (P := P) hp₀ inferInstance 1).unique
      (by
        have h := (hl y.1).choose_spec.1.comp (TrivSqZeroExt.fstHom O O O)
        rw [y.2] at h
        exact h) Corr.one⟩
  let g : LieG P.Gt → LieG P.G := fun x => ⟨(hr x.1).choose,
    (existsUnique_right (P := P) hp₀ inferInstance 1).unique
      (by
        have h := (hr x.1).choose_spec.1.comp (TrivSqZeroExt.fstHom O O O)
        rw [x.2] at h
        exact h) Corr.one⟩
  have hf : ∀ y, Corr P (f y).1 y.1 := fun y => (hl y.1).choose_spec.1
  have hg : ∀ x, Corr P x.1 (g x).1 := fun x => (hr x.1).choose_spec.1
  refine ⟨⟨f, g, fun y => Subtype.ext ((hr _).unique (hg _) (hf y)),
    fun x => Subtype.ext ((hl _).unique (hf _) (hg x))⟩, fun x y z h => ?_, fun a x z h => ?_⟩
  · exact (hl _).unique (hf z) (h ▸ (hf x).mul (hf y))
  · exact (hl _).unique (hf z) (h ▸ (hf x).comp (dualScale a))

theorem finrank_omega_Gt : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), Module.finrank O (omega P.Gt) = P.A.g := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P
  haveI := P.isLocalRing
  obtain ⟨e, h₁, h₂⟩ := exists_param P.G (smoothDim_model P)
  obtain ⟨e', h₃, h₄⟩ := exists_lieEquiv P
  exact finrank_omega_of_param (e.trans e') (fun c d => h₃ _ _ _ (h₁ c d)) fun a c => h₄ a _ _ (h₂ a c)

end GlobalTheory.HTLat.OmegaRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDiscreteValuationRingOfIsAboveStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDiscreteValuationRing_of_isAbove_alt : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] (V : ValuationSubring L), IsAbove R K V.toSubring → IsDiscreteValuationRing V := by
  first | exact @GlobalTheory.AbVarRed.isDiscreteValuationRing_of_isAbove | exact GlobalTheory.AbVarRed.isDiscreteValuationRing_of_isAbove | (intros; apply GlobalTheory.AbVarRed.isDiscreteValuationRing_of_isAbove <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormMul
section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

set_option autoImplicit false

open scoped ContDiff

namespace GlobalTheory.CxForm.FormMul

theorem isForm_mul : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α β : A.Fld),
    A.IsForm α → A.IsForm β → A.IsForm (α * β) := by
  intro M _ n A α β hα hβ
  refine ⟨fun i S => ?_, fun x x' h => ?_⟩
  · have e : (fun v => (bas n).repr (A.loc (α * β) i v) S) = fun v => ∑ p : Finset (Fin (n + n)) × Finset (Fin (n + n)),
        (bas n).repr (A.loc α i v) p.1 * (bas n).repr (A.loc β i v) p.2 * (bas n).repr (bas n p.1 * bas n p.2) S :=
      funext fun v => by rw [loc_mul, repr_mul]
    rw [e]
    exact ContDiffOn.sum fun p _ => ((hα.smooth i p.1).mul (hβ.smooth i p.2)).mul contDiffOn_const
  · show α x * β x = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd) (α x' * β x')
    rw [map_mul, ← hα.compat x x' h, ← hβ.compat x x' h]

end GlobalTheory.CxForm.FormMul
end

