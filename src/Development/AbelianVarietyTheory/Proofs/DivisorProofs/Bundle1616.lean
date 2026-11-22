import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1574
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1563
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1584
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfUniversalFirstOrderTa
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SmoothDimTangent

theorem smoothOfRelativeDimension_of_universal_tangent : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B) (d : ℕ), Smooth s → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), ∃ u : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ X, spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ u = x ∧ u ≫ s = spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ x ≫ s ∧ ∀ v : Sp (DualNumber k) ⟶ X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ s → ∃! c : (Fin d → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u) → SmoothOfRelativeDimension d s := by
  intro B _ X s d hs H
  have loc : ∀ p : X, ∃ W : X.Opens, p ∈ W ∧ SmoothOfRelativeDimension d (W.ι ≫ s) := by
    intro p
    obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth s p
    let _ := (s.appLE U V e).hom.toAlgebra
    have : Algebra.IsStandardSmooth Γ(Sp B, U) Γ(X, V) := h
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := this
    have hP : Algebra.IsStandardSmoothOfRelativeDimension P.dimension Γ(Sp B, U) Γ(X, V) := ⟨_, _, _, ‹_›, P, rfl⟩
    let k := AlgebraicClosure (X.residueField p)
    let x : Sp k ⟶ X := spMap (algebraMap (X.residueField p) k) ≫ X.fromSpecResidueField p
    have hr : Set.range x.base ⊆ (V : Set X) := by
      rintro _ ⟨y, rfl⟩
      have : x.base y ∈ Set.range (X.fromSpecResidueField p).base := ⟨_, (Scheme.Hom.comp_apply _ _ y).symm⟩
      rw [Scheme.range_fromSpecResidueField] at this
      rw [Set.mem_singleton_iff.1 this]
      exact hx
    obtain ⟨φ, ψ, h1, h2, h3⟩ := GlobalTheory.T.firstOrderPoint_iff_ringHom_affineOpen_sections B X s U V hU hV e d k x hr (H k x)
    have : Nontrivial Γ(X, V) := φ.domain_nontrivial
    have : Algebra.IsStandardSmooth Γ(Sp B, U) Γ(X, V) := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth P.dimension
    have : Module.Free Γ(X, V) Ω[Γ(X, V)⁄Γ(Sp B, U)] := Algebra.IsStandardSmooth.free_kaehlerDifferential
    have hrank : Module.finrank Γ(X, V) (Ω[Γ(X, V)⁄Γ(Sp B, U)]) = P.dimension :=
      Module.finrank_eq_of_rank_eq hP.rank_kaehlerDifferential
    have hd : d = P.dimension := GlobalTheory.T.eq_of_universal_tangent_dualNumber _ _ k P.dimension d hrank φ ψ h1 h2 h3
    have h' : RingHom.IsStandardSmoothOfRelativeDimension P.dimension (s.appLE U V e).hom := hP
    have : IsAffine U := hU
    have : IsAffine V := hV
    have : SmoothOfRelativeDimension P.dimension (s.resLE U V e) :=
      (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension P.dimension)).2
        (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
          ((RingHom.isStandardSmoothOfRelativeDimension_respectsIso.arrow_mk_iso_iff (arrowResLEAppIso s U V e)).2 h'))
    have : SmoothOfRelativeDimension (P.dimension + 0) (V.ι ≫ s) := by
      rw [← Scheme.Hom.resLE_comp_ι s e]; infer_instance
    refine ⟨V, hx, ?_⟩
    rw [hd]; exact this
  choose W hW hd using loc
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) := HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) hd

end GlobalTheory.SmoothDimTangent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecFractionFieldIsPullbackOfUnramified
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem spec_fraction_field_isPullback_of_unramified : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → IsPullback (spMap (algebraMap W K')) (spMap (algebraMap K K')) (spMap (algebraMap R W)) (spMap (algebraMap R K)) := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmax

  have hRK' : Function.Injective (algebraMap R K') := by
    rw [IsScalarTower.algebraMap_eq R K K']
    exact (algebraMap K K').injective.comp (IsFractionRing.injective R K)
  have hRW : Function.Injective (algebraMap R W) := by
    rw [IsScalarTower.algebraMap_eq R W K'] at hRK'
    exact Function.Injective.of_comp hRK'

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖW : Irreducible (algebraMap R W ϖ) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hmax,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid W (nonZeroDivisors R)) K' := by
    rw [IsLocalization.iff_of_le_of_exists_dvd (M := Algebra.algebraMapSubmonoid W (nonZeroDivisors R))
      (S := K') (nonZeroDivisors W)]
    · infer_instance
    · rintro _ ⟨r, hr, rfl⟩
      refine mem_nonZeroDivisors_of_ne_zero ?_
      intro h0
      exact nonZeroDivisors.ne_zero hr (hRW (by rw [h0, map_zero]))
    · intro w hw
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
        (nonZeroDivisors.ne_zero hw) hϖW
      refine ⟨algebraMap R W (ϖ ^ n), ⟨ϖ ^ n, mem_nonZeroDivisors_of_ne_zero
        (pow_ne_zero _ hϖ.ne_zero), rfl⟩, ?_⟩
      refine ⟨(↑u⁻¹ : W), ?_⟩
      rw [hu, map_pow, _root_.mul_comm (u : W), _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
  have hpo : Algebra.IsPushout R W K K' :=
    (Algebra.isLocalization_iff_isPushout (nonZeroDivisors R) K).mp hloc
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_iff_isPushout.mpr hpo)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableLatticeDescentUnramified
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.StableLatticeDescent

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']

def consZero (n : ℕ) : (Fin n → R') →ₗ[R'] (Fin (n + 1) → R') where
  toFun w := Fin.cons 0 w
  map_add' w w' := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp
  map_smul' c w := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp

omit [Algebra R R'] in
@[simp] lemma consZero_zero (n : ℕ) (w : Fin n → R') : consZero n w 0 = 0 := rfl

omit [Algebra R R'] in
@[simp] lemma consZero_succ (n : ℕ) (w : Fin n → R') (j : Fin n) : consZero n w j.succ = w j := rfl

theorem scalar_descent [IsDomain R'] (D : Set (R' ≃ₐ[R] R')) (ϖ : R)
    (hπ : algebraMap R R' ϖ ≠ 0)
    (hres : ∀ x : R', (∀ σ ∈ D, algebraMap R R' ϖ ∣ σ x - x) →
      ∃ c : R, algebraMap R R' ϖ ∣ x - algebraMap R R' c) :
    ∀ (a : ℕ) (x : R'), (∀ σ ∈ D, (algebraMap R R' ϖ) ^ a ∣ σ x - x) →
      ∃ c : R, (algebraMap R R' ϖ) ^ a ∣ x - algebraMap R R' c := by
  intro a
  induction a with
  | zero => intro x _; exact ⟨0, by simp⟩
  | succ a ih =>
    intro x hx
    obtain ⟨c0, hc0⟩ := hres x fun σ hσ => (dvd_pow_self _ (Nat.succ_ne_zero a)).trans (hx σ hσ)
    obtain ⟨t, ht⟩ := hc0
    have hx' : x = algebraMap R R' c0 + algebraMap R R' ϖ * t := by rw [← ht]; ring
    have ht' : ∀ σ ∈ D, (algebraMap R R' ϖ) ^ a ∣ σ t - t := by
      intro σ hσ
      have h := hx σ hσ
      have e : σ x - x = algebraMap R R' ϖ * (σ t - t) := by
        rw [hx']; simp only [map_add, map_mul, AlgEquiv.commutes]; ring
      rw [e, pow_succ'] at h
      exact (mul_dvd_mul_iff_left hπ).mp h
    obtain ⟨c1, hc1⟩ := ih t ht'
    refine ⟨c0 + ϖ * c1, ?_⟩
    have e : x - algebraMap R R' (c0 + ϖ * c1) = algebraMap R R' ϖ * (t - algebraMap R R' c1) := by
      rw [hx']; simp only [map_add, map_mul]; ring
    rw [e, pow_succ']
    exact mul_dvd_mul_left _ hc1

end GlobalTheory.StableLatticeDescent

namespace GlobalTheory.StableLatticeDescent

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']

theorem main_induction [IsDomain R'] [IsDiscreteValuationRing R'] (D : Set (R' ≃ₐ[R] R')) (ϖ : R)
    (hirr : Irreducible (algebraMap R R' ϖ))
    (hres : ∀ x : R', (∀ σ ∈ D, algebraMap R R' ϖ ∣ σ x - x) →
      ∃ c : R, algebraMap R R' ϖ ∣ x - algebraMap R R' c) (r : ℕ) :
    ∀ (n : ℕ) (N : Submodule R' (Fin n → R')), (∀ w : Fin n → R', (algebraMap R R' ϖ) ^ r • w ∈ N) →
      (∀ σ ∈ D, ∀ v ∈ N, (fun i => σ (v i)) ∈ N) →
      (∀ v ∈ N, v ∈ Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')}) ∧
      (∀ u : Fin n → R', (∀ σ ∈ D, (fun i => σ (u i)) - u ∈ N) →
        ∃ a : Fin n → R', (∀ i, a i ∈ Set.range (algebraMap R R')) ∧ u - a ∈ N) := by
  have hπ : algebraMap R R' ϖ ≠ 0 := hirr.ne_zero
  have hfix : ∀ (σ : R' ≃ₐ[R] R') (y : R'), y ∈ Set.range (algebraMap R R') → σ y = y := by
    rintro σ y ⟨c, rfl⟩; exact AlgEquiv.commutes σ c
  intro n
  induction n with
  | zero =>
    intro N _ _
    refine ⟨fun v _ => ?_, fun u _ => ⟨0, fun i => i.elim0, ?_⟩⟩
    · have : v = 0 := Subsingleton.elim _ _
      rw [this]; exact Submodule.zero_mem _
    · have : u - 0 = 0 := Subsingleton.elim _ _
      rw [this]; exact Submodule.zero_mem _
  | succ n ih =>
    intro N hlat hstab
    set π := algebraMap R R' ϖ with hπdef
    let L := consZero (R' := R') n
    have hLact : ∀ (σ : R' ≃ₐ[R] R') (w : Fin n → R'),
        (fun i => σ (L w i)) = L (fun i => σ (w i)) := by
      intro σ w; funext i
      refine Fin.cases ?_ ?_ i <;> simp [L]
    let K := N.comap L
    have hKlat : ∀ w : Fin n → R', π ^ r • w ∈ K := fun w => by
      show L (π ^ r • w) ∈ N
      rw [L.map_smul]; exact hlat _
    have hKstab : ∀ σ ∈ D, ∀ w ∈ K, (fun i => σ (w i)) ∈ K := by
      intro σ hσ w hw
      show L _ ∈ N
      rw [← hLact]; exact hstab σ hσ _ hw
    obtain ⟨hPK, hQK⟩ := ih K hKlat hKstab
    let I : Ideal R' := N.map (LinearMap.proj (R := R') (φ := fun _ : Fin (n + 1) => R') 0)
    have hrI : π ^ r ∈ I := ⟨π ^ r • (fun _ => 1 : Fin (n + 1) → R'), hlat _, by simp⟩
    have hI0 : I ≠ ⊥ := by
      intro h
      rw [h, Submodule.mem_bot] at hrI
      exact pow_ne_zero r hπ hrI
    obtain ⟨a, ha⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI0 hirr
    have hmemI : ∀ v ∈ N, π ^ a ∣ v 0 := by
      intro v hv
      have : v 0 ∈ I := ⟨v, hv, rfl⟩
      rw [ha, Ideal.mem_span_singleton] at this
      exact this
    obtain ⟨vs, hvsN, hvs0⟩ : ∃ v ∈ N, v 0 = π ^ a := by
      have : π ^ a ∈ I := by rw [ha]; exact Ideal.subset_span rfl
      obtain ⟨v, hv, hv0⟩ := this
      exact ⟨v, hv, hv0⟩
    have hpa : π ^ a ∈ Set.range (algebraMap R R') := ⟨ϖ ^ a, by simp [hπdef]⟩

    have hvsK : ∀ σ ∈ D, (fun i => σ (Fin.tail vs i)) - Fin.tail vs ∈ K := by
      intro σ hσ
      have e : L ((fun i => σ (Fin.tail vs i)) - Fin.tail vs) = (fun i => σ (vs i)) - vs := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [L, hvs0, hfix σ _ hpa]
        · intro j; simp [L, Fin.tail]
      show L _ ∈ N
      rw [e]; exact N.sub_mem (hstab σ hσ _ hvsN) hvsN
    obtain ⟨a0, ha0, ha0K⟩ := hQK (Fin.tail vs) hvsK
    obtain ⟨vo, hvo⟩ : ∃ vo, vo = vs - L (Fin.tail vs - a0) := ⟨_, rfl⟩
    have hvoN : vo ∈ N := hvo ▸ N.sub_mem hvsN ha0K
    have hvo0 : vo 0 = π ^ a := by rw [hvo]; simp [L, hvs0]
    have hvorat : ∀ i, vo i ∈ Set.range (algebraMap R R') := by
      intro i
      refine Fin.cases ?_ ?_ i
      · rw [hvo0]; exact hpa
      · intro j
        have : vo j.succ = a0 j := by rw [hvo]; simp [L, Fin.tail]
        rw [this]; exact ha0 j
    have hrat_add : ∀ x y : R', x ∈ Set.range (algebraMap R R') → y ∈ Set.range (algebraMap R R') →
        x + y ∈ Set.range (algebraMap R R') := by
      rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩; exact ⟨c + d, map_add _ _ _⟩
    have hrat0 : (0 : R') ∈ Set.range (algebraMap R R') := ⟨0, map_zero _⟩
    have hLrat : ∀ w : Fin n → R', (∀ i, w i ∈ Set.range (algebraMap R R')) →
        ∀ i, L w i ∈ Set.range (algebraMap R R') := by
      intro w hw i
      refine Fin.cases ?_ ?_ i
      · simpa [L] using hrat0
      · intro j; simpa [L] using hw j
    refine ⟨?_, ?_⟩
    ·
      intro v hv
      obtain ⟨t, ht⟩ := hmemI v hv
      obtain ⟨w, hw⟩ : ∃ w, w = Fin.tail (v - t • vo) := ⟨_, rfl⟩
      have hLw : L w = v - t • vo := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [L, ht, hvo0]; ring
        · intro j; simp [L, hw, Fin.tail]
      have hwK : w ∈ K := by
        show L w ∈ N
        rw [hLw]; exact N.sub_mem hv (N.smul_mem t hvoN)
      have hspan : Submodule.span R' {v | v ∈ K ∧ ∀ i, v i ∈ Set.range (algebraMap R R')} ≤
          (Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')}).comap L := by
        rw [Submodule.span_le]
        rintro w' ⟨hw'K, hw'r⟩
        exact Submodule.subset_span ⟨hw'K, hLrat w' hw'r⟩
      have h1 : L w ∈ Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')} :=
        hspan (hPK w hwK)
      have h2 : t • vo ∈ Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')} :=
        Submodule.smul_mem _ t (Submodule.subset_span ⟨hvoN, hvorat⟩)
      have : v = L w + t • vo := by rw [hLw]; abel
      rw [this]; exact Submodule.add_mem _ h1 h2
    ·
      intro u hu
      have h0 : ∀ σ ∈ D, π ^ a ∣ σ (u 0) - u 0 := by
        intro σ hσ; simpa using hmemI _ (hu σ hσ)
      obtain ⟨c, hc⟩ := scalar_descent D ϖ hπ hres a (u 0) h0
      obtain ⟨t, ht⟩ := hc
      obtain ⟨e, he⟩ : ∃ e : Fin (n + 1) → R', e = Fin.cons (algebraMap R R' c) 0 := ⟨_, rfl⟩
      have herat : ∀ i, e i ∈ Set.range (algebraMap R R') := by
        intro i
        refine Fin.cases ?_ ?_ i
        · rw [he]; exact ⟨c, rfl⟩
        · intro j; rw [he]; simpa using hrat0
      obtain ⟨u', hu'⟩ : ∃ u', u' = u - e - t • vo := ⟨_, rfl⟩
      obtain ⟨w, hw⟩ : ∃ w, w = Fin.tail u' := ⟨_, rfl⟩
      have hLw : L w = u' := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [L, hu', he, hvo0]; rw [ht, hπdef]; ring
        · intro j; simp [L, hw, Fin.tail]
      have hwinv : ∀ σ ∈ D, (fun i => σ (w i)) - w ∈ K := by
        intro σ hσ
        have key : L ((fun i => σ (w i)) - w) = ((fun i => σ (u i)) - u) - (σ t - t) • vo := by
          rw [L.map_sub, ← hLact, hLw, hu']
          funext i
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul,
            hfix σ _ (herat i), hfix σ _ (hvorat i)]
          ring
        show L _ ∈ N
        rw [key]; exact N.sub_mem (hu σ hσ) (N.smul_mem _ hvoN)
      obtain ⟨a', ha', ha'K⟩ := hQK w hwinv
      refine ⟨e + L a', fun i => hrat_add _ _ (herat i) (hLrat a' ha' i), ?_⟩
      have : u - (e + L a') = t • vo + L (w - a') := by
        rw [L.map_sub, hLw, hu']; abel
      rw [this]; exact N.add_mem (N.smul_mem t hvoN) ha'K

end GlobalTheory.StableLatticeDescent

namespace GlobalTheory

theorem stable_lattice_descent_unramified (R R' : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] (hm : (maximalIdeal R).map (algebraMap R R') = maximalIdeal R')
    (D : Set (R' ≃ₐ[R] R'))
    (hres : ∀ x : R', (∀ σ ∈ D, σ x - x ∈ maximalIdeal R') →
      ∃ r : R, x - algebraMap R R' r ∈ maximalIdeal R')
    (n r : ℕ) (N : Submodule R' (Fin n → R'))
    (hlat : (maximalIdeal R') ^ r • (⊤ : Submodule R' (Fin n → R')) ≤ N)
    (hstab : ∀ σ ∈ D, ∀ v ∈ N, (fun i => σ (v i)) ∈ N) :
    N = Submodule.span R' {v | v ∈ N ∧ ∀ i, v i ∈ Set.range (algebraMap R R')} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hmax : maximalIdeal R' = Ideal.span {algebraMap R R' ϖ} := by
    rw [← hm, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]
  have hirr : Irreducible (algebraMap R R' ϖ) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax
  have hres' : ∀ x : R', (∀ σ ∈ D, algebraMap R R' ϖ ∣ σ x - x) →
      ∃ c : R, algebraMap R R' ϖ ∣ x - algebraMap R R' c := by
    intro x hx
    obtain ⟨c, hc⟩ := hres x fun σ hσ => by
      rw [hmax, Ideal.mem_span_singleton]; exact hx σ hσ
    rw [hmax, Ideal.mem_span_singleton] at hc
    exact ⟨c, hc⟩
  have hmem : algebraMap R R' ϖ ∈ maximalIdeal R' := by
    rw [hmax]; exact Ideal.mem_span_singleton_self _
  have hlat' : ∀ w : Fin n → R', (algebraMap R R' ϖ) ^ r • w ∈ N := fun w =>
    hlat (Submodule.smul_mem_smul (Ideal.pow_mem_pow hmem r) Submodule.mem_top)
  obtain ⟨hP, -⟩ :=
    StableLatticeDescent.main_induction D ϖ hirr hres' r n N hlat' hstab
  exact le_antisymm (fun v hv => hP v hv) (Submodule.span_le.mpr fun v hv => hv.1)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharArchimedeanExpRealLinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdCharLin

theorem continuous_ofMixed (F : Type) [Field F] [NumberField F] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

theorem stdChar_mixed_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsStdChar D ψ (-1) → IsInfFam θ →
    ∃ β : mixedEmbedding.mixedSpace D.host.F →ₗ[ℝ] ℝ,
      (∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm a, 0) : AdeleRing (𝓞 D.host.F) D.host.F) =
        Complex.exp (2 * Real.pi * Complex.I * β a)) ∧
      ∀ a, β a = -(∑ ρ, θ ρ (((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm a) ⊗ₜ[D.host.F]
        (1 : D.host.E))).re := by
  intro D ψ θ hψ hθ
  obtain ⟨hc, hall⟩ := hψ
  have key := hall.2 θ hθ
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F with he
  let z : Ainf D.host.F → ℂ := fun x => ∑ ρ, θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E))
  have hkey : ∀ x, ψ ((x, 0) : AdeleRing (𝓞 D.host.F) D.host.F) =
      Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * z x) := fun x => key x
  have him : ∀ x, (z x).im = 0 := by
    intro x
    have h1 := hc.2.1 ((x, 0) : AdeleRing (𝓞 D.host.F) D.host.F)
    rw [hkey x, Complex.norm_exp] at h1
    have hre : (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * z x).re = 2 * Real.pi * (z x).im := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_eq_one_iff] at h1
    have hp : (0 : ℝ) < 2 * Real.pi := by positivity
    rcases mul_eq_zero.1 h1 with h | h
    · linarith
    · exact h
  have hzadd : ∀ x y, z (x + y) = z x + z y := by
    intro x y
    simp only [z, TensorProduct.add_tmul, map_add, Finset.sum_add_distrib]
  let g : mixedEmbedding.mixedSpace D.host.F →+ ℝ :=
    { toFun := fun a => -(z (e.symm a)).re
      map_zero' := by simp [z]
      map_add' := by intro a b; simp only [map_add, hzadd, Complex.add_re, neg_add] }
  have hg : Continuous g := by
    have : Continuous fun x : Ainf D.host.F => z x :=
      continuous_finset_sum _ fun ρ _ => (hθ ρ).2
    exact (Complex.continuous_re.comp (this.comp (continuous_ofMixed D.host.F))).neg
  refine ⟨(g.toRealLinearMap hg : mixedEmbedding.mixedSpace D.host.F →ₗ[ℝ] ℝ), ?_, fun a => rfl⟩
  intro a
  have hz : z (e.symm a) = ((z (e.symm a)).re : ℂ) := Complex.ext rfl (by simp [him])
  rw [hkey (e.symm a)]
  congr 1
  change _ = 2 * Real.pi * Complex.I * ((-(z (e.symm a)).re : ℝ) : ℂ)
  rw [hz]
  push_cast
  simp only [Complex.ofReal_re]
  ring

end GlobalTheory.StdCharLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionDeterminantRoot
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem weil_twist_base : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m) (t : T0) (k : GA D (Wc D i)) (x : (AE D)ˣ), IsDetRoot (Wc D i) k x → ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → R.ωP i t (1, k) f = ((R.xi t x : Circle) : ℂ) • R.ωP i A.μ0 (1, k) f := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i t k x hx f hf
  have h := GlobalTheory.TwistFactorProof.frame_ratio R (GlobalTheory.T.weilDatum_unique_on_thetaFunctions D) (GlobalTheory.T.exists_weilDatum_twist_heckeCharacters D) hR.thP.ωP i A.μ0 t hx hf
  rw [GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hR.lev.xi_base ▸ hR.lev.xi A.μ0) x, Circle.coe_one, one_smul] at h
  exact h

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagSiegel

open MeasureTheory Formalism.IndefR.Datum

def diagInt {F : Type} [Field F] [NumberField F] {κ : Type} (μ : @Measure (κ → AF F) (borel _))
    (Φ : (κ ⊕ κ → AF F) → ℂ) : ℂ :=
  @integral (κ → AF F) ℂ _ _ (borel _) μ (fun u => Φ (Sum.elim u u))

def diagMat {m n : ℕ} {X : Type} (w : Matrix (Fin m) (Fin n) X) : Matrix (Fin m) (Fin (n + n)) X :=
  (Matrix.fromCols w w).submatrix id finSumFinEquiv.symm

def thetaDiagInt {D : D7} {m n : ℕ} (ν : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (f : Mx D m (n + n) → ℂ) : ℂ :=
  ∫ w in 𝓕, f (diagMat w) ∂ν

def ruleFac {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (_c : E →ₐ[R] E) (C : GlobalTheory.WeilM.TestClass R)
    (χ : Eˣ →* Circle) (a : ℕ) {ν : Type} [Fintype ν] [DecidableEq ν] (t : GL ν E) : ℂ :=
  (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
    (((C.modu (Units.map (Algebra.norm R : E →* R) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ)

end GlobalTheory.DiagSiegel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedClassCountTorusDecompositionStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.twisted_class_count_torus_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, ∀ y : ∀ w : Pl E, GLw n w, (∀ w, (nrmL n w (y w)).val.charpoly = atPl w P) → (∀ᶠ w in cofinite, y w ∈ GlobalTheory.LFun.KGL w n) → ∃ (ι : Type) (_ : Fintype ι) (K L : ι → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, NumberField (K i)) (_ : ∀ i, Field (L i)) (_ : ∀ i, NumberField (L i)) (_ : ∀ i, Algebra (K i) (L i)) (_ : ∀ i, Algebra.IsQuadraticExtension (K i) (L i)) (x : ∀ i, GlobalTheory.QuadSymbol.FinFam (K i)), Fintype.card ι = nfac P ∧ (∀ i, NumberField.IsTotallyReal (K i)) ∧ (∀ i, NumberField.IsTotallyComplex (L i)) ∧ (∀ i, GlobalTheory.QuadSymbol.AlmostNorm (K i) (L i) (x i)) ∧ ∑ i, Fintype.card (InfinitePlace (K i)) = n * Fintype.card (InfinitePlace E) ∧ Nonempty ({c : TwCl (thE E n) // (c.rep * thE E n c.rep).val.charpoly = P ∧ ∀ w ∈ S, ∃ g, locEl n w c.rep = g⁻¹ * y w * thL n w g} ≃ ∀ i, {q : (K i)ˣ ⧸ GlobalTheory.QuadSymbol.globalNorms (K i) (L i) // ∃ t : (K i)ˣ, q = QuotientGroup.mk t ∧ ∀ u, x i u / GlobalTheory.QuadSymbol.finDiag (K i) t u ∈ GlobalTheory.QuadSymbol.normGroup (K i) (L i) (u.adicCompletion (K i))}) := by
  first | exact @GlobalTheory.BCT.FacCl.main | exact GlobalTheory.BCT.FacCl.main | (intros; apply GlobalTheory.BCT.FacCl.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingSectionsFiniteTypeStatement
section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_sections_finite_type : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Unf Xo c σ r), IsUnf U → ∀ Z : Comp Xo c, ∃ (R : Subalgebra c.F (Om Z)) (_ : Algebra.FiniteType c.F R) (t : Formalism.L2.Pj.Ix Dw → (Om Z)ˣ), (∀ (e : Formalism.L2.Pj.Ix Dw → ℤ), ∀ f ∈ secZ Xo c e, ((∏ i, t i ^ e i : (Om Z)ˣ) : Om Z) * genVal Z f ∈ R) ∧ ∀ φ : R →+* ℂ, φ.comp (algebraMap c.F R) = σ → ∃ z ∈ framesOn U Z, ∃ s : Formalism.L2.Pj.Ix Dw → ℂˣ, ∀ (e : Formalism.L2.Pj.Ix Dw → ℤ), ∀ f ∈ secZ Xo c e, ∀ b : R, (b : Om Z) = ((∏ i, t i ^ e i : (Om Z)ˣ) : Om Z) * genVal Z f → φ b = ((∏ i, s i ^ e i : ℂˣ) : ℂ) * rdU U f z.1 z.2 := by
  first | exact @GlobalTheory.DegCmp.exists_chart_read_at_frames | exact GlobalTheory.DegCmp.exists_chart_read_at_frames | (intros; apply GlobalTheory.DegCmp.exists_chart_read_at_frames <;> assumption)
end

