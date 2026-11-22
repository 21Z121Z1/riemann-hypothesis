import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrreducibleConstituentRanksUniqueOfCharpoly
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0024
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0385
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0606
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0028
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0054
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0055
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleConstituentsCharpolyProduct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0056

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrreducibleConstituentRanksUniqueOfCharpolyStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrreducible_constituent_ranks_unique_of_charpoly : SSRankUnique := by
  first | exact @GlobalTheory.SSRank.ssRankUnique_holds | exact GlobalTheory.SSRank.ssRankUnique_holds | (intros; apply GlobalTheory.SSRank.ssRankUnique_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BocksteinReductionCommutesWithRestriction
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

noncomputable section

namespace GlobalTheory.EtC.BockRed

open GlobalTheory.EtC

def comp {S R T : Type} [CommRing S] [CommRing R] [CommRing T] {I : Cx S} {J : Cx R} {K : Cx T}
    (ρ : SemiMap I J) (σ : SemiMap J K) : SemiMap I K where
  app U s := (σ.app U s).comp (ρ.app U s)
  nat g s a := by
    change Sec.res g (σ.app _ s (ρ.app _ s a)) = σ.app _ s (ρ.app _ s (Sec.res g a))
    rw [σ.nat, ρ.nat]
  comm U s t a := by
    change Sec.map _ (σ.app U s (ρ.app U s a)) = σ.app U t (ρ.app U t (Sec.map _ a))
    rw [σ.comm, ρ.comm]

end GlobalTheory.EtC.BockRed

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacterTrivialAtWildOfCoprimePowStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_trivial_at_wild_of_coprime_pow : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω), A.valuation (p : Ω) < 1 → ∀ (R : Type) [CommRing R] (χ : G F Ω →* Rˣ), IsOpen (χ.ker : Set (G F Ω)) → ∀ σ : G F Ω, (∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) → ∀ m : ℕ, 0 < m → Nat.Coprime m p → χ σ ^ m = 1 → χ σ = 1 := by
  first | exact @GlobalTheory.WildChar.main | exact GlobalTheory.WildChar.main | (intros; apply GlobalTheory.WildChar.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletionEmbeddingsSingleFrobeniusOrbitStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_embeddings_single_frobenius_orbit : ∀ {R : Ranks} (H : Host R) (l : ℕ) [Fact l.Prime], l ∉ H.small → l ≠ H.q → l ≠ H.d → ∀ (c : H.E →+* PadicAlgCl l) (K : Loc.FinExt l) (hc : ∀ x, c x ∈ K.1), (K.1 : Set (PadicAlgCl l)) ⊆ closure (Set.range c) → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})] (s : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ s P → Module.finrank ℚ_[l] ↥K.1 = orderOf (H.galE s) ∧ ∀ τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l, ∃! i : ZMod (orderOf (H.galE s)), ∀ x : H.E, τ ⟨c x, hc x⟩ = c ((s ^ i.val) x) := by
  first | exact @GlobalTheory.LocalFrobeniusOrbit.embeddings_orbit | exact GlobalTheory.LocalFrobeniusOrbit.embeddings_orbit | (intros; apply GlobalTheory.LocalFrobeniusOrbit.embeddings_orbit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CosetDecompositionEvenOrder
section
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

namespace GlobalTheory

theorem pow_mem_iff_even_of_index_two_notMem {G : Type} [Group G] (H : Subgroup G) (hH : H.index = 2)
    (a : G) (ha : a ∉ H) (k : ℕ) : a ^ k ∈ H ↔ Even k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Subgroup.mul_mem_iff_of_index_two hH, Nat.even_add_one, ih]
    simp [ha]

theorem frobenius_orbit_positions_comm (G : Type) [CommGroup G] [Finite G] (H : Subgroup G) (φ c : G)
    (hH : H.index = 2) (hφ : φ ∉ H) (hc : c ∉ H) (hcc : c * c = 1) (hcZ : c ∉ Subgroup.zpowers φ) :
    2 ≤ orderOf φ ∧ Even (orderOf φ) ∧ ∃ (N : ℕ) (g : Fin N → G) (pos : (Σ _ : Fin N, Fin (orderOf φ)) ≃ H), 0 < N ∧ (∀ v s, (pos ⟨v, s⟩ : G) = φ ^ s.val * g v * c ^ s.val) ∧ (∀ v v', g v' * (g v)⁻¹ ∈ Subgroup.zpowers φ → v = v') ∧ (∀ v v', g v' * c * (g v)⁻¹ ∉ Subgroup.zpowers φ) ∧ ∀ x : G, ∃ v, g v * x⁻¹ ∈ Subgroup.zpowers φ ∨ g v * c * x⁻¹ ∈ Subgroup.zpowers φ := by
  classical
  have hφk := pow_mem_iff_even_of_index_two_notMem H hH φ hφ
  have hck := pow_mem_iff_even_of_index_two_notMem H hH c hc
  have hev : Even (orderOf φ) := (hφk _).1 (by rw [pow_orderOf_eq_one]; exact H.one_mem)
  have hpos : 0 < orderOf φ := orderOf_pos φ
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hce : ∀ k : ℕ, Even k → c ^ k = 1 := by
    rintro k ⟨m, rfl⟩
    rw [pow_add, ← mul_pow, hcc, one_pow]
  have hco : ∀ k : ℕ, ¬ Even k → c ^ k = c := by
    intro k hk
    obtain ⟨m, rfl⟩ := Nat.not_even_iff_odd.1 hk
    rw [pow_succ, hce _ (even_two_mul m), one_mul]
  refine ⟨by obtain ⟨m, hm⟩ := hev; omega, hev, ?_⟩
  set Z := Subgroup.zpowers φ with hZ
  let D : Subgroup G := Z ⊔ Subgroup.zpowers c
  have hZD : Z ≤ D := le_sup_left
  have hcD : c ∈ D := (le_sup_right : Subgroup.zpowers c ≤ D) (Subgroup.mem_zpowers c)
  have hφD : φ ∈ D := hZD (Subgroup.mem_zpowers φ)
  have hD : ∀ x ∈ D, x ∈ Z ∨ x * c ∈ Z := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    obtain ⟨k, rfl⟩ := (mem_powers_iff_mem_zpowers.2 hz : z ∈ Submonoid.powers c)
    by_cases hk : Even k
    · left; simpa [hce k hk] using hy
    · right; simpa [hco k hk, mul_assoc, hcc] using hy
  have hZpow : ∀ x ∈ Z, ∃ s : Fin (orderOf φ), φ ^ s.val = x := by
    intro x hx
    obtain ⟨k, rfl⟩ := (mem_powers_iff_mem_zpowers.2 hx : x ∈ Submonoid.powers φ)
    exact ⟨⟨k % orderOf φ, Nat.mod_lt _ hpos⟩, pow_mod_orderOf φ k⟩
  have hr : ∀ q : G ⧸ D, ∃ a : G, a ∈ H ∧ (a : G ⧸ D) = q := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    by_cases ha : a ∈ H
    · exact ⟨a, ha, rfl⟩
    · refine ⟨a * c, ?_, ?_⟩
      · rw [Subgroup.mul_mem_iff_of_index_two hH]; simp [ha, hc]
      · exact QuotientGroup.mk_mul_of_mem a hcD
  choose r hrH hrq using hr
  let e : Fin (Nat.card (G ⧸ D)) ≃ G ⧸ D := (Finite.equivFin (G ⧸ D)).symm
  let g : Fin (Nat.card (G ⧸ D)) → G := fun v => r (e v)
  have hgH : ∀ v, g v ∈ H := fun v => hrH _
  have key : ∀ v v', g v' * (g v)⁻¹ ∈ D → v = v' := by
    intro v v' h
    apply e.injective
    rw [← hrq (e v), ← hrq (e v'), QuotientGroup.eq, mul_comm]
    exact h
  have cover : ∀ x : G, ∃ v, g v * x⁻¹ ∈ D := by
    intro x
    refine ⟨e.symm (x : G ⧸ D), ?_⟩
    have h := hrq (x : G ⧸ D)
    rw [eq_comm, QuotientGroup.eq, mul_comm] at h
    simpa [g] using h
  let f : (Σ _ : Fin (Nat.card (G ⧸ D)), Fin (orderOf φ)) → H := fun p =>
    ⟨φ ^ p.2.val * g p.1 * c ^ p.2.val, by
      rw [Subgroup.mul_mem_iff_of_index_two hH, H.mul_mem_cancel_right (hgH _), hφk, hck]⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨v, s⟩ ⟨v', t⟩ h
      have h' : φ ^ s.val * g v * c ^ s.val = φ ^ t.val * g v' * c ^ t.val := congrArg Subtype.val h
      have hv : v = v' := by
        apply key
        have : g v' * (g v)⁻¹ = φ ^ s.val * c ^ s.val * (φ ^ t.val * c ^ t.val)⁻¹ := by
          rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
          calc g v' * (φ ^ t.val * c ^ t.val) = φ ^ t.val * g v' * c ^ t.val := by ac_rfl
            _ = φ ^ s.val * g v * c ^ s.val := h'.symm
            _ = _ := by ac_rfl
        rw [this]
        exact D.mul_mem (D.mul_mem (D.pow_mem hφD _) (D.pow_mem hcD _))
          (D.inv_mem (D.mul_mem (D.pow_mem hφD _) (D.pow_mem hcD _)))
      subst hv
      have h2 : φ ^ s.val * c ^ s.val = φ ^ t.val * c ^ t.val := by
        apply mul_left_cancel (a := g v)
        calc g v * (φ ^ s.val * c ^ s.val) = φ ^ s.val * g v * c ^ s.val := by ac_rfl
          _ = φ ^ t.val * g v * c ^ t.val := h'
          _ = _ := by ac_rfl
      have hZp : ∀ k : ℕ, φ ^ k ∈ Z := fun k => Z.pow_mem (Subgroup.mem_zpowers φ) k
      have h3 : φ ^ s.val = φ ^ t.val := by
        by_cases hs : Even s.val <;> by_cases ht : Even t.val
        · simpa [hce _ hs, hce _ ht] using h2
        · exfalso
          rw [hce _ hs, hco _ ht, mul_one] at h2
          exact hcZ ((Z.mul_mem_cancel_left (hZp t.val)).1 (h2 ▸ hZp s.val))
        · exfalso
          rw [hco _ hs, hce _ ht, mul_one] at h2
          exact hcZ ((Z.mul_mem_cancel_left (hZp s.val)).1 (h2 ▸ hZp t.val))
        · rw [hco _ hs, hco _ ht] at h2
          exact mul_right_cancel h2
      have h4 : s = t := Fin.ext (pow_injOn_Iio_orderOf s.2 t.2 h3)
      subst h4
      rfl
    · rintro ⟨h, hh⟩
      obtain ⟨v, hv⟩ := cover h
      have hv' : h * (g v)⁻¹ ∈ D := by
        have := D.inv_mem hv
        rwa [mul_inv_rev, inv_inv] at this
      have hH' : h * (g v)⁻¹ ∈ H := H.mul_mem hh (H.inv_mem (hgH v))
      rcases hD _ hv' with h1 | h1
      · obtain ⟨s, hs⟩ := hZpow _ h1
        refine ⟨⟨v, s⟩, Subtype.ext ?_⟩
        have hes : Even s.val := (hφk _).1 (hs ▸ hH')
        show φ ^ s.val * g v * c ^ s.val = h
        rw [hce _ hes, hs]; simp
      · obtain ⟨s, hs⟩ := hZpow _ h1
        refine ⟨⟨v, s⟩, Subtype.ext ?_⟩
        have hes : ¬ Even s.val := by
          rw [← hφk, hs, H.mul_mem_cancel_left hH']; exact hc
        show φ ^ s.val * g v * c ^ s.val = h
        rw [hco _ hes, hs]
        calc h * (g v)⁻¹ * c * g v * c = h * ((g v)⁻¹ * g v) * (c * c) := by ac_rfl
          _ = h := by simp [hcc]
  refine ⟨Nat.card (G ⧸ D), g, Equiv.ofBijective f hf, Nat.card_pos, fun v s => rfl,
    fun v v' h => key v v' (hZD h), ?_, ?_⟩
  · intro v v' h
    have h1 : g v' * c * (g v)⁻¹ = g v' * (g v)⁻¹ * c := by ac_rfl
    rw [h1] at h
    have hv := key v v' ((D.mul_mem_cancel_right hcD).1 (hZD h))
    subst hv
    exact hcZ (by simpa using h)
  · intro x
    obtain ⟨v, hv⟩ := cover x
    refine ⟨v, (hD _ hv).imp id fun h => ?_⟩
    have h1 : g v * c * x⁻¹ = g v * x⁻¹ * c := by ac_rfl
    rwa [h1]

theorem frobenius_orbit_positions : ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (φ c : G), (∀ a b : G, a * b = b * a) → H.index = 2 → φ ∉ H → c ∉ H → c * c = 1 → c ∉ Subgroup.zpowers φ → 2 ≤ orderOf φ ∧ Even (orderOf φ) ∧ ∃ (N : ℕ) (g : Fin N → G) (pos : (Σ _ : Fin N, Fin (orderOf φ)) ≃ H), 0 < N ∧ (∀ v s, (pos ⟨v, s⟩ : G) = φ ^ s.val * g v * c ^ s.val) ∧ (∀ v v', g v' * (g v)⁻¹ ∈ Subgroup.zpowers φ → v = v') ∧ (∀ v v', g v' * c * (g v)⁻¹ ∉ Subgroup.zpowers φ) ∧ ∀ x : G, ∃ v, g v * x⁻¹ ∈ Subgroup.zpowers φ ∨ g v * c * x⁻¹ ∈ Subgroup.zpowers φ := by
  intro G inst _ H φ c hcomm
  letI : CommGroup G := { inst with mul_comm := hcomm }
  exact frobenius_orbit_positions_comm G H φ c

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrExtensionEmbedding
section
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

namespace GlobalTheory

theorem exists_finite_ext_numberField_sqrt (Qq E K : Type) [Field Qq] [Field E] [Field K]
    [NumberField K] (i : E →+* Qq) (e : E →+* K) (a : Qq) :
    ∃ (Kf : IntermediateField Qq (AlgebraicClosure Qq)) (s : Kf) (eK : K →+* Kf),
      FiniteDimensional Qq Kf ∧ s ^ 2 = algebraMap Qq Kf a ∧
        ∀ x : E, eK (e x) = algebraMap Qq Kf (i x) := by
  classical
  let Ω := AlgebraicClosure Qq
  letI : Algebra E K := e.toAlgebra
  letI : Algebra E Ω := ((algebraMap Qq Ω).comp i).toAlgebra
  haveI : CharZero E := RingHom.charZero e
  haveI : Module.Finite E K := Module.Finite.of_restrictScalars_finite ℚ E K
  let f : K →ₐ[E] Ω := IsAlgClosed.lift
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap Qq Ω a) (n := 2) two_pos
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := E) (M := K)
  let S : Set Ω := insert s (f '' (T : Set K))
  haveI : Finite S := ((T.finite_toSet.image f).insert s).to_subtype
  let Kf : IntermediateField Qq Ω := IntermediateField.adjoin Qq S
  have hfin : FiniteDimensional Qq Kf :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hmem : ∀ x : K, f x ∈ Kf := by
    intro x
    have hx : x ∈ Submodule.span E (T : Set K) := hT ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      exact IntermediateField.subset_adjoin Qq S (Set.mem_insert_of_mem _ ⟨y, hy, rfl⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy =>
      rw [map_smul, Algebra.smul_def]
      exact mul_mem (Kf.algebraMap_mem (i c)) hy
  refine ⟨Kf, ⟨s, IntermediateField.subset_adjoin Qq S (Set.mem_insert _ _)⟩,
    (f : K →+* Ω).codRestrict Kf hmem, hfin, Subtype.ext hs, fun x => Subtype.ext ?_⟩
  exact f.commutes x

theorem exists_complete_dvr_ext_numberField_sqrt : ∀ (W Qq E K : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [Field E] [Field K] [NumberField K] (i : E →+* Qq) (e : E →+* K) (a : W), ∃ (O Kf : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : Field Kf) (_ : Algebra O Kf) (ι : Qq →+* Kf) (j : W →+* O) (w : O) (eK : K →+* Kf), IsFractionRing O Kf ∧ (∀ x : W, ι (algebraMap W Qq x) = algebraMap O Kf (j x)) ∧ j.Finite ∧ IsAdicComplete (IsLocalRing.maximalIdeal O) O ∧ w ^ 2 = j a ∧ ∀ x : E, eK (e x) = ι (i x) := by
  intro W Qq E K _ _ _ _ _ _ _ _ _ _ i e a
  obtain ⟨Kf, s, eK, hfin, hs, he⟩ :=
    exists_finite_ext_numberField_sqrt Qq E K i e (algebraMap W Qq a)
  letI : Algebra W Kf := ((algebraMap Qq Kf).comp (algebraMap W Qq)).toAlgebra
  haveI : IsScalarTower W Qq Kf := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI h1 := FormalIsogeny.finite_integralClosure W Qq Kf
  haveI h2 := FormalIsogeny.isDiscreteValuationRing_integralClosure W Qq Kf
  have h3 := FormalIsogeny.isAdicComplete_maximalIdeal_of_finite W (integralClosure W Kf)
  have h4 := integralClosure.isFractionRing_of_finite_extension (A := W) Qq Kf
  have hs' : s ^ 2 = algebraMap W Kf a := hs
  have hint : IsIntegral W s :=
    IsIntegral.of_pow two_pos (hs' ▸ isIntegral_algebraMap)
  exact ⟨integralClosure W Kf, Kf, inferInstance, inferInstance, h2, inferInstance, inferInstance,
    algebraMap Qq Kf, algebraMap W _, ⟨s, hint⟩, eK, h4, fun _ => rfl,
    RingHom.finite_algebraMap.2 h1, h3, Subtype.ext hs', he⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFrobeniusConjInertiaPowModWildStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_conj_inertia_pow_mod_wild : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (k : Fin 2) (v : N.PlG k), ∀ γ ∈ Ine (F := H.E) (N.plOm.1 (A.plGw k v)), ∃ φ : G H.E N.Om, φ * γ * φ⁻¹ * (γ ^ H.g k)⁻¹ ∈ Ine (F := H.E) (N.plOm.1 (A.plGw k v)) ∧ φ * γ * φ⁻¹ * (γ ^ H.g k)⁻¹ ∈ wildSet N (N.plOm.1 (A.plGw k v)) := by
  first | exact @GlobalTheory.TameRel.main | exact GlobalTheory.TameRel.main | (intros; apply GlobalTheory.TameRel.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGlobalLatticeLocalGiven
section
noncomputable section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO

namespace TupApx

variable {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_pow_smul {π : R} (hπ : Irreducible π) {k : ℕ} (g : Matrix (Fin k) (Fin k) K) :
    ∃ (a : ℕ) (g0 : Matrix (Fin k) (Fin k) R), algebraMap R K π ^ a • g = g0.map (algebraMap R K) := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun ij : Fin k × Fin k => g ij.1 ij.2)
  obtain ⟨a, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.coe_ne_zero d) hπ
  choose y hy using hd
  refine ⟨a, Matrix.of fun i j => (u⁻¹ : Rˣ) * y (i, j), ?_⟩
  ext i j
  have h1 : π ^ a = (u⁻¹ : Rˣ) * (d : R) := by rw [hu]; simp
  rw [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, map_mul, hy, ← map_pow, h1, map_mul, smul_eq_mul,
    Algebra.smul_def, mul_assoc]

theorem exists_approx {E : Type} [Field E] (f : E →+* K) {π : R} (hπ : Irreducible π) (t : E)
    (ht : f t = algebraMap R K π)
    (hd : ∀ (y : R) (N : ℕ), ∃ (x : E) (z : R), f x = algebraMap R K (y + π ^ N * z))
    {k : ℕ} (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det) :
    ∃ (B : Matrix (Fin k) (Fin k) E) (u : Matrix (Fin k) (Fin k) R), IsUnit u.det ∧
      B.map f = g * u.map (algebraMap R K) := by
  obtain ⟨a, g0, h0⟩ := exists_pow_smul (K := K) hπ g
  obtain ⟨b, h, h1⟩ := exists_pow_smul (K := K) hπ g⁻¹
  choose x z hx using fun i j => hd (g0 i j) (a + b + 1)
  have hp0 : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ.ne_zero
  refine ⟨Matrix.of fun i j => (t ^ a)⁻¹ * x i j, 1 + π • (h * Matrix.of z), ?_, ?_⟩
  · rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    have hr : IsLocalRing.residue R π = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff]; exact hπ.not_isUnit
    have : (IsLocalRing.residue R).mapMatrix (1 + π • (h * Matrix.of z)) = 1 := by
      rw [map_add, map_one]
      have : (IsLocalRing.residue R).mapMatrix (π • (h * Matrix.of z)) = 0 := by
        ext i j; simp [hr]
      rw [this, add_zero]
    rw [this]; simp
  · have e1 : (1 + π • (h * Matrix.of z)).map (algebraMap R K) =
        1 + algebraMap R K π • (h.map (algebraMap R K) * (Matrix.of z).map (algebraMap R K)) := by
      rw [← Matrix.map_mul]
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, Matrix.one_apply,
        apply_ite (algebraMap R K), map_one, map_zero]
    rw [e1, ← h1, mul_add, mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]
    ext i j
    have h2 := congrFun (congrFun h0 i) j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h2
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀,
      map_pow, ht, hx, map_add, ← h2]
    field_simp
    ring

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem colSpan_mul_le {k : ℕ} (g : Matrix (Fin k) (Fin k) K) (u : Matrix (Fin k) (Fin k) R) :
    colSpan R (g * u.map (algebraMap R K)) ≤ colSpan R g := by
  rw [colSpan, Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  have : (fun i => (g * u.map (algebraMap R K)) i c) = ∑ j, u j c • fun i => g i j := by
    funext i
    simp [Matrix.mul_apply, Algebra.smul_def, mul_comm]
  change (fun i => (g * u.map (algebraMap R K)) i c) ∈ colSpan R g
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem colSpan_mul_eq {k : ℕ} (g : Matrix (Fin k) (Fin k) K) (u : Matrix (Fin k) (Fin k) R) (hu : IsUnit u.det) :
    colSpan R (g * u.map (algebraMap R K)) = colSpan R g := by
  refine le_antisymm (colSpan_mul_le g u) ?_
  have := colSpan_mul_le (g * u.map (algebraMap R K)) u⁻¹
  rwa [Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this

theorem isLattice_colSpan {A E : Type} [CommRing A] [Field E] [Algebra A E] {k : ℕ} (B : Matrix (Fin k) (Fin k) E)
    (hB : IsUnit B.det) : Submodule.IsLattice E (colSpan A B) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [colSpan, Submodule.span_span_of_tower, eq_top_iff]
  intro w _
  have : w = ∑ j, (B⁻¹.mulVec w) j • fun i => B i j := by
    funext i
    have h : B.mulVec (B⁻¹.mulVec w) = w := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]
    conv_lhs => rw [← h]
    generalize B⁻¹.mulVec w = y
    simp [Matrix.mulVec, dotProduct, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem span_image {A E R K : Type} [CommRing A] [Field E] [Algebra A E] [CommRing R] [Field K] [Algebra R K]
    (f : E →+* K) (hf : ∀ r : A, f (algebraMap A E r) ∈ Set.range (algebraMap R K)) {k : ℕ}
    (B : Matrix (Fin k) (Fin k) E) :
    Submodule.span R ((fun (x : Fin k → E) i => f (x i)) '' (colSpan A B : Set (Fin k → E))) = colSpan R (B.map f) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    change (fun i => f (x i)) ∈ colSpan R (B.map f)
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      exact Submodule.subset_span ⟨c, rfl⟩
    | zero =>
      have : (fun i => f ((0 : Fin k → E) i)) = 0 := by funext i; simp
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : (fun i => f ((x + y) i)) = (fun i => f (x i)) + fun i => f (y i) := by funext i; simp
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      obtain ⟨s, hs⟩ := hf a
      have : (fun i => f ((a • x) i)) = s • fun i => f (x i) := by
        funext i; simp [Algebra.smul_def, hs]
      rw [this]; exact Submodule.smul_mem _ _ hx
  · rw [colSpan, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact Submodule.subset_span ⟨fun i => B i c, Submodule.subset_span ⟨c, rfl⟩, rfl⟩

end TupApx

theorem exists_tup_eq : ∀ (p : ℕ) (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] (X : Fields) (P : Places p O Kf) (T : PlTie X P) (n : ℕ) (hn : n = P.m + 1) (v : Fin P.nV) (L : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)), Formalism.MainNotions.G.IsLattice (P.W v) L → ∃ M : Submodule (𝓞 X.E) (Sp X.E n), Submodule.IsLattice X.E M ∧ T.tup hn M v = L := by
  intro p O Kf _ _ _ _ _ X P T n hn v L hL
  subst hn
  obtain ⟨g, hg, rfl⟩ := hL
  have hS := P.setting v
  haveI := hS.frac_alt
  obtain ⟨B, u, hu, hB⟩ := TupApx.exists_approx (T.iw v) hS.p_unif (p : X.E) (by simp)
    (fun y N => by obtain ⟨x, z, h⟩ := T.iw_dense v y N; exact ⟨x, z, h⟩) g hg
  have hdet : IsUnit B.det := by
    have h1 : T.iw v B.det = g.det * algebraMap _ _ u.det := by
      rw [RingHom.map_det, RingHom.map_det, ← Matrix.det_mul]
      exact congrArg Matrix.det hB
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, map_zero] at h1
    exact (hg.mul (hu.map _)).ne_zero h1.symm
  refine ⟨colSpan (𝓞 X.E) B, TupApx.isLattice_colSpan B hdet, ?_⟩
  rw [← TupApx.colSpan_mul_eq g u hu, ← hB,
    ← TupApx.span_image (T.iw v) (fun r => (T.iw_int v _).1 (IntAt.coe _ r)) B]
  rfl

end GlobalTheory.GO
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleConstituentsCharpolyProductStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_constituents_charpoly_product : SSList := by
  first | exact @GlobalTheory.ssList_holds | exact GlobalTheory.ssList_holds | (intros; apply GlobalTheory.ssList_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobeniusNontrivialOnInertQuadratic
section
open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

namespace GlobalTheory

theorem frobenius_moves_quadratic_subfield_of_inert :
    ∀ (E : Type) [Field E] [NumberField E] (M : Subfield E) (p : ℕ) (Q : HeightOneSpectrum (𝓞 E)) (φ : E ≃ₐ[ℚ] E), p.Prime → Module.finrank ℚ M = 2 → (Ideal.span {((p : ℕ) : 𝓞 M)}).IsPrime → ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal → (∀ x : 𝓞 E, φ • x - x ^ p ∈ Q.asIdeal) → ∃ x ∈ M, φ x ≠ x := by
  intro E _ _ M p Q φ hp hM hP hQ hφ
  by_contra h
  push_neg at h
  haveI : FiniteDimensional ℚ M := Module.finite_of_finrank_pos (by omega)
  haveI : NumberField M := {}
  let f : 𝓞 M →+* 𝓞 E := RingOfIntegers.mapRingHom M.subtype
  have hp0 : ((p : ℕ) : 𝓞 M) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hcard : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 M)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, hM]
  set P : Ideal (𝓞 M) := Ideal.span {((p : ℕ) : 𝓞 M)} with hPdef
  have hne : P ≠ ⊥ := by
    rw [hPdef, Ne, Ideal.span_singleton_eq_bot]; exact hp0
  have hmax : P.IsMaximal := hP.isMaximal hne
  have hcom : P = Q.asIdeal.comap f := by
    refine hmax.eq_of_le (Ideal.comap_ne_top f Q.isPrime.ne_top) ?_
    rw [hPdef, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hQ
  have key : ∀ x : 𝓞 M ⧸ P, x ^ p = x := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_pow, eq_comm, Ideal.Quotient.eq, hcom, Ideal.mem_comap, map_sub, map_pow]
    have h1 : φ • f y = f y := by
      apply Subtype.ext
      exact h _ (y : M).2
    have h2 := hφ (f y)
    rwa [h1] at h2
  haveI : Finite (𝓞 M ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hne
  letI : Fintype (𝓞 M ⧸ P) := Fintype.ofFinite _
  haveI : IsDomain (𝓞 M ⧸ P) := Ideal.Quotient.isDomain P
  have hc : Fintype.card (𝓞 M ⧸ P) = p ^ 2 := by
    rw [← hcard, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  classical
  have h1 : 1 < p := hp.one_lt
  have hdeg : (Polynomial.X ^ p - Polynomial.X : Polynomial (𝓞 M ⧸ P)).natDegree = p := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;> simp [h1]
  have hnz : (Polynomial.X ^ p - Polynomial.X : Polynomial (𝓞 M ⧸ P)) ≠ 0 := by
    intro h0
    rw [h0] at hdeg
    simp at hdeg
    omega
  have hle : (Finset.univ : Finset (𝓞 M ⧸ P)).card ≤ p := by
    refine le_trans ?_ hdeg.le
    apply Polynomial.card_le_degree_of_subset_roots
    intro x _
    rw [Polynomial.mem_roots hnz]
    simp [key x]
  rw [Finset.card_univ, hc] at hle
  nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacterStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mu_character : MuChar := by
  first | exact @GlobalTheory.MuCharProof.muChar_holds | exact GlobalTheory.MuCharProof.muChar_holds | (intros; apply GlobalTheory.MuCharProof.muChar_holds <;> assumption)
end

