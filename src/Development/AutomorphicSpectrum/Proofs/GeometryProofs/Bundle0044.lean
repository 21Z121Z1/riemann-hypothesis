import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0037
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0015
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0011
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0029
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalIsoOfIntegrallyClosedStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_iso_of_integrally_closed : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (p : Cpt ξ), NormAt ξ' f (RingHom.id Ω) p → (∀ a : Ω, IsIntegral (regAt ξ p) a → a ∈ regAt ξ p) → IsoAt ξ' f (RingHom.id Ω) p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.NormAt.isoAt_of_integrallyClosed | exact GlobalTheory.CompanionTheory.Ar.NormAt.isoAt_of_integrallyClosed | (intros; apply GlobalTheory.CompanionTheory.Ar.NormAt.isoAt_of_integrallyClosed <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NotInFibreOfIsUnit
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem regAt_isLocalRing (q : Cpt ξ) : IsLocalRing (regAt ξ q) :=
  IsLocalRing.of_surjective' (genMap ξ q).rangeRestrict (genMap ξ q).rangeRestrict_surjective

theorem not_inFibre_of_isUnit {q : Cpt ξ} {p : ℕ} (h : IsUnit (p : regAt ξ q)) : ¬ InFibre ξ p q := by
  obtain ⟨v, hv⟩ := h.exists_right_inv
  have e : (p : Ω) * (v : Ω) = 1 := by
    have := congrArg (Subtype.val) hv
    simpa using this
  have hp : (p : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one e
  have hreg : (p : Ω) ∈ regAt ξ q := natCast_mem (regAt ξ q) p
  have hinv : (p : Ω)⁻¹ ∈ regAt ξ q := by
    rw [eq_comm.1 (eq_inv_of_mul_eq_one_right e)]
    exact v.2
  exact not_not.2 ⟨hp, hreg, hinv⟩

theorem inFibre_unique {q : Cpt ξ} {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (h : InFibre ξ p q)
    (h' : InFibre ξ p' q) : p' = p := by
  by_contra hne
  haveI := regAt_isLocalRing (ξ := ξ) q
  have hc : IsCoprime (p : ℤ) (p' : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hp').2 (Ne.symm hne))
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (regAt ξ q))
  simp only [eq_intCast, Int.cast_natCast] at hab
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with hu | hu
  · exact not_inFibre_of_isUnit (isUnit_of_mul_isUnit_right hu) h
  · exact not_inFibre_of_isUnit (isUnit_of_mul_isUnit_right hu) h'

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrderValuationCompare
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem z_value_of_order : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (L : Lat ξ Ω) (σ ϖ : Ω) (M : ℕ) (a : ℤ) (V C : Type) [CommRing V] [IsLocalRing V] [Field C] [Algebra V C] (z : Spec (CommRingCat.of V) ⟶ X) (h : genPt ξ ⤳ centre z) (e : Ω) (γ π : C), IsCptGen ξ → OrderAt L σ ϖ M a ⟨centre z, h⟩ → L.IsGenAt ⟨centre z, h⟩ e → ValAt ξ (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) (σ / e) γ → ValAt ξ (Spec.map (CommRingCat.ofHom (algebraMap V C)) ≫ z) ϖ π → π ≠ 0 → ∃ u : Vˣ, γ ^ M = π ^ a * algebraMap V C u :=
  @PositivityTheory.Xgn.valuation_at_centre_order

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PieceLocalizationAtElement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem exists_basicOpen_piece (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (U : X.Opens) (R : Subring Ω) (a : Ω) (hc : IsCptGen ξ) (hP : IsPiece ξ U R) (haR : a ∈ R)
    (ha0 : a ≠ 0) :
    ∃ U' : X.Opens, IsPiece ξ U' (locSub R a) ∧ ∀ q : Cpt ξ, q.1 ∈ U' ↔ q.1 ∈ U ∧ unitAt ξ q a := by
  by_cases hη : genPt ξ ∈ U
  swap
  · have hno : ∀ q : Cpt ξ, q.1 ∉ U := fun q hq => hη (q.2.mem_open U.isOpen hq)
    refine ⟨U, ⟨hP.affine, hP.spec, fun b => ?_⟩, fun q => ?_⟩
    · refine ⟨fun _ q hq => absurd hq (hno q), fun _ => le_locSub R a ?_⟩
      exact (hP.ring b).2 fun q hq => absurd hq (hno q)
    · exact ⟨fun h => absurd h (hno q), fun h => h.1⟩
  obtain ⟨-, hrng⟩ := GlobalTheory.T.germ_genPt_injective_range_regAt X Ω ξ hc U hη hP.spec
  obtain ⟨s, hs⟩ := (hrng a).2 ((hP.ring a).1 haR)
  have hga : ∀ (q : Cpt ξ) (hq : q.1 ∈ U), genMap ξ q (X.presheaf.germ U q.1 hq s) = a :=
    fun q hq => (genMap_germ_eq_stalk_closed ξ q U hq hη s).trans hs
  have hmem : ∀ q : Cpt ξ, q.1 ∈ X.basicOpen s ↔ q.1 ∈ U ∧ unitAt ξ q a := by
    intro q
    constructor
    · intro hq
      have hqU : q.1 ∈ U := X.basicOpen_le s hq
      have hu := (Scheme.mem_basicOpen X s q.1 hqU).1 hq
      obtain ⟨v, hv⟩ := hu.exists_right_inv
      have h1 : a * genMap ξ q v = 1 := by
        rw [← hga q hqU, ← map_mul, hv, map_one]
      exact ⟨hqU, ha0, ⟨_, hga q hqU⟩, ⟨v, (inv_eq_of_mul_eq_one_right h1).symm⟩⟩
    · rintro ⟨hqU, -, -, ⟨t, ht⟩⟩
      refine (Scheme.mem_basicOpen X s q.1 hqU).2 (isUnit_iff_exists_inv.2 ⟨t, hc.inj q ?_⟩)
      rw [map_mul, map_one, hga q hqU, ht, mul_inv_cancel₀ ha0]
  have hreg : ∀ c : Ω, c ∈ regAt ξ (Subtype.mk (genPt ξ) specializes_rfl : Cpt ξ) := by
    intro c
    obtain ⟨y, hy⟩ := hc.bij.2 c
    refine ⟨y, ?_⟩
    have e : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
      TopCat.Presheaf.stalkSpecializes_refl _ _
    change (X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) ≫
      Scheme.stalkClosedPointTo ξ).hom y = c
    rw [e]
    exact hy
  have hη' : genPt ξ ∈ X.basicOpen s :=
    (hmem (Subtype.mk (genPt ξ) specializes_rfl : Cpt ξ)).2 ⟨hη, ha0, hreg a, hreg a⁻¹⟩
  refine ⟨X.basicOpen s, ⟨hP.affine.basicOpen s, fun q hq => hP.spec q (X.basicOpen_le s hq),
    fun b => ?_⟩, hmem⟩
  constructor
  · intro hb q hq
    obtain ⟨k, hk⟩ := (mem_locSub_iff haR ha0 b).1 hb
    obtain ⟨hqU, -, -, hinv⟩ := (hmem q).1 hq
    have h1 := (hP.ring _).1 hk q hqU
    have e : b = a⁻¹ ^ k * (a ^ k * b) := by
      rw [inv_pow, ← _root_.mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ha0), _root_.one_mul]
    rw [e]
    exact (regAt ξ q).mul_mem ((regAt ξ q).pow_mem hinv _) h1
  · intro hb
    obtain ⟨-, hrng'⟩ := GlobalTheory.T.germ_genPt_injective_range_regAt X Ω ξ hc (X.basicOpen s) hη'
      (fun q hq => hP.spec q (X.basicOpen_le s hq))
    obtain ⟨t, ht⟩ := (hrng' b).2 hb
    have hloc := hP.affine.isLocalization_basicOpen s
    obtain ⟨n, c, hcn⟩ := IsLocalization.Away.surj s t
    have hres : ∀ x : Γ(X, U),
        (X.presheaf.germ (X.basicOpen s) (genPt ξ) hη' ≫ Scheme.stalkClosedPointTo ξ).hom
          (algebraMap Γ(X, U) Γ(X, X.basicOpen s) x) =
        (X.presheaf.germ U (genPt ξ) hη ≫ Scheme.stalkClosedPointTo ξ).hom x := by
      intro x
      have := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (X.basicOpen_le s)) (genPt ξ) hη' x
      exact congrArg (Scheme.stalkClosedPointTo ξ).hom this
    have key : a ^ n * b = (X.presheaf.germ U (genPt ξ) hη ≫ Scheme.stalkClosedPointTo ξ).hom c := by
      have := congrArg (X.presheaf.germ (X.basicOpen s) (genPt ξ) hη' ≫
        Scheme.stalkClosedPointTo ξ).hom hcn
      rw [map_mul, map_pow, hres, hres, hs, ht] at this
      rw [← this, _root_.mul_comm]
    refine (mem_locSub_iff haR ha0 b).2 ⟨n, (hP.ring _).2 fun q hq => ?_⟩
    rw [key]
    exact (hrng _).1 ⟨c, rfl⟩ q hq

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModelNonemptyStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_model_nonempty : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω), (∃ c, x c ≠ 0 ∧ ∀ a : Ω, ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, a = u / v) → Nonempty (PModel o x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.nonempty_pModel_of_chart | exact GlobalTheory.CompanionTheory.Ar.nonempty_pModel_of_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.nonempty_pModel_of_chart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperDominatingSurjectiveStatement
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_dominating_surjective : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (s' : X' ⟶ Spec (CommRingCat.of ℤ)) (f : X' ⟶ X) (i : Ω →+* Ω'), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → IsProper s' → Dominates ξ' ξ f i → Function.Surjective f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.surjective_of_dominates | exact GlobalTheory.CompanionTheory.Ar.FlagBun.surjective_of_dominates | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.surjective_of_dominates <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtChartLocalization
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem chart_regAt_localisation : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (c : κ) (p : Cpt M.ξ), InChart M.ξ x c p → (∀ a ∈ chRing o x c, a ∈ regAt M.ξ p) ∧ ∀ a : Ω, a ∈ regAt M.ξ p ↔ ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, unitAt M.ξ p v ∧ a = u / v :=
  PositivityTheory.HtPt.Ma.regat_loc

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtLeIffSpecializes
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem regAt_le_regAt_iff_specializes : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (p q : Cpt M.ξ), regAt M.ξ p ≤ regAt M.ξ q ↔ q.1 ⤳ p.1 :=
  @PositivityTheory.HtPt.Ma.reg_le_spec

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtLocalOrderFraction
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar

theorem regAt_local_mono_frac : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ p : Cpt ξ, IsLocalRing (regAt ξ p)) ∧ (∀ p q : Cpt ξ, q.1 ⤳ p.1 → regAt ξ p ≤ regAt ξ q) ∧ (IsCptGen ξ → ∀ (p : Cpt ξ) (a : Ω), ∃ u ∈ regAt ξ p, ∃ v ∈ regAt ξ p, v ≠ 0 ∧ a = u / v) :=
  @PositivityTheory.HtPt.Ma.reg_local

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularAtBaseChangeStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_at_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ (f : T → FractionRing R) (g' : Γ'.G.left), Γ.RegularAt f (F g') → Γ'.RegularAt (fun t => κ (f t)) g' := by
  first | exact @GlobalTheory.CompanionTheory.Relay.regular_at_base_change | exact GlobalTheory.CompanionTheory.Relay.regular_at_base_change | (intros; apply GlobalTheory.CompanionTheory.Relay.regular_at_base_change <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularLocalRingFractionFieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_local_ring_fraction_field : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ∀ p : Cpt ξ, IsFractionRing (regAt ξ p) Ω := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieStalk.isFractionRing_regAt | exact GlobalTheory.CompanionTheory.Ar.LieStalk.isFractionRing_regAt | (intros; apply GlobalTheory.CompanionTheory.Ar.LieStalk.isFractionRing_regAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSurjectiveOpenImmersionStatement
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalk_surjective_open_immersion : ∀ (S X₀ Xg X' : Scheme.{0}) (e : Xg ⟶ X₀) (f : X' ⟶ Xg) (W' : X'.Opens) (jW : W'.toScheme ⟶ S) (jQ : S ⟶ Xg), IsPreimmersion e → IsOpenImmersion jQ → IsIso jW → jW ≫ jQ = W'.ι ≫ f → ∀ x ∈ W', Function.Surjective ((f ≫ e).stalkMap x).hom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.stalkMap_comp_surjective_of_open_part | exact GlobalTheory.CompanionTheory.Ar.Flat.stalkMap_comp_surjective_of_open_part | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.stalkMap_comp_surjective_of_open_part <;> assumption)
end

