import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0190
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0114
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0121
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0118
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicUniformizationDiffUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ContinuousOnValue
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0020
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0191
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteNormLocalBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

namespace GlobalTheory.CompanionTheory.Ar.Br.FinPlace

section Valued

variable {F : Type*} [Field F] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {N : Type*} [NormedField N]

theorem val_lt_one_iff (v : Valuation F Γ) (κ : F →+* N) (h : ∀ a, v a ≤ 1 ↔ ‖κ a‖ ≤ 1) (a : F) :
    v a < 1 ↔ ‖κ a‖ < 1 := by
  by_cases ha : a = 0
  · simp [ha]
  have hv : 0 < v a := zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr ha)
  have hn : 0 < ‖κ a‖ := norm_pos_iff.mpr ((map_ne_zero κ).mpr ha)
  have e := h a⁻¹
  rw [map_inv₀, map_inv₀, norm_inv, inv_le_one₀ hv, inv_le_one₀ hn] at e
  rw [← not_le, ← not_le, e]

theorem norm_le_of_val_le (v : Valuation F Γ) (κ : F →+* N) (h : ∀ a, v a ≤ 1 ↔ ‖κ a‖ ≤ 1) {a b : F} (hb : b ≠ 0)
    (hab : v a ≤ v b) : ‖κ a‖ ≤ ‖κ b‖ := by
  have hv : 0 < v b := zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hb)
  have hn : 0 < ‖κ b‖ := norm_pos_iff.mpr ((map_ne_zero κ).mpr hb)
  have e := (h (a / b)).mp (by rw [map_div₀]; exact div_le_one_of_le₀ hab zero_le)
  rw [map_div₀, norm_div] at e
  exact (div_le_one hn).mp e

theorem norm_eq_of_val_eq (v : Valuation F Γ) (κ : F →+* N) (h : ∀ a, v a ≤ 1 ↔ ‖κ a‖ ≤ 1) {a b : F} (hb : b ≠ 0)
    (hab : v a = v b) : ‖κ a‖ = ‖κ b‖ := by
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab
    exact (Valuation.ne_zero_iff v).mpr hb hab.symm
  exact le_antisymm (norm_le_of_val_le v κ h hb hab.le) (norm_le_of_val_le v κ h ha hab.ge)

end Valued

theorem norm_natCast_lt_one_iff (q : Nat.Primes) (n : ℕ) : ‖(n : ℂ_[q])‖ < 1 ↔ (q : ℕ) ∣ n := by
  have e : ‖(n : ℂ_[q])‖ = ‖(n : ℚ_[q])‖ := by
    have h1 := PadicComplex.norm_extends (q : ℕ) ((n : ℚ_[q]) : PadicAlgCl q)
    have h2 := PadicAlgCl.norm_extends (q : ℕ) (n : ℚ_[q])
    simpa using h1.trans h2
  rw [e]
  exact Padic.norm_natCast_lt_one_iff

theorem prime_eq {F : Type*} [Field F] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ)
    {p q : Nat.Primes} (κ : F →+* ℂ_[p]) (κ₀ : F →+* ℂ_[q]) (h : ∀ a, v a ≤ 1 ↔ ‖κ a‖ ≤ 1)
    (h₀ : ∀ a, v a ≤ 1 ↔ ‖κ₀ a‖ ≤ 1) : p = q := by
  have h1 : ‖κ ((p : ℕ) : F)‖ < 1 := by
    rw [map_natCast, norm_natCast_lt_one_iff]
  have h2 : ‖κ₀ ((p : ℕ) : F)‖ < 1 := (val_lt_one_iff v κ₀ h₀ _).mp ((val_lt_one_iff v κ h _).mpr h1)
  rw [map_natCast, norm_natCast_lt_one_iff] at h2
  exact Subtype.ext (((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp h2).symm)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem hasFinNorm_of_isometry {U : Set (Xo.XF c)} {τ : E →+* ℂ} {φ : FrameFn Xo c} {p : Nat.Primes}
    {κ κ' : c.F →+* ℂ_[p]} {t : ℝ} (g : ℂ_[p] ≃+* ℂ_[p]) (hg : ∀ z, ‖g z‖ = ‖z‖) (hκ : ∀ a, g (κ a) = κ' a)
    (h : HasFinNorm U τ φ p κ t) : HasFinNorm U τ φ p κ' t := by
  have hs : ∀ z, ‖g.symm z‖ = ‖z‖ := fun z => by
    rw [← hg (g.symm z), RingEquiv.apply_symm_apply]
  intro V K _ _ _ _ _ _ j β y v w T tK m m' hj hjβ hF hv hw
  have e := h V K ((g.symm : ℂ_[p] →+* ℂ_[p]).comp j) β y v w T tK m m'
    (fun a => by
      rw [← hj a]
      simp only [RingHom.comp_apply, RingHom.coe_coe, hs])
    (by
      ext a
      have h1 : j (β a) = κ' a := by rw [← hjβ]; rfl
      simp only [RingHom.comp_apply, RingHom.coe_coe, h1, ← hκ, RingEquiv.symm_apply_apply]) hF hv hw
  simpa only [RingHom.comp_apply, RingHom.coe_coe, hs] using e

theorem exists_rho_at (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) [NumberField c.F]
    (hfin : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm U τ φ p κ t)
    (la : HeightOneSpectrum (𝓞 c.F)) :
    ∃ r : ℝ, ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (π : c.F),
      (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation c.F π = WithZero.exp (-1 : ℤ) →
      HasFinNorm U τ φ p κ (r * Real.log ‖κ π‖) := by
  by_cases hex : ∃ (p₀ : Nat.Primes) (κ₀ : c.F →+* ℂ_[p₀]) (π₀ : c.F),
      (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ₀ a‖ ≤ 1) ∧ la.valuation c.F π₀ = WithZero.exp (-1 : ℤ)
  · obtain ⟨p₀, κ₀, π₀, hκ₀, hπ₀⟩ := hex
    obtain ⟨t₀, ht₀⟩ := hfin p₀ κ₀
    have hne : π₀ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ₀
      exact WithZero.exp_ne_zero hπ₀.symm
    have hlt : ‖κ₀ π₀‖ < 1 := (val_lt_one_iff _ κ₀ hκ₀ π₀).mp (by
      rw [hπ₀, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
    have hpos : 0 < ‖κ₀ π₀‖ := norm_pos_iff.mpr ((map_ne_zero κ₀).mpr hne)
    have hlog : Real.log ‖κ₀ π₀‖ ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hpos hlt.ne
    refine ⟨t₀ / Real.log ‖κ₀ π₀‖, fun p κ π hκ hπ => ?_⟩
    have hp : p = p₀ := prime_eq (la.valuation c.F) κ κ₀ hκ hκ₀
    subst hp
    obtain ⟨g, hg, hgκ⟩ := GlobalTheory.T.padic_embeddings_conjugate_of_units c.F p κ₀ κ (fun a => (hκ₀ a).symm.trans (hκ a))
    have e : ‖κ π‖ = ‖κ₀ π₀‖ := by
      rw [norm_eq_of_val_eq _ κ hκ hne (hπ.trans hπ₀.symm), ← hgκ, hg]
    rw [e, div_mul_cancel₀ _ hlog]
    exact hasFinNorm_of_isometry g hg hgκ ht₀
  · exact ⟨0, fun p κ π h1 h2 => (hex ⟨p, κ, π, h1, h2⟩).elim⟩

theorem exists_rho : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c), (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm U τ φ p κ t) → ∃ ρ : HeightOneSpectrum (𝓞 c.F) → ℝ, ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (la : HeightOneSpectrum (𝓞 c.F)) (π : c.F), (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation c.F π = WithZero.exp (-1 : ℤ) → HasFinNorm U τ φ p κ (ρ la * Real.log ‖κ π‖) := by
  intro E _ _ _ H D l Xo c _ U τ φ hfin
  choose ρ hρ using exists_rho_at U τ φ hfin
  exact ⟨ρ, fun p κ la π h1 h2 => hρ la p κ π h1 h2⟩

end GlobalTheory.CompanionTheory.Ar.Br.FinPlace
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricComponentAlgClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br

theorem exists_fieldMap_of_surjective {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X)
    (h : Function.Surjective (Scheme.stalkClosedPointTo ξ).hom) (z : X) (hz : ξ (IsLocalRing.closedPoint Ω) = z) :
    ∃ i : Ω →+* X.residueField z, spMap i ≫ ξ = X.fromSpecResidueField z := by
  subst hz
  let g := X.descResidueField (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ)
  have hsurj : Function.Surjective g.hom := by
    intro a
    obtain ⟨b, hb⟩ := h a
    refine ⟨(X.residue _).hom b, ?_⟩
    have e := congrArg CommRingCat.Hom.hom
      (X.residue_descResidueField (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ))
    exact (congrArg (fun φ => φ b) e).trans hb
  let e : X.residueField (ξ (IsLocalRing.closedPoint Ω)) ≃+* Ω :=
    RingEquiv.ofBijective g.hom ⟨g.hom.injective, hsurj⟩
  refine ⟨e.symm.toRingHom, ?_⟩
  have h1 : Spec.map g ≫ X.fromSpecResidueField (ξ (IsLocalRing.closedPoint Ω)) = ξ :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X ξ
  have h2 : spMap e.symm.toRingHom ≫ Spec.map g = 𝟙 _ := by
    have h3 : g ≫ CommRingCat.ofHom e.symm.toRingHom = 𝟙 _ := by
      ext a
      exact e.symm_apply_apply a
    exact (Spec.map_comp _ _).symm.trans ((congrArg Spec.map h3).trans (Spec.map_id _))
  refine (congrArg (spMap e.symm.toRingHom ≫ ·) h1).symm.trans ?_
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ X.fromSpecResidueField _) h2).trans (Category.id_comp _))

theorem isGeom_of_fnAlgClosed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Formalism.L2.Pj.Comp Xo c) (Z' : CptOver Y (Z : Set (Xo.XF c))), FracBase β → Formalism.L2.Pj.FnAlgClosed Xo c → Z'.IsGeom := by
  intro E _ _ _ H D l Xo c O _ β Y Z Z' _ hc x ⟨f, hf0, hf⟩
  have hsurj : Function.Surjective (Scheme.stalkClosedPointTo Z'.ξ₀).hom := by
    have h := Z'.gen.bij.2
    rw [Scheme.stalkClosedPointTo_comp] at h
    intro a
    obtain ⟨b, hb⟩ := h a
    exact ⟨_, hb⟩
  have hgp : genPt Z'.ξ₀ = Formalism.L2.Pj.genPt Z := by
    have hg := Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)
    have h2 : Formalism.L2.Pj.genPt Z ⤳ genPt Z'.ξ₀ := hg.specializes Z'.genPt_mem
    have h3 : genPt Z'.ξ₀ ⤳ Formalism.L2.Pj.genPt Z := (Z'.closure _).1 hg.mem
    exact (h3.antisymm h2).eq
  obtain ⟨i, hi⟩ := exists_fieldMap_of_surjective Z'.ξ₀ hsurj _ hgp
  have hcomp : i.comp Z'.inc = algebraMap c.F (Formalism.L2.Pj.kap Z) := by
    have h1 : Formalism.L2.Pj.genSp Z ≫ Formalism.L2.Pj.strK = spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) :=
      (Spec.map_preimage _).symm
    have h2 : spMap (i.comp Z'.inc) = spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) := by
      rw [← h1]
      have e : spMap (i.comp Z'.inc) = spMap i ≫ spMap Z'.inc := by
        rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl
      rw [e, ← Z'.over_inc, ← Category.assoc, hi]
      rfl
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
  have hb : IsAlgebraic c.F (algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z) (i x)) := by
    refine ⟨f, hf0, ?_⟩
    have h3 := Polynomial.hom_eval₂ f Z'.inc ((algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).comp i) x
    rw [hf, map_zero] at h3
    rw [Polynomial.aeval_def]
    refine Eq.trans ?_ h3.symm
    have e : algebraMap c.F (Formalism.L2.Pj.Om Z) =
        ((algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).comp i).comp Z'.inc := by
      rw [RingHom.comp_assoc, hcomp]
      exact IsScalarTower.algebraMap_eq _ _ _
    rw [e]
    rfl
  obtain ⟨k, hk⟩ := hc Z _ hb
  refine ⟨k, i.injective ?_⟩
  have h2 : algebraMap c.F (Formalism.L2.Pj.kap Z) k = i x := by
    apply (algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).injective
    rw [← hk, ← IsScalarTower.algebraMap_apply]
  rw [← h2, ← hcomp]
  rfl

end GlobalTheory.CompanionTheory.Ar.Br
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedBaseChangeIffFibers
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Approx

private theorem eq_of_sp_complex_pts {K : Type} [Field K] (a b : ↥(Sp K)) : a = b := by
  revert a b
  change ∀ a b : PrimeSpectrum K, a = b
  intro a b
  exact PrimeSpectrum.ext ((Ideal.eq_bot_of_prime a.asIdeal).trans (Ideal.eq_bot_of_prime b.asIdeal).symm)

private theorem nonempty_sp (K : Type) [Field K] : Nonempty ↥(Sp K) := by
  change Nonempty (PrimeSpectrum K)
  infer_instance

theorem connectedSpace_pullback_of_fieldHom {k K K' : Type} [CommRing k] [Field K] [Field K']
    {X : Scheme.{0}} (p : X ⟶ Sp k) (f : k →+* K) (j : K →+* K')
    (h : ConnectedSpace ↥(pullback p (spMap (j.comp f)))) :
    ConnectedSpace ↥(pullback p (spMap f)) := by
  rw [spMap_comp] at h
  let e := pullbackLeftPullbackSndIso p (spMap f) (spMap j)
  let g : pullback p (spMap j ≫ spMap f) ⟶ pullback p (spMap f) :=
    e.inv ≫ pullback.fst (pullback.snd p (spMap f)) (spMap j)
  refine Function.Surjective.connectedSpace (f := ⇑g) ?_ g.continuous
  intro z
  obtain ⟨y'⟩ := nonempty_sp K'
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pullback.snd p (spMap f)) (g := spMap j) z y' (eq_of_sp_complex_pts _ _)
  refine ⟨e.hom w, ?_⟩
  have h2 : e.hom ≫ g = pullback.fst (pullback.snd p (spMap f)) (spMap j) := by
    simp [g, e]
  rw [← hw, ← h2]
  rfl

private theorem connectedSpace_of_iso {A B : Scheme.{0}} (e : A ≅ B) [ConnectedSpace A] :
    ConnectedSpace B := by
  refine Function.Surjective.connectedSpace (f := ⇑e.hom) (fun b => ⟨e.inv b, ?_⟩) e.hom.continuous
  rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
  rfl

theorem geometricallyConnected_pullback_snd_iff {X S T : Scheme.{0}} (p : X ⟶ S) (g : T ⟶ S) :
    GeometricallyConnected (pullback.snd p g) ↔
      ∀ (K : Type) [Field K] (y : Spec (CommRingCat.of K) ⟶ T),
        ConnectedSpace ↥(pullback p (y ≫ g)) := by
  rw [geometricallyConnected_iff]
  constructor
  · intro H K _ y
    haveI : ConnectedSpace ↥(pullback (pullback.snd p g) y) :=
      H y (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
    exact connectedSpace_of_iso (pullbackLeftPullbackSndIso p g y)
  · intro H K _ y Z fst snd hpb
    haveI := H K y
    exact connectedSpace_of_iso (hpb.isoPullback ≪≫ pullbackLeftPullbackSndIso p g y).symm

theorem geometricallyConnected_pullback_snd_spMap_iff {k R : Type} [CommRing k] [CommRing R]
    {X : Scheme.{0}} (p : X ⟶ Sp k) (a : k →+* R) :
    GeometricallyConnected (pullback.snd p (spMap a)) ↔
      ∀ (K : Type) [Field K] (φ : R →+* K), ConnectedSpace ↥(pullback p (spMap (φ.comp a))) := by
  rw [geometricallyConnected_pullback_snd_iff]
  constructor
  · intro H K _ φ
    have := H K (spMap φ)
    rwa [← spMap_comp] at this
  · intro H K _ y
    obtain ⟨φ, rfl⟩ : ∃ φ : R →+* K, spMap φ = y :=
      ⟨(Spec.preimage (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))).hom, Spec.map_preimage _⟩
    rw [← spMap_comp]
    exact H K φ

theorem exists_field_amalgam {F K₁ K₂ : Type} [Field F] [Field K₁] [Field K₂]
    (a : F →+* K₁) (b : F →+* K₂) :
    ∃ (L : Type) (_ : Field L) (i : K₁ →+* L) (j : K₂ →+* L), i.comp a = j.comp b := by
  letI := a.toAlgebra
  letI := b.toAlgebra
  haveI : Nontrivial (K₁ ⊗[F] K₂) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K₁ ⊗[F] K₂)
  letI := Ideal.Quotient.field m
  refine ⟨K₁ ⊗[F] K₂ ⧸ m, inferInstance,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeRight.toRingHom, ?_⟩
  ext x
  simp only [RingHom.comp_apply]
  congr 1
  exact (Algebra.TensorProduct.algebraMap_apply x).symm.trans (Algebra.TensorProduct.algebraMap_apply' x)

theorem exists_residueField_lift {k K : Type} [CommRing k] [Field K] (f : k →+* K)
    (x : PrimeSpectrum k) (hx : x.asIdeal = RingHom.ker f) :
    ∃ ψ : x.asIdeal.ResidueField →+* K, ψ.comp (algebraMap k x.asIdeal.ResidueField) = f := by
  have h2 : x.asIdeal.primeCompl ≤ Submonoid.comap f (IsUnit.submonoid K) := by
    intro r hr
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
    refine isUnit_iff_ne_zero.mpr fun h0 => Ideal.mem_primeCompl_iff.mp hr ?_
    rw [hx]
    exact RingHom.mem_ker.mpr h0
  refine ⟨Ideal.ResidueField.lift x.asIdeal f hx.le h2, ?_⟩
  ext r
  exact Ideal.ResidueField.lift_algebraMap x.asIdeal f hx.le h2 r

theorem geometricallyConnected_pullback_snd_spMap_iff_residueField :
    ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (X : Scheme.{0}) (p : X ⟶ Sp k),
      GeometricallyConnected (pullback.snd p (spMap (algebraMap k V))) ↔
        ∀ x ∈ Set.range (PrimeSpectrum.comap (algebraMap k V)),
          GeometricallyConnected (pullback.snd p (spMap (algebraMap k x.asIdeal.ResidueField))) := by
  intro k V _ _ _ X p
  rw [geometricallyConnected_pullback_snd_spMap_iff]
  constructor
  · rintro H x ⟨q, rfl⟩
    rw [geometricallyConnected_pullback_snd_spMap_iff]
    intro K _ ψ
    have hker : (PrimeSpectrum.comap (algebraMap k V) q).asIdeal =
        RingHom.ker ((algebraMap V q.asIdeal.ResidueField).comp (algebraMap k V)) := by
      rw [← RingHom.comap_ker, Ideal.ker_algebraMap_residueField]
      rfl
    obtain ⟨ψ', hψ'⟩ := exists_residueField_lift _ _ hker
    obtain ⟨L, hL, i, j', hij⟩ := exists_field_amalgam ψ ψ'
    apply connectedSpace_pullback_of_fieldHom p _ i
    have e : i.comp (ψ.comp (algebraMap k (PrimeSpectrum.comap (algebraMap k V) q).asIdeal.ResidueField)) =
        (j'.comp (algebraMap V q.asIdeal.ResidueField)).comp (algebraMap k V) := by
      rw [← RingHom.comp_assoc, hij, RingHom.comp_assoc, hψ', RingHom.comp_assoc]
    rw [e]
    exact H L _
  · intro H K _ φ
    haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
    let q : PrimeSpectrum V := ⟨RingHom.ker φ, inferInstance⟩
    have hx : (PrimeSpectrum.comap (algebraMap k V) q).asIdeal =
        RingHom.ker (φ.comp (algebraMap k V)) := by
      rw [← RingHom.comap_ker]
      rfl
    obtain ⟨ψ, hψ⟩ := exists_residueField_lift _ _ hx
    have := (geometricallyConnected_pullback_snd_spMap_iff p _).mp (H _ ⟨q, rfl⟩) K ψ
    rwa [hψ] at this

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyIntegralOfClosedFibre
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem exists_comp_residue_eq (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (K : Type) [Field K] (φ : A →+* K) :
    ∃ ψ : IsLocalRing.ResidueField A →+* K, ψ.comp (IsLocalRing.residue A) = φ := by
  have hm : (RingHom.ker φ).IsMaximal := by
    have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
    exact IsArtinianRing.isMaximal_of_isPrime _
  have he : RingHom.ker φ = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hm
  have H : ∀ a ∈ IsLocalRing.maximalIdeal A, φ a = 0 := fun a ha => by
    rw [← he] at ha
    exact (RingHom.mem_ker).1 ha
  exact ⟨Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) φ H,
    RingHom.ext fun a => Ideal.Quotient.lift_mk (IsLocalRing.maximalIdeal A) φ H⟩

theorem geometricallyIntegral_of_closedFibre (A : Type) [CommRing A] [IsLocalRing A]
    [IsArtinianRing A] (X : Scheme.{0}) (p : X ⟶ Sp A)
    (h : GeometricallyIntegral (pullback.snd p (spMap (IsLocalRing.residue A)))) :
    GeometricallyIntegral p := by
  constructor
  intro K _ y Z fst snd hpb
  obtain ⟨ψ, hψ⟩ := exists_comp_residue_eq A K (Spec.preimage y).hom
  have hy : Spec.map (CommRingCat.ofHom ψ) ≫ spMap (IsLocalRing.residue A) = y := by
    rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ, CommRingCat.ofHom_hom]
    exact Spec.map_preimage y
  have hw : fst ≫ p = (snd ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ spMap (IsLocalRing.residue A) := by
    rw [Category.assoc, hy]
    exact hpb.w
  have hbig : IsPullback (pullback.lift fst (snd ≫ Spec.map (CommRingCat.ofHom ψ)) hw ≫
      pullback.fst p (spMap (IsLocalRing.residue A))) snd p
      (Spec.map (CommRingCat.ofHom ψ) ≫ spMap (IsLocalRing.residue A)) := by
    rw [pullback.lift_fst, hy]
    exact hpb
  have hsq : IsPullback (pullback.lift fst (snd ≫ Spec.map (CommRingCat.ofHom ψ)) hw) snd
      (pullback.snd p (spMap (IsLocalRing.residue A))) (Spec.map (CommRingCat.ofHom ψ)) :=
    IsPullback.of_right hbig (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  exact h.geometrically_isIntegral (Spec.map (CommRingCat.ofHom ψ)) _ snd hsq

theorem isIso_appTop_of_artinian : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (X : Scheme.{0}) (p : X ⟶ Sp A), Flat p → IsProper p →
    GeometricallyIntegral (pullback.snd p (spMap (IsLocalRing.residue A))) → IsIso p.appTop := by
  intro A _ _ _ X p hflat hprop hgi
  haveI : IsAffine (Sp A) := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  haveI : IsLocallyNoetherian (Sp A) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of A)))
  haveI := hflat
  haveI := hprop
  haveI : GeometricallyIntegral p := geometricallyIntegral_of_closedFibre A X p hgi
  exact GlobalTheory.ProperFunctions.isIso_appTop_of_isAffine p

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFirstStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_descent_first : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag), Function.Injective β → IsCovOf 𝔐₀ 𝔐 i h → FlagsOver Fl₀ Fl i → ∃ j : 𝔐₀.Li →+ 𝔐.Li, (∀ (a : Ω₀) e, j (a • e) = i a • j e) ∧ (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) ∧ (∀ s a, j (Fl₀.b s a) = Fl.b s a) ∧ (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐₀.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐₀.M.GramAt 𝔐₀.t.PP.L (z ≫ h) b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => j (b k)) Γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChgLie.lie_of_cover | exact GlobalTheory.CompanionTheory.Ar.ChgLie.lie_of_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.ChgLie.lie_of_cover <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentLabelFrame
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem not_inFibre_centre {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (z : Spec (CommRingCat.of ℂ) ⟶ X) (h : genPt ξ ⤳ centre z)
    (r : ℕ) (hr : r.Prime) : ¬ InFibre ξ r ⟨centre z, h⟩ := by
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne_zero
  have hu : IsUnit ((r : X.presheaf.stalk (centre z))) := by
    have h1 : IsUnit ((Scheme.stalkClosedPointTo z).hom (r : X.presheaf.stalk (centre z))) := by
      have e : (Scheme.stalkClosedPointTo z).hom (r : X.presheaf.stalk (centre z)) = (r : ℂ) := map_natCast _ r
      exact e ▸ hr0.isUnit
    exact isUnit_of_map_unit (Scheme.stalkClosedPointTo z).hom _ h1
  obtain ⟨u, hu⟩ := hu
  have hg : genMap ξ ⟨centre z, h⟩ (u : X.presheaf.stalk (centre z)) = (r : Ω) := by
    rw [hu, map_natCast]
  refine not_not.2 ⟨Nat.cast_ne_zero.2 hr.ne_zero, ⟨_, hg⟩, ⟨((u⁻¹ : (X.presheaf.stalk (centre z))ˣ) : X.presheaf.stalk (centre z)), ?_⟩⟩
  rw [← hg]
  exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])

theorem frame_valAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (lab : CMType H ⊕ CMType H) (r : ℕ) (s : Fin r → 𝔐.Li) (h : genPt 𝔐.ξ ⤳ centre z), (𝔐.V lab).IsFrameAt s ⟨centre z, h⟩ → ∀ i, ∃ v : epsAt z ⟶ 𝔐.t.G, 𝔐.M.ValAt z (s i) v := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 z lab r s h hs i
  have hinj : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S Ω K J y 𝔐 hinj
    ⟨centre z, h⟩ (fun r hr => not_inFibre_centre 𝔐.ξ z h r hr)
  have hmem : s i ∈ 𝔐.V lab ⟨centre z, h⟩ := by
    rw [hs.2]
    exact Submodule.subset_span ⟨i, rfl⟩
  rw [h1 lab] at hmem
  have hlat : s i ∈ 𝔐.M.lat ⟨centre z, h⟩ := by
    rw [h3]
    exact (le_iSup (fun s' => 𝔐.dR s' ⟨centre z, h⟩) lab) hmem
  exact (𝔐.M.exists_valAt_iff z (s i)).2 ⟨h, hlat⟩

end GlobalTheory.CompanionTheory.Ar.HodgeVal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicUniformizationDiffUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_uniformization_diff_unique : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), SmoothOfRelativeDimension g A.hom → ConnectedSpace A.left → ∀ (v : epsR ℂ ⟶ A), ¬ IsTangent v → ∀ (w w' : Fin g → ℂ), u.IsDiff w v → u.IsDiff w' v → w = w' := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.DualFibre.eq_of_isDiff_of_not_isTangent | exact GlobalTheory.CompanionTheory.Ggeo.DualFibre.eq_of_isDiff_of_not_isTangent | (intros; apply GlobalTheory.CompanionTheory.Ggeo.DualFibre.eq_of_isDiff_of_not_isTangent <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootLinesUnramifiedPrimesStatement
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_lines_unramified_primes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) [Fintype (CMType H)] (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω), Fl.RootLines M.xdeg e → ∀ p : ℕ, p.Prime → p ∉ S → ¬ (p : ℤ) ∣ NumberField.discr E → (∀ z : Y.X, (p : Y.X.residueField z) = 0 → FibPF Y.t z) → Nonempty (DRTie M D.p p H) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.HcptTie.drTie_of_hodgeCpt | exact GlobalTheory.CompanionTheory.Ar.Conj.HcptTie.drTie_of_hodgeCpt | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.HcptTie.drTie_of_hodgeCpt <;> assumption)
end

