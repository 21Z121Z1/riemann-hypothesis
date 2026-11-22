import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLinearLiftOfAdditiveFamily
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0142
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0131
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0070
import Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfB
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0189
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0184
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0002
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.DifferentIdealLogSumRootDiscriminantStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0004
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0005
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0006
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0191
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0009
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0026
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExists
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicEndomorphismFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Flat.ActFam

theorem comp_mul_hom {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) (a b : X ⟶ M) :
    (u ≫ a) * (u ≫ b) = u ≫ (a * b) := by
  rw [Hom.mul_def, Hom.mul_def, comp_lift_assoc]

theorem exists_action_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (ρ : ℝ) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M (Metric.ball 0 ρ) ψ), 0 < ρ → ∃ B : (Fin n → ℂ) → (𝓞 E →+* Module.End ℂ (Fin g → ℂ)), (∀ c x, DifferentiableOn ℂ (fun b => B b c x) (Metric.ball 0 ρ)) ∧ ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ c x, e.ex b (B b c x) = e.ex b x ≫ t.act.act c := by
  intro E _ _ _ H R _ t g n M ρ ψ e hρ
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ρ := Metric.mem_ball_self hρ
  have hlift := fun c : 𝓞 E => exists_linear_lift_of_additive_family R t.G g n M (Metric.ball 0 ρ) ψ e g
    (Metric.ball 0 ρ) (fun b z => e.ex b z ≫ t.act.act c) Metric.isOpen_ball subset_rfl
    (fun b hb z w => by
      haveI := t.act.hom c
      simp only [e.add b hb z w]
      exact (IsMonHom.monoidHom (t.act.act c) _).map_mul _ _)
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp e.hol (t.act.act c).left)
  choose h hd hs using hlift
  have hex : ∀ c, ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ z, e.ex b (h c b z) = e.ex b z ≫ t.act.act c :=
    fun c b hb z => (hs c b hb).1 z
  have huq : ∀ c, ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ l : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      (∀ z, e.ex b (l z) = e.ex b z ≫ t.act.act c) → l = h c b :=
    fun c b hb l hl => (hs c b hb).2.1 l hl
  have hring : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∃ f : 𝓞 E →+* Module.End ℂ (Fin g → ℂ), ∀ c, f c = h c b := by
    intro b hb
    refine ⟨RingHom.mk' ⟨⟨fun c => h c b, ?_⟩, ?_⟩ ?_, fun c => rfl⟩
    · refine (huq 1 b hb LinearMap.id fun z => ?_).symm
      rw [t.act.one]
      exact (Category.comp_id _).symm
    · intro c c'
      refine (huq (c * c') b hb (h c b * h c' b) fun z => ?_).symm
      rw [Module.End.mul_apply, hex c b hb, hex c' b hb, mul_comm c c', t.act.mul, Category.assoc]
    · intro c c'
      refine (huq (c + c') b hb (h c b + h c' b) fun z => ?_).symm
      rw [LinearMap.add_apply, e.add b hb, hex c b hb, hex c' b hb, t.act.add, comp_mul_hom]
  have hall : ∀ b, ∃ f : 𝓞 E →+* Module.End ℂ (Fin g → ℂ),
      b ∈ Metric.ball (0 : Fin n → ℂ) ρ → ∀ c, f c = h c b := by
    intro b
    by_cases hb : b ∈ Metric.ball (0 : Fin n → ℂ) ρ
    · obtain ⟨f, hf⟩ := hring b hb
      exact ⟨f, fun _ => hf⟩
    · obtain ⟨f, -⟩ := hring 0 h0
      exact ⟨f, fun hb' => absurd hb' hb⟩
  choose B hB using hall
  refine ⟨B, fun c x => ?_, fun b hb c x => ?_⟩
  · refine (hd c x).congr fun b hb => ?_
    simp only [hB b hb c]
  · rw [hB b hb c]
    exact hex c b hb x

end GlobalTheory.CompanionTheory.Ar.Flat.ActFam
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IrreducibleComponentClopen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br

theorem exists_ringEquiv_of_genPt_eq {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X)
    (ξ' : Sp Ω' ⟶ X) (h : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom)
    (h' : Function.Bijective (Scheme.stalkClosedPointTo ξ').hom) (he : genPt ξ = genPt ξ') :
    ∃ e : Ω ≃+* Ω', spMap e.toRingHom ≫ ξ = ξ' := by
  haveI : IsIso (Scheme.stalkClosedPointTo ξ) := (ConcreteCategory.isIso_iff_bijective _).2 h
  haveI : IsIso (Scheme.stalkClosedPointTo ξ') := (ConcreteCategory.isIso_iff_bijective _).2 h'
  have hi : Inseparable (ξ (IsLocalRing.closedPoint Ω)) (ξ' (IsLocalRing.closedPoint Ω')) := .of_eq he
  let i : CommRingCat.of Ω ≅ CommRingCat.of Ω' :=
    (asIso (Scheme.stalkClosedPointTo ξ)).symm ≪≫ X.presheaf.stalkCongr hi ≪≫
      asIso (Scheme.stalkClosedPointTo ξ')
  refine ⟨i.commRingCatIsoToRingEquiv, ?_⟩
  have e1 : Scheme.stalkClosedPointTo ξ ≫ i.hom =
      (X.presheaf.stalkCongr hi).hom ≫ Scheme.stalkClosedPointTo ξ' := by simp [i]
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have h2 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ'
  have h3 : Spec.map (X.presheaf.stalkCongr hi).hom ≫ X.fromSpecStalk _ = X.fromSpecStalk _ :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hi.symm.specializes
  show Spec.map i.hom ≫ ξ = ξ'
  conv_lhs => rw [← h1]
  conv_rhs => rw [← h2]
  rw [← Category.assoc, ← Spec.map_comp, e1, Spec.map_comp, Category.assoc, h3]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem bijective_stalk_of_cptOver {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {U : Set (Xo.XF c)}
    (Z : CptOver Y U) (hβ : FracBase β) : Function.Bijective (Scheme.stalkClosedPointTo Z.ξ₀).hom := by
  obtain ⟨h1, h2⟩ := j_flat_preimmersion Y hβ.1 hβ.2.2
  have hb := stalkMap_bijective_of_flat_preimmersion Y.j (Z.ξ₀ (IsLocalRing.closedPoint Z.Ω))
  have hg := Z.gen.bij
  rw [Scheme.stalkClosedPointTo_comp] at hg
  exact (Function.Bijective.of_comp_iff _ hb).1 hg

theorem genPt_eq_of_cptOver {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}
    {Y : Model Xo c β} {Y' : Model Xo c β'} {U : Set (Xo.XF c)} (Z : CptOver Y U) (Z' : CptOver Y' U) :
    genPt Z.ξ₀ = genPt Z'.ξ₀ :=
  (((Z.closure _).1 Z'.genPt_mem).antisymm ((Z'.closure _).1 Z.genPt_mem)).eq

theorem cptOver_any : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)), U ∈ irreducibleComponents (Xo.XF c) → IsClopen U ∧ (∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), FracBase β → Nonempty (CptOver Y U)) ∧ ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Y' : Model Xo c β') (Z : CptOver Y U) (Z' : CptOver Y' U), FracBase β → FracBase β' → Z.IsGeom → Z'.IsGeom := by
  intro E _ _ _ H D l Xo c U hU
  refine ⟨Formalism.L2.Pj.CompSplitPfB.cspB_isClopen (Formalism.L2.Pj.CompSplitPfD.cspD_comp_disj Xo c) ⟨U, hU⟩,
    fun O _ β Y hβ => nonempty_cptOver_of_fraction hβ.1 hβ.2.2 Y U hU, ?_⟩
  intro O _ β Y O' _ β' Y' Z Z' hβ hβ' hg
  obtain ⟨e, he⟩ := exists_ringEquiv_of_genPt_eq Z.ξ₀ Z'.ξ₀ (bijective_stalk_of_cptOver Z hβ)
    (bijective_stalk_of_cptOver Z' hβ') (genPt_eq_of_cptOver Z Z')
  have h2 : spMap e.toRingHom ≫ spMap Z.inc = spMap Z'.inc := by
    rw [← Z.over_inc, ← Z'.over_inc, ← he, Category.assoc]
  have h4 : CommRingCat.ofHom Z.inc ≫ CommRingCat.ofHom e.toRingHom = CommRingCat.ofHom Z'.inc :=
    Spec.map_injective (by rw [Spec.map_comp]; exact h2)
  have h3 : e.toRingHom.comp Z.inc = Z'.inc := congrArg CommRingCat.Hom.hom h4
  rintro x ⟨f, hf, hx⟩
  have h5 : f.eval₂ Z.inc (e.symm x) = 0 := by
    apply e.injective
    have := Polynomial.hom_eval₂ f Z.inc e.toRingHom (e.symm x)
    rw [h3] at this
    simpa [hx] using this
  obtain ⟨a, ha⟩ := hg (e.symm x) ⟨f, hf, h5⟩
  refine ⟨a, ?_⟩
  rw [← h3]
  simp [ha]

end GlobalTheory.CompanionTheory.Ar.Br
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPrincipalBaseChangeIffStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrincipal_base_change_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L L' : Type) [Field L] [Field L'] (e : L →+* L') (t : SAB H (Sp L)) (t' : SAB H (Sp L')) (_ : SABMap t' t (spMap e)), IsPrincipal t' ↔ IsPrincipal t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.isPrincipal_iff_of_sabMap_field | exact GlobalTheory.CompanionTheory.Ar.isPrincipal_iff_of_sabMap_field | (intros; apply GlobalTheory.CompanionTheory.Ar.isPrincipal_iff_of_sabMap_field <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPrincipalDim
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SabModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isPrincipal_dim {K : Type} [Field K] {t : SAB H (Sp K)} (_h : IsPrincipal t) :
    ∃ d, SmoothOfRelativeDimension d t.G.hom := by
  letI := t.grp
  haveI hs : IsSemiAbelian t.G := t.semi
  haveI : Smooth t.G.hom := hs.smooth
  haveI : GeometricallyConnected t.G.hom := hs.geomConnected
  have hc := t.G.hom.isConnected_preimage_singleton (IsLocalRing.closedPoint K)
  have hu : t.G.hom ⁻¹' {IsLocalRing.closedPoint K} = Set.univ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  haveI : PreconnectedSpace t.G.left := ⟨by rw [← hu]; exact hc.isPreconnected⟩
  exact exists_dim_of_preconnected t.G.hom hc.nonempty.some

def pol {K : Type} [Field K] (t : SAB H (Sp K)) (h : IsPrincipal t) : Out.PolAV (Sp K) where
  A := t.G
  isAb := ⟨inferInstance, t.semi.smooth, h.1, t.semi.geomConnected⟩
  g := (isPrincipal_dim h).choose
  smoothDim := (isPrincipal_dim h).choose_spec
  L := t.PP.L
  isLB := t.PP.isLB
  rigid := ⟨t.PP.rig, t.PP.rigGen⟩
  sym := fun _ => by
    obtain ⟨-, ws, gs', -⟩ := t.sym
    exact ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩
  ample := h.2.1
  ktriv := h.2.2

end GlobalTheory.CompanionTheory.Ar.SabModel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KroneckerCharacterPeriodFormula
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.TopLL

theorem shift {k : Type} [Field k] [NumberField k] (N N' : LogNorms k) (C : ∀ p : Nat.Primes, (k →+* ℂ_[p]) → ℝ)
    (hinf : N.inf = N'.inf) (hfin : ∀ p κ, N.fin p κ = N'.fin p κ + C p κ)
    (hC : {p : Nat.Primes | ∃ κ, C p κ ≠ 0}.Finite) (h : N'.IsAdelic) :
    N.IsAdelic ∧ N.deg = N'.deg - (∑ᶠ p, ∑ κ, C p κ) / Module.finrank ℚ k := by
  constructor
  · refine (h.union hC).subset ?_
    rintro p ⟨κ, hκ⟩
    by_cases hc : C p κ = 0
    · left
      exact ⟨κ, by rw [hfin, hc, add_zero] at hκ; exact hκ⟩
    · right
      exact ⟨κ, hc⟩
  · have h1 : Function.HasFiniteSupport (fun p => N'.finSum p) := by
      refine h.subset ?_
      intro p hp
      obtain ⟨κ, _, hκ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
      exact ⟨κ, hκ⟩
    have h2 : Function.HasFiniteSupport (fun p => ∑ κ, C p κ) := by
      refine hC.subset ?_
      intro p hp
      obtain ⟨κ, _, hκ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
      exact ⟨κ, hκ⟩
    have hs : ∑ᶠ p, N.finSum p = ∑ᶠ p, N'.finSum p + ∑ᶠ p, ∑ κ, C p κ := by
      rw [← finsum_add_distrib h1 h2]
      refine finsum_congr fun p => ?_
      simp only [LogNorms.finSum, hfin, Finset.sum_add_distrib]
    have hk : (Module.finrank ℚ k : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
    simp only [LogNorms.deg, hs, hinf]
    field_simp
    ring

theorem corr {E k : Type} [Field E] [NumberField E] [Field k] [NumberField k] (f : E →+* k) (d : ℕ) (hd : d ≠ 0) :
    {p : Nat.Primes | ∃ κ : k →+* ℂ_[p], logIdeal ((κ.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) -
      Real.log ‖((d : ℕ) : ℂ_[p])‖ ≠ 0}.Finite ∧
    ∑ᶠ p : Nat.Primes, ∑ κ : k →+* ℂ_[p], (logIdeal ((κ.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) -
      Real.log ‖((d : ℕ) : ℂ_[p])‖) = Module.finrank ℚ k * (Real.log d - Real.log (rootDiscr E)) := by
  have hdk : (d : k) ≠ 0 := by exact_mod_cast hd
  have hI := GlobalTheory.T.logIdeal_support_finite E (differentIdeal ℤ (𝓞 E)) differentIdeal_ne_bot
  have hX := GlobalTheory.T.log_norms_of_nonzero_adelic k (d : k) hdk
  have hP := GlobalTheory.T.product_formula_log_norms k (d : k) hdk
  have hD := GlobalTheory.T.different_ideal_log_sum_root_discriminant E
  have hcast : ∀ (p : Nat.Primes) (κ : k →+* ℂ_[p]), κ (d : k) = ((d : ℕ) : ℂ_[p]) := fun _ κ => map_natCast κ d
  constructor
  · refine (hI.union hX).subset ?_
    rintro p ⟨κ, hκ⟩
    by_cases h0 : logIdeal ((κ.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) = 0
    · right
      refine ⟨κ, ?_⟩
      simp only [LogNorms.ofElt, hcast]
      intro h
      exact hκ (by rw [h0, h, sub_zero])
    · left
      exact ⟨_, h0⟩
  · set A : Nat.Primes → ℝ := fun p => ∑ κ : k →+* ℂ_[p],
      logIdeal ((κ.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) with hAdef
    set B : Nat.Primes → ℝ := fun p => (LogNorms.ofElt (d : k)).finSum p with hBdef
    have hAB : ∀ p : Nat.Primes, ∑ κ : k →+* ℂ_[p], (logIdeal ((κ.comp f).comp (algebraMap (𝓞 E) E))
        (differentIdeal ℤ (𝓞 E)) - Real.log ‖((d : ℕ) : ℂ_[p])‖) = A p - B p := by
      intro p
      simp only [hAdef, hBdef, LogNorms.finSum, LogNorms.ofElt, hcast, Finset.sum_sub_distrib]
    have hA : Function.HasFiniteSupport A := by
      refine hI.subset ?_
      intro p hp
      obtain ⟨κ, _, hκ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
      exact ⟨_, hκ⟩
    have hB : Function.HasFiniteSupport B := hP.1
    have hF : ∀ p : Nat.Primes, (Module.finrank ℚ E : ℝ) * A p = (Module.finrank ℚ k : ℝ) *
        ∑ j : E →+* ℂ_[p], logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) := fun p =>
      GlobalTheory.T.sum_embeddings_base_change E k ℂ_[p] f (fun j => logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)))
    have hE : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
    have hsA : ∑ᶠ p, A p = -(Module.finrank ℚ k : ℝ) * Real.log (rootDiscr E) := by
      have h1 : (Module.finrank ℚ E : ℝ) * ∑ᶠ p, A p =
          (Module.finrank ℚ k : ℝ) * (-(Module.finrank ℚ E : ℝ) * Real.log (rootDiscr E)) := by
        rw [mul_finsum, finsum_congr hF, ← mul_finsum, hD.2]
      apply mul_left_cancel₀ hE
      rw [h1]
      ring
    have hsB : ∑ᶠ p, B p = -(Module.finrank ℚ k : ℝ) * Real.log d := by
      have h2 := hP.2
      have h3 : ∑ s : k →+* ℂ, Real.log ‖s (d : k)‖ = (Module.finrank ℚ k : ℝ) * Real.log d := by
        simp only [map_natCast, Complex.norm_natCast, Finset.sum_const, Finset.card_univ, Embeddings.card,
          nsmul_eq_mul]
      rw [h3] at h2
      simp only [hBdef]
      linarith
    rw [finsum_congr hAB, finsum_sub_distrib hA hB, hsA, hsB]
    ring

theorem degree_frames : FlatDegree → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ))
    (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (U : Set (Xo.XF c)) (τ : E →+* ℂ)
    (φ : FrameFn Xo c) [NumberField c.F] (N : LogNorms c.F) [NeZero H.d] (χ : DirichletCharacter ℂ H.d),
    GlobalTheory.IsKroneckerChar χ → IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → IsFlatGen U τ φ FU i →
    (∀ s, HasInfNorm U τ φ s (N.inf s)) → (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), HasFinNorm U τ φ p κ (N.fin p κ)) →
    N.IsAdelic ∧ N.deg = ((D.p : ℝ) - D.q) / 2 * (GlobalTheory.CM.logOm E χ).re := by
  intro hFD E _ _ _ H D l Xo c g ty FU i U τ φ _ N _ χ hχ hty hrt hflat hinf hfin
  let f : E →+* c.F := (τ.codRestrict c.F.toSubfield (c.conj τ) :)
  have hf : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), κ.comp (tauIn c τ) = (κ.comp f).comp (algebraMap (𝓞 E) E) :=
    fun _ _ => rfl
  let C : ∀ p : Nat.Primes, (c.F →+* ℂ_[p]) → ℝ := fun p κ => (D.q : ℝ) *
    (logIdeal ((κ.comp f).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((H.d : ℕ) : ℂ_[p])‖)
  let N' : LogNorms c.F := ⟨N.inf, fun p κ => N.fin p κ - C p κ⟩
  have hN' : HasNorms U τ φ N' := by
    refine ⟨hinf, fun p κ => ?_⟩
    have e : N'.fin p κ + D.q * (logIdeal (κ.comp (tauIn c τ)) (differentIdeal ℤ (𝓞 E)) -
        Real.log ‖((H.d : ℕ) : ℂ_[p])‖) = N.fin p κ := by
      rw [hf]
      simp only [N', C]
      ring
    rw [e]
    exact hfin p κ
  obtain ⟨hA', hdeg'⟩ := hFD E H D l Xo c g ty FU i U τ φ N' χ hχ hty hrt hflat hN'
  have hd : H.d ≠ 0 := NeZero.ne _
  obtain ⟨hc1, hc2⟩ := corr f H.d hd
  have hCfin : {p : Nat.Primes | ∃ κ, C p κ ≠ 0}.Finite := by
    refine hc1.subset ?_
    rintro p ⟨κ, hκ⟩
    exact ⟨κ, right_ne_zero_of_mul hκ⟩
  obtain ⟨hA, hdeg⟩ := shift N N' C rfl (fun p κ => by simp [N']) hCfin hA'
  refine ⟨hA, ?_⟩
  have hsum : ∑ᶠ p, ∑ κ, C p κ = (D.q : ℝ) * (Module.finrank ℚ c.F * (Real.log H.d - Real.log (rootDiscr E))) := by
    rw [← hc2, mul_finsum]
    refine finsum_congr fun p => ?_
    simp only [C, Finset.mul_sum]
  have hF : (Module.finrank ℚ c.F : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hsq : 2 * Real.log (Real.sqrt H.d) = Real.log H.d := by
    rw [Real.log_sqrt (Nat.cast_nonneg _)]
    ring
  rw [hdeg, hdeg', hsum, hsq]
  field_simp
  ring

end GlobalTheory.CompanionTheory.Ar.Fl.TopLL
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelConstantsExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_constants_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Tor.Level H) (c : Coeff l)
    (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀]
    [CharZero Ω] [Algebra Ω₀ Ω] (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X')
    (cst : c.F →+* Ω₀) (V V' : Type) [AddCommGroup V] [Module Ω₀ V] [AddCommGroup V'] [Module Ω V']
    (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V') (ρ : 𝓞 E →+* Module.End Ω₀ V) (ρ' : 𝓞 E →+* Module.End Ω V')
    (L : CMType H ⊕ CMType H → Lat ξ V) (j : V →+ V') (r : CMType H ⊕ CMType H → ℕ)
    (b : ∀ s, Fin (r s) → V'),
    IsCptGen ξ → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) →
    M.IsActOf t.act.act ρ → M'.IsActOf t'.act.act ρ' →
    (∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q)) →
    (∀ q : Cpt ξ', (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q) → IsIntegrallyClosed (regAt ξ' q)) →
    (∀ s (q : Cpt ξ), (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → L s q = M.eigLat ρ (cst.comp (labelEmb c s)) q) →
    M'.lat = M.lat.pull ξ' f j →
    (∀ s, ∀ e ∈ eigSp ρ (cst.comp (labelEmb c s)),
      j e ∈ eigSp ρ' (((algebraMap Ω₀ Ω).comp cst).comp (labelEmb c s))) →
    (∀ s, ((L s).pull ξ' f j).IsFlagVBOn Set.univ (b s)) →
    ∀ s, (M'.eigLat ρ' (((algebraMap Ω₀ Ω).comp cst).comp (labelEmb c s))).IsFlagVBOn
      {q | ∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q} (b s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagStep.eigLat_isFlagVBOn_of_pull_char0 | exact GlobalTheory.CompanionTheory.Ar.FlagStep.eigLat_isFlagVBOn_of_pull_char0 | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagStep.eigLat_isFlagVBOn_of_pull_char0 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieNormSqBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem lieNormSq_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R R' : Type) [CommRing R] [CommRing R'] (ω : R) (ω' : R') (C : Ell H R ω) (C' : Ell H R' ω') (f : R →+* R') (φ : C'.P.A.left ⟶ C.P.A.left) (σ : R' →+* ℂ) (r : ℝ), EllMap C' C f φ → (IsLieNormSq C.P C.v (σ.comp f) r ↔ IsLieNormSq C'.P C'.v σ r) := by
  intro E _ _ _ H R R' _ _ ω ω' C C' f φ σ r h
  exact (GlobalTheory.CM.EllComp.isLieNormSq_iff h.2.1 h.2.2.1 σ r).symm

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NefDegreeScaleInvariant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.nef_degree_scale_invariant : PB.Inputs → ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X) (L : Lat ξ Ω) (a a' : K → ℤ) (e e' u : Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → u ≠ 0 → L.IsDegOn Set.univ y a e → (L.scale u).IsDegOn Set.univ y a' e' → NefOnFibres (mCoordIdeal y) a → NefOnFibres (mCoordIdeal y) a' := by
  first | exact @LevelTowerAlt.nef_fibres_scaled_lattice | exact LevelTowerAlt.nef_fibres_scaled_lattice
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NoetherianIntegralClosedCover
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

open TopologicalSpace in

theorem isIntegral_subscheme_vanishingIdeal {X : Scheme.{0}} (Z : Closeds X)
    (h : IsIrreducible (Z : Set X)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  haveI : IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  have hr : Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = (Z : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  haveI : IrreducibleSpace (Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι) :=
    Subtype.irreducibleSpace (by rw [hr]; exact h)
  let f := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph
  haveI : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
    Function.Surjective.irreducibleSpace f.symm.continuous f.symm.surjective
  exact isIntegral_of_irreducibleSpace_of_isReduced _

open TopologicalSpace in

theorem exists_integral_closed_cover :
    ∀ (X : Scheme.{0}) [IsNoetherian X], ∃ (n : ℕ) (Z : Fin n → Scheme.{0}) (j : ∀ i, Z i ⟶ X),
      (∀ i, IsIntegral (Z i) ∧ IsClosedImmersion (j i)) ∧ ∀ x : X, ∃ i, x ∈ Set.range (j i) := by
  intro X _
  haveI : Finite (irreducibleComponents X) :=
    (finite_irreducibleComponents_of_isNoetherian (X := X)).to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (irreducibleComponents X)
  let C : Fin n → Closeds X := fun i =>
    ⟨(e.symm i).1, isClosed_of_mem_irreducibleComponents _ (e.symm i).2⟩
  refine ⟨n, fun i => (Scheme.IdealSheafData.vanishingIdeal (C i)).subscheme,
    fun i => (Scheme.IdealSheafData.vanishingIdeal (C i)).subschemeι,
    fun i => ⟨GlobalTheory.CompanionTheory.Ar.Approx.isIntegral_subscheme_vanishingIdeal (C i) (e.symm i).2.1, inferInstance⟩,
    fun x => ⟨e ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩⟩
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  show x ∈ (e.symm (e _)).1
  rw [Equiv.symm_apply_apply]
  exact mem_irreducibleComponent

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistAutHoldsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.TwistAut_holds : GlobalTheory.CompanionTheory.Ar.TwistAut := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TwistAutProof.twistAut | exact GlobalTheory.CompanionTheory.Ar.TwistAutProof.twistAut | (intros; apply GlobalTheory.CompanionTheory.Ar.TwistAutProof.twistAut <;> assumption)
end

