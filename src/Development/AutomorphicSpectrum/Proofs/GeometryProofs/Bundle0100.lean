import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightLowerBoundChartNorm
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0094
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeEigenDecompositionLocal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeExtendScalars
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0089
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0057
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0095
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointComponentLocalRingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_component_local_ring : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ q : Cpt ξ, IsLocalRing (regAt ξ q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isLocalRing_regAt | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isLocalRing_regAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.isLocalRing_regAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightLowerBoundChartNormStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_lower_bound_chart_norm : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y → ∀ (a : K → ℤ) (u : Ω) (q m : ℕ), 0 < q → 0 < m → (m : Ω) * u ^ q ∈ chartLatNm y a q → ∀ (φ : ((Σ k, ι k) → ℂ) → ℝ) (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), ∀ val : L, val ≠ 0 → HasVal y a u w val → (Module.finrank ℚ L : ℝ)⁻¹ * (∑ σ : L →+* ℂ, (φ (fun p => σ (w p)) - Real.log ‖σ val‖)) - Real.log m / q ≤ ptHt (fun k => (a k : ℝ)) φ L w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.SecLow.height_ge_of_section | exact GlobalTheory.CompanionTheory.Ar.Ht.SecLow.height_ge_of_section | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.SecLow.height_ge_of_section <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentTwistFrameCompat
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TwistInterior

theorem genPt_specializes_of_injective {Ω : Type} [Field Ω] {R : CommRingCat.{0}} [IsDomain R]
    (φ : R ⟶ CommRingCat.of Ω) (hφ : Function.Injective φ.hom) (q : Spec R) :
    genPt (Spec.map φ) ⤳ q := by
  refine (PrimeSpectrum.le_iff_specializes (genPt (Spec.map φ) : PrimeSpectrum R) q).1 ?_
  intro a ha
  have hm : φ.hom a ∈ IsLocalRing.maximalIdeal Ω := ha
  have h0 : φ.hom a = 0 := by
    by_contra hne
    exact hm (isUnit_iff_ne_zero.2 hne)
  have : a = 0 := hφ (h0.trans (map_zero φ.hom).symm)
  rw [this]
  exact zero_mem _

theorem lift_transfer {X X' W W' V : Scheme.{0}} {Ω : Type} [Field Ω] {R : Type} [CommRing R]
    (e : X' ≅ X) (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (hξ : ξ' ≫ e.hom = ξ)
    (hgen : IsCptGen ξ') (hall : ∀ q : X', genPt ξ' ⤳ q) (hdom : ∀ p : X', IsDomain (X'.presheaf.stalk p))
    (sW : W ⟶ Sp R) (hproj : IsProjOver sW)
    (f : X ⟶ W) (f' : X' ⟶ W') (j : V ⟶ W) (j' : V ⟶ W') [Mono j'] (Ψ : V ≅ V) (x x' : Sp Ω ⟶ V)
    (hx : x' ≫ Ψ.inv = x) (hf : ξ ≫ f = x ≫ j) (hf' : ξ' ≫ f' = x' ≫ j') (p : X')
    (hu : ∃ u' : Spec (X'.presheaf.stalk p) ⟶ V, u' ≫ j' = X'.fromSpecStalk p ≫ f') :
    ∃ u : Spec (X.presheaf.stalk (e.hom p)) ⟶ V, u ≫ j = X.fromSpecStalk (e.hom p) ≫ f := by
  obtain ⟨u', hu'⟩ := hu
  haveI := hdom p
  have h' : ξ' (IsLocalRing.closedPoint Ω) ⤳ p := hall p
  let φ : X'.presheaf.stalk p ⟶ CommRingCat.of Ω := X'.presheaf.stalkSpecializes h' ≫ Scheme.stalkClosedPointTo ξ'
  let ξp : Sp Ω ⟶ Spec (X'.presheaf.stalk p) := Spec.map φ
  have hξp : ξp ≫ X'.fromSpecStalk p = ξ' := by
    simp only [ξp, φ]
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ'
  have hgp : ∀ q, genPt ξp ⤳ q := genPt_specializes_of_injective φ (hgen.inj ⟨p, hall p⟩)
  have hxu : ξp ≫ u' = x' := by
    rw [← cancel_mono j', Category.assoc, hu', ← Category.assoc, hξp, hf']
  have heq : u' ≫ Ψ.inv ≫ j = X'.fromSpecStalk p ≫ e.hom ≫ f := by
    refine GlobalTheory.T.eq_of_eq_generic_projective R (Spec (X'.presheaf.stalk p)) W sW Ω ξp _ _ hproj hgp ?_
    have h1 : ξp ≫ u' ≫ Ψ.inv ≫ j = x ≫ j := by rw [reassoc_of% hxu, reassoc_of% hx]
    have h2 : ξp ≫ X'.fromSpecStalk p ≫ e.hom ≫ f = x ≫ j := by rw [reassoc_of% hξp, reassoc_of% hξ, hf]
    rw [h1, h2]
  haveI : IsIso (e.hom.stalkMap p) := inferInstance
  refine ⟨inv (Spec.map (e.hom.stalkMap p)) ≫ u' ≫ Ψ.inv, ?_⟩
  rw [Category.assoc, Category.assoc, heq, ← Scheme.SpecMap_stalkMap_fromSpecStalk_assoc, IsIso.inv_hom_id_assoc]

end GlobalTheory.CompanionTheory.Ar.TwistInterior

namespace GlobalTheory.CompanionTheory.Ar.TwistInterior

theorem interior_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∀ z : Sp ℂ ⟶ A'.X, A'.Interior z ↔ A.Interior (z ≫ e.hom) := by
  intro E _ _ _ H D l Xo c O O' _ _ β β' Y Y' g Φ n S Ω _ K _ J _ y A A' e x x' hβ hβ' hΦ hξ hf hf' hfst hsnd _ _ _ z
  have hΦ' : Φ.inv ≫ Xo.s = Xo.s := (Iso.inv_comp_eq Φ).2 hΦ.symm
  let ΦF : Xo.XF c ≅ Xo.XF c :=
    { hom := pullback.lift (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Φ.hom)
        (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
        (by rw [Category.assoc, hΦ, pullback.condition])
      inv := pullback.lift (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Φ.inv)
        (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
        (by rw [Category.assoc, hΦ', pullback.condition])
      hom_inv_id := pullback.hom_ext
        (by simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Iso.hom_inv_id, Category.comp_id,
          Category.id_comp])
        (by simp only [Category.assoc, pullback.lift_snd, Category.id_comp])
      inv_hom_id := pullback.hom_ext
        (by simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Iso.inv_hom_id, Category.comp_id,
          Category.id_comp])
        (by simp only [Category.assoc, pullback.lift_snd, Category.id_comp]) }
  have hxx : x ≫ ΦF.hom = x' := by
    apply pullback.hom_ext
    · simp only [ΦF, Category.assoc, pullback.lift_fst, hfst]
    · simp only [ΦF, Category.assoc, pullback.lift_snd, hsnd]
  obtain ⟨hjY, hA⟩ := GlobalTheory.T.hodge_cpt_interior_iff E H D l Xo c O β Y S Ω K J y A (z ≫ e.hom) hβ
  obtain ⟨hjY', hA'⟩ := GlobalTheory.T.hodge_cpt_interior_iff E H D l Xo c O' β' Y' S Ω K J y A' z hβ'
  have hc : centre (z ≫ e.hom) = e.hom (centre z) := rfl
  rw [hA, hA', hc]
  constructor
  · exact lift_transfer e A.ξ A'.ξ hξ A'.tie.gen A'.all (fun p => (A'.normal p).1) Y.s Y.proj A.f A'.f Y.j Y'.j
      ΦF x x' (by rw [← hxx, Category.assoc, Iso.hom_inv_id, Category.comp_id]) hf hf' (centre z)
  · intro hu
    have key := lift_transfer e.symm A'.ξ A.ξ (by rw [← hξ, Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id])
      A.tie.gen A.all (fun p => (A.normal p).1) Y'.s Y'.proj A'.f A.f Y'.j Y.j ΦF.symm x' x
      (by rw [Iso.symm_inv, hxx]) hf' hf (e.hom (centre z)) hu
    have hp : e.symm.hom (e.hom (centre z)) = centre z := by
      rw [Iso.symm_hom, ← Scheme.Hom.comp_apply, e.hom_inv_id]
      rfl
    rwa [hp] at key

end GlobalTheory.CompanionTheory.Ar.TwistInterior
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeEigenDecompositionLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_lattice_eigen_decomposition_local : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs : Type) [Field Ω] [CharZero Ω] [AddCommGroup Vs] [Module Ω Vs]
    [FiniteDimensional Ω Vs] (ρ : 𝓞 E →+* Module.End Ω Vs) (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (bar : 𝓞 E ≃+* 𝓞 E) (R' : Subring Ω) [IsLocalRing R'] (g p q : ℕ) (ℓ : Fin g → Vs)
    (t : Fin (p + q) → Vs × Module.Dual Ω Vs) (HL : Submodule R' (Vs × Module.Dual Ω Vs)) (σ σ' : E →+* Ω),
    (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a f, ρH a (0, f) = (0, f ∘ₗ ρ (bar a))) →
    (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) →
    (∀ e, σ e ∈ R') → (∀ e, σ' e ∈ R') →
    LinearIndependent Ω ℓ → Submodule.span Ω (Set.range ℓ) = ⊤ → HodgeAt ρH HL ℓ t →
    Module.finrank Ω (HT.eigSp ρ σ) = p → Module.finrank Ω (HT.eigSp ρ σ') = q →
    ∃ (b₁ : Fin p → Vs) (b₂ : Fin q → Vs) (u : Fin (p + q) → Vs × Module.Dual Ω Vs)
      (A : Matrix (Fin (p + q)) (Fin (p + q)) R'),
      LinearIndependent Ω b₁ ∧ Submodule.span R' (Set.range b₁) = HT.eigSub ρ σ (Submodule.span R' (Set.range ℓ)) ∧
      LinearIndependent Ω b₂ ∧ Submodule.span R' (Set.range b₂) = HT.eigSub ρ σ' (Submodule.span R' (Set.range ℓ)) ∧
      IsAdapted ρH σ b₁ b₂ u ∧ (∀ i, u i ∈ HL) ∧ IsUnit A.det ∧
      ∀ i, HT.eigProj ρH σ (t i) = ∑ j, (A i j : Ω) • u j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.Frames.adapted_frames | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.Frames.adapted_frames | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.Frames.adapted_frames <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeExtendScalarsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_lattice_extend_scalars : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs]
    (ρ : 𝓞 E →+* Module.End Ω Vs) (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs)) (bar : 𝓞 E ≃+* 𝓞 E)
    (R R' : Subring Ω) (hR : R ≤ R') (g N : ℕ) (ℓ : Fin g → Vs) (t : Fin N → Vs × Module.Dual Ω Vs)
    (HLx : Submodule R (Vs × Module.Dual Ω Vs)) (HLy : Submodule R' (Vs × Module.Dual Ω Vs))
    (C A : Type) [Field C] [CommRing A] [Algebra A C] (ψ : R' →+* C),
    (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a f, ρH a (0, f) = (0, f ∘ₗ ρ (bar a))) →
    LinearIndependent Ω ℓ → Submodule.span Ω (Set.range ℓ) = ⊤ →
    HodgeAt ρH HLx ℓ t → HodgeAt ρH HLy ℓ t →
    (∀ r : R, ψ ⟨r, hR r.2⟩ ∈ (algebraMap A C).range) →
    ∃ (ρC : 𝓞 E →+* Module.End C (Fin g → C))
      (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
      (ev : HLy →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C))
      (HV : Submodule A ((Fin g → C) × Module.Dual C (Fin g → C))),
      (∀ a y, (ρHC a y).1 = ρC a y.1) ∧ (∀ a f, ρHC a (0, f) = (0, f ∘ₗ ρC (bar a))) ∧
      Tied ℓ ψ ρ ρC ∧ IsEval ℓ ψ ρH ρHC HLy ev ∧
      HV.map ((LinearMap.fst C (Fin g → C) (Module.Dual C (Fin g → C))).restrictScalars A) = stdLat A C g ∧
      (∀ f : Module.Dual C (Fin g → C), ((0 : Fin g → C), f) ∈ HV ↔
        ∀ e ∈ stdLat A C g, f e ∈ (algebraMap A C).range) ∧
      ∀ ht : ∀ i, t i ∈ HLy, HT.IsFreeOn ρHC HV (fun i => ev ⟨t i, ht i⟩) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalExists.exists_eval | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalExists.exists_eval | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.EvalExists.exists_eval <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeGermEigenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_lattice_germ_eigen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)) (𝓗 : HodgeLat M.lat ρ H.bar r) (σ : E →+* Ω) (u : Fin r → (Fin d → Ω) × Module.Dual Ω (Fin d → Ω)), IsCptGen ξ → S.Gives 𝓗 → (∀ (p : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ p) → LinearIndependent Ω u → Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ → ∀ p : Cpt ξ, ∃ (x : Fin r → (Fin d → X.presheaf.stalk p.1) × (Fin d → X.presheaf.stalk p.1)) (A : Matrix (Fin r) (Fin r) Ω), IsHBasis (S.g p).B x ∧ (𝓗.quot σ).IsFrameAt (fun j => ∑ l, A j l • u l) p ∧ ∀ j, HT.eigProj 𝓗.ρH σ (toH S p (x j)) = ∑ l, A j l • u l := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegZ.Frame.exists_basis_frame | exact GlobalTheory.CompanionTheory.Ar.Flat.DegZ.Frame.exists_basis_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegZ.Frame.exists_basis_frame <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeStableUnderActionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_lattice_stable_under_action : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs]
    (ρ : 𝓞 E →+* Module.End Ω Vs) (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (R : Subring Ω) (g N : ℕ) (ℓ : Fin g → Vs) (t : Fin N → Vs × Module.Dual Ω Vs)
    (HL : Submodule R (Vs × Module.Dual Ω Vs)),
    (∀ a y, (ρH a y).1 = ρ a y.1) → HodgeAt ρH HL ℓ t →
    (∀ i, t i ∈ HL) ∧ (∀ a, ∀ h ∈ HL, ρH a h ∈ HL) ∧ ∀ a i, ρ a (ℓ i) ∈ Submodule.span R (Set.range ℓ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.hodgeAt_stable | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.hodgeAt_stable | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.hodgeAt_stable <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicFamilyConjugate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem top_le_spMap_comp_iff {X : Scheme.{0}} (σ : ℂ →+* ℂ) (x : Sp ℂ ⟶ X) (U : X.Opens) :
    ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U ↔ ⊤ ≤ x ⁻¹ᵁ U := by
  have hsub : ∀ a b : Sp ℂ, a = b := fun a b => Subsingleton.elim (α := PrimeSpectrum ℂ) a b
  constructor
  · intro h p _
    have hq : x.base ((spMap σ).base p) ∈ U := h (show p ∈ (⊤ : (Sp ℂ).Opens) from trivial)
    rwa [hsub ((spMap σ).base p) p] at hq
  · intro h p _
    exact h (show (spMap σ).base p ∈ (⊤ : (Sp ℂ).Opens) from trivial)

private theorem gammaSpecIso_appLE_spMap_apply (z : Γ(Sp ℂ, ⊤)) (σ : ℂ →+* ℂ)
    (e : (⊤ : (Sp ℂ).Opens) ≤ (spMap σ) ⁻¹ᵁ ⊤) :
    (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom)
      ((CommRingCat.Hom.hom (Scheme.Hom.appLE (spMap σ) ⊤ ⊤ e)) z) =
    σ ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) z) := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ)
  exact congrArg (fun φ => CommRingCat.Hom.hom φ z) h

theorem valAt'_spMap_comp {X : Scheme.{0}} (σ : ℂ →+* ℂ) (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (spMap σ ≫ x) U f = σ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' x U f) := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt'
  by_cases hx : ⊤ ≤ x ⁻¹ᵁ U
  · have hc : ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U := (top_le_spMap_comp_iff σ x U).2 hx
    rw [dif_pos hc, dif_pos hx]
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt
    rw [← Scheme.Hom.appLE_comp_appLE (spMap σ) x U ⊤ ⊤ hx (by simp)]
    rw [CommRingCat.hom_comp, RingHom.comp_apply]
    exact gammaSpecIso_appLE_spMap_apply _ σ _
  · have hc : ¬ ⊤ ≤ (spMap σ ≫ x) ⁻¹ᵁ U := fun h => hx ((top_le_spMap_comp_iff σ x U).1 h)
    rw [dif_neg hc, dif_neg hx, map_zero]

private theorem differentiableOn_conj_comp_star {m : ℕ} {g : (Fin m → ℂ) → ℂ} {S : Set (Fin m → ℂ)}
    (hg : DifferentiableOn ℂ g S) :
    DifferentiableOn ℂ (fun b => starRingEnd ℂ (g (star b))) (star ⁻¹' S) := by
  intro b hb
  obtain ⟨L, hL⟩ := hg (star b) hb
  have h1 : HasFDerivWithinAt (star : (Fin m → ℂ) → (Fin m → ℂ))
      ((starL' ℝ : (Fin m → ℂ) ≃L[ℝ] (Fin m → ℂ)) : (Fin m → ℂ) →L[ℝ] (Fin m → ℂ)) (star ⁻¹' S) b :=
    ((starL' ℝ : (Fin m → ℂ) ≃L[ℝ] (Fin m → ℂ)) : (Fin m → ℂ) →L[ℝ] (Fin m → ℂ)).hasFDerivWithinAt
  have h2 : HasFDerivWithinAt g (L.restrictScalars ℝ) S (star b) := hL.restrictScalars ℝ
  have h3 := h2.comp b h1 (fun y hy => hy)
  have hR := ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasFDerivWithinAt b h3
  let L' : (Fin m → ℂ) →L[ℂ] ℂ :=
    { toFun := fun v => star (L (star v))
      map_add' := fun v w => by simp [star_add, map_add]
      map_smul' := fun c v => by simp [star_smul, map_smul]
      cont := continuous_star.comp (L.continuous.comp continuous_star) }
  exact ⟨L', HasFDerivWithinAt.of_restrictScalars (𝕜 := ℝ) hR (by ext v; rfl)⟩

theorem isHolTo_conj (X : Scheme.{0}) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (hy : IsHolTo B y) :
    IsHolTo (star ⁻¹' B) (fun b => spMap (starRingEnd ℂ) ≫ y (star b)) := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo at hy ⊢
  intro U f
  obtain ⟨ho, hd⟩ := hy U f
  have hset : {b | b ∈ star ⁻¹' B ∧
        ⊤ ≤ (TopologicalSpace.Opens.map (spMap (starRingEnd ℂ) ≫ y (star b)).base).obj U}
      = star ⁻¹' {b | b ∈ B ∧ ⊤ ≤ (TopologicalSpace.Opens.map (y b).base).obj U} := by
    ext b
    exact and_congr_right fun _ => top_le_spMap_comp_iff (starRingEnd ℂ) (y (star b)) U
  rw [hset]
  refine ⟨ho.preimage continuous_star, ?_⟩
  refine (differentiableOn_conj_comp_star hd).congr ?_
  intro b _
  exact valAt'_spMap_comp (starRingEnd ℂ) (y (star b)) U f

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionHiddenFirstStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_first : ∀ (R S : Type) [CommRing R] [CommRing S] (f : R →+* S) (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B B₂ : Germ.FB R d O) (C C₂ : Germ.FB S d O) (φ ψ : Germ.Pt R 1 d) (lam : Germ.PS R 2 d), IsMapOf f B C → IsMapOf f B₂ C₂ → IsIso B B₂ φ ψ lam → IsIso C C₂ (fun i => MvPowerSeries.map f (φ i)) (fun i => MvPowerSeries.map f (ψ i)) (MvPowerSeries.map f lam) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isIso_map | exact GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isIso_map | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isIso_map <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionHiddenSecondStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_second : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (R S : Type) [CommRing R] [Nontrivial R] [CommRing S] (f : R →+* S) (d r : ℕ) (B : Germ.FB R d (𝓞 E)) (B₂ : Germ.FB S d (𝓞 E)) (x : Fin r → (Fin d → R) × (Fin d → R)), IsMapOf f B B₂ → IsHBasis B x → IsHBasis B₂ (fun j => vmap f (x j)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isHBasis_map | exact GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isHBasis_map | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegZ.isHBasis_map <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiLinearCombinationDetStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iota_multi_linear_combination_det : ∀ (Ω Vs : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] (p : ℕ) (P : Matrix (Fin p) (Fin p) Ω) (v : Fin p → Vs),
    exteriorPower.ιMulti Ω p (fun i => ∑ k, P i k • v k) = P.det • exteriorPower.ιMulti Ω p v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.ιMulti_matrix_transform | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.ιMulti_matrix_transform | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.ιMulti_matrix_transform <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarOfBlockAlgebraicStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isArithVar_of_block_algebraic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι' k) → Ω) (d : ℕ), IsBlockMap κ v → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → IsArithVar (mCoordIdeal (y ∘ v)) d → (∀ t ∈ blockFnField y, IsAlgebraic (blockFnField (y ∘ v)) t) → IsArithVar (mCoordIdeal y) d := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.isArithVar_of_isAlgebraic_image | exact GlobalTheory.CompanionTheory.Ar.Cmp.isArithVar_of_isAlgebraic_image | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.isArithVar_of_isAlgebraic_image <;> assumption)
end

