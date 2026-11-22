import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0080
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0294
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0082
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0073
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0188
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0298
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0299
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0081
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0296
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0255
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0019

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptGoodReductionDegree
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenFlag

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.FlagBun

section Model

theorem coordTie_along {o : Type} [CommRing o] {X : Scheme.{0}} {Ω : Type} [Field Ω] [Algebra o Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ κ' : Type} {x : κ → Ω} (h : CoordTie o ξ x) (e : κ' → κ)
    (he : Function.Surjective e) (x' : κ' → Ω) (hx : ∀ c, x' c = x (e c)) : CoordTie o ξ x' := by
  obtain rfl : x' = fun c => x (e c) := funext hx
  have hc : ∀ c p, InChart ξ (fun c => x (e c)) c p ↔ InChart ξ x (e c) p := fun c p =>
    and_congr Iff.rfl (he.forall (p := fun c' => x c' / x (e c) ∈ regAt ξ p)).symm
  refine ⟨h.gen, fun p => ?_, fun c h0 => ?_, fun c h0 a => ?_⟩
  · obtain ⟨c, hp⟩ := h.cover p
    obtain ⟨c, rfl⟩ := he c
    exact ⟨c, (hc c p).2 hp⟩
  · obtain ⟨U, hU, hq⟩ := h.affine (e c) h0
    exact ⟨U, hU, fun q => (hq q).trans (exists_congr fun _ => (hc c _).symm)⟩
  · have : (Set.range fun j => x (e j) / x (e c)) = Set.range fun j => x j / x (e c) :=
      he.range_comp fun j => x j / x (e c)
    simpa only [hc, this] using h.ring (e c) h0 a

theorem closure_genField (Ω : Type) [Field Ω] {I : Type} :
    Subfield.closure (Set.range (algebraMap Ω (FractionRing (MvPolynomial I Ω))) ∪
      {a | ∃ l l' : Option I, a = (l.elim 1 fun q => algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q)) /
        (l'.elim 1 fun q => algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q))}) = ⊤ := by
  set F := Subfield.closure (Set.range (algebraMap Ω (FractionRing (MvPolynomial I Ω))) ∪
      {a | ∃ l l' : Option I, a = (l.elim 1 fun q => algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q)) /
        (l'.elim 1 fun q => algebraMap (MvPolynomial I Ω) _ (MvPolynomial.X q))}) with hF
  have hp : ∀ p : MvPolynomial I Ω, algebraMap _ (FractionRing (MvPolynomial I Ω)) p ∈ F := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      refine Subfield.subset_closure (Or.inl ⟨a, ?_⟩)
      rw [IsScalarTower.algebraMap_apply Ω (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))]
      rfl
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp (Subfield.subset_closure (Or.inr ⟨some i, none, ?_⟩))
      simp
  refine eq_top_iff.2 fun a _ => ?_
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial I Ω) a
  exact div_mem (hp p) (hp q)

end Model

theorem exists_genericFlag : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (y₀ : Sp Ω ⟶ Xo.XF c) (d : ℕ), A.ξ ≫ A.f = y₀ ≫ Y.j → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S) → (∀ p ∈ S, HT.HTFree A p) → (∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ A.R p)) → A.IsCover d → ∃ (Ω' : Type) (_ : Field Ω') (_ : CharZero Ω') (i : Ω →+* Ω') (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω') (𝔐 : HodgeCpt Y S y') (g : 𝔐.X ⟶ A.X) (b : ∀ s, Fin (labelRk D s) → 𝔐.Li) (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module 𝔐.Ω₀ Li₀) (M₀ : LieModel Y.t.G 𝔐.ξ₀ Li₀) (j : Li₀ →+ 𝔐.Li) (V₀ : CMType H ⊕ CMType H → Submodule 𝔐.Ω₀ Li₀), GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ A.ξ g i ∧ 𝔐.f = g ≫ A.f ∧ 𝔐.R = A.R ∧ (∀ p ∈ S, HT.HTFree 𝔐 p) ∧ (∀ s, Submodule.span Ω' (Set.range (b s)) = 𝔐.Vgen s) ∧ (∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap 𝔐.fn) ≫ (M₀.pt e).left) ∧ (∀ s e, e ∈ V₀ s ↔ j e ∈ 𝔐.Vgen s) ∧ (letI := 𝔐.fn.toAlgebra; IsGenericFlag (Ω' := Ω') j V₀ b d) := by
  intro hW E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y A y₀ d hy hS hHT hζ hcov
  classical
  haveI : Finite (GenIx (labelRk D)) := by unfold GenIx; infer_instance
  let Ω' := GenField Ω (labelRk D)
  let i : Ω →+* Ω' := algebraMap Ω Ω'
  haveI : CharZero Ω' := charZero_of_injective_algebraMap (algebraMap Ω Ω').injective

  let x : ((k : K) → J k) → Ω := fun c' => ∏ k, y ⟨k, c' k⟩
  let M₁ : PModel ℤ x :=
    { X := A.X, ξ := A.ξ, s := specZIsTerminal.from _, hover := specZIsTerminal.hom_ext _ _, all := A.all, tie := A.tie }
  let w : Option (GenIx (labelRk D)) → Ω' :=
    fun o => o.elim 1 fun q => algebraMap (MvPolynomial (GenIx (labelRk D)) Ω) Ω' (MvPolynomial.X q)
  obtain ⟨M₂, f₂, hd₂⟩ := GlobalTheory.T.exists_join_model_dominates ℤ Ω _ x M₁ Ω' i _ w (fun a => by simp)
    ⟨none, one_ne_zero⟩ (closure_genField Ω)
  obtain ⟨κ₃, _, y₃, M₃, f₃, hd₃, hN, -, -⟩ := GlobalTheory.T.exists_normal_dominating_model ℤ Ω' _ _ M₂ Ω'
  letI : Fintype κ₃ := Fintype.ofFinite κ₃
  let y' : (Σ _ : Unit, κ₃) → Ω' := fun q => y₃ q.2
  have htie : CoordTie ℤ M₃.ξ (fun c' : (k : Unit) → κ₃ => ∏ k, y' ⟨k, c' k⟩) :=
    coordTie_along M₃.tie (fun c' => c' ()) (fun a => ⟨fun _ => a, rfl⟩) _ fun c' => by simp [y']
  have hd₃' : M₃.ξ ≫ f₃ = M₂.ξ := by
    have h := hd₃
    unfold GlobalTheory.CompanionTheory.Ar.Dominates at h
    rw [h, show algebraMap Ω' Ω' = RingHom.id Ω' from rfl, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have hdh : GlobalTheory.CompanionTheory.Ar.Dominates M₃.ξ A.ξ (f₃ ≫ f₂) i := by
    show M₃.ξ ≫ f₃ ≫ f₂ = _
    rw [← Category.assoc, hd₃']
    exact hd₂
  have hnormal : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₃.X := (GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω' M₃.ξ M₃.tie.gen M₃.all).2.1 hN

  obtain ⟨A', e, j₁, m, he, hf, hm, hcst, hR, hext, hpt, hHT', hV⟩ := GlobalTheory.T.hodge_cpt_field_extension E H D l Xo c _ _ Y S Ω Ω' i K Unit
    J (fun _ => κ₃) y y' A y₀ M₃.X M₃.ξ (f₃ ≫ f₂) hy hS (fun p hp => (hHT p hp).2) M₃.all
    (by convert htie using 1 <;> first | exact Subsingleton.elim _ _ | skip) hnormal hdh
  have hd' : GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ (e.hom ≫ f₃ ≫ f₂) i := by
    show A'.ξ ≫ e.hom ≫ f₃ ≫ f₂ = _
    rw [← Category.assoc, he]
    exact hdh
  have hf' : A'.f = (e.hom ≫ f₃ ≫ f₂) ≫ A.f := hf.trans (Category.assoc _ _ _).symm
  have hfn : GlobalTheory.CompanionTheory.Ar.Dominates A'.ξ A.ξ₀ A'.f (i.comp A.fn) := by
    have h : A.ξ ≫ A.f = Spec.map (CommRingCat.ofHom A.fn) ≫ A.ξ₀ := A.fn_over
    have h' : A'.ξ ≫ e.hom ≫ f₃ ≫ f₂ = Spec.map (CommRingCat.ofHom i) ≫ A.ξ := hd'
    show A'.ξ ≫ A'.f = Spec.map (CommRingCat.ofHom (i.comp A.fn)) ≫ A.ξ₀
    have e1 : A'.ξ ≫ A'.f = (A'.ξ ≫ e.hom ≫ f₃ ≫ f₂) ≫ A.f :=
      (congrArg (A'.ξ ≫ ·) hf').trans (Category.assoc _ _ _).symm
    have e2 : Spec.map (CommRingCat.ofHom (i.comp A.fn)) =
        Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom A.fn) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
    rw [e1, h', Category.assoc, h, e2, Category.assoc]
  let 𝔐 : HodgeCpt Y S y' :=
    { A' with Ω₀ := A.Ω₀, fld₀ := A.fld₀, ξ₀ := A.ξ₀, gen₀ := A.gen₀, fn := i.comp A.fn, fn_over := hfn }
  have hy' : 𝔐.ξ ≫ 𝔐.f = (spMap i ≫ y₀) ≫ Y.j := by
    show A'.ξ ≫ A'.f = _
    have h' := hd'
    unfold GlobalTheory.CompanionTheory.Ar.Dominates at h'
    rw [hf', ← Category.assoc, h', Category.assoc, hy, Category.assoc]

  obtain ⟨cst₀, y₁, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_constants_generic_point E H D l Xo c Y S Ω' Unit (fun _ => κ₃) y' 𝔐 (spMap i ≫ y₀) hy'
  obtain ⟨Li₀, _, _, M₀, j, V₀, cb, hj, hsm, hV₀, hcb, hli, hspan⟩ := GlobalTheory.T.constants_compatible_generic E H D l Xo c Y S Ω' Unit
    (fun _ => κ₃) y' 𝔐 (spMap i ≫ y₀) cst₀ y₁ hy' h₁ h₂ h₃
  have hfin := GlobalTheory.T.finrank_adjoin_vars_field 𝔐.Ω₀ Ω A.fn (GenIx (labelRk D)) d hcov.1 hcov.2
  obtain ⟨hsp, hgen⟩ := GlobalTheory.T.generic_flag_field_change 𝔐.Ω₀ Ω A.fn _ (labelRk D) d hcov.1 hfin Li₀ 𝔐.Li j V₀ cb hcb hsm hli
  refine ⟨Ω', inferInstance, inferInstance, i, Unit, inferInstance, fun _ => κ₃, inferInstance, y', 𝔐,
    e.hom ≫ f₃ ≫ f₂, _, Li₀, _, _, M₀, j, V₀, hd', hf', hR, fun p hp => ⟨?_, hHT' p hp⟩,
    fun s => (hsp s).trans (hspan s), hj, hV₀, hgen⟩
  exact GlobalTheory.T.hodge_comp_field_extension hW E H D l Xo c Y S Ω Ω' i K Unit J (fun _ => κ₃) y y' A 𝔐 (e.hom ≫ f₃ ≫ f₂) m j₁ y₀ p hp hd' hf' hR
    hext hpt hy (hζ p hp) (hHT p hp).1

end GlobalTheory.CompanionTheory.Ar.GenFlag
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsIsoAppOfIsAbelianScheme
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem isAbelianScheme_pullback {S S' : Scheme.{0}} (A : Over S) [GrpObj A]
    (hA : IsAbelianScheme A) (f : S' ⟶ S) : IsAbelianScheme ((Over.pullback f).obj A) :=
  { comm := by have := hA.comm; infer_instance
    smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
    proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
    geomConnected := by
      have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }

theorem isIso_appTop_restrict {S : Scheme.{0}} (A : Over S) [GrpObj A]
    (hA : IsAbelianScheme A) (V : S.Opens) [IsAffine V.toScheme] :
    IsIso (A.hom ∣_ V).appTop := by
  let R : Type := Γ(V.toScheme, ⊤)
  let e : V.toScheme ≅ Sp R := V.toScheme.isoSpec
  let f : Sp R ⟶ S := e.inv ≫ V.ι
  have hf : e.hom ≫ f = V.ι := by simp [f]
  obtain ⟨S₀, B, _, φ, -, hfin, hB, hpb⟩ :=
    GlobalTheory.T.abelianScheme_spreads_out_finiteType_subring R ((Over.pullback f).obj A) ∅ (isAbelianScheme_pullback A hA f)
  have : IsNoetherianRing S₀ := Algebra.FiniteType.isNoetherianRing ℤ S₀
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have : GeometricallyIntegral B.hom :=
    GlobalTheory.geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres B.hom
  have w : (A.hom ⁻¹ᵁ V).ι ≫ A.hom = (A.hom ∣_ V ≫ e.hom) ≫ f := by
    rw [Category.assoc, hf]
    exact (isPullback_morphismRestrict A.hom V).flip.w
  have sq : IsPullback (pullback.lift _ _ w) (A.hom ∣_ V) (pullback.snd A.hom f) e.hom := by
    refine IsPullback.of_right (h₁₂ := pullback.fst A.hom f) (v₁₃ := A.hom) (h₂₂ := f) ?_
      (pullback.lift_snd _ _ _) (.of_hasPullback _ _)
    rw [pullback.lift_fst, hf]
    exact (isPullback_morphismRestrict A.hom V).flip
  exact GlobalTheory.ProperFunctions.isIso_appTop_baseChange (sq.paste_horiz hpb.1)

theorem isIso_app_of_isAbelianScheme : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A],
    IsAbelianScheme A → ∀ U : S.Opens, IsIso (A.hom.app U) := fun _ A _ hA U ↦
  GlobalTheory.ProperFunctions.isIso_app_of_forall_affineOpens A.hom (fun V ↦
    have : IsAffine V.1.toScheme := V.2
    isIso_appTop_restrict A hA V.1) U

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalSystemSplitFibresStatement
section
open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_system_split_fibres : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (Yl : ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → LocalSystem Xo p W), (∀ p W hp hW i, (Yl p W hp hW i).SplitFibres ∧ (Yl p W hp hW i).N3) → ∀ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), (∀ (p : ℕ) (W : ValuationSubring ℂ) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (b : 𝓞 c.F →+* c.V W), (∀ x, ((b x : c.V W) : c.F) = (x : c.F)) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Dominates Y (Yl p W hp hW ⟨l, c, hg p hp⟩) b) → ∀ (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ), p.Prime → p ∉ S → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (τ : CMType H) (a : ⋀[Ω]^D.p 𝔐.Li) (b : ⋀[Ω]^D.q 𝔐.Li), a ≠ 0 → b ≠ 0 → (∃ x f, IsCoeffAt (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) D.p D.q a b x f) → NumTrivMod (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) D.p D.q a b) (p : Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.numTriv_offS | exact GlobalTheory.CompanionTheory.Ar.Flat.numTriv_offS | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.numTriv_offS <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelOnHodgeFromFamilyStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_on_hodge_from_family : GlobalTheory.CompanionTheory.Ar.Num.FamilyExistsPos → HodgeLatticeFlagBound := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.model_on_hodge_of_family_pos | exact GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.model_on_hodge_of_family_pos | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HodgeModel.model_on_hodge_of_family_pos <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrdinaryCurveModelRelayStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinary_curve_model_relay : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∀ (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → v (p : C) < 1 → ∀ τ (hb : ((Fin (labelRk D (e τ)) → C) →ₗ[C] (Fin (D.p + D.q) → C))), Function.Injective hb → LinearMap.range hb = LinearMap.ker (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) → (stdLat RC _).comap hb.toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).W τ → (∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, hb a - GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (i τ) a ∈ mulLat (algebraMap O C w) (stdLat RC _)) → (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).map (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))).toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).om τ ∧ (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).comap hb.toAddMonoidHom = divLat (algebraMap O C w) (((chartD e b pq sc w P i).bc RC).lie τ) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.ordinary_curve_model_relay | exact GlobalTheory.CompanionTheory.Relay.ordinary_curve_model_relay | (intros; apply GlobalTheory.CompanionTheory.Relay.ordinary_curve_model_relay <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmallPointsOverNumberField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.small_points_over_number_field : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L₀ : Type) [Field L₀] [NumberField L₀], 1 ≤ D.p + D.q → ∀ w ∈ Small.ptsOver L₀ (mCoordIdeal y), ∃ (L : Type) (_ : Field L) (_ : NumberField L) (e : L₀ →+* L) (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) (_ : AddCommGroup V) (_ : Module L V) (_ : Module (𝓞 L) V) (_ : IsScalarTower (𝓞 L) L V) (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V), CoordsAt 𝔐.ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) (fun p => e (w p)) ∧ 𝔐.IsLinPtOf z P MV A ∧ (∀ s, Module.finrank L (eigSp A.ρ (A.σ s)) = labelRk D s) ∧ Module.finrank (𝓞 L) A.Bq.carrier ≤ Fintype.card (CMType H) * (D.p + D.q) := by
  first | exact @LevelTowerAlt.integral_point_extends_compact | exact LevelTowerAlt.integral_point_extends_compact
end

