import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2345
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2573
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2582
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueStatementHolds
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2642
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2625
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2409
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormsAddOfFactorProduct
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2626
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasMarkingTransportOfCmTypeEmbedding
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.GoodTransport

theorem exists_equiv_of_lattices {La : Type} [AddCommGroup La] {g : ℕ} (P P' : La →+ (Fin g → ℂ))
    (hi : Function.Injective P) (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤)
    (hi' : Function.Injective P') (hd' : DiscreteTopology P'.range) (hs' : Submodule.span ℝ (Set.range P') = ⊤) :
    ∃ φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ), ∀ a, φ (P a) = P' a := by
  let L : Submodule ℤ (Fin g → ℂ) := LinearMap.range P.toIntLinearMap
  let L' : Submodule ℤ (Fin g → ℂ) := LinearMap.range P'.toIntLinearMap
  haveI : DiscreteTopology L := hd
  haveI : DiscreteTopology L' := hd'
  haveI : IsZLattice ℝ L := ⟨hs⟩
  haveI : IsZLattice ℝ L' := ⟨hs'⟩
  let e : La ≃ₗ[ℤ] L := LinearEquiv.ofInjective P.toIntLinearMap hi
  let e' : La ≃ₗ[ℤ] L' := LinearEquiv.ofInjective P'.toIntLinearMap hi'
  let b := Module.Free.chooseBasis ℤ L
  let b₀ := b.map e.symm
  let b' := b₀.map e'
  let φ := (b.ofZLatticeBasis ℝ L).equiv (b'.ofZLatticeBasis ℝ L') (Equiv.refl _)
  have key : (φ.toLinearMap.restrictScalars ℤ).comp P.toIntLinearMap = P'.toIntLinearMap := by
    refine b₀.ext fun k => ?_
    have h1 : P (b₀ k) = b.ofZLatticeBasis ℝ L k := by
      rw [Module.Basis.ofZLatticeBasis_apply]
      exact congrArg Subtype.val (e.apply_symm_apply (b k))
    have h2 : P' (b₀ k) = b'.ofZLatticeBasis ℝ L' k := by
      rw [Module.Basis.ofZLatticeBasis_apply]
      rfl
    change φ (P (b₀ k)) = P' (b₀ k)
    rw [h1, h2, Module.Basis.equiv_apply]
    rfl
  exact ⟨φ, fun a => LinearMap.congr_fun key a⟩

theorem ex_eq_iff {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (z w : Fin g → ℂ) :
    u.ex z = u.ex w ↔ z - w ∈ u.Λ := by
  have := u.ex_add (z - w) w
  rw [sub_add_cancel] at this
  rw [← u.ker, this]
  exact mul_eq_right

def imHerm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (herm Hm z w).im)
    (fun _ _ _ => by simp [herm])
    (fun r z w => by
      rw [herm, herm, smul_dotProduct, Complex.smul_im])
    (fun _ _ _ => by simp [herm, Matrix.mulVec_add])
    (fun r z w => by
      rw [herm, herm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im, star_trivial])

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}

theorem fibre_marks {Xo : Moduli D l} {σ : KA l →+* ℂ} {g₀ : ℕ} {ty : Fin g₀ → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty)
    (i : Fin Fu.n) {P : (Fu.Di i).La →+ (Fin g₀ → ℂ)} (hP : IsPeriod (Fu.Di i) ty P) {y₀ : Sp ℂ ⟶ Xo.X}
    (hy : y₀ = Fu.u i P) {s' : Sp ℂ ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s'} (m : ObjMap o Xo.univ y₀) {g : ℕ}
    (u : HolUnif o.t.G o.t.PP.L g) (h : (Fin g₀ → ℂ) → (Fin g → ℂ))
    (hh : ∀ z, (u.ex (h z)).left ≫ m.toSABMap.φ = (Fu.ex i P z).left) :
    (∀ (a : 𝓞 E) z, u.ex (h z) ≫ o.t.act.act a = u.ex (h fun k => ty k (a : E) * z k)) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
        o.eta a = u.ex (h ((l.M : ℂ)⁻¹ • P (Fu.t i a)))) ∧
      ∀ a, o.etaA a = u.ex (h ((l.A : ℂ)⁻¹ • P (Fu.t i a))) := by
  subst hy
  have inj : ∀ x y : 𝟙_ (Over (Sp ℂ)) ⟶ o.t.G, x.left ≫ m.toSABMap.φ = y.left ≫ m.toSABMap.φ → x = y :=
    fun x y h => Over.OverMorphism.ext (m.cart.1.hom_ext h (by rw [Over.w x, Over.w y]))
  refine ⟨fun a z => inj _ _ ?_, fun a ha => inj _ _ ?_, fun a => inj _ _ ?_⟩
  · rw [hh, Fu.ex_lin i P hP, Over.comp_left, Over.comp_left, ← hh, Category.assoc, Category.assoc]
    exact congrArg _ (m.act a)
  · rw [hh, ← Fu.ex_eta i P hP a ha]
    exact m.eta a
  · rw [hh, ← Fu.ex_etaA i P hP a]
    exact m.etaA a

theorem exists_eta_eq (a : D.La) : ∃ a₁ ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
    ∀ {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s),
      o.eta a = o.eta a₁ := by
  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [l.coprime]; trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 h1
  refine ⟨y • a, Submodule.smul_mem_smul hy trivial, fun o => ?_⟩
  have : a = x • a + y • a := by rw [← add_smul, hxy, one_smul]
  conv_lhs => rw [this]
  rw [o.eta_add, o.eta_ker _ (Submodule.smul_mem_smul hx trivial), _root_.one_mul]

theorem exists_transport {Xo : Moduli D l} {σ : KA l →+* ℂ} {g₀ : ℕ} {ty : Fin g₀ → (E →+* ℂ)}
    (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) {P P' : (Fu.Di i).La →+ (Fin g₀ → ℂ)} (hP : IsPeriod (Fu.Di i) ty P)
    (hP' : IsPeriod (Fu.Di i) ty P') {y₀ y₀' : Sp ℂ ⟶ Xo.X} (hy : y₀ = Fu.u i P) (hy' : y₀' = Fu.u i P')
    {s s' : Sp ℂ ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s} {o' : Obj D l (baseKA l) s'} (m : ObjMap o Xo.univ y₀)
    (m' : ObjMap o' Xo.univ y₀') {g g' : ℕ} (u : HolUnif o.t.G o.t.PP.L g) (u' : HolUnif o'.t.G o'.t.PP.L g')
    {Hm : Matrix (Fin g) (Fin g) ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ} {κ : u.Λ → ℂ} {κ' : u'.Λ → ℂ}
    (hAH : u.IsAH Hm κ) (hAH' : u'.IsAH Hm' κ') : ∃ φ, IsTransport o o' u u' Hm Hm' φ := by
  obtain ⟨h, hex, hΛ, hE, -⟩ := FibreCmp.exists_equiv_of_isAH E H D l Xo σ g₀ ty Fu i P y₀ s o m g u Hm κ hP hy hAH
  obtain ⟨h', hex', hΛ', hE', -⟩ :=
    FibreCmp.exists_equiv_of_isAH E H D l Xo σ g₀ ty Fu i P' y₀' s' o' m' g' u' Hm' κ' hP' hy' hAH'
  obtain ⟨a1, a2, a3⟩ := fibre_marks Fu i hP hy m u h hex
  obtain ⟨b1, b2, b3⟩ := fibre_marks Fu i hP' hy' m' u' h' hex'
  obtain ⟨φ₀, hφ₀⟩ := exists_equiv_of_lattices P P' hP.2.1 hP.2.2.1 hP.2.2.2.1 hP'.2.1 hP'.2.2.1 hP'.2.2.2.1
  let φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g' → ℂ) :=
    ((h.symm.restrictScalars ℝ).trans φ₀).trans (h'.restrictScalars ℝ)
  have hφ : ∀ z, φ (h z) = h' (φ₀ z) := fun z => congrArg (fun t => h' (φ₀ t)) (h.symm_apply_apply z)
  have lat : ∀ z, φ z ∈ u'.Λ ↔ z ∈ u.Λ := fun z => by
    obtain ⟨z, rfl⟩ := h.surjective z
    rw [hφ, hΛ, hΛ']
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, φ₀.injective ((hφ₀ a).trans ha)⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, (hφ₀ a).symm⟩
  have exq : ∀ z w, u.ex z = u.ex w → u'.ex (φ z) = u'.ex (φ w) := fun z w hzw => by
    rw [ex_eq_iff] at hzw ⊢
    rw [← map_sub, lat]
    exact hzw
  have lin : ∀ (a : 𝓞 E) z, φ₀ (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * φ₀ z k := fun a z => by
    let T : (Fin g₀ → ℂ) →ₗ[ℝ] (Fin g₀ → ℂ) :=
      LinearMap.pi fun k => (LinearMap.mulLeft ℝ (ty k (a : E))).comp (LinearMap.proj k)
    have : φ₀.toLinearMap.comp T = T.comp φ₀.toLinearMap := by
      refine LinearMap.ext_on_range hP.2.2.2.1 fun x => ?_
      have e1 : T (P x) = P (a • x) := funext fun k => (hP.1 a x k).symm
      have e2 : T (P' x) = P' (a • x) := funext fun k => (hP'.1 a x k).symm
      change φ₀ (T (P x)) = T (φ₀ (P x))
      rw [e1, hφ₀, hφ₀, e2]
    exact LinearMap.congr_fun this z
  have dv : ∀ (n : ℕ) x, φ₀ ((n : ℂ)⁻¹ • P x) = (n : ℂ)⁻¹ • P' x := fun n x => by
    have e : ∀ v : Fin g₀ → ℂ, (n : ℂ)⁻¹ • v = (n : ℝ)⁻¹ • v := fun v => by
      rw [← Complex.coe_smul]; simp
    rw [e, e, map_smul, hφ₀]
  refine ⟨φ, lat, fun a z w hw => ?_, fun z w => ?_, fun a z hz => ?_, fun a z hz => ?_⟩
  · obtain ⟨z, rfl⟩ := h.surjective z
    rw [a1] at hw
    rw [exq _ _ hw, hφ, hφ, b1, lin]
  · obtain ⟨z, rfl⟩ := h.surjective z
    obtain ⟨w, rfl⟩ := h.surjective w
    let j := (h.restrictScalars ℝ).toLinearMap
    have : (imHerm Hm').compl₁₂ (φ.toLinearMap.comp j) (φ.toLinearMap.comp j) = (imHerm Hm).compl₁₂ j j := by
      refine LinearMap.ext_on_range hP.2.2.2.1 fun x => LinearMap.ext_on_range hP.2.2.2.1 fun y => ?_
      change (herm Hm' (φ (h (P x))) (φ (h (P y)))).im = (herm Hm (h (P x)) (h (P y))).im
      rw [hφ, hφ, hφ₀, hφ₀, hE, hE']
    exact LinearMap.congr_fun (LinearMap.congr_fun this z) w
  · obtain ⟨a₁, ha₁, e⟩ := exists_eta_eq (l := l) a
    rw [e o, a2 a₁ ha₁] at hz
    rw [exq _ _ hz, e o', b2 a₁ ha₁, hφ, dv]
  · rw [a3] at hz
    rw [exq _ _ hz, b3, hφ, dv]

theorem hasTransport_of_goodEmb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens) (e : c.F →+* ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsClosed (U : Set (Xo.XF c)) → IsOpenImmersion io → Set.range io = compactOf Y U → io ≫ genStr Y = B.str → 1 ≤ D.p + D.q → Formalism.L2.PjFree.GoodEmb c e → HasTransport Xo c U e := by
  intro E _ _ _ H D l Xo c O _ β Y U e B io hU hio hr hs hpq he y y' hy hy' hyU hyU' o o' ⟨m⟩ ⟨m'⟩ g g' u u' Hm Hm'
    κ κ' hAH hAH'
  let e₀ : Fin (Fintype.card (Pad.Letter D)) ≃ Pad.Letter D := (Fintype.equivFin _).symm
  have hty := (GlobalTheory.Relab.relab_good E H l c e he).2.2.2 D _ e₀
  obtain ⟨Fu⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H D l Xo (e.comp (IntermediateField.inclusion c.le).toRingHom) _
    (fun j => Formalism.L2.PjFree.relab c e (e₀ j).1) hpq he hty
  have ov : ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ toF Xo c = spMap e →
      (x ≫ toX Xo c) ≫ Xo.s = spMap (e.comp (IntermediateField.inclusion c.le).toRingHom) := fun x hx => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx, DetExtendZero.spMap_comp]
  obtain ⟨i, P, hP, hu⟩ := Fu.onto _ (ov y hy)
  obtain ⟨i', P', hP', hu'⟩ := Fu.onto _ (ov y' hy')
  obtain rfl : i = i' := GlobalTheory.T.complexPoints_component_same_periodSpace E H D l Xo c O β Y U e _ _ Fu i i' P P' y y' B io hU hio hr hs hy hy' hyU hyU'
    hP hP' hu.symm hu'.symm
  exact exists_transport Fu i hP hP' hu.symm hu'.symm m m' u u' hAH hAH'

end GlobalTheory.DetLine.GoodTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeOfLocal
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem local_of_opens_pullback (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q] {X Y : Scheme.{0}}
    (f : X ⟶ Y) {Ix : Type} (V : Ix → Y.Opens) (hV : ∀ y : Y, ∃ i, y ∈ V i)
    (h : ∀ i, Q (pullback.snd f (V i).ι)) : Q f := by
  have hV' : iSup V = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.2 (hV y)
  exact IsZariskiLocalAtTarget.of_openCover (P := Q) (Y.openCoverOfIsOpenCover V hV') h

theorem Good.of_opens {g : ℕ} {X Y : Scheme.{0}} (f : X ⟶ Y) {Ix : Type} (V : Ix → Y.Opens)
    (hV : ∀ y : Y, ∃ i, y ∈ V i) (h : ∀ i, Good g (pullback.snd f (V i).ι)) : Good g f := by
  have h1 : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{0} g) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  have h2 : IsZariskiLocalAtTarget (@GeometricallyConnected.{0}) := by
    rw [GeometricallyConnected.eq_geometrically]; infer_instance
  exact ⟨local_of_opens_pullback @IsProper f V hV fun i ↦ (h i).proper,
    local_of_opens_pullback (@SmoothOfRelativeDimension g) f V hV fun i ↦ (h i).smooth,
    local_of_opens_pullback @GeometricallyConnected f V hV fun i ↦ (h i).conn⟩

theorem hasRep_of_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (g : ℕ), IsAbelianScheme A → (∀ s : S, ∃ V : S.Opens, s ∈ V ∧ HasRep A g (Over.mk V.ι)) → HasRep A g (𝟙_ _) := by
  intro S A _ g hA h
  choose V hV hR using h
  obtain ⟨B, P, hP, hG⟩ := GlobalTheory.T.exists_additiveFamily_representative_zariski_glue S A hA S V (fun _ ↦ g) (fun s ↦ ⟨s, hV s⟩) hR
  exact ⟨B, toUnit B, P, hP, Good.of_opens (Y := S) B.hom V (fun s ↦ ⟨s, hV s⟩) hG⟩

end GlobalTheory.DualCon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLatticeBasisOfEigenvectors
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem eigconj_sum_mem_latT_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p : ℕ) [Fact p.Prime]
    (l : Level H) (c : Coeff l) [Algebra c.F ℂ_[p]],
    letI := H.starRing; ∀ (Q : PtP E p) (τ : Psi H) (n : ℕ) (xx : Fin n → LieG Q.Gt) (g : Matrix (Fin n) (Fin n) ℂ_[p]),
      (∀ j, AvDefs.IsEig Q.Gt Q.oGt (embInt c Q.integers (conjEmb τ.1)) (xx j)) →
      IsLatBasis ℂ_[p] (htLat c Q (conjEmb τ.1)) (fun i => ∑ j, g i j • Q.bLie (xx j)) → ∀ a : Fin n → ℂ_[p],
        (∑ i, a i • ∑ j, g i j • Q.bLie (xx j) ∈ Q.latT ↔ ∀ i, ‖(1 : ℂ_[p]) * a i‖ ≤ 1) := by
  intro E _ _ _ H p _ l c _
  letI := H.starRing
  intro Q τ n xx g hx hb a
  have hs : (∑ i, a i • ∑ j, g i j • Q.bLie (xx j)) ∈ Q.eigV (embInt c Q.integers (conjEmb τ.1)) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bLie_mem_eigV (hx j)))
  have h := hb.sum_mem_iff a
  rw [htLat_conj] at h
  simp only [_root_.one_mul, ← mem_range_iff_norm_le p]
  rw [← h]
  exact ⟨fun h1 => ⟨h1, hs⟩, fun h1 => h1.1⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFamGramPosSemidef
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi Formalism.L2.Pj
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.LieHt

namespace GlobalTheory.HeightParts

section Gram

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] (h : HermFam K V) (σ : K →+* ℂ)

theorem hermFam_add_left (x y z : V) : h.form σ (x + y) z = h.form σ x z + h.form σ y z := by
  rw [← h.conj_symm σ z (x + y), h.add_right, map_add, h.conj_symm, h.conj_symm]

theorem hermFam_smul_left (a : K) (x y : V) : h.form σ (a • x) y = starRingEnd ℂ (σ a) * h.form σ x y := by
  rw [← h.conj_symm σ y (a • x), h.smul_right, map_mul, h.conj_symm]

theorem hermFam_sum_sum {α β : Type} [Fintype α] [Fintype β] (c : α → K) (x : α → V) (d : β → K) (y : β → V) :
    h.form σ (∑ i, c i • x i) (∑ j, d j • y j) =
      ∑ i, ∑ j, starRingEnd ℂ (σ (c i)) * σ (d j) * h.form σ (x i) (y j) := by
  classical
  have hl : ∀ (s : Finset α) (z : V), h.form σ (∑ i ∈ s, c i • x i) z = ∑ i ∈ s, h.form σ (c i • x i) z := by
    intro s z
    induction s using Finset.induction_on with
    | empty =>
      have := hermFam_add_left h σ 0 0 z
      simp only [add_zero] at this
      simp only [Finset.sum_empty]
      linear_combination -this
    | insert a s ha ih => rw [Finset.sum_insert ha, hermFam_add_left, ih, Finset.sum_insert ha]
  have hr : ∀ (s : Finset β) (z : V), h.form σ z (∑ j ∈ s, d j • y j) = ∑ j ∈ s, h.form σ z (d j • y j) := by
    intro s z
    induction s using Finset.induction_on with
    | empty =>
      have := h.add_right σ z 0 0
      simp only [add_zero] at this
      simp only [Finset.sum_empty]
      linear_combination -this
    | insert a s ha ih => rw [Finset.sum_insert ha, h.add_right, ih, Finset.sum_insert ha]
  rw [hl]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hr]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hermFam_smul_left, h.smul_right]
  ring

theorem hermFam_gram_posSemidef {n : ℕ} (v : Fin n → V) : (h.gram σ v).PosSemidef := by
  classical
  let W := Submodule.span K (Set.range v)
  haveI : FiniteDimensional K W := FiniteDimensional.span_of_finite K (Set.finite_range v)
  let b := Module.finBasis K W
  have hb : LinearIndependent K (fun i => (b i : V)) := b.linearIndependent.map' W.subtype W.ker_subtype
  let g : Matrix (Fin n) (Fin (Module.finrank K W)) K :=
    Matrix.of fun i j => b.repr ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ j
  have hf : ∀ i, v i = ∑ j, g i j • (b j : V) := fun i => by
    have := congrArg W.subtype (b.sum_repr ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩).symm
    rw [map_sum] at this
    simpa [g] using this
  have hG := (h.posDef σ _ _ hb).posSemidef
  let B : Matrix (Fin n) (Fin (Module.finrank K W)) ℂ := Matrix.of fun i j => starRingEnd ℂ (σ (g i j))
  let G : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) ℂ := Matrix.of fun i j => h.form σ (b i : V) (b j)
  have e : h.gram σ v = B * G * B.conjTranspose := by
    ext i j
    simp only [HermFam.gram, G, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, B, RCLike.star_def,
      Complex.conj_conj]
    rw [hf i, hf j, hermFam_sum_sum, Finset.sum_comm]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [e]
  exact hG.mul_mul_conjTranspose_same B

end Gram

section Mono

variable {K : Type} [Field K] [NumberField K] {m r m' : ℕ} {h : HermFam K (Fin m → K)}
  {L : Submodule (𝓞 K) (Fin m → K)} {ε : Fin r → Fin m → K} {q : (Fin m → K) →ₗ[K] (Fin m' → K)}
  {h' : HermFam K (Fin m' → K)} {L' : Submodule (𝓞 K) (Fin m' → K)}

theorem torusExt_mono {C C' : ℝ} (hT : TorusExt h L ε q h' L' C) (hC : C ≤ C') : TorusExt h L ε q h' L' C' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, hm⟩ := hT
  have hd : (0 : ℂ) ≤ ((C' - C : ℝ) : ℂ) := Complex.zero_le_real.2 (sub_nonneg.2 hC)
  refine ⟨a1, a2, a3, a4, a5, a6, a7, fun σ => ⟨?_, fun n v => ?_⟩⟩
  · have := (hm σ).1.add ((hermFam_gram_posSemidef h σ ε).smul hd)
    convert this using 1
    push_cast
    module
  · have := ((hm σ).2 n v).add ((hermFam_gram_posSemidef h σ v).smul hd)
    convert this using 1
    push_cast
    module

end Mono

section With

variable {D : D7} (O : Setup D)

def IsLieAtWith (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ) (y : Pt O.s) (K : Type) [Field K] [NumberField K] (io : K →+* Qb)
    (L : Submodule (𝓞 K) (Fin (D.R.f * O.N) → K)) (h : HermFam K (Fin (D.R.f * O.N) → K)) : Prop :=
  ∃ (fK : O.κ.c.F →+* K) (yK : Sp K ⟶ gen O.s.T.Z)
    (xO : Sp (𝓞 K) ⟶ O.s.T.Z.X) (hx : spMap (algebraMap (𝓞 K) K) ≫ xO = yK ≫ genι O.s.T.Z)
    (hio : spMap io ≫ yK = y.y) (e : Fin (D.R.f * O.N) ≃ Letter O.S.Dw)
    (b : Fin (D.R.f * O.N) → TanM (yK ≫ genι O.s.T.Z) O.s.T.Z.t.G),
    O.CoreWith x P ∧ yK ≫ genStr O.s.T.Z = spMap fK ∧
    (∀ i, (tv (bcTan io (by rw [← Category.assoc, hio]) (b i))).left = y.u (e i).1 (e i).2) ∧
    L = lieCoordLat O.s.T.Z.t hx b ∧
    ∀ (σ : K →+* ℂ) (z : CxPts (genStr O.s.T.Z) (σ.comp fK)) (hz : z.1 = spMap σ ≫ yK) (u v : Fin (D.R.f * O.N) → K),
      h.form σ u v = x.met (σ.comp fK) z (bcTan σ (by rw [hz, Category.assoc]) (∑ i, v i • b i))
        (bcTan σ (by rw [hz, Category.assoc]) (∑ i, u i • b i))

variable {O} in

theorem IsLieAtWith.isLieAt {x : ToroidalCompactificationData O.s} {P : PolOf x O.Φ} {y : Pt O.s} {K : Type} [Field K] [NumberField K]
    {io : K →+* Qb} {L : Submodule (𝓞 K) (Fin (D.R.f * O.N) → K)} {h : HermFam K (Fin (D.R.f * O.N) → K)}
    (hw : IsLieAtWith O x P y K io L h) : IsLieAt O y K L h := by
  obtain ⟨fK, yK, xO, hx, hio, e, b, h₁, h₂, h₃, h₄, h₅⟩ := hw
  exact ⟨x, P, io, fK, yK, xO, hx, hio, e, b, h₁, h₂, h₃, h₄, h₅⟩

end With

end GlobalTheory.HeightParts

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionOfRep
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef

theorem le_of_rep : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (a b a' b' : ℤ) (M M' : HermLB p) (f : X.functionField), P.Rep a b M → P.Rep a' b' M' → f ≠ 0 → f ∈ P.Bl (a - a') (b - b') 1 → Le M' M := by
  intro k _ X _ p P a b a' b' M M' f hM hM' hf hB
  have hR : P.Rep (a - a') (b - b') (M.tens M'.dual) := by
    have h := Pair.rep_tens k X p P a b (-a') (-b') M M'.dual hM (Pair.rep_dual k X p P a' b' M' hM')
    simpa only [sub_eq_add_neg] using h
  obtain ⟨e, -, hrange, hnorm, hloc⟩ := RepDict.rep_dict k X p P _ _ _ hR
  have hfH : f ∈ (P.H (a - a') (b - b') : Set X.functionField) := hB.1
  rw [← hrange] at hfH
  obtain ⟨u, rfl⟩ := hfH
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_exists_smallSection_difference k X p M M').2 ⟨u, fun σ y => ?_, fun hu => ?_⟩
  · rw [← hnorm u σ y]
    have h0 : 0 ≤ P.nu (a - a') (b - b') σ y (e u) := by
      unfold Pair.nu; positivity
    exact pow_le_one₀ h0 (hB.2 σ y)
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (P.L.isLB.cover.ge (Opens.mem_top (genericPoint X)))
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (P.A.isLB.cover.ge (Opens.mem_top (genericPoint X)))
    have hne : P.loc (a - a') (b - b') (e u) i j ≠ 0 := by
      have h1 := (P.r i).ne_zero
      have h2 := (P.r' j).ne_zero
      simp only [Pair.loc]
      exact mul_ne_zero (mul_ne_zero hf (zpow_ne_zero _ h1)) (zpow_ne_zero _ h2)
    have hg := (hloc u (genericPoint X) i j hi hj).2 (unitAt_genericPoint hne)
    obtain ⟨c, hc⟩ := Opens.mem_iSup.1 ((M.tens M'.dual).isLB.cover.ge (Opens.mem_top (genericPoint X)))
    rw [mem_nonzeroLocus_iff u c hc, hu] at hg
    change genericPoint X ∈ X.basicOpen (0 : Γ(X, _)) at hg
    simp at hg

end GlobalTheory.HSNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairBallsFiniteStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermLineBundlePair_balls_finite : GlobalTheory.Published.ArithHilbertSamuel → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (a c : ℤ) (R : ℝ), GlobalTheory.Published.ArCalc → (P.Bl a c R).Finite := by
  first | exact @GlobalTheory.VolBr.BallFinite.bl_finite | exact GlobalTheory.VolBr.BallFinite.bl_finite | (intros; apply GlobalTheory.VolBr.BallFinite.bl_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormsAddOfFactorProductStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_forms_add_of_factor_product : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → IsProjOver A.hom →
    ∀ (M₁ M₂ M₃ : LB A.left) (u₁ : HolUnif A M₁ g) (u₂ : HolUnif A M₂ g) (u₃ : HolUnif A M₃ g)
      (H₁ H₂ H₃ : Matrix (Fin g) (Fin g) ℂ) (χ₁ : u₁.Λ → ℂ) (χ₂ : u₂.Λ → ℂ) (χ₃ : u₃.Λ → ℂ),
    M₁.IsLB → M₂.IsLB → M₃.IsLB → u₂.ex = u₁.ex → u₃.ex = u₁.ex →
    IsFactorAH u₁ H₁ χ₁ → IsFactorAH u₂ H₂ χ₂ → IsFactorAH u₃ H₃ χ₃ → H₃ = H₁ + H₂ →
    LBIso (abelian₂ A M₂) (LB.div (abelian₂ A M₃) (abelian₂ A M₁)) := by
  first | exact @GlobalTheory.TorusRM.lbIso_lam_of_add | exact GlobalTheory.TorusRM.lbIso_lam_of_add | (intros; apply GlobalTheory.TorusRM.lbIso_lam_of_add <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinFourierExpansionSupportStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertEisenstein_fourier_expansion_support : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (G : (Emb F → ℂ) → ℂ), HasExpansion 𝔞 𝔟 k G → ∃ (Z : ℂ → ℂ) (a : F → ℂ), IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Z ∧ a 0 = (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) ∧ (∀ ξ, ξ ≠ 0 → ∃ n : ℤ, a ξ = n) ∧ (∀ ξ, ξ ≠ 0 → a ξ ≠ 0 → ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ i : Emb F, 0 < i ξ) ∧ ∀ w ∈ upperHalf F, HasSum (fun ξ : F ↦ a ξ * qPow ξ w) ((cK F k : ℂ) * G w / (omegaFactor 𝔞 : ℂ) ^ k) := by
  first | exact @GlobalTheory.HilbFam.fourier_with_support | exact GlobalTheory.HilbFam.fourier_with_support | (intros; apply GlobalTheory.HilbFam.fourier_with_support <;> assumption)
end

