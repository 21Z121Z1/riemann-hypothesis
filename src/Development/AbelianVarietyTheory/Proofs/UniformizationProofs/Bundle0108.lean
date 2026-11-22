import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0102
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsOddNeZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0103
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0104

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitPointEqOfIso
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace ArcObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_sabMap_of_iso (hG : GlobalFnsSt) {S S' : Scheme.{0}} {t t' : SAB H S} {u u' : SAB H S'} {f : S' ⟶ S}
    (n : SABMap u t f) (n' : SABMap u' t' f) (hA : IsAbelianScheme u.G) (ψ : t.G ≅ t'.G) [IsMonHom ψ.hom]
    (hact : ∀ x, t.act.act x ≫ ψ.hom = ψ.hom ≫ t'.act.act x) (hL : LBIso t.PP.L (t'.PP.L.pull ψ.hom.left)) :
    ∃ m : SABMap u u' (𝟙 _), m.φ ≫ n'.φ = n.φ ≫ ψ.hom.left := by
  have c := n.cart.comp (isGrpPullback_of_iso ψ)
  rw [Category.comp_id] at c
  obtain ⟨α, hα, hφ⟩ := grpPullback_iso c n'.cart
  have ha : ∀ x, (u.act.act x).left ≫ α.hom.left = α.hom.left ≫ (u'.act.act x).left := fun x => by
    have e : (t.act.act x).left ≫ ψ.hom.left = ψ.hom.left ≫ (t'.act.act x).left := congrArg (fun q => q.left) (hact x)
    apply n'.cart.1.hom_ext
    · rw [Category.assoc, hφ, Category.assoc, n'.act, ← Category.assoc, n.act, ← Category.assoc, hφ, Category.assoc,
        Category.assoc, e]
    · simp only [Category.assoc, Over.w]
  have hb : LBIso u.PP.L (u'.PP.L.pull α.hom.left) := by
    obtain ⟨w, hw⟩ := hL
    obtain ⟨w₁, g₁, -⟩ := (isPullCubical_iff _ _ _).1 n.lin
    obtain ⟨w₂, g₂, -⟩ := (isPullCubical_iff _ _ _).1 n'.lin
    have hw' := (isGen_iff w).1 hw
    obtain ⟨w₃, T⟩ := exists_comp t.PP.isLB w w₁ hw' g₁ t'.PP.isLB u.PP.isLB
    obtain ⟨w₄, g₄⟩ : ∃ w₄ : LB.Iso u.PP.L (t'.PP.L.pull (α.hom.left ≫ n'.cm.F)), PGen w₄ := by
      rw [hφ]; exact ⟨w₃, T.pgen_comp t.PP.isLB hw' g₁⟩
    obtain ⟨w₅, T'⟩ := exists_cancel t'.PP.isLB w₂ w₄ g₂ g₄ u'.PP.isLB u.PP.isLB
    exact ⟨w₅, (isGen_iff w₅).2 (T'.pgen_cancel t'.PP.isLB g₂ g₄)⟩
  exact ⟨⟨CubeMap.ofHom α.hom, isGrpPullback_of_iso α, rfl, ha,
    HeckePoint.isPullCubical_of_iso hG hA α.hom u.cub u'.cub hb⟩, hφ⟩

theorem exists_sab_fac {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {h : S'' ⟶ S} (m : SABMap t' t f) (n : SABMap t'' t h) (e : h = g ≫ f) :
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact ObjMaps.exists_sab_cancel m n

variable {D : Datum H} {l : Level H}

theorem objMap_eq (hS : SerreSt) {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {F : Type} [Field F]
    {s : S ⟶ Sp B} {s' : Sp F ⟶ Sp B} {o : Obj D l b s} {o₁ : Obj D l b s'} {y y' : Sp F ⟶ S} (e : y = y')
    (m : ObjMap o₁ o y) (m' : ObjMap o₁ o y') : m.toSABMap.φ = m'.toSABMap.φ := by
  subst e
  exact objMap_unique_of_field hS m m'

theorem point_eq (hL : Laws) {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O']
    {β : O →+* c.F} {β' : O' →+* c.F} {Y : Model Xo c β} {Y' : Model Xo c β'} {S : Scheme.{0}} {χ : S ⟶ Y.X}
    {χ' : S ⟶ Y'.X} {t t' : SAB H S} (m : SABMap t Y.t χ) (m' : SABMap t' Y'.t χ') (ψ : t.G ≅ t'.G) [IsMonHom ψ.hom]
    (hact : ∀ x, t.act.act x ≫ ψ.hom = ψ.hom ≫ t'.act.act x) (hb : LBIso t.PP.L (t'.PP.L.pull ψ.hom.left))
    {K : Type} [Field K] (j : Sp K ⟶ S) (y y' : Sp K ⟶ Xo.XF c) (hy : y ≫ Y.j = j ≫ χ) (hy' : y' ≫ Y'.j = j ≫ χ')
    (hs : y ≫ pullback.snd _ _ = y' ≫ pullback.snd _ _)
    (hlev : ∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G),
      ((∃ v, σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨ ∃ v, σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v) →
      ∀ g : Sp K ⟶ t.G.left, g ≫ t.G.hom = j → g ≫ m.φ = y ≫ σ.left ≫ Y.m.φ →
        g ≫ ψ.hom.left ≫ m'.φ = y' ≫ σ'.left ≫ Y'.m.φ) :
    y = y' ∧ ∀ (T : Scheme.{0}) (g : T ⟶ t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left) (τ : T ⟶ Sp K),
      g ≫ t.G.hom = τ ≫ j → g₁ ≫ Y.oF.t.G.hom = τ ≫ y → g ≫ m.φ = g₁ ≫ Y.m.φ →
      g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ → g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom →
      g ≫ ψ.hom.left ≫ m'.φ = g₂ ≫ Y'.m.φ := by
  have hid : spMap (RingHom.id (KA l)) = 𝟙 _ := Spec.map_id _
  have hs' : y' ≫ pullback.fst _ _ ≫ Xo.s = y ≫ pullback.fst _ _ ≫ Xo.s := by
    rw [pullback.condition, reassoc_of% hs]
  obtain ⟨o, ⟨m₁⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ _ (y ≫ pullback.fst _ _ ≫ Xo.s) y
    rfl rfl (by rw [hid, Category.comp_id]) Y.oF
  obtain ⟨o', ⟨m₂⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ _ (y ≫ pullback.fst _ _ ≫ Xo.s) y'
    rfl rfl (by rw [hid, Category.comp_id, hs']) Y'.oF
  obtain ⟨k₁, e₁⟩ := ObjMaps.exists_sab_comp Y.m m₁.toSABMap
  obtain ⟨k₂, e₂⟩ := ObjMaps.exists_sab_comp Y'.m m₂.toSABMap
  obtain ⟨n, hn⟩ := exists_sab_fac m k₁ hy
  obtain ⟨n', hn'⟩ := exists_sab_fac m' k₂ hy'
  obtain ⟨ν, hν⟩ := exists_sabMap_of_iso hL.globalFns n n'
    ⟨inferInstance, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩ ψ hact hb
  have hνw : ν.φ ≫ o'.t.G.hom = o.t.G.hom := ν.cart.1.w.trans (Category.comp_id _)
  have hψ : n.φ ≫ ψ.hom.left ≫ m'.φ = ν.φ ≫ m₂.toSABMap.φ ≫ Y'.m.φ := by
    rw [← e₂, hn', reassoc_of% hν]
  have key : ∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G)
      (x : 𝟙_ (Over (Sp K)) ⟶ o.t.G) (x' : 𝟙_ (Over (Sp K)) ⟶ o'.t.G),
      ((∃ v, σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨ ∃ v, σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v) →
      x.left ≫ m₁.toSABMap.φ = y ≫ σ.left → x'.left ≫ m₂.toSABMap.φ = y' ≫ σ'.left →
      x.left ≫ ν.φ = 𝟙 _ ≫ x'.left := by
    intro σ σ' x x' h hx hx'
    have b : x.left ≫ o.t.G.hom = 𝟙 _ := Over.w x
    have b' : x'.left ≫ o'.t.G.hom = 𝟙 _ := Over.w x'
    have q := hlev σ σ' h (x.left ≫ n.φ) (by rw [Category.assoc, n.cart.1.w, reassoc_of% b])
      (by rw [Category.assoc, ← hn, e₁, reassoc_of% hx])
    rw [Category.id_comp]
    apply k₂.cart.1.hom_ext
    · show (_ ≫ _) ≫ k₂.φ = _ ≫ k₂.φ
      rw [e₂, Category.assoc, ← hψ, reassoc_of% hx', ← q, Category.assoc]
    · rw [Category.assoc, hνw, b, b']
  let ν' : ObjMap o o' (𝟙 _) :=
    ⟨ν, fun a => key _ _ _ _ (Or.inr ⟨a, rfl, rfl⟩) (m₁.eta a) (m₂.eta a),
      fun a => key _ _ _ _ (Or.inl ⟨a, rfl, rfl⟩) (m₁.etaA a) (m₂.etaA a)⟩
  obtain ⟨p₁, f₁⟩ := ObjComp.objMap_comp Y.m0 m₁
  obtain ⟨p₀, f₀⟩ := ObjComp.objMap_comp m₂ ν'
  obtain ⟨p₂, f₂⟩ := ObjComp.objMap_comp Y'.m0 p₀
  have hf := (Xo.rep _ _ inferInstance o).unique ⟨Category.assoc _ _ _, ⟨p₁⟩⟩
    ⟨by rw [Category.id_comp, Category.assoc, hs'], ⟨p₂⟩⟩
  have hp : m₁.toSABMap.φ ≫ Y.m0.toSABMap.φ = (ν.φ ≫ m₂.toSABMap.φ) ≫ Y'.m0.toSABMap.φ :=
    f₁.symm.trans ((objMap_eq hL.serre hf p₁ p₂).trans (f₂.trans (congrArg (· ≫ _) f₀)))
  rw [Category.id_comp] at hf
  obtain rfl : y = y' := pullback.hom_ext hf hs
  refine ⟨rfl, fun T g g₁ g₂ τ h₁ h₂ h₃ h₄ h₅ => ?_⟩
  obtain ⟨u, u₁, u₂⟩ : ∃ u : T ⟶ o.t.G.left, u ≫ m₁.toSABMap.φ = g₁ ∧ u ≫ o.t.G.hom = τ :=
    ⟨m₁.cart.1.lift g₁ τ h₂, m₁.cart.1.lift_fst _ _ _, m₁.cart.1.lift_snd _ _ _⟩
  have a₁ : u ≫ n.φ = g := by
    apply m.cart.1.hom_ext
    · show (_ ≫ _) ≫ m.φ = _ ≫ m.φ
      rw [Category.assoc, ← hn, e₁, reassoc_of% u₁, h₃]
    · rw [Category.assoc, n.cart.1.w, reassoc_of% u₂, h₁]
  have a₂ : u ≫ ν.φ ≫ m₂.toSABMap.φ = g₂ := by
    apply Y'.m0.cart.1.hom_ext
    · show (_ ≫ _) ≫ Y'.m0.toSABMap.φ = _ ≫ Y'.m0.toSABMap.φ
      rw [Category.assoc, ← hp, reassoc_of% u₁, h₄]
    · rw [Category.assoc, Category.assoc, m₂.cart.1.w, reassoc_of% hνw, reassoc_of% u₂, ← h₅, h₂]
  rw [← a₁, ← a₂, Category.assoc, hψ, Category.assoc, Category.assoc]

end ArcObj

theorem arcWit_point_eq_of_iso : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ') (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre), ∀ (ψ : W.t.G ≅ W'.t.G) (bc : W.t.G ≅ (Over.pullback (specOf (RingHom.id (PowerSeries k)))).obj W'.t.G), IsMonHom ψ.hom → IsMonHom bc.hom → bc.hom.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k))) = ψ.hom.left → IsPullUnif (RingHom.id (PowerSeries k)) hD bc W'.P.U W.P.U → (∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) → ∀ (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c), y ≫ Y.j = jK (PowerSeries k) ≫ χ → y' ≫ Y'.j = jK (PowerSeries k) ≫ χ' → y ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → y' ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → (∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G), ((∃ v, σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨ ∃ v, σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v) → ∀ g : Sp (FractionRing (PowerSeries k)) ⟶ W.t.G.left, g ≫ W.t.G.hom = jK (PowerSeries k) → g ≫ W.m.φ = y ≫ σ.left ≫ Y.m.φ → g ≫ ψ.hom.left ≫ W'.m.φ = y' ≫ σ'.left ≫ Y'.m.φ) → y = y' ∧ (Mono Y.j → ∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left), g ≫ W.m.φ = g₁ ≫ Y.m.φ → g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ → g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom → g ≫ ψ.hom.left ≫ W'.m.φ = g₂ ≫ Y'.m.φ) := by
  intro hL _ E _ _ _ H D l Xo c k _ bF a O O' _ _ β β' Y Y' χ χ' W W' hD ψ bc hψ _ hbc hU hact y y' hy hy' hs hs' hlev
  have hb : LBIso W.t.PP.L (W'.t.PP.L.pull ψ.hom.left) := by
    obtain ⟨w, hw, -⟩ := hU.lg
    rw [← W.P.bundle, ← W'.P.bundle, ← hbc]
    exact ⟨w, hw⟩
  obtain ⟨e, h⟩ := ArcObj.point_eq hL W.m W'.m ψ hact hb _ y y' hy hy' (hs.trans hs'.symm) hlev
  refine ⟨e, fun hm T g g₁ g₂ h₁ h₂ h₃ => ?_⟩
  have := ThetaShiftProofs.isOpenImmersion_jK_powerSeries k
  have q : (g ≫ W.t.G.hom) ≫ χ = (g₁ ≫ Y.oF.t.G.hom) ≫ Y.j := by
    have h₁' : g ≫ W.m.cm.F = g₁ ≫ Y.m.cm.F := h₁
    rw [Category.assoc, ← W.m.cart.1.w, reassoc_of% h₁', Y.m.cart.1.w, Category.assoc]; rfl
  have hr : Set.range (g ≫ W.t.G.hom) ⊆ Set.range (jK (PowerSeries k)) := by
    rintro _ ⟨p, rfl⟩
    exact arcWit_mem_range_jK_of_mem_range_j E H D l Xo c k bF a O β Y χ W _
      ⟨(g₁ ≫ Y.oF.t.G.hom) p, congrArg (fun z => z p) q.symm⟩
  have hτ := IsOpenImmersion.lift_fac (jK (PowerSeries k)) _ hr
  refine h T g g₁ g₂ _ hτ.symm ?_ h₁ h₂ h₃
  rw [← cancel_mono Y.j, ← q, Category.assoc _ y, hy, ← Category.assoc _ (jK _), hτ]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqRankAddDimStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.unif_g_eq_rank_add_g : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => A.g = D.toPre.rank + D.toPre.P.g := by
  first | exact @GlobalTheory.UT.dim_eq_rank_add_dim | exact GlobalTheory.UT.dim_eq_rank_add_dim | (intros; apply GlobalTheory.UT.dim_eq_rank_add_dim <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOneOfFiniteOrderOfFixThreeTorsion
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.FiniteOrderFix

open TorsionZero in

theorem exists_sec_le {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp K) {L : LB X}
    (hL : L.IsLB) {N : ℕ} {σ : Type} (s : σ → (lbPow L N).Sec)
    (hcov : ⨆ i, nonzeroLocus (s i) = ⊤) (haff : ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (r : ∀ i, σ → Γ(X, nonzeroLocus (s i)))
    (hr : ∀ i j k, resG X (inf_le_right : nonzeroLocus (s i) ⊓ (lbPow L N).U k ≤ _) ((s j).f k) =
      resG X inf_le_left (r i j) * resG X inf_le_right ((s i).f k))
    (hgen : ∀ i (f : Γ(X, nonzeroLocus (s i))), ∃ F : MvPolynomial σ K,
      f = MvPolynomial.eval₂ (constHom p _) (r i) F)
    (U : X.Opens) (hU : genericPoint X ∈ U) :
    ∃ (d : ℕ) (u : (lbPow L (N * d)).Sec), (∃ j, u.f j ≠ 0) ∧
      ∀ z : Sp K ⟶ X, z ≫ p = 𝟙 _ → ⊤ ≤ z ⁻¹ᵁ nonzeroLocus u → ⊤ ≤ z ⁻¹ᵁ U := by
  obtain ⟨R, _, _, _, 𝒜, _, Φ, -, -, -, hρ⟩ := SectionRing.exists_sectionRing K X p L hL
  choose ρ hρc hρ using hρ
  obtain ⟨i, hi⟩ : ∃ i, genericPoint X ∈ nonzeroLocus (s i) :=
    TopologicalSpace.Opens.mem_iSup.1 (by rw [hcov]; trivial)
  letI : Algebra K Γ(X, nonzeroLocus (s i)) := (constHom p _).toAlgebra
  obtain ⟨h1, h2, -⟩ := chart_facts p Φ ρ hL hρc hρ s i hi (fun _ => rfl) (r i) (hr i) (fun f => by
    obtain ⟨F, hF⟩ := hgen i f
    exact ⟨F, hF.symm⟩)
  obtain ⟨f, hfU, hf⟩ := (haff i).exists_basicOpen_le ⟨_, hU⟩ hi
  obtain ⟨F, hF⟩ := hgen i f
  obtain ⟨n, G, hG, hGF⟩ := exists_homogenisation F i
  have hG' : (G * MvPolynomial.X i).IsHomogeneous (n + 1) := hG.mul (MvPolynomial.isHomogeneous_X K i)
  have hGf : MvPolynomial.aeval (r i) G = f := (hGF _ (r i) h1).trans hF.symm
  have hm := aeval_mem_of_isHomogeneous 𝒜 (fun j => (Φ N (s j)).2) hG'
  obtain ⟨u, hu⟩ := (Φ (N * (n + 1))).surjective ⟨_, hm⟩
  have hu' : (Φ _ u : R) = MvPolynomial.aeval (fun j => (Φ N (s j) : R)) (G * MvPolynomial.X i) :=
    congrArg Subtype.val hu
  refine ⟨n + 1, u, ?_, fun z hz hzu => ?_⟩
  · by_contra h0
    have h3 := eq_zero_of_not_mem Φ ρ hL hρ u fun h => by
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
      have e : u.f k = 0 := by_contra fun e => h0 ⟨k, e⟩
      rw [e, Scheme.basicOpen_zero] at hk
      exact hk
    have h4 := (h2 _ _ hG').1 (hu'.symm.trans h3)
    rw [map_mul, MvPolynomial.aeval_X, h1, _root_.mul_one, hGf] at h4
    rw [h4, Scheme.basicOpen_zero] at hf
    exact hf
  · obtain ⟨ev, hev, hevr⟩ := exists_ev p Φ ρ hL hρc hρ z hz
    have h3 := (hev _ u).2 hzu
    rw [hu', map_mul, map_mul, MvPolynomial.aeval_X, mul_ne_zero_iff] at h3
    have hzi := (hev _ (s i)).1 h3.2
    let v : Γ(X, nonzeroLocus (s i)) →ₐ[K] K :=
      { TorsionZero.val z _ hzi with commutes' := fun a => val_const p z hz _ hzi a }
    have h4 := h3.1
    rw [MvPolynomial.comp_aeval_apply, funext fun j => hevr N (s j) (s i) _ hzi (r i j) (hr i j),
      aeval_mul_of_isHomogeneous _ _ hG, mul_ne_zero_iff] at h4
    have h5 : v f ≠ 0 := by
      rw [← hGf, MvPolynomial.comp_aeval_apply]
      exact h4.1
    exact fun y hy => hfU ((val_ne_zero_iff z _ hzi f).1 h5 hy)

theorem eq_of_agree_on_pow_torsion (h : Laws) {K : Type} [Field K] [IsAlgClosed K] (P P' : PolAV (Sp K))
    {q : ℕ} (hq : 2 ≤ q) (hqK : (q : K) ≠ 0) (f f' : P.A ⟶ P'.A)
    (hf : ∀ (k : ℕ) (x : baseOver (Sp K) ⟶ P.A), x ^ q ^ k = 1 → x ≫ f = x ≫ f') : f = f' := by
  rcases Nat.eq_zero_or_pos P.g with hg | hg
  · exact EndOnTorsion.eq_of_dim_zero P P' hg _ _ (hf 0 1 (one_pow _))
  have := polAV_isIntegral_of_isAlgClosed K P
  have := P'.isAb.proper
  have hw : f.left ≫ P'.A.hom = f'.left ≫ P'.A.hom := (Over.w f).trans (Over.w f').symm
  have := isClosedImmersion_equalizer_ι_of_isSeparated P'.A.hom hw
  let U : P.A.left.Opens := ⟨(Set.range (equalizer.ι f.left f'.left))ᶜ,
    (equalizer.ι f.left f'.left).isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hU : genericPoint P.A.left ∉ U := fun hU => by
    obtain ⟨m, s, hcov, hs⟩ := veryAmple_lbPow h.ample K P 4 le_rfl
    choose haff r hr hgen using hs
    obtain ⟨d, u, hu, hz⟩ := exists_sec_le P.A.hom P.isLB s hcov haff r hr hgen U hU
    obtain ⟨k, hk⟩ : ∃ k, 4 ^ P.g * P.g.factorial * d < (q ^ k) ^ 2 :=
      ⟨_, (Nat.lt_pow_self hq).trans_le (Nat.le_self_pow two_ne_zero _)⟩
    have hM : ((q ^ k : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hqK
    have hM1 : 1 ≤ q ^ k := Nat.one_le_pow _ _ (by omega)
    have hcard := (h.mulN (Sp K) P _ hM1).2.2.2.2 K (𝟙 _) hM
    have h₄ := card_zeros_on_torsion_coset_le h.mulN SectionRing.exists_sectionRing
      (PowSec.exists_basis_sections h.globalSectionsRank) (veryAmple_lbPow h.ample) (exists_mulPull_sec h.mulPull)
      SmoothDim.ringKrullDim_affineOpen polAV_isIntegral_of_isAlgClosed isIntegral_adjoin_of_mul_pow_mem
      graded_bezout_bound K P 4 d (q ^ k) 1 hg le_rfl hM u hu
    have h₅ : ∀ x : baseOver (Sp K) ⟶ P.A, x ^ q ^ k = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ nonzeroLocus u :=
      fun x hx hx' => (TorsionZero.top_le_iff x.left _).1 (hz x.left (Over.w x) hx')
        (range_subset_range_equalizer_ι x.left (congrArg (·.left) (hf k x hx)) ⟨_, rfl⟩)
    have e : (q ^ k) ^ (2 * P.g) = (q ^ k) ^ 2 * (q ^ k) ^ (2 * P.g - 2) := by
      rw [← pow_add]; congr 1; omega
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => and_iff_left_of_imp (h₅ x)), hcard, e] at h₄
    exact absurd (Nat.le_of_mul_le_mul_right h₄ (pow_pos hM1 _)) (not_le.2 hk)
  have : IsDominant (equalizer.ι f.left f'.left) := ⟨dense_iff_closure_eq.2 (top_unique
    ((genericPoint_spec P.A.left).def.ge.trans (closure_mono (Set.singleton_subset_iff.2 (not_not.1 hU)))))⟩
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated P'.A.hom hw _ (equalizer.condition _ _))

open SerreField in

theorem eq_one_of_field (h : Laws) {K : Type} [Field K] [IsAlgClosed K] [CharZero K] (P : PolAV (Sp K))
    {M : ℕ} (hM : 3 ≤ M) (σ : CategoryTheory.End P.A) [hσ : IsMonHom (σ : P.A ⟶ P.A)] {m : ℕ} (hm : m ≠ 0)
    (hord : σ ^ m = 1) (hfix : ∀ x : baseOver (Sp K) ⟶ P.A, x ^ M = 1 → x ≫ σ = x) : σ = 1 := by
  have hdiv := DivisibleHom.exists_eq_pow_of_torsion_comp_eq_one (fun S _ P n hn =>
    ⟨(h.mulN S P n hn).1, (h.mulN S P n hn).2.1, (h.mulN S P n hn).2.2.1, (h.mulN S P n hn).2.2.2.1⟩)
  have hfix' := fix_torsion_of_fix_geometric_of_isDominant h.mulN P M (by omega) (by
    simpa using (Nat.cast_ne_zero.2 (by omega) : (M : K) ≠ 0).isUnit.map
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) (𝟙 _) σ hσ hfix
  let τ : P.A ⟶ P.A := σ
  have hu : IsMonHom (τ * (𝟙 P.A)⁻¹) := by
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  obtain ⟨⟨φ, hφ, e⟩, -⟩ := hdiv _ P P.A M (by omega) (τ * (𝟙 P.A)⁻¹) hu (fun T x hx => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hfix' T x hx, Category.comp_id, mul_inv_cancel])
  have hpow : ∀ (n : ℕ) (x : P.A ⟶ P.A), (toRing τ ^ n).1 (Additive.ofMul x) =
      Additive.ofMul (x ≫ (σ ^ n : CategoryTheory.End P.A)) := fun n x => by
    induction n with
    | zero => exact congrArg Additive.ofMul (Category.comp_id x).symm
    | succ n ih =>
      rw [pow_succ', pow_succ', End.mul_def, ← Category.assoc]
      exact (congrArg (toRing τ).1 ih).trans (toRing_apply _ _)
  have key : toRing τ = 1 := by
    refine eq_one_of_pow_eq_one_of_congr_one (homRing P.A) M hM ?_ ?_ (toRing τ) (toRing φ) m hm ?_ ?_
    · rintro k ⟨f, u, hu, hf⟩ hk e
      have h1 := congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) e
      simp only [natCast_mul_apply, hf, Category.id_comp] at h1
      have h2 : u ^ k = 1 := h1
      obtain ⟨_, _, _, -⟩ := h.mulN _ P k (by omega)
      have h3 : u = 1 := DivisibleHom.cancel_of_flat_surjective (mulA P.A k)
        (by rw [DivisibleHom.mulA_comp, h2, MonObj.comp_one])
      exact homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)
    · rintro q ⟨f, u, hu, hf⟩ hq e
      have h3 : u = 1 := eq_of_agree_on_pow_torsion h P P hq (Nat.cast_ne_zero.2 (by omega)) u 1
        fun k x hx => by
          obtain ⟨⟨g, v, hv, hg⟩, e⟩ := e k
          have h1 := congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) e
          simp only [← Nat.cast_pow, natCast_mul_apply, hf, hg, Category.id_comp] at h1
          have h2 : u = v ^ q ^ k := h1
          rw [h2, MonObj.comp_pow, ← MonObj.pow_comp, hx, MonObj.one_comp, MonObj.comp_one]
      exact homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)
    · refine homRing_ext ?_
      change _ = Additive.ofMul (𝟙 P.A) + ((M : homRing P.A) * toRing φ).1 _
      rw [natCast_mul_apply, toRing_apply, toRing_apply, Category.id_comp, Category.id_comp,
        ← ofMul_pow, ← e, ← ofMul_mul, mul_comm, inv_mul_cancel_right]
    · exact homRing_ext (by rw [hpow, hord, Category.id_comp]; rfl)
  have h1 := congrArg (fun g : homRing P.A => g.1 (Additive.ofMul (𝟙 P.A))) key
  simp only [toRing_apply, Category.id_comp] at h1
  exact h1

theorem eq_one_of_finite_order_of_fix_three_torsion :
    LL → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (p : Spec (CommRingCat.of F) ⟶ S) (h : CategoryTheory.End (Over.mk p ⊗ P.A)), h ≫ fst _ _ = fst _ _ → ptSecT P.A 1 ≫ h = ptSecT P.A 1 → (∃ n, 1 ≤ n ∧ h ^ n = 1) → (∀ x : Over.mk p ⟶ P.A, x ^ 3 = 1 → ptSecT P.A x ≫ h = ptSecT P.A x) → h = 1 := by
  rintro ⟨laws, -⟩ S _ P F _ _ _ p h hfst h0 ⟨n, hn, hord⟩ hfix
  obtain ⟨P', g, hg, -, pm, -⟩ := laws.polBaseChange S _ p P
  have hg' : IsPullback (snd (Over.mk p) P.A).left (fst (Over.mk p) P.A).left P.A.hom p :=
    (IsPullback.of_hasPullback p P.A.hom).flip
  let e := hg.isoIsPullback _ _ hg'
  have e₁ : e.hom ≫ (snd (Over.mk p) P.A).left = g := hg.isoIsPullback_hom_fst _ _ hg'
  have e₂ : e.hom ≫ (fst (Over.mk p) P.A).left = P'.A.hom := hg.isoIsPullback_hom_snd _ _ hg'
  have e₃ : h.left ≫ (fst (Over.mk p) P.A).left = (fst (Over.mk p) P.A).left := congrArg (·.left) hfst
  let σ : CategoryTheory.End P'.A := Over.homMk (e.hom ≫ h.left ≫ e.inv) (by
    rw [← e₂, Category.assoc, Category.assoc, e.inv_hom_id_assoc, e₃])
  have hσ : σ.left ≫ e.hom = e.hom ≫ h.left := by
    change (e.hom ≫ h.left ≫ e.inv) ≫ e.hom = _
    simp
  have hpow : ∀ k : ℕ, (σ ^ k).left ≫ e.hom = e.hom ≫ (h ^ k).left := fun k => by
    induction k with
    | zero => exact (Category.id_comp _).trans (Category.comp_id _).symm
    | succ k ih =>
      rw [pow_succ', pow_succ', End.mul_def, End.mul_def, Over.comp_left, Over.comp_left, Category.assoc, hσ,
        reassoc_of% ih]
  let c : Over.mk p ⟶ Over.mk ((baseOver (Sp F)).hom ≫ p) := Over.homMk (𝟙 _) (by simp)
  let ρ : (baseOver (Sp F) ⟶ P'.A) →* (Over.mk p ⟶ P.A) := MonoidHom.mk' (fun x => c ≫ toBase hg.w x)
    fun x y => by rw [pm, MonObj.comp_mul]
  have hρ : ∀ x, (ptSecT P.A (ρ x)).left = x.left ≫ e.hom := fun x => by
    refine hg'.hom_ext ?_ ?_
    · rw [← Over.comp_left, ptSecT, lift_snd, Category.assoc, e₁]
      exact Category.id_comp _
    · rw [← Over.comp_left, ptSecT, lift_fst, Category.assoc, e₂]
      exact (Over.w x).symm
  have key : ∀ x, ptSecT P.A (ρ x) ≫ h = ptSecT P.A (ρ x) → x ≫ σ = x := fun x hx => by
    have := congrArg (·.left) hx
    simp only [Over.comp_left, hρ] at this
    refine Over.OverMorphism.ext ((cancel_mono e.hom).1 ?_)
    rw [Over.comp_left, Category.assoc, hσ, ← Category.assoc, this]
  have hη : (1 : baseOver (Sp F) ⟶ P'.A) = η[P'.A] :=
    (congrArg (· ≫ η[P'.A]) toUnit_unit).trans (Category.id_comp _)
  have : IsMonHom (σ : P'.A ⟶ P'.A) := laws.rigidity _ _ _ P'.isAb P'.isAb σ (by
    have := key 1 (by rw [map_one]; exact h0)
    rwa [hη] at this)
  have h1 : σ = 1 := eq_one_of_field laws P' le_rfl σ (m := n) (by omega)
    (Over.OverMorphism.ext ((cancel_mono e.hom).1 ((hpow n).trans (by rw [hord]; exact (hpow 0).symm))))
    fun x hx => key x (hfix _ (by rw [← map_pow, hx, map_one]))
  refine Over.OverMorphism.ext ((cancel_epi e.hom).1 ?_)
  rw [← hσ, h1]
  exact hpow 0

end GlobalTheory.FiniteOrderFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenCubicalTrivialisationSpecialFibreStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_even_cubical_trivialisation_specialFibre : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (gen : (Over.pullback (jK V)).obj G ≅ A.A), IsMonHom gen.hom → ∀ (P : CP G) (w : G ⟶ G), IsMonHom w → LBIso P.L.L (cubeLB G ![𝟙 G, w] P.L.L) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Q₀ : TQ (thickObj V (maximalIdeal V) 0 G) X) (P₀ : CP (thickObj V (maximalIdeal V) 0 G)), IsLevelCP (maximalIdeal V) 0 P₀ P → ∃ σ : CubTriv P₀.c Q₀.i, σ.Even := by
  first | exact @GlobalTheory.EvenTriv.exists_even_cubTriv_specialFibre | exact GlobalTheory.EvenTriv.exists_even_cubTriv_specialFibre | (intros; apply GlobalTheory.EvenTriv.exists_even_cubTriv_specialFibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralThetaSectionWithExpansionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_theta_section_with_expansion : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∃ θ f, U.Theta θ f) := by
  first | exact @GlobalTheory.ThetaIntegral.exists_theta | exact GlobalTheory.ThetaIntegral.exists_theta | (intros; apply GlobalTheory.ThetaIntegral.exists_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLinearFourierJacobiExpansionFamilyStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_fourierJacobi_expansion_family : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∃ ex : ∀ α : D.X, EA A (jFK (R := V) F) k →ₗ[F] WB D F k α, (∀ t, U.ExpF F k t.sec (fun α => (ex α t).sec)) ∧ (∀ t s, U.ExpF F k t s → ∀ α, s α = (ex α (SecMod.mk _ t)).sec) ∧ (∀ t, (∀ α, ex α t = 0) → t = 0) ∧ ∀ α, (U.Supp F k α ↔ ex α ≠ 0)) := by
  first | exact @GlobalTheory.UU.ExpLinMap.exists_expansion_linear | exact GlobalTheory.UU.ExpLinMap.exists_expansion_linear | (intros; apply GlobalTheory.UU.ExpLinMap.exists_expansion_linear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionPrimitiveTwistTorusExtensionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_section_primitive_twist_torus_extension : GlobalFnsSt → ∀ (A : Type) [CommRing A] [IsLocalRing A] (X : Type) [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] (Q : TQ G X) (M : LB Q.B.left), M.IsLB → (∃ s : LB.Sec (M.pull Q.q.left), (∃ j, s.f j ≠ 0)) → ∃ O : LB Q.B.left, O.IsLB ∧ (∃ u : LB.Gen (abelian₂ Q.B O), u.IsGen) ∧ ∃ s : LB.Sec (LB.div M O), (∃ j, s.f j ≠ 0) := by
  first | exact @GlobalTheory.exists_sec_primitive_twist | exact GlobalTheory.exists_sec_primitive_twist | (intros; apply GlobalTheory.exists_sec_primitive_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijOfMatchStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expBij_of_match_of_fam_expF : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : PreU (IsLocalRing.maximalIdeal V) D.toPre A G) (U' : UnifPre (IsLocalRing.maximalIdeal V) D A G), Match U U' → ∀ k : ℕ, 1 ≤ k → U.FE (FractionRing V) k → (∀ s : Fam D.toPre (FractionRing V) k, ∃ t, U.ExpF (FractionRing V) k t s.s) → U'.ExpBij k := by
  first | exact @GlobalTheory.ExpansionClause.expBij_of_match | exact GlobalTheory.ExpansionClause.expBij_of_match | (intros; apply GlobalTheory.ExpansionClause.expBij_of_match <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InducedFrobeniusCompUniqueOriginStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indAt_comp_equiv_unique_id : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p p' p'' : QkPt D.toPre F N) (ψ ψ' : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)), IndAt U.toUnifPre F N p ψ → (IndAt U.toUnifPre F N p' ψ' → QkAdd p p' p'' → IndAt U.toUnifPre F N p'' (ψ ≫ ψ')) ∧ (QkPt.Equiv D.toPre F p p' → IndAt U.toUnifPre F N p' ψ) ∧ (4 ≤ N → IndAt U.toUnifPre F N p ψ' → ψ = ψ') ∧ (p'.y = 0 → p'.g.IsZero → IndAt U.toUnifPre F N p' (𝟙 _)) := by
  first | exact @GlobalTheory.UT.IndComp.indAt_comp_unique | exact GlobalTheory.UT.IndComp.indAt_comp_unique | (intros; apply GlobalTheory.UT.IndComp.indAt_comp_unique <;> assumption)
end

