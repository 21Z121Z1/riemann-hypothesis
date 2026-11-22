import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2500
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoGenResMapSmulHom

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleFamilyUniqueIso
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTest.FlagUniq

variable {B Y : Scheme.{0}} {ι : Type} {E : ι → B.Modules} {n : ι → ℕ}

def Carries {T : Scheme.{0}} (π : Y ⟶ B) (g : T ⟶ B) (h : T ⟶ Y) (w : h ≫ π = g)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a))
    (flT : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (n a)) : Prop :=
  ∀ a i, ∃ e : (Scheme.Modules.pullback h).obj ((fl a).F i) ≅ (flT a).F i,
    e.hom ≫ (flT a).ι i = (Scheme.Modules.pullback h).map ((fl a).ι i) ≫
      (Scheme.Modules.pullbackComp h π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E a)

theorem carries_id (π : Y ⟶ B) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) :
    Carries π π (𝟙 Y) (Category.id_comp π) fl fl := by
  intro a i
  refine ⟨(Scheme.Modules.pullbackId Y).app ((fl a).F i), ?_⟩
  have h1 : (Scheme.Modules.pullback (𝟙 Y)).map ((fl a).ι i) ≫
      (Scheme.Modules.pullbackId Y).hom.app ((Scheme.Modules.pullback π).obj (E a)) =
      (Scheme.Modules.pullbackId Y).hom.app ((fl a).F i) ≫ (fl a).ι i :=
    (Scheme.Modules.pullbackId Y).hom.naturality ((fl a).ι i)
  have h2 := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality π) (E a)
  simp at h2
  simp only [Iso.app_hom, Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app]
  rw [← h1, ← h2, Iso.hom_inv_id_app_assoc]

theorem carries_comp {T Y' : Scheme.{0}} (π : Y ⟶ B) (π' : Y' ⟶ B) (g : T ⟶ B) (h₁ : T ⟶ Y') (h₂ : Y' ⟶ Y)
    (w₁ : h₁ ≫ π' = g) (w₂ : h₂ ≫ π = π')
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a))
    (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback π').obj (E a)) (n a))
    (flT : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (n a))
    (c₁ : Carries π' g h₁ w₁ fl' flT) (c₂ : Carries π π' h₂ w₂ fl fl') :
    Carries π g (h₁ ≫ h₂) (by rw [Category.assoc, w₂, w₁]) fl flT := by
  subst w₁ w₂
  intro a i
  obtain ⟨e₁, he₁⟩ := c₁ a i
  obtain ⟨e₂, he₂⟩ := c₂ a i
  refine ⟨(Scheme.Modules.pullbackComp h₁ h₂).symm.app _ ≪≫ (Scheme.Modules.pullback h₁).mapIso e₂ ≪≫ e₁, ?_⟩
  have h3 := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity h₁ h₂ π) (E a)
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc, he₁] at h3 ⊢
  rw [← Functor.map_comp_assoc, he₂]
  simp [Scheme.Modules.pullbackCongr] at h3 ⊢
  have hn : (Scheme.Modules.pullbackComp h₁ h₂).inv.app ((fl a).F i) ≫
      (Scheme.Modules.pullback h₁).map ((Scheme.Modules.pullback h₂).map ((fl a).ι i)) =
      (Scheme.Modules.pullback (h₁ ≫ h₂)).map ((fl a).ι i) ≫
        (Scheme.Modules.pullbackComp h₁ h₂).inv.app ((Scheme.Modules.pullback π).obj (E a)) :=
    ((Scheme.Modules.pullbackComp h₁ h₂).inv.naturality ((fl a).ι i)).symm
  rw [reassoc_of% hn]
  congr 1
  have h4 := congrArg (fun f => (Scheme.Modules.pullbackComp h₁ h₂).inv.app ((Scheme.Modules.pullback π).obj (E a)) ≫
    (Scheme.Modules.pullback h₁).map ((Scheme.Modules.pullbackComp h₂ π).hom.app (E a)) ≫
    (Scheme.Modules.pullbackComp h₁ (h₂ ≫ π)).hom.app (E a) ≫ f ≫ eqToHom (by rw [Category.assoc])) h3
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.inv_hom_id_app_assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] at h4
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc] at h4
  exact h4.symm

end GlobalTheory.CovTest.FlagUniq

open GlobalTheory.CovTest.FlagUniq in

theorem GlobalTheory.CovTest.flagBundle_iso_over : ∀ (B Y Y' : Scheme.{0}) (π : Y ⟶ B) (π' : Y' ⟶ B) (ι : Type) (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback π').obj (E a)) (r a)), IsFlagBundle π E r fl → IsFlagBundle π' E r fl' → ∃ e : Y ≅ Y', e.hom ≫ π' = π := by
  intro B Y Y' π π' ι E r fl fl' h h'
  obtain ⟨g₁, ⟨w₁, c₁⟩, -⟩ := h' Y π fl
  obtain ⟨g₂, ⟨w₂, c₂⟩, -⟩ := h Y' π' fl'
  obtain ⟨u, -, hu⟩ := h Y π fl
  obtain ⟨u', -, hu'⟩ := h' Y' π' fl'
  have e₁ : g₁ ≫ g₂ = 𝟙 Y :=
    (hu _ ⟨_, carries_comp π π' π g₁ g₂ w₁ w₂ fl fl' fl c₁ c₂⟩).trans (hu _ ⟨_, carries_id π fl⟩).symm
  have e₂ : g₂ ≫ g₁ = 𝟙 Y' :=
    (hu' _ ⟨_, carries_comp π' π π' g₂ g₁ w₂ w₁ fl' fl fl' c₂ c₁⟩).trans (hu' _ ⟨_, carries_id π' fl'⟩).symm
  exact ⟨⟨g₁, g₂, e₁, e₂⟩, w₁⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointFlagsUniqueFlagCoverPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag

open GlobalTheory.FlagMod (FlagCover Frames frX frVec)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open GlobalTheory.Toroidal (gen genι genStr)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)

theorem tv_vecAt_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X}
    (F : Frames Y π) {S : Type} [CommRing S] (k : F.J) (z : Sp S ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) {x : Sp S ⟶ Y.X}
    (hx : z ≫ π = x) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    (tv (F.vecAt k z hz hx σ i)).left = (tv (F.vecAt k z hz rfl σ i)).left := by
  subst hx
  rfl

theorem exists_gen_unit {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (Q Q' : FrPt Xo c S)
    (e : Q'.x = Q.x) : ∃ u : Sˣ, ∀ e : Q'.x = Q.x, ∀ i, (e ▸ Q'.s).f i = scal Q.x (u : S) i * Q.s.f i := by
  obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := Q'
  dsimp only at e
  subst e
  obtain ⟨u0, hu0⟩ := gen_unit Q.s s' Q.gen t4'
  exact ⟨u0, fun _ => hu0⟩

theorem rel_unique : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : GlobalTheory.FlagMod.FlagCover Y) (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.FramesExist X → GlobalTheory.VarFlag.CarriesTri C → ∀ (K : Type) [Field K] (z z' : Sp K ⟶ X.YY) (p : Sp K ⟶ C.Y.X), (∀ s, p s ∈ GlobalTheory.VarFlag.Vo C) → GlobalTheory.VarFlag.Rel X.F C z p → GlobalTheory.VarFlag.Rel X.F C z' p → z = z' := by
  intro E _ _ _ H Dw l Xo c Y X C _ hC K _ z z' p hp hr hr'
  obtain ⟨φ, k, hk, g, hφ, hg, hc⟩ := hr
  obtain ⟨φ', k', hk', g', hφ', hg', hc'⟩ := hr'
  have e1 : p ≫ C.π ≫ genι Y = z ≫ X.π := carries_over C hc
  have e2 : p ≫ C.π ≫ genι Y = z' ≫ X.π := carries_over C hc'
  have hπ : z' ≫ X.π = z ≫ X.π := e2.symm.trans e1
  have ephi : φ' = φ := by
    have h0 : spMap φ' = spMap φ := by rw [← hφ', ← hφ, ← Category.assoc, hπ, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h0)
  subst ephi
  obtain ⟨g0, hg0⟩ : ∃ g0 : EigFrame Y φ' (z ≫ X.π), ∀ τ i, g0.v τ i = g'.v τ i := by
    rw [← hπ]; exact ⟨g', fun _ _ => rfl⟩
  have hc0 : C.Carries p g0 := (carries_congr C hπ.symm g0 g' hg0 p).2 hc'
  obtain ⟨t, ht⟩ := hC K _ _ (z ≫ X.π) p g g0 hc hc0
  letI : Algebra c.F K := φ'.toAlgebra
  have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  have hxg : (p ≫ C.π) ≫ genι Y = z ≫ X.π := by rw [Category.assoc]; exact e1
  have hr : Set.range (p ≫ C.π) ⊆ Set.range Y.jQ := by
    rintro _ ⟨a, rfl⟩
    have := hp a
    rw [Scheme.Hom.comp_apply]
    exact this
  have := Y.jQ_open
  let y := IsOpenImmersion.lift Y.jQ (p ≫ C.π) hr
  have hy0 : y ≫ Y.jQ = p ≫ C.π := IsOpenImmersion.lift_fac _ _ _
  have hyj : z ≫ X.π = y ≫ Y.j := by
    rw [Model.j, ← Category.assoc, hy0, ← hxg]
  have hstr : genStr Y = genι Y ≫ Y.s := by
    calc genStr Y = genStr Y ≫ spMap (RingHom.id c.F) := by rw [hid, Category.comp_id]
      _ = genι Y ≫ Y.s := (pullback.condition (f := Y.s) (g := spMap (RingHom.id c.F))).symm
  have hy : y ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := by
    rw [← Y.jQ_over, ← Category.assoc, hy0]
    show (p ≫ C.π) ≫ genStr Y = _
    rw [hstr, ← Category.assoc, hxg, Category.assoc]
    exact hφ
  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr hy hyj k hk
  obtain ⟨Q', hQ'⟩ := X.top.exists_chartFr hy (hπ.trans hyj) k' hk'
  have hx : frX Q ≫ Y.j = z ≫ X.π := hQ.over
  have hx' : frX Q' ≫ Y.j = z ≫ X.π := hQ'.over.trans hπ
  have eQ : Q'.x = Q.x := by
    rw [← GlobalTheory.FlagMod.frX_fst, ← GlobalTheory.FlagMod.frX_fst,
      GlobalTheory.FlagMod.xF_ext (Y := Y) (GlobalTheory.FlagMod.frX_snd Q') (GlobalTheory.FlagMod.frX_snd Q) (hx'.trans hx.symm)]
  obtain ⟨u0, hu0⟩ := exists_gen_unit Q Q' eQ
  choose cf hcf1 hcf2 hcf3 using ht.2.2
  have h1 : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  let T : Ix Dw → Kˣ := fun ix => match ix with | none => u0 | some q => t q.1 q.2
  have hB : FrBor T Q Q' := by
    refine GlobalTheory.FlagMod.frBor_of_frVec (X.F.inM hk rfl) hx hx' T (fun σ j i => cf σ i j)
      (fun σ r s hrs => hcf2 σ s r hrs) (fun σ i => hcf1 σ i) (fun σ i => ?_) hu0
    rw [hQ'.frVec_eq hπ hx', hQ.frVec_eq rfl hx]
    refine (GlobalTheory.LieMet.isComb_iff _ _ _).1 ?_
    have h3 := hcf3 σ i
    simp only [h1, Category.id_comp] at h3
    rw [hg0 σ i, hg' σ i, ← tv_vecAt_congr X.F k' z' hk' hπ σ i] at h3
    have e : (fun j => g.v σ j) = fun j => (tv (X.F.vecAt k z hk rfl σ j)).left := funext (hg σ)
    rw [e] at h3
    exact h3
  exact (X.rep K Q').unique (hQ.lies.frBor hB) hQ'.lies

end GlobalTheory.VarFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.FlagFamily

open Limits

theorem isProjOver_pullback_over {k : Type} [CommRing k] {B X Y : Scheme.{0}} {q : B ⟶ Sp k} (hq : IsProjOver q)
    {f : X ⟶ B} {g : Y ⟶ B} (hf : IsProjOver (f ≫ q)) (hg : IsProjOver (g ≫ q)) :
    IsProjOver (pullback.fst f g ≫ f ≫ q) := by
  have : IsProper q := projProper k B q hq
  have h := ProjSpace.isProjOver_comp_of_isClosedImmersion (pullback.mapDesc f g q)
    (ProjSpace.isProjOver_pullback hf hg)
  rwa [pullback.lift_fst_assoc, Category.comp_id] at h

theorem exists_widePullback {k : Type} [CommRing k] {B : Scheme.{0}} {q : B ⟶ Sp k} (hq : IsProjOver q)
    (ι : Type) [Finite ι] : ∀ (Z : ι → Scheme.{0}) (ρ : ∀ a, Z a ⟶ B), (∀ a, IsProjOver (ρ a ≫ q)) →
      ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (p : ∀ a, Y ⟶ Z a), (∀ a, p a ≫ ρ a = π) ∧ IsProjOver (π ≫ q) ∧
        ∀ (T : Scheme.{0}) (g : T ⟶ B) (h : ∀ a, T ⟶ Z a), (∀ a, h a ≫ ρ a = g) →
          ∃! g' : T ⟶ Y, g' ≫ π = g ∧ ∀ a, g' ≫ p a = h a := by
  induction ι using Finite.induction_empty_option with
  | @of_equiv α β e ih =>
    intro Z ρ hρ
    obtain ⟨Y, π, p, hp, hY, H⟩ := ih (fun a => Z (e a)) (fun a => ρ (e a)) fun a => hρ _
    let p' : ∀ b, Y ⟶ Z b := Equiv.piCongrLeft (fun b => Y ⟶ Z b) e p
    have hp' (a : α) : p' (e a) = p a := Equiv.piCongrLeft_apply_apply _ _ _ _
    refine ⟨Y, π, p', e.forall_congr_right.1 fun a => by rw [hp', hp], hY, fun T g h hh => ?_⟩
    obtain ⟨g', ⟨h₁, h₂⟩, u⟩ := H T g (fun a => h (e a)) fun a => hh _
    exact ⟨g', ⟨h₁, e.forall_congr_right.1 fun a => by rw [hp', h₂]⟩,
      fun y hy => u y ⟨hy.1, fun a => by rw [← hp', hy.2]⟩⟩
  | h_empty =>
    intro Z ρ _
    exact ⟨B, 𝟙 B, fun a => a.elim, fun a => a.elim, by rwa [Category.id_comp],
      fun T g _ _ => ⟨g, ⟨Category.comp_id g, fun a => a.elim⟩, fun y hy => (Category.comp_id y).symm.trans hy.1⟩⟩
  | @h_option α _ ih =>
    intro Z ρ hρ
    obtain ⟨Y, π, p, hp, hY, H⟩ := ih (fun a => Z (some a)) (fun a => ρ (some a)) fun a => hρ _
    refine ⟨pullback π (ρ none), pullback.fst _ _ ≫ π,
      fun a => Option.rec (pullback.snd _ _) (fun a => pullback.fst _ _ ≫ p a) a, ?_,
      by simpa only [Category.assoc] using isProjOver_pullback_over hq hY (hρ none), fun T g h hh => ?_⟩
    · rintro (_ | a)
      · exact pullback.condition.symm
      · exact (Category.assoc _ _ _).trans (congrArg _ (hp a))
    · obtain ⟨g', ⟨h₁, h₂⟩, u⟩ := H T g (fun a => h (some a)) fun a => hh _
      refine ⟨pullback.lift g' (h none) (h₁.trans (hh none).symm), ⟨by rw [pullback.lift_fst_assoc, h₁], ?_⟩,
        fun y hy => ?_⟩
      · rintro (_ | a)
        · exact pullback.lift_snd _ _ _
        · exact (pullback.lift_fst_assoc _ _ _ _).trans (h₂ a)
      · refine pullback.hom_ext ?_ ?_
        · rw [pullback.lift_fst]
          exact u _ ⟨(Category.assoc _ _ _).trans hy.1, fun a => (Category.assoc _ _ _).trans (hy.2 (some a))⟩
        · rw [pullback.lift_snd]
          exact hy.2 none

def compIso {X Y B : Scheme.{0}} (p : X ⟶ Y) (ρ : Y ⟶ B) {π : X ⟶ B} (w : p ≫ ρ = π) (E : B.Modules) :
    (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback ρ).obj E) ≅ (Scheme.Modules.pullback π).obj E :=
  (Scheme.Modules.pullbackComp p ρ).app E ≪≫ (Scheme.Modules.pullbackCongr w).app E

theorem compIso_assoc {T X Y B : Scheme.{0}} (t : T ⟶ X) (p : X ⟶ Y) (ρ : Y ⟶ B) {π : X ⟶ B} (w : p ≫ ρ = π)
    {g : T ⟶ B} (w' : t ≫ π = g) (w'' : (t ≫ p) ≫ ρ = g) (E : B.Modules) :
    (Scheme.Modules.pullback t).map (compIso p ρ w E).hom ≫ (compIso t π w' E).hom =
      (Scheme.Modules.pullbackComp t p).hom.app _ ≫ (compIso (t ≫ p) ρ w'' E).hom := by
  subst w w'
  have h := Scheme.Modules.pseudofunctor_associativity t p ρ
  rw [Iso.inv_comp_eq, ← Functor.isoWhiskerRight_inv, Iso.inv_comp_eq] at h
  have h' := congrArg (fun φ => φ.app E) h
  simp [compIso, Scheme.Modules.pullbackCongr] at h' ⊢
  simpa using h'.symm

def Induces {T Y B : Scheme.{0}} (t : T ⟶ Y) (π : Y ⟶ B) {g : T ⟶ B} (w : t ≫ π = g) {E : B.Modules} {n : ℕ}
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n) (fl' : Vert.Flag ((Scheme.Modules.pullback g).obj E) n) : Prop :=
  ∀ i, ∃ e : (Scheme.Modules.pullback t).obj (fl.F i) ≅ fl'.F i,
    e.hom ≫ fl'.ι i = (Scheme.Modules.pullback t).map (fl.ι i) ≫ (compIso t π w E).hom

theorem Induces.congr {T Y B : Scheme.{0}} {t t' : T ⟶ Y} {π : Y ⟶ B} {g : T ⟶ B} {w : t ≫ π = g} {E : B.Modules} {n : ℕ}
    {fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n} {fl' : Vert.Flag ((Scheme.Modules.pullback g).obj E) n}
    (h : Induces t π w fl fl') (e : t = t') (w' : t' ≫ π = g) : Induces t' π w' fl fl' := by
  subst e
  exact h

theorem induces_pull_iff {T X Y B : Scheme.{0}} (t : T ⟶ X) (p : X ⟶ Y) (ρ : Y ⟶ B) {π : X ⟶ B} (w : p ≫ ρ = π)
    {g : T ⟶ B} (w' : t ≫ π = g) (w'' : (t ≫ p) ≫ ρ = g) {E : B.Modules} {n : ℕ}
    (fl : Vert.Flag ((Scheme.Modules.pullback ρ).obj E) n) (fl' : Vert.Flag ((Scheme.Modules.pullback g).obj E) n) :
    Induces t π w' ((fl.pull p).ofIso (compIso p ρ w E)) fl' ↔ Induces (t ≫ p) ρ w'' fl fl' := by
  refine forall_congr' fun i => ?_
  have key : (Scheme.Modules.pullback t).map ((Scheme.Modules.pullback p).map (fl.ι i) ≫ (compIso p ρ w E).hom) ≫
      (compIso t π w' E).hom = (Scheme.Modules.pullbackComp t p).hom.app (fl.F i) ≫
        (Scheme.Modules.pullback (t ≫ p)).map (fl.ι i) ≫ (compIso (t ≫ p) ρ w'' E).hom := by
    rw [Functor.map_comp, Category.assoc, compIso_assoc t p ρ w w' w'',
      ← (Scheme.Modules.pullbackComp t p).hom.naturality_assoc]
    rfl
  constructor
  · rintro ⟨e, he⟩
    refine ⟨((Scheme.Modules.pullbackComp t p).app (fl.F i)).symm ≪≫ e, ?_⟩
    rw [Iso.trans_hom, Category.assoc, Iso.symm_hom, Iso.inv_comp_eq]
    exact he.trans key
  · rintro ⟨e, he⟩
    refine ⟨(Scheme.Modules.pullbackComp t p).app (fl.F i) ≪≫ e, ?_⟩
    rw [Iso.trans_hom, Category.assoc, he]
    exact key.symm

theorem isFlagBundle_of_widePullback {B Y : Scheme.{0}} {ι : Type} (E : ι → B.Modules) (r : ι → ℕ)
    {Z : ι → Scheme.{0}} (ρ : ∀ a, Z a ⟶ B)
    (fl : ∀ a, Unit → Vert.Flag ((Scheme.Modules.pullback (ρ a)).obj (E a)) (r a))
    (hfl : ∀ a, IsFlagBundle (ρ a) (fun _ : Unit => E a) (fun _ => r a) (fl a))
    (π : Y ⟶ B) (p : ∀ a, Y ⟶ Z a) (hp : ∀ a, p a ≫ ρ a = π)
    (H : ∀ (T : Scheme.{0}) (g : T ⟶ B) (h : ∀ a, T ⟶ Z a), (∀ a, h a ≫ ρ a = g) →
      ∃! g' : T ⟶ Y, g' ≫ π = g ∧ ∀ a, g' ≫ p a = h a) :
    IsFlagBundle π E r fun a => ((fl a ()).pull (p a)).ofIso (compIso (p a) (ρ a) (hp a) (E a)) := by
  intro T g fl'
  have h₀ (a : ι) : ∃! h : T ⟶ Z a, ∃ w : h ≫ ρ a = g, ∀ _ : Unit, Induces h (ρ a) w (fl a ()) (fl' a) :=
    hfl a T g fun _ => fl' a
  choose h hh u using h₀
  choose w hw using hh
  obtain ⟨g', ⟨h₁, h₂⟩, u'⟩ := H T g h w
  have w₂ (y : T ⟶ Y) (hy : y ≫ π = g) (a : ι) : (y ≫ p a) ≫ ρ a = g := by rw [Category.assoc, hp, hy]
  refine ⟨g', ⟨h₁, fun a => ?_⟩, fun y ⟨hy, hy'⟩ => u' y ⟨hy, fun a => u a _ ⟨w₂ y hy a, fun _ => ?_⟩⟩⟩
  · refine (induces_pull_iff g' (p a) (ρ a) (hp a) h₁ (w₂ g' h₁ a) (fl a ()) (fl' a)).2 ?_
    exact (hw a ()).congr (h₂ a).symm _
  · exact (induces_pull_iff y (p a) (ρ a) (hp a) hy (w₂ y hy a) (fl a ()) (fl' a)).1 (hy' a)

theorem exists_isFlagBundle_isProjOver : ∀ (k : Type) [CommRing k] (B : Scheme.{0}) (q : B ⟶ Sp k) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ), IsProjOver q → (∀ a, ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ _ : Unit, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), GlobalTheory.CovTest.IsFlagBundle π (fun _ : Unit => E a) (fun _ => r a) fl ∧ IsProjOver (π ≫ q)) → ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ a, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), GlobalTheory.CovTest.IsFlagBundle π E r fl ∧ IsProjOver (π ≫ q) := by
  intro k _ B q ι _ E r hq h
  choose Z ρ fl hfl hρ using h
  obtain ⟨Y, π, p, hp, hY, H⟩ := exists_widePullback hq ι Z ρ hρ
  exact ⟨Y, π, _, isFlagBundle_of_widePullback E r ρ fl hfl π p hp H, hY⟩

end GlobalTheory.FlagFamily
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProjectionSurjective
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false

noncomputable section

open Limits GlobalTheory.QCoh

namespace GlobalTheory.FlagSurj

variable {X : Scheme.{0}}

theorem freeMap_comp {I J K : Type} (f : I → J) (g : J → K) :
    SheafOfModules.freeMap (R := X.ringCatSheaf) f ≫ SheafOfModules.freeMap g =
      SheafOfModules.freeMap (g ∘ f) := by
  have := (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).map_comp (↾f) (↾g)
  simp only [SheafOfModules.freeFunctor_map] at this
  exact this.symm

theorem freeMap_id (I : Type) :
    SheafOfModules.freeMap (R := X.ringCatSheaf) (id : I → I) = 𝟙 _ := by
  have := (SheafOfModules.freeFunctor (R := X.ringCatSheaf)).map_id I
  simp only [SheafOfModules.freeFunctor_map] at this
  exact this

def finSplit {i r : ℕ} (h : i ≤ r) : Fin i ⊕ Fin (r - i) ≃ Fin r :=
  finSumFinEquiv.trans (finCongr (by omega))

def freeIso {I J : Type} (e : I ≃ J) :
    SheafOfModules.free (R := X.ringCatSheaf) I ≅ SheafOfModules.free J where
  hom := SheafOfModules.freeMap e
  inv := SheafOfModules.freeMap e.symm
  hom_inv_id := by rw [freeMap_comp]; simpa using freeMap_id I
  inv_hom_id := by rw [freeMap_comp]; simpa using freeMap_id J

variable (X) in

def splitIso {i r : ℕ} (h : i ≤ r) : freeModule X (Fin i) ⊞ freeModule X (Fin (r - i)) ≅ freeModule X (Fin r) :=
  biprod.isoCoprod _ _ ≪≫ SheafOfModules.freeSumIso _ _ ≪≫ freeIso (finSplit h)

theorem inl_splitIso_hom {i r : ℕ} (h : i ≤ r) :
    biprod.inl ≫ (splitIso X h).hom = SheafOfModules.freeMap (R := X.ringCatSheaf) (Fin.castLE h) := by
  simp only [splitIso, Iso.trans_hom]
  erw [biprod_isoCoprod_hom, biprod.inl_desc_assoc, SheafOfModules.inl_freeSumIso_hom_assoc]
  erw [freeMap_comp]
  congr 1
  all_goals (funext x; ext; simp [finSplit])

theorem isSubbundle_comp_iso {F G H : X.Modules} {i : G ⟶ F} (hi : IsSubbundle i) (e : F ≅ H) :
    IsSubbundle (i ≫ e.hom) :=
  have := hi.mono
  have ⟨_, s, hs⟩ := hi
  ⟨inferInstance, s, hs.of_iso (cokernelCompIsIso _ _).symm⟩

variable (X) in

theorem isSubbundle_freeMap_castLE {i r : ℕ} (h : i ≤ r) :
    IsSubbundle (SheafOfModules.freeMap (R := X.ringCatSheaf) (Fin.castLE h)) := by
  rw [← inl_splitIso_hom]
  exact isSubbundle_comp_iso (isSubbundle_inl (F := freeModule X (Fin i)) (isVB_freeModule_fin X (r - i))) _

variable (X) in

def freeFlag (r : ℕ) : Vert.Flag (freeModule X (Fin r)) r where
  F i := freeModule X (Fin i)
  ι i := SheafOfModules.freeMap (Fin.castLE (Nat.lt_succ_iff.mp i.2))
  isSubbundle i := isSubbundle_freeMap_castLE X _
  isVB i := isVB_freeModule_fin X i
  step i := SheafOfModules.freeMap (Fin.castLE (by simp))
  step_ι i := (freeMap_comp (X := X) _ _).trans rfl
  isIso_last := by
    have h : SheafOfModules.freeMap (R := X.ringCatSheaf) (Fin.castLE (le_refl r)) = 𝟙 _ := freeMap_id _
    exact h ▸ inferInstance

theorem isFlagBundle_surjective : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules)
    (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)),
    (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → Function.Surjective π := by
  intro B Y π ι _ E r fl hE hfl b
  choose U e hb he using fun a => hE a b
  let V : B.Opens := Finset.univ.inf U
  have hle : ∀ a, V ≤ U a := fun a => Finset.inf_le (Finset.mem_univ a)
  have hbV : b ∈ V := by
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_finset_inf]
    simpa using hb
  have hfr (a : ι) := (isFrame_restrict_iff V.ι _).2 ((he a).res ((V.ι_image_le ⊤).trans (hle a)))
  let φ : ∀ a, freeModule V.toScheme (Fin (r a)) ≅ (Scheme.Modules.pullback V.ι).obj (E a) := fun a =>
    (isFrame_freeFrame _ _).iso (hfr a) ≪≫ (Scheme.Modules.restrictFunctorIsoPullback V.ι).app (E a)
  obtain ⟨g', ⟨w, -⟩, -⟩ := hfl V.toScheme V.ι (fun a => (freeFlag V.toScheme (r a)).ofIso (φ a))
  refine ⟨g' ⟨b, hbV⟩, ?_⟩
  have h : (g' ≫ π) ⟨b, hbV⟩ = V.ι ⟨b, hbV⟩ := by rw [w]
  exact (Scheme.Hom.comp_apply g' π _).symm.trans (h.trans (Scheme.Opens.ι_apply V _))

end GlobalTheory.FlagSurj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleTransportIso
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false

namespace GlobalTheory.CovTest

open CategoryTheory AlgebraicGeometry

theorem isFlagBundle_cond_iso {B Y T : Scheme.{0}} (π : Y ⟶ B) {ι : Type} (E E' : ι → B.Modules) (r : ι → ℕ)
    (e : ∀ a, E a ≅ E' a) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a))
    (g : T ⟶ B) (fl'' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E' a)) (r a))
    (y : T ⟶ Y) (w : y ≫ π = g) :
    (∀ a i, ∃ e0 : (Scheme.Modules.pullback y).obj ((fl a).F i) ≅
        ((fl'' a).ofIso ((Scheme.Modules.pullback g).mapIso (e a)).symm).F i,
      e0.hom ≫ ((fl'' a).ofIso ((Scheme.Modules.pullback g).mapIso (e a)).symm).ι i =
        (Scheme.Modules.pullback y).map ((fl a).ι i) ≫
          (Scheme.Modules.pullbackComp y π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E a)) ↔
    (∀ a i, ∃ e0 : (Scheme.Modules.pullback y).obj (((fl a).ofIso ((Scheme.Modules.pullback π).mapIso (e a))).F i) ≅
        (fl'' a).F i,
      e0.hom ≫ (fl'' a).ι i =
        (Scheme.Modules.pullback y).map (((fl a).ofIso ((Scheme.Modules.pullback π).mapIso (e a))).ι i) ≫
          (Scheme.Modules.pullbackComp y π).hom.app (E' a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E' a)) := by
  have nat : ∀ a, (Scheme.Modules.pullback y).map ((Scheme.Modules.pullback π).map (e a).hom) ≫
      (Scheme.Modules.pullbackComp y π).hom.app (E' a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E' a) =
      (Scheme.Modules.pullbackComp y π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E a) ≫
        (Scheme.Modules.pullback g).map (e a).hom := by
    intro a
    rw [← Category.assoc, ← Functor.comp_map, (Scheme.Modules.pullbackComp y π).hom.naturality (e a).hom,
      Category.assoc, (Scheme.Modules.pullbackCongr w).hom.naturality (e a).hom]
  constructor
  · intro h a i
    obtain ⟨e0, he⟩ := h a i
    refine ⟨e0, ?_⟩
    have he' := congrArg (· ≫ (Scheme.Modules.pullback g).map (e a).hom) he
    simp only [Vert.Flag.ofIso, Iso.symm_hom, Functor.mapIso_inv, Category.assoc] at he'
    rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id] at he'
    simp only [Vert.Flag.ofIso, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    rw [nat a]
    exact he'
  · intro h a i
    obtain ⟨e0, he⟩ := h a i
    refine ⟨e0, ?_⟩
    simp only [Vert.Flag.ofIso, Functor.mapIso_hom, Functor.map_comp, Category.assoc] at he
    rw [nat a] at he
    simp only [Vert.Flag.ofIso, Iso.symm_hom, Functor.mapIso_inv]
    rw [← Category.assoc, he]
    simp only [Category.assoc]
    rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]

theorem isFlagBundle_of_iso : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (E E' : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → (∀ a, Nonempty (E a ≅ E' a)) → ∃ fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E' a)) (r a), IsFlagBundle π E' r fl' := by
  intro B Y π ι E E' r fl hfl he
  have e : ∀ a, E a ≅ E' a := fun a => (he a).some
  refine ⟨fun a => (fl a).ofIso ((Scheme.Modules.pullback π).mapIso (e a)), fun T g fl'' => ?_⟩
  obtain ⟨g', ⟨w, hg⟩, hu⟩ := hfl T g (fun a => (fl'' a).ofIso ((Scheme.Modules.pullback g).mapIso (e a)).symm)
  refine ⟨g', ⟨w, (isFlagBundle_cond_iso π E E' r e fl g fl'' g' w).1 hg⟩, fun y ⟨wy, hy⟩ => ?_⟩
  exact hu y ⟨wy, (isFlagBundle_cond_iso π E E' r e fl g fl'' y wy).2 hy⟩

end GlobalTheory.CovTest
end

