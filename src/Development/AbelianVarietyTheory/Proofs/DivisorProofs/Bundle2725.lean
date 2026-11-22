import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2618
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2619
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2646
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1280
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1790
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1976
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleBaseChange
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBaseChangeStable

open Limits (pullback)

set_option backward.isDefEq.respectTransparency false in

theorem comp_assoc_app {X Y Z W : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (E : W.Modules) :
    (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj E) ≫
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app E =
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app E) ≫
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app E ≫ eqToHom (by rw [Category.assoc]) := by
  have e := congrArg (fun t => NatTrans.app t E) (Scheme.Modules.pseudofunctor_associativity f g h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, eqToHom_app, Category.id_comp] at e
  calc _ = (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app E) ≫
      (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app E ≫ ((Scheme.Modules.pullbackComp f (g ≫ h)).inv.app E ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app E) ≫
        (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj E) ≫
      (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app E) := by
        simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
        erw [CategoryTheory.Functor.map_id, Category.id_comp]
    _ = _ := by rw [e]

set_option backward.isDefEq.respectTransparency false in

theorem comp_congr_app {X Y Z : Scheme.{0}} (f : X ⟶ Y) {u v : Y ⟶ Z} (w : u = v) (E : Z.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackCongr w).hom.app E) ≫
      (Scheme.Modules.pullbackComp f v).hom.app E =
    (Scheme.Modules.pullbackComp f u).hom.app E ≫ (Scheme.Modules.pullbackCongr (congrArg (f ≫ ·) w)).hom.app E := by
  subst w
  simp [Scheme.Modules.pullbackCongr]

set_option backward.isDefEq.respectTransparency false in

theorem congr_refl_app {X Y : Scheme.{0}} (f : X ⟶ Y) (h : f = f) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app M = 𝟙 _ := by
  simp [Scheme.Modules.pullbackCongr]

variable {B Y B' : Scheme.{0}} (π : Y ⟶ B) (g : B' ⟶ B)

set_option backward.isDefEq.respectTransparency false in

theorem bcIso_coh {T : Scheme.{0}} (h : T ⟶ pullback π g) (E : B.Modules) :
    (Scheme.Modules.pullbackComp h (pullback.fst π g)).hom.app ((Scheme.Modules.pullback π).obj E) ≫
      (Scheme.Modules.pullbackComp (h ≫ pullback.fst π g) π).hom.app E ≫
        (Scheme.Modules.pullbackCongr (show (h ≫ pullback.fst π g) ≫ π = (h ≫ pullback.snd π g) ≫ g by
          rw [Category.assoc, Category.assoc, pullback.condition])).hom.app E =
    (Scheme.Modules.pullback h).map (FlagBaseChange.bcIso π g E).hom ≫
      (Scheme.Modules.pullbackComp h (pullback.snd π g)).hom.app ((Scheme.Modules.pullback g).obj E) ≫
        (Scheme.Modules.pullbackComp (h ≫ pullback.snd π g) g).hom.app E := by
  rw [reassoc_of% (comp_assoc_app h (pullback.fst π g) π E), comp_assoc_app h (pullback.snd π g) g E,
    ← Functor.map_comp_assoc]
  have e : (FlagBaseChange.bcIso π g E).hom ≫ (Scheme.Modules.pullbackComp (pullback.snd π g) g).hom.app E =
      (Scheme.Modules.pullbackComp (pullback.fst π g) π).hom.app E ≫
        (Scheme.Modules.pullbackCongr pullback.condition).hom.app E := by
    simp [FlagBaseChange.bcIso]
  rw [e, Functor.map_comp_assoc, reassoc_of% (comp_congr_app h (pullback.condition (f := π) (g := g)) E)]
  simp [Scheme.Modules.pullbackCongr]

set_option backward.isDefEq.respectTransparency false in

theorem bcIso_coh_map {T : Scheme.{0}} (h : T ⟶ pullback π g) (E : B.Modules) {F : Y.Modules}
    (j : F ⟶ (Scheme.Modules.pullback π).obj E) (w : (h ≫ pullback.fst π g) ≫ π = (h ≫ pullback.snd π g) ≫ g) :
    (Scheme.Modules.pullbackComp h (pullback.fst π g)).hom.app F ≫
      (Scheme.Modules.pullback (h ≫ pullback.fst π g)).map j ≫
        (Scheme.Modules.pullbackComp (h ≫ pullback.fst π g) π).hom.app E ≫
          (Scheme.Modules.pullbackCongr w).hom.app E =
    (Scheme.Modules.pullback h).map
        ((Scheme.Modules.pullback (pullback.fst π g)).map j ≫ (FlagBaseChange.bcIso π g E).hom) ≫
      (Scheme.Modules.pullbackComp h (pullback.snd π g)).hom.app ((Scheme.Modules.pullback g).obj E) ≫
        (Scheme.Modules.pullbackComp (h ≫ pullback.snd π g) g).hom.app E := by
  have n := (Scheme.Modules.pullbackComp h (pullback.fst π g)).hom.naturality j
  simp only [Functor.comp_map] at n
  rw [← reassoc_of% n, bcIso_coh, Functor.map_comp_assoc]

set_option backward.isDefEq.respectTransparency false in

theorem match_lift {T : Scheme.{0}} (h : T ⟶ pullback π g) {g' : T ⟶ Y} {t : T ⟶ B'}
    (h₁ : h ≫ pullback.fst π g = g') (h₂ : h ≫ pullback.snd π g = t) (w : g' ≫ π = t ≫ g)
    (E : B.Modules) {F : Y.Modules} (j : F ⟶ (Scheme.Modules.pullback π).obj E) {F' : T.Modules}
    (j' : F' ⟶ (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback g).obj E))
    (e : (Scheme.Modules.pullback g').obj F ≅ F')
    (he : e.hom ≫ j' ≫ (Scheme.Modules.pullbackComp t g).hom.app E =
      (Scheme.Modules.pullback g').map j ≫ (Scheme.Modules.pullbackComp g' π).hom.app E ≫
        (Scheme.Modules.pullbackCongr w).hom.app E) :
    ∃ e' : (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback (pullback.fst π g)).obj F) ≅ F',
      e'.hom ≫ j' = (Scheme.Modules.pullback h).map
          ((Scheme.Modules.pullback (pullback.fst π g)).map j ≫ (FlagBaseChange.bcIso π g E).hom) ≫
        (Scheme.Modules.pullbackComp h (pullback.snd π g)).hom.app ((Scheme.Modules.pullback g).obj E) ≫
          (Scheme.Modules.pullbackCongr h₂).hom.app ((Scheme.Modules.pullback g).obj E) := by
  subst h₁ h₂
  refine ⟨(Scheme.Modules.pullbackComp h (pullback.fst π g)).app F ≪≫ e, ?_⟩
  rw [← cancel_mono ((Scheme.Modules.pullbackComp (h ≫ pullback.snd π g) g).hom.app E)]
  simp only [Iso.trans_hom, Iso.app_hom, Category.assoc, he]
  rw [bcIso_coh_map]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in

theorem match_fst {T : Scheme.{0}} (h : T ⟶ pullback π g) {t : T ⟶ B'}
    (h₂ : h ≫ pullback.snd π g = t) (w : (h ≫ pullback.fst π g) ≫ π = t ≫ g)
    (E : B.Modules) {F : Y.Modules} (j : F ⟶ (Scheme.Modules.pullback π).obj E) {F' : T.Modules}
    (j' : F' ⟶ (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback g).obj E))
    (e : (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback (pullback.fst π g)).obj F) ≅ F')
    (he : e.hom ≫ j' = (Scheme.Modules.pullback h).map
          ((Scheme.Modules.pullback (pullback.fst π g)).map j ≫ (FlagBaseChange.bcIso π g E).hom) ≫
        (Scheme.Modules.pullbackComp h (pullback.snd π g)).hom.app ((Scheme.Modules.pullback g).obj E) ≫
          (Scheme.Modules.pullbackCongr h₂).hom.app ((Scheme.Modules.pullback g).obj E)) :
    ∃ e' : (Scheme.Modules.pullback (h ≫ pullback.fst π g)).obj F ≅ F',
      e'.hom ≫ j' ≫ (Scheme.Modules.pullbackComp t g).hom.app E =
        (Scheme.Modules.pullback (h ≫ pullback.fst π g)).map j ≫
          (Scheme.Modules.pullbackComp (h ≫ pullback.fst π g) π).hom.app E ≫
            (Scheme.Modules.pullbackCongr w).hom.app E := by
  subst h₂
  refine ⟨((Scheme.Modules.pullbackComp h (pullback.fst π g)).app F).symm ≪≫ e, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Category.assoc, reassoc_of% he]
  rw [congr_refl_app, Category.id_comp, ← bcIso_coh_map π g h E j w, Iso.inv_hom_id_app_assoc]

set_option backward.isDefEq.respectTransparency false in

theorem isFlagBundle_pullback : ∀ (B Y B' : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ g : B' ⟶ B, IsFlagBundle (Limits.pullback.snd π g) (fun a => (Scheme.Modules.pullback g).obj (E a)) r (fun a => FlagBaseChange.pullFlag π g (fl a)) := by
  intro B Y B' π ι E r fl hfl g T t fl'
  obtain ⟨g', ⟨w, hw⟩, huniq⟩ :=
    hfl T (t ≫ g) (fun a => (fl' a).ofIso ((Scheme.Modules.pullbackComp t g).app (E a)))
  refine ⟨pullback.lift g' t w, ⟨pullback.lift_snd _ _ _, fun a i => ?_⟩, ?_⟩
  · obtain ⟨e, he⟩ := hw a i
    exact match_lift π g (pullback.lift g' t w) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) w (E a)
      ((fl a).ι i) ((fl' a).ι i) e he
  · rintro h ⟨w₀, hm⟩
    have w₁ : (h ≫ pullback.fst π g) ≫ π = t ≫ g := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, w₀]
    have e₁ : h ≫ pullback.fst π g = g' := huniq _ ⟨w₁, fun a i => by
      obtain ⟨e, he⟩ := hm a i
      exact match_fst π g h w₀ w₁ (E a) ((fl a).ι i) ((fl' a).ι i) e he⟩
    exact pullback.hom_ext (e₁.trans (pullback.lift_fst _ _ _).symm)
      (w₀.trans (pullback.lift_snd _ _ _).symm)

end GlobalTheory.FlagBaseChangeStable
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProjectionSurjectiveStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_projection_surjective : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → Function.Surjective π := by
  first | exact @GlobalTheory.FlagSurj.isFlagBundle_surjective | exact GlobalTheory.FlagSurj.isFlagBundle_surjective | (intros; apply GlobalTheory.FlagSurj.isFlagBundle_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePullbackBaseChange
section
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CovTest GlobalTheory.Published

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTest.BCFlag

theorem pc_assoc {X Y Z W : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (M : W.Modules) :
    (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M =
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M ≫
          (Scheme.Modules.pullbackCongr (Category.assoc f g h).symm).hom.app M := by
  have := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity f g h) M
  simp at this
  have e2 := congrArg (fun x => (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
    (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M ≫ x) this
  simp only [Iso.hom_inv_id_app_assoc, ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app] at e2
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at e2
  rw [e2]
  simp [Scheme.Modules.pullbackCongr, eqToHom_app]

theorem pc_congr {T P B : Scheme.{0}} (f : T ⟶ P) {u v : P ⟶ B} (c : u = v) {k : T ⟶ B} (h₁ : f ≫ u = k)
    (h₂ : f ≫ v = k) (M : B.Modules) :
    (Scheme.Modules.pullbackComp f u).hom.app M ≫ (Scheme.Modules.pullbackCongr h₁).hom.app M =
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackCongr c).hom.app M) ≫
        (Scheme.Modules.pullbackComp f v).hom.app M ≫ (Scheme.Modules.pullbackCongr h₂).hom.app M := by
  subst c h₁
  simp [Scheme.Modules.pullbackCongr]

theorem congr_trans' {T B : Scheme.{0}} {u v k : T ⟶ B} (c : u = v) (d : v = k) (M : B.Modules) :
    (Scheme.Modules.pullbackCongr c).hom.app M ≫ (Scheme.Modules.pullbackCongr d).hom.app M =
      (Scheme.Modules.pullbackCongr (c.trans d)).hom.app M := by
  subst c d
  simp [Scheme.Modules.pullbackCongr]

theorem pc_coh {T P Y B' B : Scheme.{0}} (f : T ⟶ P) (a : P ⟶ Y) (b : P ⟶ B') (π : Y ⟶ B) (g : B' ⟶ B)
    (cond : a ≫ π = b ≫ g) (h : T ⟶ Y) (t : T ⟶ B') (ha : f ≫ a = h) (hb : f ≫ b = t) (w : h ≫ π = t ≫ g)
    (E : B.Modules) :
    (Scheme.Modules.pullbackComp f a).hom.app ((Scheme.Modules.pullback π).obj E) ≫
        (Scheme.Modules.pullbackCongr ha).hom.app ((Scheme.Modules.pullback π).obj E) ≫
          (Scheme.Modules.pullbackComp h π).hom.app E ≫ (Scheme.Modules.pullbackCongr w).hom.app E =
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp a π).hom.app E ≫
          (Scheme.Modules.pullbackCongr cond).hom.app E ≫ (Scheme.Modules.pullbackComp b g).inv.app E) ≫
        (Scheme.Modules.pullbackComp f b).hom.app ((Scheme.Modules.pullback g).obj E) ≫
          (Scheme.Modules.pullbackCongr hb).hom.app ((Scheme.Modules.pullback g).obj E) ≫
            (Scheme.Modules.pullbackComp t g).hom.app E := by
  subst ha hb
  have e1 : (Scheme.Modules.pullbackCongr (rfl : f ≫ a = f ≫ a)).hom.app ((Scheme.Modules.pullback π).obj E) = 𝟙 _ := by
    simp [Scheme.Modules.pullbackCongr]
  have e2 : (Scheme.Modules.pullbackCongr (rfl : f ≫ b = f ≫ b)).hom.app ((Scheme.Modules.pullback g).obj E) = 𝟙 _ := by
    simp [Scheme.Modules.pullbackCongr]
  rw [e1, e2, Category.id_comp, Category.id_comp, reassoc_of% (pc_assoc f a π E), pc_assoc f b g E,
    congr_trans']
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc (Scheme.Modules.pullback f) ((Scheme.Modules.pullbackComp b g).inv.app E)]
  erw [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [pc_congr f cond _ (Category.assoc f b g).symm]

theorem step_key {T Y B' B : Scheme.{0}} (π : Y ⟶ B) (g : B' ⟶ B) (f : T ⟶ pullback π g) (h : T ⟶ Y) (t : T ⟶ B')
    (ha : f ≫ pullback.fst π g = h) (hb : f ≫ pullback.snd π g = t) (w : h ≫ π = t ≫ g) (E : B.Modules)
    (F : Y.Modules) (ιF : F ⟶ (Scheme.Modules.pullback π).obj E) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback (pullback.fst π g)).map ιF ≫ (bcIso π g E).hom) ≫
        (Scheme.Modules.pullbackComp f (pullback.snd π g)).hom.app ((Scheme.Modules.pullback g).obj E) ≫
          (Scheme.Modules.pullbackCongr hb).hom.app ((Scheme.Modules.pullback g).obj E) ≫
            (Scheme.Modules.pullbackComp t g).hom.app E =
      (Scheme.Modules.pullbackComp f (pullback.fst π g)).hom.app F ≫
        (Scheme.Modules.pullbackCongr ha).hom.app F ≫ (Scheme.Modules.pullback h).map ιF ≫
          (Scheme.Modules.pullbackComp h π).hom.app E ≫ (Scheme.Modules.pullbackCongr w).hom.app E := by
  rw [← (Scheme.Modules.pullbackCongr ha).hom.naturality_assoc,
    ← (Scheme.Modules.pullbackComp f (pullback.fst π g)).hom.naturality_assoc,
    pc_coh f (pullback.fst π g) (pullback.snd π g) π g pullback.condition h t ha hb w E]
  simp only [bcIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, CategoryTheory.Functor.map_comp,
    Category.assoc, Functor.comp_map]

theorem step_exists {T Y B' B : Scheme.{0}} (π : Y ⟶ B) (g : B' ⟶ B) (f : T ⟶ pullback π g) (h : T ⟶ Y) (t : T ⟶ B')
    (ha : f ≫ pullback.fst π g = h) (hb : f ≫ pullback.snd π g = t) (w : h ≫ π = t ≫ g) (E : B.Modules)
    (F : Y.Modules) (ιF : F ⟶ (Scheme.Modules.pullback π).obj E) (G : T.Modules)
    (ιG : G ⟶ (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback g).obj E))
    (e : (Scheme.Modules.pullback h).obj F ≅ G)
    (hee : e.hom ≫ ιG ≫ (Scheme.Modules.pullbackComp t g).hom.app E =
      (Scheme.Modules.pullback h).map ιF ≫ (Scheme.Modules.pullbackComp h π).hom.app E ≫
        (Scheme.Modules.pullbackCongr w).hom.app E) :
    ((Scheme.Modules.pullbackComp f (pullback.fst π g)).app F ≪≫
        (Scheme.Modules.pullbackCongr ha).app F ≪≫ e).hom ≫ ιG =
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback (pullback.fst π g)).map ιF ≫ (bcIso π g E).hom) ≫
        (Scheme.Modules.pullbackComp f (pullback.snd π g)).hom.app ((Scheme.Modules.pullback g).obj E) ≫
          (Scheme.Modules.pullbackCongr hb).hom.app ((Scheme.Modules.pullback g).obj E) := by
  rw [← cancel_mono ((Scheme.Modules.pullbackComp t g).hom.app E)]
  simp only [Iso.trans_hom, Iso.app_hom, Category.assoc]
  rw [hee, step_key π g f h t ha hb w E F ιF]

theorem step_unique {T Y B' B : Scheme.{0}} (π : Y ⟶ B) (g : B' ⟶ B) (f : T ⟶ pullback π g) (t : T ⟶ B')
    (hb : f ≫ pullback.snd π g = t) (w : (f ≫ pullback.fst π g) ≫ π = t ≫ g) (E : B.Modules)
    (F : Y.Modules) (ιF : F ⟶ (Scheme.Modules.pullback π).obj E) (G : T.Modules)
    (ιG : G ⟶ (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback g).obj E))
    (e : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback (pullback.fst π g)).obj F) ≅ G)
    (hee : e.hom ≫ ιG =
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback (pullback.fst π g)).map ιF ≫ (bcIso π g E).hom) ≫
        (Scheme.Modules.pullbackComp f (pullback.snd π g)).hom.app ((Scheme.Modules.pullback g).obj E) ≫
          (Scheme.Modules.pullbackCongr hb).hom.app ((Scheme.Modules.pullback g).obj E)) :
    (((Scheme.Modules.pullbackComp f (pullback.fst π g)).app F).symm ≪≫ e).hom ≫ ιG ≫
        (Scheme.Modules.pullbackComp t g).hom.app E =
      (Scheme.Modules.pullback (f ≫ pullback.fst π g)).map ιF ≫
        (Scheme.Modules.pullbackComp (f ≫ pullback.fst π g) π).hom.app E ≫
          (Scheme.Modules.pullbackCongr w).hom.app E := by
  have k := step_key π g f _ t rfl hb w E F ιF
  have e1 : (Scheme.Modules.pullbackCongr (rfl : f ≫ pullback.fst π g = f ≫ pullback.fst π g)).hom.app F = 𝟙 _ := by
    simp [Scheme.Modules.pullbackCongr]
  have hee' := congrArg (· ≫ (Scheme.Modules.pullbackComp t g).hom.app E) hee
  simp only [Category.assoc] at hee'
  rw [e1, Category.id_comp, ← hee'] at k
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Category.assoc] at k ⊢
  rw [k]
  simp

theorem isFlagBundle_baseChange : ∀ (B Y B' : Scheme.{0}) (π : Y ⟶ B) (g : B' ⟶ B) (ι : Type) (E : ι → B.Modules) (n : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)), IsFlagBundle π E n fl →
    IsFlagBundle (pullback.snd π g) (fun a => (Scheme.Modules.pullback g).obj (E a)) n (fun a => bcFlag π g (fl a)) := by
  intro B Y B' π g ι E n fl H T t fl''
  obtain ⟨h, ⟨w, he⟩, hu⟩ := H T (t ≫ g) (fun a => (fl'' a).ofIso ((Scheme.Modules.pullbackComp t g).app (E a)))
  refine ⟨pullback.lift h t w, ⟨pullback.lift_snd _ _ _, fun a i => ?_⟩, ?_⟩
  · obtain ⟨e, hee⟩ := he a i
    exact ⟨_, step_exists π g (pullback.lift h t w) h t (pullback.lift_fst h t w) (pullback.lift_snd h t w) w (E a)
      ((fl a).F i) ((fl a).ι i) ((fl'' a).F i) ((fl'' a).ι i) e hee⟩
  · rintro y ⟨w'', he''⟩
    have w₁ : (y ≫ pullback.fst π g) ≫ π = t ≫ g := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, w'']
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      refine hu _ ⟨w₁, fun a i => ?_⟩
      obtain ⟨e, hee⟩ := he'' a i
      exact ⟨_, step_unique π g y t w'' w₁ (E a) ((fl a).F i) ((fl a).ι i) ((fl'' a).F i) ((fl'' a).ι i) e hee⟩
    · rw [pullback.lift_snd, w'']

end GlobalTheory.CovTest.BCFlag

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleTransportAlongIso
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagIsoBundle

theorem pull_natural {B Y T : Scheme.{0}} (π : Y ⟶ B) (g' : T ⟶ Y) (g : T ⟶ B) (w : g' ≫ π = g)
    {M N : B.Modules} (f : M ⟶ N) :
    (Scheme.Modules.pullback g').map ((Scheme.Modules.pullback π).map f) ≫
        (Scheme.Modules.pullbackComp g' π).hom.app N ≫ (Scheme.Modules.pullbackCongr w).hom.app N =
      (Scheme.Modules.pullbackComp g' π).hom.app M ≫ (Scheme.Modules.pullbackCongr w).hom.app M ≫
        (Scheme.Modules.pullback g).map f := by
  have h1 := (Scheme.Modules.pullbackComp g' π).hom.naturality f
  have h2 := (Scheme.Modules.pullbackCongr w).hom.naturality f
  simp only [Functor.comp_map] at h1
  rw [← Category.assoc, h1, Category.assoc, h2]

theorem isFlagBundle_of_iso : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (E E' : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) (e : ∀ a, E a ≅ E' a), IsFlagBundle π E r fl → IsFlagBundle π E' r (fun a => (fl a).ofIso ((Scheme.Modules.pullback π).mapIso (e a))) := by
  intro B Y π ι E E' r fl e h T g fl''
  obtain ⟨g', ⟨w, H⟩, uniq⟩ := h T g fun a =>
    (fl'' a).ofIso ((Scheme.Modules.pullback g).mapIso (e a)).symm
  refine ⟨g', ⟨w, fun a i => ?_⟩, fun y ⟨w', H'⟩ => uniq y ⟨w', fun a i => ?_⟩⟩
  · obtain ⟨e0, he0⟩ := H a i
    refine ⟨e0, ?_⟩
    have k := pull_natural π g' g w (e a).hom
    simp only [Vert.Flag.ofIso, Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom, Functor.map_comp,
      Category.assoc] at he0 ⊢
    rw [k, ← reassoc_of% he0, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]
  · obtain ⟨e1, he1⟩ := H' a i
    refine ⟨e1, ?_⟩
    have k := pull_natural π y g w' (e a).hom
    simp only [Vert.Flag.ofIso, Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom, Functor.map_comp,
      Category.assoc] at he1 ⊢
    rw [reassoc_of% he1, reassoc_of% k, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]

end GlobalTheory.FlagIsoBundle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleTransportIsoStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_transport_iso : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (E E' : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → (∀ a, Nonempty (E a ≅ E' a)) → ∃ fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E' a)) (r a), IsFlagBundle π E' r fl' := by
  first | exact @GlobalTheory.CovTest.isFlagBundle_of_iso | exact GlobalTheory.CovTest.isFlagBundle_of_iso | (intros; apply GlobalTheory.CovTest.isFlagBundle_of_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleUniqueUpToIsoStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_unique_up_to_iso : ∀ (B Y Y' : Scheme.{0}) (π : Y ⟶ B) (π' : Y' ⟶ B) (ι : Type) (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) (fl' : ∀ a, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback π').obj (E a)) (r a)), GlobalTheory.CovTest.IsFlagBundle π E r fl → GlobalTheory.CovTest.IsFlagBundle π' E r fl' → ∃ e : Y ≅ Y', e.hom ≫ π' = π := by
  first | exact @GlobalTheory.CovTest.exists_iso_of_isFlagBundle | exact GlobalTheory.CovTest.exists_iso_of_isFlagBundle | (intros; apply GlobalTheory.CovTest.exists_iso_of_isFlagBundle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatConstantAbsLeNineStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_constant_abs_le_nine : Hypotheses2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → |c₁| ≤ 9 * D.R.r * Lb → ∀ (la : AllWt.Weight (T.Q.Dw j)) (w : Psi T.Q.H → ℤ) Z, (∀ τ, |w τ| ≤ 3 * (D.R.r : ℤ)) → GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0) → Y.degC la Z - Y.rkC la Z * (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2) ≤ Y.degC (la + GlobalTheory.FlatLine.parWt (T.Q.Dw j) w) Z := by
  first | exact @GlobalTheory.TwistDeg.deg_twist_ge | exact GlobalTheory.TwistDeg.deg_twist_ge | (intros; apply GlobalTheory.TwistDeg.deg_twist_ge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDescentSectionsInjectiveEqualizer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem isPullback_fibreSquare_baseChange : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsPullback p q y π → ∀ r : pullback p p ⟶ pullback π π, r ≫ pullback.fst π π = pullback.fst p p ≫ q → r ≫ pullback.snd π π = pullback.snd p p ≫ q → IsPullback r (pullback.fst p p ≫ p) (pullback.fst π π ≫ π) y := by
  intro R _ S Y Z π y p q H r h1 h2
  have A : IsPullback (pullback.fst p p ≫ q) (pullback.snd p p) π (p ≫ y) :=
    IsPullback.paste_horiz (IsPullback.of_hasPullback p p) H.flip
  have X : IsPullback r (pullback.snd p p) (pullback.snd π π) q := by
    refine IsPullback.of_right (h₁₂ := pullback.fst π π) ?_ h2 (IsPullback.of_hasPullback π π)
    rw [h1, ← H.w]; exact A
  have := IsPullback.paste_vert X H.flip
  rwa [pullback.condition (f := p), pullback.condition (f := π)]

theorem descend_of_equalised_fibreSquare : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ V : Y.Opens, Function.Injective (p.app V).hom ∧ ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom := by
  intro R _ _ _ _ S Y Z π y p q hπ hs hS hy H
  have hinj := GlobalTheory.T.appTop_injective_of_surjective_integral_toSpecDomain R S π hs hS
  have heq := GlobalTheory.T.mem_range_appTop_of_fibreSquare_projections_eq R S π hπ hS hinj
  let r : pullback p p ⟶ pullback π π := pullback.map p p π π q q y H.w H.w
  have h1 : r ≫ pullback.fst π π = pullback.fst p p ≫ q := pullback.lift_fst _ _ _
  have h2 : r ≫ pullback.snd π π = pullback.snd p p ≫ q := pullback.lift_snd _ _ _
  have hP := isPullback_fibreSquare_baseChange R S Y Z π y p q H r h1 h2
  exact GlobalTheory.T.app_injective_descent_of_affineOpens Y Z p fun V hV => ⟨GlobalTheory.T.app_injective_affineOpen_flat_baseChange_proper R S Y Z π y p q hπ hy H hinj V hV,
    GlobalTheory.T.mem_range_app_of_flat_baseChange_equalised R S Y Z π y p q hπ hy H r h1 h2 hP heq V hV⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineDegreeEqEigenLatticeDegreeSub
section
noncomputable section

namespace GlobalTheory.PtDeg

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem lineDeg_eq_deg_eigLat_sub : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ), (∀ la, ∀ w ∈ valOn Z la, w s.sig = (ρ la : EReal)) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)), Nonempty (SABMap t₀ Xo.univ.t y.x) → Nonempty (SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) → ∀ (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ t : 𝓞 E →+* 𝓞 K, (∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 a)) → (Function.support ρ).Finite ∧ lineDeg s.cInf ρ = ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat B.t.act t) - ReciprocityTheory.GeometryOfNumbersTheory.deg h (F.eigLat B.t.act (t.comp (H.bar : 𝓞 E →+* 𝓞 E))) := by
  intro E _ _ _ H Dw l Xo c r U x hL Z τ s ρ hρ K _ _ _ y hy B t₀ hm1 hm2 F h hh t ht
  obtain ⟨m1⟩ := hm1
  obtain ⟨m2⟩ := hm2
  obtain ⟨π, ε, hπ, -⟩ := GlobalTheory.FlatDegreeCompare.exists_under_valuation_sum_log_absNorm c.F K (algebraMap c.F K)
  have ht' := GlobalTheory.T.hostIntegerCharacter_comp_conj_eq_conjEmbedding E H Dw l Xo c τ K t ht
  obtain ⟨u, hu, hui, hus⟩ := GlobalTheory.T.exists_frameCoords_basis_eigenLattice_span E H Dw l Xo c K y B t₀ m1 m2 F τ.1 t ht
  obtain ⟨u', hu', hui', hus'⟩ := GlobalTheory.T.exists_frameCoords_basis_eigenLattice_span E H Dw l Xo c K y B t₀ m1 m2 F (conjEmb τ.1) _ ht'
  have hfin := GlobalTheory.T.flatSection_constValuation_eigenLattice_at_prime E H Dw l Xo c r U x hL Z τ s ρ hρ K y hy B t₀ m1 m2 F t ht π ε hπ u u' hu hu'
  have hlat := GlobalTheory.T.degree_determinant_line_two_hermitianLattices K h _ _ (GlobalTheory.CM.DegBound.eigLat_fg F _ _) (GlobalTheory.CM.DegBound.eigLat_fg F _ _) u u' hui hus hui'
    hus' _ (GlobalTheory.T.flatSection_ne_zero_at_numberField_point E H Dw l Xo c r U x hL Z τ s K y hy) (fun 𝔓 => (ε 𝔓 : ℝ) * ρ (π 𝔓)) hfin
  have harch := GlobalTheory.T.constLengthFlatSection_eq_frameNorm_complexEmbedding E H Dw l Xo c r U x hL Z τ s K y hy B t₀ m1 m2 F h hh u u' hu hu'
  obtain ⟨hf, hd⟩ := GlobalTheory.T.adelicLine_degree_invariant_finite_extension c.F K π ε hπ s.cInf ρ hlat.1
  refine ⟨hf, hd.trans ?_⟩
  rw [← hlat.2]
  congr 1
  funext σ
  exact harch σ

end GlobalTheory.PtDeg
end
end

