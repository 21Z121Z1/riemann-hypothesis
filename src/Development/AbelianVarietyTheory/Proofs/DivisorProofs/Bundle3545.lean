import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3531
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3532
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0237
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1053
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0355
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3521
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2837
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3527
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3520
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3528
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomSchemeLow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanonHom

theorem pullSec : ∀ {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left),
    IsGrpPullback G' G f φ → ∀ (O : Type) [CommRing O] (a' : OAct O G') (a : OAct O G), (∀ r, (a'.act r).left ≫ φ = φ ≫ (a.act r).left) →
    ∀ (X : Type) [AddCommGroup X] [Module O X] (T : Over S') (x₀ : X → (Over.mk (T.hom ≫ f) ⟶ G)),
    (∀ y z, x₀ (y + z) = x₀ y * x₀ z) → (∀ (r : O) y, x₀ (r • y) = x₀ y ≫ a.act r) →
    ∃ x : X → (T ⟶ G'), (∀ y, (x y).left ≫ φ = (x₀ y).left) ∧ (∀ y z, x (y + z) = x y * x z) ∧
      ∀ (r : O) y, x (r • y) = x y ≫ a'.act r := by
  intro S S' G' _ G _ f φ hφ O _ a' a ha X _ _ T x₀ hadd hlin
  have hw : ∀ y, (x₀ y).left ≫ G.hom = T.hom ≫ f := fun y => Over.w (x₀ y)
  let x : X → (T ⟶ G') := fun y => Over.homMk (hφ.1.lift (x₀ y).left T.hom (hw y)) (hφ.1.lift_snd _ _ _)
  have hx : ∀ y, (x y).left ≫ φ = (x₀ y).left := fun y => hφ.1.lift_fst _ _ _
  have uniq : ∀ (p q : T ⟶ G'), p.left ≫ φ = q.left ≫ φ → p = q := fun p q h => by
    ext; apply hφ.1.hom_ext h; rw [Over.w p, Over.w q]
  refine ⟨x, hx, fun y z => uniq _ _ ?_, fun r y => uniq _ _ ?_⟩
  · rw [hx, hadd, hφ.2 T (x y) (x z) (x₀ y) (x₀ z) (hx y).symm (hx z).symm]
  · rw [hx, hlin, Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, hx]

theorem pushSec : ∀ {S S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left),
    IsGrpPullback G' G f φ → ∀ (O : Type) [CommRing O] (a' : OAct O G') (a : OAct O G), (∀ r, (a'.act r).left ≫ φ = φ ≫ (a.act r).left) →
    ∀ (X : Type) [AddCommGroup X] [Module O X] (T : Over S') (x : X → (T ⟶ G')),
    (∀ y z, x (y + z) = x y * x z) → (∀ (r : O) y, x (r • y) = x y ≫ a'.act r) →
    ∃ x₀ : X → (Over.mk (T.hom ≫ f) ⟶ G), (∀ y, (x₀ y).left = (x y).left ≫ φ) ∧ (∀ y z, x₀ (y + z) = x₀ y * x₀ z) ∧
      ∀ (r : O) y, x₀ (r • y) = x₀ y ≫ a.act r := by
  intro S S' G' _ G _ f φ hφ O _ a' a ha X _ _ T x hadd hlin
  have hw : ∀ y, ((x y).left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ f)).hom := fun y => by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w (x y)]; rfl
  refine ⟨fun y => Over.homMk ((x y).left ≫ φ) (hw y), fun y => rfl, fun y z => ?_, fun r y => ?_⟩
  · ext
    change (x (y + z)).left ≫ φ = _
    rw [hadd]
    exact (hφ.2 T (x y) (x z) (Over.homMk _ (hw y)) (Over.homMk _ (hw z)) rfl rfl).symm
  · ext
    simp only [Over.homMk_left, Over.comp_left, hlin, Category.assoc, ha]

theorem objMap_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'}
    {S S' : Scheme.{0}} {s' : S' ⟶ Sp B'} {s : S ⟶ Sp B} {o' : Obj D l b' s'} {o : Obj D l b s} {f f' : S' ⟶ S}
    (h : f = f') (m : ObjMap o' o f) : ∃ m' : ObjMap o' o f', m'.toSABMap.φ = m.toSABMap.φ := by
  subst h; exact ⟨m, rfl⟩

theorem obj_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
    {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s₁ s₂ : S ⟶ Sp B}
    (h : s₁ = s₂) (o : Obj D l b s₁) : ∃ o₂ : Obj D l b s₂, ∀ {S₀ : Scheme.{0}} {B₀ : Type} [CommRing B₀] {b₀ : Base l B₀}
      {s₀ : S₀ ⟶ Sp B₀} (o₀ : Obj D l b₀ s₀) (f : S ⟶ S₀), Nonempty (ObjMap o o₀ f) → Nonempty (ObjMap o₂ o₀ f) := by
  subst h; exact ⟨o, fun _ _ h => h⟩

theorem homScheme_low : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X], ∃ (Cs : Scheme.{0}) (g : Cs ⟶ Sp c.F) (oC : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) (g ≫ lowMap c (RingHom.id c.F))) (u : X → (𝟙_ (Over Cs) ⟶ oC.t.G)), SmoothOfRelativeDimension (D'.dim + Module.finrank (𝓞 E) X * (Module.finrank ℚ E / 2 * (D'.p + D'.q))) g ∧ (∀ y z, u (y + z) = u y * u z) ∧ (∀ (a : 𝓞 E) y, u (a • y) = u y ≫ oC.t.act.act a) ∧ (∀ (V : Type) [CommRing V] [IsReduced V] (bV : c.F →+* V) (o' : LowObj D' c bV) (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (v : Sp V ⟶ Cs) (m : ObjMap o' oC v), v ≫ g = spMap bV ∧ ∀ y, (x y).left ≫ m.toSABMap.φ = v ≫ (u y).left) ∧ (∀ (A : Type) [CommRing A] [IsReduced A] (v₁ v₂ : Sp A ⟶ Cs), v₁ ≫ g = v₂ ≫ g → ∀ (s' : Sp A ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v₁) (m₂ : ObjMap o'' oC v₂) (z : X → (Sp A ⟶ o''.t.G.left)), s' = v₁ ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v₁ ≫ (u y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = v₂ ≫ (u y).left) → v₁ = v₂) ∧ (∀ (k : Type) [Field k] (v : Sp (DualNumber k) ⟶ Cs) (s' : Sp (DualNumber k) ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v) (m₂ : ObjMap o'' oC (constPt v)) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)), s' = v ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v ≫ (u y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = constPt v ≫ (u y).left) → v = constPt v) := by
  intro E _ _ _ H D' l c X _ _ _ _
  have hXo : Nonempty (Moduli D' (LowDat.lowLevel l)) := by
    by_cases hpq : 1 ≤ D'.p + D'.q
    · exact GlobalTheory.Moduli.moduli_scheme_exists E H D' _ hpq
    · exact GlobalTheory.T.nonempty_moduli_of_rank_zero H D' _ (by omega)
  obtain ⟨Xo⟩ := hXo
  set sF : Sp c.F ⟶ Sp (KA (LowDat.lowLevel l)) := lowMap c (RingHom.id c.F) with hsF
  have P := GlobalTheory.T.shimuraObject_pullback_comp_cancel (D := D') (l := LowDat.lowLevel l)
  obtain ⟨oY, ⟨mY⟩⟩ := P.1 Xo.s Xo.univ (pullback.fst Xo.s sF) (pullback.snd Xo.s sF ≫ sF) pullback.condition.symm
  have hB : IsAbelianScheme oY.t.G := ⟨inferInstance, oY.t.semi.smooth, oY.proper, oY.t.semi.geomConnected⟩
  have hg := GlobalTheory.T.smoothOfRelativeDimension_shimuraObject_abelianScheme D' (LowDat.lowLevel l) (pullback.snd Xo.s sF ≫ sF) oY
  haveI : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Module.Projective (𝓞 E) X := GlobalTheory.Forms.projective_of_int _ _
  obtain ⟨C, _, u, -, hCsm, -, hadd, hlin, huniv⟩ :=
    GlobalTheory.HomScheme.exists_homObj_relDim _ oY.t.G hB _ hg oY.t.act X
  obtain ⟨oC, ⟨mC⟩⟩ := P.1 (pullback.snd Xo.s sF ≫ sF) oY C.hom ((C.hom ≫ pullback.snd Xo.s sF) ≫ sF)
    (Category.assoc _ _ _)
  obtain ⟨u', hu'φ, hu'add, hu'lin⟩ := pullSec oC.t.G oY.t.G C.hom mC.toSABMap.φ mC.cart (𝓞 E) oC.t.act oY.t.act mC.act X
    (𝟙_ (Over C.left)) (fun y => Over.homMk (𝟙 C.left) (by simp) ≫ u y) (fun y z => by rw [hadd, comp_mul])
    (fun r y => by rw [hlin, Category.assoc])
  have key : ∀ {T : Scheme.{0}} (v₁ v₂ : T ⟶ C.left), v₁ ≫ C.hom = v₂ ≫ C.hom →
      (∀ y, v₁ ≫ (u y).left = v₂ ≫ (u y).left) → v₁ = v₂ := by
    intro T v₁ v₂ hw hu
    obtain ⟨c0, -, huq⟩ := huniv (Over.mk (v₁ ≫ C.hom)) (fun y => Over.homMk v₁ rfl ≫ u y)
      (fun y z => by rw [hadd, comp_mul]) (fun r y => by rw [hlin, Category.assoc])
    have e1 := huq (Over.homMk v₁ rfl) (fun y => rfl)
    have e2 := huq (Over.homMk v₂ hw.symm) (fun y => by ext; simpa using (hu y).symm)
    simpa using congrArg CommaMorphism.left (e1.trans e2.symm)
  have hu'l : ∀ y, (u' y).left ≫ mC.toSABMap.φ = (u y).left := fun y => by rw [hu'φ]; simp
  have key2 : ∀ (A : Type) [CommRing A], IsNilpotent (nilradical A) → ∀ (v₁ v₂ : Sp A ⟶ C.left)
      (s' : Sp A ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s')
      (m₁ : ObjMap o'' oC v₁) (m₂ : ObjMap o'' oC v₂) (z : X → (Sp A ⟶ o''.t.G.left)), v₁ ≫ C.hom = v₂ ≫ C.hom →
      (∀ y, z y ≫ m₁.toSABMap.φ = v₁ ≫ (u' y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = v₂ ≫ (u' y).left) → v₁ = v₂ := by
    intro A _ hA v₁ v₂ s' o'' m₁ m₂ z hw hz₁ hz₂
    obtain ⟨k₁, hk₁⟩ := (P.2 _ _ s' oY oC o'' C.hom v₁ mC).1 m₁
    obtain ⟨k₂, hk₂⟩ := (P.2 _ _ s' oY oC o'' C.hom v₂ mC).1 m₂
    obtain ⟨k₂', hk₂'⟩ := objMap_congr hw.symm k₂
    have hφ := GlobalTheory.T.objMap_unique_of_nilpotent_nilradical' A hA s' _ o'' oY (v₁ ≫ C.hom) k₁ k₂'
    refine key v₁ v₂ hw fun y => ?_
    calc v₁ ≫ (u y).left = z y ≫ k₁.toSABMap.φ := by rw [hk₁, ← Category.assoc, hz₁, Category.assoc, hu'l]
      _ = z y ≫ k₂'.toSABMap.φ := by rw [hφ]
      _ = v₂ ≫ (u y).left := by rw [hk₂', hk₂, ← Category.assoc, hz₂, Category.assoc, hu'l]
  refine ⟨C.left, C.hom ≫ pullback.snd Xo.s sF, oC, u', ?_, hu'add, hu'lin, ?_, ?_, ?_⟩
  · haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := D'.dim)
    haveI h1 : SmoothOfRelativeDimension D'.dim (pullback.snd Xo.s sF) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @SmoothOfRelativeDimension D'.dim)
        (IsPullback.of_hasPullback Xo.s sF) Xo.smooth
    haveI := hCsm
    rw [add_comm]
    infer_instance
  · intro V _ _ bV o' x hxadd hxlin
    obtain ⟨f, ⟨hf, ⟨k⟩⟩, -⟩ := Xo.rep (Sp V) (lowMap c bV) inferInstance o'
    have hlow : lowMap c bV = spMap bV ≫ sF := by simp only [hsF, lowMap, spMap, ← Spec.map_comp]; rfl
    let fY : Sp V ⟶ pullback Xo.s sF := pullback.lift f (spMap bV) (hf.trans hlow)
    obtain ⟨k', -⟩ := objMap_congr (pullback.lift_fst f (spMap bV) (hf.trans hlow)).symm k
    obtain ⟨n, -⟩ := (P.2 Xo.s (pullback.snd Xo.s sF ≫ sF) (lowMap c bV) Xo.univ oY o' (pullback.fst _ _) fY mY).2 k'
    obtain ⟨x₀, hx₀, hx₀add, hx₀lin⟩ := pushSec o'.t.G oY.t.G fY n.toSABMap.φ n.cart (𝓞 E) o'.t.act oY.t.act n.act X
      (𝟙_ (Over (Sp V))) x hxadd hxlin
    obtain ⟨cc, hcc, -⟩ := huniv (Over.mk ((𝟙_ (Over (Sp V))).hom ≫ fY)) x₀ hx₀add hx₀lin
    have hccw : cc.left ≫ C.hom = fY := by simpa using Over.w cc
    obtain ⟨n', hn'⟩ := objMap_congr hccw.symm n
    obtain ⟨m, hm⟩ := (P.2 _ _ (lowMap c bV) oY oC o' C.hom cc.left mC).2 n'
    refine ⟨cc.left, m, ?_, fun y => ?_⟩
    · rw [← Category.assoc, hccw, pullback.lift_snd]
    · apply mC.cart.1.hom_ext
      · rw [Category.assoc, ← hm, hn', Category.assoc, hu'l, ← hx₀, ← hcc y]
        rfl
      · rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w (x y), Category.assoc, Over.w (u' y)]
        simp
  · intro A _ _ v₁ v₂ hv s' o'' m₁ m₂ z hs' hz₁ hz₂
    refine key2 A (by rw [nilradical_eq_zero]; exact IsNilpotent.zero) v₁ v₂ s' o'' m₁ m₂ z ?_ hz₁ hz₂
    obtain ⟨k₁, -⟩ := (P.2 _ _ s' oY oC o'' C.hom v₁ mC).1 m₁
    obtain ⟨K₁, -⟩ := (P.2 _ _ s' Xo.univ oY o'' (pullback.fst _ _) (v₁ ≫ C.hom) mY).1 k₁
    obtain ⟨k₂, -⟩ := (P.2 _ _ s' oY oC o'' C.hom v₂ mC).1 m₂
    obtain ⟨K₂, -⟩ := (P.2 _ _ s' Xo.univ oY o'' (pullback.fst _ _) (v₂ ≫ C.hom) mY).1 k₂
    have hv' := hv =≫ sF
    simp only [Category.assoc] at hv'
    have hs₁ : ((v₁ ≫ C.hom) ≫ pullback.fst Xo.s sF) ≫ Xo.s = s' := by
      rw [hs']; simp only [Category.assoc, pullback.condition]
    have hs₂ : ((v₂ ≫ C.hom) ≫ pullback.fst Xo.s sF) ≫ Xo.s = s' := by
      rw [hs']; simp only [Category.assoc, pullback.condition]; exact hv'.symm
    have hfst := (Xo.rep (Sp A) s' inferInstance o'').unique ⟨hs₁, ⟨K₁⟩⟩ ⟨hs₂, ⟨K₂⟩⟩
    apply pullback.hom_ext
    · simpa only [Category.assoc] using hfst
    · simpa only [Category.assoc] using hv
  · intro k _ v s' o'' m₁ m₂ z hs' hz₁ hz₂
    refine key2 (DualNumber k) (IsNoetherianRing.isNilpotent_nilradical _) v (constPt v) s' o'' m₁ m₂ z ?_ hz₁ hz₂
    haveI : FiniteDimensional ℚ c.F := c.fin
    haveI : Algebra.IsAlgebraic ℚ c.F := Algebra.IsAlgebraic.of_finite ℚ c.F
    have hcp : ∀ {W : Scheme.{0}} (w : C.left ⟶ W), constPt v ≫ w = constPt (v ≫ w) := fun w => by simp [constPt]
    obtain ⟨k₁, -⟩ := (P.2 _ _ s' oY oC o'' C.hom v mC).1 m₁
    obtain ⟨K₁, -⟩ := (P.2 _ _ s' Xo.univ oY o'' (pullback.fst _ _) (v ≫ C.hom) mY).1 k₁
    obtain ⟨k₂, -⟩ := (P.2 _ _ s' oY oC o'' C.hom (constPt v) mC).1 m₂
    obtain ⟨K₂, -⟩ := (P.2 _ _ s' Xo.univ oY o'' (pullback.fst _ _) (constPt v ≫ C.hom) mY).1 k₂
    obtain ⟨K₁', -⟩ := objMap_congr (Category.assoc v C.hom (pullback.fst Xo.s sF)) K₁
    obtain ⟨K₂', -⟩ := objMap_congr (show (constPt v ≫ C.hom) ≫ pullback.fst Xo.s sF =
      constPt (v ≫ C.hom ≫ pullback.fst Xo.s sF) by simp [constPt]) K₂
    have hs₁ : s' = (v ≫ C.hom ≫ pullback.fst Xo.s sF) ≫ Xo.s := by
      rw [hs']; simp only [Category.assoc, pullback.condition]
    obtain ⟨o₂, ho₂⟩ := obj_congr hs₁ o''
    have hfst := Xo.unram k _ o₂ (ho₂ Xo.univ _ ⟨K₁'⟩) (ho₂ Xo.univ _ ⟨K₂'⟩)
    apply pullback.hom_ext
    · simp only [Category.assoc]; rw [hcp]; exact hfst
    · simp only [Category.assoc]; rw [hcp]; exact GlobalTheory.Models.RankZero.eq_constPt_field _

end GlobalTheory.UCanonHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvarianceEtale
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.HomotopyInv

variable {R : Type} [CommRing R]

theorem eqv_comp {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} {F : Shv R} (hf : Eqv R f F) (hg : Eqv R g F) :
    Eqv R (f ≫ g) F := fun n => by
  have h : (pull R (f ≫ g) F n : H R E'' F n → H R E F n) = pull R f F n ∘ pull R g F n :=
    funext fun x => pull_comp R f g F n x
  rw [h]
  exact (hf n).comp (hg n)

attribute [local instance] Polynomial.algebra

theorem eqv_baseChange (q : ℕ) (A : Type) [CommRing A] (i : ℤ) (A' : Type) [CommRing A']
    (s : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A))
    (h : Eqv _ (spMap (Polynomial.C : A' →+* Polynomial A')) (tw q i)) :
    Eqv _ (sch.map (pullback.map (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ≫ 𝟙 _) s (𝟙 _) s
      (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i) := by
  first
  | exact @_root_.GlobalTheory.PolynomialPushoutEquivalence.main
  | exact _root_.GlobalTheory.PolynomialPushoutEquivalence.main
  | (apply _root_.GlobalTheory.PolynomialPushoutEquivalence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialPushoutEquivalence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialPushoutEquivalence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialPushoutEquivalence.main ..)

theorem homotopy_invariance_etale : GlobalTheory.EtC.C4 := by
  intro q _ A _ hq i
  have hqΓ : IsUnit ((q : ℕ) : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  refine GlobalTheory.T.etC_b3 q (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)))
    (𝟙 (Spec (CommRingCat.of A))) hqΓ i ?_
  intro A' _ s hA'
  refine eqv_baseChange q A i A' s ?_
  have hq' : IsUnit (q : A') := by simpa using hq.map (Spec.preimage s).hom
  exact GlobalTheory.T.homotopyInvariance_tateTwist_strictlyHenselian q A' hA' hq' i

end GlobalTheory.EtC.HomotopyInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerActionSemiAbelianAlongTraitsOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc

theorem oAct_along_traits : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → ∃ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) ∧ (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∃ β : T.t.G.left ⟶ out.G.left, IsGrpPullback T.t.G out.G ξ β ∧ LBIso T.t.PP.L (out.L.L.pull β) ∧ ∀ a, (T.t.act.act a).left ≫ β = β ≫ (f a).left) := by
  intro E _ _ _ H Dw l Xo c C X₁ M U₀ EE out hAdm
  obtain ⟨f, hfm, H0⟩ := GlobalTheory.T.integerAction_extends_semiAbelian_thetaModel E H Dw l Xo c C X₁ M U₀ EE out hAdm
  refine ⟨f, hfm, ?_⟩
  rintro T ξ ⟨ξ₀, hξ₀, hlies⟩
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := T.gen
  obtain ⟨γ, hγ, hγL, hγa⟩ := H0 (FractionRing T.V) ξ₀ T.y hlies tK ⟨m₂⟩
  obtain ⟨β, hβ, hφβ, hβa⟩ := GlobalTheory.T.exists_grpPullback_completeDVR_of_generic_compat T.V T.cdvr T.t.G T.t.semi M.Z out.G out.semi ξ tK.G m₁.φ γ m₁.cart
    (hγ.congr hξ₀ rfl)
  refine ⟨β, hβ, ?_, fun a => hβa (T.t.act.act a) (f a) (tK.act.act a) (m₁.act a) (hγa a)⟩
  have h₁ : LBIso tK.PP.L (T.t.PP.L.pull m₁.φ) := by
    obtain ⟨w, hw, -⟩ := m₁.lin
    exact ⟨w, hw⟩
  have hL := out.L.isLB
  refine GlobalTheory.T.lineBundleIso_of_generic_semiAbelian_completeDVR T.V T.cdvr T.t.G T.t.semi tK.G m₁.φ m₁.cart _ _ T.t.PP.isLB (pull_isLB hL β) ?_
  exact LBIso.trans (pull_isLB T.t.PP.isLB _) tK.PP.isLB (pull_isLB (pull_isLB hL β) _) (LBIso.symm h₁)
    (LBIso.trans tK.PP.isLB (pull_isLB hL γ) (pull_isLB (pull_isLB hL β) _) hγL
      (GenSpread.lbIso_pull_pull hL m₁.φ hφβ.symm))

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerActionSemiAbelianAlongTraitsOverModuli
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc

private theorem fieldPt_lift_preimm {X' X : Scheme.{0}} (j : X' ⟶ X) [IsPreimmersion j] {K : Type} [Field K]
    (y : Sp K ⟶ X) (ξ : X') (h : y (IsLocalRing.closedPoint K) = j ξ) : ∃ z : Sp K ⟶ X', z ≫ j = y := by
  obtain ⟨⟨p, φ⟩, hy⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
  have hp : p = j ξ := by
    rw [← h, ← hy]
    exact (X.fromSpecResidueField_apply p _).symm
  subst hp
  have : IsIso (j.residueFieldMap ξ) := by
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨(j.residueFieldMap ξ).hom.injective, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := X'.residue_surjective ξ a
    obtain ⟨b, rfl⟩ := j.stalkMap_surjective ξ a
    exact ⟨X.residue _ b, congr($(Scheme.residue_residueFieldMap j ξ).hom b)⟩
  refine ⟨Spec.map (inv (j.residueFieldMap ξ) ≫ φ) ≫ X'.fromSpecResidueField ξ, ?_⟩
  rw [← hy, Scheme.SpecToEquivOfField_symm_apply, Category.assoc,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, ← Spec.map_comp,
    IsIso.hom_inv_id_assoc]

theorem oAct_along_traits_of_over : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∃ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) ∧ (∀ z : Y.Z, r z ∈ Set.range C.i → z ∈ abLocus out.G) ∧ (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ r = T.y ≫ C.i → ∃ β : T.t.G.left ⟶ out.G.left, IsGrpPullback T.t.G out.G ξ β ∧ LBIso T.t.PP.L (out.L.L.pull β) ∧ ∀ a, (T.t.act.act a).left ≫ β = β ≫ (f a).left) := by
  intro E _ _ _ H Dw l Xo c C X₁ Y U₀ EE out r hO hpt
  obtain ⟨wi⟩ := nonempty_uWit X₁
  obtain ⟨f, ψ, hfm, -, -, -, H0⟩ := GlobalTheory.T.semiAbelianAction_eq_universal_at_fieldPoints_of_thetaModel E H Dw l Xo c C X₁ Y U₀ EE out r hO hpt wi
  refine ⟨f, hfm, ?_, ?_⟩
  · rintro z ⟨x, hx⟩ K _ _ t ⟨p, hp⟩
    haveI := C.isPreimmersion_i
    obtain ⟨y, hy⟩ := fieldPt_lift_preimm C.i (t ≫ r) x (by
      have e : (t ≫ r) (IsLocalRing.closedPoint K) = r (t p) := by
        rw [Subsingleton.elim (α := PrimeSpectrum K) (IsLocalRing.closedPoint K) p]
        exact Scheme.Hom.comp_apply _ _ _
      rw [e, hp, hx])
    obtain ⟨tK, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull (y ≫ pullback.fst _ _) Xo.univ.t
    obtain ⟨γ, hγ, -, -⟩ := H0 K t y hy.symm tK ⟨m⟩
    haveI : IsProper Xo.univ.t.G.hom := Xo.univ.proper
    haveI : IsProper tK.G.hom := MorphismProperty.of_isPullback m.cart.1 inferInstance
    rw [← hγ.1.isoPullback_inv_snd]
    infer_instance
  · intro T ξ hξ
    obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := T.gen
    obtain ⟨γ, hγ, hγL, hγa⟩ := H0 (FractionRing T.V) (jK T.V ≫ ξ) T.y (by rw [Category.assoc]; exact hξ) tK ⟨m₂⟩
    obtain ⟨β, hβ, hφβ, hβa⟩ := GlobalTheory.T.exists_grpPullback_completeDVR_of_generic_compat T.V T.cdvr T.t.G T.t.semi Y.Z out.G out.semi ξ tK.G m₁.φ γ m₁.cart hγ
    refine ⟨β, hβ, ?_, fun a => hβa (T.t.act.act a) (f a) (tK.act.act a) (m₁.act a) (hγa a)⟩
    have h₁ : LBIso tK.PP.L (T.t.PP.L.pull m₁.φ) := by
      obtain ⟨w, hw, -⟩ := m₁.lin
      exact ⟨w, hw⟩
    have hL := out.L.isLB
    refine GlobalTheory.T.lineBundleIso_of_generic_semiAbelian_completeDVR T.V T.cdvr T.t.G T.t.semi tK.G m₁.φ m₁.cart _ _ T.t.PP.isLB (pull_isLB hL β) ?_
    exact LBIso.trans (pull_isLB T.t.PP.isLB _) tK.PP.isLB (pull_isLB (pull_isLB hL β) _) (LBIso.symm h₁)
      (LBIso.trans tK.PP.isLB (pull_isLB hL γ) (pull_isLB (pull_isLB hL β) _) hγL
        (GenSpread.lbIso_pull_pull hL m₁.φ hφβ.symm))

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralThetaTermsTorsionPointsFrames
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

noncomputable section
namespace GlobalTheory.Poinc.Sep.FrameInt

theorem exists_rescale_gen {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (u : Γ(Y, ⊤)ˣ) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      val t' r z J = gm r z ⊤ u * val t r z J := by
  refine ⟨⟨fun j => t.s j * res le_top u⟩, fun i j => ?_, fun Z r z J hJ => ?_⟩
  · rw [map_mul, map_mul, ht i j, _root_.mul_assoc]
    refine congrArg (fun q => _ * (_ * q)) (unit_ext fun y hy => ?_)
    exact ((gm_res _ y _ hy _).trans (gm_res _ y le_top hy.1 _)).trans
      ((gm_res _ y _ hy _).trans (gm_res _ y le_top hy.2 _)).symm
  · exact (map_mul _ _ _).trans ((mul_comm _ _).trans (congrArg (· * _) (gm_res r z le_top (hJ.mem φ r) u)))

end GlobalTheory.Poinc.Sep.FrameInt

namespace GlobalTheory.Poinc.Sep.FrameInt

theorem gs_top_eq {V : Type} [CommRing V] [IsDomain V] (a : V) (z : (TF (R := V) (FractionRing V)).left) :
    gs (toUnit (TF (R := V) (FractionRing V))).left z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) =
      cst (FractionRing V) z (algebraMap V (FractionRing V) a) := by
  rw [toUnit_left_eq, GlobalTheory.RatioVal.gs_specMap, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  exact (GlobalTheory.RatioVal.gs_id_const z _).symm

theorem map_map_unit {V : Type} [CommRing V] (ε : Vˣ) :
    ((Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom.toMonoidHom ε) : Vˣ) : V) = ε := by
  show (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ε) = ε
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

end GlobalTheory.Poinc.Sep.FrameInt

open GlobalTheory.Poinc.Sep.FrameInt in

theorem GlobalTheory.Poinc.Sep.FrameInt.integral_terms : ∀ (m : ℕ), Odd m → 3 ≤ m → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ k : ℕ, k ≠ 0 → IsUnit (k : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D (m ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))), (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' → ThetaOne.OneBasisAt D f θ') → ∀ (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∃ (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A)) (t : ∀ c, LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1))) (s₀ : V₁), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V₁) (p : Over.mk x ⟶ D.P.A), p ^ (m ^ 2) = 1 → ∃ c, p = toUnit _ ≫ b c) ∧ (∀ c, (t c).IsGen) ∧ (∀ c (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ (m ^ 2)) ((m ^ 2) ^ 2) 1)), Normd κ → ∀ (Z : Scheme) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J → val (t c) r z J ^ ((m ^ 2) ^ 2) * val κ (r ≫ (b c).left) z J = 1) ∧ (∀ c (Z : Scheme) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J → sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c).left) z J * (val (t c) r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (s₀ * u 0 c)) * (val ρ₀ r z J).val) := by
  intro m hm hm3 V₁ _ _ _ hV hk D X C _ e u mo hmo hT θ hθ ρ₀ hρ₀
  haveI : IsNoetherianRing V₁ := hV.1
  haveI : IsIntegrallyClosed V₁ := hV.2.1
  have hN1 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
  obtain ⟨th, g, b, w, hgb, -, hcov, hw, hcoef, ⟨c₀, hc₀⟩, hbN, hfr, -⟩ :=
    thetaTerms_integral D hN1 e _ hT

  have ht : ∀ c, ∃ t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1)), t.IsGen ∧
      ∀ z J, Good D.P.L z J → val t (toUnit (TF (R := V₁) (FractionRing V₁))).left z J = val (w c) (𝟙 _) z J := by
    intro c
    obtain ⟨t', ht'⟩ := GlobalTheory.T.exists_generator_translatedBundle_integralPoint V₁ D (b c)
    obtain ⟨ε, hε⟩ := hfr c t' ht'
    obtain ⟨t, htg, htv⟩ := exists_rescale_gen D.P.L _ _ t' ht'
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom.toMonoidHom ε)
    refine ⟨t, htg, fun z J hJ => Units.ext ?_⟩
    rw [htv _ _ z J hJ, Units.val_mul, hε z J hJ, gm_top_eq, map_map_unit]
  choose t htg htv using ht

  obtain ⟨ν, hν⟩ := exists_ratio (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.P.isLB rfl ρ₀ D.rig hρ₀ D.rig_gen
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.thetaFamily_term_zero_integral_torusPoint V₁ D θ hθ th
  choose f hf using fun c => GlobalTheory.T.exists_function_thetaSection_integralPoint V₁ D θ (b c) (t c) (htg c) ρ₀ hρ₀
  obtain ⟨z⟩ := exists_pt (R := V₁) (F := FractionRing V₁)
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB z
  have hTF : (TF (R := V₁) (FractionRing V₁)).hom = (toUnit (TF (R := V₁) (FractionRing V₁))).left := by
    simpa using (Over.w (toUnit (TF (R := V₁) (FractionRing V₁)))).symm
  set ν' : V₁ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of V₁)).hom.hom.toMonoidHom ν with hν'
  have key : ∀ c, algebraMap V₁ (FractionRing V₁) (u 0 c * mo 0) =
      lam * algebraMap V₁ (FractionRing V₁) (f c) * algebraMap V₁ (FractionRing V₁) ν' := by
    intro c
    have h0 := hcoef 0 c
    rw [show e 0 = 0 from map_zero e] at h0
    have a := hlam (g c) (b c) (hgb c) (w c) _ h0 z J hJ
    rw [← htv c z J hJ, _root_.mul_assoc, hf c _ _ z J hJ, gs_top_eq,
      hν _ _ z J hJ, Units.val_mul, gm_top_eq, rigV, hTF] at a
    have a' : cst (FractionRing V₁) z (algebraMap V₁ (FractionRing V₁) (u 0 c * mo 0)) *
        (val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
          (toUnit (TF (R := V₁) (FractionRing V₁))).left z J).val =
        cst (FractionRing V₁) z (lam * algebraMap V₁ (FractionRing V₁) (f c) * algebraMap V₁ (FractionRing V₁) ν') *
        (val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
          (toUnit (TF (R := V₁) (FractionRing V₁))).left z J).val := by
      rw [a, cst_eq, cst_eq, cst_eq, cst_eq, map_mul, map_mul]
      ring
    exact cst_inj z ((Units.isUnit _).mul_left_inj.1 a')

  obtain ⟨c₁, hc₁⟩ := (hmo 0).2
  have hinj := IsFractionRing.injective V₁ (FractionRing V₁)
  have hlam0 : lam ≠ 0 := by
    intro h
    have := key c₀
    rw [h, zero_mul, zero_mul] at this
    have h1 : u 0 c₀ * mo 0 = 1 := hc₀
    rw [h1, map_one] at this
    exact one_ne_zero this
  have hν0 : algebraMap V₁ (FractionRing V₁) (ν' : V₁) ≠ 0 :=
    (IsUnit.map (algebraMap V₁ (FractionRing V₁)) ν'.isUnit).ne_zero
  have cross : ∀ c, f c * u 0 c₁ = f c₁ * u 0 c := by
    intro c
    apply hinj
    have k1 := key c
    have k2 := key c₁
    have : lam * algebraMap V₁ (FractionRing V₁) ν' *
        algebraMap V₁ (FractionRing V₁) (f c * u 0 c₁) =
        lam * algebraMap V₁ (FractionRing V₁) ν' * algebraMap V₁ (FractionRing V₁) (f c₁ * u 0 c) := by
      rw [map_mul, map_mul]
      have e1 : lam * algebraMap V₁ (FractionRing V₁) (f c) * algebraMap V₁ (FractionRing V₁) ν' *
          algebraMap V₁ (FractionRing V₁) (u 0 c₁) = algebraMap V₁ (FractionRing V₁) (u 0 c * mo 0) *
          algebraMap V₁ (FractionRing V₁) (u 0 c₁) := by rw [k1]
      have e2 : lam * algebraMap V₁ (FractionRing V₁) (f c₁) * algebraMap V₁ (FractionRing V₁) ν' *
          algebraMap V₁ (FractionRing V₁) (u 0 c) = algebraMap V₁ (FractionRing V₁) (u 0 c₁ * mo 0) *
          algebraMap V₁ (FractionRing V₁) (u 0 c) := by rw [k2]
      simp only [map_mul] at e1 e2
      linear_combination e1 - e2
    exact mul_left_cancel₀ (mul_ne_zero hlam0 hν0) this
  refine ⟨b, t, f c₁ * ↑(hc₁.unit⁻¹), hcov, htg, ?_, ?_⟩
  · intro c κ hκ Z r z' J' hJ'
    refine GlobalTheory.T.integralFrame_identity_of_genericPoint V₁ D (m ^ 2) (b c) (hbN c) (t c) (htg c) κ hκ (fun y I hI => ?_) Z r z' J' hJ'
    rw [htv c y I hI]
    have := (hw c).2 κ hκ y I hI
    rwa [show (g c).b.left = (toUnit (TF (R := V₁) (FractionRing V₁))).left ≫ (b c).left from
      congrArg (fun q => q.left) (hgb c)] at this
  · intro c Z r z' J' hJ'
    have hs : f c = f c₁ * ↑(hc₁.unit⁻¹) * u 0 c := by
      rw [mul_right_comm, ← cross c, _root_.mul_assoc, IsUnit.mul_val_inv, _root_.mul_one]
    rw [hf c Z r z' J' hJ', hs]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixedHeightByInductionSuccStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMixedHeightByInduction_succ : ArchInteg → ArchRecip → ∀ m : ℕ, (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T) → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∃ T, IsMix p (m + 1) T := by
  first | exact @GlobalTheory.MixHt.Step.isMix_succ | exact GlobalTheory.MixHt.Step.isMix_succ | (intros; apply GlobalTheory.MixHt.Step.isMix_succ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicImageNotOntoModConjIdealStatement
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicImage_not_onto_mod_conj_ideal : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (hn : 0 < n) (hc : Cois D y n) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hn𝔭 : (n : 𝓞 E) ∈ 𝔭) (hi : img D y Z' 𝔭 ≠ ⊤) (hL : (perp D Z ⊓ perp D Z').map y ≤ img D y Z' 𝔭),
    img D y Z' (𝔭.map (H.bar : 𝓞 E →+* 𝓞 E)) ≠ ⊤ := by
  first | exact @GlobalTheory.LowFilt.CoisBar.img_bar_ne_top | exact GlobalTheory.LowFilt.CoisBar.img_bar_ne_top | (intros; apply GlobalTheory.LowFilt.CoisBar.img_bar_ne_top <;> assumption)
end
end

