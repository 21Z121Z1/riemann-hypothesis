import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3494
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3507
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3495
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3496

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseSchOfHomScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.BaseSch

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_injective {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g := by
  have := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  simpa using this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem lowMap_eq {l : Geo.Tor.Level H} (c : Coeff l) {A : Type} [CommRing A] (b : c.F →+* A) :
    lowMap c b = spMap b ≫ lowMap c (RingHom.id c.F) := by
  simp only [lowMap, RingHom.id_comp]
  rw [← spMap_comp']

theorem objMap_congr {D : Datum H} {l : Geo.Tor.Level H} {S S' : Scheme.{0}} {s : S ⟶ Sp (KA l)}
    {s' : S' ⟶ Sp (KA l)} {o : Obj D l (baseKA l) s} {o' : Obj D l (baseKA l) s'} {f f' : S' ⟶ S} (h : f = f')
    (m : ObjMap o' o f) : ∃ m' : ObjMap o' o f', m'.toSABMap.φ = m.toSABMap.φ := by
  subst h
  exact ⟨m, rfl⟩

theorem exists_section_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {q : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G q φ) (σ : 𝟙_ (Over S) ⟶ G) :
    ∃ σ' : 𝟙_ (Over S') ⟶ G', σ'.left ≫ φ = q ≫ σ.left := by
  have hw : (q ≫ σ.left) ≫ G.hom = 𝟙 S' ≫ q := by
    rw [Category.assoc, Over.w σ]
    simp
  refine ⟨Over.homMk (h.1.lift (q ≫ σ.left) (𝟙 S') hw) (by simpa using h.1.lift_snd _ _ hw), ?_⟩
  simp

theorem hom_ext_pull {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {q : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G q φ) {T : Over S'} (σ₁ σ₂ : T ⟶ G')
    (e : σ₁.left ≫ φ = σ₂.left ≫ φ) : σ₁ = σ₂ := by
  ext1
  exact h.1.hom_ext e (by rw [Over.w σ₁, Over.w σ₂])

theorem pull_mul {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {q : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G q φ) (σ₁ σ₂ : 𝟙_ (Over S') ⟶ G') (τ₁ τ₂ : 𝟙_ (Over S) ⟶ G)
    (h₁ : σ₁.left ≫ φ = q ≫ τ₁.left) (h₂ : σ₂.left ≫ φ = q ≫ τ₂.left) :
    (σ₁ * σ₂).left ≫ φ = q ≫ (τ₁ * τ₂).left := by
  let Q : Over.mk ((𝟙_ (Over S')).hom ≫ q) ⟶ 𝟙_ (Over S) := Over.homMk q (by simp)
  have e := h.2 (𝟙_ (Over S')) σ₁ σ₂ (Q ≫ τ₁) (Q ≫ τ₂) (by simp [Q, h₁]) (by simp [Q, h₂])
  rw [← e, ← MonObj.comp_mul]
  simp [Q]

theorem sec_comp_eq {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} (f : S' ⟶ S) (φ : G'.left ⟶ G.left)
    (hw : φ ≫ G.hom = G'.hom ≫ f) (σ : 𝟙_ (Over S') ⟶ G') (τ : 𝟙_ (Over S) ⟶ G) :
    (σ.left ≫ φ) ≫ G.hom = (f ≫ τ.left) ≫ G.hom := by
  rw [Category.assoc, hw, Category.assoc, Over.w τ, ← Category.assoc, Over.w σ]
  simp

end GlobalTheory.UCanon.BaseSch

namespace GlobalTheory.UCanon.BaseSch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

set_option maxHeartbeats 800000 in

theorem of_homScheme (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    (Cs : Scheme.{0}) (g : Cs ⟶ Sp c.F)
    (oC : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) (g ≫ lowMap c (RingHom.id c.F)))
    (u : X → (𝟙_ (Over Cs) ⟶ oC.t.G)) (N : ℕ) (hsm : SmoothOfRelativeDimension N g)
    (hex : ∀ (V : Type) [CommRing V] [IsReduced V] (bV : c.F →+* V) (o' : LowObj D' c bV)
      (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) →
      (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (v : Sp V ⟶ Cs) (m : ObjMap o' oC v),
        v ≫ g = spMap bV ∧ ∀ y, (x y).left ≫ m.toSABMap.φ = v ≫ (u y).left)
    (huniq : ∀ (A : Type) [CommRing A] [IsReduced A] (v₁ v₂ : Sp A ⟶ Cs), v₁ ≫ g = v₂ ≫ g →
      ∀ (s' : Sp A ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s')
        (m₁ : ObjMap o'' oC v₁) (m₂ : ObjMap o'' oC v₂) (z : X → (Sp A ⟶ o''.t.G.left)),
        s' = v₁ ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v₁ ≫ (u y).left) →
        (∀ y, z y ≫ m₂.toSABMap.φ = v₂ ≫ (u y).left) → v₁ = v₂)
    (heps : ∀ (k : Type) [Field k] (v : Sp (DualNumber k) ⟶ Cs) (s' : Sp (DualNumber k) ⟶ Sp (KA (LowDat.lowLevel l)))
      (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v)
      (m₂ : ObjMap o'' oC (constPt v)) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)),
      s' = v ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v ≫ (u y).left) →
      (∀ y, z y ≫ m₂.toSABMap.φ = constPt v ≫ (u y).left) → v = constPt v)
    (hadd : ∀ y z, u (y + z) = u y * u z) (hlin : ∀ (a : 𝓞 E) y, u (a • y) = u y ≫ oC.t.act.act a)
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (bV : c.F →+* V) (o' : LowObj D' c bV)
    (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)) (hx : ∀ y z, x (y + z) = x y * x z)
    (hxl : ∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsRegularLocalRing W) (b : c.F →+* W) (o : LowObj D' c b)
      (x₀ : X → (𝟙_ (Over (Sp W)) ⟶ o.t.G)) (θ₀ : W →+* V) (m : ObjMap o' o (spMap θ₀)),
      b.EssFiniteType ∧ (∀ y z, x₀ (y + z) = x₀ y * x₀ z) ∧ (∀ (a : 𝓞 E) y, x₀ (a • y) = x₀ y ≫ o.t.act.act a) ∧
      IsLocalHom θ₀ ∧ θ₀.comp b = bV ∧ (∀ y, (x y).left ≫ m.toSABMap.φ = spMap θ₀ ≫ (x₀ y).left) ∧
      ((∀ (A : Type) [CommRing A] [IsReduced A] (f₁ f₂ : W →+* A), f₁.comp b = f₂.comp b →
        ∀ (o'' : LowObj D' c (f₁.comp b)) (m₁ : ObjMap o'' o (spMap f₁)) (m₂ : ObjMap o'' o (spMap f₂))
          (z : X → (Sp A ⟶ o''.t.G.left)), (∀ y, z y ≫ m₁.toSABMap.φ = spMap f₁ ≫ (x₀ y).left) →
          (∀ y, z y ≫ m₂.toSABMap.φ = spMap f₂ ≫ (x₀ y).left) → (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f₁ = f₂) ∧
        (∀ (k : Type) [Field k] (f : W →+* DualNumber k) (o'' : LowObj D' c (f.comp b)) (m₁ : ObjMap o'' o (spMap f))
          (m₂ : ObjMap o'' o (spMap (GlobalTheory.RigChart.constHom f))) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)),
          (∀ y, z y ≫ m₁.toSABMap.φ = spMap f ≫ (x₀ y).left) →
          (∀ y, z y ≫ m₂.toSABMap.φ = spMap (GlobalTheory.RigChart.constHom f) ≫ (x₀ y).left) →
          (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f = GlobalTheory.RigChart.constHom f)) ∧
      (letI := ((residue W).comp b).toAlgebra
        ∃ a t : ℕ, ringKrullDim W = a ∧ Algebra.trdeg c.F (ResidueField W) = t ∧ a + t = N) := by
  obtain ⟨v, m0, hvg, hvx⟩ := hex V bV o' x hx hxl
  obtain ⟨hreg, b, hqb, hft, hdim⟩ :=
    GlobalTheory.SmoothStalk.stalk_regular_essFiniteType_dim c.F Cs g N hsm (v (closedPoint V))
  haveI : IsDomain (Cs.presheaf.stalk (v (closedPoint V))) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  obtain ⟨q, hq⟩ : ∃ q, q = Cs.fromSpecStalk (v (closedPoint V)) := ⟨_, rfl⟩
  rw [← hq] at hqb
  have hs : lowMap c b = q ≫ g ≫ lowMap c (RingHom.id c.F) := by
    rw [lowMap_eq c b, ← hqb, Category.assoc]
  obtain ⟨o, ⟨mq⟩⟩ := (obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).1
    (g ≫ lowMap c (RingHom.id c.F)) oC q (lowMap c b) hs
  have hsec := fun y => exists_section_pull mq.toSABMap.cart (u y)
  choose x₀ hx₀ using hsec
  set θ₀ : Cs.presheaf.stalk (v (closedPoint V)) →+* V := (Scheme.stalkClosedPointTo v).hom with hθ₀
  have hθq : spMap θ₀ ≫ q = v := by
    rw [hq]
    simpa [hθ₀, spMap] using Scheme.Spec_stalkClosedPointTo_fromSpecStalk v
  have hθb : θ₀.comp b = bV := by
    apply spMap_injective
    rw [spMap_comp', ← hqb, ← Category.assoc, hθq, hvg]
  obtain ⟨m0', hm0'⟩ := objMap_congr hθq.symm m0
  obtain ⟨n, hn⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o' q (spMap θ₀) mq).2 m0'
  have hmono : ∀ {T : Scheme.{0}} (a₁ a₂ : T ⟶ Sp (Cs.presheaf.stalk (v (closedPoint V)))), a₁ ≫ q = a₂ ≫ q → a₁ = a₂ :=
    fun a₁ a₂ h => by rw [hq] at h; exact (cancel_mono _).1 h
  refine ⟨Cs.presheaf.stalk (v (closedPoint V)), inferInstance, inferInstance, hreg, b, o, x₀, θ₀, n, hft, ?_, ?_, ?_, hθb, ?_, ⟨?_, ?_⟩, hdim⟩
  · intro y z
    apply hom_ext_pull mq.toSABMap.cart
    rw [hx₀, hadd, pull_mul mq.toSABMap.cart _ _ _ _ (hx₀ y) (hx₀ z)]
  · intro a y
    apply hom_ext_pull mq.toSABMap.cart
    rw [hx₀, hlin, Over.comp_left, Over.comp_left, Category.assoc, mq.toSABMap.act a, reassoc_of% (hx₀ y)]
  · exact inferInstance
  · intro y
    refine mq.toSABMap.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, ← hn, hm0', hvx, Category.assoc, hx₀, ← Category.assoc, hθq]
    · exact sec_comp_eq _ _ n.toSABMap.cart.1.w (x y) (x₀ y)
  · intro A _ _ f₁ f₂ hf o'' m₁ m₂ z hz₁ hz₂ _
    obtain ⟨k₁, hk₁⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o'' q (spMap f₁) mq).1 m₁
    obtain ⟨k₂, hk₂⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o'' q (spMap f₂) mq).1 m₂
    have hg : ∀ f : Cs.presheaf.stalk (v (closedPoint V)) →+* A, (spMap f ≫ q) ≫ g = spMap (f.comp b) := fun f => by
      rw [Category.assoc, hqb, spMap_comp']
    have e := huniq A (spMap f₁ ≫ q) (spMap f₂ ≫ q) (by rw [hg, hg, hf]) _ o'' k₁ k₂ z
      (by rw [lowMap_eq c (f₁.comp b), ← hg, Category.assoc])
      (fun y => by rw [hk₁, ← Category.assoc, hz₁, Category.assoc, hx₀, Category.assoc])
      (fun y => by rw [hk₂, ← Category.assoc, hz₂, Category.assoc, hx₀, Category.assoc])
    exact spMap_injective (hmono _ _ e)
  · intro k _ f o'' m₁ m₂ z hz₁ hz₂ _
    obtain ⟨k₁, hk₁⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o'' q (spMap f) mq).1 m₁
    obtain ⟨k₂, hk₂⟩ := ((obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).2 _ _ _ oC o o'' q
      (spMap (GlobalTheory.RigChart.constHom f)) mq).1 m₂
    have hc : spMap (GlobalTheory.RigChart.constHom f) ≫ q = constPt (spMap f ≫ q) := by
      simp only [constPt, GlobalTheory.RigChart.constHom, spMap_comp', Category.assoc]
    obtain ⟨k₂', hk₂'⟩ := objMap_congr hc k₂
    have e := heps k (spMap f ≫ q) _ o'' k₁ k₂' z
      (by rw [lowMap_eq c (f.comp b), spMap_comp', ← hqb]; simp only [Category.assoc])
      (fun y => by rw [hk₁, ← Category.assoc, hz₁, Category.assoc, hx₀, Category.assoc])
      (fun y => by rw [hk₂', hk₂, ← Category.assoc, hz₂, Category.assoc, hx₀, ← Category.assoc, hc])
    rw [← hc] at e
    exact spMap_injective (hmono _ _ e)

end GlobalTheory.UCanon.BaseSch

namespace GlobalTheory.UCanon.BaseSch

theorem exists_baseSch_of_homScheme (hcs : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X], ∃ (Cs : Scheme.{0}) (g : Cs ⟶ Sp c.F) (oC : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) (g ≫ lowMap c (RingHom.id c.F))) (u : X → (𝟙_ (Over Cs) ⟶ oC.t.G)), SmoothOfRelativeDimension (D'.dim + Module.finrank (𝓞 E) X * (Module.finrank ℚ E / 2 * (D'.p + D'.q))) g ∧ (∀ y z, u (y + z) = u y * u z) ∧ (∀ (a : 𝓞 E) y, u (a • y) = u y ≫ oC.t.act.act a) ∧ (∀ (V : Type) [CommRing V] [IsReduced V] (bV : c.F →+* V) (o' : LowObj D' c bV) (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (v : Sp V ⟶ Cs) (m : ObjMap o' oC v), v ≫ g = spMap bV ∧ ∀ y, (x y).left ≫ m.toSABMap.φ = v ≫ (u y).left) ∧ (∀ (A : Type) [CommRing A] [IsReduced A] (v₁ v₂ : Sp A ⟶ Cs), v₁ ≫ g = v₂ ≫ g → ∀ (s' : Sp A ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v₁) (m₂ : ObjMap o'' oC v₂) (z : X → (Sp A ⟶ o''.t.G.left)), s' = v₁ ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v₁ ≫ (u y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = v₂ ≫ (u y).left) → v₁ = v₂) ∧ (∀ (k : Type) [Field k] (v : Sp (DualNumber k) ⟶ Cs) (s' : Sp (DualNumber k) ⟶ Sp (KA (LowDat.lowLevel l))) (o'' : Obj D' (LowDat.lowLevel l) (baseKA (LowDat.lowLevel l)) s') (m₁ : ObjMap o'' oC v) (m₂ : ObjMap o'' oC (constPt v)) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)), s' = v ≫ g ≫ lowMap c (RingHom.id c.F) → (∀ y, z y ≫ m₁.toSABMap.φ = v ≫ (u y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = constPt v ≫ (u y).left) → v = constPt v)) : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H) {l : Geo.Tor.Level H} (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (bV : c.F →+* V) (o' : LowObj D' c bV) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x : X → (𝟙_ (Over (Sp V)) ⟶ o'.t.G)), (∀ y z, x (y + z) = x y * x z) → (∀ (a : 𝓞 E) y, x (a • y) = x y ≫ o'.t.act.act a) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsRegularLocalRing W) (b : c.F →+* W) (o : LowObj D' c b) (x₀ : X → (𝟙_ (Over (Sp W)) ⟶ o.t.G)) (θ₀ : W →+* V) (m : ObjMap o' o (spMap θ₀)), b.EssFiniteType ∧ (∀ y z, x₀ (y + z) = x₀ y * x₀ z) ∧ (∀ (a : 𝓞 E) y, x₀ (a • y) = x₀ y ≫ o.t.act.act a) ∧ IsLocalHom θ₀ ∧ θ₀.comp b = bV ∧ (∀ y, (x y).left ≫ m.toSABMap.φ = spMap θ₀ ≫ (x₀ y).left) ∧ ((∀ (A : Type) [CommRing A] [IsReduced A] (f₁ f₂ : W →+* A), f₁.comp b = f₂.comp b → ∀ (o'' : LowObj D' c (f₁.comp b)) (m₁ : ObjMap o'' o (spMap f₁)) (m₂ : ObjMap o'' o (spMap f₂)) (z : X → (Sp A ⟶ o''.t.G.left)), (∀ y, z y ≫ m₁.toSABMap.φ = spMap f₁ ≫ (x₀ y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = spMap f₂ ≫ (x₀ y).left) → (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f₁ = f₂) ∧ (∀ (k : Type) [Field k] (f : W →+* DualNumber k) (o'' : LowObj D' c (f.comp b)) (m₁ : ObjMap o'' o (spMap f)) (m₂ : ObjMap o'' o (spMap (GlobalTheory.RigChart.constHom f))) (z : X → (Sp (DualNumber k) ⟶ o''.t.G.left)), (∀ y, z y ≫ m₁.toSABMap.φ = spMap f ≫ (x₀ y).left) → (∀ y, z y ≫ m₂.toSABMap.φ = spMap (GlobalTheory.RigChart.constHom f) ≫ (x₀ y).left) → (∀ y, z y ≫ o''.t.G.hom = 𝟙 _) → f = GlobalTheory.RigChart.constHom f)) ∧ (letI := ((residue W).comp b).toAlgebra; ∃ a t : ℕ, ringKrullDim W = a ∧ Algebra.trdeg c.F (ResidueField W) = t ∧ a + t = D'.dim + Module.finrank (𝓞 E) X * (Module.finrank ℚ E / 2 * (D'.p + D'.q))) := by
  intro E _ _ _ H D' l c V _ _ _ bV o' X _ _ _ _ x hx hxl
  obtain ⟨Cs, g, oC, u, hsm, hadd, hlin, hex, huniq, heps⟩ := hcs D' c X
  exact of_homScheme D' c X Cs g oC u _ hsm hex huniq heps hadd hlin V bV o' x hx hxl

end GlobalTheory.UCanon.BaseSch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFrameWeightsStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cusp_frame_weights : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ Z, Nonempty (CuspFrame Z Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₂) ∧ ∃ (f₁ : CuspFrame Z Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) (Λ β : ℝ), 1 ≤ Λ ∧ 1 ≤ β ∧ Real.log f₁.n ≤ PP ∧ Real.log β ≤ PP ∧ Real.log Λ ≤ PP * (kap p i / lenT p i PP + 1) ∧ (∀ q σ, ChowHt.frameNorm (f₁.A σ) (fun a => σ (f₁.w.col q a)) ≤ Λ) ∧ BergLe Z Y.U (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ β := by
  first | exact @GlobalTheory.FrameBerg.frames_short_berg | exact GlobalTheory.FrameBerg.frames_short_berg | (intros; apply GlobalTheory.FrameBerg.frames_short_berg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisionPointPairOverAlgClosedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_divisionPoint_pair_over_algClosed : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ (y : D.X) (x : TF (R := V) F ⟶ D.P.A), x ^ k = DegPre.cF D F y → ∃ p : QkPt D F k, p.y = y ∧ p.g.b = x := by
  first | exact @GlobalTheory.UCanon.exists_qk_over_cF | exact GlobalTheory.UCanon.exists_qk_over_cF | (intros; apply GlobalTheory.UCanon.exists_qk_over_cF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughIsogenyOfDieudonneRangeLeStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_through_isogeny_of_dieudonne_range_le : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G Q H : PDivGroup p k) (q : G ⟶ Q) (f : G ⟶ H), G.IsConn → IsIsog q → LinearMap.range (T.map f) ≤ LinearMap.range (T.map q) → ∃ g : Q ⟶ H, q ≫ g = f := by
  first | exact @GlobalTheory.Dieu.exists_comp_eq_of_range_map_le | exact GlobalTheory.Dieu.exists_comp_eq_of_range_map_le | (intros; apply GlobalTheory.Dieu.exists_comp_eq_of_range_map_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibrePowerPointFiniteExtensionDvrStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibrePower_point_finite_extension_dvr : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (b : cycAway n →+* V) (PB : PolAV (Sp V)) (r : ℕ) (c : (Fin r → ℤ) → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ a a', c (a + a') = c a * c a') → ∃ (F : SFam PB.g n (zetaAway n)) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f₁ : V →+* V₁) (v : Sp V₁ ⟶ (GlobalTheory.LowChart.powA F r).left) (hs : v ≫ GlobalTheory.LowChart.toO F r = spMap (f₁.comp b)), IsCN V₁ ∧ IsDiscreteValuationRing V₁ ∧ Function.Injective f₁ ∧ f₁.Finite ∧ IsLocalHom f₁ ∧ ∃ (β₁ : (GlobalTheory.LowChart.siegAt F v _ hs).A.left ⟶ PB.A.left) (β₁₂ : (G2 (GlobalTheory.LowChart.siegAt F v _ hs).A).left ⟶ (G2 PB.A).left), IsGrpPullback (GlobalTheory.LowChart.siegAt F v _ hs).A PB.A (spMap f₁) β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso (GlobalTheory.LowChart.siegAt F v _ hs).P ((abelian₂ PB.A PB.L).pull β₁₂) ∧ ∀ a, (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • a)).left ≫ β₁ = spMap f₁ ≫ (c a).left := by
  first | exact @GlobalTheory.LowChart.exists_fibrePow_point_of_polAV | exact GlobalTheory.LowChart.exists_fibrePow_point_of_polAV | (intros; apply GlobalTheory.LowChart.exists_fibrePow_point_of_polAV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRegularThetaSetupCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}

def USetup.regSet (X₁ : USetup C) : Set X₁.M.Z := {z | X₁.S.R ≤ X₁.M.O z}

theorem USetup.isOpen_regSet (X₁ : USetup C) : IsOpen X₁.regSet := by
  obtain ⟨s, hs⟩ := X₁.S.fg
  have e : X₁.regSet = ⋂ a ∈ s, {z | a ∈ X₁.M.O z} := by
    ext z
    simp only [USetup.regSet, Set.mem_setOf_eq, Set.mem_iInter]
    rw [← hs, Algebra.adjoin_le_iff]
    exact ⟨fun h a ha => h ha, fun h a ha => h a ha⟩
  rw [e]
  exact isOpen_biInter_finset fun a _ => X₁.M.isOpen_setOf_mem_O a

def USetup.cov (X₁ : USetup C) : Set (Xo.XF c) := {x | ∃ w ∈ X₁.regSet, X₁.π w = C.i x}

theorem USetup.exists_open_cov {X₁ : USetup C} {ξ : Xo.XF c} {w : X₁.M.Z} (hw : X₁.π w = C.i ξ)
    (hR : X₁.S.R ≤ X₁.M.O w) : ∃ W : Set (Xo.XF c), IsOpen W ∧ ξ ∈ W ∧ closure {ξ} ∩ W ⊆ X₁.cov := by
  haveI := X₁.fin
  have hcl : IsClosedMap X₁.π := X₁.π.isClosedMap
  have hF : IsClosed (X₁.π '' (closure {w} \ X₁.regSet)) := hcl _ (isClosed_closure.sdiff X₁.isOpen_regSet)
  refine ⟨C.i ⁻¹' (X₁.π '' (closure {w} \ X₁.regSet))ᶜ, hF.isOpen_compl.preimage C.i.continuous, ?_, ?_⟩
  · rintro ⟨w', ⟨hw', hn⟩, he⟩
    have e := GlobalTheory.eq_of_specializes_of_isIntegralHom X₁.π (specializes_iff_mem_closure.2 hw') (hw.trans he.symm)
    exact hn (by rw [← e]; exact hR)
  · rintro x ⟨hx, hxW⟩
    have hs : C.i ξ ⤳ C.i x := (specializes_iff_mem_closure.2 hx).map C.i.continuous
    have hT : closure {C.i ξ} ⊆ X₁.π '' closure {w} :=
      (hcl _ isClosed_closure).closure_subset_iff.2
        (Set.singleton_subset_iff.2 ⟨w, subset_closure rfl, hw⟩)
    obtain ⟨w', hw', he⟩ := hT (specializes_iff_mem_closure.1 hs)
    refine ⟨w', ?_, he⟩
    by_contra hn
    exact hxW ⟨w', ⟨hw', hn⟩, he⟩

theorem USetup.exists_finite_cover
    (h : ∀ x : Xo.XF c, ∃ (X' : USetup C) (w : X'.M.Z), X'.π w = C.i x ∧ X'.S.R ≤ X'.M.O w) :
    ∃ s : Set (USetup C), s.Finite ∧ ∀ x : Xo.XF c, ∃ X' ∈ s, x ∈ X'.cov := by
  haveI := Formalism.L2.Pj.CompFin.isNoetherian_XF Xo c
  suffices key : ∀ T : TopologicalSpace.Closeds (Xo.XF c),
      ∃ s : Set (USetup C), s.Finite ∧ ∀ x ∈ T, ∃ X' ∈ s, x ∈ X'.cov by
    obtain ⟨s, hs, hT⟩ := key ⊤
    exact ⟨s, hs, fun x => hT x trivial⟩
  intro T
  induction T using WellFoundedLT.induction with
  | _ T ih =>
  by_cases hirr : IsIrreducible (T : Set (Xo.XF c))
  · have hg := hirr.isGenericPoint_genericPoint_closure
    rw [T.isClosed.closure_eq] at hg
    obtain ⟨X', w, hw, hR⟩ := h hirr.genericPoint
    obtain ⟨W, hW, hξ, hcov⟩ := USetup.exists_open_cov hw hR
    let T₁ : TopologicalSpace.Closeds (Xo.XF c) := ⟨(T : Set (Xo.XF c)) \ W, T.isClosed.sdiff hW⟩
    have hlt : T₁ < T := by
      refine lt_of_le_of_ne (fun x hx => hx.1) fun e => ?_
      have hmem : hirr.genericPoint ∈ (T₁ : Set (Xo.XF c)) := by
        rw [e]; exact hg.mem
      exact hmem.2 hξ
    obtain ⟨s, hs, hsT⟩ := ih T₁ hlt
    refine ⟨insert X' s, hs.insert X', fun x hx => ?_⟩
    by_cases hxW : x ∈ W
    · exact ⟨X', Set.mem_insert _ _, hcov ⟨by rw [hg.def]; exact hx, hxW⟩⟩
    · obtain ⟨X'', h1, h2⟩ := hsT x ⟨hx, hxW⟩
      exact ⟨X'', Set.mem_insert_of_mem _ h1, h2⟩
  · obtain ⟨S, hSi, hTS⟩ := TopologicalSpace.NoetherianSpace.exists_finset_irreducible T
    have hle : ∀ k ∈ S, k < T := by
      intro k hk
      refine lt_of_le_of_ne ?_ fun e => hirr (e ▸ hSi ⟨k, hk⟩)
      rw [hTS]
      exact Finset.le_sup (f := id) hk
    have hk : ∀ k : S, ∃ s : Set (USetup C), s.Finite ∧ ∀ x ∈ (k : TopologicalSpace.Closeds (Xo.XF c)),
        ∃ X' ∈ s, x ∈ X'.cov := fun k => ih k (hle k k.2)
    choose f hf hfT using hk
    refine ⟨⋃ k, f k, Set.finite_iUnion hf, fun x hx => ?_⟩
    rw [hTS] at hx
    have hx' : x ∈ ((S.sup id : TopologicalSpace.Closeds (Xo.XF c)) : Set (Xo.XF c)) := hx
    rw [TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion] at hx'
    simp only [Set.mem_iUnion, Function.comp_apply, id] at hx'
    obtain ⟨k, hkS, hxk⟩ := hx'
    obtain ⟨X'', h1, h2⟩ := hfT ⟨k, hkS⟩ x hxk
    exact ⟨X'', Set.mem_iUnion.2 ⟨_, h1⟩, h2⟩

theorem exists_fin_uSetup_regular_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), (∀ x : Xo.XF c, ∃ (X' : USetup C) (w : X'.M.Z), X'.π w = C.i x ∧ X'.S.R ≤ X'.M.O w) → ∃ (m : ℕ) (X' : Fin m → USetup C) (U : ∀ k, (X' k).M.Z.Opens), (∀ k, (X' k).S.R ≤ (X' k).M.ringOn (U k)) ∧ ∀ x : Xo.XF c, ∃ k, ∃ w ∈ U k, (X' k).π w = C.i x := by
  intro E _ _ _ H Dw l Xo c C h
  obtain ⟨s, hs, hcov⟩ := USetup.exists_finite_cover h
  haveI := hs.to_subtype
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin s
  refine ⟨m, fun k => (e.symm k).1, fun k => ⟨(e.symm k).1.regSet, (e.symm k).1.isOpen_regSet⟩,
    fun k => fun a ha => RatModel.mem_ringOn.2 fun z hz => hz ha, fun x => ?_⟩
  obtain ⟨X'', hX, w, hw, he⟩ := hcov x
  have key : ∀ Y : USetup C, Y = X'' → ∃ w ∈ Y.regSet, Y.π w = C.i x := by
    rintro Y rfl
    exact ⟨w, hw, he⟩
  exact ⟨e ⟨X'', hX⟩, key _ (by simp)⟩

end GlobalTheory.UPoinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeSubmoduleFiniteIndexNumberField
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan

namespace GlobalTheory

theorem latt_free_sub_full_rank {E : Type} [Field E] [NumberField E] (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    ∃ (f : (Fin (Module.finrank (𝓞 E) X) → 𝓞 E) →ₗ[𝓞 E] X) (m : ℕ), 0 < m ∧
      Function.Injective f ∧ ∀ x : X, m • x ∈ LinearMap.range f := by
  classical
  haveI : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X
  set r := Module.finrank (𝓞 E) X
  obtain ⟨e, he⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := X) (le_refl r)
  let f : (Fin r → 𝓞 E) →ₗ[𝓞 E] X := Fintype.linearCombination (𝓞 E) e
  have hfv' : ∀ c : Fin r → 𝓞 E, f c = ∑ i, c i • e i := fun c => by
    simp [f, Fintype.linearCombination_apply]
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    rw [hfv'] at hc
    exact funext ((Fintype.linearIndependent_iff.mp he) c hc)

  have key : ∀ x : X, ∃ n : ℕ, 0 < n ∧ n • x ∈ LinearMap.range f := by
    intro x
    have hdep : ¬ LinearIndependent (𝓞 E) (Fin.cons x e : Fin (r + 1) → X) := by
      intro h
      have := h.fintype_card_le_finrank
      simp [r] at this
    rw [Fintype.not_linearIndependent_iff] at hdep
    obtain ⟨g, hg, i, hi⟩ := hdep
    rw [Fin.sum_univ_succ] at hg
    simp only [Fin.cons_zero, Fin.cons_succ] at hg
    have ha : g 0 ≠ 0 := by
      intro h0
      rw [h0, zero_smul, zero_add] at hg
      have hz := (Fintype.linearIndependent_iff.mp he) (fun j => g j.succ) hg
      refine hi ?_
      refine Fin.cases h0 (fun j => hz j) i
    have hax : g 0 • x ∈ LinearMap.range f := by
      refine ⟨fun j => - g j.succ, ?_⟩
      rw [hfv']
      simp only [neg_smul, Finset.sum_neg_distrib]
      exact (neg_eq_of_add_eq_zero_left hg)
    have hI : Ideal.span {g 0} ≠ ⊥ := by simpa using ha
    have hN : Ideal.absNorm (Ideal.span {g 0}) ≠ 0 := by
      rwa [Ne, Ideal.absNorm_eq_zero_iff]
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {g 0}))
    refine ⟨Ideal.absNorm (Ideal.span {g 0}), Nat.pos_of_ne_zero hN, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← hb, mul_smul]
    exact Submodule.smul_mem _ _ hax
  choose N hNpos hNmem using key
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := X)
  refine ⟨f, ∏ s ∈ S, N s, Finset.prod_pos (fun s _ => hNpos s), hf, ?_⟩
  have hgen : ∀ s ∈ S, (∏ t ∈ S, N t) • s ∈ LinearMap.range f := by
    intro s hs
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem N hs
    rw [hk, mul_comm, mul_smul]
    exact AddSubmonoid.nsmul_mem (LinearMap.range f).toAddSubmonoid (hNmem s) k
  intro x
  have hx : x ∈ Submodule.span ℤ (S : Set X) := by rw [hS]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen y hy
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [smul_comm]
    exact zsmul_mem hy a

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionThetaSectionIntegralPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_function_thetaSection_integralPoint : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → ∀ (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∃ f : V, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) J, Good D.P.L z J → sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ b.left) z J * (val t r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom f) * (val ρ₀ r z J).val := by
  first | exact @GlobalTheory.IntPointFn.fn_of_theta | exact GlobalTheory.IntPointFn.fn_of_theta | (intros; apply GlobalTheory.IntPointFn.fn_of_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaugedTorusInvariantHeatOperatorStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gauged_torusInvariant_heatOperator : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd ⇑D), (∀ i, (∃ V : Q.P.A.left.Opens, h₁.W i = Y.q.left ⁻¹ᵁ V) ∧ IsWt Y 0 _ (h₁.p i) ∧ IsWt Y 0 _ (h₁.p' i) ∧ ∀ (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h₁.W i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → IsWt Y α (Y.q.left ⁻¹ᵁ V) (h₁.d i _ f)) → ∀ (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X), e.IsGen → (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) → ∃ h' : Heat Y.H Y.q.left Q.P.L dd ⇑D, IsBasic Y h' ∧ h'.Θ = h₁.Θ ∧ h'.u = h₁.u ∧ ∀ (k : ℕ) (σ σ' : SecM ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L k) (ρ ρ' : SecM Y.q.left Q.P.L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ r z J = sval σ r z J * ((val e r z J) ^ k).val) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ' r z J = sval σ' r z J * ((val e r z J) ^ k).val) → h₁.Acts k σ σ' → h'.Acts k ρ ρ' := by
  first | exact @GlobalTheory.Heat.Gauge.exists_gauge_heat | exact GlobalTheory.Heat.Gauge.exists_gauge_heat | (intros; apply GlobalTheory.Heat.Gauge.exists_gauge_heat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingDegenerationDataPrincipalTripleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generating_degenerationData_principalTriple : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t : SAB H (Sp W)), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∃ g, SmoothOfRelativeDimension g t.G.hom) → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x₀ : X → (𝟙_ (Over (Sp W)) ⟶ t.G)), (∀ y z, x₀ (y + z) = x₀ y * x₀ z) → (∀ (a : 𝓞 E) y, x₀ (a • y) = x₀ y ≫ t.act.act a) → ∃ (D : DegPre W) (_ : Module (𝓞 E) D.X) (oa : letI := H.starRing; D.OAct (𝓞 E)) (φB : t.G.left ⟶ D.P.A.left) (e : X ≃ₗ[𝓞 E] D.X), D.PsiEven ∧ D.TauBimult ∧ (∀ y, PsiUnitOn D y Set.univ) ∧ (letI := H.starRing; TraceFormTwistIso D oa H.w0) ∧ IsAbPart t D oa φB ∧ ∀ y, (x₀ y).left ≫ φB = (D.c (e y)).left := by
  first | exact @GlobalTheory.UBaseData.main | exact GlobalTheory.UBaseData.main | (intros; apply GlobalTheory.UBaseData.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullDegCompOfFirstTopStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isPullDeg_comp_of_first_top : ∀ {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D''), p.W = ⊤ → ∃ r : IsPullDeg (j.comp i) D D'', r.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (j.comp i)) = (q.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf j)) ≫ p.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) ∧ ∀ x, r.xe x = p.xe (q.xe x) := by
  first | exact @GlobalTheory.PullDegCompTop.exists_isPullDeg_comp_top | exact GlobalTheory.PullDegCompTop.exists_isPullDeg_comp_top | (intros; apply GlobalTheory.PullDegCompTop.exists_isPullDeg_comp_top <;> assumption)
end

