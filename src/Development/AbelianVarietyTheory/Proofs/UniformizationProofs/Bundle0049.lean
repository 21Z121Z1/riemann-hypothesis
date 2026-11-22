import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitCoboundaryOfMulCocycleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CoeffMemOfPoints
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.UU.RingPoint

noncomputable section
namespace GlobalTheory.UU.UnitCob

section Alg
variable {B C : Type} [CommRing B] [CommRing C] {M N : Type} [AddCommGroup M] [AddCommGroup N]

def ev (κ : B →+* C) (c : Multiplicative M →* Cˣ) : AddMonoidAlgebra B M →+* C :=
  AddMonoidAlgebra.liftNCRingHom κ ((Units.coeHom C).comp c) fun _ _ => Commute.all _ _

theorem ev_single (κ : B →+* C) (c : Multiplicative M →* Cˣ) (m : M) (b : B) :
    ev κ c (AddMonoidAlgebra.single m b) = κ b * (c (Multiplicative.ofAdd m)).val := by
  simp [ev, AddMonoidAlgebra.liftNCRingHom]

def pair (c : Multiplicative M →* Cˣ) (c' : Multiplicative N →* Cˣ) : Multiplicative (M × N) →* Cˣ :=
  MonoidHom.mk' (fun p => c (Multiplicative.ofAdd p.toAdd.1) * c' (Multiplicative.ofAdd p.toAdd.2)) fun p q => by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ofAdd_add, map_mul]
    exact _root_.mul_mul_mul_comm _ _ _ _

theorem map_mapDomain (s : M → N) (F : AddMonoidAlgebra B N →+* C) (G : AddMonoidAlgebra B M →+* C)
    (h : ∀ m b, F (AddMonoidAlgebra.single (s m) b) = G (AddMonoidAlgebra.single m b)) (a : AddMonoidAlgebra B M) :
    F (AddMonoidAlgebra.mapDomain s a) = G a := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [AddMonoidAlgebra.mapDomain_add, map_add, map_add, ha, hb]
  | single m b => rw [AddMonoidAlgebra.mapDomain_single, h]

theorem hom_eq (F G : AddMonoidAlgebra B M →+* C)
    (h : ∀ m b, F (AddMonoidAlgebra.single m b) = G (AddMonoidAlgebra.single m b)) (a : AddMonoidAlgebra B M) :
    F a = G a := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | single m b => exact h m b

theorem ev_eq_zero (κ : B →+* C) (c : Multiplicative M →* Cˣ) (a : AddMonoidAlgebra B M)
    (h : ∀ m, κ (a.coeff m) = 0) : ev κ c a = 0 := by
  rw [← AddMonoidAlgebra.sum_coeff_single a, Finsupp.sum, map_sum]
  exact Finset.sum_eq_zero fun m _ => by rw [ev_single, h, zero_mul]

theorem coeff_mem (I : Ideal B) (G : AddMonoidAlgebra B M →+* AddMonoidAlgebra (B ⧸ I) M)
    (hG : ∀ m b, G (AddMonoidAlgebra.single m b) = AddMonoidAlgebra.single m (Ideal.Quotient.mk I b))
    (a : AddMonoidAlgebra B M) (h : G a = 1) (p : M) : (a - 1).coeff p ∈ I := by
  have k : AddMonoidAlgebra.mapRingHom M (Ideal.Quotient.mk I) a = G a :=
    hom_eq _ G (fun m b => by rw [hG]; simp) a
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← AddMonoidAlgebra.coeff_mapRingHom, map_sub, k, h, map_one, sub_self]
  rfl

def mon (B : Type) [CommRing B] (s : M →+ N) : Multiplicative M →* (AddMonoidAlgebra B N)ˣ :=
  ((AddMonoidAlgebra.of B N).comp (AddMonoidHom.toMultiplicative s)).toHomUnits

theorem mon_val (s : M →+ N) (m : M) :
    (mon B s (Multiplicative.ofAdd m)).val = AddMonoidAlgebra.single (s m) 1 := rfl

end Alg

section Geo
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Y : Over S}

def ev₁ {Z : Over S} (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y) : AddMonoidAlgebra Γ(Y.left, ⊤) X →+* Γ(Z.left, ⊤) :=
  ev y.left.appTop.hom (splitTorusPointsEquiv S X Z t)

def ev₂ {Z : Over S} (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y) :
    AddMonoidAlgebra Γ(Y.left, ⊤) (X × X) →+* Γ(Z.left, ⊤) :=
  ev y.left.appTop.hom (pair (splitTorusPointsEquiv S X Z t) (splitTorusPointsEquiv S X Z t'))

theorem ev₁_single {Z : Over S} (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (m : X) (b) :
    ev₁ t y (AddMonoidAlgebra.single m b) = y.left.appTop.hom b * (chV t m).val := ev_single _ _ _ _

theorem ev₂_single {Z : Over S} (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (m : X × X) (b) :
    ev₂ t t' y (AddMonoidAlgebra.single m b) = y.left.appTop.hom b * ((chV t m.1).val * (chV t' m.2).val) :=
  ev_single _ _ _ _

theorem chV_comp {Z Z' : Over S} (σ : Z' ⟶ Z) (t : Z ⟶ splitTorus S X) (χ : X) :
    (chV (σ ≫ t) χ).val = σ.left.appTop.hom (chV t χ).val := by
  rw [chV_val, chV_val, Rosenlicht.over_appTop_comp]

theorem chV_ext {Z : Over S} {t t' : Z ⟶ splitTorus S X} (h : ∀ χ, (chV t χ).val = (chV t' χ).val) : t = t' :=
  (splitTorusPointsEquiv S X Z).injective (MonoidHom.ext fun a => Units.ext (h a.toAdd))

theorem exists_point {U : Over S} {D : Type} [CommRing D] (e : Γ(U.left, ⊤) ≃+* D) (c : Multiplicative X →* Dˣ) :
    ∃ t : U ⟶ splitTorus S X, ∀ χ, e (chV t χ).val = (c (Multiplicative.ofAdd χ)).val :=
  ⟨(splitTorusPointsEquiv S X U).symm ((Units.map e.symm.toMonoidHom).comp c), fun χ => by
    rw [chV, MulEquiv.apply_symm_apply]; exact e.apply_symm_apply _⟩

theorem exists_coeffs [IsAffine Y.left] (f : Γ((splitTorus S X ⊗ splitTorus S X ⊗ Y).left, ⊤)) :
    ∃ φ : AddMonoidAlgebra Γ(Y.left, ⊤) (X × X), ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      (lift t (lift t' y)).left.appTop.hom f = ev₂ t t' y φ := by
  obtain ⟨U, y₀, e, -, he, hU⟩ := exists_ringPoint Y (AddMonoidAlgebra Γ(Y.left, ⊤) (X × X))
    AddMonoidAlgebra.singleZeroRingHom
  obtain ⟨t₀, h₀⟩ := exists_point (S := S) e (mon _ (AddMonoidHom.inl X X))
  obtain ⟨t₁, h₁⟩ := exists_point (S := S) e (mon _ (AddMonoidHom.inr X X))
  refine ⟨e ((lift t₀ (lift t₁ y₀)).left.appTop.hom f), fun Z t t' y => ?_⟩
  obtain ⟨σ, hσ, Hσ⟩ := hU Z y (ev₂ t t' y) fun b => (ev₂_single t t' y 0 b).trans (by simp [chV_zero])
  have a₀ : σ ≫ t₀ = t := chV_ext fun χ => by
    rw [chV_comp, Hσ, h₀, mon_val, ev₂_single]; simp [chV_zero]
  have a₁ : σ ≫ t₁ = t' := chV_ext fun χ => by
    rw [chV_comp, Hσ, h₁, mon_val, ev₂_single]; simp [chV_zero]
  rw [← Hσ, Rosenlicht.over_appTop_comp, comp_lift, comp_lift, a₀, a₁, hσ]

theorem appTop_ev₁ {Z : Over S} (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (a : AddMonoidAlgebra Γ(Y.left, ⊤) X) :
    (lift t y).left.appTop.hom (ev₁ (fst (splitTorus S X) Y) (snd _ _) a) = ev₁ t y a :=
  hom_eq ((lift t y).left.appTop.hom.comp (ev₁ (fst (splitTorus S X) Y) (snd _ _))) _ (fun m b => by
    rw [RingHom.comp_apply, ev₁_single, ev₁_single, map_mul, ← chV_comp, Rosenlicht.over_appTop_comp, lift_fst,
      lift_snd]) a

abbrev pl {Z W : Scheme.{0}} (r : Z ⟶ W) (u : Γ(W, ⊤)ˣ) : Γ(Z, ⊤)ˣ := Units.map r.appTop.hom.toMonoidHom u

theorem gm_mul_iff {Z W W' W'' : Scheme.{0}} (r₁ : Z ⟶ W) (r₂ : Z ⟶ W') (r₃ : Z ⟶ W'') (r₄ : Z ⟶ W'')
    (u : Γ(W, ⊤)ˣ) (v : Γ(W', ⊤)ˣ) (w : Γ(W'', ⊤)ˣ) :
    (∀ z, gm r₁ z ⊤ u * gm r₂ z ⊤ v = gm r₃ z ⊤ w * gm r₄ z ⊤ w) ↔
      r₁.appTop.hom u.val * r₂.appTop.hom v.val = r₃.appTop.hom w.val * r₄.appTop.hom w.val := by
  have e : ∀ z, (gm r₁ z ⊤ u * gm r₂ z ⊤ v = gm r₃ z ⊤ w * gm r₄ z ⊤ w) =
      (gm (𝟙 Z) z ⊤ (pl r₁ u * pl r₂ v) = gm (𝟙 Z) z ⊤ (pl r₃ w * pl r₄ w)) := fun z => by
    rw [map_mul, map_mul, gm_top r₁, gm_top r₂, gm_top r₃, gm_top r₄]
  simp only [e]
  exact ⟨fun h => congrArg Units.val (unit_ext fun z _ => h z), fun h z => congrArg _ (Units.ext h)⟩

theorem gm_one_iff {Z W : Scheme.{0}} (r : Z ⟶ W) (u : Γ(W, ⊤)ˣ) :
    (∀ z, gm r z ⊤ u = 1) ↔ r.appTop.hom u.val = 1 := by
  have e : ∀ z, (gm r z ⊤ u = 1) = (gm (𝟙 Z) z ⊤ (pl r u) = gm (𝟙 Z) z ⊤ 1) := fun z => by
    rw [map_one, gm_top r]
  simp only [e]
  exact ⟨fun h => congrArg Units.val (unit_ext fun z _ => h z), fun h z => congrArg _ (Units.ext h)⟩

theorem cocycle_of_points [IsAffine Y.left] (φ : AddMonoidAlgebra Γ(Y.left, ⊤) (X × X))
    (h : ∀ (Z : Over S) (t t' t'' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      ev₂ (t * t') t'' y φ * ev₂ t t' y φ = ev₂ t (t' * t'') y φ * ev₂ t' t'' y φ) :
    AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.1, p.2)) φ *
        AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, (0 : X))) φ =
      AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, p.2)) φ *
        AddMonoidAlgebra.mapDomain (fun p : X × X => ((0 : X), p.1, p.2)) φ := by
  obtain ⟨U, y₀, e, -, he, -⟩ := exists_ringPoint Y (AddMonoidAlgebra Γ(Y.left, ⊤) (X × X × X))
    AddMonoidAlgebra.singleZeroRingHom
  obtain ⟨t₀, h₀⟩ := exists_point (S := S) e (mon _ (AddMonoidHom.inl X (X × X)))
  obtain ⟨t₁, h₁⟩ := exists_point (S := S) e (mon _ ((AddMonoidHom.inr X (X × X)).comp (AddMonoidHom.inl X X)))
  obtain ⟨t₂, h₂⟩ := exists_point (S := S) e (mon _ ((AddMonoidHom.inr X (X × X)).comp (AddMonoidHom.inr X X)))
  have key : ∀ (s : X × X → X × X × X) (t t' : U ⟶ splitTorus S X),
      (∀ m : X × X, e (chV t m.1).val * e (chV t' m.2).val = AddMonoidAlgebra.single (s m) 1) →
      AddMonoidAlgebra.mapDomain s φ = e (ev₂ t t' y₀ φ) := fun s t t' H =>
    map_mapDomain s (RingHom.id _) (e.toRingHom.comp (ev₂ t t' y₀)) (fun m b => by
      change _ = e (ev₂ t t' y₀ _)
      rw [ev₂_single, map_mul, map_mul, H, he]
      simp [AddMonoidAlgebra.single_mul_single]) φ
  rw [key _ (t₀ * t₁) t₂, key _ t₀ t₁, key _ t₀ (t₁ * t₂), key _ t₁ t₂, ← map_mul, ← map_mul, h]
  all_goals
    intro m
    simp [chV_mul, h₀, h₁, h₂, mon_val, AddMonoidAlgebra.single_mul_single]

end Geo

section Red
variable {A : Type} [CommRing A] (J : Ideal A) {X : Type} [AddCommGroup X] {Y : Over (Spec (CommRingCat.of A))}

theorem coeff_mem_of_points [IsAffine Y.left] (φ : AddMonoidAlgebra Γ(Y.left, ⊤) (X × X))
    (h : ∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) →
      ∀ (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y), ev₂ t t' y φ = 1) (p : X × X) :
    (φ - 1).coeff p ∈ J.map (strMap Y) := by
  obtain ⟨I, hI⟩ : ∃ I, I = J.map (strMap Y) := ⟨_, rfl⟩
  rw [← hI]
  obtain ⟨U, y₀, e, -, he, -⟩ := exists_ringPoint Y (AddMonoidAlgebra (Γ(Y.left, ⊤) ⧸ I) (X × X))
    (AddMonoidAlgebra.singleZeroRingHom.comp (Ideal.Quotient.mk I))
  obtain ⟨t₀, h₀⟩ := exists_point e (mon _ (AddMonoidHom.inl X X))
  obtain ⟨t₁, h₁⟩ := exists_point e (mon _ (AddMonoidHom.inr X X))
  have hU : ∃ s, s ≫ red J = U.hom := (exists_comp_red_iff J U).2 fun a ha => e.injective (by
    have : Ideal.Quotient.mk I (strMap Y a) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (hI ▸ Ideal.mem_map_of_mem _ ha)
    rw [← appTop_strMap y₀, he, RingHom.comp_apply, this, map_zero, map_zero])
  refine coeff_mem I (e.toRingHom.comp (ev₂ t₀ t₁ y₀)) (fun m b => ?_) φ
    ((congrArg e (h U hU t₀ t₁ y₀)).trans (map_one e)) p
  change e (ev₂ t₀ t₁ y₀ _) = _
  rw [ev₂_single, map_mul, map_mul, he, h₀, h₁, mon_val, mon_val]
  simp [AddMonoidAlgebra.single_mul_single]

end Red

theorem exists_coboundary : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] (Y : Over (Spec (CommRingCat.of A))) [IsAffine Y.left] (f : Γ((splitTorus (Spec (CommRingCat.of A)) X ⊗ splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).left, ⊤)ˣ), (∀ (Z : Over (Spec (CommRingCat.of A))) (t t' t'' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y) (z : Z.left), gm (lift (t * t') (lift t'' y)).left z ⊤ f * gm (lift t (lift t' y)).left z ⊤ f = gm (lift t (lift (t' * t'') y)).left z ⊤ f * gm (lift t' (lift t'' y)).left z ⊤ f) → (∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) → ∀ (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y) (z : Z.left), gm (lift t (lift t' y)).left z ⊤ f = 1) → ∃ g : Γ((splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).left, ⊤)ˣ, (∀ (Z : Over (Spec (CommRingCat.of A))) (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y) (z : Z.left), gm (lift t (lift t' y)).left z ⊤ f * gm (lift (t * t') y).left z ⊤ g = gm (lift t y).left z ⊤ g * gm (lift t' y).left z ⊤ g) ∧ (∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) → ∀ (t : Z ⟶ splitTorus _ X) (y : Z ⟶ Y) (z : Z.left), gm (lift t y).left z ⊤ g = 1) := by
  intro A _ J hJ X _ Y _ f hc h1
  obtain ⟨φ, hφ⟩ := exists_coeffs f.val
  have hI : IsNilpotent (J.map (strMap Y)) := by
    obtain ⟨n, hn⟩ := hJ
    exact ⟨n, by rw [← Ideal.map_pow, hn]; exact Ideal.map_bot⟩
  obtain ⟨u, hu, Hu⟩ := GlobalTheory.T.exists_unit_coboundary_of_cocycle_addMonoidAlgebra _ _ hI X φ
    (coeff_mem_of_points J φ fun Z hZ t t' y => (hφ Z t t' y).symm.trans ((gm_one_iff _ _).1 (h1 Z hZ t t' y)))
    (cocycle_of_points φ fun Z t t' t'' y => by
      rw [← hφ, ← hφ, ← hφ, ← hφ]
      exact (gm_mul_iff _ _ _ _ _ _ _).1 (hc Z t t' t'' y))
  refine ⟨Units.map (ev₁ (fst _ Y) (snd _ _)).toMonoidHom u, fun Z t t' y => (gm_mul_iff _ _ _ _ _ _ _).2 ?_,
    fun Z hZ t y => (gm_one_iff _ _).2 ?_⟩
  · have e := congrArg (ev₂ t t' y) Hu
    rw [map_mul, map_mul, map_mapDomain _ _ (ev₁ (t * t') y), map_mapDomain _ _ (ev₁ t y),
      map_mapDomain _ _ (ev₁ t' y), ← hφ, ← appTop_ev₁ (t * t'), ← appTop_ev₁ t, ← appTop_ev₁ t'] at e
    · exact e
    all_goals
      intro m b
      simp [ev₁_single, ev₂_single, chV_mul, chV_zero]
  · refine (appTop_ev₁ t y u.val).trans ?_
    have hle : J.map (strMap Y) ≤ RingHom.ker y.left.appTop.hom := Ideal.map_le_iff_le_comap.2 fun a ha =>
      (appTop_strMap y a).trans ((exists_comp_red_iff J Z).1 hZ a ha)
    have e : ev₁ t y (u.val - 1) = 0 := ev_eq_zero _ _ _ fun m => hle (hu m)
    rwa [map_sub, map_one, sub_eq_zero] at e

end GlobalTheory.UU.UnitCob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EqOneOfGroupLike
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.UnitRigid

theorem coeff_inl_mul_inr {B X : Type} [CommRing B] [AddCommGroup X] (a b : AddMonoidAlgebra B X) (x y : X) :
    (AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inl X X) a *
      AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inr X X) b).coeff (x, y) = a.coeff x * b.coeff y := by
  classical
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a a' h h' => simp only [map_add, add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h, h']
  | single p r =>
    induction b using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add b b' h h' => simp only [map_add, mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h, h']
    | single q s =>
      simp only [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single,
        AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      by_cases h₁ : p = x <;> by_cases h₂ : q = y <;> simp [h₁, h₂]

theorem eq_one_of_groupLike {B X : Type} [CommRing B] [AddCommGroup X] (I : Ideal B) (hI : ∀ b ∈ I, IsNilpotent b)
    (g : AddMonoidAlgebra B X)
    (h : AddMonoidAlgebra.mapDomainRingHom B ((AddMonoidHom.id X).prod (AddMonoidHom.id X)) g =
      AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inl X X) g *
        AddMonoidAlgebra.mapDomainRingHom B (AddMonoidHom.inr X X) g)
    (h₁ : AddMonoidAlgebra.mapRingHom X (Ideal.Quotient.mk I) g = 1) : g = 1 := by
  classical
  have idem : ∀ x, IsIdempotentElem (g.coeff x) := fun x => by
    have e := congrArg (fun a => a.coeff (x, x)) h
    simp only [coeff_inl_mul_inr] at e
    refine e.symm.trans ?_
    exact Finsupp.mapDomain_apply (f := fun x : X => (x, x)) (fun _ _ q => congrArg Prod.fst q) g.coeff x
  ext x
  have e := congrArg (fun a => a.coeff x) h₁
  simp only [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply] at e ⊢
  split_ifs at e ⊢ with hx
  · have m : 1 - g.coeff x ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, e, map_one, sub_self]
    exact (sub_eq_zero.1 ((idem x).one_sub.eq_zero_of_isNilpotent (hI _ m))).symm
  · exact (idem x).eq_zero_of_isNilpotent (hI _ (Ideal.Quotient.eq_zero_iff_mem.1 e))

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem chV_comp {Z Z' : Over S} (σ : Z' ⟶ Z) (t : Z ⟶ splitTorus S X) (χ : X) :
    (chV (σ ≫ t) χ).val = σ.left.appTop.hom (chV t χ).val := by
  rw [chV_val, chV_val, Rosenlicht.over_appTop_comp]

theorem point_ext {Z : Over S} {t t' : Z ⟶ splitTorus S X} (h : ∀ χ, (chV t χ).val = (chV t' χ).val) : t = t' :=
  (splitTorusPointsEquiv S X Z).injective (MonoidHom.ext fun a => Units.ext (h a.toAdd))

theorem exists_point (Z : Over S) (c : Multiplicative X →* Γ(Z.left, ⊤)) :
    ∃ t : Z ⟶ splitTorus S X, ∀ χ, (chV t χ).val = c (Multiplicative.ofAdd χ) :=
  ⟨(splitTorusPointsEquiv S X Z).symm c.toHomUnits, fun χ => by rw [chV, MulEquiv.apply_symm_apply]; rfl⟩

theorem exists_universal {Y W : Over S} [IsAffine W.left] (y : W ⟶ Y) (u : Γ((splitTorus S X ⊗ Y).left, ⊤)) :
    ∃ g : AddMonoidAlgebra Γ(W.left, ⊤) X, ∀ (Z : Over S) (s : Z ⟶ W) (t : Z ⟶ splitTorus S X)
      (θ : AddMonoidAlgebra Γ(W.left, ⊤) X →+* Γ(Z.left, ⊤)),
      (∀ b, θ (AddMonoidAlgebra.single 0 b) = s.left.appTop.hom b) →
      (∀ χ, θ (AddMonoidAlgebra.single χ 1) = (chV t χ).val) → (lift t (s ≫ y)).left.appTop.hom u = θ g := by
  obtain ⟨U, y₀, e, -, -, H⟩ := RingPoint.exists_ringPoint W (AddMonoidAlgebra Γ(W.left, ⊤) X)
    AddMonoidAlgebra.singleZeroRingHom
  obtain ⟨t₀, ht₀⟩ := exists_point U (e.symm.toMonoidHom.comp (AddMonoidAlgebra.of _ X))
  refine ⟨e ((lift t₀ (y₀ ≫ y)).left.appTop.hom u), fun Z s t θ h₁ h₂ => ?_⟩
  obtain ⟨σ, hσ, hθ⟩ := H Z s θ h₁
  have ht : σ ≫ t₀ = t := point_ext fun χ => by
    rw [chV_comp, hθ, ht₀, ← h₂]
    exact congrArg θ (e.apply_symm_apply _)
  rw [← hθ, ← ht, ← hσ, Category.assoc, ← comp_lift, Rosenlicht.over_appTop_comp]

theorem eq_one_affine {A : Type} [CommRing A] (J : Ideal A) (hJ : IsNilpotent J) {Y W : Over (Spec (CommRingCat.of A))}
    [IsAffine W.left] (u : Γ((splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).left, ⊤))
    (hm : ∀ (Z : Over (Spec (CommRingCat.of A))) (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom u = (lift t y).left.appTop.hom u * (lift t' y).left.appTop.hom u)
    (h₁ : ∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) → ∀ (t : Z ⟶ splitTorus _ X) (y : Z ⟶ Y),
      (lift t y).left.appTop.hom u = 1) (t : W ⟶ splitTorus _ X) (y : W ⟶ Y) : (lift t y).left.appTop.hom u = 1 := by
  obtain ⟨g, hg⟩ := exists_universal y u
  let I : Ideal Γ(W.left, ⊤) := J.map (RingPoint.strMap W)
  have hI : ∀ b ∈ I, IsNilpotent b := fun b hb => by
    obtain ⟨n, hn⟩ := hJ
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hb n
    rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot] at this
    exact this
  have one : g = 1 := by
    refine eq_one_of_groupLike I hI g ?_ ?_
    · obtain ⟨U, s, e, -, he, -⟩ := RingPoint.exists_ringPoint W (AddMonoidAlgebra Γ(W.left, ⊤) (X × X))
        AddMonoidAlgebra.singleZeroRingHom
      have key : ∀ (f : X →+ X × X) (t : U ⟶ splitTorus _ X),
          (∀ χ, (chV t χ).val = e.symm (AddMonoidAlgebra.single (f χ) 1)) →
          (lift t (s ≫ y)).left.appTop.hom u = e.symm (AddMonoidAlgebra.mapDomainRingHom _ f g) := fun f t ht =>
        hg U s t (e.symm.toRingHom.comp (AddMonoidAlgebra.mapDomainRingHom _ f))
          (fun b => e.symm_apply_eq.2 (by rw [he]; simp)) (fun χ => by rw [ht]; simp)
      obtain ⟨t₁, ht₁⟩ := exists_point U (e.symm.toMonoidHom.comp ((AddMonoidAlgebra.of _ (X × X)).comp
        (AddMonoidHom.toMultiplicative (AddMonoidHom.inl X X))))
      obtain ⟨t₂, ht₂⟩ := exists_point U (e.symm.toMonoidHom.comp ((AddMonoidAlgebra.of _ (X × X)).comp
        (AddMonoidHom.toMultiplicative (AddMonoidHom.inr X X))))
      have a₁ : ∀ χ, (chV t₁ χ).val = e.symm (AddMonoidAlgebra.single (AddMonoidHom.inl X X χ) 1) := ht₁
      have a₂ : ∀ χ, (chV t₂ χ).val = e.symm (AddMonoidAlgebra.single (AddMonoidHom.inr X X χ) 1) := ht₂
      apply e.symm.injective
      rw [map_mul, ← key _ t₁ a₁, ← key _ t₂ a₂, ← hm, key]
      intro χ
      rw [chV_mul, Units.val_mul, a₁, a₂, ← map_mul, AddMonoidAlgebra.single_mul_single]
      simp
    · obtain ⟨U, s, e, -, he, -⟩ := RingPoint.exists_ringPoint W (AddMonoidAlgebra (Γ(W.left, ⊤) ⧸ I) X)
        (AddMonoidAlgebra.singleZeroRingHom.comp (Ideal.Quotient.mk I))
      obtain ⟨t₁, ht₁⟩ := exists_point U (e.symm.toMonoidHom.comp (AddMonoidAlgebra.of _ X))
      have a₁ : ∀ χ, (chV t₁ χ).val = e.symm (AddMonoidAlgebra.single χ 1) := ht₁
      have hU : ∃ s, s ≫ red J = U.hom := (RingPoint.exists_comp_red_iff J U).2 fun a ha => by
        apply e.injective
        rw [← RingPoint.appTop_strMap s, he, RingHom.comp_apply,
          Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha), map_zero, map_zero]
      have k := hg U s t₁ (e.symm.toRingHom.comp (AddMonoidAlgebra.mapRingHom X (Ideal.Quotient.mk I)))
        (fun b => e.symm_apply_eq.2 (by rw [he]; simp)) (fun χ => by rw [a₁]; simp)
      apply e.symm.injective
      rw [map_one]
      exact k.symm.trans (h₁ U hU _ _)
  have k := hg W (𝟙 W) t (AddMonoidAlgebra.liftNCRingHom (RingHom.id _)
    ((Units.coeHom _).comp (splitTorusPointsEquiv _ X W t)) fun _ _ => Commute.all _ _)
    (fun b => by simp) (fun χ => by simp [chV])
  rwa [Category.id_comp, one, map_one] at k

theorem unit_eq_one : ∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] (Y : Over (Spec (CommRingCat.of A))) (u : Γ((splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).left, ⊤)ˣ), (∀ (Z : Over (Spec (CommRingCat.of A))) (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y) (z : Z.left), gm (lift (t * t') y).left z ⊤ u = gm (lift t y).left z ⊤ u * gm (lift t' y).left z ⊤ u) → (∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) → ∀ (t : Z ⟶ splitTorus _ X) (y : Z ⟶ Y) (z : Z.left), gm (lift t y).left z ⊤ u = 1) → u = 1 := by
  intro A _ J hJ X _ Y u hm h₁
  have hm' : ∀ (Z : Over (Spec (CommRingCat.of A))) (t t' : Z ⟶ splitTorus _ X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom u.val =
        (lift t y).left.appTop.hom u.val * (lift t' y).left.appTop.hom u.val := fun Z t t' y => by
    have e : Units.map (lift (t * t') y).left.appTop.hom.toMonoidHom u =
        Units.map (lift t y).left.appTop.hom.toMonoidHom u * Units.map (lift t' y).left.appTop.hom.toMonoidHom u :=
      unit_ext fun z _ => by rw [map_mul, ← gm_top, ← gm_top, ← gm_top, hm]
    exact congrArg Units.val e
  have h₁' : ∀ (Z : Over (Spec (CommRingCat.of A))), (∃ s, s ≫ red J = Z.hom) →
      ∀ (t : Z ⟶ splitTorus _ X) (y : Z ⟶ Y), (lift t y).left.appTop.hom u.val = 1 := fun Z hZ t y => by
    have e : Units.map (lift t y).left.appTop.hom.toMonoidHom u = 1 :=
      unit_ext fun z _ => by rw [map_one, ← gm_top, h₁ Z hZ]
    exact congrArg Units.val e
  refine unit_ext fun z _ => ?_
  let 𝒰 := (splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).left.affineCover
  obtain ⟨i, w, rfl⟩ := 𝒰.exists_eq z
  let W : Over (Spec (CommRingCat.of A)) := Over.mk (𝒰.f i ≫ (splitTorus (Spec (CommRingCat.of A)) X ⊗ Y).hom)
  haveI : IsAffine W.left := inferInstanceAs (IsAffine (𝒰.X i))
  let κ : W ⟶ splitTorus (Spec (CommRingCat.of A)) X ⊗ Y := Over.homMk (𝒰.f i) rfl
  have e := eq_one_affine J hJ u.val hm' h₁' (κ ≫ fst _ _) (κ ≫ snd _ _)
  rw [lift_comp_fst_snd] at e
  have e' : Units.map (𝒰.f i).appTop.hom.toMonoidHom u = 1 := Units.ext e
  refine gm_inj (U := ⊤) (U' := ⊤) (𝒰.f i) w trivial trivial ?_
  rw [gm_top, e', map_one, map_one]

end GlobalTheory.UU.UnitRigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenMulPullPowUnif
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem exists_gen_mulPull_pow_unif : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (n k k' : ℕ), k' = k * n ^ 2 → ∃ β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, (𝟙 G ^ n).left] ![(k' : ℤ), -(k : ℤ)]), β.IsGen := by
  intro R _ _ I D A G _ _ U n k k' hk
  have hL := U.LG.isLB
  have hcube : GlobalTheory.MulPull.HasGen U.LG.L (thφ G (x3 G)) thε := ⟨U.cubG.t, U.cubG.isGen⟩
  have hrig : GlobalTheory.MulPull.HasGen U.LG.L (K := PUnit) (fun _ => eSec G) (fun _ => 1) :=
    ⟨U.LG.rig, U.LG.rigGen⟩
  have hneg : GlobalTheory.MulPull.HasGen U.LG.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1] :=
    ⟨U.symG, U.symG_gen⟩
  have main : GlobalTheory.MulPull.HasGen U.LG.L (K := Fin 2) ![(𝟙 G : G ⟶ G).left, (𝟙 G ^ n).left]
      ![(n : ℤ) ^ 2, -1] := by
    refine GlobalTheory.MulPull.hasGen_pow hL hcube (𝟙 G) ?_ ?_ n
    · refine (hrig.pull (toUnit G).left).of_formEq hL (fun W _ h => ?_)
      simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, _root_.mul_one]
      rfl
    · refine hneg.inv.of_formEq hL (fun W _ h => ?_)
      have e : ((𝟙 G : G ⟶ G)⁻¹) = ι[G] := Category.id_comp _
      rw [e]
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
        _root_.mul_one, neg_neg]
      exact _root_.mul_comm _ _
  obtain ⟨t, ht⟩ := main
  have hp : GlobalTheory.MulPull.HasGen U.LG.L (K := Fin 2) ![(𝟙 G : G ⟶ G).left, (𝟙 G ^ n).left]
      (fun i => (k : ℤ) * (![(n : ℤ) ^ 2, -1] : Fin 2 → ℤ) i) := ⟨_, powGen_isGen _ _ _ t ht k⟩
  refine hp.of_formEq hL (fun W _ h => ?_)
  subst hk
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    _root_.mul_one, mul_neg]
  push_cast
  rfl

end GlobalTheory.UT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankSecPullSandwichStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_shift_finrank_sec_pull_bounds : ∀ (K : Type) [Field K] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) [IsFinite φ] [Etale φ] (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ d : ℕ, (∀ x : X, φ.finrank x = d) → (∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤)) → (∀ t : ℕ, Module.Finite K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤)) → ∃ a : ℕ, ∀ t : ℕ, d * Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ Module.finrank K (SecOnR (φ ≫ f) ((pw H (t + a : ℕ)).pull φ) ⊤) ∧ Module.finrank K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) ≤ d * Module.finrank K (SecOnR (f) (pw H (t + a : ℕ)) ⊤) := by
  first | exact @GlobalTheory.finrank_sec_pull_sandwich | exact GlobalTheory.finrank_sec_pull_sandwich | (intros; apply GlobalTheory.finrank_sec_pull_sandwich <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordEndRatioDescendsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gen_of_torusEnd_compat : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a : thickObj R I e G ⟶ thickObj R I e G) (aB : D.P.A ⟶ D.P.A) (h : D.X → D.X) (t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ splitTorus _ D.X), IsMonHom a → TorusEndOf D.X h t → g.i ≫ a = t ≫ g.i → a ≫ g.q = g.q ≫ (Over.pullback (thick R I e)).map aB → ∀ χ : D.X, ∃ u : LB.Gen (LB.LinComb D.P.L (Y := (thickObj R I e D.P.A).left) (fun k => pullback.fst D.P.A.hom (thick R I e) ≫ Sum.elim (D.Oφ (𝟙 _) (h χ)) (D.Oφ aB χ) k) (Sum.elim Oε Oinvε)), u.IsGen ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.P.L z J → val (g.t χ) (x ≫ a.left) z J = val (g.t (h χ)) x z J * val u (x ≫ g.q.left) z J := by
  first | exact @GlobalTheory.gtCoord_end_ratio_descends | exact GlobalTheory.gtCoord_end_ratio_descends | (intros; apply GlobalTheory.gtCoord_end_ratio_descends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionPairEqOfThetaOperatorRelStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.torsionPair_eq_of_thetaOperator_rel : GlobalFnsSt → SecTwistSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 1 ≤ n → ∀ (p p' : QkPt D F n) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε n))) (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p'.g.b) (DegPre.lineε n))), w.IsGen → w'.IsGen → (∀ s : Fam D F n, ∃ s' : Fam D F n, PhiRel D F n p w s s' ∧ PhiRel D F n p' w' s s') → p'.y = p.y → p.g.b = p'.g.b → p.g = p'.g := by
  first | exact @GlobalTheory.qkPt_g_eq_of_phiRel | exact GlobalTheory.qkPt_g_eq_of_phiRel | (intros; apply GlobalTheory.qkPt_g_eq_of_phiRel <;> assumption)
end

