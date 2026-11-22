import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2553
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2552
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftedRatiosGenerateSurjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FormalAlg.LevSurj

theorem appLE_cst {R : Type} [CommRing R] {X X' : Scheme.{0}} (g : X' ⟶ X) (f : X ⟶ Spec (CommRingCat.of R))
    (U : X.Opens) (V : X'.Opens) (h : V ≤ g ⁻¹ᵁ U) (a : R) :
    (g.appLE U V h).hom (AbLaw.cst f U a) = AbLaw.cst (g ≫ f) V a := by
  simp only [AbLaw.cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  change ((X.presheaf.map (homOfLE le_top).op ≫ g.appLE U V h).hom) _ =
    ((g.appTop ≫ X'.presheaf.map (homOfLE le_top).op).hom) _
  rw [Scheme.Hom.map_appLE]
  rfl

theorem appLE_of_eq {X X' : Scheme.{0}} (g : X' ⟶ X) (U : X.Opens) (V : X'.Opens) (hV : g ⁻¹ᵁ U = V)
    (h : V ≤ g ⁻¹ᵁ U) (hs : Function.Surjective (g.app U).hom) :
    Function.Surjective (g.appLE U V h).hom ∧ RingHom.ker (g.appLE U V h).hom = RingHom.ker (g.app U).hom := by
  subst hV
  have : g.appLE U (g ⁻¹ᵁ U) h = g.app U := by simp [Scheme.Hom.appLE]
  rw [this]
  exact ⟨hs, rfl⟩

end GlobalTheory.FormalAlg.LevSurj

namespace GlobalTheory.FormalAlg.LevSurj

theorem ev_surjective : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), (∀ e (V : (Y e).left.Opens), towerIdeal Y e (I ^ (e + 1)) V = ⊥) ∧ ∀ e i, Function.Surjective (C.ev e i) := by
  intro R _ I Y β hβ n C
  have h1 : ∀ e (V : (Y e).left.Opens), towerIdeal Y e (I ^ (e + 1)) V = ⊥ := by
    intro e V
    rw [towerIdeal, show thick R I e = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))) from rfl,
      cst_comp_spec, ← Ideal.map_map, Ideal.map_quotient_self, Ideal.map_bot]
  refine ⟨h1, fun e i => ?_⟩
  induction e with
  | zero =>
    have hc : AbLaw.cst ((Y 0).hom ≫ thick R I 0) (C.D 0 i) =
        (AbLaw.cst (Y 0).hom (C.D 0 i)).comp (Ideal.Quotient.mk _) := cst_comp_spec _ _ _
    have : C.ev 0 i = (MvPolynomial.eval₂Hom (AbLaw.cst (Y 0).hom (C.D 0 i)) (C.ρ 0 i)).comp
        (MvPolynomial.map (Ideal.Quotient.mk _)) := by
      ext <;> simp [Charts.ev, hc]
    rw [this]
    exact (C.surj i).comp (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective)
  | succ e ih =>
    have hp : β e ≫ (Y (e + 1)).hom ≫ thick R I (e + 1) = (Y e).hom ≫ thick R I e := by
      rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
    have hev : ((β e).appLE (C.D (e + 1) i) (C.D e i) (C.pre e i).ge).hom.comp (C.ev (e + 1) i) = C.ev e i := by
      rw [Charts.ev, MvPolynomial.comp_eval₂Hom, Charts.ev]
      congr 1
      · ext a
        simp only [RingHom.comp_apply]
        rw [appLE_cst]
        exact congrArg (fun q => AbLaw.cst q (C.D e i) a) (by simpa only [Category.assoc] using hp)
      · funext j
        exact C.ρ_pull e i j
    have hk := (GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (e + 1)) (Y (e + 1)).left (Y e).left ((Y (e + 1)).hom ≫ thick R I (e + 1))
      (β e) (Y e).hom ((GlobalTheory.T.isPullback_thick_tower_squares R I Y β hβ).1 e)).2.2 (C.D (e + 1) i) (C.aff (e + 1) i)
    obtain ⟨hr, hker⟩ := appLE_of_eq (β e) (C.D (e + 1) i) (C.D e i) (C.pre e i) (C.pre e i).ge hk.1
    rw [hk.2] at hker
    set r := ((β e).appLE (C.D (e + 1) i) (C.D e i) (C.pre e i).ge).hom with hr_def
    set c := AbLaw.cst ((Y (e + 1)).hom ≫ thick R I (e + 1)) (C.D (e + 1) i) with hc_def
    set S := (C.ev (e + 1) i).range with hS_def
    have hsq : ∀ x y, x ∈ RingHom.ker r → y ∈ RingHom.ker r → x * y = 0 := by
      intro x y hx hy
      rw [hker] at hx hy
      have hxy := Ideal.mul_mem_mul hx hy
      rw [← Ideal.map_mul, ← pow_add] at hxy
      have hle : (I ^ (e + 1 + (e + 1))).map c ≤ (I ^ (e + 1 + 1)).map c :=
        Ideal.map_mono (Ideal.pow_le_pow_right (by omega))
      have h0 : (I ^ (e + 1 + 1)).map c = ⊥ := h1 (e + 1) (C.D (e + 1) i)
      have := hle hxy
      rw [h0] at this
      exact (Submodule.mem_bot _).1 this
    have hsplit : ∀ b, ∃ s ∈ S, b - s ∈ RingHom.ker r := by
      intro b
      obtain ⟨P, hP⟩ := ih (r b)
      refine ⟨C.ev (e + 1) i P, ⟨P, rfl⟩, ?_⟩
      rw [RingHom.mem_ker, map_sub, ← hP, ← hev, RingHom.comp_apply, sub_self]
    have hKS : ∀ x ∈ RingHom.ker r, x ∈ S := by
      intro x hx
      have hx' := hx
      rw [hker] at hx'
      change x ∈ Submodule.span _ _ at hx'
      induction hx' using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, -, rfl⟩ := hy
        exact ⟨MvPolynomial.C a, by simp [Charts.ev, c]⟩
      | zero => exact S.zero_mem
      | add y z hy hz ihy ihz =>
        have hy' : y ∈ RingHom.ker r := hker ▸ hy
        have hz' : z ∈ RingHom.ker r := hker ▸ hz
        exact S.add_mem (ihy hy') (ihz hz')
      | smul a y hy ihy =>
        have hy' : y ∈ RingHom.ker r := hker ▸ hy
        obtain ⟨s, hs, has⟩ := hsplit a
        have : a • y = s * y + (a - s) * y := by rw [smul_eq_mul]; ring
        rw [this, hsq _ _ has hy', add_zero]
        exact S.mul_mem hs (ihy hy')
    intro b
    obtain ⟨s, hs, hbs⟩ := hsplit b
    have : b ∈ S := by
      have := S.add_mem hs (hKS _ hbs)
      rwa [add_sub_cancel] at this
    exact this

end GlobalTheory.FormalAlg.LevSurj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftedRatiosProjectiveRelations
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg.LiftRatios

theorem appLE_rs {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens} (hU : U' ≤ U) (hV : V' ≤ V)
    (h : V ≤ f ⁻¹ᵁ U) (h' : V' ≤ f ⁻¹ᵁ U') (y : Γ(Y, U)) :
    (f.appLE U' V' h').hom (rs Y hU y) = rs X hV ((f.appLE U V h).hom y) := by
  change (Y.presheaf.map (homOfLE hU).op ≫ f.appLE U' V' h').hom y =
    (f.appLE U V h ≫ X.presheaf.map (homOfLE hV).op).hom y
  rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem app_cst_comp {R : Type} [CommRing R] {X X' : Scheme.{0}} (φ : X' ⟶ X) (f : X ⟶ Spec (CommRingCat.of R))
    (V : X.Opens) (r : R) : (φ.app V).hom (cst f V r) = cst (φ ≫ f) (φ ⁻¹ᵁ V) r := by
  have e := Scheme.Hom.appLE_comp_appLE φ f ⊤ V (φ ⁻¹ᵁ V) (by simp) le_rfl
  rw [Scheme.Hom.app_eq_appLE]
  exact congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) e

theorem preimage_injective {X Y : Scheme.{0}} (f : X ⟶ Y) (hf : Surjective f) {U U' : Y.Opens}
    (h : f ⁻¹ᵁ U = f ⁻¹ᵁ U') : U = U' := by
  refine SetLike.ext fun y => ?_
  obtain ⟨z, rfl⟩ := hf.surj y
  rw [← Scheme.Hom.mem_preimage, ← Scheme.Hom.mem_preimage, h]

theorem mem_of_appLE_mem (R : Type) [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (e : ℕ)
    (V : (Y (e + 1)).left.Opens) (hV : IsAffineOpen V) (W : (Y e).left.Opens) (hW : β e ⁻¹ᵁ V = W)
    (x : Γ((Y (e + 1)).left, V)) (hx : ((β e).appLE V W hW.ge).hom x ∈ towerIdeal Y e I W) :
    x ∈ towerIdeal Y (e + 1) I V := by
  subst hW
  rw [Scheme.Hom.appLE_eq_app] at hx
  obtain ⟨-, -, hk⟩ := GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (e + 1)) _ _ ((Y (e + 1)).hom ≫ thick R I (e + 1)) (β e) (Y e).hom
    ((GlobalTheory.T.isPullback_thick_tower_squares R I Y β hβ).1 e)
  obtain ⟨hs, hker⟩ := hk V hV
  have hc : β e ≫ (Y (e + 1)).hom ≫ thick R I (e + 1) = (Y e).hom ≫ thick R I e := by
    rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
  have hmap : Ideal.map ((β e).app V).hom (towerIdeal Y (e + 1) I V) = towerIdeal Y e I (β e ⁻¹ᵁ V) := by
    unfold towerIdeal
    rw [Ideal.map_map]
    congr 1
    ext r
    rw [RingHom.comp_apply, app_cst_comp, hc]
  have hx' : x ∈ Ideal.comap ((β e).app V).hom (Ideal.map ((β e).app V).hom (towerIdeal Y (e + 1) I V)) := by
    rw [hmap]
    exact hx
  rw [Ideal.comap_map_of_surjective _ hs] at hx'
  have hle : Ideal.comap ((β e).app V).hom ⊥ ≤ towerIdeal Y (e + 1) I V := by
    intro y hy
    have hy' : y ∈ RingHom.ker ((β e).app V).hom := hy
    rw [hker] at hy'
    exact Ideal.map_mono (Ideal.pow_le_self (Nat.succ_ne_zero e)) hy'
  exact SetLike.le_def.1 (sup_le le_rfl hle) hx'

theorem lifted_ratios_mod : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), (∀ e i j, (Y e).left.basicOpen (C.ρ e i j) = C.D e i ⊓ C.D e j) ∧ (∀ e i, C.ρ e i i - 1 ∈ towerIdeal Y e I (C.D e i)) ∧ ∀ e i j l, rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i l) - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) * rs (Y e).left (inf_le_right : C.D e i ⊓ C.D e j ≤ C.D e j) (C.ρ e j l) ∈ towerIdeal Y e I (C.D e i ⊓ C.D e j) := by
  intro R _ I Y β hβ n C
  have hsur : ∀ e, Surjective (β e) := fun e =>
    MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip (GlobalTheory.GenSystem.surjective_thickTrans R I e)
  have h1 : ∀ e i j, (Y e).left.basicOpen (C.ρ e i j) = C.D e i ⊓ C.D e j := by
    intro e
    induction e with
    | zero => exact C.basic
    | succ e ih =>
      intro i j
      refine preimage_injective (β e) (hsur e) ?_
      have hb := Scheme.basicOpen_appLE (β e) (C.D e i) (C.D (e + 1) i) (C.pre e i).ge (C.ρ (e + 1) i j)
      rw [C.ρ_pull, ih] at hb
      rw [Scheme.Hom.preimage_inf, C.pre, C.pre, hb]
      exact (inf_eq_right.2 ((Scheme.Hom.preimage_mono (β e) (Scheme.basicOpen_le _ _)).trans
        (C.pre e i).le)).symm
  refine ⟨h1, ?_, ?_⟩
  · intro e
    induction e with
    | zero =>
      intro i
      rw [C.ρ_self, sub_self]
      exact Ideal.zero_mem _
    | succ e ih =>
      intro i
      refine mem_of_appLE_mem R I Y β hβ e _ (C.aff (e + 1) i) _ (C.pre e i) _ ?_
      rw [map_sub, map_one, C.ρ_pull]
      exact ih i
  · intro e
    induction e with
    | zero =>
      intro i j l
      rw [C.cocycle, sub_self]
      exact Ideal.zero_mem _
    | succ e ih =>
      intro i j l
      have hV : IsAffineOpen (C.D (e + 1) i ⊓ C.D (e + 1) j) := by
        rw [← h1 (e + 1) i j]
        exact (C.aff (e + 1) i).basicOpen _
      have hW : β e ⁻¹ᵁ (C.D (e + 1) i ⊓ C.D (e + 1) j) = C.D e i ⊓ C.D e j := by
        rw [Scheme.Hom.preimage_inf, C.pre, C.pre]
      refine mem_of_appLE_mem R I Y β hβ e _ hV _ hW _ ?_
      rw [map_sub, map_mul, appLE_rs (β e) _ inf_le_left (C.pre e i).ge, appLE_rs (β e) _ inf_le_left (C.pre e i).ge,
        appLE_rs (β e) _ inf_le_right (C.pre e j).ge, C.ρ_pull, C.ρ_pull, C.ρ_pull]
      exact ih i j l

end GlobalTheory.FormalAlg.LiftRatios
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFixedOfQuotientClassesFixedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_fixed_of_quotientClasses_fixed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ (V : Type) [CommRing V] [IsDomain V] (φ : R →+* V) [Algebra (FractionRing R) (AlgebraicClosure (FractionRing V))], (∀ r, algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ (φ r))) → ∀ k : ℕ, 1 ≤ k → ∀ σ : (AlgebraicClosure (FractionRing V)) ≃+* (AlgebraicClosure (FractionRing V)), (∀ v : V, σ (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ v)) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ v)) → (∀ p q : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k, QkExt σ.toRingHom p q → QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing V)) p q) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ k = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  first | exact @GlobalTheory.Mum.TorsFixed.fixed_of_classes_fixed | exact GlobalTheory.Mum.TorsFixed.fixed_of_classes_fixed | (intros; apply GlobalTheory.Mum.TorsFixed.fixed_of_classes_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointAlgebraicModelStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_point_algebraic_model : ∀ (A₀ : Over (Sp Qb)) [GrpObj A₀] (A : Over (Sp ℂ)) [GrpObj A] (p : A.left ⟶ A₀.left) (g n : ℕ),
    IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → IsGrpPullback A A₀ (spMap (algebraMap Qb ℂ)) p →
    1 ≤ n → ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ^ n = 1 →
    ∃ c : 𝟙_ (Over (Sp Qb)) ⟶ A₀, x.left ≫ p = spMap (algebraMap Qb ℂ) ≫ c.left := by
  first | exact @GlobalTheory.RealMult.torsion_of_complex_is_algebraic | exact GlobalTheory.RealMult.torsion_of_complex_is_algebraic | (intros; apply GlobalTheory.RealMult.torsion_of_complex_is_algebraic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointClassAtStalkSmulActionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPointClassAtStalk_smul_action : ∀ {E : Type} [Field E] {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [AddCommGroup M] [Module (𝓞 E) M] (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c') (act : OAct (𝓞 E) G)
    (hlin : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (a : M) (r : 𝓞 E) (A B : Over.mk (x ≫ ℓ) ⟶ G),
      A.left = x ≫ w a → B.left = x ≫ w (r • a) → B = A ≫ act.act r)
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (P : Over.mk t ⟶ G) (r : 𝓞 E)
    (PT RT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hRT : RT ≫ (torsion.ι G n).left = (P ≫ act.act r).left) (x : Sp K) (cP cR : M)
    (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) cP) (hcR : GlobalTheory.TorsSpec.ValAt G n ℓ w (RT x) cR), cR = r • cP := by
  first | exact @GlobalTheory.TorsSpec.class_act | exact GlobalTheory.TorsSpec.class_act | (intros; apply GlobalTheory.TorsSpec.class_act <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointClassImageEqLevelAction
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

theorem exists_torsion_map_of_isGrpPullback {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) {f : X' ⟶ X'}
    {φ : G.left ⟶ G.left} (h : IsGrpPullback G G f φ) (hc : (mulN G n).left ≫ φ = φ ≫ (mulN G n).left) :
    ∃ τ : (torsion G n).left ⟶ (torsion G n).left,
      τ ≫ (torsion.ι G n).left = (torsion.ι G n).left ≫ φ ∧ τ ≫ (torsion G n).hom = (torsion G n).hom ≫ f := by
  have hP := GrpTangent.isPullback_torsion G n
  have hw : ((torsion.ι G n).left ≫ φ) ≫ (mulN G n).left =
      ((torsion G n).hom ≫ f) ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left := by
    have e := eta_comp_of_isGrpPullback h
    rw [Category.assoc, ← hc, ← Category.assoc, hP.w]
    exact (Category.assoc _ _ _).trans
      ((congrArg ((torsion G n).hom ≫ ·) e).trans (Category.assoc _ _ _).symm)
  exact ⟨hP.lift _ _ hw, hP.lift_fst _ _ hw, hP.lift_snd _ _ hw⟩

theorem class_move : ∀ {E : Type} [Field E] {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [AddCommGroup M] [Module (𝓞 E) M] (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c') (act : OAct (𝓞 E) G)
    {Γ : Type} [Group Γ] (ρ' : Γ →* Aut X') (ρ : Γ →* Aut V) (hρ : ∀ γ, (ρ γ).hom ≫ ℓ = ℓ ≫ (ρ' γ).hom)
    (ι : Γ →* (M ≃ₗ[𝓞 E] M)) (m : Γ → (G.left ⟶ G.left)) (hm : GlobalTheory.EqvAct.IsEqvAct ρ' G act m)
    (hmv : ∀ γ c, w c ≫ m γ = (ρ γ).hom ≫ w (ι γ c))
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (γ : Γ) (P Q : Over.mk t ⟶ G)
    (PT QT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hQT : QT ≫ (torsion.ι G n).left = Q.left) (hPQ : Q.left = P.left ≫ m γ) (x : Sp K) (cP cQ : M)
    (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) cP) (hcQ : GlobalTheory.TorsSpec.ValAt G n ℓ w (QT x) cQ), cQ = ι γ cP := by
  intro E _ X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ _ hun act Γ _ ρ' ρ hρ ι m hm hmv K _ _ t γ P Q PT QT hPT hQT hPQ
    x cP cQ hcP hcQ
  haveI := mono_torsion_ι G n
  have hpb := hm.1 γ
  obtain ⟨τ, hτι, hτh⟩ := exists_torsion_map_of_isGrpPullback G n hpb
    (by rw [← act_natCast act n]; exact hm.2.1 γ _)
  have hPQT : PT ≫ τ = QT := by
    rw [← cancel_mono (torsion.ι G n).left, Category.assoc, hτι, reassoc_of% hPT, hQT, hPQ]
  have hq : τ (PT x) = QT x := by rw [← hPQT, Scheme.Hom.comp_apply]
  have hιh : (torsion.ι G n).left ≫ G.hom = (torsion G n).hom := Over.w _
  have hval : ValAt G n ℓ w (PT x) ((ι γ).symm cQ) := by
    intro Ω _ _ y z hyz
    rw [← hq] at hcQ
    have key := Scheme.SpecMap_stalkMap_fromSpecStalk τ (x := PT x)
    have h1 := hcQ Ω (y ≫ Spec.map (τ.stalkMap (PT x))) (z ≫ (ρ γ).hom) (by
      simp only [Category.assoc, reassoc_of% key, hτh, hρ, reassoc_of% hyz])
    simp only [Category.assoc, reassoc_of% key, hτι] at h1
    refine hpb.1.hom_ext ?_ ?_
    · simp only [Category.assoc, hmv, LinearEquiv.apply_symm_apply]
      exact h1
    · simp only [Category.assoc, hw, hιh]
      exact hyz
  rw [valAt_unique G n hn ℓ w hw hun (PT x) cP _ hcP hval, LinearEquiv.apply_symm_apply]

end GlobalTheory.TorsSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointLocallyConstantComplexAbelianStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPoint_locally_constant_complexAbelian : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (N : ℕ), 1 ≤ N → ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ^ N = 1 →
    ∀ t : T.left, ∃ (U : T.left.Opens) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A), t ∈ U ∧ U.ι ≫ x.left = U.ι ≫ T.hom ≫ y.left := by
  first | exact @GlobalTheory.TorsionLocal.locally_eq_const_of_pow_eq_one | exact GlobalTheory.TorsionLocal.locally_eq_const_of_pow_eq_one | (intros; apply GlobalTheory.TorsionLocal.locally_eq_const_of_pow_eq_one <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointTransferThroughCommonGrpPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPoint_transfer_through_common_grpPullback : ∀ {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] (K : Type) [Field K] [Algebra (FractionRing V) K] [Algebra (FractionRing V') K] (A : PolAV (Sp (FractionRing V))) (A' : PolAV (Sp (FractionRing V'))) (P₀ : PolAV (Sp K)) (a : P₀.A.left ⟶ A.A.left) (a' : P₀.A.left ⟶ A'.A.left), IsGrpPullback P₀.A A.A (spMap (algebraMap (FractionRing V) K)) a → IsGrpPullback P₀.A A'.A (spMap (algebraMap (FractionRing V') K)) a' → ∀ (m : ℕ) (x : TFK (R := V) K ⟶ A.A), x ^ m = 1 → ∃ (w : Sp K ⟶ P₀.A.left) (x' : TFK (R := V') K ⟶ A'.A), w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a = x.left ∧ w ≫ a' = x'.left ∧ x' ^ m = 1 := by
  first | exact @GlobalTheory.PtTrans.ptTrans | exact GlobalTheory.PtTrans.ptTrans | (intros; apply GlobalTheory.PtTrans.ptTrans <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTowerPresentationCotangentPullbackResRigiStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionTowerPresentation_cotangentPullback_res_rigidification : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (n : ℕ), cotMap (G.res n) (d.om (n + 1)) = d.om n := by
  first | exact @GlobalTheory.PtExt.OmRes.cotMap_res_om | exact GlobalTheory.PtExt.OmRes.cotMap_res_om | (intros; apply GlobalTheory.PtExt.OmRes.cotMap_res_om <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionGeometricFibresOfDescendedGroup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem torusExtension_of_descended : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → Surjective π → ∀ (G' : Over S) [GrpObj G'] (G : Over (Sp R)) [GrpObj G] (β : G'.left ⟶ G.left), IsGrpPullback G' G π β → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ S), Nonempty (TorusExtension ((Over.pullback t).obj G'))) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ Sp R), Nonempty (TorusExtension ((Over.pullback p).obj G)) := by
  intro R _ S π hlft hsurj G' _ G _ β h hG' Ω _ _ p
  haveI := hlft
  haveI := hsurj
  obtain ⟨t, rfl⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective π p
  have h1 := (isGrpPullback_pullback G' t).comp h
  have h2 := isGrpPullback_pullback G (t ≫ π)
  obtain ⟨e, he, -⟩ := grpPullback_iso h1 h2
  haveI := he
  exact ⟨torusExtOfIso e (hG' Ω t).some⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointCharacterValuesFixedLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtensionPoint_characterValues_fixed_local : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → ∀ (σ : F →+* F), (∀ t ∈ T, σ t = t) → ∀ (g : GtPtF D F) (b : Sp T ⟶ D.P.A.left), spMap T.subtype ≫ b = g.b.left → b ≫ D.P.A.hom = spMap φ₁ → ∀ (S : Set D.X), AddSubgroup.closure S = ⊤ → (∀ χ ∈ S, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F)) → ∀ χ, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) := by
  first | exact @GlobalTheory.CharValsFixed.main | exact GlobalTheory.CharValsFixed.main | (intros; apply GlobalTheory.CharValsFixed.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointFixedOfChartValuesFixedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtensionPoint_fixed_of_chartValues_fixed : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (σ : F →+* F) (hσ : σ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F) (g : GtPtF D F), spMap σ ≫ g.b.left = g.b.left → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ χ, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F)) → GlobalTheory.TorusExt.gtExt D σ hσ g = g := by
  first | exact @GlobalTheory.TorusExt.gtExt_eq_self_of_charVal_fixed | exact GlobalTheory.TorusExt.gtExt_eq_self_of_charVal_fixed | (intros; apply GlobalTheory.TorusExt.gtExt_eq_self_of_charVal_fixed <;> assumption)
end

