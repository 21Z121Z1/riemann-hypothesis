import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.NeTopOfAdmissibleBase
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2374
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEndOfPadd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def ActsAs {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) (b : D.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D.toPre.X) (g : G ⟶ G) : Prop :=
  ∀ e : ℕ, (Over.pullback (thick R I e)).map g ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R I e)).map b ∧
    ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.toPre.X ⟶ splitTorus _ D.toPre.X,
      TorusEndOf D.toPre.X h t ∧ (U.gt e).i ≫ (Over.pullback (thick R I e)).map g = t ≫ (U.gt e).i

theorem pull_padd {S S' : Scheme.{0}} (f : S' ⟶ S) {T G : Over S} [GrpObj G] (a b : T ⟶ G) :
    (Over.pullback f).map (padd G a b) = padd _ ((Over.pullback f).map a) ((Over.pullback f).map b) := by
  simp [padd, Functor.Monoidal.lift_μ_assoc]

theorem comp_padd' {S : Scheme.{0}} {T T' G : Over S} [GrpObj G] (x : T ⟶ T') (a b : T' ⟶ G) :
    x ≫ padd G a b = padd G (x ≫ a) (x ≫ b) := by
  rw [padd, padd, comp_lift_assoc]

theorem padd_comp_hom {S : Scheme.{0}} {X Y T : Over S} [GrpObj X] [GrpObj Y] (f f' : T ⟶ X) (h : X ⟶ Y) [IsMonHom h] :
    padd X f f' ≫ h = padd Y (f ≫ h) (f' ≫ h) := by
  rw [padd, padd, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]

theorem torusEndOf_padd {S : Scheme.{0}} {X : Type} [AddCommGroup X] {h h' : X → X}
    {t t' : splitTorus S X ⟶ splitTorus S X} (ht : TorusEndOf X h t) (ht' : TorusEndOf X h' t') :
    TorusEndOf X (h + h') (padd _ t t') := by
  rw [GlobalTheory.LinearUnifCheck.torusEndOf_iff] at ht ht' ⊢
  intro χ
  have hc : ∀ x, (charUnit S X x).val =
      (GlobalTheory.splitTorusPointsEquiv S X (splitTorus S X) (𝟙 _) (Multiplicative.ofAdd x)).val := fun x =>
    ((GlobalTheory.splitTorusPointsEquiv_val S X _ (𝟙 _) x).trans (SplitTorusHom.appTop_id _)).symm
  have hp : padd (splitTorus S X) t t' = t * t' := rfl
  rw [hp, ← GlobalTheory.splitTorusPointsEquiv_val, map_mul, MonoidHom.mul_apply, Units.val_mul,
    GlobalTheory.splitTorusPointsEquiv_val, GlobalTheory.splitTorusPointsEquiv_val, ht, ht', hc, hc, hc, Pi.add_apply, ofAdd_add,
    map_mul, Units.val_mul]

theorem actsAs_padd {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) {b b' : D.toPre.P.A ⟶ D.toPre.P.A} {h h' : D.toPre.X → D.toPre.X} {g g' : G ⟶ G}
    (hg : ActsAs U b h g) (hg' : ActsAs U b' h' g') : ActsAs U (padd _ b b') (h + h') (padd G g g') := by
  intro e
  obtain ⟨q1, t, ht, i1⟩ := hg e
  obtain ⟨q2, t', ht', i2⟩ := hg' e
  have := (U.gt e).q_hom
  have := (U.gt e).i_hom
  refine ⟨?_, padd _ t t', torusEndOf_padd ht ht', ?_⟩
  · rw [pull_padd, pull_padd, padd_comp_hom, q1, q2, comp_padd']
  · rw [pull_padd, comp_padd', i1, i2, padd_comp_hom]

theorem actsAs_comp {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) {b b' : D.toPre.P.A ⟶ D.toPre.P.A} {h h' : D.toPre.X → D.toPre.X} {g g' : G ⟶ G}
    (hg : ActsAs U b h g) (hg' : ActsAs U b' h' g') : ActsAs U (b ≫ b') (h ∘ h') (g ≫ g') := by
  intro e
  obtain ⟨q1, t, ht, i1⟩ := hg e
  obtain ⟨q2, t', ht', i2⟩ := hg' e
  refine ⟨?_, t ≫ t', GlobalTheory.LinearUnifCheck.torusEndOf_comp ht ht', ?_⟩
  · rw [Functor.map_comp, Category.assoc, q2, ← Category.assoc, q1, Category.assoc, ← Functor.map_comp]
  · rw [Functor.map_comp, ← Category.assoc, i1, Category.assoc, i2, Category.assoc]

theorem actsAs_id {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) : ActsAs U (𝟙 _) id (𝟙 G) := by
  intro e
  refine ⟨by simp, 𝟙 _, ?_, by simp⟩
  rw [GlobalTheory.LinearUnifCheck.torusEndOf_iff]; intro χ; simp

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointCharacterValuesFixedLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.CharValsFixed

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt GlobalTheory.BXOf GlobalTheory.UnramTorsion

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (T : Subring F) [IsLocalRing T] (φ₁ : R →+* T), (∀ r, (φ₁ r : F) = algebraMap (FractionRing R) F (algebraMap R _ r)) → ∀ (J₀ : D.P.A.left → D.P.L.ι), (∀ x, x ∈ D.P.L.U (J₀ x)) → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ ψ : Sp T ⟶ D.P.A.left, J (spMap T.subtype ≫ ψ) = J₀ (ψ (closedPoint T))) → ∀ (σ : F →+* F), (∀ t ∈ T, σ t = t) → ∀ (g : GtPtF D F) (b : Sp T ⟶ D.P.A.left), spMap T.subtype ≫ b = g.b.left → b ≫ D.P.A.hom = spMap φ₁ → ∀ (S : Set D.X), AddSubgroup.closure S = ⊤ → (∀ χ ∈ S, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F)) → ∀ χ, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) := by
  intro R _ _ D F _ _ T _ φ₁ hφ₁ J₀ h₀ J hJ eJ σ hσ g b hb hbA S hS hSfix
  let ρ : TF (R := R) F ⟶ Over.mk (spMap φ₁) := Over.homMk (spMap T.subtype) (by
    show spMap T.subtype ≫ spMap φ₁ = jFK (R := R) F ≫ jK R
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ₁)
  let w : ((TF (R := R) F).left.presheaf.stalk (closedPoint F))ˣ →* Fˣ :=
    (Units.map σ.toMonoidHom).comp (sig F) * (sig F)⁻¹
  have hwv : ∀ u, ((w u : Fˣ) : F) = σ (sig F u : F) * ((sig F u)⁻¹ : Fˣ) := fun u => rfl
  have hw1 : ∀ u, w u = 1 ↔ σ (sig F u : F) = (sig F u : F) := fun u => by
    constructor
    · intro h
      have e := congrArg Units.val h
      rw [hwv, Units.val_one] at e
      calc σ (sig F u : F) = σ (sig F u : F) * ((sig F u)⁻¹ : Fˣ) * (sig F u : F) := by
            rw [_root_.mul_assoc, Units.inv_mul, _root_.mul_one]
        _ = (sig F u : F) := by rw [e, _root_.one_mul]
    · intro h
      apply Units.ext
      rw [hwv, h, Units.mul_inv, Units.val_one]
  have hw : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ D.P.A.left)) (ε : K → ℤ)
      (t : LB.Gen (LB.LinComb D.P.L φ ε)) (r : (Over.mk (spMap φ₁)).left ⟶ Y),
      w (val t (ρ.left ≫ r) (closedPoint F) J) = 1 := by
    intro Y K _ φ ε t r
    obtain ⟨u, hu⟩ := val_integral T.subtype h₀ eJ t r
    refine (hw1 _).2 ?_
    have hu' : (sig F (val t (ρ.left ≫ r) (closedPoint F) J) : F) = T.subtype u := hu
    rw [hu']
    exact hσ _ (u : T).2
  let b' : Over.mk (spMap φ₁) ⟶ D.P.A := Over.homMk b hbA
  have hgb : g.b = ρ ≫ b' := by
    ext1
    exact hb.symm
  have hth : ∀ χ χ', w (th D (closedPoint F) J (cP D _ χ) (cP D _ χ') g.b) = 1 := fun χ χ' => by
    rw [hgb, ← comp_cP D ρ χ, ← comp_cP D ρ χ']
    exact w_th ρ w hw _ _ _
  let H : AddSubgroup D.X :=
    { carrier := {χ | w (charVal g χ (closedPoint F) J) = 1}
      zero_mem' := by
        show w _ = 1
        rw [charVal_zero g hJ, map_one]
      add_mem' := fun {χ χ'} (h : w _ = 1) (h' : w _ = 1) => by
        show w _ = 1
        have e := congrArg w (charVal_add g hJ χ χ')
        rw [map_mul, map_mul, hth, h, h', _root_.mul_one, _root_.mul_one] at e
        exact e
      neg_mem' := fun {χ} (h : w _ = 1) => by
        show w _ = 1
        have e := congrArg w (charVal_add g hJ χ (-χ))
        rw [map_mul, map_mul, hth, h, _root_.mul_one, _root_.one_mul, add_neg_cancel, charVal_zero g hJ,
          map_one] at e
        exact e.symm }
  have hSH : S ⊆ H := fun χ hχ => (hw1 _).2 (hSfix χ hχ)
  have hH : H = ⊤ := eq_top_iff.2 (hS ▸ (AddSubgroup.closure_le H).2 hSH)
  intro χ
  exact (hw1 _).1 (show χ ∈ H by rw [hH]; trivial)

end GlobalTheory.CharValsFixed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointFixedOfChartValuesFixed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TorusExt

open GlobalTheory.BXOf ReciprocityTheory.ChartRestriction.G.DVR

theorem gtExt_eq_self_of_charVal_fixed : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (σ : F →+* F) (hσ : σ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F) (g : GtPtF D F), spMap σ ≫ g.b.left = g.b.left → ∀ (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L (Z := (TF (R := R) F).left) (closedPoint F) J → (∀ χ, σ (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F) = (GlobalTheory.BXOf.sig F (GlobalTheory.TorusExt.charVal g χ (closedPoint F) J) : F)) → GlobalTheory.TorusExt.gtExt D σ hσ g = g := by
  intro R _ _ D F _ _ σ hσ g hb J hJ hfix
  have hb' : extMap σ hσ ≫ g.b = g.b := Over.OverMorphism.ext hb
  have hφ0 : ∀ χ k, Spec.map (CommRingCat.ofHom σ) ≫ DegPre.gtφ D F g.b χ k = DegPre.gtφ D F g.b χ k := by
    intro χ k
    show (extMap σ hσ).left ≫ DegPre.gtφ D F g.b χ k = DegPre.gtφ D F g.b χ k
    fin_cases k
    · show (extMap σ hσ ≫ (cP D _ χ * g.b)).left = (cP D _ χ * g.b).left
      rw [MonObj.comp_mul, comp_cP, hb']
    · show (extMap σ hσ ≫ cP D _ χ).left = (cP D _ χ).left
      rw [comp_cP]
    · show (extMap σ hσ ≫ g.b).left = g.b.left
      rw [hb']
    · show (extMap σ hσ ≫ (1 : TF (R := R) F ⟶ D.P.A)).left = (1 : TF (R := R) F ⟶ D.P.A).left
      rw [MonObj.comp_one]
  refine gt_ext_val ((gtExt_b σ hσ g).trans hb') fun χ y J' hJ' => ?_
  obtain rfl : y = closedPoint F := Subsingleton.elim (α := PrimeSpectrum F) _ _
  have hdel : ∀ ψ : Spec (CommRingCat.of F) ⟶ D.P.A.left, Spec.map (CommRingCat.ofHom σ) ≫ ψ = ψ →
      del D.P.L σ J J' ψ = del D.P.L (RingHom.id F) J J' ψ := by
    intro ψ h
    unfold del
    rw [h, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have e₁ := val_nat (g.isGen χ) σ hJ hJ' (𝟙 _)
  have e₂ := val_nat (g.isGen χ) (RingHom.id F) hJ hJ' (𝟙 _)
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] at e₂
  have hu : Units.map σ.toMonoidHom (sig F (charVal g χ (closedPoint F) J)) = sig F (charVal g χ (closedPoint F) J) :=
    Units.ext (hfix χ)
  have hu' : Units.map (RingHom.id F).toMonoidHom (sig F (charVal g χ (closedPoint F) J)) =
      sig F (charVal g χ (closedPoint F) J) := Units.ext rfl
  have key : sig F (charVal (gtExt D σ hσ g) χ (closedPoint F) J') = sig F (charVal g χ (closedPoint F) J') := by
    rw [gtExt_val σ hσ g χ hJ', extMap_left, ← Category.comp_id (spMap σ)]
    refine e₁.trans (Eq.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ DegPre.gtε k)
      (hdel _ ((congrArg _ (Category.id_comp _)).trans ((hφ0 χ k).trans (Category.id_comp _).symm))))
      (hu.trans hu'.symm)) e₂.symm)
  exact Units.map_injective (f := (stalkClosedPointIso (CommRingCat.of F)).hom.hom.toMonoidHom)
    (stalkClosedPointIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.injective key

end GlobalTheory.TorusExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionTangentGeneratorsHolomorphicFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.JetGen

theorem mul_dot_basis {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (f : X →+ ℂ) {c : ℂ}
    (hc : c ≠ 0) (χ : X) : c * (co bX χ ⬝ᵥ fun l => f (bX l) / c) = f χ := by
  conv_rhs => rw [← bX.sum_repr χ]
  rw [map_sum, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_zsmul, zsmul_eq_mul]
  simp only [co]
  field_simp

theorem dual_alg (A : DualNumber ℂ) {c d c0 d0 l : ℂ} (hc : c ≠ 0) (hc0 : c0 ≠ 0) (hA : A.fst = 1)
    (hl : l = A.snd + d / c - d0 / c0) :
    A * (TrivSqZeroExt.inl c + TrivSqZeroExt.inr d) * TrivSqZeroExt.inl c0 =
      (1 + TrivSqZeroExt.inr l) * TrivSqZeroExt.inl c * (TrivSqZeroExt.inl c0 + TrivSqZeroExt.inr d0) := by
  ext
  · simp [hA]
  · simp [hA, hl]
    field_simp
    ring

theorem co_add {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (χ χ' : X) :
    co bX (χ + χ') = co bX χ + co bX χ' := by
  ext l; simp [co]

theorem tangent_generators : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X)
    (d : CD N g r bX) (G : Geo ν d.toAB) (gm : GtPt D (TE R ℂ)) (W : Fin g → ℂ),
    (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) → IsD ν d.toAB W gm.b →
    ∃ T : Fin r → ℂ, ∀ (χ : N.X) (ct : Fin g → ℂ), ct = d.t12 *ᵥ co bX χ →
      vE (gm.s (ν.eX χ)) (𝟙 _) ν.J * (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) +
        TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex ct)).left)) ct W) : DualNumber ℂ) *
        TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) =
      (1 + TrivSqZeroExt.inr ((2 * Real.pi * Complex.I : ℂ) * (co bX χ ⬝ᵥ T))) *
        TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex ct)).left) ct) *
        (TrivSqZeroExt.inl (G.frG (ν.J (ν.eA (d.ex 0)).left) 0) +
          TrivSqZeroExt.inr (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W) : DualNumber ℂ) := by
  intro R _ _ _ _ D _ _ _ N ν g r bX d G gm W h0 hD

  set cf : (Fin g → ℂ) → ℂ := fun w => G.frG (ν.J (ν.eA (d.ex w)).left) w with hcf
  set df : (Fin g → ℂ) → ℂ := fun w => fderiv ℂ (G.frG (ν.J (ν.eA (d.ex w)).left)) w W with hdf
  have hc : ∀ w, cf w ≠ 0 := fun w => by
    simp only [hcf, ← G.fr_eq]
    exact mul_ne_zero (Units.ne_zero _) (GlobalTheory.Ex.Arch.AbVal.rg_ne_zero ν)
  set Dl : (Fin g → ℂ) → ℂ := fun w => df w / cf w with hDl
  set A : N.X → DualNumber ℂ := fun χ => vE (gm.s (ν.eX χ)) (𝟙 _) ν.J with hA
  have hA1 : ∀ χ, (A χ).fst = 1 := fun χ => GlobalTheory.T.torusExtension_characterValue_constantTerm_one ν gm h0 (ν.eX χ)
  set ct : N.X → (Fin g → ℂ) := fun χ => d.t12 *ᵥ co bX χ with hct
  have hct_add : ∀ χ χ', ct (χ + χ') = ct χ + ct χ' := fun χ χ' => by
    simp only [hct, co_add, Matrix.mulVec_add]
  have hx : ∀ χ, ν.eA (d.ex (ct χ)) = DegPre.cF D ℂ (ν.eX χ) := fun χ => by
    rw [← d.c_eq]; exact ν.c_eq χ
  have hprod := fun x y z j hj => GlobalTheory.T.cubeValue_complexPoints_eq_frameAlternatingProduct ν d.toAB d.cub G x y z j hj

  have hsnd : ∀ χ χ', (A (χ + χ')).snd + (Dl (ct χ + ct χ') + Dl 0 - Dl (ct χ) - Dl (ct χ')) =
      (A χ).snd + (A χ').snd := fun χ χ' => by
    have hm := GlobalTheory.T.torusExtension_dualCharValues_mul_cube ν gm (ν.eX χ) (ν.eX χ')
    rw [GlobalTheory.T.cube_value_eq_first_jet_alternating_product ν d.toAB G hprod W gm h0 hD _ _ (ct χ) (ct χ') (hx χ) (hx χ'), ← map_add] at hm
    have e := congrArg TrivSqZeroExt.snd hm
    simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_one,
      TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op] at e
    have e1 := hA1 (χ + χ'); have e2 := hA1 χ; have e3 := hA1 χ'
    simp only [hA] at e1 e2 e3 ⊢
    rw [e1, e2, e3] at e
    linear_combination e
  clear hprod
  set ℓ : N.X → ℂ := fun χ => (A χ).snd + Dl (ct χ) - Dl 0 with hℓ
  have hℓ_add : ∀ χ χ', ℓ (χ + χ') = ℓ χ + ℓ χ' := fun χ χ' => by
    have := hsnd χ χ'
    simp only [hℓ, hct_add]
    linear_combination this
  let ℓh : N.X →+ ℂ := AddMonoidHom.mk' ℓ hℓ_add
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨fun l => ℓ (bX l) / (2 * Real.pi * Complex.I), fun χ ct' hct' => ?_⟩
  have hT : (2 * Real.pi * Complex.I : ℂ) * (co bX χ ⬝ᵥ fun l => ℓ (bX l) / (2 * Real.pi * Complex.I)) = ℓ χ :=
    mul_dot_basis bX ℓh h2pi χ
  rw [hT, hct']
  exact dual_alg (A χ) (hc _) (hc 0) (hA1 χ) rfl

end GlobalTheory.MBLow.Cl.JetGen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusPointPermutationSign
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum polydisc defCoord cWt)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusRenumber

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

def permCLE (σ : Equiv.Perm (Fin g)) : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) :=
  (LinearEquiv.funCongrLeft ℂ ℂ σ).toContinuousLinearEquiv

@[simp] theorem permCLE_apply (σ : Equiv.Perm (Fin g)) (w : Fin g → ℂ) : permCLE σ w = w ∘ σ := rfl

def pre (u : HolUnif A L g) (T : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) : HolUnif A L g where
  ex z := u.ex (T z)
  ex_add z w := by rw [map_add, u.ex_add]
  ex_onto y := by
    obtain ⟨x, rfl⟩ := u.ex_onto y
    exact ⟨T.symm x, by simp⟩
  Λ := u.Λ.comap (((T : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).restrictScalars ℤ)
  ker z := by rw [u.ker]; rfl
  discrete := by
    haveI := u.discrete
    exact DiscreteTopology.of_continuous_injective
      (f := fun x : u.Λ.comap (((T : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).restrictScalars ℤ)
        ↦ (⟨T x, x.2⟩ : u.Λ))
      (by fun_prop) (fun x y h ↦ Subtype.ext (T.injective (congrArg Subtype.val h)))
  full := by
    have h1 : ((u.Λ.comap (((T : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).restrictScalars ℤ) :
        Submodule ℤ (Fin g → ℂ)) : Set (Fin g → ℂ)) =
        (T.symm.toLinearEquiv.restrictScalars ℝ : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) '' (u.Λ : Set (Fin g → ℂ)) := by
      ext x
      simp only [SetLike.mem_coe, Submodule.mem_comap, Set.mem_image]
      constructor
      · intro hx; exact ⟨T x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩; simpa using hy
    rw [h1, Submodule.span_image, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact (T.symm.toLinearEquiv.restrictScalars ℝ).surjective
  hol U f := ⟨(u.hol U f).1.preimage T.continuous,
    (u.hol U f).2.comp T.differentiableOn (fun _ hz ↦ hz)⟩
  fr i z := u.fr i (T z)
  fr_hol i := (u.fr_hol i).comp T.differentiableOn (fun _ hz ↦ hz)
  fr_ne i z h := u.fr_ne i (T z) h
  fr_compat i j z h := u.fr_compat i j (T z) h

theorem pre_isDiff (u : HolUnif A L g) (T : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ)) (w : Fin g → ℂ)
    (v : epsR ℂ ⟶ A) : (pre u T).IsDiff w v ↔ u.IsDiff (T w) v := by
  have key : ∀ (U : A.left.Opens) (f : Γ(A.left, U)),
      fderiv ℂ (fun z ↦ valAt' ((pre u T).ex z).left U f) 0 w =
        fderiv ℂ (fun z ↦ valAt' (u.ex z).left U f) 0 (T w) := by
    intro U f
    have : (fun z ↦ valAt' ((pre u T).ex z).left U f) = (fun z ↦ valAt' (u.ex z).left U f) ∘ T := rfl
    rw [this, ContinuousLinearEquiv.comp_right_fderiv, map_zero]
    rfl
  unfold HolUnif.IsDiff
  simp only [key]

end GlobalTheory.TorusRenumber

namespace GlobalTheory.TorusRenumber

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

theorem pre_isAH (u : HolUnif A L g) (T : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ))
    (Hm Hm' : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (h : u.IsAH Hm χ) (hH : Hm'.IsHermitian)
    (hT : ∀ z l, T z ⬝ᵥ Hm.mulVec (star (T l)) = z ⬝ᵥ Hm'.mulVec (star l)) :
    (pre u T).IsAH Hm' (fun l ↦ χ ⟨T l, l.2⟩) := by
  obtain ⟨-, hpos, hχ, hfr⟩ := h
  refine ⟨hH, fun z hz ↦ ?_, fun l ↦ hχ _, fun l i z hz ↦ ?_⟩
  · rw [← hT]
    exact hpos _ (fun h0 ↦ hz (T.injective (by rw [h0, map_zero])))
  · have := hfr ⟨T l, l.2⟩ i (T z) hz
    change u.fr i (T z) = _ * _ * u.fr i (T (z + l))
    rw [this, hT, hT, map_add]

theorem perm_dot_diagonal (σ : Equiv.Perm (Fin g)) (d : Fin g → ℂ) (z l : Fin g → ℂ) :
    permCLE σ z ⬝ᵥ (Matrix.diagonal d).mulVec (star (permCLE σ l)) =
      z ⬝ᵥ (Matrix.diagonal (d ∘ σ.symm)).mulVec (star l) := by
  simp only [permCLE_apply, Matrix.mulVec_diagonal, dotProduct, Function.comp_apply, Pi.star_apply]
  exact Equiv.sum_comp σ (fun i ↦ z i * (d (σ.symm i) * star (l i))) |>.symm.trans (by simp) |>.symm

end GlobalTheory.TorusRenumber

namespace GlobalTheory.TorusRenumber

theorem isTorusPoint_perm  (F : Type) [Field F] [NumberField F] (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ))
    (π : Equiv.Perm (Fin (Module.finrank ℚ F))) (𝔞 𝔟 : FracId F) (z : (F →+* ℝ) → ℂ)
    (X : Obj F (𝔞 * 𝔟⁻¹) (Sp ℂ)) (δ : X.DetOmega)
    (h : IsTorusPoint e 𝔞 𝔟 z X δ) :
      IsTorusPoint (π.trans e) 𝔞 𝔟 z X ((((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℂ) • δ) := by
  obtain ⟨c, u, hc, hlat, hact, ⟨χ, hAH⟩, hdet⟩ := h
  set T := permCLE π.symm with hTdef
  refine ⟨c, pre u T, hc, ?_, ?_, ⟨_, pre_isAH u T _ _ χ hAH ?_ ?_⟩, ?_⟩
  · intro w
    change T w ∈ u.Λ ↔ _
    rw [hlat]
    simp only [hTdef, permCLE_apply, Equiv.trans_apply]
    constructor
    · rintro ⟨m, hm, β, hβ, hw⟩
      refine ⟨m, hm, β, hβ, funext fun i ↦ ?_⟩
      simpa using congrFun hw (π i)
    · rintro ⟨m, hm, β, hβ, rfl⟩
      exact ⟨m, hm, β, hβ, funext fun i ↦ by simp⟩
  · intro a w
    change u.ex (T _) = u.ex (T w) ≫ _
    rw [← hact a (T w)]
    congr 1
    funext j
    simp [hTdef]
  · rw [show (Matrix.diagonal fun i ↦ ((2 * (π.trans e) i (c : F) / (4 * Real.pi ^ 2 * (z ((π.trans e) i)).im) : ℝ) : ℂ)) =
      (Matrix.diagonal fun i ↦ ((2 * e i (c : F) / (4 * Real.pi ^ 2 * (z (e i)).im) : ℝ) : ℂ)).submatrix π π by
        rw [Matrix.submatrix_diagonal_equiv]; rfl]
    exact hAH.1.submatrix π
  · intro w l
    rw [hTdef, perm_dot_diagonal]
    rfl
  · intro v W' hW'
    have hW : ∀ i, u.IsDiff ((W'.submatrix id π.symm) i) (v i).hom := fun i ↦ by
      exact (pre_isDiff u T (W' i) (v i).hom).1 (hW' i)
    rw [AlternatingMap.smul_apply, hdet v _ hW, Matrix.det_permute', Equiv.Perm.sign_symm, smul_eq_mul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs <;> simp [hs]

end GlobalTheory.TorusRenumber
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFrameInvariantUnderDescentDatumStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_frame_invariant_under_descentDatum : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X) (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ)
    (V : Y.Opens) (t : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ), (∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (t i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (t j)) →
    ∀ (c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ),
      (∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (𝟙 _) z _ c = gm (pullback.fst f f) z _ (t i) * gm (𝟙 _) z _ (φ i j) * (gm (pullback.snd f f) z _ (t j))⁻¹) →
    ∀ (V' : Y.Opens), V' ≤ V → ∀ u : Γ(X, f ⁻¹ᵁ V')ˣ, (∀ z : ↥(pullback f f), f (pullback.fst f f z) ∈ V' →
        gm (pullback.fst f f) z _ u * gm (𝟙 _) z _ c = gm (pullback.snd f f) z _ u) →
    ∃ s : ∀ i, Γ(X, f ⁻¹ᵁ V' ⊓ L.U i)ˣ,
      (∀ (i j : L.ι) (x : X), f x ∈ V' → x ∈ L.U i → x ∈ L.U j →
        gm (𝟙 X) x _ (s i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (s j)) ∧
      ∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V' → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (pullback.fst f f) z _ (s i) * gm (𝟙 _) z _ (φ i j) = gm (pullback.snd f f) z _ (s j) := by
  first | exact @GlobalTheory.LBDescent.twist_frame_descent | exact GlobalTheory.LBDescent.twist_frame_descent | (intros; apply GlobalTheory.LBDescent.twist_frame_descent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifTrait
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def UnifTrait {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (G : Over (Sp R))
    [GrpObj G] (L : LB G.left) : Prop :=
  ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (G' : Over (Sp W)) (_ : GrpObj G')
    (_ : IsCommMonObj G') (β : G'.left ⟶ G.left) (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W)))
    (U' : Unif (maximalIdeal W) D' A' G'), GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧
      IsGrpPullback G' G (spMap φ) β ∧ LBIso U'.LG.L (L.pull β) ∧ Nonempty (IsPullDeg φ D.toPre D'.toPre)

end GlobalTheory.Mum
end
end

