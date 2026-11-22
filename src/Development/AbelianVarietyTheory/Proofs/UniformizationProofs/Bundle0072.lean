import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0047
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyTrivialTorusQuotientFlatSurjectiveCosets
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsProdB
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem prod_famT {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (α : D.X) (k : ℕ) {U : Type} [CommGroup U] (h : ((T ⊗ D.P.A).left ⟶ D.P.A.left) → U) :
    ∏ i, h (famφT D T α i) ^ DegPre.famε k i =
      h (snd T D.P.A).left ^ ((k : ℤ) - 1) * h (DVR.cP D (T ⊗ D.P.A) α * snd T D.P.A).left *
        (h (DVR.cP D (T ⊗ D.P.A) α).left)⁻¹ * h (1 : T ⊗ D.P.A ⟶ D.P.A).left := by
  have e₁ : famφT D T α 1 = (DVR.cP D (T ⊗ D.P.A) α * snd T D.P.A).left :=
    congrArg (fun q : T ⊗ D.P.A ⟶ D.P.A => q.left) (mul_comm (snd T D.P.A) (DVR.cP D (T ⊗ D.P.A) α))
  have e₂ : famφT D T α 2 = (DVR.cP D (T ⊗ D.P.A) α).left := rfl
  have e₃ : famφT D T α 3 = (1 : T ⊗ D.P.A ⟶ D.P.A).left := rfl
  rw [Fin.prod_univ_four, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]; rfl

theorem exists_isProdB : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (k l : ℕ) (β ga α : D.X), β + ga = α → ∀ (f : SecBT D T k β) (g : SecBT D T l ga),
    ∃ h : SecBT D T (k + l) α, IsProdB f g h := by
  intro R _ _ D T k l β ga α hα f g
  subst hα
  let a : T ⊗ D.P.A ⟶ D.P.A := DVR.cP D _ β
  let b : T ⊗ D.P.A ⟶ D.P.A := DVR.cP D _ ga
  let x : T ⊗ D.P.A ⟶ D.P.A := snd T D.P.A
  have hu := DVR.pullGen_isGen _ _ _ _ D.cub.isGen (lift a (lift b x)).left
  obtain ⟨t, ht⟩ := exists_sec D.P.isLB (φ' := famφT D T (β + ga)) (ε' := DegPre.famε (k + l)) (fun U _ h => by
      have p₁ := prod_cub a b x h
      have p₂ := prod_famT D T β k h
      have p₃ := prod_famT D T ga l h
      have p₄ := prod_famT D T (β + ga) (k + l) h
      rw [DVR.cPoint_add] at p₄
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4 ⊕ Fin 4) (K' := thK) (U := U) _
        (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₂ p₃) p₁) (Eq.trans ?_ p₄.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, a, b, x]
      push_cast
      module)
    (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.mulSec f g) (genSec (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift a (lift b x)).left) hu))
  refine ⟨t, fun Z r z J hJ => ?_⟩
  refine (ht _ _ z J hJ).trans ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
    (H1.SectionArithmetic.sval_mulSec _ _ _ z hJ) ((sval_genSec _ hu _ z hJ).trans (congrArg Units.val
      ((val_cub D.cub r hJ a b x).trans ?_)))))
  rw [DVR.comp_cP, DVR.comp_cP]; rfl

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLimitUnit
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.FormalValue

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NormGen

theorem exists_factor {V W : Type} [CommRing V] [CommRing W] (I : Ideal V) (φ : V →+* W) (e : ℕ) {Z : Scheme.{0}}
    (r : Z ⟶ Sp W) (σ : Z ⟶ Sp (V ⧸ I ^ (e + 1))) (h : σ ≫ thick V I e = r ≫ spMap φ) :
    ∃ ρ : Z ⟶ Sp (W ⧸ I.map φ ^ (e + 1)), ρ ≫ thick W (I.map φ) e = r := by
  let ψ : CommRingCat.of W ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).inv ≫ r.appTop
  have hr : Z.toSpecΓ ≫ Spec.map ψ = r := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hk : I.map φ ^ (e + 1) ≤ RingHom.ker ψ.hom := by
    rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro v hv
    have e₁ : CommRingCat.ofHom φ ≫ ψ = CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (V ⧸ I ^ (e + 1)))).inv ≫ σ.appTop := by
      rw [Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop,
        ← Scheme.Hom.comp_appTop, h]
    have e₂ := congrArg (fun q => q.hom v) e₁
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
      Ideal.Quotient.eq_zero_iff_mem.2 hv, map_zero] at e₂
    exact e₂
  refine ⟨Z.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ ψ.hom hk)), ?_⟩
  rw [Category.assoc, ← Spec.map_comp, ← hr]
  rfl

theorem gs_valR {A : Type} [CommRing A] {X Z : Scheme.{0}} (ρ : Z ⟶ Sp A) (y : Sp A ⟶ X) (V : X.Opens)
    (ht : ⊤ ≤ y ⁻¹ᵁ V) (s : Γ(X, V)) (z : Z) :
    gs ρ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (valR y V s)) = gs (ρ ≫ y) z V s := by
  rw [valR, dif_pos ht, Iso.hom_inv_id_apply, ← gs_pull ρ y z V (ht trivial)]
  exact gs_res ρ z ht trivial _

theorem valR_id {A : Type} [CommRing A] (a : A) :
    valR (𝟙 (Sp A)) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = a := by
  rw [valR, dif_pos (show ⊤ ≤ 𝟙 (Sp A) ⁻¹ᵁ ⊤ from le_top)]
  have : Scheme.Hom.appLE (𝟙 (Sp A)) ⊤ ⊤ le_top = 𝟙 _ := by
    exact (Category.id_comp _).trans ((Sp A).presheaf.map_id _)
  rw [this]
  exact Iso.inv_hom_id_apply _ _

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem exists_limit_unit (U : PreU I D A G) {W : Type} [CommRing W] [IsLocalRing W] (φ : R →+* W)
    [IsAdicComplete (I.map φ) W] (x : Sp W ⟶ G.left) (hx : x ≫ G.hom = spMap φ) (b : Sp W ⟶ D.P.A.left)
    (hb : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → xe ≫ (U.gt e).pG.left = r ≫ b)
    {jL : U.P.L.L.ι} {jM : D.P.L.ι} (hL : ⊤ ≤ x ⁻¹ᵁ U.P.L.L.U jL) (hM : ⊤ ≤ b ⁻¹ᵁ D.P.L.U jM) :
    ∃ a : Γ(Sp W, ⊤)ˣ, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, gm r z ⊤ a * gw (U.w e) xe z jM (fun _ => jL) = 1 := by
  choose y hy using exists_lift_thick I G φ x hx
  have mL : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, (fstG I e G).left (xe z) ∈ U.P.L.L.U jL := fun e Z r xe h z =>
    (congrArg (fun q => q z ∈ U.P.L.L.U jL) h).mpr (hL (show r z ∈ (⊤ : (Sp W).Opens) from trivial))
  have mM : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, (U.gt e).pG.left (xe z) ∈ D.P.L.U jM := fun e Z r xe h z =>
    (congrArg (fun q => q z ∈ D.P.L.U jM) (hb e Z r xe h)).mpr (hM (show r z ∈ (⊤ : (Sp W).Opens) from trivial))
  let O : ∀ e, (thickObj R I e G).left.Opens := fun e =>
    (D.P.L.pull (U.gt e).pG.left).U (fun _ => jM) ⊓ (U.P.L.L.pull (fstG I e G).left).U (fun _ => jL)
  let s : ∀ e, Γ((thickObj R I e G).left, O e)ˣ := fun e => (U.w e).s (fun _ => jM, fun _ => jL)
  have mO : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Sp W) (xe : Z ⟶ (thickObj R I e G).left),
      xe ≫ (fstG I e G).left = r ≫ x → ∀ z : Z, xe z ∈ O e := fun e Z r xe h z =>
    ⟨mem_pull.2 (mM e Z r xe h z), mem_pull.2 (mL e Z r xe h z)⟩
  have ht : ∀ e, ⊤ ≤ y e ⁻¹ᵁ O e := fun e z _ => mO e _ _ _ (hy e) z
  have hc : ∀ e, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))
      (valR (y (e + 1)) (O (e + 1)) (s (e + 1)).val) = valR (y e) (O e) (s e).val := fun e => by
    have := isLocalRing_quotient_pow (ne_top_of_isHausdorff (I.map φ)) e
    have := fstG_mono (I := I) (G := G) (e + 1)
    have e₁ : thickTrans W (I.map φ) e ≫ y (e + 1) = y e ≫ thickMap R I e G := by
      rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, Category.assoc, hy,
        show thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left from thickMap_comp_fGl I e G, hy,
        ← Category.assoc, thickTrans_comp]
    apply toStkA_injective
    refine (toStkA_map_valR _ _ _ _ (ht _) _).trans (Eq.trans ?_ (toStkA_valR_eq_gs _ _ _ (ht _) _).symm)
    refine (gs_unit _ _ _ (mO (e + 1) _ (thickTrans W (I.map φ) e ≫ thick W (I.map φ) (e + 1)) _ (by
      rw [Category.assoc, hy, Category.assoc]) _) _).trans (Eq.trans ?_ (gs_unit _ _ _ (mO e _ _ _ (hy e) _) _).symm)
    refine congrArg Units.val ((congrArg (fun q => gm q _ (O (e + 1)) (s (e + 1))) e₁).trans ?_)
    exact U.w_compat e _ (y e) _ jM jL (mM e _ _ _ (hy e) _) (mL e _ _ _ (hy e) _)
  obtain ⟨a, ha⟩ := exists_unit_limit (I.map φ) _ hc fun e => isUnit_valR _ _ (ht e) _
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom.toMonoidHom a, fun e Z r xe h z => ?_⟩
  obtain ⟨ρ, rfl⟩ := exists_factor I φ e r (xe ≫ (thickObj R I e G).hom) (by
    rw [← hx, ← Category.assoc r, ← h, Category.assoc, Category.assoc]
    exact congrArg (xe ≫ ·) pullback.condition.symm)
  have := fstG_mono (I := I) (G := G) e
  obtain rfl : xe = ρ ≫ y e := by
    rw [← cancel_mono (fstG I e G).left, h, Category.assoc, Category.assoc, hy]
  apply Units.ext
  have H := congrArg (fun t => gs ρ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (W ⧸ I.map φ ^ (e + 1)))).inv.hom t)) (ha e)
  simp only [map_mul, map_one] at H
  rw [gs_mul ρ z ⊤ trivial, gs_valR _ _ _ (ht e), gs_unit _ _ _ (mO e _ _ _ h z), gs_eq ρ z ⊤ trivial 1, map_one,
    map_one] at H
  refine Eq.trans (congrArg₂ (· * ·) ?_ rfl) H
  rw [← gs_unit _ z ⊤ trivial, ← gs_valR ρ (thick W (I.map φ) e) ⊤ le_top]
  refine congrArg (fun t => gs ρ z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (W ⧸ I.map φ ^ (e + 1)))).inv.hom t)) ?_
  have k := valR_spMap (Ideal.Quotient.mk (I.map φ ^ (e + 1))) (𝟙 (Sp W)) ⊤ le_top
    ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom a.val)
  rw [valR_id, Category.comp_id] at k
  exact k

theorem one_pG (U : PreU I D A G) {T : Over (Spec (CommRingCat.of R))} (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T.left)
    (oe : Z ⟶ (thickObj R I e G).left) (h : oe ≫ (fstG I e G).left = r ≫ (1 : T ⟶ G).left) :
    oe ≫ (U.gt e).pG.left = r ≫ (1 : T ⟶ D.P.A).left := by
  have hf : ∀ (H : Over (Spec (CommRingCat.of R))) [GrpObj H],
      eSec (thickObj R I e H) ≫ (fstG I e H).left = thick R I e ≫ eSec H := fun H _ => by
    show eSec (thickObj R I e H) ≫ pullback.fst H.hom (thick R I e) = _
    simp [eSec]
    rw [pullback.lift_fst, ← Category.assoc, ← pullback.condition, Category.comp_id]
  have hp : eSec (thickObj R I e G) ≫ (U.gt e).pG.left = thick R I e ≫ eSec D.P.A := by
    have := (U.gt e).q_hom
    have h : eSec (thickObj R I e G) ≫ (U.gt e).q.left = eSec (thickObj R I e D.P.A) :=
      congrArg (·.left) (IsMonHom.one_hom (U.gt e).q)
    rw [← hf D.P.A, ← h, Category.assoc]
    rfl
  have hσ : (oe ≫ (thickObj R I e G).hom) ≫ thick R I e = r ≫ T.hom := by
    rw [← Over.w (1 : T ⟶ G), ← Category.assoc r, ← h, Category.assoc, Category.assoc]
    exact congrArg (oe ≫ ·) pullback.condition.symm
  have := fstG_mono (I := I) (G := G) e
  have ho : oe = (oe ≫ (thickObj R I e G).hom) ≫ eSec (thickObj R I e G) := by
    rw [← cancel_mono (fstG I e G).left, h, Category.assoc _ (eSec _), hf, ← Category.assoc _ (thick R I e), hσ,
      one_left, Category.assoc]
  rw [ho, Category.assoc _ (eSec _), hp, ← Category.assoc _ (thick R I e), hσ, one_left, Category.assoc]

theorem gw_change (U : PreU I D A G) (e : ℕ) {Z : Scheme.{0}} (xe : Z ⟶ (thickObj R I e G).left) (z : Z)
    {p : Z ⟶ G.left} {q : Z ⟶ D.P.A.left} (hp : xe ≫ (fstG I e G).left = p) (hq : xe ≫ (U.gt e).pG.left = q)
    {j j' : D.P.L.ι} {k k' : U.P.L.L.ι} (hj : q z ∈ D.P.L.U j) (hj' : q z ∈ D.P.L.U j') (hk : p z ∈ U.P.L.L.U k)
    (hk' : p z ∈ U.P.L.L.U k') :
    gw (U.w e) xe z j (fun _ => k) =
      gm q z _ (D.P.L.g j j') * (gm p z _ (U.P.L.L.g k k'))⁻¹ * gw (U.w e) xe z j' (fun _ => k') := by
  subst hp hq
  have w := (isGen_iff _).1 (U.w_gen e) Z xe z j j' (fun _ => k) (fun _ => k') hj hj' (mem_pull.2 hk) (mem_pull.2 hk')
  rw [gm_pull_g _ _ xe z _ _ (mem_pull.2 hk) (mem_pull.2 hk')] at w
  exact w

theorem exists_normAt : AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ (a : Multiplicative D.X →* Wˣ) (x : TA V W ⟶ G), U.TorPt a x → ∃ ν, U.NormAt x ν := by
  intro V _ _ _ _ D A G _ _ U W _ _ _ hW a x hx
  have := hW.2.2.2.2
  obtain ⟨jx, hjx⟩ := exists_chart U.P.L.isLB (x.left (cpt W))
  obtain ⟨jo, hjo⟩ := exists_chart U.P.L.isLB ((1 : TA V W ⟶ G).left (cpt W))
  obtain ⟨jM, hjM⟩ := exists_chart D.P.isLB ((1 : TA V W ⟶ D.P.A).left (cpt W))
  replace hjx := (top_le_iff_cpt (A := W) x.left _).2 hjx
  replace hjo := (top_le_iff_cpt (A := W) (1 : TA V W ⟶ G).left _).2 hjo
  replace hjM := (top_le_iff_cpt (A := W) (1 : TA V W ⟶ D.P.A).left _).2 hjM
  obtain ⟨α, hα⟩ := exists_limit_unit U (algebraMap V W) x.left (Over.w x) (1 : TA V W ⟶ D.P.A).left
    (fun e Z r xe h => (hx e Z r xe h).1) hjx hjM
  obtain ⟨β, hβ⟩ := exists_limit_unit U (algebraMap V W) (1 : TA V W ⟶ G).left (Over.w _) (1 : TA V W ⟶ D.P.A).left
    (fun e Z r xe h => one_pG U (T := TA V W) e Z r xe h) hjo hjM
  obtain ⟨ν, hν⟩ := exists_gen_of_local (V := W) U.P.L.L U.P.L.isLB (K := Fin 2) ![x.left, (1 : TA V W ⟶ G).left] ![-1, 1]
  have ht : ⊤ ≤ LB.wchart U.P.L.L (K := Fin 2) ![x.left, (1 : TA V W ⟶ G).left] ![jx, jo] := fun y _ =>
    Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [hjx trivial, hjo trivial]
  obtain ⟨n, hn⟩ : ∃ n : Γ(Sp W, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp W) (z : Z) (JG), Good U.P.L.L z JG →
      val ν r z JG = (gm (r ≫ x.left) z _ (U.P.L.L.g (JG (r ≫ x.left)) jx))⁻¹ *
        gm (r ≫ (1 : TA V W ⟶ G).left) z _ (U.P.L.L.g (JG (r ≫ (1 : TA V W ⟶ G).left)) jo) * gm r z ⊤ n := by
    refine ⟨res (X := Sp W) ht (ν.s ![jx, jo]), fun Z r z JG hG => ?_⟩
    refine (gen_trans hν r z (hG.mem _ r) (ht trivial)).trans (congrArg₂ (· * ·) ?_ (gm_res r z ht trivial _).symm)
    rw [trF, Fin.prod_univ_two]
    exact congrArg₂ (· * ·) (zpow_neg_one _) (zpow_one _)
  refine ⟨UU.scaleGen (β * α⁻¹ * n⁻¹ : Γ(Sp W, ⊤)ˣ) ν, UU.scaleGen_isGen _ hν,
    fun e Z (r : Z ⟶ Sp W) xe oe h₁ h₂ z JG J hG hJ => ?_⟩
  have q₁ := (hx e Z r xe h₁).1
  have q₂ := one_pG U (T := TA V W) e Z r oe h₂
  have m : ∀ {X : Scheme.{0}} {f : Sp W ⟶ X} {O : X.Opens}, ⊤ ≤ f ⁻¹ᵁ O → (r ≫ f) z ∈ O := fun h => h trivial
  have a₁ := eq_inv_of_mul_eq_one_right (hα e Z r xe h₁ z)
  have a₂ := eq_inv_of_mul_eq_one_right (hβ e Z r oe h₂ z)
  have w₁ : U.wv e xe z JG J = _ := (congrArg₂ (fun j k => gw (U.w e) xe z (J j) (fun _ => JG k)) q₁ h₁).trans
    (gw_change U e xe z h₁ q₁ (hJ _) (m hjM) (hG _) (m hjx))
  have w₂ : U.wv e oe z JG J = _ := (congrArg₂ (fun j k => gw (U.w e) oe z (J j) (fun _ => JG k)) q₂ h₂).trans
    (gw_change U e oe z h₂ q₂ (hJ _) (m hjM) (hG _) (m hjo))
  rw [a₁] at w₁
  rw [a₂] at w₂
  have v := val_scaleGen (β * α⁻¹ * n⁻¹) ν r hG
  rw [hn Z r z JG hG, map_mul, map_mul, map_inv, map_inv] at v
  refine (congrArg₂ (· * ·) v w₂).trans (Eq.trans ?_ w₁.symm)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.NormGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPsiThetaExpansionPsiRelation
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.PsiExists

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem cT_zero (T : Over (Spec (CommRingCat.of R))) : cT D T 0 = 1 := by
  have h := DVR.cPoint_add D T 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem comp_famφT {T T₀ : Over (Spec (CommRingCat.of R))} (r : T ⟶ T₀ ⊗ D.P.A) (α : D.X) (k : Fin 4) :
    r.left ≫ famφT D T₀ α k = ![(r ≫ snd T₀ D.P.A).left, ((r ≫ snd T₀ D.P.A) * cT D T α).left, (cT D T α).left,
      (1 : T ⟶ D.P.A).left] k := by
  have c : r ≫ cT D _ α = cT D T α := by rw [← Category.assoc, comp_toUnit]
  fin_cases k
  · rfl
  · exact congrArg (fun q => q.left) ((MonObj.comp_mul r (snd T₀ D.P.A) (cT D _ α)).trans (congrArg _ c))
  · exact congrArg (fun q => q.left) c
  · exact congrArg (fun q => q.left) (MonObj.comp_one (M := D.P.A) r)

theorem famφT_eq (T₀ : Over (Spec (CommRingCat.of R))) (α : D.X) :
    famφT D T₀ α = ![(snd T₀ D.P.A).left, (snd T₀ D.P.A * cT D _ α).left, (cT D _ α).left,
      (1 : T₀ ⊗ D.P.A ⟶ D.P.A).left] := rfl

theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem exists_pullB {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (k : ℕ) (f : ∀ α, SecBT D T k α) :
    ∃ s : Raw D F k, PullB D F φ k f s := by
  have H : ∀ α, FormEq (Sum.elim (fun i => (φ ▷ D.P.A).left ≫ famφT D T α i)
      (fun e : PEmpty => (e.elim : (DegPre.BF D F).left ⟶ D.P.A.left))) (Sum.elim (DegPre.famε k) fun e => e.elim)
      (DegPre.famφ D F α) (DegPre.famε k) := by
    intro α U _ h
    have e : (fun i => (φ ▷ D.P.A).left ≫ famφT D T α i) = DegPre.famφ D F α := by
      funext i
      rw [comp_famφT, whiskerRight_snd]; rfl
    rw [e, Fintype.prod_sum_type]
    simp
  choose s hs using fun α => exists_sec D.P.isLB (H α)
    (pullMulSec (f α) (φ ▷ D.P.A).left (LB.oneGen D.P.L) (oneGen_isGen _))
  refine ⟨s, fun α z J hJ => ?_⟩
  refine (hs α _ _ z J hJ).trans ((sval_pullMulSec _ _ _ _ _ _ hJ).trans ?_)
  rw [val_one, Units.val_one, _root_.mul_one, Category.id_comp]

theorem isIso_trF (χ : D.X) : IsIso (DegPre.trF D F χ) := by
  have key : ∀ a b : D.X, a + b = 0 → DegPre.trF D F a ≫ DegPre.trF D F b = 𝟙 _ := by
    intro a b hab
    have c : DegPre.trF D F a ≫ cT D _ b = cT D _ b := by rw [← Category.assoc, comp_toUnit]
    have e : DegPre.trF D F a ≫ (snd (TF (R := R) F) D.P.A * cT D _ b) = snd _ _ := by
      rw [MonObj.comp_mul, c, show DegPre.trF D F a ≫ snd _ _ = snd (TF (R := R) F) D.P.A * cT D _ a from lift_snd _ _,
        _root_.mul_assoc]
      have := (DVR.cPoint_add D (DegPre.BF D F) a b).symm
      rw [hab] at this
      rw [show cT D (DegPre.BF D F) a * cT D _ b = 1 from this.trans (cT_zero D _), _root_.mul_one]
    have e' : DegPre.trF D F a ≫ fst _ _ = fst _ _ := lift_fst _ _
    exact (comp_lift _ _ _).trans ((congrArg₂ lift e' e).trans lift_fst_snd)
  exact ⟨DegPre.trF D F (-χ), key _ _ (add_neg_cancel χ), key _ _ (neg_add_cancel χ)⟩

theorem exists_translate (χ : D.X) (s₀ : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F 0) (DegPre.famε 1))) :
    ∃ h : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F χ) (DegPre.famε 1)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
        sval h r z J = sval s₀ (r ≫ (DegPre.trF D F χ).left) z J *
          (val (D.psi χ) (r ≫ (fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) z J *
            val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
              (r ≫ (DegPre.BF D F).hom) z J).val := by
  let κ : DegPre.BF D F ⟶ TK R := Over.homMk ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F)
    ((Category.assoc _ _ _).trans (Over.w (fst (TF (R := R) F) D.P.A)))
  have H : FormEq (Sum.elim (fun i => (DegPre.trF D F χ).left ≫ DegPre.famφ D F 0 i)
      (Sum.elim (fun _ : PUnit => κ.left ≫ ptK (D.c χ)) (fun _ : PUnit => (DegPre.BF D F).hom ≫ eSec D.P.A)))
      (Sum.elim (DegPre.famε 1) (Sum.elim (fun _ => -1) (fun _ => 1))) (DegPre.famφ D F χ) (DegPre.famε 1) := by
    intro U _ h
    have e₁ : (fun i => (DegPre.trF D F χ).left ≫ DegPre.famφ D F 0 i) =
        ![(snd (TF (R := R) F) D.P.A * cT D _ χ).left, (snd (TF (R := R) F) D.P.A * cT D _ χ).left,
          (1 : DegPre.BF D F ⟶ D.P.A).left, (1 : DegPre.BF D F ⟶ D.P.A).left] := by
      funext i
      refine (comp_famφT D (DegPre.trF D F χ) 0 i).trans ?_
      rw [cT_zero, _root_.mul_one,
        show DegPre.trF D F χ ≫ snd _ _ = snd (TF (R := R) F) D.P.A * cT D _ χ from lift_snd _ _]
    have e₂ : κ.left ≫ ptK (D.c χ) = (cT D (DegPre.BF D F) χ).left :=
      congrArg (fun q => q.left) (show κ ≫ cT D _ χ = cT D _ χ by rw [← Category.assoc, comp_toUnit])
    have e₃ : (DegPre.BF D F).hom ≫ eSec D.P.A = (1 : DegPre.BF D F ⟶ D.P.A).left := rfl
    rw [e₁, e₂, e₃, show DegPre.famφ D F χ = _ from famφT_eq D (TF (R := R) F) χ, Fintype.prod_sum_type,
      Fintype.prod_sum_type]
    simp [Fin.prod_univ_four, DegPre.famε, _root_.mul_assoc]
  obtain ⟨h, hh⟩ := exists_sec D.P.isLB H (pullMulSec s₀ (DegPre.trF D F χ).left
    (LB.mulGen D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (D.psi χ) κ.left)
      (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig (DegPre.BF D F).hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ (D.psi_gen χ) _) (DVR.pullGen_isGen _ _ _ _ D.rig_gen _)))
  refine ⟨h, fun Z r z J hJ => (hh Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ _ _ hJ).trans ?_)⟩
  exact congrArg (fun u : (Z.presheaf.stalk z)ˣ => sval s₀ (r ≫ (DegPre.trF D F χ).left) z J * u.val)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _) (val_pull hJ _ _ _)))

def constVal {F : Type} [Field F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) : F →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp ((p.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)

theorem constVal_eq {F : Type} [Field F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (c : F) :
    constVal p z c = gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) := (gs_eq p z ⊤ trivial _).symm

theorem exists_ratio (h₁ : Laws) (h₂ : Laws2) (χ : D.X)
    (s t : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F χ) (DegPre.famε 1))) (hs : ∃ j, s.f j ≠ 0) (ht : ∃ j, t.f j ≠ 0) :
    ∃ a : Fˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
      sval s r z J = constVal (r ≫ (fst (TF (R := R) F) D.P.A).left) z a.val * sval t r z J := by
  obtain ⟨b, hb⟩ := exists_basis_twist_field h₁ h₂ R D F 1 le_rfl χ
  have : Subsingleton (Fin (1 ^ D.P.g)) := by rw [one_pow]; infer_instance
  let i₀ : Fin (1 ^ D.P.g) := ⟨0, by simp⟩
  have key : ∀ s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F χ) (DegPre.famε 1)), (∃ j, s.f j ≠ 0) →
      ∃ c : F, c ≠ 0 ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J), Good D.P.L z J →
        sval s r z J = constVal (r ≫ (fst (TF (R := R) F) D.P.A).left) z c * sval (b i₀) r z J := by
    rintro s ⟨j, hj⟩
    obtain ⟨c, hc, -⟩ := hb s
    have hc' : ∀ j, s.f j = DegPre.constBF D F (c i₀) _ * (b i₀).f j := fun j =>
      (hc j).trans (Fintype.sum_subsingleton _ i₀)
    refine ⟨c i₀, fun h0 => hj ?_, fun Z r z J hJ => ?_⟩
    · rw [hc', h0, DegPre.constBF, map_zero, map_zero, map_zero, zero_mul]
    · rw [constVal_eq]
      exact (congrArg (gs r z _) (hc' _)).trans ((gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg₂ (· * ·)
        ((gs_res r z le_top (hJ.mem _ r) _).trans (gs_pull r (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _)) rfl))
  obtain ⟨c, hc0, hc⟩ := key s hs
  obtain ⟨d, hd0, hd⟩ := key t ht
  refine ⟨Units.mk0 (c / d) (div_ne_zero hc0 hd0), fun Z r z J hJ => ?_⟩
  rw [hc Z r z J hJ, hd Z r z J hJ, ← _root_.mul_assoc, ← map_mul, Units.val_mk0, div_mul_cancel₀ c hd0]

theorem exists_psi_of_section (h₁ : Laws) (h₂ : Laws2) (i : (TK R).left ⟶ Spec (CommRingCat.of F))
    (hi : i ≫ jFK (R := R) F = 𝟙 _) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (hf : ∀ α, ∃ j, (f α).f j ≠ 0) :
    ∃ ψ : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => ptK (D.c χ)) (fun _ => -1)),
      (∀ χ, (ψ χ).IsGen) ∧ ∀ (χ : D.X) (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ 𝟙_ _) (κ : T ⟶ TK R)
        (y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → sval (f χ) (lift ρ y).left z J =
          (val (ψ χ) κ.left z J * rigV D z J).val * sval (f 0) (lift ρ (y * cT D T χ)).left z J := by
  obtain ⟨s, hs⟩ := exists_pullB D F (toUnit _) 1 f
  have hs0 := fun α => (pullB_ne_zero_iff R D F 1 f s hs α).2 (hf α)
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have : IsIntegral (DegPre.BF D F).left := isIntegral_tensor_left_of_smooth_grpObj _ D.P.A (TF (R := R) F)
  choose h hh using fun χ => exists_translate D F χ (s 0)
  have hh0 : ∀ χ, ∃ j, (h χ).f j ≠ 0 := fun χ => by
    obtain ⟨J, hJ⟩ := exists_good_pt (Z := (DegPre.BF D F).left) D.P.isLB (genericPoint _)
    have := isIso_trF D F χ
    have : IsIso (DegPre.trF D F χ).left := inferInstanceAs (IsIso ((Over.forget _).map (DegPre.trF D F χ)))
    rw [exists_ne_zero_iff_sval_ne_zero _ hJ, hh χ _ _ _ J hJ, Category.id_comp]
    exact mul_ne_zero (sval_ne_zero_of_isIso _ _ D.P.L D.P.isLB _ _ _ (s 0) (hs0 0) _ _ _ J hJ) (Units.ne_zero _)
  choose a ha using fun χ => exists_ratio D F h₁ h₂ χ (s χ) (h χ) (hs0 χ) (hh0 χ)
  let u : D.X → Γ((TK R).left, ⊤)ˣ := fun χ => Units.map (i.app ⊤).hom.toMonoidHom (unitOn (a χ))
  refine ⟨fun χ => GlobalTheory.UU.scaleGen (u χ) (D.psi χ), fun χ => GlobalTheory.UU.scaleGen_isGen _ (D.psi_gen χ), ?_⟩
  intro χ T ρ κ y z J hJ
  have hκ : (κ.left ≫ i) ≫ jFK (R := R) F = κ.left := by rw [Category.assoc, hi, Category.comp_id]
  let κ' : T ⟶ TF (R := R) F := Over.homMk (κ.left ≫ i)
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jK R) hκ).trans (Over.w κ)))
  have hρ : κ' ≫ toUnit _ = ρ := toUnit_unique _ _
  have v₁ := pullB_values R D _ _ _ 1 f s hs χ T κ' y z J hJ
  have v₂ := pullB_values R D _ _ _ 1 f s hs 0 T κ' (y * cT D T χ) z J hJ
  rw [hρ] at v₁ v₂
  have a₁ : (lift κ' y).left ≫ (fst (TF (R := R) F) D.P.A).left = κ.left ≫ i :=
    congrArg (fun q => q.left) (lift_fst κ' y)
  have a₂ : (lift κ' y).left ≫ (DegPre.trF D F χ).left = (lift κ' (y * cT D T χ)).left := by
    refine congrArg (fun q => q.left) (?_ : lift κ' y ≫ DegPre.trF D F χ = _)
    refine (comp_lift _ _ _).trans (congrArg₂ lift (lift_fst _ _) ?_)
    refine (MonObj.comp_mul (lift κ' y) (snd _ D.P.A) (cT D _ χ)).trans ?_
    rw [lift_snd, ← Category.assoc, comp_toUnit]
  have a₃ : (lift κ' y).left ≫ (DegPre.BF D F).hom = T.hom := Over.w _
  have a₄ : (lift κ' y).left ≫ (fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F = κ.left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jFK (R := R) F) a₁).trans hκ)
  have w₁ := ha χ _ (lift κ' y).left z J hJ
  have w₂ := hh χ _ (lift κ' y).left z J hJ
  rw [a₂, a₃, a₄] at w₂
  rw [a₁] at w₁
  have w₃ := GlobalTheory.UU.val_scaleGen (u χ) (D.psi χ) κ.left hJ
  have w₄ : (gm κ.left z ⊤ (u χ)).val = constVal (κ.left ≫ i) z (a χ).val :=
    (gs_unit κ.left z ⊤ trivial _).symm.trans ((gs_pull κ.left i z ⊤ trivial _).trans (constVal_eq _ _ _).symm)
  have alg : ∀ (A : Type) [CommRing A] (x₁ x₂ s₁ s₂ t c : A) (p q u v : Aˣ), s₁ = x₁ → s₂ = x₂ → s₁ = c * t →
      t = s₂ * (p * q).val → v = u * p → u.val = c → x₁ = (v * q).val * x₂ := by
    intro A _ x₁ x₂ s₁ s₂ t c p q u v e₁ e₂ e₃ e₄ e₅ e₆
    rw [← e₁, ← e₂, e₃, e₄, e₅, ← e₆]
    simp only [Units.val_mul]
    ring
  exact alg _ _ _ _ _ _ _ _ _ _ _ v₁ v₂ w₁ w₂ w₃ w₄

end GlobalTheory.PsiExists

namespace GlobalTheory

theorem exists_psi_psiRel : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (f : ∀ α, SecBT D (𝟙_ _) 1 α), (∀ α, ∃ j, (f α).f j ≠ 0) → ∃ ψ h, PsiRel (setPsi D ψ h) (𝟙_ _) f := by
  intro h₁ h₂ R _ _ D f hf
  obtain ⟨ψ, h, H⟩ := PsiExists.exists_psi_of_section D (FractionRing R) h₁ h₂ (𝟙 _)
    ((Category.id_comp _).trans (Spec.map_id _)) f hf
  exact ⟨ψ, h, H⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyTrivialTorusQuotientFlatSurjectiveCosetsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.locallyTrivial_torusQuotient_flat_surjective_cosets : (∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (G B : Over S) [GrpObj G] (i : splitTorus S X ⟶ G) (q : G ⟶ B), IsMonHom i → IsAffineHom q.left → (∀ b : B.left, ∃ V : B.left.Opens, b ∈ V ∧ IsAffineOpen V ∧ (∀ a : Γ(G.left, q.left ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.left.app V).hom c = a) ∧ Function.Injective (q.left.app V).hom ∧ (snd (splitTorus _ X) G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ∧ ∃ u : Multiplicative X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ, ∀ χ, IsWt i _ (u (Multiplicative.ofAdd χ)).val χ) → Mono i ∧ Flat q.left ∧ Surjective q.left ∧ (Smooth G.hom → Smooth B.hom) ∧ ∀ (Z : Over S) (g g' : Z ⟶ G), g ≫ q = g' ≫ q ↔ ∃ t : Z ⟶ splitTorus S X, g' = (t ≫ i) * g) := by
  first | exact @GlobalTheory.LocTriv.main | exact GlobalTheory.LocTriv.main | (intros; apply GlobalTheory.LocTriv.main <;> assumption)
end

