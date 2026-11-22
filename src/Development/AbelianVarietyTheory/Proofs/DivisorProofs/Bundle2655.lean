import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2351
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2556
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2453
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0644
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0038
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0037
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1528
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2404
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchingSquareGlueLineBundleOfLocalGenerators
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PinchLift

theorem ratio_tele {G : Type*} [CommGroup G] (a b c : G) : a * b⁻¹ * (c * a⁻¹) = c * b⁻¹ := by
  rw [mul_comm c, ← _root_.mul_assoc, mul_comm a b⁻¹, mul_inv_cancel_right, mul_comm]

theorem ratio_cancel_left {G : Type*} [CommGroup G] (w a b : G) : a * b⁻¹ = w * a * (w * b)⁻¹ := by
  rw [mul_inv, ← _root_.mul_assoc, mul_comm w a, mul_inv_cancel_right]

theorem assemble : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → GlobalTheory.PinchLift.Glues p i i' p' → ∀ (L' : LB X') (LZ : LB Z) (hL' : L'.IsLB) (hLZ : LZ.IsLB) (w : LB.Iso (L'.pull i') (LZ.pull p')), w.IsGen → (∀ x : X, ∃ (W : X.Opens) (s' : ∀ k, Γ(X', L'.U k ⊓ p ⁻¹ᵁ W)ˣ) (sZ : ∀ j, Γ(Z, LZ.U j ⊓ i ⁻¹ᵁ W)ˣ), x ∈ W ∧ GlobalTheory.PinchLift.GenOn L' (p ⁻¹ᵁ W) s' ∧ GlobalTheory.PinchLift.GenOn LZ (i ⁻¹ᵁ W) sZ ∧ GlobalTheory.PinchLift.Matched i' p' L' LZ w (p ⁻¹ᵁ W) (i ⁻¹ᵁ W) s' sZ) → ∃ e : Pic X, GlobalTheory.CechPic.pull p e = cls L' hL' ∧ GlobalTheory.CechPic.pull i e = cls LZ hLZ := by
  intro X X' Z Z' p i i' p' hsq hG L' LZ hL' hLZ w _ hloc
  have hc : i' ≫ p = p' ≫ i := hsq.w
  have hpt : ∀ z : Z', i (p' z) = p (i' z) := fun z => (congrArg (fun q => q z) hc).symm
  choose W s' sZ hxW hs' hsZ hM using hloc
  have r'e := fun x y => GlobalTheory.T.exists_ratio_unit_of_lineBundle_generators_on_opens _ L' hL' _ _ (s' y) (s' x) (hs' y) (hs' x)
  choose r' hr' using r'e
  have rZe := fun x y => GlobalTheory.T.exists_ratio_unit_of_lineBundle_generators_on_opens _ LZ hLZ _ _ (sZ y) (sZ x) (hsZ y) (hsZ x)
  choose rZ hrZ using rZe
  have le' : ∀ x y : X, p ⁻¹ᵁ (W x ⊓ W y) ≤ p ⁻¹ᵁ W y ⊓ p ⁻¹ᵁ W x := fun x y _ h => ⟨h.2, h.1⟩
  have leZ : ∀ x y : X, i ⁻¹ᵁ (W x ⊓ W y) ≤ i ⁻¹ᵁ W y ⊓ i ⁻¹ᵁ W x := fun x y _ h => ⟨h.2, h.1⟩
  have ge := fun x y => GlobalTheory.T.exists_unit_of_pinchingSquare_glued_units _ _ _ _ p i i' p' hc hG (W x ⊓ W y) (res (le' x y) (r' x y)) (res (leZ x y) (rZ x y)) (by
    intro z hz
    have hz' : i (p' z) ∈ W x ⊓ W y := (hpt z).symm ▸ hz
    obtain ⟨k, hk⟩ := exists_chart hL' (i' z)
    obtain ⟨j, hj⟩ := exists_chart hLZ (p' z)
    rw [gm_res _ z _ hz, gm_res _ z _ hz', hr' x y Z' i' z k hk hz.2 hz.1, hrZ x y Z' p' z j hj hz'.2 hz'.1,
      hM y z j k hj hk hz'.2 hz.2, hM x z j k hj hk hz'.1 hz.1]
    exact ratio_cancel_left _ _ _)
  choose g hgp hgi using ge
  have Gp : ∀ x y (t : X') (k : L'.ι), p t ∈ W x → p t ∈ W y → t ∈ L'.U k →
      gm p t (W x ⊓ W y) (g x y) = gm (𝟙 X') t (L'.U k ⊓ p ⁻¹ᵁ W y) (s' y k) * (gm (𝟙 X') t (L'.U k ⊓ p ⁻¹ᵁ W x) (s' x k))⁻¹ := by
    intro x y t k hx hy hk
    rw [hgp x y t ⟨hx, hy⟩, gm_res _ t _ (show t ∈ p ⁻¹ᵁ (W x ⊓ W y) from ⟨hx, hy⟩), hr' x y X' (𝟙 X') t k hk hy hx]
  have Gi : ∀ x y (t : Z) (k : LZ.ι), i t ∈ W x → i t ∈ W y → t ∈ LZ.U k →
      gm i t (W x ⊓ W y) (g x y) = gm (𝟙 Z) t (LZ.U k ⊓ i ⁻¹ᵁ W y) (sZ y k) * (gm (𝟙 Z) t (LZ.U k ⊓ i ⁻¹ᵁ W x) (sZ x k))⁻¹ := by
    intro x y t k hx hy hk
    rw [hgi x y t ⟨hx, hy⟩, gm_res _ t _ (show t ∈ i ⁻¹ᵁ (W x ⊓ W y) from ⟨hx, hy⟩), hrZ x y Z (𝟙 Z) t k hk hy hx]
  let E : LB X := ⟨X, W, g⟩
  have hE : E.IsLB := by
    refine ⟨eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩, fun x => ?_, fun x y z => ?_⟩
    · refine GlobalTheory.T.unit_eq_of_germs_pinching_square _ _ _ _ p i i' p' hc hG _ _ _ (fun t ht => ?_) (fun t ht => ?_)
      · obtain ⟨k, hk⟩ := exists_chart hL' t
        rw [map_one, gm_res _ t _ ht]
        exact (Gp x x t k ht ht hk).trans (mul_inv_cancel _)
      · obtain ⟨k, hk⟩ := exists_chart hLZ t
        rw [map_one, gm_res _ t _ ht]
        exact (Gi x x t k ht ht hk).trans (mul_inv_cancel _)
    · refine GlobalTheory.T.unit_eq_of_germs_pinching_square _ _ _ _ p i i' p' hc hG _ _ _ (fun t ht => ?_) (fun t ht => ?_)
      · obtain ⟨k, hk⟩ := exists_chart hL' t
        rw [map_mul, gm_res _ t _ ht, gm_res _ t _ ht, gm_res _ t _ ht]
        show gm p t (W x ⊓ W y) (g x y) * gm p t (W y ⊓ W z) (g y z) = gm p t (W x ⊓ W z) (g x z)
        rw [Gp x y t k ht.1.1 ht.1.2 hk, Gp y z t k ht.1.2 ht.2 hk, Gp x z t k ht.1.1 ht.2 hk]
        exact ratio_tele _ _ _
      · obtain ⟨k, hk⟩ := exists_chart hLZ t
        rw [map_mul, gm_res _ t _ ht, gm_res _ t _ ht, gm_res _ t _ ht]
        show gm i t (W x ⊓ W y) (g x y) * gm i t (W y ⊓ W z) (g y z) = gm i t (W x ⊓ W z) (g x z)
        rw [Gi x y t k ht.1.1 ht.1.2 hk, Gi y z t k ht.1.2 ht.2 hk, Gi x z t k ht.1.1 ht.2 hk]
        exact ratio_tele _ _ _
  refine ⟨cls E hE, ?_, ?_⟩
  · rw [← cls_pull hE p (pull_isLB hE p)]
    exact (cls_eq_iff _ _).2 (LBIso.symm (GlobalTheory.T.lineBundle_iso_pullback_of_local_unit_generators _ _ p L' X W g s' hs' Gp))
  · rw [← cls_pull hE i (pull_isLB hE i)]
    exact (cls_eq_iff _ _).2 (LBIso.symm (GlobalTheory.T.lineBundle_iso_pullback_of_local_unit_generators _ _ i LZ X W g sZ hsZ Gi))

end GlobalTheory.PinchLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchingSquareUnitsPatch
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

theorem germ_app_congr {Y X : Scheme.{0}} {f g : Y ⟶ X} (e : f = g) (W : X.Opens) (y : Y) (hf : f y ∈ W)
    (hg : g y ∈ W) (s : Γ(X, W)) :
    Y.presheaf.germ (f ⁻¹ᵁ W) y hf ((f.app W).hom s) = Y.presheaf.germ (g ⁻¹ᵁ W) y hg ((g.app W).hom s) := by
  subst e; rfl

theorem affine_descent_units : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z),
    IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.Pinch.Cond p i →
    ∀ W : X.Opens, IsAffineOpen W → ∀ (u' : Γ(X', p ⁻¹ᵁ W)ˣ) (v : Γ(Z, i ⁻¹ᵁ W)ˣ),
      (∀ z : Z', p (i' z) ∈ W → gm i' z (p ⁻¹ᵁ W) u' = gm p' z (i ⁻¹ᵁ W) v) →
      ∃ u : Γ(X, W)ˣ, pullU p W u = u' := by
  intro X X' Z Z' p i i' p' h hp hi hc W hW u' v huv
  have hw : ∀ z : Z', p (i' z) = i (p' z) := fun z => by
    have := congrArg (fun f : Z' ⟶ X => f z) h.w
    simpa using this
  have claim : ∀ (s' : Γ(X', p ⁻¹ᵁ W)) (t : Γ(Z, i ⁻¹ᵁ W)),
      (∀ z : Z', ∀ hz : p (i' z) ∈ W,
        Z'.presheaf.germ (i' ⁻¹ᵁ (p ⁻¹ᵁ W)) z hz ((i'.app (p ⁻¹ᵁ W)).hom s') =
          Z'.presheaf.germ (p' ⁻¹ᵁ (i ⁻¹ᵁ W)) z (show i (p' z) ∈ W from hw z ▸ hz) ((p'.app (i ⁻¹ᵁ W)).hom t)) →
      ∃ s : Γ(X, W), (p.app W).hom s = s' := by
    intro s' t hst
    obtain ⟨s₀, rfl⟩ := Scheme.Hom.app_surjective i W hW t
    have hd : (i'.app (p ⁻¹ᵁ W)).hom (s' - (p.app W).hom s₀) = 0 := by
      apply TopCat.Presheaf.section_ext Z'.sheaf
      intro z hz
      show (Z'.presheaf.germ (i' ⁻¹ᵁ p ⁻¹ᵁ W) z hz).hom ((i'.app (p ⁻¹ᵁ W)).hom (s' - (p.app W).hom s₀)) =
        (Z'.presheaf.germ (i' ⁻¹ᵁ p ⁻¹ᵁ W) z hz).hom 0
      rw [map_sub, map_sub, map_zero, sub_eq_zero, hst z hz]
      have e1 := germ_app_congr h.w W z hz (show i (p' z) ∈ W from hw z ▸ hz) s₀
      exact e1.symm
    have hmem := GlobalTheory.T.closedImmersion_baseChange_ker_mem_map_affine X X' Z Z' p i i' p' h hp hi W hW _ hd
    have key : ∃ y, (i.app W).hom y = 0 ∧ (p.app W).hom y = s' - (p.app W).hom s₀ := by
      refine Submodule.span_induction (p := fun x _ => ∃ y, (i.app W).hom y = 0 ∧ (p.app W).hom y = x)
        ?_ ?_ ?_ ?_ hmem
      · rintro _ ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · exact ⟨0, map_zero _, map_zero _⟩
      · rintro _ _ _ _ ⟨y₁, h₁, e₁⟩ ⟨y₂, h₂, e₂⟩
        exact ⟨y₁ + y₂, by rw [map_add, h₁, h₂, add_zero], by rw [map_add, e₁, e₂]⟩
      · rintro r _ _ ⟨y, hy, rfl⟩
        obtain ⟨y', hy', e'⟩ := (hc W hW).2 y hy r
        exact ⟨y', hy', by rw [smul_eq_mul, mul_comm]; exact e'⟩
    obtain ⟨y, -, hy⟩ := key
    exact ⟨s₀ + y, by rw [map_add, hy, add_sub_cancel]⟩
  have germs : ∀ (a : Γ(X', p ⁻¹ᵁ W)ˣ) (b : Γ(Z, i ⁻¹ᵁ W)ˣ),
      (∀ z : Z', p (i' z) ∈ W → gm i' z (p ⁻¹ᵁ W) a = gm p' z (i ⁻¹ᵁ W) b) →
      ∃ s : Γ(X, W), (p.app W).hom s = a.val := by
    intro a b hab
    refine claim a.val b.val fun z hz => ?_
    have := congrArg Units.val (hab z hz)
    rwa [gm_val i' z _ hz, gm_val p' z _ (show i (p' z) ∈ W from hw z ▸ hz)] at this
  obtain ⟨x, hx⟩ := germs u' v huv
  obtain ⟨y, hy⟩ := germs u'⁻¹ v⁻¹ fun z hz => by rw [map_inv, map_inv, huv z hz]
  have hxy : x * y = 1 := (hc W hW).1 (by
    show (p.app W).hom (x * y) = (p.app W).hom 1
    rw [map_mul, map_one, hx, hy, Units.mul_inv])
  exact ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, Units.ext hx⟩

theorem pullU_injective {X X' : Scheme.{0}} (p : X' ⟶ X)
    (hp : ∀ W : X.Opens, IsAffineOpen W → Function.Injective (p.app W)) (W : X.Opens) :
    Function.Injective (pullU p W) := by
  intro a b hab
  apply unit_ext
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
  have hle : V ≤ W := hVW
  have e : res hle a = res hle b := by
    apply Units.ext
    apply hp V hV
    have := congrArg Units.val (show pullU p V (res hle a) = pullU p V (res hle b) by
      rw [pullU_res₂, pullU_res₂, hab])
    exact this
  rw [← gm_res (𝟙 X) x hle hxV a, ← gm_res (𝟙 X) x hle hxV b, e]

theorem unitsPatch : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z),
    IsPullback i' p' p i → IsAffineHom p → IsClosedImmersion i → GlobalTheory.Pinch.Cond p i →
    GlobalTheory.Pinch.UnitsPatch p i i' p' := by
  intro X X' Z Z' p i i' p' h hp hi hc W
  have hinj : ∀ V : X.Opens, Function.Injective (pullU p V) :=
    pullU_injective p (fun V hV => (hc V hV).1)
  refine ⟨hinj W, fun u' v huv => ?_⟩
  have hw : ∀ z : Z', p (i' z) = i (p' z) := fun z => by
    have := congrArg (fun f : Z' ⟶ X => f z) h.w
    simpa using this
  let J : Type := {V : X.Opens // IsAffineOpen V ∧ V ≤ W}
  have hsub : ∀ j : J, p ⁻¹ᵁ j.1 ≤ p ⁻¹ᵁ W := fun j x hx => j.2.2 hx
  have hsubZ : ∀ j : J, i ⁻¹ᵁ j.1 ≤ i ⁻¹ᵁ W := fun j x hx => j.2.2 hx
  have loc : ∀ j : J, ∃ a : Γ(X, j.1)ˣ, pullU p j.1 a = res (hsub j) u' := by
    intro j
    refine affine_descent_units X X' Z Z' p i i' p' h hp hi hc j.1 j.2.1 _ (res (hsubZ j) v) ?_
    intro z hz
    rw [gm_res i' z (hsub j) hz, gm_res p' z (hsubZ j) (show i (p' z) ∈ j.1 from hw z ▸ hz)]
    exact huv z (j.2.2 hz)
  choose a ha using loc

  have hD : ∀ j : J, ∀ y : X', ∀ hy : p y ∈ j.1, gm p y j.1 (a j) = gm (𝟙 X') y (p ⁻¹ᵁ W) u' := by
    intro j y hy
    rw [← gm_id_pull p y j.1 hy, ha j, gm_res (𝟙 X') y (hsub j) hy]
  obtain ⟨s, hs⟩ := glue_unit W (fun j : J => j.1) (fun j => j.2.2) (by
      intro x hx
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV, hVW⟩, hxV⟩) a (by
      intro j k x hx
      have hle1 : j.1 ⊓ k.1 ≤ j.1 := inf_le_left
      have hle2 : j.1 ⊓ k.1 ≤ k.1 := inf_le_right
      have e : res hle1 (a j) = res hle2 (a k) := by
        apply hinj
        apply unit_ext
        intro y hy
        rw [gm_id_pull p y _ hy, gm_id_pull p y _ hy, gm_res p y hle1 hy, gm_res p y hle2 hy,
          hD j y (hle1 hy), hD k y (hle2 hy)]
      rw [← gm_res (𝟙 X) x hle1 hx, ← gm_res (𝟙 X) x hle2 hx, e])
  refine ⟨s, unit_ext fun y hy => ?_⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (show p y ∈ W from hy) W.2
  let j : J := ⟨V, hV, hVW⟩
  rw [gm_id_pull p y W hy, ← gm_res p y j.2.2 hxV, hs j]
  exact hD j y hxV

end GlobalTheory.Pinch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceRingFractionEmbedding
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PlaceRingFacts

open IsDedekindDomain

variable {R : Subring ℂ} [IsDiscreteValuationRing R]

theorem valuation_unit_mul_pow {ϖ : R} (hϖ : Irreducible ϖ) (u : Rˣ) (n : ℕ) :
    (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R)
      (algebraMap R (FractionRing R) ((u : R) * ϖ ^ n)) = WithZero.exp (-(n : ℤ)) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, map_mul, map_pow,
    HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero hϖ.maximalIdeal_eq,
    HeightOneSpectrum.intValuation_eq_one_iff.2 ?_]
  · rw [_root_.one_mul, ← WithZero.exp_nsmul]
    congr 1
    simp
  · exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit

theorem ord_unit_mul_pow {ϖ : R} (hϖ : Irreducible ϖ) (u : Rˣ) (n : ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (algebraMap R (FractionRing R) ((u : R) * ϖ ^ n)) = n := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw, valuation_unit_mul_pow hϖ u n, WithZero.log_exp, neg_neg]

theorem ord_div {x y : FractionRing R} (hx : x ≠ 0) (hy : y ≠ 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (x / y) = GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R x - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R y := by
  set v := (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R)
  have hvx : v x ≠ 0 := by simpa [v] using hx
  have hvy : v y ≠ 0 := by simpa [v] using hy
  have ex : v x = WithZero.exp (-GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R x) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw, neg_neg, WithZero.exp_log hvx]
  have ey : v y = WithZero.exp (-GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R y) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw, neg_neg, WithZero.exp_log hvy]
  have : v (x / y) = WithZero.exp (-(GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R x - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R y)) := by
    rw [map_div₀, ex, ey, ← WithZero.exp_sub]
    congr 1
    ring
  rw [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw, this, WithZero.log_exp, neg_neg]

end GlobalTheory.PlaceRingFacts

namespace GlobalTheory.PlaceRingFacts

theorem norm_natCast_self (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [← Padic.norm_p (p := l), ← PadicComplex.norm_extends' l (l : ℚ_[l])]
  congr 1
  simp

theorem place_ring_facts : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l])
    (R : Subring ℂ) [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∃ j : FractionRing R →+* ℂ, (∀ x : R, j (algebraMap R (FractionRing R) x) = x) ∧ CharZero R ∧
      (l : R) ∈ IsLocalRing.maximalIdeal R ∧ Nat.card (E →+* FractionRing R) = Module.finrank ℚ E ∧
      (∀ σ : E →+* ℂ, ∃ τ : E →+* FractionRing R, j.comp τ = σ) ∧
      ∀ (x : FractionRing R) (r : ℚ), ((-r : ℚ) : WithTop ℚ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l x → Sz l lam (r : ℝ) (j x) := by
  intro E _ _ l _ lam R _ hR
  obtain ⟨-, hSz, -, hfr⟩ := hR
  have hlp : (l : ℕ).Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hA : ∀ x : R, (x : ℂ) ∈ algebraicClosure ℚ ℂ := fun x => (hSz x x.2).1
  let i0 : R →+* algebraicClosure ℚ ℂ := R.subtype.codRestrict (algebraicClosure ℚ ℂ) hA
  have hi0 : Function.Injective i0 := fun a b h => Subtype.ext (show (a : ℂ) = b from congrArg (fun z : algebraicClosure ℚ ℂ => (z : ℂ)) h)
  let jA : FractionRing R →+* algebraicClosure ℚ ℂ := IsFractionRing.lift hi0
  have hjA : ∀ x : R, jA (algebraMap R (FractionRing R) x) = i0 x := fun x => IsFractionRing.lift_algebraMap hi0 x
  let j : FractionRing R →+* ℂ := (IntermediateField.val (algebraicClosure ℚ ℂ)).toRingHom.comp jA
  have hj : ∀ x : R, j (algebraMap R (FractionRing R) x) = x := fun x => by
    show ((jA (algebraMap R (FractionRing R) x) : algebraicClosure ℚ ℂ) : ℂ) = x
    rw [hjA]
    rfl
  let g : FractionRing R →+* ℂ_[l] := lam.comp jA
  have hN1 : ∀ a : R, ‖g (algebraMap R (FractionRing R) a)‖ ≤ 1 := fun a => by
    obtain ⟨h, hh⟩ := hSz a a.2
    have e : g (algebraMap R (FractionRing R) a) = lam ⟨(a : ℂ), h⟩ := by
      simp only [g, RingHom.comp_apply, hjA]
      rfl
    rw [e]
    simpa using hh
  have hunit : ∀ u : Rˣ, ‖g (algebraMap R (FractionRing R) u)‖ = 1 := fun u => by
    have hprod : ‖g (algebraMap R (FractionRing R) u)‖ * ‖g (algebraMap R (FractionRing R) (u⁻¹ : Rˣ))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    have h1 := hN1 u
    have h2 := hN1 (u⁻¹ : Rˣ)
    have h0 := norm_nonneg (g (algebraMap R (FractionRing R) u))
    refine le_antisymm h1 ?_
    calc (1 : ℝ) = _ := hprod.symm
      _ ≤ ‖g (algebraMap R (FractionRing R) u)‖ * 1 := mul_le_mul_of_nonneg_left h2 h0
      _ = _ := mul_one _
  have hgl : ‖g (algebraMap R (FractionRing R) (l : R))‖ = (l : ℝ)⁻¹ := by
    rw [map_natCast, map_natCast]
    exact norm_natCast_self l
  have hlinv : (l : ℝ)⁻¹ ≠ 1 := by
    intro h
    rw [inv_eq_one] at h
    linarith
  have hmax : (l : R) ∈ IsLocalRing.maximalIdeal R := by
    refine (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 fun hu => ?_)
    obtain ⟨u, hu⟩ := hu
    have := hunit u
    rw [hu, hgl] at this
    exact hlinv this
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  set c := ‖g (algebraMap R (FractionRing R) ϖ)‖ with hc
  have hpowR : ∀ a : R, a ≠ 0 → ∃ n : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (algebraMap R (FractionRing R) a) = n ∧
      ‖g (algebraMap R (FractionRing R) a)‖ = c ^ n := fun a ha => by
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    refine ⟨n, ord_unit_mul_pow hϖ u n, ?_⟩
    rw [map_mul, map_mul, norm_mul, hunit, _root_.one_mul, map_pow, map_pow, norm_pow]
  have hlR : (l : R) ≠ 0 := Nat.cast_ne_zero.2 hlp.ne_zero
  obtain ⟨k, hk1, hk2⟩ := hpowR _ hlR
  rw [hgl] at hk2
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hlinv (by simpa using hk2)
  have hc0 : 0 ≤ c := norm_nonneg _
  have hcl : c = (l : ℝ) ^ (-(1 / (k : ℝ))) := by
    have hl0 : (0 : ℝ) ≤ l := by positivity
    refine (pow_left_inj₀ hc0 (Real.rpow_nonneg hl0 _) hk0).1 ?_
    rw [← hk2, ← Real.rpow_natCast, ← Real.rpow_mul hl0]
    have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk0
    rw [show -(1 / (k : ℝ)) * k = -1 by field_simp, Real.rpow_neg_one]
  have hcne : c ≠ 0 := by
    rw [hcl]
    exact (Real.rpow_pos_of_pos (by positivity) _).ne'
  have hgen : ∀ x : FractionRing R, x ≠ 0 →
      ‖g x‖ = c ^ (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R x) := fun x hx => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : algebraMap R (FractionRing R) b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hb0
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at hx
    have haK : algebraMap R (FractionRing R) a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 ha0
    obtain ⟨na, hna1, hna2⟩ := hpowR a ha0
    obtain ⟨nb, hnb1, hnb2⟩ := hpowR b hb0
    rw [ord_div haK hbK, hna1, hnb1, map_div₀, norm_div, hna2, hnb2, zpow_sub₀ hcne, zpow_natCast, zpow_natCast]

  have hrange : ∀ σ : E →+* ℂ, ∀ x, σ x ∈ j.fieldRange := fun σ x => by
    obtain ⟨a, ha, b, hb, hb0, h⟩ := hfr σ x
    refine RingHom.mem_fieldRange.2 ⟨algebraMap R (FractionRing R) ⟨a, ha⟩ / algebraMap R (FractionRing R) ⟨b, hb⟩, ?_⟩
    rw [map_div₀, hj, hj]
    exact (div_eq_iff hb0).2 h.symm
  have hsurj : ∀ σ : E →+* ℂ, ∃ τ : E →+* FractionRing R, j.comp τ = σ := fun σ => by
    refine ⟨(j.rangeRestrictFieldEquiv.symm : j.fieldRange →+* FractionRing R).comp
      (σ.codRestrict j.fieldRange (hrange σ)), ?_⟩
    ext x
    simp
  refine ⟨j, hj, inferInstance, hmax, ?_, hsurj, ?_⟩
  · have hbij : Function.Bijective (fun τ : E →+* FractionRing R => j.comp τ) := by
      refine ⟨fun τ₁ τ₂ h => ?_, fun σ => hsurj σ⟩
      ext x
      exact j.injective (congrArg (fun f : E →+* ℂ => f x) h)
    rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, NumberField.Embeddings.card]
  · intro x r hle
    refine ⟨(jA x).2, ?_⟩
    show ‖g x‖ ≤ (l : ℝ) ^ (r : ℝ)
    by_cases hx : x = 0
    · rw [hx, map_zero, norm_zero]
      positivity
    rw [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp, if_neg hx, WithTop.coe_le_coe] at hle
    have hlK : ((l : ℕ) : FractionRing R) = algebraMap R (FractionRing R) (l : R) := (map_natCast _ _).symm
    rw [hlK, hk1] at hle
    have hle' : -(r : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R x : ℝ) / (k : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).2 hle
      push_cast at this
      exact this
    rw [hgen x hx, hcl, ← Real.rpow_intCast, ← Real.rpow_mul (by positivity)]
    refine Real.rpow_le_rpow_of_exponent_le hl1.le ?_
    have : -(1 / (k : ℝ)) * (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R x : ℝ) = -((GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R x : ℝ) / (k : ℝ)) := by ring
    rw [this]
    linarith

end GlobalTheory.PlaceRingFacts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlurisubharmonicDecreasingLimitExtensionStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plurisubharmonic_decreasing_limit_extension : ∀ {n : ℕ} {U : Set (V n)}, IsOpen U → ∀ (e : V n → ℝ), ContDiffOn ℝ ∞ e U → (∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (e w : ℂ)) y ξ).re) → (∀ a : ℝ, IsCompact {y | y ∈ U ∧ e y ≤ a}) → ∀ (φ : ℕ → V n → ℝ), (∀ k, ContDiffOn ℝ ∞ (φ k) U) → (∀ k, ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (φ k w : ℂ)) y ξ).re) → (∀ k, ∀ y ∈ U, φ (k + 1) y ≤ φ k y) → ∀ (F0 : V n → ℂ), ContDiffOn ℝ ∞ F0 U → ∀ (h : V n → ℝ≥0∞), Measurable h → (∀ k, ∀ y ∈ U, ∀ ξ : Fin n → ℂ, ENNReal.ofReal (‖∑ j, wdb n j F0 y * (starRingEnd ℂ) (ξ j)‖ ^ 2) ≤ h y * ENNReal.ofReal (leviV n (fun w => (φ k w : ℂ)) y ξ).re) → ∀ A : ℝ≥0∞, (∀ k, ∫⁻ y in U, h y * ENNReal.ofReal (Real.exp (-φ k y)) ≤ A) → ∃ F : V n → ℂ, DifferentiableOn ℂ F U ∧ ∫⁻ y in U, ENNReal.ofReal (‖F0 y - F y‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k y)) ≤ A := by
  first | exact @GlobalTheory.HormanderLimit.hormander_limit | exact GlobalTheory.HormanderLimit.hormander_limit | (intros; apply GlobalTheory.HormanderLimit.hormander_limit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareBundleIsomorphismCompat
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerShift

open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw

theorem evc_congr {S : Scheme.{0}} {A T Y : Over S} {M N : LB (A ⊗ T).left} (hM : M.IsLB) (hN : N.IsLB)
    (e : LBIso M N) (a : Y ⟶ A) (t : Y ⟶ T) : evc hM a t = evc hN a t := by
  unfold evc
  rw [(cls_eq_iff hM hN).2 e]

theorem ker_shift : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (S : Scheme.{0}) (A : Over S) [GrpObj A]
    (rm : OAct (𝓞 F) A) (P : 𝔠.elt → LB (A ⊗ A).left), (∀ c, (P c).IsLB) →
    (∀ c, LBIso (P c) ((P c).pull (lift (snd A A) (fst A A)).left)) →
    (∀ (a : 𝓞 F) c, LBIso (P (a • c)) ((P c).pull (lift (fst A A) (snd A A ≫ rm.act a)).left)) →
    ∀ (c d : 𝔠.elt) (a b : 𝓞 F), a • d = b • c → ∀ (T : Over S) (y : T ⟶ A),
      HasGen ((P c).pull (lift (fst A T) (snd A T ≫ y)).left) →
      HasGen ((P d).pull (lift (fst A T) (snd A T ≫ (y ≫ rm.act a))).left) := by
  intro F _ _ 𝔠 S A _ rm P hP hsymm hsmul c d a b had T y hy
  have sy : ∀ c (Y : Over S) (u v : Y ⟶ A), evc (hP c) u v = evc (hP c) v u := by
    intro c Y u v
    have hs : ((P c).pull (lift (snd A A) (fst A A)).left).IsLB := pull_isLB (hP c) _
    rw [evc_congr (hP c) hs (hsymm c) u v]
    exact (evc_ev (hP c) (snd A A) (fst A A) hs u v).trans (by rw [lift_snd, lift_fst])
  have sm : ∀ (a : 𝓞 F) c (Y : Over S) (u v : Y ⟶ A), evc (hP (a • c)) u v = evc (hP c) u (v ≫ rm.act a) := by
    intro a c Y u v
    have hs : ((P c).pull (lift (fst A A) (snd A A ≫ rm.act a)).left).IsLB := pull_isLB (hP c) _
    rw [evc_congr (hP (a • c)) hs (hsmul a c) u v]
    exact (evc_ev (hP c) (fst A A) (snd A A ≫ rm.act a) hs u v).trans (by rw [lift_fst, lift_snd_assoc])
  have h0 : evc (hP c) (fst A T) (snd A T ≫ y) = 0 := (triv_ev_iff (hP c) _ _).1 hy
  have h1 := congrArg (CechPic.pull (lift (fst A T ≫ rm.act b) (snd A T)).left) h0
  rw [pull_evc, map_zero, lift_fst, lift_snd_assoc] at h1
  have e1 := sm a d (A ⊗ T) (fst A T) (snd A T ≫ y)
  rw [had] at e1
  show Triv _
  rw [triv_ev_iff (hP d), ← Category.assoc, ← e1, sy, sm, sy]
  exact h1

end GlobalTheory.KerShift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolKerAtPullbackOfIsGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.polKerAt_pullback_of_isGrpPullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ : Obj b N s₁) (o : Obj b N s) (m : ObjMap o₁ o t) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (B : Over Y) [GrpObj B] [IsCommMonObj B] (θ : B₁.left ⟶ B.left) (ψ₁' : B₁ ⟶ o₁.A) (ψ' : B ⟶ o.A) (c : ℕ), IsGrpPullback B₁ B t θ → θ ≫ ψ'.left = ψ₁'.left ≫ m.φ → (PolKerAt o ψ' c t ↔ PolKerAt o₁ ψ₁' c (𝟙 T)) := by
  first | exact @UpperTheory.Cb.polKerAt_pullback_of_isGrpPullback | exact UpperTheory.Cb.polKerAt_pullback_of_isGrpPullback
end

