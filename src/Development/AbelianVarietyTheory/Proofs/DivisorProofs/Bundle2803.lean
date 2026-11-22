import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2483
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2723
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2482
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2711
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2712
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSmoothGroupOverNbhd
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2256

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftValuationSubring
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.TorEnd

theorem exists_lift_valuationSubring {F : Type} [Field F] (O : ValuationSubring F) {M : Type} [CommGroup M]
    (τ : M →* Fˣ) {k : ℕ} (hk : k ≠ 0) (hτ : τ ^ k = 1) :
    ∃ σ : M →* Oˣ, σ ^ k = 1 ∧ ∀ x, ((σ x : O) : F) = τ x := by
  have hp : ∀ x, (τ x : F) ^ k = 1 := fun x => by
    rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hτ, MonoidHom.one_apply, Units.val_one]
  have hm : ∀ x, (τ x : F) ∈ O := fun x => by
    rw [← O.valuation_le_one_iff]
    have := congrArg O.valuation (hp x)
    rw [map_pow, map_one] at this
    exact ((pow_eq_one_iff_of_nonneg zero_le hk).1 this).le
  let σ₀ : M →* O :=
    { toFun := fun x => ⟨τ x, hm x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  refine ⟨σ₀.toHomUnits, MonoidHom.ext fun x => Units.ext (Subtype.ext ?_), fun x => rfl⟩
  rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
  exact hp x

theorem chV_comp_torusMap {S : Scheme.{0}} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {Z : Over S}
    (z : Z ⟶ splitTorus S X) (m : Y →+ X) (χ : Y) :
    GlobalTheory.UU.chV (z ≫ GlobalTheory.SplitTorus.torusMap S m) χ = GlobalTheory.UU.chV z (m χ) := by
  refine Units.ext ?_
  rw [GlobalTheory.UU.chV_val, GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, GlobalTheory.SplitTorus.charUnit_val,
    ← GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.val_eq, GlobalTheory.SplitTorus.val_comp_torusMap]

theorem torMatch_of_endChar : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (f : G ⟶ G), IsMonHom f → ∀ m, EndChar U f m → TorMatch U U (RingHom.id R) f.left m := by
  intro R _ _ _ hR G _ _ hG D A U f hf m hm F _ _ i₁ i₂ hi k hk τ τ' q q' x x' hτ' hτ hq hqt hq' hqt' hx hx'
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
  obtain ⟨s, s₁, s₂, s₃, s₄⟩ := GlobalTheory.ToricTorsionUnif.main R hR G hG D A U k (Nat.one_le_iff_ne_zero.2 hk0)
  let a : R →+* F := (@algebraMap (FractionRing R) F _ _ i₁).comp (algebraMap R (FractionRing R))
  have ha₂ : a = (@algebraMap (FractionRing R) F _ _ i₂).comp (algebraMap R (FractionRing R)) :=
    RingHom.ext fun r => hi r
  let ν : Multiplicative D.toPre.X →* Multiplicative D.toPre.X := AddMonoidHom.toMultiplicative m
  have pw : ∀ {B : Type} [CommRing B] (σ : Multiplicative D.toPre.X →* Bˣ), σ ^ k = 1 → σ.comp ν ^ k = 1 :=
    fun σ h => MonoidHom.ext fun χ => DFunLike.congr_fun h (ν χ)
  obtain rfl : τ = τ'.comp ν := MonoidHom.ext fun χ => hτ χ.toAdd
  have e₁ := @s₄ F _ _ i₁ a _ (pw τ' hτ') q x rfl hq hqt hx
  have e₂ := @s₄ F _ _ i₂ a _ hτ' q' x' ha₂ hq' hqt' hx'
  rw [e₁, reassoc_of% e₂]
  obtain ⟨O, hO, hloc⟩ := IsLocalRing.exists_factor_valuationRing a
  let c : R →+* O := a.codRestrict O.toSubring hO
  have hc : IsLocalHom c := hloc
  obtain ⟨σ, hσ, hστ⟩ := exists_lift_valuationSubring O τ' hk0 hτ'
  have n₁ := s₂ O F c a O.subtype _ (pw σ hσ) _ (pw τ' hτ') rfl fun χ => (hστ (ν χ)).symm
  have n₂ := s₂ O F c a O.subtype _ hσ _ hτ' rfl fun χ => (hστ χ).symm
  suffices key : s O c _ (pw σ hσ) = s O c σ hσ ≫ f by
    rw [n₁, n₂, key, Over.comp_left, Category.assoc]
  have hkO : IsUnit (k : O) := by simpa using hk.map c
  refine GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) G hG.smooth O (spMap c) k hkO _ _ ?_
    (ResidueField O) (residue O) inferInstance ?_
  · rw [s₁, ← MonObj.pow_comp, s₁, MonObj.one_comp]
  let a₀ : R →+* ResidueField O := (residue O).comp c
  have ha₀ : ∀ r ∈ maximalIdeal R ^ (0 + 1), a₀ r = 0 := fun r hr => by
    rw [zero_add, pow_one] at hr
    exact (residue_eq_zero_iff _).2 (map_nonunit c r hr)
  let σ₀ : Multiplicative D.toPre.X →* (ResidueField O)ˣ := (Units.map (residue O).toMonoidHom).comp σ
  have hσ₀ : σ₀ ^ k = 1 := MonoidHom.ext fun χ => by
    have := DFunLike.congr_fun hσ χ
    rw [MonoidHom.pow_apply, MonoidHom.one_apply] at this ⊢
    simp only [σ₀, MonoidHom.comp_apply, ← map_pow, this, map_one]
  have r₁ := s₂ O _ c a₀ (residue O) _ (pw σ hσ) _ (pw σ₀ hσ₀) rfl fun χ => rfl
  have r₂ := s₂ O _ c a₀ (residue O) _ hσ _ hσ₀ rfl fun χ => rfl
  have h₀ := isGrpPullback_pullback G (spMap a₀)
  let z : Over.mk (spMap (RingHom.id (ResidueField O))) ⟶ splitTorus (Sp (ResidueField O)) D.toPre.X :=
    (GlobalTheory.splitTorusPointsEquiv _ _ _).symm
      ((Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField O))).inv.hom.toMonoidHom).comp σ₀)
  have hz : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (σ₀ (Multiplicative.ofAdd χ)) := fun χ => by
    simp only [GlobalTheory.UU.chV, z, MulEquiv.apply_symm_apply]
    rfl
  have t₁ := s₃ _ _ a₀ ha₀ a₀ (RingHom.id _) _ _ h₀ _ (pw σ₀ hσ₀) (z ≫ GlobalTheory.SplitTorus.torusMap _ m) rfl
    fun χ => (chV_comp_torusMap z m χ).trans (hz _)
  have t₂ := s₃ _ _ a₀ ha₀ a₀ (RingHom.id _) _ _ h₀ _ hσ₀ z rfl hz
  have hf₀ : ((Over.pullback (spMap a₀)).map f).left ≫ pullback.fst G.hom (spMap a₀) =
      pullback.fst G.hom (spMap a₀) ≫ f.left := pullback.lift_fst _ _ _
  have hE := hm _ a₀ ha₀ _ _ h₀ _ hf₀
  rw [Over.comp_left, ← r₁, ← reassoc_of% r₂, t₁, t₂, Category.assoc z, ← hE, Category.assoc, ← hf₀]
  simp only [Over.comp_left, Category.assoc]

end GlobalTheory.Poinc.TorEnd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleDescentFiniteFlat
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBDescent

theorem exists_descent : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f] [IsLocallyNoetherian Y] (L : LB X), L.IsLB → ∀ (φ : ∀ i j, Γ(pullback f f, GlobalTheory.LBDescent.chart f L i j)ˣ), GlobalTheory.LBDescent.DescCompat f L φ → GlobalTheory.LBDescent.DescCocycle f L φ → ∃ L' : LB Y, L'.IsLB ∧ LBIso L (L'.pull f) := by
  intro X Y f _ _ _ _ L hL φ hc hcoc
  refine GlobalTheory.T.exists_lineBundle_of_descentInvariant_frames f L hL φ fun y => ?_
  obtain ⟨V, hy, t, ht⟩ := GlobalTheory.T.exists_lineBundle_trivial_near_fibre_finite f L hL y
  obtain ⟨c, hct, hcc⟩ := GlobalTheory.T.descentDatum_frame_cocycle_unit f L hL φ hc hcoc V t ht
  obtain ⟨V', hle, hy', u, hu⟩ := GlobalTheory.T.finiteFlat_unitCocycle_locally_coboundary f V c hcc y hy
  exact ⟨V', hy', GlobalTheory.T.twisted_frame_invariant_under_descentDatum f L φ V t ht c hct V' hle u hu⟩

end GlobalTheory.LBDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFrameOfSectionUnitsOnClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem isUnit_gs_id_iff {X : Scheme.{0}} (z : X) (U : X.Opens) (h : z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs (𝟙 X) z U a) ↔ z ∈ X.basicOpen a := by
  rw [gs_eq (𝟙 X) z U h, X.mem_basicOpen a z h]
  rfl

theorem exists_frame_of_isUnit_on_fibre : ∀ (X Y : Scheme.{0}) (β : X ⟶ Y), IsClosedMap β.base → ∀ (L : LB X), L.IsLB → ∀ (V : Y.Opens) (s : ∀ k : L.ι, Γ(X, β ⁻¹ᵁ V ⊓ L.U k)), IsSecOver L (β ⁻¹ᵁ V) s → ∀ y : Y, y ∈ V → (∀ (z : X) (k : L.ι), β z = y → z ∈ L.U k → IsUnit (gs (𝟙 X) z (β ⁻¹ᵁ V ⊓ L.U k) (s k))) → ∃ V' : Y.Opens, y ∈ V' ∧ V' ≤ V ∧ ∃ T : ∀ k : L.ι, Γ(X, β ⁻¹ᵁ V' ⊓ L.U k)ˣ, IsFrameOver L (β ⁻¹ᵁ V') T ∧ ∀ (f : X ⟶ X) (w : LB.Iso L (L.pull f)), SecCarriedOver L (β ⁻¹ᵁ V) s f w → FrameCarried L (β ⁻¹ᵁ V') T f w := by
  intro X Y β hβ L hL V s hs y hy hu
  let N : X.Opens := ⨆ k, X.basicOpen (s k)
  have hN : ∀ z : X, β z = y → z ∈ N := by
    intro z hz
    obtain ⟨k, hk⟩ := exists_chart hL z
    have hm : z ∈ β ⁻¹ᵁ V ⊓ L.U k := ⟨show β z ∈ V from hz ▸ hy, hk⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, (isUnit_gs_id_iff z _ hm _).1 (hu z k hz hk)⟩
  let V₀ : Y.Opens := ⟨(β '' (N : Set X)ᶜ)ᶜ, (hβ _ N.2.isClosed_compl).isOpen_compl⟩
  have hy₀ : y ∈ V₀ := by
    rintro ⟨p, hp, e⟩
    exact hp (hN p e)
  have hV₀ : ∀ p : X, β p ∈ V₀ → p ∈ N := by
    intro p hp
    by_contra h
    exact hp ⟨p, h, rfl⟩
  have hle : ∀ k, β ⁻¹ᵁ (V ⊓ V₀) ⊓ L.U k ≤ β ⁻¹ᵁ V ⊓ L.U k := fun k z hz => ⟨hz.1.1, hz.2⟩
  have hunit : ∀ k, IsUnit ((X.presheaf.map (homOfLE (hle k)).op).hom (s k)) := by
    intro k
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro z hz
    obtain ⟨k', hk'⟩ := TopologicalSpace.Opens.mem_iSup.1 (hV₀ z hz.1.2)
    have hm' : z ∈ β ⁻¹ᵁ V ⊓ L.U k' := X.basicOpen_le _ hk'
    have h1 : IsUnit (gs (𝟙 X) z _ (s k)) := by
      rw [hs z k k' hm'.1 hz.2 hm'.2]
      exact (Units.isUnit _).mul ((isUnit_gs_id_iff z _ hm' _).2 hk')
    rw [← gs_res (𝟙 X) z (hle k) hz, gs_eq (𝟙 X) z _ hz] at h1
    exact h1
  have key : ∀ (f : X ⟶ X) (z : X) (k : L.ι), f z ∈ β ⁻¹ᵁ (V ⊓ V₀) → f z ∈ L.U k →
      (gm f z _ (hunit k).unit : X.presheaf.stalk z) = gs f z _ (s k) := by
    intro f z k h1 h2
    have hm : f z ∈ β ⁻¹ᵁ (V ⊓ V₀) ⊓ L.U k := ⟨h1, h2⟩
    rw [← gs_unit f z _ hm, IsUnit.unit_spec, gs_res f z (hle k) hm]
  refine ⟨V ⊓ V₀, ⟨hy, hy₀⟩, inf_le_left, fun k => (hunit k).unit, ?_, ?_⟩
  · intro k k'
    refine unit_ext fun z hz => ?_
    rw [map_mul, gm_res _ z _ hz, gm_res _ z _ hz, gm_res _ z _ hz]
    apply Units.ext
    rw [Units.val_mul, key (𝟙 X) z k hz.1.1 hz.1.2, key (𝟙 X) z k' hz.2.1 hz.2.2]
    exact hs z k k' hz.1.1.1 hz.1.2 hz.2.2
  · intro f w hw z j k hz hfz hk hj
    apply Units.ext
    rw [Units.val_mul, key f z j hfz hj, key (𝟙 X) z k hz hk]
    exact hw z j k hz.1 hfz.1 hk hj

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftOfObstructionZeroStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundleLift_of_obstruction_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (S : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (P : S.Presents s i) (L₀ : LB X₀), IsPullback i s₀ s (spMap π) → L₀.IsLB → IsObL S α L₀ 0 → ∃ L : LB X, L.IsLB ∧ LBIso (L.pull i) L₀ := by
  first | exact @GlobalTheory.LBObs.exists_lift_of_isObL_zero | exact GlobalTheory.LBObs.exists_lift_of_isObL_zero | (intros; apply GlobalTheory.LBObs.exists_lift_of_isObL_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLocalGeneratorNearFiniteSetStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_localGenerator_near_finiteSet : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∀ F : Set X, F.Finite → F ⊆ W → ∃ (V : X.Opens) (a : ∀ k, Γ(X, V ⊓ L.U k)ˣ), F ⊆ V ∧ GlobalTheory.Pinch.LocGen L V a := by
  first | exact @GlobalTheory.Pinch.Semiloc.exists_locGen_near_finite | exact GlobalTheory.Pinch.Semiloc.exists_locGen_near_finite | (intros; apply GlobalTheory.Pinch.Semiloc.exists_locGen_near_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowSectionTransportPullbackIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open TopologicalSpace

namespace GlobalTheory.Mum

theorem exists_secK_of_iso_pull : ∀ {X X' : Scheme.{0}} (L : LB X) (L' : LB X') (f : X' ⟶ X) (w : LB.Iso L' (L.pull f)), L.IsLB → L'.IsLB → w.IsGen → ∀ (N : ℕ) (t : H0 L' N), ∃ s : SecK L f N, ∀ (Z : Scheme.{0}) (p : Z ⟶ X') (z : Z) J J', Good L z J → Good L' z J' → sval s p z J = (gw w p z (J (p ≫ f)) (J' p) ^ N).val * sval t p z J' := by
  intro X X' L L' f w hL hL' hw N t
  have hp := (isGen_iff w).1 hw
  have mL : ∀ (j : Fin 1 → L.ι) (x : X'), x ∈ LB.wchart L (fun _ : Fin 1 => f) j → f x ∈ L.U (j 0) :=
    fun j x hx => Set.mem_iInter.1 hx 0
  have mL' : ∀ (k : L'.ι) (x : X'), x ∈ L'.U k → x ∈ LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k) :=
    fun k x hx => Set.mem_iInter.2 fun _ => hx
  have indep : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k k' : L'.ι), f (r z) ∈ L.U j → r z ∈ L'.U k →
      r z ∈ L'.U k' →
      (gw w r z j k ^ N).val * gs r z (LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k)) (t.f (fun _ => k)) =
      (gw w r z j k' ^ N).val * gs r z (LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k')) (t.f (fun _ => k')) := by
    intro Z r z j k k' hj hk hk'
    rw [sec_trans t r z (mL' k _ hk) (mL' k' _ hk'), hp Z r z j j k k' hj hj hk hk', gm_self hL (r ≫ f) z hj,
      ← _root_.mul_assoc, ← Units.val_mul, trF, Fin.prod_univ_one, Category.comp_id, zpow_natCast, ← mul_pow, _root_.one_mul,
      mul_right_comm, inv_mul_cancel, _root_.one_mul]
  have glue : ∀ j : Fin 1 → L.ι, ∃ a : Γ(X', LB.wchart L (fun _ : Fin 1 => f) j),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (k : L'.ι), r z ∈ LB.wchart L (fun _ : Fin 1 => f) j → r z ∈ L'.U k →
      gs r z _ a = (gw w r z (j 0) k ^ N).val *
        gs r z (LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k)) (t.f (fun _ => k)) := by
    intro j
    let W : L'.ι → X'.Opens := fun k => LB.wchart L (fun _ : Fin 1 => f) j ⊓ L'.U k
    have l₁ : ∀ k, W k ≤ (L.pull f).U (fun _ => j 0) ⊓ L'.U k := fun k x hx => ⟨mem_pull.2 (mL j x hx.1), hx.2⟩
    have l₂ : ∀ k, W k ≤ LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k) := fun k x hx => mL' k x hx.2
    obtain ⟨u, hu⟩ : ∃ u : ∀ k, Γ(X', W k), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) k, r z ∈ W k →
        gs r z (W k) (u k) = (gw w r z (j 0) k ^ N).val *
          gs r z (LB.wchart L' (fun _ : Fin 1 => 𝟙 X') (fun _ => k)) (t.f (fun _ => k)) :=
      ⟨fun k => (res (l₁ k) (w.s (fun _ => j 0, k)) ^ N).val *
          (X'.presheaf.map (homOfLE (l₂ k)).op).hom (t.f (fun _ => k)), fun Z r z k hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_unit r z _ hz _).trans
          (congrArg Units.val ((map_pow _ _ _).trans (congrArg (· ^ N) (gm_res r z (l₁ k) hz _)))))
          (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := X'.sheaf.existsUnique_gluing' W (LB.wchart L (fun _ : Fin 1 => f) j)
      (fun k => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨k, hk⟩ := exists_chart hL' y
        exact Opens.mem_iSup.2 ⟨k, hy, hk⟩) u
      (fun k k' => fn_ext (V := W k ⊓ W k') fun y hy => by
        refine (gs_res (𝟙 X') y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 X') y inf_le_right hy _).symm)
        rw [hu _ _ y k hy.1, hu _ _ y k' hy.2]
        exact indep _ (𝟙 X') y (j 0) k k' (mL j y hy.1.1) hy.1.2 hy.2.2)
    refine ⟨a, fun Z r z k h₁ h₂ => ?_⟩
    have hz : r z ∈ W k := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z (W k)) (ha k)).trans (hu Z r z k hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z J J' hJ hJ' => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hL' y
    refine (gs_res (𝟙 X') y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 X') y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 X') y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 X') y j j' hy.1 hy.2)))
      (gs_res (𝟙 X') y _ hy _))).symm)
    refine (ha j _ (𝟙 X') y k hy.1 hk).trans (Eq.trans ?_ (congrArg _ (ha j' _ (𝟙 X') y k hy.2 hk)).symm)
    rw [hp _ (𝟙 X') y (j 0) (j' 0) k k (mL j y hy.1) (mL j' y hy.2) hk hk, gm_self hL' (𝟙 X') y hk, inv_one, _root_.mul_one,
      mul_pow, Units.val_mul, _root_.mul_assoc, Fin.prod_univ_one, zpow_natCast]
  · rw [sval_of t r z J' (fun _ => J' r) (fun _ => by rw [Category.comp_id])]
    exact ha _ Z r z (J' r) (hJ.mem (fun _ : Fin 1 => f) r) (hJ' r)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearCombinationTangentVectorsAffineOpenStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearCombination_tangentVectors_affineOpen : ∀ {K B : Type} [CommRing K] [CommRing B] {Y : Scheme.{0}} (p : Y ⟶ Sp K) (Y₀ : Y.affineOpens) (φ : K →+* B) (x : Sp B ⟶ Y) (hx : x ≫ p = spMap φ) (hxY : ⊤ ≤ x ⁻¹ᵁ Y₀.1) {n : ℕ} (w : Fin n → (Sp (DualNumber B) ⟶ Y)) (hwp : ∀ a, w a ≫ p = spMap ((algebraMap B (DualNumber B)).comp φ)) (hwx : ∀ a, spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w a = x) (c : Fin n → B), ∃ S : Sp (DualNumber B) ⟶ Y, S ≫ p = spMap ((algebraMap B (DualNumber B)).comp φ) ∧ spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ S = x ∧ ∀ O : Y.Opens, ⊤ ≤ x ⁻¹ᵁ O → ∀ f : Γ(Y, O), (valR S O f).snd = ∑ a, c a * (valR (w a) O f).snd := by
  first | exact @GlobalTheory.CechKS.LinTan.exists_linComb | exact GlobalTheory.CechKS.LinTan.exists_linComb | (intros; apply GlobalTheory.CechKS.LinTan.exists_linComb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationInvariantRigidifiedBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearisation_invariant_rigidified_bundle : ∀ (T X : Scheme.{0}) (π : X ⟶ T) (e : T ⟶ X), e ≫ π = 𝟙 T → Function.Surjective π.appTop.hom → ∀ (L : LB X), L.IsLB → (∃ r : LB.Gen (L.pull e), r.IsGen) → ∀ (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (θ : Ga → (T ⟶ T)), (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a c, θ (a * c) = θ a ≫ θ c) → (∀ a, e ≫ ρ a = θ a ≫ e) → (∀ a, LBIso L (L.pull (ρ a))) → ∃ u : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ a] ![1, -1]), (∀ a, (u a).IsGen) ∧ ∀ a c, LB.Gen.Corr L _ _ _ _ (u (a * c)) (LB.mulGen L _ _ _ _ (u a) (LB.pullGen L _ _ (u c) (ρ a))) := by
  first | exact @GlobalTheory.MumLin.exists_linearisation | exact GlobalTheory.MumLin.exists_linearisation | (intros; apply GlobalTheory.MumLin.exists_linearisation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationProd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.ProdLin

theorem exists_linearisation_prod : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ga Gb : Type) [Group Ga] [Group Gb] (ρ₁ : Ga → (X ⟶ X)) (ρ₂ : Gb → (X ⟶ X)) (ρ : Ga × Gb → (X ⟶ X)), (∀ p, ρ p = ρ₁ p.1 ≫ ρ₂ p.2) → (∀ a b, ρ₁ a ≫ ρ₂ b = ρ₂ b ≫ ρ₁ a) → (∀ a c, ρ₁ (a * c) = ρ₁ a ≫ ρ₁ c) → (∀ b d, ρ₂ (b * d) = ρ₂ b ≫ ρ₂ d) → ∀ (v₁ : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ₁ a] ![1, -1])) (v₂ : ∀ b, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ₂ b] ![1, -1])), (∀ a, (v₁ a).IsGen) → (∀ b, (v₂ b).IsGen) → (∀ a c, LB.Gen.Corr L _ _ _ _ (v₁ (a * c)) (LB.mulGen L _ _ _ _ (v₁ a) (LB.pullGen L _ _ (v₁ c) (ρ₁ a)))) → (∀ b d, LB.Gen.Corr L _ _ _ _ (v₂ (b * d)) (LB.mulGen L _ _ _ _ (v₂ b) (LB.pullGen L _ _ (v₂ d) (ρ₂ b)))) → (∀ a b, LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ (v₁ a) (LB.pullGen L _ _ (v₂ b) (ρ₁ a))) (LB.mulGen L _ _ _ _ (v₂ b) (LB.pullGen L _ _ (v₁ a) (ρ₂ b)))) → ∃ u : ∀ p : Ga × Gb, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ p] ![1, -1]), (∀ p, (u p).IsGen) ∧ ∀ p q, LB.Gen.Corr L _ _ _ _ (u (p * q)) (LB.mulGen L _ _ _ _ (u p) (LB.pullGen L _ _ (u q) (ρ p))) := by
  intro X L hL Ga Gb _ _ ρ₁ ρ₂ ρ hρ hcomm hρ₁ hρ₂ v₁ v₂ hv₁ hv₂ hc₁ hc₂ hc
  have hex : ∀ p : Ga × Gb, ∃ u : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ p] ![1, -1]), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J →
        val u r z J = val (LB.mulGen L _ _ _ _ (v₁ p.1) (LB.pullGen L _ _ (v₂ p.2) (ρ₁ p.1))) r z J := by
    intro p
    refine exists_gen hL ?_ _ (DVR.mulGen_isGen_of_isGen _ (hv₁ _) _ (DVR.pullGen_isGen_of_isGen _ _ _ (hv₂ _) _))
    intro U _ h
    simp [Fintype.prod_sum_type, Fin.prod_univ_two, hρ p]
  choose u hu hval using hex
  refine ⟨u, hu, fun p q => ?_⟩
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  refine corr_of_val hL fun y J hJ => ?_
  have e0 := hval (a * c, b * d) X (𝟙 X) y J hJ
  have e1 := hval (a, b) X (𝟙 X) y J hJ
  have e2 := hval (c, d) X (𝟙 X ≫ ρ (a, b)) y J hJ
  have f1 := val_corr hJ (hc₁ a c) (𝟙 X)
  have f2 := val_corr hJ (hc₂ b d) (ρ₁ (a * c))
  have g := val_corr hJ (hc c b) (ρ₁ a)
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at e0
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at e1
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at e2
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at f1
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at f2
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁] at g
  try simp only [val_mul hJ, val_pull hJ, Prod.mk_mul_mk, Category.id_comp, Category.assoc, hρ, hρ₁]
  rw [e0, e1, e2, f1, f2, ← hcomm c b, _root_.mul_assoc, _root_.mul_assoc, ← _root_.mul_assoc (val (v₁ c) (ρ₁ a) y J), g]
  simp only [_root_.mul_assoc]
end GlobalTheory.ProdLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalNormalDomainFiniteExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_normal_domain_finite_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (K' : Type) [Field K'] [Algebra (FractionRing R) K'] [FiniteDimensional (FractionRing R) K'], ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (_ : IsNoetherianRing R') (_ : IsIntegrallyClosed R') (ρ : R →+* R') (e : FractionRing R' ≃+* K'), IsLocalHom ρ ∧ Function.Injective ρ ∧ (∀ r, e (algebraMap R' _ (ρ r)) = algebraMap (FractionRing R) K' (algebraMap R _ r)) ∧ ∀ (x : FractionRing R) (w : R'), e (algebraMap R' _ w) = algebraMap (FractionRing R) K' x → ∃ r : R, algebraMap R _ r = x := by
  first | exact @GlobalTheory.LocalNormalExt.exists_local_normal_domain_of_finite_extension | exact GlobalTheory.LocalNormalExt.exists_local_normal_domain_of_finite_extension | (intros; apply GlobalTheory.LocalNormalExt.exists_local_normal_domain_of_finite_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSmoothGroupOverNbhdStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_smooth_group_over_nbhd : ∀ (σ : Setup) (E : Emb σ), σ.Common → ∀ x : Sp σ.R, ∃ g : σ.R, g ∉ x.asIdeal ∧ ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ E.P), E.LocGrp g H h ∧ ∀ z : E.P, z ∈ E.U → x.asIdeal ≤ (E.p z).asIdeal → (E.p z).asIdeal ≤ x.asIdeal → z ∈ Set.range h := by
  first | exact @GlobalTheory.Desc.Emb.exists_locGrp | exact GlobalTheory.Desc.Emb.exists_locGrp | (intros; apply GlobalTheory.Desc.Emb.exists_locGrp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogKodairaSpencerLocalEigenFrameStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logKodairaSpencer_local_eigenFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed Xo c → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (x : X₀ TF.Y Z) (φ : c.F →+* (X₀ TF.Y Z).presheaf.stalk x) (f : GlobalTheory.ShFam.EigFrame TF.Y φ ((show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ (barComp TF.Y Z).ι)), (show Sp ((X₀ TF.Y Z).presheaf.stalk x) ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk x) ≫ s₀ TF.Y Z = spMap φ → ∃ D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z, GlobalTheory.LogKSDiv.GenKS TF Z (fun τ k => spMap (dualMap (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)) ≫ f.v τ k) D ∧ ∀ (U : (X₀ TF.Y Z).Opens) (ω : TopForm.FormsOn (s₀ TF.Y Z) Dw.dim U), TopForm.IsFrame ω → ∀ hx : x ∈ U, RegAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U (gen_mem hx) ω)) ∧ (UnitAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U (gen_mem hx) ω)) ↔ x ∈ (j₀ TF.Y Z).opensRange) := by
  first | exact @GlobalTheory.LogKSDiv.exists_genKS_local | exact GlobalTheory.LogKSDiv.exists_genKS_local | (intros; apply GlobalTheory.LogKSDiv.exists_genKS_local <;> assumption)
end

