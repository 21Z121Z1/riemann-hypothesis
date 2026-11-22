import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0094
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenericFibreIsoOfCompatibleThickenings
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsCPMapDescends
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0099
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFacOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleOfNormOneGenerators
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteDimensionalFieldDegenerationValues
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.FiniteValues
open GlobalTheory.TorusExt GlobalTheory.ArcExt

theorem exists_finset_point {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    (B : Over (Spec (CommRingCat.of R))) [LocallyOfFiniteType B.hom] (p : TF (R := R) F ⟶ B) :
    ∃ S : Finset F, ∀ K : IntermediateField (FractionRing R) F, (S : Set F) ⊆ K →
      ∃ l : TF (R := R) K ⟶ B, extMap (R := R) (algebraMap K F) rfl ≫ l = p := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hpt, -⟩ := B.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (p.left (IsLocalRing.closedPoint F))) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨f, hf⟩ : ∃ f : Γ(B.left, U) ⟶ CommRingCat.of F, Spec.map f ≫ hU.fromSpec = p.left := by
    refine ⟨Spec.preimage (IsOpenImmersion.lift hU.fromSpec p.left ?_), ?_⟩
    · rintro _ ⟨y, rfl⟩
      rw [hU.range_fromSpec, Subsingleton.elim (α := PrimeSpectrum F) y (IsLocalRing.closedPoint F)]
      exact hpt
    · rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg⟩ : ∃ g : CommRingCat.of R ⟶ Γ(B.left, U), Spec.map g = hU.fromSpec ≫ B.hom :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hgf : g ≫ f = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫
      CommRingCat.ofHom (algebraMap (FractionRing R) F) :=
    Spec.map_injective (by
      rw [Spec.map_comp, hg, ← Category.assoc, hf, Spec.map_comp]
      exact Over.w p)
  have hV : ∀ r : R, f.hom (g.hom r) = algebraMap (FractionRing R) F (algebraMap R _ r) := fun r =>
    congrArg (fun q => q.hom r) hgf
  have hft : g.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map g) := by rw [hg]; infer_instance
    exact HasRingHomProperty.Spec_iff.1 this
  let _ : Algebra R Γ(B.left, U) := g.hom.toAlgebra
  obtain ⟨s, hs⟩ := (show Algebra.FiniteType R Γ(B.left, U) from hft).out
  refine ⟨s.image f.hom, fun K hK => ?_⟩
  have hr : ∀ a, f.hom a ∈ K := fun a => by
    have ha : a ∈ Algebra.adjoin R (s : Set Γ(B.left, U)) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact hK (Finset.mem_image_of_mem _ hx)
    | algebraMap r => exact (hV r).symm ▸ K.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let f' : Γ(B.left, U) ⟶ CommRingCat.of K := CommRingCat.ofHom (f.hom.codRestrict K hr)
  refine ⟨Over.homMk (Spec.map f' ≫ hU.fromSpec) ?_, Over.OverMorphism.ext ?_⟩
  · change (Spec.map f' ≫ hU.fromSpec) ≫ B.hom = Spec.map _ ≫ Spec.map _
    rw [Category.assoc, ← hg, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact hV r
  · change Spec.map _ ≫ Spec.map f' ≫ hU.fromSpec = _
    rw [← hf, ← Spec.map_comp_assoc]
    rfl

theorem exists_finite_field_of_values : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra.IsAlgebraic (FractionRing R) F] (N : NumD F) (_ : NumOf D F N) (T : Set N.A), T.Finite → ∃ (K₁ : IntermediateField (FractionRing R) F) (A₀ : Subgroup N.A), FiniteDimensional (FractionRing R) K₁ ∧ (∀ x ∈ T, x ∈ A₀) ∧ (∀ χ, N.c χ ∈ A₀) ∧ (∀ x ∈ A₀, ∀ y ∈ A₀, ∀ u ∈ A₀, (N.θ x y u : F) ∈ K₁) ∧ (∀ x ∈ A₀, (N.σ x : F) ∈ K₁) ∧ (∀ x ∈ A₀, N.th x ∈ K₁) ∧ ∀ χ, (N.ψ χ : F) ∈ K₁ := by
  intro R _ _ D F _ _ _ N ν T hT
  haveI := D.P.isAb.proper
  choose S hS using fun x : N.A => exists_finset_point D.P.A (ν.eA x)
  let s : Set F := ⋃ x ∈ T, (S x : Set F)
  haveI : Finite s := (hT.biUnion fun x _ => (S x).finite_toSet).to_subtype
  let K := IntermediateField.adjoin (FractionRing R) s
  let f : K →+* F := algebraMap K F
  have hf : f.comp (algebraMap (FractionRing R) K) = algebraMap (FractionRing R) F := rfl
  let Φ : (TF (R := R) K ⟶ D.P.A) →* N.A :=
    MonoidHom.mk' (fun x => ν.eA.symm (extMap f hf ≫ x)) fun x y => by rw [MonObj.comp_mul, map_mul]
  have hΦ : ∀ x, ν.eA (Φ x) = extMap f hf ≫ x := fun x => ν.eA.apply_symm_apply _
  let J : (Sp K ⟶ D.P.A.left) → D.P.L.ι := fun ψ => ν.J (spMap f ≫ ψ)
  have hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ) := fun ψ z _ => by
    have h := ν.good (spMap f ≫ ψ) (Set.mem_univ (IsLocalRing.closedPoint F))
    rw [Subsingleton.elim (α := PrimeSpectrum K) z (spMap f (IsLocalRing.closedPoint F))]
    exact h
  have hJ' : ∀ ψ, ν.J (spMap f ≫ ψ) = J ψ := fun _ => rfl
  have hm : ∀ a : K, f a ∈ K := fun a => a.2
  have hv : ∀ {Y : Scheme.{0}} {I : Type} [Fintype I] {φ : I → (Y ⟶ D.P.A.left)} {ε : I → ℤ}
      (t : LB.Gen (LB.LinComb D.P.L φ ε)) (r : Sp K ⟶ Y), vF t (spMap f ≫ r) ν.J ∈ K := fun t r => by
    rw [vF_ext f hJ hJ']; exact hm _
  have hw : ∀ {Y : Scheme.{0}} {I : Type} [Fintype I] {φ : I → (Y ⟶ D.P.A.left)} {ε : I → ℤ}
      (t : LB.Sec (LB.LinComb D.P.L φ ε)) (r : Sp K ⟶ Y), sF t (spMap f ≫ r) ν.J ∈ K := fun t r => by
    rw [sF_ext f hJ hJ']; exact hm _
  have hrig : rigVal ν ∈ K := by
    rw [rigVal, ← Over.w (extMap (R := R) f hf)]
    exact hv _ _
  refine ⟨K, Φ.range, IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral,
    fun x hx => ?_, fun χ => ?_, ?_, ?_, ?_, fun χ => ?_⟩
  · obtain ⟨l, hl⟩ := hS x K ((Set.subset_biUnion_of_mem (u := fun x => (S x : Set F)) hx).trans
      (IntermediateField.subset_adjoin _ _))
    exact ⟨l, ν.eA.injective ((hΦ l).trans hl)⟩
  · exact ⟨DegPre.cF D K (ν.eX χ), ν.eA.injective ((hΦ _).trans ((DVR.comp_cP D _ _).trans (ν.c_eq χ).symm))⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _ ⟨u, rfl⟩
    rw [ν.θ_eq, hΦ, hΦ, hΦ, ← comp_lift, ← comp_lift]
    exact hv _ _
  · rintro _ ⟨x, rfl⟩
    rw [ν.σ_eq, hΦ]
    exact hv _ _
  · rintro _ ⟨x, rfl⟩
    have h0 : rigVal ν ≠ 0 := vF_ne_zero ν.good _ _
    rw [eq_div_of_mul_eq h0 (ν.th_eq (Φ x)), hΦ]
    exact div_mem (hw _ _) hrig
  · rw [ν.ψ_eq]
    refine mul_mem ?_ hrig
    rw [← (extMap_jFK (R := R) f hf).trans (Category.id_comp _)]
    exact hv _ _

end GlobalTheory.FiniteValues
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericRel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericIso

open GlobalTheory.RigidGeneric GlobalTheory.SecRingIso ReciprocityTheory.ChartRestriction.G.DVR in

theorem exists_genericRel : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), GlobalTheory.GenericIso.LevelIso U.toUnifPre U'.toUnifPre hD j → GlobalTheory.GenericIso.Enough U.toUnifPre U'.toUnifPre hD j → ∃ (Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))), GlobalTheory.GenericIso.GenericRel U.toUnifPre U'.toUnifPre hD j Φ w := by
  intro hL R _ _ I hI D D' A A' G G' _ _ _ _ hG hG' U U' hD j _ en
  obtain ⟨w, v, hw, hv, -, lf⟩ := exists_compare U
  obtain ⟨w', v', hw', hv', e', lf'⟩ := exists_compare U'
  have jac : I ≤ Ideal.jacobson ⊥ := by
    have := hI.2.2.2
    exact IsAdicComplete.le_jacobson_bot I
  have := hI.1
  have := hG.smooth
  have := hG'.smooth
  have := hG.geomConnected
  have := hG'.geomConnected
  let Ag : ∀ k, H0 U'.LG.L k → H0 U.LG.L k → Prop := fun k σ' σ => ∀ e,
    Agr (W := (thickObj R I e G').left) (Idx := D.toPre.P.L.ι × D'.toPre.P.L.ι)
      ((j e).hom.left ≫ (fstG I e G).left) (fstG I e G').left
      (fun y i => (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left y) ∈
        D.toPre.P.L.U i.1 ∧ (U'.gt e).pG.left y ∈ D'.toPre.P.L.U i.2)
      (fun Z r z i jL => Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z i.1 (fun _ => jL))
      (fun Z r z i jL => Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z i.1 i.2 * Geo.Tor.gw (U'.w e) r z i.2 (fun _ => jL))
      σ σ'
  have ov : ∀ e, ((j e).hom.left ≫ (fstG I e G).left) ≫ G.hom = (fstG I e G').left ≫ G'.hom := fun e =>
    (Category.assoc _ _ _).trans ((congrArg ((j e).hom.left ≫ ·) (Over.w (fstG I e G))).trans
      (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ thick R I e) (Over.w (j e).hom))).trans
        (Over.w (fstG I e G')).symm))
  have cov : ∀ e (y : (thickObj R I e G').left), ∃ i : D.toPre.P.L.ι × D'.toPre.P.L.ι,
      (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left y) ∈
        D.toPre.P.L.U i.1 ∧ (U'.gt e).pG.left y ∈ D'.toPre.P.L.U i.2 := fun e y => by
    obtain ⟨a, ha⟩ := exists_chart D.toPre.P.isLB
      ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left y))
    obtain ⟨b, hb⟩ := exists_chart D'.toPre.P.isLB ((U'.gt e).pG.left y)
    exact ⟨(a, b), ha, hb⟩
  obtain ⟨Φ, w₀, h₀, H⟩ := exists_iso_of_rel hL G.hom G'.hom U.LG.isLB U'.LG.isLB A A' (gen_over' U) (gen_over' U')
    (gen_injective U) (gen_injective U') hv hv' lf lf' Ag
    (fun k c s' s t' t d' d h h' f' f e => (h e).comb (ov e) (h' e) f f')
    (fun n m s' s t' t d' d h h' f' f e => (h e).mul (h' e) f f')
    (fun k s' s h => ⟨fun f => funext ((sec_eq_zero_and_hom_eq_of_thickenings R I jac G).1 _
        (linComb_isLB _ U.LG.isLB _ _) s fun e J => by
          have : IsIso (j e).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (j e).hom))
          exact (ConcreteCategory.bijective_of_isIso ((j e).hom.left.app _)).1
            (((h e).zero U'.LG.isLB (cov e) f J).trans (map_zero _).symm)),
      fun f => funext ((sec_eq_zero_and_hom_eq_of_thickenings R I jac G').1 _
        (linComb_isLB _ U'.LG.isLB _ _) s' fun e J => (h e).symm.zero U.LG.isLB (cov e) f J)⟩)
    (fun k hk s => by
      obtain ⟨c, t', t, hc, h₁, h₂⟩ := (en k hk).1 s
      exact ⟨c, hc, t', t, fun e Z r z i a b hC => h₂ e Z r z i.1 i.2 a b hC.1 hC.2, funext h₁⟩)
    (fun k hk s => by
      obtain ⟨c, t', t, hc, h₁, h₂⟩ := (en k hk).2 s
      exact ⟨c, hc, t', t, fun e Z r z i a b hC => h₂ e Z r z i.1 i.2 a b hC.1 hC.2, funext h₁⟩)
  obtain ⟨u, hu, K⟩ := exists_move U.LG.isLB U'.LG.isLB A.isLB A'.isLB (gen_inv U') hv h₀ hw' e'
    ((U'.gen ≪≫ Φ ≪≫ U.gen.symm).hom.left ≫ pullback.fst G.hom (jK R))
    ((Category.assoc _ _ _).trans (congrArg (U'.gen.hom.left ≫ ·) (Category.assoc _ _ _)))
  refine ⟨U'.gen ≪≫ Φ ≪≫ U.gen.symm, u, hu, fun k hk σ' σ h => ?_⟩
  obtain ⟨a, ha⟩ := exists_pulls U.LG.isLB A.isLB hv σ
  obtain ⟨a', ha'⟩ := exists_pulls U'.LG.isLB A'.isLB hv' σ'
  exact K k σ σ' a a' ha
    (H k hk σ' σ a' a (fun e Z r z i a b hC => h e Z r z i.1 i.2 a b hC.1 hC.2) ha' ha) ha'

end GlobalTheory.GenericIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericSquare
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ClosedPol

theorem exists_fibre_pull (laws : Laws) {S S' Z Z' : Scheme.{0}} {j : Z ⟶ S} {j' : Z' ⟶ S'} {f : S' ⟶ S} {ψ : Z' ⟶ Z}
    (sq : ψ ≫ j = j' ≫ f) {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB) (A : PolAV Z)
    (gen : (Over.pullback j).obj G ≅ A.A) [IsMonHom gen.hom]
    (hA : LBIso (A.L.pull gen.hom.left) (L.pull (pullback.fst G.hom j))) :
    ∃ (A' : PolAV Z') (gen' : (Over.pullback j').obj ((Over.pullback f).obj G) ≅ A'.A),
      IsMonHom gen'.hom ∧ LBIso (A'.L.pull gen'.hom.left) ((L.pull (pullback.fst G.hom f)).pull
        (pullback.fst ((Over.pullback f).obj G).hom j')) := by
  obtain ⟨A', g, hg, -, mul, t, ht⟩ := laws.polBaseChange _ _ ψ A
  have pg : IsGrpPullback A'.A A.A ψ g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    obtain rfl : x₀ = toBase hg.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = toBase hg.w y := Over.OverMorphism.ext hy
    exact (congrArg (fun a => a.left) (mul T x y)).symm⟩
  have : IsMonHom gen.symm.hom := inferInstanceAs (IsMonHom gen.inv)
  have h₂ := (pg.comp ((isGrpPullback_of_iso gen.symm).comp (isGrpPullback_pullback G j))).congr
    ((congrArg _ (Category.id_comp _)).trans sq) rfl
  obtain ⟨gen', hgen', e⟩ := grpPullback_iso ((isGrpPullback_pullback _ j').comp
    (isGrpPullback_pullback G f)) h₂
  have hi : gen.inv.left ≫ gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, gen.inv_hom_id, Over.id_left]
  refine ⟨A', gen', hgen', LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB g) gen'.hom.left)
    (pull_isLB (pull_isLB hL _) _) ?_ ?_⟩
  · exact LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (Geo.Tor.chartPullPull _ _ _ rfl) (LBIso.symm ⟨t, ht⟩)
  · refine LBIso.chartPull (h := gen'.hom.left ≫ g ≫ gen.inv.left)
      (chartPullLinComb A.L g _ (fun _ : PUnit => gen.hom.left) _ _ fun _ => ?_)
      (chartPullLinComb L _ _ (fun _ : PUnit => pullback.fst G.hom j) _ _ fun _ => ?_) hA
    · rw [Category.assoc, Category.assoc, hi, Category.comp_id]
    · rw [Category.assoc, Category.assoc]
      exact e.symm

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem exists_generic_square {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]
    (φ : R →+* V) (hφ : Function.Injective φ) :
    ∃ ψ : Spec (CommRingCat.of (FractionRing V)) ⟶ Spec (CommRingCat.of (FractionRing R)),
      ψ ≫ jK R = jK V ≫ spMap φ := by
  have gen : ∀ (K F : Type) [Field K] [Field F] [Algebra R K] [IsFractionRing R K] (g : R →+* F),
      Function.Injective g → ∃ ψ : K →+* F, ψ.comp (algebraMap R K) = g := fun K F _ _ _ _ g hg =>
    ⟨IsFractionRing.lift hg, RingHom.ext fun x => IsFractionRing.lift_algebraMap hg x⟩
  obtain ⟨ψ, hψ⟩ := gen (FractionRing R) (FractionRing V) ((algebraMap V (FractionRing V)).comp φ)
    ((IsFractionRing.injective V (FractionRing V)).comp hφ)
  exact ⟨spMap ψ, (spMap_comp _ ψ).trans ((congrArg spMap hψ).trans (spMap_comp φ _).symm)⟩

theorem exists_desc_pull {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] {G : Over S} {G' : Over S'}
    [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {F : G'.left ⟶ G.left} (pF : IsGrpPullback G' G f F)
    (Q : TQ G X) {P : CP G} (D : Q.Desc P) {P' : CP G'} {hw w} (k : IsCPMap P' P f F hw w) :
    ∃ (Q' : TQ G' X) (D' : Q'.Desc P') (β : Q'.B.left ⟶ Q.B.left), IsGrpPullback Q'.B Q.B f β ∧
      LBIso D'.M.L.L (D.M.L.L.pull β) := by
  obtain ⟨Q₀, hQ⟩ := exists_tq_baseChange _ _ _ X _ _ F pF Q
  obtain ⟨β, eβ, pβ⟩ := TQ.exists_isGrpPullback _ _ _ X _ _ F pF Q Q₀ hQ
  obtain ⟨M₀, v, hv⟩ := exists_pull (hw := pβ.1.w) D.M
    (fun Z x y => Over.OverMorphism.ext (pβ.2 Z x y _ _ rfl rfl).symm)
  obtain ⟨w₄, -, k₄⟩ := D.map.exists_comp k (by rw [Category.assoc, Over.w, hw, Category.comp_id])
  obtain ⟨w₅, k₅⟩ := cpMap_congr ((Category.comp_id _).trans (Category.id_comp _).symm) eβ.symm k₄
    (by rw [Category.assoc, pβ.1.w, Over.w_assoc, Category.id_comp])
  have := Q₀.q_hom
  obtain ⟨w₆, k₆, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ P' _ _ _ Q₀.q.left (by simp) _ hv).2
    (toBase_mul_of_isMonHom Q₀.q _) w₅ k₅
  exact ⟨Q₀, ⟨M₀, w₆, k₆⟩, β, pβ, v, hv.gen⟩

theorem exists_fourth {S S' Z Z' : Scheme.{0}} {t : Z ⟶ S} {t' : Z' ⟶ S'} {f : S' ⟶ S} {b : Z' ⟶ Z}
    (sq : b ≫ t = t' ≫ f) {G : Over S} {G' : Over S'} {H : Over Z} {H' : Over Z'} [GrpObj G] [IsCommMonObj G]
    [GrpObj G'] [IsCommMonObj G'] [GrpObj H] [IsCommMonObj H] [GrpObj H'] [IsCommMonObj H']
    {F : G'.left ⟶ G.left} {c : H.left ⟶ G.left} {c' : H'.left ⟶ G'.left} (pF : IsGrpPullback G' G f F)
    (pc : IsGrpPullback H G t c) (pc' : IsGrpPullback H' G' t' c') {P : CP G} {P' : CP G'} {N : CP H} {N' : CP H'}
    {h₁ w₁ h₂ w₂ h₃ w₃} (k₁ : IsCPMap P' P f F h₁ w₁) (k₂ : IsCPMap N P t c h₂ w₂) (k₃ : IsCPMap N' P' t' c' h₃ w₃) :
    ∃ (E : H'.left ⟶ H.left) (pE : IsGrpPullback H' H b E) (w : _), IsCPMap N' N b E pE.1.w w := by
  have p := pc'.comp pF
  have w : (c' ≫ F) ≫ G.hom = (H'.hom ≫ b) ≫ t := p.1.w.trans (by rw [Category.assoc, sq])
  have e₁ := pc.1.lift_fst _ _ w
  have e₂ := pc.1.lift_snd _ _ w
  have p' := p.congr sq.symm e₁.symm
  have pE := pc.cancel p' e₂
  obtain ⟨w₄, -, k₄⟩ := k₁.exists_comp k₃ p.1.w
  obtain ⟨w₅, k₅⟩ := cpMap_congr sq.symm e₁.symm k₄ p'.1.w
  obtain ⟨w₆, k₆, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ N' _ _ _ _ e₂ _ k₂).2
    (fun Z x y => Over.OverMorphism.ext (pE.2 Z x y _ _ rfl rfl).symm) w₅ k₅
  exact ⟨_, pE, w₆, k₆⟩

theorem exists_trait (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (I : Ideal R) {k : Type}
    [Field k] (a : R ⧸ I ^ (0 + 1) →+* k) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (φ : R →+* V)
      (b : R ⧸ I ^ (0 + 1) →+* V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)), CDVR V ∧ Function.Injective φ ∧
      RingHom.ker a = RingHom.ker b ∧ spMap b ≫ thick R I 0 = thick V _ 0 ≫ spMap φ := by
  have := RingHom.ker_isPrime a
  obtain ⟨V, _, _, _, φ, hV, hφ, hm⟩ := exists_cdvr R ((RingHom.ker a).comap (Ideal.Quotient.mk _))
  have hm' : (IsLocalRing.maximalIdeal V ^ (0 + 1)).comap φ = (RingHom.ker a).comap (Ideal.Quotient.mk _) := by
    rw [← hm, zero_add, pow_one]
  have le : I ^ (0 + 1) ≤ (IsLocalRing.maximalIdeal V ^ (0 + 1)).comap φ := fun r hr => by
    rw [hm', Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hr]
    exact zero_mem _
  refine ⟨V, _, ‹_›, ‹_›, φ, Ideal.quotientMap (IsLocalRing.maximalIdeal V ^ (0 + 1)) φ le, hV, hφ,
    Ideal.ext fun y => ?_, ?_⟩
  · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← Ideal.mem_comap, ← hm', RingHom.mem_ker, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem]
    rfl
  · rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      Ideal.quotientMap_comp_mk]

set_option maxHeartbeats 800000 in

theorem main : Laws → Laws2 → Laws3 → USt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (T : TowerR I P X) (k : Type) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (0 + 1)))), RelAmple ((Over.pullback x).obj (T.l 0).Q.B) ((T.l 0).D.M.L.L.pull (pullback.fst _ x)) ∧ KTriv ((Over.pullback x).obj (T.l 0).Q.B) ((T.l 0).D.M.L.L.pull (pullback.fst _ x)) := by
  intro laws _ _ hU R _ _ _ I ⟨⟨hN, _⟩, _, hc, _⟩ G _ _ P hG ⟨w, _, hw, _, _, prim, _⟩ A gen hgen hA X _ _ _ T k _ x
  obtain ⟨a, rfl⟩ : ∃ a : R ⧸ I ^ (0 + 1) →+* k, spMap a = x := ⟨(Spec.preimage x).hom, Spec.map_preimage x⟩
  obtain ⟨V, _, _, _, φ, b, hV, hφ, hab, sq⟩ := exists_trait R I a
  obtain ⟨ψ, sq'⟩ := exists_generic_square φ hφ
  obtain ⟨A', gen', hgen', hA'⟩ := exists_fibre_pull laws sq' P.L.isLB A gen hA
  obtain ⟨P', wP, hP', H⟩ := exists_cp_pull _ _ (spMap φ) G ((Over.pullback (spMap φ)).obj G) _ _
    (toBase_mul_pullback G (spMap φ)) P
  have prim' := prim_pull (spMap φ) prim
  rw [← hP'] at hA' prim'
  obtain ⟨P₀, w₀, H₀⟩ := exists_isLevelCP (IsLocalRing.maximalIdeal V) 0 P'
  obtain ⟨wl, hl⟩ := (T.l 0).lev
  obtain ⟨F, pF, w₃, k₃⟩ := exists_fourth (G := G) (G' := (Over.pullback (spMap φ)).obj G) (H := thickObj R I 0 G)
    (H' := thickObj V (IsLocalRing.maximalIdeal V) 0 ((Over.pullback (spMap φ)).obj G)) (P := P) (P' := P')
    (N := (T.l 0).Pe) (N' := P₀) sq (isGrpPullback_pullback G (spMap φ))
    (isGrpPullback_pullback G (thick R I 0)) (isGrpPullback_pullback _ (thick V (IsLocalRing.maximalIdeal V) 0)) H hl H₀
  obtain ⟨Q₀, D₀, β, pβ, hβ⟩ := exists_desc_pull pF (T.l 0).Q (T.l 0).D k₃
  have hG' := IsSemiAbelian.pullback (spMap φ) G hG
  have ev := GlobalTheory.T.exists_even_cubical_trivialisation_specialFibre laws V hV A' _ hG' gen' hgen' P' ((Over.pullback (spMap φ)).map w) inferInstance
    prim' X Q₀ P₀ ⟨w₀, H₀⟩
  obtain ⟨wA, hwA⟩ := hA'
  have pol := pol_dvr laws hU
    { cdvr := hV, semi := hG', gen := gen', gen_hom := hgen', P := P', wA := wA, wA_gen := hwA, X := X, Q₀ := Q₀,
      P₀ := P₀, lev₀ := ⟨w₀, H₀⟩, even₀ := ev } D₀
  have : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  let _ : Field (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := Ideal.Quotient.field _
  exact pol_of_ker_eq a b hab _ (T.l 0).Q.isAb (T.l 0).D.M.L.isLB Q₀.B pβ D₀.M.L.isLB hβ pol

end GlobalTheory.ClosedPol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeometricTestMapClassicalPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem GlobalTheory.ZH.exists_geoTest_tMap_and_centre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), S.Big → ρ.HasGeo → (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), Set.range (gPt p ≫ y) ⊆ U₀ → ∃ (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u), Nonempty (Q.TMap t c)) ∧ ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y := by
  intro hL o Ω _ _ _ hA S ρ M U₀ EE hB Q hbig hgeo
  refine ⟨fun p _ y hy => ?_, fun z hz => ?_⟩
  · obtain ⟨y₀, Fs, hn, hF⟩ := GlobalTheory.T.exists_factor_classicalPoint_of_large_test o Ω S ρ M U₀ EE hB Q p y hy
    obtain ⟨t, ht⟩ := hgeo p y₀ hn Fs
    obtain ⟨c⟩ := hF t.u ht
    exact ⟨y₀, t, c, GlobalTheory.T.nonempty_testModel_to_closure hL o Ω S ρ M U₀ EE hB Q p y y₀ t c hbig⟩
  · haveI := hA.ft
    haveI := hA.char
    exact ((GlobalTheory.ZH.classical_points_and_local_regularity o Ω M U₀ hB.ov.normal).1 U₀ le_rfl hB.ov.ne z hz).1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsFib
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.Ex.AbPartIso
variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N N' : NumD F}

def HomF (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A) : Prop :=
  φ.hom ≫ fst _ _ = fst _ _ ∧ ∀ (Z : Over (Sp R)) (t : Z ⟶ TF (R := R) F) (x y : Z ⟶ D.P.A),
    lift t (x * y) ≫ φ.hom ≫ snd _ _ = (lift t x ≫ φ.hom ≫ snd _ _) * (lift t y ≫ φ.hom ≫ snd _ _)

abbrev BunIso (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A) : Type :=
  LB.Iso (D.P.L.pull (snd (TF (R := R) F) D.P.A).left) (D'.P.L.pull (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left)

def Carries (ν : NumOf D F N) (ν' : NumOf D' F N') (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A)
    (x : N.A) (x' : N'.A) : Prop :=
  lift (𝟙 _) (ν.eA x) ≫ φ.hom = lift (𝟙 _) (ν'.eA x')

def wVal (ν : NumOf D F N) (ν' : NumOf D' F N') {φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A} (w : BunIso φ)
    (f : N.A → N'.A) (x : N.A) : F :=
  valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left _
    (w.s (fun _ => ν'.J (ν'.eA (f x)).left, fun _ => ν.J (ν.eA x).left)).val

def AllIso (P : ∀ {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {N N' : NumD F} (_ : NumOf D F N) (_ : NumOf D' F N') {φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A},
    BunIso φ → (N.A → N'.A) → Prop) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (φ : TF (R := R) F ⊗ D.P.A ≅ TF (R := R) F ⊗ D'.P.A)
    (w : BunIso φ) (f : N.A → N'.A), HomF φ → w.IsGen → (∀ x, Carries ν ν' φ x (f x)) → P ν ν' w f

def TorsMap {O : Type} [CommRing O] (B B' : NumB O) (m : ℕ) (c : O) (ρ : B.A → B'.A) : Prop :=
  (∀ b b', b ^ m ^ 2 = 1 → b' ^ m ^ 2 = 1 →
    ρ (b * b') = ρ b * ρ b' ∧ B'.weil (m ^ 2) (ρ b) (ρ b') = B.weil (m ^ 2) b b') ∧
  ∀ b, b ^ m ^ 2 = 1 → ρ b ^ m ^ 2 = 1 ∧ B'.uth m (ρ b) 1 = c * B.uth m b 1

def IsFib (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (Q : PolAV (Sp F))
    (Φ : Q.A.left ⟶ D.P.A.left) : Prop :=
  IsGrpPullback Q.A D.P.A (TF (R := R) F).hom Φ ∧ LBIso Q.L (D.P.L.pull Φ) ∧ Q.g = D.P.g

theorem exists_isFib (hB : PolBaseChangeSt) (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    ∃ Q Φ, IsFib D F Q Φ := by
  obtain ⟨P', φ, hφ, hg, hm, ht⟩ := hB _ _ (TF (R := R) F).hom D.P
  refine ⟨P', φ, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, LBIso.symm ht, hg⟩
  rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
  rfl

end GlobalTheory.Ex.AbPartIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleExtensionThetaSectionSemiAbelian
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem exists_extension_with_section : Semi.extend_existsSt.{0} → Out.MulNSt → (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, (n : K) ≠ 0 → Surjective (mulN B n).left) → ∀ (C : Core) (L : C.Law) (T : C.Theta) (n : ℕ), letI := L.grp; letI := L.comm; IsSemiAbelian C.GG → C.HasTests → C.TorsSec n → T.Few n → ∃ M : LB C.G.toScheme, M.IsLB ∧ LBIso (M.pull C.a) T.L.L ∧ ∀ z : C.Z, ∃ (N : C.Z.Opens) (σ : LB.Sec (M.pull (C.GG.hom ⁻¹ᵁ N).ι)), z ∈ N ∧ ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, C.GG.hom ((C.GG.hom ⁻¹ᵁ N).ι x) = z' := by
  intro hE hM hS C L T n hG hT hTors hFew
  have hB : T.BTest L := GlobalTheory.T.baseChangeTest_of_surjective_mul_abelianVariety hS C L T
  have hO : IsOpen (T.Om L) := (GlobalTheory.ZJ.etale_mulN_and_isOpen_om_of_isSemiAbelian C L T hG hM).2
  obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_norms_of_tests hE C L T hT hB
  have h6 : L.CompanionTheory (T.Om L) := GlobalTheory.T.companionTheory_om_of_tests_torsionSections hE C L T n hT hB hTors hFew
  have hγ := GlobalTheory.ZJ.Core.exists_gen_normOne C L T (T.Om L) ν hO hν h6
  obtain ⟨-, hlft, -, hint, hflat, -, hop, -⟩ := core_basic C
  have := C.lft
  have hsm : Smooth C.GG.hom := by
    have := L.smooth
    exact SmoothOfRelativeDimension.smooth C.g _
  have hN : Geo.Tor.IsNormalScheme C.G.toScheme := fun x =>
    GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth C.GG.hom C.normal x
  have hlft' : LocallyOfFiniteType (C.GG.hom ≫ C.π) := inferInstance
  exact GlobalTheory.T.exists_local_section_ne_zero_on_fibres' C L T (T.Om L) ν hO hν h6
    (@GlobalTheory.exists_lineBundle_of_normOne_generators C.G.toScheme C.A.left hint (C.GG.hom ≫ C.π) hflat hlft' hN C.a hop T.L.L T.L.isLB ν hν.isNrm hγ)

end GlobalTheory.ZJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPointIndependenceSpreadToGeometricFibresStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pointIndependence_spread_to_geometricFibres : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ G.left), IsSeparated G.hom → IsGrpPullback A G (spMap (algebraMap R K)) φ → ∀ (n k : ℕ) (y : Fin n → (baseOver (Sp R) ⟶ G)) (y₀ : Fin n → (baseOver (Sp K) ⟶ A)), (∀ i, (y₀ i).left ≫ φ = spMap (algebraMap R K) ≫ (y i).left) → (∀ c c' : Fin n → Fin k, linComb y₀ (fun i => (c i : ℕ)) = linComb y₀ (fun i => (c' i : ℕ)) → c = c') → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] (π : G'.left ⟶ G.left) (y' : Fin n → (baseOver (Sp R') ⟶ G')), IsGrpPullback G' G (spMap g) π → (∀ i, (y' i).left ≫ π = spMap g ≫ (y i).left) → ∀ (F : Type) [Field F] [IsAlgClosed F] (s : Spec (CommRingCat.of F) ⟶ Sp R') (c c' : Fin n → Fin k), linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R')) ≫ y' i) (fun i => (c i : ℕ)) = linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R')) ≫ y' i) (fun i => (c' i : ℕ)) → c = c' := by
  first | exact @GlobalTheory.GenSpread.exists_forall_linComb_injective | exact GlobalTheory.GenSpread.exists_forall_linComb_injective | (intros; apply GlobalTheory.GenSpread.exists_forall_linComb_injective <;> assumption)
end

