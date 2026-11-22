import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenCubicalTrivialisationLiftNilpotent
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralFamiliesSpanPullDegeneration
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorusQuotientSchemeOverNilpotentThickening
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThickTorusLevelWeightExpansion

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitMemRangeJKOfMemRangeJ
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace ArcNotAbelian

theorem isProper_fibre {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (K : Type) [Field K]
    (t : Spec (CommRingCat.of K) ⟶ S) (p : Spec (CommRingCat.of K)) (hp : t p ∈ abLocus G) :
    IsProper (pullback.snd G.hom t) := by
  let K' := AlgebraicClosure K
  let u : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K) := Spec.map (CommRingCat.ofHom (algebraMap K K'))
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have q : Spec (CommRingCat.of K') := (default : PrimeSpectrum K')
  have : Nonempty (Spec (CommRingCat.of K')) := ⟨q⟩
  have h₁ : IsProper (pullback.snd G.hom (u ≫ t)) :=
    hp K' (u ≫ t) ⟨q, congrArg (fun z => t z) (Subsingleton.elim (u q) p)⟩
  have P := (IsPullback.of_hasPullback (pullback.snd G.hom t) u).paste_horiz (IsPullback.of_hasPullback G.hom t)
  have h₂ : UniversallyClosed (pullback.snd (pullback.snd G.hom t) u) := by
    rw [← P.isoPullback_hom_snd]; infer_instance
  have hu : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) u :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have : UniversallyClosed (pullback.snd G.hom t) :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed) hu h₂
  have := hG.separated
  have := hG.smooth
  exact ⟨⟩

open TorusToProper in

theorem subsingleton_of_mono (K : Type) [Field K] (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Spec (CommRingCat.of K))) [GrpObj B]
    [IsProper B.hom] (f : splitTorus (Spec (CommRingCat.of K)) X ⟶ B) (hf : IsMonHom f) [Mono f] :
    Subsingleton X := by
  have h := splitTorus_hom_proper_trivial_field K X B f hf
  have e : ptFun K X (AddMonoidAlgebra K X) (univ K X) = ptFun K X (AddMonoidAlgebra K X) 1 := by
    rw [← cancel_mono f, h, ← Category.assoc, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _
  have e₂ := (ptFun_fst K X _ (univ K X)).symm.trans
    ((congrArg (fun z => z.left ≫ Rosenlicht.torusFst _ X) e).trans (ptFun_fst K X _ 1))
  have e₃ : charRing X _ (univ K X) = charRing X (AddMonoidAlgebra K X) 1 :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective e₂)
  have key : ∀ a : X, (AddMonoidAlgebra.single a 1 : AddMonoidAlgebra K X) = 1 := by
    intro a
    have := congrArg (fun φ => φ (AddMonoidAlgebra.single a 1)) e₃
    simp only [charRing_single] at this
    simpa [univ] using this
  exact ⟨fun a b => AddMonoidAlgebra.single_left_injective (one_ne_zero (α := K)) ((key a).trans (key b).symm)⟩

theorem subsingleton_of_mem_abLocus {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G)
    (A : Type) [CommRing A] (hA : IsField A) (t : Spec (CommRingCat.of A) ⟶ S) (p : Spec (CommRingCat.of A))
    (hp : t p ∈ abLocus G) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ (Over.pullback t).obj G) (hf : IsMonHom f) [Mono f] :
    Subsingleton X := by
  letI := hA.toField
  have : IsProper ((Over.pullback t).obj G).hom := isProper_fibre G hG A t p hp
  exact subsingleton_of_mono A X _ f hf

end ArcNotAbelian

open ArcNotAbelian in

theorem arcWit_mem_range_jK_of_mem_range_j : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (χ : Sp (PowerSeries k) ⟶ Y.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (x : Sp (PowerSeries k)), χ x ∈ Set.range Y.j → x ∈ Set.range (jK (PowerSeries k)) := by
  intro E _ _ _ H D l Xo c k _ bF a O _ β Y χ W x hx
  refine mem_range_jK x fun hX => ?_
  have h₁ : χ x ∈ abLocus Y.t.G := by
    obtain ⟨p, hp⟩ := hx
    have hz : Y.jQ p ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨_, rfl⟩
    rw [← hp]
    exact hz
  have h₂ : x ∈ abLocus W.t.G := (abLocus_pullback abLocusOne Y.t.semi W.m.cart.1 x).1 h₁
  have hmax : (Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one, ← PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  have hF : IsField (PowerSeries k ⧸ Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (0 + 1)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have hle : Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (0 + 1) ≤ x.asIdeal := by
    rw [zero_add, pow_one, Ideal.span_le, Set.singleton_subset_iff]; exact hX
  obtain ⟨p, hp⟩ : x ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries k)} ^ (0 + 1)))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact hle
  let g := W.P.U.gt 0
  have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hp' : thick (PowerSeries k) (Ideal.span {PowerSeries.X}) 0 p ∈ abLocus W.t.G := by
    rw [← hp] at h₂; exact h₂
  have hs := subsingleton_of_mem_abLocus W.t.G W.t.semi _ hF _ p hp' W.P.D.toPre.X g.i g.i_hom
  have hn : Nontrivial (a.restrict β).D₀.X := (a.restrict β).nontriv
  exact not_subsingleton _ (W.e.toEquiv.subsingleton)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BijectiveOfIso
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.GenericFibreSections

variable {X₁ X₂ Y Y' : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂}

theorem exists_transfer (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (φ₁ : Y ⟶ X₁) (φ₂ : Y ⟶ X₂) (k : ℤ)
    (V : L₁.ι → L₂.ι → Y.Opens) (hV : ∀ i j y, φ₁ y ∈ L₁.U i → φ₂ y ∈ L₂.U j → y ∈ V i j)
    (u : ∀ i j, Γ(Y, V i j)ˣ)
    (hu : ∀ (y : Y) i i' j j', φ₁ y ∈ L₁.U i → φ₁ y ∈ L₁.U i' → φ₂ y ∈ L₂.U j → φ₂ y ∈ L₂.U j' →
      gm (𝟙 Y) y _ (u i j) * gm (𝟙 Y ≫ φ₁) y _ (L₁.g i i') ^ k =
        gm (𝟙 Y ≫ φ₂) y _ (L₂.g j j') ^ k * gm (𝟙 Y) y _ (u i' j'))
    (s : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => φ₁) (fun _ => k))) :
    ∃ s' : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => φ₂) (fun _ => k)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J₁ J₂, Good L₁ z J₁ → Good L₂ z J₂ →
        sval s' r z J₂ = (gm r z _ (u (J₁ (r ≫ φ₁)) (J₂ (r ≫ φ₂)))).val * sval s r z J₁ := by
  have glue : ∀ j : Fin 1 → L₂.ι, ∃ a : Γ(Y, LB.wchart L₂ (fun _ : Fin 1 => φ₂) j),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (i : L₁.ι),
      r z ∈ LB.wchart L₂ (fun _ : Fin 1 => φ₂) j → φ₁ (r z) ∈ L₁.U i →
      gs r z _ a = (gm r z _ (u i (j 0))).val *
        gs r z (LB.wchart L₁ (fun _ : Fin 1 => φ₁) (fun _ => i)) (s.f (fun _ => i)) := by
    intro j
    let W : L₁.ι → Y.Opens := fun i =>
      LB.wchart L₂ (fun _ : Fin 1 => φ₂) j ⊓ LB.wchart L₁ (fun _ : Fin 1 => φ₁) (fun _ => i)
    have l : ∀ i, W i ≤ V i (j 0) := fun i y hy =>
      hV i (j 0) y (Set.mem_iInter.1 hy.2 0) (Set.mem_iInter.1 hy.1 0)
    obtain ⟨b, hb⟩ : ∃ b : ∀ i, Γ(Y, W i), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) i, r z ∈ W i →
        gs r z (W i) (b i) = (gm r z _ (u i (j 0))).val *
          gs r z (LB.wchart L₁ (fun _ : Fin 1 => φ₁) (fun _ => i)) (s.f (fun _ => i)) :=
      ⟨fun i => (Y.presheaf.map (homOfLE (l i)).op).hom (u i (j 0)).val *
          (Y.presheaf.map (homOfLE (inf_le_right : W i ≤ LB.wchart L₁ (fun _ : Fin 1 => φ₁) (fun _ => i))).op).hom
            (s.f (fun _ => i)), fun Z r z i hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res r z _ hz _).trans (gs_unit r z _ (l i hz) _))
          (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' W (LB.wchart L₂ (fun _ : Fin 1 => φ₂) j)
      (fun i => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨i, hi⟩ := exists_chart hL₁ (φ₁ y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hy, Set.mem_iInter.2 fun _ => hi⟩) b
      (fun i i' => fn_ext (V := W i ⊓ W i') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        have m : φ₂ y ∈ L₂.U (j 0) := Set.mem_iInter.1 hy.1.1 0
        have e := hu y i i' (j 0) (j 0) (Set.mem_iInter.1 hy.1.2 0) (Set.mem_iInter.1 hy.2.2 0) m m
        rw [gm_self hL₂ (𝟙 Y ≫ φ₂) y m, _root_.one_zpow, _root_.one_mul] at e
        rw [hb _ _ y i hy.1, hb _ _ y i' hy.2, sec_trans s (𝟙 Y) y hy.1.2 hy.2.2, ← _root_.mul_assoc, ← Units.val_mul,
          ← e, trF, Fintype.prod_unique])
    refine ⟨a, fun Z r z i h₁ h₂ => ?_⟩
    have hz : r z ∈ W i := ⟨h₁, Set.mem_iInter.2 fun _ => h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z (W i)) (ha i)).trans (hb Z r z i hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  · obtain ⟨i, hi⟩ := exists_chart hL₁ (φ₁ y)
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L₂ _ _ (𝟙 Y) y j j' hy.1 hy.2)))
      (gs_res (𝟙 Y) y _ hy _))).symm)
    refine (ha j _ (𝟙 Y) y i hy.1 hi).trans (Eq.trans ?_ (congrArg _ (ha j' _ (𝟙 Y) y i hy.2 hi)).symm)
    have e := hu y i i (j 0) (j' 0) hi hi (Set.mem_iInter.1 hy.1 0) (Set.mem_iInter.1 hy.2 0)
    rw [gm_self hL₁ (𝟙 Y ≫ φ₁) y hi, _root_.one_zpow, _root_.mul_one] at e
    rw [e, Fintype.prod_unique, Units.val_mul, _root_.mul_assoc]
    rfl
  · exact ha _ Z r z (J₁ (r ≫ φ₁)) (hJ₂.mem (fun _ : Fin 1 => φ₂) r) (hJ₁ (r ≫ φ₁))

theorem exists_pull (h : Y' ⟶ Y) (φ : Y ⟶ X₁) (φ' : Y' ⟶ X₁) (e : φ' = h ≫ φ) (k : ℤ)
    (s : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => φ) (fun _ => k))) :
    ∃ s' : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => φ') (fun _ => k)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J, Good L₁ z J → sval s' r z J = sval s (r ≫ h) z J := by
  subst e
  exact ⟨_, fun Z r z J hJ => H1.SectionArithmetic.sval_pullSec s h r z hJ⟩

theorem sec_ext {M : LB Y} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  obtain ⟨f, _⟩ := s
  obtain ⟨f', _⟩ := s'
  obtain rfl : f = f' := funext h
  rfl

theorem gw_trans {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} (hw : w.IsGen) (y : Y)
    {i i' : L₁.ι} {j j' : L₂.ι} (hi : f₁ y ∈ L₁.U i) (hi' : f₁ y ∈ L₁.U i') (hj : f₂ y ∈ L₂.U j) (hj' : f₂ y ∈ L₂.U j') :
    gw w (𝟙 Y) y j (fun _ => i) * gm (𝟙 Y ≫ f₁) y _ (L₁.g i i') =
      gm (𝟙 Y ≫ f₂) y _ (L₂.g j j') * gw w (𝟙 Y) y j' (fun _ => i') := by
  have e := (isGen_iff w).1 hw Y (𝟙 Y) y j j' (fun _ => i) (fun _ => i') hj hj' (mem_pull.2 hi) (mem_pull.2 hi')
  rw [gm_pull_g L₁ f₁ (𝟙 Y) y _ _ (mem_pull.2 hi) (mem_pull.2 hi')] at e
  rw [e, _root_.mul_right_comm, inv_mul_cancel_right]

theorem bijective_of_iso (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (p : Y' ⟶ X₁) [IsIso f₁] [IsIso p]
    (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w.IsGen) (k : ℕ)
    (Rel : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))) →
      LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => p) (fun _ => (k : ℤ))) → Prop)
    (hRel : ∀ σ t, Rel σ t ↔ ∀ (Z : Scheme.{0}) (rA : Z ⟶ Y') (y : Z ⟶ Y), rA ≫ p = y ≫ f₁ → ∀ (z : Z) J₁ J₂,
      Good L₁ z J₁ → Good L₂ z J₂ →
      (gw w y z (J₂ (y ≫ f₂)) (fun _ => J₁ (y ≫ f₁))).val ^ k * sval t rA z J₁ = sval σ y z J₂) :
    (∀ σ, ∃! t, Rel σ t) ∧ ∀ t, ∃! σ, Rel σ t := by
  have hV : ∀ i j (y : Y), f₁ y ∈ L₁.U i → f₂ y ∈ L₂.U j →
      y ∈ (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i) := fun i j y hi hj => ⟨mem_pull.2 hj, mem_pull.2 hi⟩
  refine ⟨fun σ => ?_, fun t => ?_⟩
  · obtain ⟨s, hs⟩ := exists_transfer hL₂ hL₁ f₂ f₁ k
      (fun j i => (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i)) (fun j i y hj hi => hV i j y hi hj)
      (fun j i => ((show Γ(Y, (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i))ˣ from
        w.s (fun _ => j, fun _ => i)) ^ k)⁻¹) (fun y j j' i i' hj hj' hi hi' => by
        have e := gw_trans hw y hi hi' hj hj'
        rw [map_inv, map_inv, map_pow, map_pow, zpow_natCast, zpow_natCast]
        change (gw w (𝟙 Y) y j (fun _ => i) ^ k)⁻¹ * _ = _ * (gw w (𝟙 Y) y j' (fun _ => i') ^ k)⁻¹
        rw [inv_mul_eq_iff_eq_mul, ← _root_.mul_assoc, ← mul_pow, e, mul_pow, mul_inv_cancel_right]) σ
    obtain ⟨t, ht⟩ := exists_pull (p ≫ inv f₁) f₁ p (by simp) k s
    refine ⟨t, (hRel _ _).2 fun Z rA y e z J₁ J₂ h₁ h₂ => ?_, fun t' H' => ?_⟩
    · have e' : rA ≫ p ≫ inv f₁ = y := by rw [← Category.assoc, e]; simp
      rw [ht Z rA z J₁ h₁, e', hs Z y z J₂ J₁ h₂ h₁, map_inv, map_pow, ← Units.val_pow_eq_pow_val]
      exact Units.mul_inv_cancel_left _ _
    · refine sec_ext (sec_ext_val hL₁ fun y J₁ h₁ => ?_)
      choose J₂ h₂ using fun χ : Y' ⟶ X₂ => exists_chart hL₂ (χ y)
      have e := (hRel _ _).1 H' Y' (𝟙 _) (p ≫ inv f₁) (by simp) y J₁ J₂ h₁ h₂
      rw [ht _ _ y J₁ h₁, Category.id_comp, hs _ _ y J₂ J₁ h₂ h₁, map_inv, map_pow, ← e, ← Units.val_pow_eq_pow_val]
      exact (Units.inv_mul_cancel_left _ _).symm
  · obtain ⟨s, hs⟩ := exists_pull (f₁ ≫ inv p) p f₁ (by simp) k t
    obtain ⟨σ, hσ⟩ := exists_transfer hL₁ hL₂ f₁ f₂ k
      (fun i j => (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i)) hV
      (fun i j => (show Γ(Y, (L₂.pull f₂).U (fun _ => j) ⊓ (L₁.pull f₁).U (fun _ => i))ˣ from
        w.s (fun _ => j, fun _ => i)) ^ k) (fun y i i' j j' hi hi' hj hj' => by
        have e := gw_trans hw y hi hi' hj hj'
        rw [map_pow, map_pow, zpow_natCast, zpow_natCast, ← mul_pow, ← mul_pow]
        exact congrArg (· ^ k) e) s
    refine ⟨σ, (hRel _ _).2 fun Z rA y e z J₁ J₂ h₁ h₂ => ?_, fun σ' H' => ?_⟩
    · have e' : y ≫ f₁ ≫ inv p = rA := by rw [← Category.assoc, ← e]; simp
      rw [hσ Z y z J₁ J₂ h₁ h₂, hs Z y z J₁ h₁, e', map_pow, Units.val_pow_eq_pow_val]
      rfl
    · refine sec_ext (sec_ext_val hL₂ fun y J₂ h₂ => ?_)
      choose J₁ h₁ using fun χ : Y ⟶ X₁ => exists_chart hL₁ (χ y)
      have e := (hRel _ _).1 H' Y (𝟙 Y ≫ f₁ ≫ inv p) (𝟙 _) (by simp) y J₁ J₂ h₁ h₂
      rw [← e, hσ _ _ y J₁ J₂ h₁ h₂, hs _ _ y J₁ h₁, map_pow, Units.val_pow_eq_pow_val]
      rfl

theorem sameK_bijective : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (k : ℕ), (∀ σ, ∃! t, U.SameK (k := k) σ t) ∧ ∀ t, ∃! σ, U.SameK (k := k) σ t := by
  intro R _ _ I D A G _ _ U k
  have h₀ : IsIso (TFK (R := R) (FractionRing R)).hom := by
    show IsIso (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) (FractionRing R))))
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    infer_instance
  have h₁ : IsIso (snd (TFK (R := R) (FractionRing R)) A.A).left :=
    inferInstanceAs (IsIso (pullback.snd (TFK (R := R) (FractionRing R)).hom A.A.hom))
  have h₂ : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
  exact bijective_of_iso A.isLB U.P.L.isLB U.gen.hom.left (pullback.fst G.hom (jK R))
    (snd (TFK (R := R) (FractionRing R)) A.A).left U.wA U.wA_gen k (fun σ t => U.SameK (k := k) σ t)
    (fun _ _ => Iff.rfl)

end GlobalTheory.GenericFibreSections
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionOverZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.GtCount

open GlobalTheory.TorusExt

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.GtCount.card_torsion_eq_mul {G B : Type} [AddCommGroup G] [AddCommGroup B] (p : G →+ B) (n : ℕ)
    (h : ∀ b : B, n • b = 0 → ∃ g, p g = b ∧ n • g = 0) :
    Nat.card {g : G // n • g = 0} = Nat.card {b : B // n • b = 0} * Nat.card {g : G // n • g = 0 ∧ p g = 0} := by
  have h' : ∀ b : {b : B // n • b = 0}, ∃ g, p g = b ∧ n • g = 0 := fun b => h b b.2
  choose s hs using h'
  have hp : ∀ g : {g : G // n • g = 0}, n • p g = 0 := fun g => by
    rw [← map_nsmul, g.2, map_zero]
  have hsec : ∀ (b b' : {b : B // n • b = 0}), (b : B) = b' → s b = s b' := by
    rintro b b' hbb
    rw [Subtype.ext hbb]
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun g => (⟨p g, hp g⟩, ⟨g - s ⟨p g, hp g⟩, ?_, ?_⟩)
      invFun := fun x => ⟨s x.1 + x.2.1, by rw [nsmul_add, (hs _).2, x.2.2.1, add_zero]⟩
      left_inv := fun g => Subtype.ext (add_sub_cancel _ _)
      right_inv := fun x => ?_ }
  · rw [nsmul_sub, g.2, (hs _).2, sub_zero]
  · rw [map_sub, (hs _).1, sub_self]
  · have hx : p (s x.1 + x.2.1) = x.1 := by rw [map_add, (hs _).1, x.2.2.2, add_zero]
    refine Prod.ext (Subtype.ext hx) (Subtype.ext ?_)
    change s x.1 + x.2.1 - s ⟨p (s x.1 + x.2.1), _⟩ = x.2.1
    rw [hsec ⟨p (s x.1 + x.2.1), _⟩ x.1 hx, add_sub_cancel_left]

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.GtCount.card_torus_torsion (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (F : Type) [Field F]
    [IsAlgClosed F] (n : ℕ) (hn : (n : F) ≠ 0) :
    Nat.card {t : Multiplicative X →* Fˣ // t ^ n = 1} = n ^ Module.finrank ℤ X := by
  haveI : NeZero (n : F) := ⟨hn⟩
  haveI : NeZero n := ⟨by rintro rfl; simp at hn⟩
  have hroots : Nat.card (rootsOfUnity n F) = n := by
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F n
    exact hζ.card_rootsOfUnity
  let b := Module.Free.chooseBasis ℤ X
  let e₁ : {t : Multiplicative X →* Fˣ // t ^ n = 1} ≃ (Multiplicative X →* rootsOfUnity n F) :=
    { toFun := fun t => (t.1).codRestrict (rootsOfUnity n F) fun x => by
        have := DFunLike.congr_fun t.2 x
        simpa [MonoidHom.pow_apply, mem_rootsOfUnity] using this
      invFun := fun s => ⟨(rootsOfUnity n F).subtype.comp s, by
        refine MonoidHom.ext fun x => ?_
        simpa [MonoidHom.pow_apply] using (mem_rootsOfUnity _ _).1 (s x).2⟩
      left_inv := fun t => Subtype.ext (MonoidHom.ext fun x => rfl)
      right_inv := fun s => MonoidHom.ext fun x => Subtype.ext rfl }
  let e := e₁.trans (MonoidHom.toAdditiveRight.trans
    ((addMonoidHomLequivInt ℤ).toEquiv.trans (b.constr ℤ).symm.toEquiv))
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_congr Additive.toMul, hroots,
    Module.finrank_eq_card_chooseBasisIndex, Nat.card_eq_fintype_card]

attribute [local instance] gtGroup

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
attribute [local instance] _root_.GlobalTheory.TorusExt.gtGroup in
theorem _root_.GlobalTheory.GtCount.gtTors_iff {R : Type} [CommRing R] [IsDomain R] {D : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (n : ℕ) (g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F) : _root_.GlobalTheory.UU.GtTors D n g ↔ n • g = 0 := by
  unfold _root_.GlobalTheory.UU.GtTors
  simp [_root_.GlobalTheory.TorusExt.isNsmul_iff_eq, _root_.GlobalTheory.TorusExt.isZero_iff_eq]

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
attribute [local instance] _root_.GlobalTheory.TorusExt.gtGroup in

theorem _root_.GlobalTheory.GtCount.card_torsion_over_zero {R : Type} [CommRing R] [IsDomain R] (D : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre R) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] (n : ℕ) (hn : (n : F) ≠ 0) :
    Nat.card {g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F // n • g = 0 ∧ g.b = 1} = n ^ D.rank := by
  let φ := _root_.GlobalTheory.TorusExt.torusPt D F
  have hinj : Function.Injective φ := _root_.GlobalTheory.TorusExt.torusPt_injective
  let e : {t : Multiplicative D.X →* Fˣ // t ^ n = 1} → {g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F // n • g = 0 ∧ g.b = 1} :=
    fun t => ⟨φ (Additive.ofMul t.1), by
      rw [← map_nsmul, ← ofMul_pow, t.2, ofMul_one, map_zero], _root_.GlobalTheory.TorusExt.torusPt_b _⟩
  have he : Function.Bijective e := by
    refine ⟨fun t t' htt => Subtype.ext ?_, fun g => ?_⟩
    · exact Additive.ofMul.injective (hinj (congrArg Subtype.val htt))
    · obtain ⟨t, ht⟩ := _root_.GlobalTheory.TorusExt.exists_torusPt_eq g.2.2
      refine ⟨⟨t, ?_⟩, Subtype.ext ht.symm⟩
      apply Additive.ofMul.injective
      apply hinj
      rw [ofMul_pow, map_nsmul, ← ht, g.2.1, ofMul_one, map_zero]
  rw [← Nat.card_congr (Equiv.ofBijective e he), _root_.GlobalTheory.GtCount.card_torus_torsion D.X F n hn]

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
attribute [local instance] _root_.GlobalTheory.TorusExt.gtGroup in

theorem _root_.GlobalTheory.GtCount.card_gtTors : _root_.ReciprocityTheory.ChartRestriction.G.Out.Laws → _root_.ReciprocityTheory.ChartRestriction.G.Out.Laws2 → (∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), (N : F) ≠ 0 → Nat.card {g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F // _root_.GlobalTheory.UU.GtTors D N g} = N ^ (2 * D.P.g + D.rank) ∧ Nat.card {g : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F // _root_.GlobalTheory.UU.GtTors D N g ∧ g.b = _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre.zeroF D F} = N ^ D.rank) := by
  intro hL _ R _ _ _ D F _ _ _ N hN
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have hz : _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre.zeroF D F = 1 := by unfold _root_.ReciprocityTheory.ChartRestriction.G.Out.DegPre.zeroF; rfl
  have h0 : (0 : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F).b = 1 := by
    simpa using _root_.GlobalTheory.TorusExt.nsmul_b 0 (0 : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F)
  let p : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F →+ Additive (_root_.ReciprocityTheory.ChartRestriction.G.Out.TF F ⟶ D.P.A) :=
    { toFun := fun g => Additive.ofMul g.b
      map_zero' := by rw [h0]; rfl
      map_add' := fun g g' => by rw [_root_.GlobalTheory.TorusExt.add_b]; rfl }
  have hsurj : ∀ b : Additive (_root_.ReciprocityTheory.ChartRestriction.G.Out.TF F ⟶ D.P.A), N • b = 0 → ∃ g, p g = b ∧ N • g = 0 := by
    intro b hb
    obtain ⟨g, hgb, hg⟩ := _root_.GlobalTheory.TorusExt.exists_nsmul_eq_of_pow_eq hN0 (0 : _root_.ReciprocityTheory.ChartRestriction.G.Out.GtPtF D F) (b := Additive.toMul b)
      (by rw [h0]; exact hb)
    exact ⟨g, by simp [p, hgb], hg⟩
  have hB : Nat.card {b : Additive (_root_.ReciprocityTheory.ChartRestriction.G.Out.TF F ⟶ D.P.A) // N • b = 0} = N ^ (2 * D.P.g) := by
    have := (hL.mulN (Spec (CommRingCat.of R)) D.P N (Nat.one_le_iff_ne_zero.2 hN0)).2.2.2.2 F
      (_root_.ReciprocityTheory.ChartRestriction.G.Out.TF F).hom hN
    rw [← this]
    exact Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun b => Iff.rfl)
  simp only [_root_.GlobalTheory.GtCount.gtTors_iff, hz]
  refine ⟨?_, _root_.GlobalTheory.GtCount.card_torsion_over_zero D F N hN⟩
  rw [_root_.GlobalTheory.GtCount.card_torsion_eq_mul p N hsurj, hB, pow_add]
  congr 1
  rw [← _root_.GlobalTheory.GtCount.card_torsion_over_zero D F N hN]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp [p])

end GlobalTheory.GtCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenCubicalTrivialisationLiftNilpotentStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_even_cubicalTrivialisation_lift_nilpotent : (∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A), IsNilpotent J → J ≠ ⊤ → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] [IsCommMonObj G₀] (F : G₀.left ⟶ G.left) (hw), IsGrpPullback G₀ G (red J) F → ∀ (P : CP G) (P₀ : CP G₀) (w), IsCPMap P₀ P (red J) F hw w → ∀ (i : splitTorus _ X ⟶ G) (i₀ : splitTorus _ X ⟶ G₀), IsMonHom i → IsMonHom i₀ → TorusCompat (red J) F i₀ i → Nonempty (BiTriv P.c i) → (∃ σ₀ : CubTriv P₀.c i₀, σ₀.Even) → ∃ σ : CubTriv P.c i, σ.Even) := by
  first | exact @GlobalTheory.CubeLift.exists_even_cubTriv | exact GlobalTheory.CubeLift.exists_even_cubTriv | (intros; apply GlobalTheory.CubeLift.exists_even_cubTriv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGtPtOfCharacter
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU
attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem exists_gtPt_of_character : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (χ₀ : Multiplicative D.X →* Fˣ), ∃ g : GtPtF D F, g.b = DegPre.zeroF D F ∧ (∀ α z J, Good D.P.L z J → (val (g.s α) (𝟙 _) z J).val = gs (𝟙 _) z ⊤ (scal (𝟙 (Spec (CommRingCat.of F))) (χ₀ (Multiplicative.ofAdd α)).val)) ∧ (∀ N : ℕ, χ₀ ^ N = 1 → GtTors D N g) ∧ (g.IsZero ↔ χ₀ = 1) := by
  intro R _ _ D F _ _ χ₀
  refine ⟨TorusExt.torusPt D F (Additive.ofMul χ₀), TorusExt.torusPt_b _, fun α z J hJ => ?_, fun N hN => ?_, ?_⟩
  · refine (congrArg Units.val (TorusExt.torusPt_val χ₀ α hJ)).trans ?_
    exact (gs_eq (𝟙 _) z ⊤ trivial _).symm
  · refine ⟨_, (TorusExt.isNsmul_iff_eq N _ _).2 rfl, (TorusExt.isZero_iff_eq _).2 ?_⟩
    rw [← map_nsmul, ← ofMul_pow, hN, ofMul_one, map_zero]
  · rw [TorusExt.isZero_iff_eq, map_eq_zero_iff _ TorusExt.torusPt_injective]
    exact ofMul_eq_zero
end GlobalTheory.UU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralFamiliesSpanPullDegenerationStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_integral_families_span_pullDegeneration : PolBaseChangeSt → GlobalFnsSt → DVR.TwistBaseChangeStatement → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R), AdmBase R I → ∀ (φ : R →+* R') (D : DegData R I) (D' : DegPre R') (hD : IsPullDeg φ D.toPre D') (k : ℕ), 1 ≤ k → ∃ (n : ℕ) (F : Fin n → Fam D.toPre (FractionRing R) k) (f : Fin n → ∀ α, D.toPre.SecB k α) (F' : Fin n → Fam D' (FractionRing R') k) (f' : Fin n → ∀ α, D'.SecB k α), (∀ i, (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) ((F i).s α) (D.toPre.famφB α) (DegPre.famε k) (f i α) (DegPre.prB D.toPre (FractionRing R)).left 1) ∧ (∀ α, GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' (FractionRing R') α) (DegPre.famε k) ((F' i).s α) (D'.famφB α) (DegPre.famε k) (f' i α) (DegPre.prB D' (FractionRing R')).left 1) ∧ (∀ x : D'.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q : Fin 4 → D'.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((D'.famφB x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (D'.famφB x) κ (r z) ∈ D'.P.L.U (q κ)) → Geo.Tor.gs (r ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) z (LB.wchart D.toPre.P.L (D.toPre.famφB (hD.xe x)) p) ((f i (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (D'.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.P.L (D'.famφB x) q) ((f' i x).f q)))) ∧ Submodule.span (FractionRing R') (Set.range F') = ⊤ := by
  first | exact @GlobalTheory.FamSpan.exists_span | exact GlobalTheory.FamSpan.exists_span | (intros; apply GlobalTheory.FamSpan.exists_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorusQuotientSchemeOverNilpotentThickeningStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.exists_torus_quotient_scheme_over_nilpotent_thickening : (∀ (A : Type) [CommRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] (F : G₀.left ⟶ G.left), IsGrpPullback G₀ G (red J) F → ∀ (Q₀ : TQ G₀ X) (i : splitTorus _ X ⟶ G), IsMonHom i → TorusCompat (red J) F Q₀.i i → ∃ (B : Over (Spec (CommRingCat.of A))) (q : G ⟶ B) (j : Q₀.B.left ⟶ B.left), IsPullback j Q₀.B.hom B.hom (red J) ∧ Q₀.q.left ≫ j = F ≫ q.left ∧ IsAffineHom q.left ∧ ∀ b : B.left, ∃ V : B.left.Opens, b ∈ V ∧ IsAffineOpen V ∧ (∀ a : Γ(G.left, q.left ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.left.app V).hom c = a) ∧ Function.Injective (q.left.app V).hom ∧ (snd (splitTorus _ X) G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) ∧ ∃ u : Multiplicative X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ, ∀ χ, IsWt i _ (u (Multiplicative.ofAdd χ)).val χ) := by
  first | exact @GlobalTheory.TorusQuotientLift.exists_quotient_scheme | exact GlobalTheory.TorusQuotientLift.exists_quotient_scheme | (intros; apply GlobalTheory.TorusQuotientLift.exists_quotient_scheme <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThickTorusLevelWeightExpansionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
theorem _root_.GlobalTheory.T.existsUnique_thickTorus_level_weight_expansion : (∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (k : ℕ) (σ : LB.Sec (LB.LinComb D.P.L (K := Fin 1) (fun _ => g.pG.left) (fun _ => (k : ℤ)))), ∃! f : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (fun i => (D.prBe I e).left ≫ D.famφB α i) (DegPre.famε k)), ∃ s : Finset D.X, (∀ α ∉ s, ∀ j, (f α).f j = 0) ∧ ∀ (z : (thickObj R I e G).left) (J), Good D.P.L z J → sval σ (𝟙 (thickObj R I e G).left) z J = ∑ α ∈ s, sval (f α) g.q.left z J * (val (g.t α) (𝟙 (thickObj R I e G).left) z J).val) := by
  first | exact @GlobalTheory.existsUnique_level_expansion | exact GlobalTheory.existsUnique_level_expansion | (intros; apply GlobalTheory.existsUnique_level_expansion <;> assumption)
end

