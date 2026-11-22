import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0008
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PureWeightSectionToTwistedPolarisationPower
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem spMap_factor_jK {V Ω : Type} [CommRing V] [IsDomain V] [Field Ω] (φ : V →+* Ω)
    (hi : Function.Injective φ) : ∃ r, spMap φ = r ≫ Out.jK V := by
  refine ⟨spMap (IsFractionRing.lift (K := FractionRing V) hi), ?_⟩
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact (IsFractionRing.lift_algebraMap hi x).symm

theorem range_comp_ι_subset {X Y : Scheme.{0}} (U : Y.Opens) (f : X ⟶ U.toScheme) :
    Set.range (f ≫ U.ι) ⊆ U := by
  rintro _ ⟨x, rfl⟩
  exact (f x).2

theorem field_point_factor_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (Ω : Type) [Field Ω] (q : Sp Ω ⟶ Sp V) :
    (∃ r, q = r ≫ spMap (IsLocalRing.residue V)) ∨ ∃ r, q = r ≫ Out.jK V := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective q
  by_cases h : RingHom.ker φ.hom = ⊥
  · exact Or.inr (spMap_factor_jK φ.hom ((RingHom.injective_iff_ker_eq_bot _).2 h))
  · have hp : (RingHom.ker φ.hom).IsPrime := RingHom.ker_isPrime _
    have hm : RingHom.ker φ.hom = IsLocalRing.maximalIdeal V :=
      IsLocalRing.eq_maximalIdeal (hp.isMaximal h)
    refine Or.inl ⟨spMap (Ideal.Quotient.lift (IsLocalRing.maximalIdeal V) φ.hom
      fun a ha => (RingHom.mem_ker).1 (hm ▸ ha)), ?_⟩
    rw [← Spec.map_comp]
    congr 1

theorem isSemiAbelian_of_fibres_dvr (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (H : Over (Sp V)) [GrpObj H] [hc : IsCommMonObj H] (hs : Smooth H.hom) (hsep : IsSeparated H.hom)
    (hq : QuasiCompact H.hom)
    (h₁ : IsSemiAbelian ((Over.pullback (spMap (IsLocalRing.residue V))).obj H))
    (h₂ : IsSemiAbelian ((Over.pullback (Out.jK V)).obj H)) : IsSemiAbelian H := by
  have key : ∀ (Ω : Type) [Field Ω] (q : Sp Ω ⟶ Sp V), ∃ (T : Scheme.{0}) (r : Sp Ω ⟶ T) (f : T ⟶ Sp V),
      q = r ≫ f ∧ IsSemiAbelian ((Over.pullback f).obj H) := by
    intro Ω _ q
    rcases field_point_factor_dvr V Ω q with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact ⟨_, r, _, hr, h₁⟩
    · exact ⟨_, r, _, hr, h₂⟩
  refine ⟨hc, hs, hsep, hq, ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ q => ?_⟩,
    fun Ω _ _ q => ?_⟩
  · obtain ⟨T, r, f, rfl, h⟩ := key K q
    have hg : GeometricallyConnected (pullback.snd H.hom f) := h.geomConnected
    rw [← (pullbackLeftPullbackSndIso H.hom f r).hom.homeomorph.connectedSpace_iff]
    exact pullback_of_geometrically hg.1 K r
  · obtain ⟨T, r, f, rfl, h⟩ := key Ω q
    obtain ⟨E⟩ := h.fibres Ω r
    have : IsMonHom (pullCompIso r f H).symm.hom := inferInstanceAs (IsMonHom (pullCompIso r f H).inv)
    exact ⟨torusExtOfIso (pullCompIso r f H).symm E⟩

namespace Core

variable (C : Core)

theorem isPullback_a : IsPullback C.a C.A.hom C.GG.hom C.U.ι := by
  have h : IsPullback C.a (𝟙 _) C.G.ι (C.a ≫ C.G.ι) := IsPullback.of_vert_isIso_mono ⟨by simp⟩
  simpa using h.paste_vert C.cart

theorem isOpenImmersion_a : IsOpenImmersion C.a :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) C.isPullback_a.flip inferInstance

theorem range_a : Set.range C.a = C.GG.hom ⁻¹' C.U := by
  have h := C.isPullback_a
  rw [← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    h.isoPullback.hom.surjective.range_comp, Scheme.Pullback.range_fst, Scheme.Opens.range_ι]

theorem isNoetherian_Z : IsNoetherian C.Z := by
  have := C.lft
  have := C.qc
  have : IsLocallyNoetherian C.Z := LocallyOfFiniteType.isLocallyNoetherian C.π
  have : CompactSpace C.Z := QuasiCompact.compactSpace_of_compactSpace C.π
  exact {}

theorem isNoetherian_P : IsNoetherian C.P.left := by
  have := C.isNoetherian_Z
  have := C.proper
  have : IsLocallyNoetherian C.P.left := LocallyOfFiniteType.isLocallyNoetherian C.P.hom
  have : CompactSpace C.P.left := QuasiCompact.compactSpace_of_compactSpace C.P.hom
  exact {}

theorem surjective_GG : Surjective C.GG.hom :=
  ⟨fun z => ⟨C.e z, by
    change (C.e ≫ C.G.ι ≫ C.P.hom) z = z
    rw [C.e_sec]; rfl⟩⟩

theorem nonempty_A : Nonempty C.A.left := by
  obtain ⟨z, hz⟩ := C.ne
  have := C.ab.geomConnected
  exact ⟨(C.A.hom.surjective ⟨z, hz⟩).choose⟩

theorem isIntegral_G : IsIntegral C.G.toScheme := by
  have : Nonempty C.G.toScheme := C.nonempty_A.map C.a
  exact isIntegral_of_isOpenImmersion C.G.ι

theorem flat_P : Flat (C.P.hom ≫ C.π) := by
  have := C.isNoetherian_P
  have := C.isOpenImmersion_a
  have := C.nonempty_A
  have := C.flat
  have := C.ab.smooth
  have : TopologicalSpace.NoetherianSpace C.A.left :=
    (C.a ≫ C.G.ι).isOpenEmbedding.isInducing.noetherianSpace
  have : IsDominant (C.a ≫ C.G.ι) :=
    ⟨(C.a ≫ C.G.ι).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have : IsSchemeTheoreticallyDominant (C.a ≫ C.G.ι) := .of_isDominant _
  have : Flat ((C.a ≫ C.G.ι) ≫ C.P.hom ≫ C.π) := by
    rw [← Category.assoc, C.cart.w]
    infer_instance
  exact flat_of_isSchemeTheoreticallyDominant
    (fun _ _ inst h => (@Module.Flat.flat_iff_torsion_eq_bot_of_isBezout ℤ _ _ _ inst.toModule _ _).mpr h)
    (C.a ≫ C.G.ι) _

variable {C} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)

include τ in

theorem Test.cl : C.Cl y := by
  have hi : Function.Injective ((OO p).subtype.comp τ.j) := (OO p).subtype_injective.comp τ.j_inj
  obtain ⟨r, hr⟩ := spMap_factor_jK _ hi
  have e : gPt p ≫ spMap τ.j = r ≫ Out.jK τ.V := (Spec.map_comp _ _).symm.trans hr
  have e' : gPt p ≫ y = (r ≫ τ.yK) ≫ C.U.ι := by
    rw [Category.assoc, τ.yK_fac, ← Category.assoc, ← e, Category.assoc, τ.fac]
  unfold Cl
  rw [e']
  exact range_comp_ι_subset _ _

theorem Test.charZero : CharZero τ.V :=
  RingHom.charZero ((OO p).subtype.comp τ.j)

theorem Test.isSemiAbelian : IsSemiAbelian τ.H := by
  obtain ⟨S, hS⟩ := τ.split
  have := τ.smooth
  have : IsCommMonObj ((Over.pullback (spMap (IsLocalRing.residue τ.V))).obj τ.H) := Functor.isCommMonObj_obj
  exact isSemiAbelian_of_fibres_dvr τ.V τ.H (SmoothOfRelativeDimension.smooth C.g _) τ.sep τ.qc
    (isSemiAbelian_of_isGt _ S _ hS)
    (isSemiAbelian_of_isAbelianScheme _ (PolPull.isAbelianScheme_of_isGrpPullback C.ab τ.φ_cart))

end Core

theorem core_basic : ∀ C : Core, IsSeparated C.GG.hom ∧ LocallyOfFiniteType C.GG.hom ∧ QuasiCompact C.GG.hom ∧ IsIntegral C.G.toScheme ∧ Flat (C.GG.hom ≫ C.π) ∧ Flat (C.P.hom ≫ C.π) ∧ IsOpenImmersion C.a ∧ IsPullback C.a C.A.hom C.GG.hom C.U.ι ∧ Set.range C.a = C.GG.hom ⁻¹' C.U ∧ IsNoetherian C.Z ∧ IsNoetherian C.P.left ∧ IsDominant C.GG.hom ∧ ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y), C.Cl y ∧ CharZero τ.V ∧ IsSemiAbelian τ.H := by
  intro C
  have := C.proper
  have := C.isNoetherian_P
  have := C.flat_P
  have := C.surjective_GG
  have : TopologicalSpace.NoetherianSpace C.G.toScheme := C.G.ι.isOpenEmbedding.isInducing.noetherianSpace
  refine ⟨inferInstanceAs (IsSeparated (C.G.ι ≫ C.P.hom)),
    inferInstanceAs (LocallyOfFiniteType (C.G.ι ≫ C.P.hom)),
    inferInstanceAs (QuasiCompact (C.G.ι ≫ C.P.hom)), C.isIntegral_G, ?_, C.flat_P, C.isOpenImmersion_a,
    C.isPullback_a, C.range_a, C.isNoetherian_Z, C.isNoetherian_P, inferInstance,
    fun p _ y τ => ⟨τ.cl, τ.charZero, τ.isSemiAbelian⟩⟩
  change Flat ((C.G.ι ≫ C.P.hom) ≫ C.π)
  rw [Category.assoc]
  infer_instance

end GlobalTheory.ZJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSectionsProportionalOfCoordinates
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.SecProp
open GlobalTheory.ZH.CrdCalc

section
variable {F : Type} [Field F] [IsAlgClosed F] {Y : Scheme.{0}} (p : Y ⟶ Sp F) [LocallyOfFiniteType p]

theorem exists_point {Z : Set Y} (hZ : IsLocallyClosed Z) (hn : Z.Nonempty) :
    ∃ r : Sp F ⟶ Y, r ≫ p = 𝟙 _ ∧ ∀ z, r z ∈ Z := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨c, hcW, hc⟩ := nonempty_inter_closedPoints hn hZ
  exact ⟨pointOfClosedPoint p c hc, pointOfClosedPoint_comp p c hc,
    fun z => (congrArg (· ∈ Z) (pointOfClosedPoint_apply p c hc z)).mpr hcW⟩

theorem fn_ext_valR [IsReduced Y] {U : Y.Opens} {a b : Γ(Y, U)}
    (h : ∀ r : Sp F ⟶ Y, r ≫ p = 𝟙 _ → ⊤ ≤ r ⁻¹ᵁ U → valR r U a = valR r U b) : a = b := by
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  by_contra hne
  have hn : ((Y.basicOpen (a - b) : Y.Opens) : Set Y).Nonempty :=
    Set.nonempty_iff_ne_empty.2 fun e => hne (SetLike.coe_injective e)
  obtain ⟨r, hr, hz⟩ := exists_point p (Y.basicOpen (a - b)).isOpen.isLocallyClosed hn
  have hU : ⊤ ≤ r ⁻¹ᵁ U := fun z _ => Y.basicOpen_le _ (hz z)
  have hu := (isUnit_valR_iff r U hU (a - b)).2 fun z _ => hz z
  have e := h r hr hU
  rw [valR_eq r U hU, valR_eq r U hU, ← sub_eq_zero, ← map_sub] at e
  rw [valR_eq r U hU, e] at hu
  exact not_isUnit_zero hu

variable {H : LB Y} {I : Type} {a b : I → H.Sec}

theorem exists_mem_basicOpen (h : ∀ r : Sp F ⟶ Y, r ≫ p = 𝟙 _ → ∃ w, w ≠ 0 ∧ Crd H b r w) (l : H.ι) (y : Y)
    (hy : y ∈ H.U l) : ∃ i, y ∈ Y.basicOpen ((b i).f l) := by
  by_contra hne
  let V : Y.Opens := ⨆ i, Y.basicOpen ((b i).f l)
  have hyV : y ∉ V := fun e => hne (TopologicalSpace.Opens.mem_iSup.1 e)
  obtain ⟨r, hr, hz⟩ := exists_point p
    ((H.U l).isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed) ⟨y, hy, hyV⟩
  obtain ⟨w, hw, hc⟩ := h r hr
  have hU : ⊤ ≤ r ⁻¹ᵁ H.U l := fun z _ => (hz z).1
  obtain ⟨c, hc'⟩ := crd_unique hc
    (⟨l, 1, hU, fun j => by simp⟩ : Crd H b r (fun i => valR r (H.U l) ((b i).f l)))
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
  have hu : IsUnit (valR r (H.U l) ((b i).f l)) := by
    rw [hc' i]
    exact c.isUnit.mul (Ne.isUnit hi)
  have z : Sp F := IsLocalRing.closedPoint F
  exact (hz z).2 (TopologicalSpace.Opens.mem_iSup.2 ⟨i, (isUnit_valR_iff r _ hU _).1 hu (Set.mem_univ z)⟩)

theorem cross_eq [IsReduced Y] (h : ∀ r : Sp F ⟶ Y, r ≫ p = 𝟙 _ → ∃ w, Crd H a r w ∧ Crd H b r w) (l : H.ι)
    (i i' : I) : (a i).f l * (b i').f l = (a i').f l * (b i).f l := by
  refine fn_ext_valR p fun r hr hU => ?_
  obtain ⟨w, ha, hb⟩ := h r hr
  obtain ⟨c, hc⟩ := crd_unique ha
    (⟨l, 1, hU, fun j => by simp⟩ : Crd H a r (fun i => valR r (H.U l) ((a i).f l)))
  obtain ⟨d, hd⟩ := crd_unique hb
    (⟨l, 1, hU, fun j => by simp⟩ : Crd H b r (fun i => valR r (H.U l) ((b i).f l)))
  rw [valR_mul r _ hU, valR_mul r _ hU, hc i, hc i', hd i, hd i']
  ring

end

theorem valR_const {F : Type} [Field F] {Y : Scheme.{0}} (p : Y ⟶ Sp F) (r : Sp F ⟶ Y) (hr : r ≫ p = 𝟙 _)
    (U : Y.Opens) (hU : ⊤ ≤ r ⁻¹ᵁ U) (a : F) :
    valR r U (resG Y le_top (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom a))) = a := by
  rw [valR_res r le_top hU, valR_eq r ⊤ le_rfl]
  have e : r.appLE ⊤ ⊤ le_rfl = r.appTop := (Scheme.Hom.app_eq_appLE r).symm
  have e₂ : p.appTop ≫ r.appTop = 𝟙 _ := by rw [← Scheme.Hom.comp_appTop, hr, Scheme.Hom.id_appTop]
  change (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom ((p.appTop ≫ r.appLE ⊤ ⊤ le_rfl).hom _) = a
  rw [e, e₂]
  exact (Scheme.ΓSpecIso (CommRingCat.of F)).inv_hom_id_apply a

theorem proportional_of_crd : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ) (I J : Type) [Fintype J] (t : I → SecA A F k) (s : J → SecA A F k) (b : Matrix I J F), (∀ x : TFK (R := R) F ⟶ A.A, ∃ v : J → F, b.mulVec v ≠ 0 ∧ Crd (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) s (show Sp F ⟶ _ from (ptSecT A.A x).left) v ∧ Crd (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) t (show Sp F ⟶ _ from (ptSecT A.A x).left) (b.mulVec v)) → ∃ c : F, ∀ i, ∑ j, kf R F (b i j) • SecM.ofSec A.A (s j) = kf R F c • SecM.ofSec A.A (t i) := by
  intro hG R _ _ A F _ _ _ k I J _ t s b H
  have hsm := A.isAb.smooth
  let T : Over (Spec (CommRingCat.of (FractionRing R))) := TFK (R := R) F
  let p : (T ⊗ A.A).left ⟶ Sp F := (fst T A.A).left
  have hp : Smooth p := inferInstanceAs (Smooth (pullback.fst T.hom A.A.hom))
  have : IsReduced (T ⊗ A.A).left := GlobalTheory.isReduced_of_smooth_of_isReduced p
  let m : I → SecM A.A A.L (k : ℤ) T := fun i => ∑ j, kf R F (b i j) • SecM.ofSec A.A (s j)
  let t' : I → SecA A F k := fun i => SecM.toSec A.A (m i)
  have key : ∀ r : Sp F ⟶ (T ⊗ A.A).left, r ≫ p = 𝟙 _ →
      ∃ w, w ≠ 0 ∧ Crd (LPow A.A A.L (k : ℤ) T) t' r w ∧ Crd (LPow A.A A.L (k : ℤ) T) t r w := by
    intro r hr
    let r' : T ⟶ T ⊗ A.A := Over.homMk r (by
      rw [← Over.w (fst T A.A), ← Category.assoc]
      exact (congrArg (· ≫ T.hom) hr).trans (Category.id_comp _))
    have er : ptSecT A.A (r' ≫ snd _ _) = r' := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ (lift_snd _ _)
      rw [ptSecT, lift_fst]
      exact Over.OverMorphism.ext hr.symm
    obtain ⟨v, hv, hs, ht⟩ := H (r' ≫ snd _ _)
    have er' : (ptSecT A.A (r' ≫ snd _ _)).left = r := congrArg (·.left) er
    replace hs : Crd (LPow A.A A.L (k : ℤ) T) s r v := er' ▸ hs
    replace ht : Crd (LPow A.A A.L (k : ℤ) T) t r (b.mulVec v) := er' ▸ ht
    refine ⟨_, hv, ?_, ht⟩
    obtain ⟨l, c, hl, hc⟩ := hs
    refine ⟨l, c, hl, fun i => ?_⟩
    have e : (t' i).f l = ∑ j, resG _ le_top (p.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (b i j))) * (s j).f l := by
      change (m i).1 l = _
      simp only [m, Submodule.coe_sum, Finset.sum_apply]
      rfl
    rw [e, valR_eq r _ hl, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← valR_eq r _ hl, valR_mul r _ hl, valR_const p r hr _ hl, hc j, mul_left_comm]
  obtain ⟨c₀, hc₀⟩ := SectionRatio.exists_ratio A.isLB (φ := fun _ : Fin 1 => (snd T A.A).left)
    (ε := fun _ => (k : ℤ)) t' t
    (fun y J hJ => by
      have hm := hJ.mem (fun _ : Fin 1 => (snd T A.A).left) (𝟙 _)
      obtain ⟨i, hi⟩ := exists_mem_basicOpen p (H := LPow A.A A.L (k : ℤ) T) (b := t)
        (fun r hr => (key r hr).imp fun w hw => ⟨hw.1, hw.2.2⟩) _ y hm
      exact ⟨i, (SectionRatio.mem_basicOpen_iff_gs _ y hm).1 hi⟩)
    (fun i i' y J hJ => by
      have hm := hJ.mem (fun _ : Fin 1 => (snd T A.A).left) (𝟙 _)
      have e := cross_eq p (H := LPow A.A A.L (k : ℤ) T) (a := t') (b := t)
        (fun r hr => (key r hr).imp fun w hw => hw.2) (fun _ => J (𝟙 _ ≫ (snd T A.A).left)) i i'
      exact (gs_mul _ y _ hm _ _).symm.trans ((congrArg (gs (𝟙 _) y _) e).trans (gs_mul _ y _ hm _ _)))
  obtain ⟨d, hd⟩ := CommPairing.surj_fst hG A.isAb T c₀
  obtain ⟨c, rfl⟩ := (kf_bijective R F).2 d
  refine ⟨c, fun i => ThetaAct.sv_ext A.isLB fun y J hJ => ?_⟩
  refine (hc₀ i y J hJ).trans (Eq.trans ?_ (ThetaAct.sv_smul _ _ _ _ hJ).symm)
  exact congrArg (· * _) ((congrArg (gs (𝟙 _) y ⊤) hd.symm).trans (gs_pull (𝟙 _) _ y ⊤ trivial _))

end GlobalTheory.ZH.SecProp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosedImmersionBaseChangeProjChart
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem IsHom.valR_mem_image_ringOn {o Ω Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field Ω'] [Algebra o Ω']
    {M : RatModel o Ω} {N : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'} {Y : Scheme.{0}} {j : Y ⟶ M.Z} [IsOpenImmersion j]
    {b : N.Z ⟶ Y} (h : M.IsHom N φ (b ≫ j)) {V : Y.Opens} (hV : ⊤ ≤ (N.pt ≫ b) ⁻¹ᵁ V) (g : Γ(Y, V)) :
    valR (N.pt ≫ b) V g ∈ φ '' (M.ringOn (j ''ᵁ V : M.Z.Opens) : Set Ω) := by
  have hne : ((j ''ᵁ V : M.Z.Opens) : Set M.Z).Nonempty :=
    ⟨_, _, hV (x := IsLocalRing.closedPoint Ω') trivial, rfl⟩
  have hle : V ≤ j ⁻¹ᵁ (j ''ᵁ V) := (j.preimage_image_eq V).ge
  refine ⟨valF M.pt _ ((j.appIso V).inv.hom g), (mem_ringOn_iff_exists hne).2 ⟨_, rfl⟩, ?_⟩
  refine (valR_spMap_comp φ.toRingHom M.pt _ (M.top_le_preimage_pt hne) _).symm.trans ?_
  rw [← show N.pt ≫ b ≫ j = spMap φ.toRingHom ≫ M.pt from h, ← Category.assoc, ← valR_appLE _ j hle hV,
    ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
  exact valR_res _ le_rfl hV g

theorem projChart_of_isPullback : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N : RatModel o Ω') (U₀ : M.Z.Opens) (R : Type) [CommRing R] (X : Scheme.{0}) (p : X ⟶ Sp R) (u₀ : U₀.toScheme ⟶ Sp R) (a : N.Z ⟶ X) (b : N.Z ⟶ U₀.toScheme) (H : LB X) (J : Type) (s : J → H.Sec) (t : J → Ω'), IsPullback a b p u₀ → M.IsHom N φ (b ≫ U₀.ι) → ImmBy p H s Set.univ → Crd H s (N.pt ≫ a) t → (∀ (i : J) (z : N.Z), N.Div t i z ↔ a z ∈ nonzeroLocus (s i)) → ∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty → M.ProjChart N φ (b ≫ U₀.ι) W t := by
  intro o Ω _ _ _ M Ω' _ _ φ N U₀ R _ X p u₀ a b H J s t sq hom imm crd hdiv W hWU hW hne
  obtain ⟨V, rfl⟩ : ∃ V : U₀.toScheme.Opens, U₀.ι ''ᵁ V = W :=
    ⟨U₀.ι ⁻¹ᵁ W, by rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]; exact inf_eq_right.2 hWU⟩
  have hV : IsAffineOpen V := U₀.ι.isAffineOpen_iff_of_isOpenImmersion.1 hW
  have hmem : ∀ z : N.Z, (b ≫ U₀.ι) z ∈ U₀.ι ''ᵁ V ↔ b z ∈ V := fun z =>
    Iff.of_eq (congrArg (b z ∈ ·) (U₀.ι.preimage_image_eq V))
  refine ⟨fun z _ => ?_, fun i hi => ?_⟩
  · have hz : a z ∈ ⨆ i ∈ (Set.univ : Set J), nonzeroLocus (s i) := by rw [imm.1]; trivial
    simp only [Set.mem_univ, iSup_pos, TopologicalSpace.Opens.mem_iSup] at hz
    obtain ⟨i, hi⟩ := hz
    exact ⟨i, (hdiv i z).2 hi⟩
  obtain ⟨hD, r, hr, hgen⟩ := imm.2 i trivial
  have hU : IsAffineOpen (a ⁻¹ᵁ nonzeroLocus (s i) ⊓ b ⁻¹ᵁ V) := by
    have : IsAffine _ := isAffineOpen_top (Sp R)
    have : IsAffine _ := hV
    have : IsAffine _ := hD
    exact .of_isIso (Scheme.Hom.isPullback_resLE sq (US := ⊤) (UT := V) (UX := nonzeroLocus (s i)) le_top le_top
      rfl).isoPullback.hom
  have hset : ((a ⁻¹ᵁ nonzeroLocus (s i) ⊓ b ⁻¹ᵁ V : N.Z.Opens) : Set N.Z) =
      {z' | (b ≫ U₀.ι) z' ∈ U₀.ι ''ᵁ V ∧ N.Div t i z'} :=
    Set.ext fun z => and_comm.trans (and_congr (hmem z).symm (hdiv i z).symm)
  refine ⟨_, hU, hset, le_antisymm (fun x hx => ?_) (Algebra.adjoin_le ?_)⟩
  · have hgp : (b ≫ U₀.ι) (genericPoint N.Z) ∈ U₀.ι ''ᵁ V := by
      have e := congrArg (fun f => f (IsLocalRing.closedPoint Ω')) (show N.pt ≫ b ≫ U₀.ι = _ from hom)
      rw [← N.pt_apply (IsLocalRing.closedPoint Ω')]
      refine (congrArg (· ∈ U₀.ι ''ᵁ V) e).mpr ?_
      exact M.top_le_preimage_pt hne (x := spMap φ.toRingHom (IsLocalRing.closedPoint Ω')) trivial
    have hUne : ((a ⁻¹ᵁ nonzeroLocus (s i) ⊓ b ⁻¹ᵁ V : N.Z.Opens) : Set N.Z).Nonempty :=
      ⟨_, hset.ge ⟨hgp, div_genericPoint hi⟩⟩
    have hpt := N.top_le_preimage_pt hUne
    have ha : ⊤ ≤ (N.pt ≫ a) ⁻¹ᵁ nonzeroLocus (s i) := le_preimage_comp _ a inf_le_left hpt
    have hb : ⊤ ≤ (N.pt ≫ b) ⁻¹ᵁ V := le_preimage_comp _ b inf_le_right hpt
    set A := Algebra.adjoin o (φ '' (M.ringOn (U₀.ι ''ᵁ V : M.Z.Opens) : Set Ω) ∪ Set.range fun j => t j / t i)
    have hB : ∀ g, valR (N.pt ≫ b) V g ∈ A := fun g =>
      Algebra.subset_adjoin (Or.inl (hom.valR_mem_image_ringOn hb g))
    have hA : ∀ g, valR (N.pt ≫ a) (nonzeroLocus (s i)) g ∈ A := fun g => by
      have : Subring.closure (Set.range (constFn p (nonzeroLocus (s i))) ∪ Set.range r) ≤
          A.toSubring.comap (valMap _ _ ha).hom := by
        rw [Subring.closure_le]
        rintro _ (⟨c, rfl⟩ | ⟨j, rfl⟩)
        · show (valMap _ _ ha).hom _ ∈ A
          rw [← valR_eq, valR_constFn _ _ _ ha, Category.assoc, sq.w, ← Category.assoc, ← valR_constFn _ _ _ hb]
          exact hB _
        · show (valMap _ _ ha).hom _ ∈ A
          rw [← valR_eq, eq_div_of_mul_eq hi (CrdCalc.crd_ratio crd (hr j) ha).symm]
          exact Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)
      rw [valR_eq _ _ ha]
      exact this (hgen.ge (Subring.mem_top g))
    have po := (isIso_pushoutSection_iff sq (US := ⊤) (UT := V) (UX := nonzeroLocus (s i)) le_top le_top rfl).1
      (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) hV hD)
    have hcl := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
    have hle : (⊤ : Subring _) ≤ A.toSubring.comap (valMap _ _ hpt).hom := by
      rw [← hcl, Subring.closure_le]
      rintro _ (⟨g, rfl⟩ | ⟨g, rfl⟩)
      · show (valMap _ _ hpt).hom _ ∈ A
        rw [← valR_eq, valR_appLE _ _ _ hpt]
        exact hA g
      · show (valMap _ _ hpt).hom _ ∈ A
        rw [← valR_eq, valR_appLE _ _ _ hpt]
        exact hB g
    obtain ⟨f, rfl⟩ := (mem_ringOn_iff_exists hUne).1 hx
    rw [valF_eq_valR, valR_eq _ _ hpt]
    exact hle (Subring.mem_top f)
  · rintro _ (⟨x, hx, rfl⟩ | ⟨j, rfl⟩)
    · exact mem_ringOn.2 fun z hz => hom.map_mem_O (mem_ringOn.1 hx _ (hset.le hz).1)
    · exact mem_ringOn.2 fun z hz => (hset.le hz).2.2 j

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivIffMemNonzeroLocus
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

namespace GlobalTheory.ZH.DivCrd

open GlobalTheory.Points CrdCalc

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {N : RatModel o Ω} {X : Scheme.{0}} {a : N.Z ⟶ X}
  {H : LB X} {J : Type} {s : J → H.Sec} {t : J → Ω}

theorem ratio_eq (ht : Crd H s (N.pt ≫ a) t) {k : J} {z : N.Z} (hz : a z ∈ nonzeroLocus (s k)) :
    t k ≠ 0 ∧ ∀ (j : J) (r : Γ(X, nonzeroLocus (s k))), IsRatio (s j) (s k) _ r →
      valF N.pt (a ⁻¹ᵁ nonzeroLocus (s k)) (a.app _ r) = t j / t k := by
  have h : ⊤ ≤ (N.pt ≫ a) ⁻¹ᵁ nonzeroLocus (s k) :=
    N.top_le_preimage_pt (U := a ⁻¹ᵁ nonzeroLocus (s k)) ⟨z, hz⟩
  have hk : t k ≠ 0 := ((crd_isUnit_iff k ht).2 h).ne_zero
  refine ⟨hk, fun j r hr => ?_⟩
  rw [eq_div_iff hk, crd_ratio ht hr h, valR_comp]
  rfl

theorem div_of_mem (hH : H.IsLB) (ht : Crd H s (N.pt ≫ a) t) {k : J} {z : N.Z}
    (hz : a z ∈ nonzeroLocus (s k)) : N.Div t k z := by
  obtain ⟨hk, h⟩ := ratio_eq ht hz
  refine ⟨hk, fun j => ?_⟩
  obtain ⟨r, hr, -⟩ := GlobalTheory.SecRatio.existsUnique_isRatio hH (s j) (s k) _ le_rfl
  exact ⟨a ⁻¹ᵁ nonzeroLocus (s k), a.app _ r, hz, h j r hr⟩

theorem crd_eq_val_mul (hH : H.IsLB) (ht : Crd H s (N.pt ≫ a) t) {K : Type} [Field K] {x : Sp K ⟶ N.Z}
    {v : J → K} {k : J} (hv : Crd H s (x ≫ a) v)
    (hz : a (x (IsLocalRing.closedPoint K)) ∈ nonzeroLocus (s k)) :
    v k ≠ 0 ∧ ∀ j, v j = N.val x (t j / t k) * v k := by
  have hx : ⊤ ≤ x ⁻¹ᵁ (a ⁻¹ᵁ nonzeroLocus (s k)) := (le_preimage_iff x _).2 hz
  have h : ⊤ ≤ (x ≫ a) ⁻¹ᵁ nonzeroLocus (s k) := hx
  refine ⟨((crd_isUnit_iff k hv).2 h).ne_zero, fun j => ?_⟩
  obtain ⟨r, hr, -⟩ := GlobalTheory.SecRatio.existsUnique_isRatio hH (s j) (s k) _ le_rfl
  rw [RatModel.val_eq ((top_le_preimage_iff _ _).1 hx) ((ratio_eq ht hz).2 j r hr), crd_ratio hv hr h,
    valR_comp]
  rfl

theorem mem_of_div_pt (hH : H.IsLB) (hs : ⨆ j, nonzeroLocus (s j) = ⊤) (ht : Crd H s (N.pt ≫ a) t)
    {K : Type} [Field K] (x : Sp K ⟶ N.Z) {i : J} (hi : N.Div t i (x (IsLocalRing.closedPoint K))) :
    a (x (IsLocalRing.closedPoint K)) ∈ nonzeroLocus (s i) := by
  have hm : a (x (IsLocalRing.closedPoint K)) ∈ ⨆ j, nonzeroLocus (s j) := by rw [hs]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  obtain ⟨v, hv⟩ := crd_exists hH s (x ≫ a)
  obtain ⟨h0, h1⟩ := crd_eq_val_mul hH ht hv hk
  have hd := div_of_mem hH ht hk
  have hu := (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton x _) _).2 ((hd.div_iff_isUnit i).1 hi)
  have hvi : IsUnit (v i) := isUnit_iff_ne_zero.2 (by rw [h1 i]; exact mul_ne_zero hu h0)
  exact (le_preimage_iff (x ≫ a) _).1 ((crd_isUnit_iff i hv).1 hvi)

theorem mem_of_div (hH : H.IsLB) (hs : ⨆ j, nonzeroLocus (s j) = ⊤) (ht : Crd H s (N.pt ≫ a) t)
    {i : J} {z : N.Z} (hi : N.Div t i z) : a z ∈ nonzeroLocus (s i) := by
  let x : Sp (N.Z.residueField z) ⟶ N.Z := N.Z.fromSpecResidueField z
  have e : x (IsLocalRing.closedPoint (N.Z.residueField z)) = z := Scheme.fromSpecResidueField_apply _ _
  have h := mem_of_div_pt hH hs ht x (i := i) (by rw [e]; exact hi)
  rwa [e] at h

theorem div_iff_mem_nonzeroLocus : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (N : RatModel o Ω) (X : Scheme.{0}) (a : N.Z ⟶ X) (H : LB X) (J : Type) (s : J → H.Sec) (t : J → Ω), H.IsLB → ⨆ j, nonzeroLocus (s j) = ⊤ → Crd H s (N.pt ≫ a) t → (∀ (i : J) (z : N.Z), N.Div t i z ↔ a z ∈ nonzeroLocus (s i)) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ N.Z) (v : J → K) (k : J), Crd H s (x ≫ a) v → N.Div t k (x (IsLocalRing.closedPoint K)) → v k ≠ 0 ∧ ∀ j, v j = N.val x (t j / t k) * v k :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hH hs ht =>
    ⟨fun _ _ => ⟨mem_of_div hH hs ht, div_of_mem hH ht⟩,
      fun _ _ x _ _ hv hk => crd_eq_val_mul hH ht hv (mem_of_div_pt hH hs ht x hk)⟩

end GlobalTheory.ZH.DivCrd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAffineRefinementSplitExtChartsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_refinement_splitExtCharts : ∀ (S : Scheme.{0}) (E : SplitExt S) (Y : Scheme.{0}) (A : LB Y), A.IsLB → ∀ π : E.B.left ⟶ Y, ∃ N₀ : LB E.B.left, N₀.IsLB ∧ (∀ l, IsAffineOpen (N₀.U l)) ∧ (∀ l, ∃ j, N₀.U l ≤ E.chart j) ∧ Nonempty (ChartPull N₀ A π) := by
  first | exact @GlobalTheory.ZH.UFib.exists_affine_refinement | exact GlobalTheory.ZH.UFib.exists_affine_refinement | (intros; apply GlobalTheory.ZH.UFib.exists_affine_refinement <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PureWeightSectionToTwistedPolarisationPowerStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
theorem _root_.GlobalTheory.T.pureWeightSection_to_twistedPolarisationPower : (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (N d : ℕ) (π : Φ.Pol N) (α : Φ.E.X), 1 ≤ N → 1 ≤ d → (∀ φ : (Φ.H d).Sec, Φ.Pure α φ → ∃ s : LB.Sec (Out.twistLB π.PB.A π.PB.L (N * d) (π.c α)), ((∀ j, s.f j = 0) → ∀ l, φ.f l = 0) ∧ ∀ x : Φ.Pt, (⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ ↔ ⊤ ≤ (Out.ptSecT π.PB.A (x ≫ Φ.D.q ≫ π.β.hom)).left ⁻¹ᵁ Out.nonzeroLocus s)) ∧ ∀ s : LB.Sec (Out.twistLB π.PB.A π.PB.L (N * d) (π.c α)), ∃ φ : (Φ.H d).Sec, Φ.Pure α φ ∧ ∀ x : Φ.Pt, (⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ ↔ ⊤ ≤ (Out.ptSecT π.PB.A (x ≫ Φ.D.q ≫ π.β.hom)).left ⁻¹ᵁ Out.nonzeroLocus s)) := by
  first | exact @GlobalTheory.ZH.TwSec.pure_sec_twist | exact GlobalTheory.ZH.TwSec.pure_sec_twist | (intros; apply GlobalTheory.ZH.TwSec.pure_sec_twist <;> assumption)
end

