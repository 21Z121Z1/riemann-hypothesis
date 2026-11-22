import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0102
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationAtUnit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteFaithfullyFlatKer
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsE8ThetaStructure
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2297
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSharpAndPrim
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0176

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNowhereZeroSectionNearOfFlatTrivial
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FlatTrivSec

variable {X Y : Scheme.{0}}

theorem isUnit_gs_iff {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (h : f z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs f z U a) ↔ f z ∈ X.basicOpen a := by
  rw [gs_eq f z U h, ← Scheme.mem_basicOpen Z _ z h, ← Scheme.preimage_basicOpen]
  rfl

def pullSec (L : LB X) (θ : LB.Sec L) (F : Y ⟶ X) : LB.Sec (L.pull F) where
  f := fun I => (Y.presheaf.map (homOfLE (LB.wchart_le L (fun _ : PUnit => F) I PUnit.unit)).op).hom
    ((F.app _).hom (θ.f (I PUnit.unit)))
  compat := fun I J => fn_ext fun y hy => by
    have hI : F y ∈ L.U (I PUnit.unit) := mem_pull.1 hy.1
    have hJ : F y ∈ L.U (J PUnit.unit) := mem_pull.1 hy.2
    have hm : (𝟙 Y ≫ F) y ∈ L.U (I PUnit.unit) ⊓ L.U (J PUnit.unit) := ⟨hI, hJ⟩
    refine (gs_res (𝟙 Y) y _ hy _).trans ((gs_res (𝟙 Y) y _ hy.1 _).trans ((gs_pull (𝟙 Y) F y _ hI _).trans ?_))
    refine Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_pull_g L F (𝟙 Y) y I J hy.1 hy.2)))
      ((gs_res (𝟙 Y) y _ hy _).trans ((gs_res (𝟙 Y) y _ hy.2 _).trans (gs_pull (𝟙 Y) F y _ hJ _))))).symm
    exact (gs_res _ y inf_le_left hm _).symm.trans ((congrArg (gs _ y _) (θ.compat _ _)).trans
      ((gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit _ y _ hm _) (gs_res _ y _ hm _))))

theorem gs_pullSec (L : LB X) (θ : LB.Sec L) (F : Y ⟶ X) (y : Y) (J : PUnit → L.ι) (hy : y ∈ (L.pull F).U J) :
    gs (𝟙 Y) y _ ((pullSec L θ F).f J) = gs F y (L.U (J PUnit.unit)) (θ.f (J PUnit.unit)) := by
  have hI : F y ∈ L.U (J PUnit.unit) := mem_pull.1 hy
  refine (gs_res (𝟙 Y) y _ hy _).trans ((gs_pull (𝟙 Y) F y _ hI _).trans ?_)
  rw [Category.id_comp]

theorem cst_bijective_of {C : Type} [CommRing C] (V : (Sp C).Opens)
    (hV : Function.Bijective ((Sp C).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom) :
    Function.Bijective (cst V.ι ⊤) := by
  have key : ∀ (V' : (Sp C).Opens) (h : V' ≤ ⊤), V' = V →
      Function.Bijective ((Sp C).presheaf.map (homOfLE h).op).hom := by
    rintro V' h rfl
    exact hV
  have h₁ : Function.Bijective V.ι.appTop.hom := by
    rw [Scheme.Opens.ι_appTop]
    exact key _ _ V.ι_image_top
  have h₀ : Function.Bijective (rs V.toScheme (le_top : (⊤ : V.toScheme.Opens) ≤ ⊤)) := by
    have : ⇑(rs V.toScheme (le_top : (⊤ : V.toScheme.Opens) ≤ ⊤)) = id := funext fun x => rs_self _ x
    rw [this]
    exact Function.bijective_id
  have h₃ : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).inv
  exact h₀.comp (h₁.comp h₃)

theorem gs_cst_top {C : Type} [CommRing C] {Z : Scheme.{0}} (f : Z ⟶ Sp C) (z : Z) (x : C) :
    gs (𝟙 Z) z ⊤ (cst f ⊤ x) = gs f z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom x) := by
  refine (gs_res (𝟙 Z) z (U := f ⁻¹ᵁ ⊤) (V := ⊤) le_top trivial _).trans ((gs_pull (𝟙 Z) f z ⊤ trivial _).trans ?_)
  rw [Category.id_comp]

theorem exists_sec_near : ∀ (B C : Type) [CommRing B] [IsNoetherianRing B] [CommRing C] (g : B →+* C), g.Flat → ∀ (W : (Sp B).Opens), Function.Bijective ((Sp C).presheaf.map (homOfLE (le_top : spMap g ⁻¹ᵁ W ≤ ⊤)).op).hom → ∀ (M : LB W.toScheme), M.IsLB → Triv (M.pull (spMap g ∣_ W)) → ∀ y : Sp C, ∃ (s : M.Sec) (D : (Sp C).Opens), y ∈ D ∧ ∀ z : (spMap g ⁻¹ᵁ W).toScheme, (spMap g ⁻¹ᵁ W).ι z ∈ D → (spMap g ∣_ W) z ∈ Out.nonzeroLocus s := by
  intro B C _ _ _ g hg W hbij M hM hT y
  classical
  haveI : CompactSpace W.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (W : Set (Sp B)))
  obtain ⟨t, ht⟩ := hT
  obtain ⟨n, c, u, hcomb⟩ := FlatSec.exists_comb_of_flat B C g hg W.toScheme W.ι _ (spMap g ∣_ W)
    (spMap g ⁻¹ᵁ W).ι (isPullback_morphismRestrict (spMap g) W) M hM (genSec t ht)
  choose a ha using fun i => DVR.ValuationAtUnit.exists_glue_ratio
    (DVR.linComb_cover M hM (fun _ : PUnit => spMap g ∣_ W) (fun _ => 1)) (pullSec M (u i) (spMap g ∣_ W)) t ht
  have hb := cst_bijective_of _ hbij
  choose e he using fun i => hb.2 (a i)
  have chart : ∀ z : (spMap g ⁻¹ᵁ W).toScheme, ∃ k, (spMap g ∣_ W) z ∈ M.U k := fun z => by
    have hz : (spMap g ∣_ W) z ∈ ⨆ k, M.U k := by rw [hM.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hz
  have key : ∀ (z : (spMap g ⁻¹ᵁ W).toScheme) (k : M.ι), (spMap g ∣_ W) z ∈ M.U k → ∀ i,
      gs (spMap g ∣_ W) z _ ((u i).f k) = gs (𝟙 _) z ⊤ (a i) * (gm (𝟙 _) z _ (t.s (fun _ => k))).val := by
    intro z k hk i
    have hz : z ∈ (M.pull (spMap g ∣_ W)).U (fun _ => k) := mem_pull.2 hk
    refine (gs_pullSec M (u i) _ z (fun _ => k) hz).symm.trans ?_
    refine (congrArg (gs (𝟙 _) z _) (ha i (fun _ => k))).trans ?_
    rw [gs_mul (𝟙 _) z _ hz, gs_res (𝟙 _) z _ hz, gs_unit (𝟙 _) z _ hz]
  have hsum : ∑ i, c i * e i = 1 := by
    apply hb.1
    rw [map_sum, map_one]
    refine fn_ext fun z _ => ?_
    obtain ⟨k, hk⟩ := chart z
    have hz : z ∈ (M.pull (spMap g ∣_ W)).U (fun _ => k) := mem_pull.2 hk
    have h1 := hcomb z k hk
    simp only [key z k hk] at h1
    have h2 : gs (𝟙 _) z _ ((genSec t ht).f (fun _ => k)) = (gm (𝟙 _) z _ (t.s (fun _ => k))).val :=
      gs_unit (𝟙 _) z _ hz _
    rw [h2] at h1
    simp only [map_mul, he]
    rw [FlatSec.gs_sum (𝟙 _) z ⊤ trivial, gs_eq (𝟙 _) z ⊤ trivial 1, map_one, map_one]
    simp only [gs_mul (𝟙 _) z ⊤ trivial]
    have h3 : (∑ i, gs (𝟙 _) z ⊤ (cst (spMap g ⁻¹ᵁ W).ι ⊤ (c i)) * gs (𝟙 _) z ⊤ (a i)) *
        (gm (𝟙 _) z _ (t.s (fun _ => k))).val = 1 * (gm (𝟙 _) z _ (t.s (fun _ => k))).val := by
      rw [_root_.one_mul, Finset.sum_mul]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => _root_.mul_assoc _ _ _) h1.symm
    exact (Units.mul_left_inj _).1 h3
  obtain ⟨i, hi⟩ : ∃ i, e i ∉ y.asIdeal := by
    by_contra hne
    push_neg at hne
    apply y.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hsum]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hne i)
  refine ⟨u i, PrimeSpectrum.basicOpen (e i), hi, fun z hz => ?_⟩
  obtain ⟨k, hk⟩ := chart z
  have hu1 : IsUnit (gs (𝟙 _) z ⊤ (a i)) := by
    rw [← he i, gs_cst_top, isUnit_gs_iff _ z ⊤ trivial, basicOpen_eq_of_affine]
    exact hz
  have hu2 : IsUnit (gs (spMap g ∣_ W) z _ ((u i).f k)) := by
    rw [key z k hk i]
    exact hu1.mul (Units.isUnit _)
  rw [isUnit_gs_iff _ z _ hk] at hu2
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hu2⟩

end GlobalTheory.FlatTrivSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushSectionsCanonicalModification
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

namespace GlobalTheory.ModifCanon
open GlobalTheory.Vanishing.H0 GlobalTheory.TangentOrigin

theorem stalkMap_bijective_of_isIso_restrict : ∀ (Y X : Scheme.{0}) (σ : X ⟶ Y) (U : Y.Opens), IsIso (σ ∣_ U) →
    ∀ x : X, x ∈ σ ⁻¹ᵁ U → Function.Bijective (σ.stalkMap x).hom := by
  intro Y X σ U h x hx
  have e := morphismRestrictStalkMap σ U ⟨x, hx⟩
  have h1 : IsIso ((σ ∣_ U).stalkMap ⟨x, hx⟩) := ((isIso_iff_isIso_stalkMap (σ ∣_ U)).1 h).2 _
  have h2 : IsIso (σ.stalkMap x) := ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff e).1 h1
  exact ConcreteCategory.bijective_of_isIso _

theorem isUnit_val_of_isUnit_germ : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (B : LB Y) (O : Y.Opens)
    (x : Sp ℂ ⟶ Y) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (f : H0 p B O) (e : Sp ℂ)
    (hy : x e ∈ O) (hiy : x e ∈ B.U i), IsUnit (H0.germ i (x e) hy hiy f) → IsUnit (H0.val x i hO hi f) := by
  intro k _ Y p B O x i hO hi f e hy hiy hu
  have hb : x e ∈ Y.basicOpen (f.loc i) := (Y.mem_basicOpen _ _ (Vanishing.memInf hy hiy)).2 hu
  have hV : ⊤ ≤ x ⁻¹ᵁ Y.basicOpen (f.loc i) := fun y _ => by rw [Subsingleton.elim y e]; exact hb
  rw [H0.val_apply, ← evalPt_res x (Y.basicOpen_le (f.loc i)) _ hV]
  exact (RingedSpace.isUnit_res_basicOpen Y.toLocallyRingedSpace.toRingedSpace (f.loc i)).map _

end GlobalTheory.ModifCanon

namespace GlobalTheory.ModifCanon

open GlobalTheory.Vanishing.H0 GlobalTheory.TangentOrigin

variable {X Y : Scheme.{0}}

abbrev jacChart {K' : LB X} {K B : LB Y} (σ : X ⟶ Y) (hK' : K'.IsLB) (hK : K.IsLB) (hB : B.IsLB) :
    ProdChart (LB.div K' (K.pull σ)) ((tens K B).pull σ) (tens K' (B.pull σ)) where
  isLB₁ := LB.isLB_div hK' (LB.isLB_pull hK σ)
  isLB₂ := LB.isLB_pull (isLB_tens hK hB) σ
  isLB₃ := isLB_tens hK' (LB.isLB_pull hB σ)
  τ := K'.ι × K.ι × B.ι
  a t := (t.1, pIdx K σ t.2.1)
  b t := pIdx (tens K B) σ (t.2.1, t.2.2)
  c t := (t.1, pIdx B σ t.2.2)
  cover x := by
    obtain ⟨i, hi⟩ := exists_chart hK' x
    obtain ⟨j, hj⟩ := exists_chart hK (σ x)
    obtain ⟨l, hl⟩ := exists_chart hB (σ x)
    exact ⟨(i, j, l), ⟨hi, mem_pIdx.2 hj⟩, mem_pIdx.2 ⟨hj, hl⟩, hi, mem_pIdx.2 hl⟩
  rule x t t' e e' := by
    rw [tr_tens _ _ x e.2.2 e'.2.2, tr_div _ _ x e.1 e'.1, tr_pull _ σ x e.2.1 e'.2.1,
      tr_pull _ σ x e.2.2.2 e'.2.2.2, tr_pull _ σ x e.1.2 e'.1.2,
      tr_tens _ _ (σ x) (mem_pull.1 e.2.1) (mem_pull.1 e'.2.1), map_mul, mul_assoc]
    exact congrArg (tr K' x t.1 t'.1 * ·) (inv_mul_cancel_left _ _).symm

theorem val_restr {k : Type} [CommRing k] {p : Y ⟶ Sp k} {B : LB Y} {O O' : Y.Opens} (x : Sp ℂ ⟶ Y) (i : B.ι)
    (h : O' ≤ O) (hO' : ⊤ ≤ x ⁻¹ᵁ O') (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (f : H0 p B O) :
    H0.val x i hO' hi (H0.restr h f) = H0.val x i hO hi f :=
  evalPt_res x (inf_le_inf_right _ h) _ _ (f.loc i)

theorem exists_push_sections : ∀ (F : Type) [Field F] [CharZero F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (d : ℕ) [SmoothOfRelativeDimension d p] (U : Y.Opens) (M : Modif p U d) (K : CanonLB p d) (K' : CanonLB M.str d) (B : LB Y), IsProjOver p → (U : Set Y).Nonempty → B.IsLB → ∃ Ψ : H0 M.str (tens K'.bundle (B.pull M.σ)) ⊤ → H0 p (tens K.bundle B) ⊤, ∀ (z : Sp ℂ ⟶ M.X), ⊤ ≤ z ⁻¹ᵁ M.opn → ∀ (k' : (tens K'.bundle (B.pull M.σ)).ι) (hk' : ⊤ ≤ z ⁻¹ᵁ (tens K'.bundle (B.pull M.σ)).U k') (k : (tens K.bundle B).ι) (hk : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ (tens K.bundle B).U k), ∃ lam : ℂˣ, ∀ g, H0.val (z ≫ M.σ) k le_top hk (Ψ g) = lam * H0.val z k' le_top hk' g := by
  intro F _ _ Y _ p d _ U M K K' B hproj hU hB
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have : GlobalTheory.IsNormalScheme Y := isNormalScheme_of_smooth p
  have : Nonempty U := hU.to_subtype
  have := M.iso
  have hXi : IsIntegral M.X := GlobalTheory.T.isIntegral_smoothProjectiveModification_of_nonempty F Y p U d M hU
  obtain ⟨J, hJ⟩ := GlobalTheory.T.exists_jacobian_section_isUnit_germ_of_localIso F Y M.X p M.σ d K K'
  have hL : (tens K.bundle B).IsLB := isLB_tens K.isLB hB
  let C := jacChart M.σ K'.isLB K.isLB hB
  have hopn : ∀ x ∈ M.opn, Function.Bijective (M.σ.stalkMap x).hom :=
    stalkMap_bijective_of_isIso_restrict Y M.X M.σ U M.iso
  have hJU : NowhereZero (H0.restr (le_top : M.opn ≤ ⊤) J) := fun x hx a ha => by
    rw [germ_restr]; exact hJ x (hopn x hx) a ha
  have hT : M.opn ≤ M.σ ⁻¹ᵁ (⊤ : Y.Opens) := fun x _ => memTop (M.σ x)
  have ext : ∀ g : H0 M.str (tens K'.bundle (B.pull M.σ)) ⊤, ∃ s : H0 p (tens K.bundle B) ⊤,
      C.mul (H0.restr le_top J) (H0.pull M.σ hT s) = H0.restr le_top g := by
    intro g
    obtain ⟨s₀, hs₀⟩ := (M.bijective_pull hL).2 ((C.mulEquiv hJU).symm (H0.restr le_top g))
    have rel : C.mul (H0.restr le_top J) (H0.pull M.σ le_rfl s₀) = H0.restr le_top g := by
      rw [hs₀]; exact (C.mulEquiv hJU).apply_symm_apply _
    obtain ⟨t, ht⟩ := (exists_sec_res_eq_iff hL (W := U) (LB.coord_mem s₀)).2 (fun x hx1 _ => by
      have := IsNormalScheme.isDiscreteValuationRing_stalk hx1
      obtain ⟨x', rfl, hb⟩ := GlobalTheory.T.exists_bijective_stalkMap_over_dvrPoint F Y p U d M hproj hU x this
      obtain ⟨i, hi⟩ := exists_chart hL (M.σ x')
      have : Nonempty ((tens K.bundle B).U i) := ⟨⟨_, hi⟩⟩
      have hne := nonempty_inf_of_isIntegral U ((tens K.bundle B).U i)
      exact ⟨i, hne, hi, GlobalTheory.T.germ_mem_range_stalk_of_pullback_mul_localIso F Y M.X p M.σ U _ _ _ C J g s₀ rel x' hb (hJ x' hb) i hi⟩)
    refine ⟨H0.ofSec p ⊤ t, ?_⟩
    have e : H0.restr (le_top : U ≤ ⊤) (H0.ofSec p ⊤ t) = s₀ := by
      rw [restr_ofSec]; exact LB.sec_ext fun i => ht i
    rw [← rel, ← e, pull_restr]
  choose Ψ hΨ using ext
  refine ⟨Ψ, fun z hz k' hk' k hk => ?_⟩
  obtain ⟨e⟩ : Nonempty (Sp ℂ) := inferInstance
  have all : ∀ (V : M.X.Opens), z e ∈ V → ⊤ ≤ z ⁻¹ᵁ V := fun V hV y _ => by
    rw [Subsingleton.elim y e]; exact hV
  have he : z e ∈ M.opn := hz trivial
  obtain ⟨t, ha, hb, hc⟩ := C.cover (z e)
  have ha' := all _ ha
  have hb' := all _ hb
  have hc' := all _ hc
  have hb'' : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ (tens K.bundle B).U ((C.b t) PUnit.unit) := fun y _ => by
    rw [Subsingleton.elim y e]; exact mem_pull.1 hb
  have hJv := isUnit_val_of_isUnit_germ F M.X M.str _ M.opn z (C.a t) hz ha' (H0.restr le_top J) e he ha
    (hJU _ he _ ha)
  obtain ⟨T1, hT1, e2⟩ : ∃ T1 : ℂ, T1 ≠ 0 ∧ ∀ g, H0.val z k' le_top hk' g = T1 * H0.val z (C.c t) le_top hc' g :=
    ⟨_, ((Units.isUnit _).map _).ne_zero, fun g => val_change (p := M.str) (O := ⊤) z k' (C.c t) le_top hk' hc' g⟩
  obtain ⟨T2, hT2, e1⟩ : ∃ T2 : ℂ, T2 ≠ 0 ∧ ∀ g, H0.val (z ≫ M.σ) k le_top hk (Ψ g) =
      T2 * H0.val (z ≫ M.σ) ((C.b t) PUnit.unit) le_top hb'' (Ψ g) :=
    ⟨_, ((Units.isUnit _).map _).ne_zero, fun g => val_change (p := p) (O := ⊤) (z ≫ M.σ) k ((C.b t) PUnit.unit) le_top hk hb'' (Ψ g)⟩
  refine ⟨Units.mk0 (T2 / (H0.val z (C.a t) hz ha' (H0.restr le_top J) * T1))
    (div_ne_zero hT2 (mul_ne_zero hJv.ne_zero hT1)), fun g => ?_⟩
  have e3 := C.val_mul (H0.restr le_top J) (H0.pull M.σ hT (Ψ g)) t z hz ha' hb' hc'
  rw [hΨ g, val_restr z _ le_top hz le_top] at e3
  have e4 := val_pull M.σ hT z (C.b t) hz hb' le_top hb'' (Ψ g)
  rw [e1, e2, e3, ← e4, Units.val_mk0]
  rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hJv.ne_zero hT1)]
  ring

end GlobalTheory.ModifCanon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianSchemeFiniteFlatSubgroup
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbQuotientAny

open GlobalTheory.AffineQuotient GlobalTheory.AbelianQuotient

set_option backward.isDefEq.respectTransparency false in

theorem exists_quotient_abelianScheme :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (H : Over (Sp R)) [GrpObj H] (i : H ⟶ A), IsAbelianScheme A → IsMonHom i → Mono i → IsFinite H.hom → Flat H.hom → ∃ (B : Over (Sp R)) (_ : GrpObj B) (q : A ⟶ B) (π : B ⟶ A), IsAbelianScheme B ∧ IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ IsFinite π.left ∧ IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q := by
  intro R _ _ A _ H _ i hA _ _ _ _
  have := hA.comm
  have := hA.proper
  have := hA.smooth
  have := hA.geomConnected
  have : IsCommMonObj H := ⟨by
    rw [← cancel_mono i, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]⟩
  obtain ⟨N, hN, hH⟩ := GlobalTheory.FiniteFlatKilled.main R H ‹_› ‹_›
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have := (GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA _ A hA N hN).1
  obtain ⟨Λ, _, _, _, _, e, _⟩ := exists_hopfAlgebra R H
  have hi : i ^ N = 1 := by
    rw [← Category.id_comp i, ← MonObj.pow_comp, hH, MonObj.one_comp]
  obtain ⟨Q, q, π, h₁, h₂, h₃, h₄, h₅⟩ := exists_quotient_hopf
    (GlobalTheory.HopfQuot.affine_quotient GlobalTheory.exists_basis_mem_of_span_eq_top_of_semilocal) (e.hom ≫ i)
    (mulA A N) (by
    rw [mulA, comp_pow, comp_pow, Category.comp_id, Category.comp_id, mul_pow, ← comp_pow,
      ← comp_pow i, hi, comp_one, comp_one, _root_.one_mul])
  have hq : IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q := by
    refine h₅.of_iso (whiskerRightIso e A) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
      <;> simp [comp_mul]
  obtain ⟨inst, hcomm, hhom, -⟩ := exists_grpObj i q hq
  refine ⟨Q, inst, q, π, ?_, hhom, h₂, h₃, h₄, h₁, hq⟩
  have : IsSeparated Q.hom := by rw [← Over.w π]; infer_instance
  have : LocallyOfFiniteType Q.hom := by rw [← Over.w π]; infer_instance
  have hw : q.left ≫ Q.hom = A.hom := Over.w q
  have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom
    hA.smooth hA.geomConnected
  have : Flat (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : UniversallyClosed (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyReduced (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyConnected (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have := flat_of_comp_of_flat_of_surjective q.left Q.hom
  have := UniversallyClosed.of_comp_surjective q.left Q.hom
  have := geometricallyReduced_of_comp q.left Q.hom
  have : LocallyOfFinitePresentation Q.hom := inferInstance
  exact ⟨hcomm, smooth_of_grpObj_of_flat Q, ⟨⟩, geometricallyConnected_of_comp q.left Q.hom⟩

end GlobalTheory.AbQuotientAny
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecCoordOfSubsingletonPic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM
open scoped CategoryTheory.Obj
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier

noncomputable section
namespace GlobalTheory.ZM.FieldPoint

theorem exists_secCoord_of_subsingleton_pic {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {I : Type} (σ : I → M.Sec)
    {A : Type} [CommRing A] [Subsingleton (CommRing.Pic A)] (x : Sp A ⟶ X) : ∃ v : I → A, SecCoord M σ x v := by
  have hL := LB.isLB_pull hM x
  obtain ⟨t, ht⟩ := GlobalTheory.LB.exists_isGen_of_subsingleton_pic hL
  let a := ReciprocityTheory.ChartRestriction.G.DVR.genSec t ht
  have ha : ⊤ ≤ nonzeroLocus a := (nonzeroLocus_genSec hL t ht).ge
  choose v hv using fun j => fnOn_top_bijective.2 (resG _ ha (secRatio a (secPull (σ j) x)))
  refine ⟨v, t, ht, fun i j h => ?_⟩
  have h1 := secRatio_on a (secPull (σ i) x) j (le_top.trans ha) le_rfl
  rw [resG_self, resG_self] at h1
  change _ = fnOn _ (v i) * a.f j
  rw [← resG_fnOn (le_top : _ ≤ ⊤), hv, resG_resG]
  exact h1

theorem exists_secCoord : ∀ (o : Type) [CommRing o] (m : ℕ) (K : Type) [Field K] (y : Sp K ⟶ PSpace o m),
    ∃ v : Fin (m + 1) → K, SecCoord (GlobalTheory.ProjSpace.O1 o m) (GlobalTheory.ProjSpace.coord o m) y v :=
  fun o _ m _ _ y => exists_secCoord_of_subsingleton_pic (O1_isLB o m) _ y

end GlobalTheory.ZM.FieldPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearL2CuspForm
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovTop.PetRep
open MeasureTheory

section Gen

open ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {D : D7}

end Gen

set_option maxHeartbeats 2000000 in

theorem adelMeas_one_of_good {D : D7} {T : Core D} {j : ℕ} (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o)
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    AdelMeas Y.U σ (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) := by
  obtain ⟨th, hr, hth, hd⟩ := h.dictU σ hσ
  have hN : 0 < D.host.g 0 * D.host.g 1 * Y.d.pd := by
    rw [h.pd]
    exact Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) (pow_pos (by norm_num) _)
  have hL := GlobalTheory.DictLocTest.locClause_of_unif_places hd (fun k hk => ((h.levelK k).1 hk).1)
    (GlobalTheory.LevelNbhd.level_mul_inf_mem_nhds D _ _ Y.Kf hN h.levelK) (fun c τ => ⟨_, hth c τ⟩)
  exact adelMeas_of_aut Y.d.Xo₂ Y.d.c₂ (U := Y.U) (σ := σ)
    (GlobalTheory.PetDef.adelAut_of_gamma (fun k la γ hγ => GlobalTheory.CovTop.Model.chi_eq_one h σ hσ k la γ hγ) hd
      (GlobalTheory.PetDef.muUnit_one Y h σ hσ) hL continuous_const)

end GlobalTheory.CovTop.PetRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSharpGen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.SiegLev GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.SiegSharpCover

def powBase {d m : ℕ} (hm : m ≠ 0) (hd : d ≠ 0) : TBase (cycAway (d * m)) d where
  ζ := (cycBase (mul_ne_zero hd hm)).ζ ^ m
  unit := (IsUnit.mul_iff.1 (by rw [← Nat.cast_mul]; exact isUnit_natCast (mul_ne_zero hd hm))).1
  prim K _ β := by
    rw [Units.val_pow_eq_pow_val, map_pow, cycBase_ζ]
    exact (isPrimitiveRoot_map (mul_ne_zero hd hm) β).pow (Nat.pos_of_ne_zero (mul_ne_zero hd hm)) (mul_comm d m)

theorem powBase_ζ {d m : ℕ} (hm : m ≠ 0) (hd : d ≠ 0) :
    ((powBase hm hd).ζ : cycAway (d * m)) = zetaAway (d * m) ^ m :=
  Units.val_pow_eq_pow_val _ _

def lowerOn {h N d : ℕ} {B : Type} [CommRing B] {ζ' ζ : B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    (C : SiegPre h (N * d) ζ' s) (h0 : N * d ≠ 0) (hζ : ζ = ζ' ^ d) : SiegPre h N ζ s where
  A := C.A
  ab := C.ab
  P := C.P
  isLB := C.isLB
  rig₁ := C.rig₁
  rig₂ := C.rig₂
  symm := C.symm
  lev a := C.lev a ^ d
  lev_add := (SiegLower.lower C (n := N) (d := d) rfl h0 (RingHom.id B) hζ).lev_add
  lev_tors := (SiegLower.lower C (n := N) (d := d) rfl h0 (RingHom.id B) hζ).lev_tors
  geom K _ _ x β z hx hz := (SiegLower.lower C (n := N) (d := d) rfl h0 (RingHom.id B) hζ).geom K x β z
    (by rw [show spMap (RingHom.id B) = 𝟙 _ from Spec.map_id _, Category.comp_id]; exact hx) hz

theorem smoothDim {h k : ℕ} {o : Type} [CommRing o] {ζ : o} {S : Scheme.{0}} {s : S ⟶ Sp o}
    (c : SiegPre h k ζ s) (hk : 2 ≤ k) (hζ : IsUnit ζ) (hu : IsUnit (k : o)) : SmoothOfRelativeDimension h c.A.hom := by
  have := c.ab.smooth
  have := c.ab.geomConnected
  choose n W hW hd using H1.exists_dim c.A.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension h) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let κ := S.residueField (c.A.hom y)
  let K := AlgebraicClosure κ
  let x : Sp K ⟶ S := spMap (algebraMap κ K) ≫ S.fromSpecResidueField (c.A.hom y)
  have hK : (k : K) ≠ 0 := by
    have := map_natCast (Spec.preimage (x ≫ s)).hom k
    rw [← this]
    exact (hu.map _).ne_zero
  have hp := (isGrpPullback_pullback c.A x).1
  obtain ⟨y', hy', -⟩ := Scheme.exists_preimage_of_isPullback hp y (default : PrimeSpectrum K)
    (Scheme.fromSpecResidueField_apply _ _).symm
  have : Smooth ((Over.pullback x).obj c.A).hom := by change Smooth (pullback.snd c.A.hom x); infer_instance
  have : ConnectedSpace ((Over.pullback x).obj c.A).left :=
    GeometricallyConnected.geometrically_connectedSpace (f := c.A.hom) x _ _ hp
  obtain ⟨d, hd'⟩ := exists_dim_of_preconnected ((Over.pullback x).obj c.A).hom y'
  have e : n y = h :=
    (H1.dim_base hp (hd y) hd' y' (by rw [hy']; exact hW y)).trans (SiegDim.dim_geometric_fibre c hk hζ hK x hd')
  have := hd y
  rwa [e] at this

end GlobalTheory.SiegSharpCover

namespace GlobalTheory.SiegSharpCover

end GlobalTheory.SiegSharpCover
end
end

