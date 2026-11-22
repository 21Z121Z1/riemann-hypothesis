import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2725
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleGluesFromCover
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2706
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2572
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2727

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOverProjectiveSpaceProjectiveAmpleTwist
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteOverPSpace

theorem isProjOver_and_isAmpleLB : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] (n k : ℕ) (Z : Scheme.{0}) (p : Z ⟶ PSpace o n), 1 ≤ k → IsFinite p → IsProjOver (p ≫ PSpace.str o n) ∧ (lbPow ((ProjSpace.O1 o n).pull p) k).IsLB ∧ IsAmpleLB (lbPow ((ProjSpace.O1 o n).pull p) k) ∧ ∀ (Y : Scheme.{0}) (h : Y ⟶ Z), LBIso ((lbPow ((ProjSpace.O1 o n).pull p) k).pull h) (lbPow ((ProjSpace.O1 o n).pull (h ≫ p)) k) := by
  intro o _ _ n k Z p hk hp
  have hO := ProjSpace.O1_isLB o n
  have hA : IsAmpleLB ((ProjSpace.O1 o n).pull p) := (isAmple_projective_O_one o n).pull_of_isAffineHom p
  refine ⟨isProjOver_comp_of_isFinite p ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩, isLB_lbPow hA.isLB k,
    (isAmpleLB_pow_iff hA.isLB hk).2 hA, fun Y h => ?_⟩
  refine (CechPic.cls_eq_iff (pull_isLB (isLB_lbPow hA.isLB k) h) (isLB_lbPow (pull_isLB hO (h ≫ p)) k)).1 ?_
  rw [CechPic.cls_pull (isLB_lbPow hA.isLB k), CechPic.cls_lbPow hA.isLB, CechPic.cls_lbPow (pull_isLB hO (h ≫ p)),
    CechPic.cls_pull hO, CechPic.cls_pull hO, CechPic.pull_comp, map_nsmul]

end GlobalTheory.FiniteOverPSpace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartPowEqOneLocal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

theorem push_pow {S' S₀ : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S₀} [GrpObj G] {f : S' ⟶ S₀}
    {π : G'.left ⟶ G.left} (hg : IsGrpPullback G' G f π) {T : Over S'} (x : T ⟶ G')
    (x₀ : Over.mk (T.hom ≫ f) ⟶ G) (h : x₀.left = x.left ≫ π) (n : ℕ) :
    (x₀ ^ n).left = (x ^ n).left ≫ π := by
  have h1 : (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ π := by
    let e : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ π) (by
      show ((1 : T ⟶ G').left ≫ π) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, hg.1.w, ← Category.assoc, Over.w])
    have he : e * e = e := Over.OverMorphism.ext ((hg.2 T 1 1 e e rfl rfl).trans (by rw [_root_.mul_one]; rfl))
    have he1 : e = 1 := mul_eq_left.1 he
    exact (congrArg (fun z => z.left) he1).symm
  induction n with
  | zero => simpa using h1
  | succ n ih => rw [pow_succ, pow_succ]; exact hg.2 T _ _ _ _ ih h

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g := by
  have := congrArg (fun z => (Spec.preimage z).hom) h
  simpa using this

theorem lift_of_residue : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X} {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q) {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left} (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (h : aH P' x0 hu hg.1 ^ q = 1) (S : Type) [CommRing S] [hS : IsLocalRing S] (y : Sp S ⟶ (torsion G' q).left), (∃ s : Sp (IsLocalRing.ResidueField S) ⟶ (Hs P' x0 hu).left, s ≫ (jH P' x0 hu hg.1 h).left = spMap (IsLocalRing.residue S) ≫ y) → ∃ s : Sp S ⟶ (Hs P' x0 hu).left, s ≫ (jH P' x0 hu hg.1 h).left = y := by
  intro E _ _ _ H X t R _ ξ q P' O _ x0 hu G' _ π hg h S _ hS y hy
  obtain ⟨s0, hs0⟩ := hy
  let o : O →+* S := (Spec.preimage (y ≫ (torsion G' q).hom)).hom
  have ho : spMap o = y ≫ (torsion G' q).hom := Spec.map_preimage _
  let φ : R →+* S := o.comp x0
  have hu' : IsUnit (φ P'.f) := hu.map o
  have hw : (y ≫ (torsion.ι G' q).left ≫ π) ≫ t.G.hom = spMap φ ≫ ξ := by
    rw [Category.assoc, Category.assoc, hg.1.w, ← Category.assoc (torsion.ι G' q).left, Over.w (torsion.ι G' q),
      ← Category.assoc, ← ho, GlobalTheory.HTMap.spc_assoc]
  let w : Over.mk (spMap φ ≫ ξ) ⟶ t.G := GlobalTheory.HTMap.mkPt _ hw
  let T : Over (Sp O) := Over.mk (y ≫ (torsion G' q).hom)
  let yt : T ⟶ torsion G' q := Over.homMk y rfl
  let x : T ⟶ G' := yt ≫ torsion.ι G' q
  have hx : x ^ q = 1 := by
    show (yt ≫ torsion.ι G' q) ^ q = 1
    rw [← MonObj.comp_pow, GlobalTheory.KernelNoTorsion.torsionι_pow, MonObj.comp_one]
  let x₀ : Over.mk (T.hom ≫ (spMap x0 ≫ ξ)) ⟶ t.G := Over.homMk (x.left ≫ π) (by
    show (x.left ≫ π) ≫ t.G.hom = T.hom ≫ spMap x0 ≫ ξ
    rw [Category.assoc, hg.1.w, ← Category.assoc, Over.w x])
  have hx₀ : x₀ ^ q = 1 := by
    refine Over.OverMorphism.ext ?_
    rw [push_pow hg x x₀ rfl q, hx]
    have := push_pow hg x x₀ rfl 0
    simp only [pow_zero] at this
    exact this.symm
  have hwq : w ^ q = 1 := GlobalTheory.HTMap.tors_of (g := 𝟙 _) (w := x₀) (by
    rw [Category.id_comp]
    show y ≫ (torsion.ι G' q).left ≫ π = (y ≫ (torsion.ι G' q).left) ≫ π
    rw [Category.assoc]) hx₀
  obtain ⟨β0, hβ0⟩ : ∃ β, P'.At φ w.left β := by
    refine GlobalTheory.HTMap.FP.at_open hu' rfl w hwq fun 𝔪 h𝔪 => ?_
    obtain rfl := IsLocalRing.eq_maximalIdeal h𝔪
    let gm : Bt P' x0 hu →+* IsLocalRing.ResidueField S := (Spec.preimage s0).hom
    have hgm : spMap gm = s0 := Spec.map_preimage _
    have e1 : spMap (gm.comp (algebraMap O (Bt P' x0 hu))) = spMap ((IsLocalRing.residue S).comp o) := by
      rw [← GlobalTheory.HTMap.spc (algebraMap O (Bt P' x0 hu)) gm, hgm, ← GlobalTheory.HTMap.spc o (IsLocalRing.residue S), ho]
      show s0 ≫ (Hs P' x0 hu).hom = _
      rw [← Over.w (jH P' x0 hu hg.1 h), ← Category.assoc, hs0, Category.assoc]
    have e2 := spMap_inj e1
    refine ⟨gm.comp (inB P' x0 hu), ?_, ?_⟩
    · show (gm.comp (inB P' x0 hu)).comp P'.str = (IsLocalRing.residue S).comp φ
      rw [RingHom.comp_assoc, inB_str, ← RingHom.comp_assoc, e2]
      rfl
    · show spMap (gm.comp (inB P' x0 hu)) ≫ P'.u.left = spMap (IsLocalRing.residue S) ≫ y ≫ (torsion.ι G' q).left ≫ π
      rw [← GlobalTheory.HTMap.spc_assoc, hgm, ← aH_left_π P' x0 hu hg.1, ← jH_ι P' x0 hu hg.1 h, Over.comp_left,
        ← Category.assoc, ← Category.assoc, hs0, Category.assoc, Category.assoc]
  letI : Algebra O S := o.toAlgebra
  have hβ : β0.comp P'.str = (algebraMap O S).comp x0 := hβ0.1
  refine ⟨(ptOf P' x0 hu β0 hβ).left, ?_⟩
  let b : T ⟶ torsion G' q := Over.homMk ((ptOf P' x0 hu β0 hβ).left ≫ (jH P' x0 hu hg.1 h).left) (by
    show ((ptOf P' x0 hu β0 hβ).left ≫ (jH P' x0 hu hg.1 h).left) ≫ (torsion G' q).hom = y ≫ (torsion G' q).hom
    rw [Category.assoc, Over.w (jH P' x0 hu hg.1 h), Over.w (ptOf P' x0 hu β0 hβ)]
    exact ho)
  have hb : b = yt := by
    refine GlobalTheory.KernelNoTorsion.torsion_hom_ext (Over.OverMorphism.ext (hg.1.hom_ext ?_ ?_))
    · have e1 : (b ≫ torsion.ι G' q).left = (ptOf P' x0 hu β0 hβ ≫ aH P' x0 hu hg.1).left := by
        show (ptOf P' x0 hu β0 hβ).left ≫ (jH P' x0 hu hg.1 h).left ≫ (torsion.ι G' q).left = _
        rw [← Over.comp_left, jH_ι]
        rfl
      rw [e1, ptOf_aH_π, hβ0.2]
      show y ≫ (torsion.ι G' q).left ≫ π = (y ≫ (torsion.ι G' q).left) ≫ π
      rw [Category.assoc]
    · rw [Over.w (b ≫ torsion.ι G' q), Over.w (yt ≫ torsion.ι G' q)]
  exact congrArg (fun z => z.left) hb
end GlobalTheory.FinPartAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderDeformationPointsDifferEpsAllOpensStatement
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
theorem _root_.GlobalTheory.T.firstOrderDeformation_points_differ_eps_allOpens : ∀ {K : Type} [Field K] {A : Over (Sp K)} {A' : Over (Sp (DualNumber K))} {i : A.left ⟶ A'.left} (hi : i ≫ A'.hom = A.hom ≫ GlobalTheory.DeRham.epsRed K) {X Z : Scheme.{0}} {h : Z ⟶ X} {y1 : Sp (DualNumber K) ⟶ X} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z} (hm' : IsPullback m' A'.hom h y1) (him : i ≫ m' = m) (U : X.affineOpens) (hU' : ⊤ ≤ y1 ⁻¹ᵁ U.1) (Ω : Z.affineOpens) (hΩ : Ω.1 ≤ h ⁻¹ᵁ U.1) {B : Type} [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω.1)) (S : Sp (DualNumber B) ⟶ A.left) (hS : S ≫ A.hom = spMap ((algebraMap B (DualNumber B)).comp (baseMap K B))) (hSx : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ S = x) (l₁ l₂ : Sp B ⟶ A'.left) (hl₁ : l₁ ≫ A'.hom = spMap (algebraMap (DualNumber K) B)) (hl₂ : l₂ ≫ A'.hom = spMap (algebraMap (DualNumber K) B)) (hΩ₁ : ⊤ ≤ (l₁ ≫ m') ⁻¹ᵁ Ω.1) (hΩ₂ : ⊤ ≤ (l₂ ≫ m') ⁻¹ᵁ Ω.1) (h₂ : ∀ f, ∃ c : B, valR (l₂ ≫ m') Ω.1 f = valR (x ≫ m) Ω.1 f + algebraMap (DualNumber K) B DualNumber.eps * c) (h₁₂ : ∀ f, valR (l₁ ≫ m') Ω.1 f - valR (l₂ ≫ m') Ω.1 f = algebraMap (DualNumber K) B DualNumber.eps * (valR (S ≫ m) Ω.1 f).snd) (O : A'.left.Opens) (hxO : ⊤ ≤ x ⁻¹ᵁ (i ⁻¹ᵁ O)) (f : Γ(A'.left, O)), valR l₁ O f - valR l₂ O f = algebraMap (DualNumber K) B DualNumber.eps * (valR S (i ⁻¹ᵁ O) ((i.app O).hom f)).snd := by
  first | exact @GlobalTheory.CechKS.valR_sub_eq_eps_mul_of_affine | exact GlobalTheory.CechKS.valR_sub_eq_eps_mul_of_affine | (intros; apply GlobalTheory.CechKS.valR_sub_eq_eps_mul_of_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleBaseChangeStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_base_change : ∀ (B Y B' : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ g : B' ⟶ B, IsFlagBundle (Limits.pullback.snd π g) (fun a => (Scheme.Modules.pullback g).obj (E a)) r (fun a => FlagBaseChange.pullFlag π g (fl a)) := by
  first | exact @GlobalTheory.FlagBaseChangeStable.isFlagBundle_pullback | exact GlobalTheory.FlagBaseChangeStable.isFlagBundle_pullback | (intros; apply GlobalTheory.FlagBaseChangeStable.isFlagBundle_pullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleGluesFromCoverStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_glues_from_cover : ∀ (B : Scheme.{0}) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → (∀ x : B, ∃ U : B.Opens, x ∈ U ∧ ∃ (Y : Scheme.{0}) (π : Y ⟶ U.toScheme) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj ((Scheme.Modules.pullback U.ι).obj (E a))) (r a)), IsFlagBundle π (fun a => (Scheme.Modules.pullback U.ι).obj (E a)) r fl) → ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl := by
  first | exact @GlobalTheory.FlagGlue.exists_isFlagBundle_of_cover | exact GlobalTheory.FlagGlue.exists_isFlagBundle_of_cover | (intros; apply GlobalTheory.FlagGlue.exists_isFlagBundle_of_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleIntegralBaseStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_integral_base : ∀ (Y Y₁ : Scheme.{0}) (ρ : Y ⟶ Y₁) (E₁ : Y₁.Modules) (fl₁ : Vert.Flag ((Scheme.Modules.pullback ρ).obj E₁) 2),
    IsIntegral Y → GlobalTheory.VB.IsVB E₁ 2 → IsFlagBundle ρ (fun _ : Unit => E₁) (fun _ => 2) (fun _ => fl₁) → IsIntegral Y₁ := by
  first | exact @GlobalTheory.FlagBase.isIntegral_base | exact GlobalTheory.FlagBase.isIntegral_base | (intros; apply GlobalTheory.FlagBase.isIntegral_base <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProjectiveOverBase
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

namespace GlobalTheory.FlagProj

theorem isProjOver_of_isFlagBundle : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (π : Y ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsProjOver q → (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → IsProjOver (π ≫ q) := by
  intro k _ _ B Y q π ι _ E r fl hq hE hY
  obtain ⟨Y₀, π₀, fl₀, h₀, hp₀⟩ := GlobalTheory.T.flag_bundle_product_of_each k B q ι E r hq fun a => GlobalTheory.T.exists_flag_bundle_proj_vector_bundle k B q (E a) (r a) hq (hE a)
  obtain ⟨e, he⟩ := GlobalTheory.T.flag_bundle_unique_up_to_iso B Y Y₀ π π₀ ι E r fl fl₀ hY h₀
  obtain ⟨N, φ, hφ, w⟩ := hp₀
  exact ⟨N, e.hom ≫ φ, inferInstance, by rw [Category.assoc, w, ← Category.assoc, he]⟩

end GlobalTheory.FlagProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePullbackBaseChangeStatement
section
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CovTest GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_pullback_base_change : ∀ (B Y B' : Scheme.{0}) (π : Y ⟶ B) (g : B' ⟶ B) (ι : Type) (E : ι → B.Modules) (n : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)), IsFlagBundle π E n fl →
    IsFlagBundle (pullback.snd π g) (fun a => (Scheme.Modules.pullback g).obj (E a)) n (fun a => bcFlag π g (fl a)) := by
  first | exact @GlobalTheory.CovTest.BCFlag.isFlagBundle_baseChange | exact GlobalTheory.CovTest.BCFlag.isFlagBundle_baseChange | (intros; apply GlobalTheory.CovTest.BCFlag.isFlagBundle_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleTransportAlongIsoStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_transport_along_iso : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (E E' : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) (e : ∀ a, E a ≅ E' a), IsFlagBundle π E r fl → IsFlagBundle π E' r (fun a => (fl a).ofIso ((Scheme.Modules.pullback π).mapIso (e a))) := by
  first | exact @GlobalTheory.FlagIsoBundle.isFlagBundle_of_iso | exact GlobalTheory.FlagIsoBundle.isFlagBundle_of_iso | (intros; apply GlobalTheory.FlagIsoBundle.isFlagBundle_of_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFramesTriangularChange
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

namespace GlobalTheory.FlagCell

theorem Spans.exists_basis {X : Scheme.{0}} {F : X.Modules} {m : ℕ} {fl : Vert.Flag F m} {V : X.Opens}
    {v : Fin m → Γ(F, V)} (h : Spans fl V v) :
    ∃ b : Module.Basis (Fin m) Γ(X, V) Γ(F, V), ∀ j, b j = v j := by
  obtain ⟨s, hs, e⟩ := h (Fin.last m)
  have hf := hs.map_iso (fl.ι (Fin.last m))
  refine ⟨hf.basis le_rfl, fun j => ?_⟩
  refine (hf.basis_apply le_rfl j).trans ((GlobalTheory.Twist.resM_self _ _).trans ((e j).trans ?_))
  rfl

theorem Spans.mem_span {X : Scheme.{0}} {F : X.Modules} {m : ℕ} {fl : Vert.Flag F m} {V : X.Opens}
    {v v' : Fin m → Γ(F, V)} (h : Spans fl V v) (h' : Spans fl V v') (j : Fin m) :
    v' j ∈ Submodule.span Γ(X, V) (v '' {k | k ≤ j}) := by
  obtain ⟨s, hs, e⟩ := h j.succ
  obtain ⟨s', -, e'⟩ := h' j.succ
  let i : Fin (j.succ : ℕ) := ⟨j, by simp⟩
  have hj : v' j = GlobalTheory.QCoh.appLinear (fl.ι j.succ) V (s' i) := (e' i).symm
  rw [hj, ← (hs.basis le_rfl).sum_repr (s' i), map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.castLE j.succ.is_le k, ?_, ?_⟩)
  · have := k.2
    simp only [Fin.val_succ] at this
    change (k : ℕ) ≤ j
    omega
  · rw [hs.basis_apply, GlobalTheory.Twist.resM_self]
    exact (e k).symm

theorem spans_change : ∀ (X : Scheme.{0}) (F : X.Modules) (m : ℕ) (fl : Vert.Flag F m) (V : X.Opens) (v v' : Fin m → Γ(F, V)), Spans fl V v → Spans fl V v' → ∃ M : Matrix (Fin m) (Fin m) Γ(X, V), M.BlockTriangular id ∧ IsUnit M.det ∧ ∀ j, v' j = ∑ k, M k j • v k := by
  intro X F m fl V v v' h h'
  obtain ⟨b, hb⟩ := h.exists_basis
  obtain ⟨b', hb'⟩ := h'.exists_basis
  have e : ⇑b = v := funext hb
  have e' : ⇑b' = v' := funext hb'
  refine ⟨b.toMatrix v', fun i j hij => ?_, ?_, fun j => ?_⟩
  · have hm := h.mem_span h' j
    rw [← e, Module.Basis.mem_span_image] at hm
    rw [Module.Basis.toMatrix_apply]
    by_contra hne
    exact absurd (hm (Finsupp.mem_support_iff.2 hne)) (not_le.2 hij)
  · rw [← e']
    exact b.isUnit_det b'
  · rw [← e]
    exact (b.sum_toMatrix_smul_self v' j).symm

end GlobalTheory.FlagCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagLocallyAdaptedAffineFrame
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB GlobalTheory.FlagZ GlobalTheory

set_option autoImplicit false
noncomputable section

open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply injective_app_of_mono exact_app_of_exact_of_mono)

namespace GlobalTheory.FlagZ.Loc

theorem isFrame_snoc_of_exact {X : Scheme.{0}} {U : X.Opens}
    {S : ShortComplex X.Modules} (hS : S.Exact) [Mono S.f] {m : ℕ}
    (a : Fin m → Γ(S.X₁, U)) (b : Γ(S.X₂, U)) (ha : IsFrame a)
    (hb : IsFrame fun _ : Fin 1 => S.g.app U b) :
    IsFrame (Fin.snoc (fun i => S.f.app U (a i)) b : Fin (m + 1) → Γ(S.X₂, U)) := by
  intro V h
  have hex := exact_app_of_exact_of_mono hS V
  have hlc : ∀ c : Fin (m + 1) → Γ(X, V),
      Fintype.linearCombination Γ(X, V) (fun i => resM S.X₂ h
        ((Fin.snoc (fun i => S.f.app U (a i)) b : Fin (m + 1) → Γ(S.X₂, U)) i)) c =
      appLinear S.f V (Fintype.linearCombination Γ(X, V) (fun i => resM S.X₁ h (a i))
        (fun i => c i.castSucc)) + c (Fin.last m) • resM S.X₂ h b := by
    intro c
    simp only [Fintype.linearCombination_apply, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
      Fin.snoc_last, map_sum, map_smul, appLinear_apply, app_resM]
  have hb1 : ∀ y : Γ(X, V), Fintype.linearCombination Γ(X, V)
      (fun i : Fin 1 => resM S.X₃ h ((fun _ : Fin 1 => S.g.app U b) i)) (fun _ => y) =
      appLinear S.g V (y • resM S.X₂ h b) := by
    intro y
    simp [Fintype.linearCombination_apply, appLinear_apply, app_resM]
  refine ⟨(injective_iff_map_eq_zero _).2 fun c hc => ?_, fun s => ?_⟩
  · rw [hlc] at hc
    have h1 := congrArg (appLinear S.g V) hc
    rw [map_add, appLinear_apply S.f, appLinear_apply S.g, hex.apply_apply_eq_zero, zero_add,
      map_zero, ← hb1] at h1
    have h2 : (fun _ : Fin 1 => c (Fin.last m)) = 0 :=
      (injective_iff_map_eq_zero _).1 (hb V h).1 _ h1
    have hl : c (Fin.last m) = 0 := congrFun h2 0
    rw [hl, zero_smul, add_zero, appLinear_apply] at hc
    have h3 := (injective_iff_map_eq_zero _).1 (ha V h).1 _
      (injective_app_of_mono S.f V (hc.trans (map_zero _).symm))
    funext i
    refine Fin.lastCases hl (fun j => congrFun h3 j) i
  · obtain ⟨y, hy⟩ := (hb V h).2 (S.g.app V s)
    have hy' : Fintype.linearCombination Γ(X, V)
        (fun i : Fin 1 => resM S.X₃ h ((fun _ : Fin 1 => S.g.app U b) i)) (fun _ => y 0) =
        S.g.app V s := by
      rw [← hy]; congr 1; funext i; rw [Fin.fin_one_eq_zero i]
    rw [hb1, appLinear_apply] at hy'
    obtain ⟨x, hx⟩ := (hex (s - y 0 • resM S.X₂ h b)).1
      (by rw [map_sub, ← hy', sub_self])
    obtain ⟨c, hc⟩ := (ha V h).2 x
    refine ⟨Fin.snoc c (y 0), ?_⟩
    rw [hlc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [show (fun i => c i) = c from rfl, hc, appLinear_apply, hx, sub_add_cancel]

theorem exists_nested_frames {X : Scheme.{0}} {E : X.Modules} {N : ℕ} (fl : Vert.Flag E N)
    (t : X) (k : Fin (N + 1)) :
    ∃ V : X.Opens, t ∈ V ∧ ∃ u : Fin k → Γ(fl.F k, V), IsFrame u ∧
      ∀ (l : Fin (N + 1)) (hl : (l : ℕ) ≤ k), ∃ s : Fin l → Γ(fl.F l, V), IsFrame s ∧
        ∀ j, (fl.ι l).app V (s j) = (fl.ι k).app V (u (Fin.castLE hl j)) := by
  induction k using Fin.induction with
  | zero =>
    obtain ⟨V, e, ht, he⟩ := fl.isVB 0 t
    refine ⟨V, ht, e, he, fun l hl => ?_⟩
    obtain rfl : l = 0 := Fin.ext (by simpa using hl)
    exact ⟨e, he, fun j => rfl⟩
  | succ i ih =>
    obtain ⟨V, htV, u, hu, hs⟩ := ih
    obtain ⟨U', c, htU', hc⟩ := fl.isVB_gr i t
    obtain ⟨W, hW, htW, b, hb⟩ := exists_app_eq_of_epi (fl.π i)
      (resM _ (inf_le_right : V ⊓ U' ≤ U') (c 0)) (show t ∈ V ⊓ U' from ⟨htV, htU'⟩)
    have hWV : W ≤ V := hW.trans inf_le_left
    let S := ShortComplex.mk (fl.step i) (fl.π i) (Limits.cokernel.condition _)
    have hS : S.Exact := ShortComplex.exact_cokernel (fl.step i)
    have hbf : IsFrame fun _ : Fin 1 => S.g.app W b := by
      convert hc.res (hW.trans inf_le_right) using 1
      funext j
      rw [Fin.fin_one_eq_zero j]
      exact hb.trans (resM_resM _ _ _)
    have hstep : ∀ x, (fl.ι i.succ).app W ((fl.step i).app W x) = (fl.ι i.castSucc).app W x :=
      fun x => (QCoh.app_app _ _ _ _).trans (by rw [fl.step_ι])
    refine ⟨W, htW, Fin.snoc (fun j => (fl.step i).app W (resM _ hWV (u j))) b,
      isFrame_snoc_of_exact (S := S) hS _ b (hu.res hWV) hbf, fun l hl => ?_⟩
    by_cases heq : (l : ℕ) = i.succ
    · obtain rfl : l = i.succ := Fin.ext heq
      exact ⟨_, isFrame_snoc_of_exact (S := S) hS _ b (hu.res hWV) hbf, fun j => rfl⟩
    · have hl' : (l : ℕ) ≤ i.castSucc := by
        simp only [Fin.val_succ, Fin.val_castSucc] at hl heq ⊢; omega
      obtain ⟨s, hsf, hsj⟩ := hs l hl'
      refine ⟨fun j => resM _ hWV (s j), hsf.res hWV, fun j => ?_⟩
      rw [app_resM (fl.ι l) hWV, hsj j, ← app_resM]
      show _ = (fl.ι i.succ).app W ((Fin.snoc (fun j => (fl.step i).app W (resM _ hWV (u j))) b :
        Fin ((i.castSucc : ℕ) + 1) → Γ(fl.F i.succ, W)) (Fin.castSucc (Fin.castLE hl' j)))
      rw [Fin.snoc_castSucc, hstep]

theorem isFrame_stdSec {N : ℕ} {T : Scheme.{0}} (g : T ⟶ Sp ℤ) (V : T.Opens) :
    IsFrame fun i : Fin N => QCoh.pullbackSections g (Taut.stdE N) (by simp : V ≤ g ⁻¹ᵁ ⊤)
      (freeFrame (Sp ℤ) (Fin N) i) := by
  haveI : (Taut.stdE N).IsQuasicoherent := (isVB_freeModule_fin (Sp ℤ) N).isQuasicoherent
  have := ((isFrame_freeFrame (Sp ℤ) (Fin N)).pullback g).res (by simp : V ≤ g ⁻¹ᵁ ⊤)
  rw [show (fun i : Fin N => QCoh.pullbackSections g (Taut.stdE N) (by simp : V ≤ g ⁻¹ᵁ ⊤)
      (freeFrame (Sp ℤ) (Fin N) i)) = fun i => resM _ (by simp : V ≤ g ⁻¹ᵁ ⊤)
      (QCoh.pullbackSections g (Taut.stdE N) le_rfl (freeFrame (Sp ℤ) (Fin N) i)) from
      funext fun i => (QCoh.res_pullbackSections _ _ _ _ _).symm]
  exact this

theorem exists_GL_colSecOn {N : ℕ} {T : Scheme.{0}} (g : T ⟶ Sp ℤ) (V : T.Opens)
    (v : Fin N → Γ((Scheme.Modules.pullback g).obj (Taut.stdE N), V)) (hv : IsFrame v) :
    ∃ G : GL (Fin N) Γ(T, V), ∀ j, colSecOn g V G.1 j = v j := by
  classical
  have he := isFrame_stdSec (N := N) g V
  letI := (he.basis le_rfl).invertibleToMatrix (hv.basis le_rfl)
  refine ⟨unitOfInvertible ((he.basis le_rfl).toMatrix (hv.basis le_rfl)), fun j => ?_⟩
  have := (he.basis le_rfl).sum_toMatrix_smul_self (hv.basis le_rfl) j
  simp only [IsFrame.basis_apply, resM_self] at this
  rw [val_unitOfInvertible]
  exact this

theorem resM_colSecOn {N : ℕ} {T : Scheme.{0}} (g : T ⟶ Sp ℤ) {V W : T.Opens} (h : W ≤ V)
    (M : Matrix (Fin N) (Fin N) Γ(T, V)) (j : Fin N) :
    resM _ h (colSecOn g V M j) = colSecOn g W (M.map (resG T h)) j := by
  simp only [colSecOn, map_sum, resM_smul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
  exact QCoh.res_pullbackSections _ _ _ _ _

theorem exists_adapted : ∀ {ι : Type} [Fintype ι] {N : ℕ} {T : Scheme.{0}} (g : T ⟶ Sp ℤ)
    (fl' : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback g).obj (Taut.stdE N)) N) (t : T),
    ∃ V : T.Opens, t ∈ V ∧ IsAffineOpen V ∧ ∃ G : ι → GL (Fin N) Γ(T, V), Loc.Adapted g fl' V G := by
  intro ι _ N T g fl' t
  have one : ∀ a, ∃ V : T.Opens, t ∈ V ∧ ∃ G : GL (Fin N) Γ(T, V), ∀ l : Fin (N + 1),
      ∃ s : Fin l → Γ((fl' a).F l, V), IsFrame s ∧
        ∀ j, ((fl' a).ι l).app V (s j) = colSecOn g V G.1 (Fin.castLE l.is_le j) := by
    intro a
    obtain ⟨V, htV, u, hu, hs⟩ := exists_nested_frames (fl' a) t (Fin.last N)
    obtain ⟨G, hG⟩ := exists_GL_colSecOn g V (fun j => ((fl' a).ι (Fin.last N)).app V (u j))
      (hu.map_iso _)
    refine ⟨V, htV, G, fun l => ?_⟩
    obtain ⟨s, hsf, hsj⟩ := hs l l.is_le
    exact ⟨s, hsf, fun j => (hsj j).trans (hG _).symm⟩
  choose V htV G hG using one
  have ht0 : t ∈ Finset.univ.inf V := by
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_finset_inf]
    simpa using htV
  obtain ⟨W, hW, htW, hle⟩ := QCoh.exists_affine_mem_le t ht0
  have hWa (a : ι) : W ≤ V a := hle.trans (Finset.inf_le (Finset.mem_univ a))
  refine ⟨W, htW, hW, fun a => Units.map (RingHom.mapMatrix (resG T (hWa a))).toMonoidHom (G a),
    fun a l => ?_⟩
  obtain ⟨s, hsf, hsj⟩ := hG a l
  refine ⟨fun j => resM _ (hWa a) (s j), hsf.res (hWa a), fun j => ?_⟩
  dsimp only
  rw [app_resM, hsj, resM_colSecOn]
  rfl

end GlobalTheory.FlagZ.Loc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameMatrixUnitsIrreducibleStatement
section
open CategoryTheory AlgebraicGeometry GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_matrix_units_irreducible : ∀ (L : Type) [Field L] (ι : Type) [Fintype ι] (n : ι → ℕ) (A : ∀ a, Matrix (Fin (n a)) (Fin (n a)) L), (∀ a, IsUnit (A a).det) → ∃ (T : Scheme.{0}) (c : T ⟶ Spec (CommRingCat.of L)) (t₁ t₂ : Spec (CommRingCat.of L) ⟶ T) (_ : t₁ ≫ c = 𝟙 _) (_ : t₂ ≫ c = 𝟙 _) (B : ∀ a, Matrix (Fin (n a)) (Fin (n a)) Γ(T, ⊤)), IrreducibleSpace T ∧ (∀ a, IsUnit (B a)) ∧ (∀ a i j, t₁.appTop (B a i j) = (Scheme.ΓSpecIso (CommRingCat.of L)).inv ((1 : Matrix (Fin (n a)) (Fin (n a)) L) i j)) ∧ (∀ a i j, t₂.appTop (B a i j) = (Scheme.ΓSpecIso (CommRingCat.of L)).inv (A a i j)) := by
  first | exact @GlobalTheory.GLPath.exists_path | exact GlobalTheory.GLPath.exists_path | (intros; apply GlobalTheory.GLPath.exists_path <;> assumption)
end

