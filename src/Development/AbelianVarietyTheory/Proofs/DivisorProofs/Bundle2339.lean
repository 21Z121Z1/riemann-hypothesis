import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2279
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0893
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelHomUnique
section
noncomputable section

namespace GlobalTheory.UPel.HT.Gen.Unique

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

theorem gObjMap_id {b : GBase G R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : GObj b N s) :
    Nonempty (GObjMap o o (𝟙 S)) :=
  ⟨{ φ := 𝟙 _
     φ₂ := 𝟙 _
     cart := GlobalTheory.SiegLower.isGrpPullback_id o.A
     sq := ⟨by simp, by simp⟩
     act := fun c => by simp
     pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB
     eta := fun y => by simp }⟩

private theorem lbIso_pull_comp_of_lbIso {X Y Z : Scheme.{0}} {M : LB X} {P : LB Y} {Q : LB Z} {a : X ⟶ Y} {c : Y ⟶ Z}
    (H₁ : LBIso M (P.pull a)) (H₂ : LBIso P (Q.pull c)) (hM : M.IsLB) (hP : P.IsLB) (hQ : Q.IsLB) :
    LBIso M (Q.pull (a ≫ c)) := by
  have E : LBIso (P.pull a) ((Q.pull c).pull a) := SiegelDescent.lbIso_square hP hQ H₂ rfl
  have F : LBIso ((Q.pull c).pull a) ((Q.pull (a ≫ c)).pull (𝟙 X)) :=
    GlobalTheory.FiniteAmple.lbIso_pull_pull c hQ (g := a) (g' := 𝟙 X) (f' := a ≫ c) (by rw [Category.id_comp])
  have hPa := pull_isLB hP a
  have hQc := pull_isLB hQ (a ≫ c)
  exact LBIso.trans hM hPa hQc H₁ (LBIso.trans hPa (pull_isLB (pull_isLB hQ c) a) hQc E
    (LBIso.trans (pull_isLB (pull_isLB hQ c) a) (pull_isLB hQc (𝟙 X)) hQc F (GlobalTheory.SiegLower.lbIso_pull_id hQc).symm))

theorem gObjMap_comp {b : GBase G R} {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R}
    {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂} {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (h₁ : GObjMap o₁ o₂ f) (h₂ : GObjMap o₂ o₃ g) : Nonempty (GObjMap o₁ o₃ (f ≫ g)) :=
  ⟨{ φ := h₁.φ ≫ h₂.φ
     φ₂ := h₁.φ₂ ≫ h₂.φ₂
     cart := IsGrpPullback.comp h₁.cart h₂.cart
     sq := ⟨by rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc],
       by rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]⟩
     act := fun c => by rw [← Category.assoc, h₁.act c, Category.assoc, h₂.act c, ← Category.assoc]
     pol := lbIso_pull_comp_of_lbIso h₁.pol h₂.pol o₁.isLB o₂.isLB o₃.isLB
     eta := fun y => by rw [← Category.assoc, h₁.eta y, Category.assoc, h₂.eta y, ← Category.assoc] }⟩

end GlobalTheory.UPel.HT.Gen.Unique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorValueLinCombChangeOfCharts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge

noncomputable section
namespace GlobalTheory.MBLow.TanGauge

theorem valR_linComb_g_factor {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    {A : Type} [CommRing A] (y : Sp A ⟶ Y) (j j' : K → L.ι)
    (hh : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) (k : K) :
    valR y (LB.wchart L φ j ⊓ LB.wchart L φ j')
      ((res (le_inf (inf_le_left.trans (LB.wchart_le L φ j k))
      (inf_le_right.trans (LB.wchart_le L φ j' k)) :
        LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)))
      (pullU (φ k) _ (L.g (j k) (j' k)))) ^ (ε k)).val = trV L (y ≫ φ k) (j k) (j' k) (ε k) := by
  have h0 : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)) :=
    le_inf (inf_le_left.trans (LB.wchart_le L φ j k)) (inf_le_right.trans (LB.wchart_le L φ j' k))
  have key : (res h0 (pullU (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)))) ^ (ε k) =
      res h0 (pullU (φ k) (L.U (j k) ⊓ L.U (j' k)) ((L.g (j k) (j' k)) ^ (ε k))) :=
    ((congrArg (res h0) (map_zpow (pullU (φ k) (L.U (j k) ⊓ L.U (j' k))) _ _)).trans
      (map_zpow (res h0) _ _)).symm
  refine (congrArg (fun u => valR y (LB.wchart L φ j ⊓ LB.wchart L φ j') (Units.val u)) key).trans ?_
  have e1 := GlobalTheory.ZH.CrdCalc.valR_res y h0 hh
      (((φ k).app (L.U (j k) ⊓ L.U (j' k))).hom ((L.g (j k) (j' k)) ^ (ε k)).val)
  refine Eq.trans ?_ (e1.trans ?_)
  · rfl
  · unfold trV
    exact GlobalTheory.ZH.EvCrd.valR_comp y (φ k) _ (hh.trans (y.preimage_mono h0)) _

theorem valR_gen_linComb : ∀ {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ Y) (j j' : K → L.ι),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j → ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j' →
    valR y (LB.wchart L φ j) (t.s j).val =
      (∏ k, trV L (y ≫ φ k) (j k) (j' k) (ε k)) * valR y (LB.wchart L φ j') (t.s j').val := by
  intro X Y L K _ φ ε t ht A _ y j j' h h'
  have hh : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j') := fun q hq => ⟨h hq, h' hq⟩
  have e : valR y (LB.wchart L φ j ⊓ LB.wchart L φ j')
      (res (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j) (t.s j)).val =
      valR y (LB.wchart L φ j ⊓ LB.wchart L φ j')
      ((show Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ from (LB.LinComb L φ ε).g j j').val *
        (res (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j') (t.s j')).val) :=
    congrArg (fun u => valR y (LB.wchart L φ j ⊓ LB.wchart L φ j') (Units.val u)) (ht j j')
  rw [GlobalTheory.ZH.CrdCalc.valR_mul y _ hh] at e
  have e1 := GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j) hh (t.s j).val
  have e2 := GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j') hh (t.s j').val
  have e3 : valR y (LB.wchart L φ j ⊓ LB.wchart L φ j') (show Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ from (LB.LinComb L φ ε).g j j').val =
      ∏ k, trV L (y ≫ φ k) (j k) (j' k) (ε k) := by
    change valR y (LB.wchart L φ j ⊓ LB.wchart L φ j') (Units.val (∏ k, _)) = _
    rw [Units.coe_prod, GlobalTheory.ZH.CrdCalc.valR_eq y _ hh, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← GlobalTheory.ZH.CrdCalc.valR_eq y _ hh]
    exact valR_linComb_g_factor L φ ε y j j' hh k
  rw [← e3]
  exact e1.symm.trans (e.trans (congrArg _ e2))

end GlobalTheory.MBLow.TanGauge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericGermFunctionFieldIsFractionRingAffineCharStatement
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
theorem _root_.GlobalTheory.T.genericGerm_functionField_isFractionRing_affineChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι → (letI := ρ.toAlgebra; IsFractionRing Γ(TF.Y.X, U.1) (X₀ TF.Y Z).functionField) ∧ ∀ a : c.F, ρ (constFn TF.Y.s U.1 a) = GlobalTheory.Cartier.constFn (s₀ TF.Y Z) a := by
  first | exact @GlobalTheory.GenFracChart.isFractionRing_and_const | exact GlobalTheory.GenFracChart.isFractionRing_and_const | (intros; apply GlobalTheory.GenFracChart.isFractionRing_and_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericTangentCoefficientsUniqueAffineOpenBasis
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv.GenUniq

open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (spMap_comp_spMap)

attribute [local instance] Over.cartesianMonoidalCategory

theorem dualMap_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) : Function.Injective (Formalism.L2.Pj.dualMap f) := by
  intro a b h
  have h1 := congrArg TrivSqZeroExt.fst h
  have h2 := congrArg TrivSqZeroExt.snd h
  simp only [Formalism.L2.Pj.dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.fst_add,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.snd_inr, zero_add] at h1 h2
  exact TrivSqZeroExt.ext (hf h1) (hf h2)

theorem exists_common_denom {A K : Type} [CommRing A] [Field K] (ρ : A →+* K)
    (hfr : ∀ x : K, ∃ a b : A, ρ b ≠ 0 ∧ x * ρ b = ρ a) {κ : Type} [Fintype κ] (c : κ → K) :
    ∃ (b : A) (a : κ → A), ρ b ≠ 0 ∧ ∀ i, ρ b * c i = ρ (a i) := by
  classical
  choose a b hb hab using hfr
  refine ⟨∏ i, b (c i), fun i => a (c i) * ∏ j ∈ Finset.univ.erase i, b (c j), ?_, fun i => ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hb _
  · rw [← Finset.mul_prod_erase Finset.univ (fun j => b (c j)) (Finset.mem_univ i), map_mul, map_mul, ← hab]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

def bcEps {A K : Type} [CommRing A] [CommRing K] (ρ : A →+* K) (x : Sp A ⟶ X) :
    tEpsG (spMap ρ ≫ x) ⟶ tEpsG x :=
  Over.homMk (spMap (Formalism.L2.Pj.dualMap ρ)) (by
    show spMap (Formalism.L2.Pj.dualMap ρ) ≫ spMap (algebraMap A (DualNumber A)) ≫ x =
      spMap (algebraMap K (DualNumber K)) ≫ spMap ρ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_alg])

theorem bcEps_smT {A K : Type} [CommRing A] [CommRing K] (ρ : A →+* K) (x : Sp A ⟶ X) (a : A)
    (v : tEpsG x ⟶ t.G) :
    bcEps ρ x ≫ smT x a v = smT (spMap ρ ≫ x) (ρ a) (bcEps ρ x ≫ v) := by
  apply Over.OverMorphism.ext
  show spMap (Formalism.L2.Pj.dualMap ρ) ≫ spMap (epsMul a) ≫ v.left =
    spMap (epsMul (ρ a)) ≫ spMap (Formalism.L2.Pj.dualMap ρ) ≫ v.left
  rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_epsMul]

theorem bcEps_combT {A K : Type} [CommRing A] [CommRing K] (ρ : A →+* K) (x : Sp A ⟶ X) {n : ℕ}
    (v : Fin n → (tEpsG x ⟶ t.G)) (a : Fin n → A) :
    bcEps ρ x ≫ combT x v a = combT (spMap ρ ≫ x) (fun i => bcEps ρ x ≫ v i) (fun i => ρ (a i)) := by
  let f : (tEpsG x ⟶ t.G) →* (tEpsG (spMap ρ ≫ x) ⟶ t.G) :=
    { toFun := fun u => bcEps ρ x ≫ u
      map_one' := MonObj.comp_one _
      map_mul' := fun u w => MonObj.comp_mul _ _ _ }
  have h := map_prod f (fun j => smT x (a j) (v j)) Finset.univ
  refine h.trans ?_
  exact Finset.prod_congr rfl fun i _ => bcEps_smT t ρ x (a i) (v i)

theorem coeff_unique {A K : Type} [CommRing A] [Field K] (ρ : A →+* K) (hinj : Function.Injective ρ)
    (hfr : ∀ x : K, ∃ a b : A, ρ b ≠ 0 ∧ x * ρ b = ρ a) (x : Sp A ⟶ X) {n : ℕ}
    (v : Fin n → (Sp (DualNumber A) ⟶ t.G.left)) (hv : ∀ i, IsTanAtG t x (v i))
    (hb : ∀ w, IsTanAtG t x w → ∃! cf : Fin n → A, IsCombAtG t x v cf w)
    (cf cf' : Fin n → K) (w : Sp (DualNumber K) ⟶ t.G.left)
    (h : IsCombAtG t (spMap ρ ≫ x) (fun i => spMap (Formalism.L2.Pj.dualMap ρ) ≫ v i) cf w)
    (h' : IsCombAtG t (spMap ρ ≫ x) (fun i => spMap (Formalism.L2.Pj.dualMap ρ) ≫ v i) cf' w) : cf = cf' := by
  let V : Fin n → (tEpsG x ⟶ t.G) := fun i => ovT (hv i)
  have e := (isCombAtG_iff t (spMap ρ ≫ x) (fun i => bcEps ρ x ≫ V i) cf w).1 h
  have e' := (isCombAtG_iff t (spMap ρ ≫ x) (fun i => bcEps ρ x ≫ V i) cf' w).1 h'
  have hc : combT (spMap ρ ≫ x) (fun i => bcEps ρ x ≫ V i) cf =
      combT (spMap ρ ≫ x) (fun i => bcEps ρ x ≫ V i) cf' := Over.OverMorphism.ext (e.trans e'.symm)
  obtain ⟨b, a, hb0, ha⟩ := exists_common_denom ρ hfr (Sum.elim cf cf')
  have hs := congrArg (smT (spMap ρ ≫ x) (ρ b)) hc
  rw [smT_combT, smT_combT] at hs
  have a1 : (fun j => ρ b * cf j) = fun j => ρ (a (Sum.inl j)) := funext fun j => ha (Sum.inl j)
  have a2 : (fun j => ρ b * cf' j) = fun j => ρ (a (Sum.inr j)) := funext fun j => ha (Sum.inr j)
  rw [a1, a2, ← bcEps_combT, ← bcEps_combT] at hs
  have hsep : IsSeparated t.G.hom := t.semi.separated
  have hdom : IsSchemeTheoreticallyDominant (spMap (Formalism.L2.Pj.dualMap ρ)) :=
    GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom _) (dualMap_injective ρ hinj)
  have hA : (combT x V fun j => a (Sum.inl j)).left = (combT x V fun j => a (Sum.inr j)).left :=
    GlobalTheory.ExtUnique.hom_ext_of_dominant t.G.hom
      ((Over.w (combT x V fun j => a (Sum.inl j))).trans (Over.w (combT x V fun j => a (Sum.inr j))).symm)
      (spMap (Formalism.L2.Pj.dualMap ρ)) (congrArg (fun φ => φ.left) hs)
  have ht : IsTanAtG t x (combT x V fun j => a (Sum.inl j)).left :=
    isTanAtG_of _ (combT_tan x V (fun j => smT_zero_ovT (hv j)) _)
  have haa : (fun j => a (Sum.inl j)) = fun j => a (Sum.inr j) :=
    (hb _ ht).unique ((isCombAtG_iff t x V _ _).2 rfl) ((isCombAtG_iff t x V _ _).2 hA.symm)
  funext j
  apply mul_left_cancel₀ hb0
  rw [congrFun a1 j, congrFun a2 j, congrFun haa j]

end GlobalTheory.LogKSDiv.GenUniq

namespace GlobalTheory.LogKSDiv

theorem generic_coeff_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (W : X.affineOpens) (K : Type) [Field K] (ρW : Γ(X, W.1) →+* K), Function.Injective ρW → (∀ x : K, ∃ a b : Γ(X, W.1), ρW b ≠ 0 ∧ x * ρW b = ρW a) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, W.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (GlobalTheory.LogKS.chart W) (v i)) → (∀ w, IsTanAtG t (GlobalTheory.LogKS.chart W) w → ∃! cf : Fin n → Γ(X, W.1), IsCombAtG t (GlobalTheory.LogKS.chart W) v cf w) → ∀ (cf cf' : Fin n → K) (w : Sp (DualNumber K) ⟶ t.G.left), IsCombAtG t (spMap ρW ≫ GlobalTheory.LogKS.chart W) (fun i => spMap (dualMap ρW) ≫ v i) cf w → IsCombAtG t (spMap ρW ≫ GlobalTheory.LogKS.chart W) (fun i => spMap (dualMap ρW) ≫ v i) cf' w → cf = cf' :=
  fun _ _ _ _ _ _ t W _ _ ρW hinj hfr _ v hv hb cf cf' w h h' =>
    GenUniq.coeff_unique t ρW hinj hfr (GlobalTheory.LogKS.chart W) v hv hb cf cf' w h h'

end GlobalTheory.LogKSDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIntegralOfIsOpenImmersionCompSurjec
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem geometricallyIntegral_of_isOpenImmersion_comp_surjective :
    ∀ (O Z T : Scheme.{0}) (j : O ⟶ Z) (f : Z ⟶ T) [IsOpenImmersion j] [GeometricallyIntegral f], Surjective (j ≫ f) → GeometricallyIntegral (j ≫ f) := by
  intro O Z T j f _ _ hs
  refine ⟨fun {K} _ y P fst snd h => ?_⟩
  have hZf : IsIntegral (pullback f y) :=
    GeometricallyIntegral.geometrically_isIntegral (f := f) y _ _ (IsPullback.of_hasPullback f y)
  let fst' : P ⟶ pullback f y := pullback.lift (fst ≫ j) snd (by rw [Category.assoc]; exact h.w)
  have sq : IsPullback fst fst' j (pullback.fst f y) := by
    refine IsPullback.of_bot (v₂₁ := pullback.snd f y) (v₂₂ := f) (h₃₁ := y) ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback f y)
    have e : fst' ≫ pullback.snd f y = snd := pullback.lift_snd _ _ _
    rw [e]; exact h
  have : IsOpenImmersion fst' := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq inferInstance
  have hsn : Surjective snd := MorphismProperty.of_isPullback (P := @Surjective) h hs
  have : Nonempty P := by
    obtain ⟨z, -⟩ := snd.surjective (Nonempty.some inferInstance : Spec (.of K))
    exact ⟨z⟩
  exact isIntegral_of_isOpenImmersion fst'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIrreducibleOpenIrreducible
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

theorem GlobalTheory.FlatModel.isIrreducible_of_geomIrr_of_le_basicOpen : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime],
    (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens),
    Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → GeomIrr s Xw → IsIrreducible (Xw : Set X) := by
  intro F _ _ V p hpr hpV X s Xw hXw hg
  have hirr := hg F V.subtype Subtype.val_injective
  set P := pullback (Xw.ι ≫ s) (spMap V.subtype)
  have hI := (IrreducibleSpace.isIrreducible_univ P).image (⇑(pullback.fst (Xw.ι ≫ s) (spMap V.subtype) ≫ Xw.ι))
    (Scheme.Hom.continuous _).continuousOn
  rw [Set.image_univ] at hI
  convert hI using 1
  have hdvr := (GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField V hpr.out.ne_zero hpV).1
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Pullback.range_fst]
  have key : ∀ x : (Xw : Scheme), (Xw.ι ≫ s) x ∈ Set.range (spMap V.subtype) := by
    intro x
    have hx : Xw.ι x ∈ X.basicOpen (p : Γ(X, ⊤)) := by
      apply hXw
      show Xw.ι x ∈ (Xw : Set X)
      rw [← Scheme.Opens.range_ι]
      exact ⟨x, rfl⟩
    have h1 : s (Xw.ι x) ∈ (Sp V).basicOpen (p : Γ(Sp V, ⊤)) := by
      rw [← Scheme.Hom.mem_preimage, Scheme.preimage_basicOpen_top, map_natCast]
      exact hx
    rw [basicOpen_eq_of_affine', map_natCast] at h1
    have hbot : (s (Xw.ι x)).asIdeal = ⊥ := by
      by_contra hne
      have hm := Ideal.IsPrime.isMaximal (s (Xw.ι x)).2 hne
      have he := IsLocalRing.eq_maximalIdeal hm
      obtain ⟨ha, hmem⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal (A := V)).1 hpV
      apply h1
      rw [he]
      convert hmem
      simp
    refine ⟨⟨⊥, Ideal.bot_prime⟩, ?_⟩
    rw [Scheme.Hom.comp_apply]
    refine PrimeSpectrum.ext ?_
    rw [hbot]
    exact (RingHom.ker_eq_bot_iff_eq_zero _).2 fun a ha => Subtype.ext ha
  have hu : (⇑(Xw.ι ≫ s) ⁻¹' Set.range ⇑(spMap V.subtype)) = Set.univ := Set.eq_univ_of_forall key
  rw [hu, Set.image_univ, Scheme.Opens.range_ι]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyIrreduciblePullbackIsoStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometrically_irreducible_pullback_iso : ∀ (V : Type) [CommRing V] (X X' : Scheme.{0}) (s : X ⟶ Sp V) (π : X' ⟶ X) (Xw O : X.Opens),
    Xw ≤ O → IsIso (π ∣_ O) → GeomIrr s Xw → GeomIrr (π ≫ s) (π ⁻¹ᵁ Xw) := by
  first | exact @GlobalTheory.FlatModel.geomIrr_preimage_of_isIso_restrict | exact GlobalTheory.FlatModel.geomIrr_preimage_of_isIso_restrict | (intros; apply GlobalTheory.FlatModel.geomIrr_preimage_of_isIso_restrict <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMorphismsIntoAffineOpenMilnorSquare
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.DualOpen

theorem glue_into_affineOpen (S : Scheme.{0}) [IsAffine S] (U T T₁ T₂ T₀ : Over S) (j₁ : T₁ ⟶ T) (j₂ : T₂ ⟶ T)
    (k₁ : T₀ ⟶ T₁) (k₂ : T₀ ⟶ T₂) (hM : Milnor j₁.left j₂.left k₁.left k₂.left) (V : U.left.Opens)
    (hV : IsAffineOpen V) (u₁ : T₁ ⟶ U) (u₂ : T₂ ⟶ U) (hk : k₁ ≫ u₁ = k₂ ≫ u₂)
    (h₁ : ∀ x, u₁.left x ∈ V) (h₂ : ∀ x, u₂.left x ∈ V) :
    ∃ u : T ⟶ U, j₁ ≫ u = u₁ ∧ j₂ ≫ u = u₂ := by
  haveI : IsAffine V.toScheme := hV
  have r₁ : Set.range u₁.left ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩; rw [Scheme.Opens.range_ι]; exact h₁ x
  have r₂ : Set.range u₂.left ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩; rw [Scheme.Opens.range_ι]; exact h₂ x
  set a₁ := IsOpenImmersion.lift V.ι u₁.left r₁ with ha₁
  set a₂ := IsOpenImmersion.lift V.ι u₂.left r₂ with ha₂
  have f₁ : a₁ ≫ V.ι = u₁.left := IsOpenImmersion.lift_fac _ _ _
  have f₂ : a₂ ≫ V.ι = u₂.left := IsOpenImmersion.lift_fac _ _ _
  have hk' : k₁.left ≫ a₁ = k₂.left ≫ a₂ := by
    rw [← cancel_mono V.ι, Category.assoc, Category.assoc, f₁, f₂]
    exact congrArg CommaMorphism.left hk
  have w : a₁.appTop ≫ k₁.left.appTop = a₂.appTop ≫ k₂.left.appTop := by
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, hk']
  set b := hM.cart.lift a₁.appTop a₂.appTop w with hb
  have b₁ : b ≫ j₁.left.appTop = a₁.appTop := hM.cart.lift_fst _ _ _
  have b₂ : b ≫ j₂.left.appTop = a₂.appTop := hM.cart.lift_snd _ _ _
  haveI := hM.aff
  let a : T.left ⟶ V.toScheme := T.left.toSpecΓ ≫ Spec.map b ≫ V.toScheme.isoSpec.inv
  have e₁ : j₁.left ≫ a = a₁ := by
    simp only [a]
    rw [Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc, b₁, ← Scheme.toSpecΓ_naturality_assoc,
      ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]
  have e₂ : j₂.left ≫ a = a₂ := by
    simp only [a]
    rw [Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc, b₂, ← Scheme.toSpecΓ_naturality_assoc,
      ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]
  have hover : (a ≫ V.ι) ≫ U.hom = T.hom := by
    apply ext_of_isAffine
    apply hM.cart.hom_ext
    · rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]; congr 1
      simp only [Category.assoc]; rw [reassoc_of% e₁, reassoc_of% f₁, Over.w u₁, Over.w j₁]
    · rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]; congr 1
      simp only [Category.assoc]; rw [reassoc_of% e₂, reassoc_of% f₂, Over.w u₂, Over.w j₂]
  refine ⟨Over.homMk (a ≫ V.ι) hover, ?_, ?_⟩
  · ext1; simp only [Over.comp_left, Over.homMk_left]; rw [← Category.assoc, e₁, f₁]
  · ext1; simp only [Over.comp_left, Over.homMk_left]; rw [← Category.assoc, e₂, f₂]

end GlobalTheory.DualOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueOpenChartsAdditiveFamiliesRepresenting
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem same_id_map {S : Scheme.{0}} {A T U : Over S} [GrpObj A] {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left}
    (hN : Fam A N) (hM : Fam A M) (u : T ⟶ U) :
    Same A N M (𝟙 T) u ↔ (addF A).map u.op (famCls hM) = famCls hN := by
  rw [same_iff_map hN hM, op_id, CategoryTheory.Functor.map_id]
  exact eq_comm

theorem glue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (Ix : Type) (U : Ix → Over S) (M : ∀ i, LB (A ⊗ U i).left), (∀ i, IsChart A (M i)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (N : LB (A ⊗ Over.mk s).left), Fam A N → ∃ (i : Ix) (u : Over.mk s ⟶ U i), Same A N (M i) (𝟙 _) u) → ∃ (B : Over S) (P : LB (A ⊗ B).left) (j : ∀ i, U i ⟶ B), Rep A (toUnit B) P ∧ (∀ i, IsOpenImmersion (j i).left) ∧ (∀ p : B.left, ∃ i, p ∈ Set.range (j i).left) ∧ ∀ i, Same A (M i) P (𝟙 _) (j i) := by
  intro S A _ hA Ix U M hM hcov
  obtain ⟨B, x, hu, j, ho, hc, hj⟩ := GlobalTheory.RepOver.representable_over S (addF A) (GlobalTheory.PicGlue.addF_separated S A hA) (GlobalTheory.PicGlue.addF_glue S A hA) Ix U
    (fun i ↦ famCls (hM i).fam)
    (fun i Y u u' h ↦ (hM i).inj Y u u' ((same_iff_map (hM i).fam (hM i).fam u u').2 h))
    (fun i T y ↦ by
      obtain ⟨N, hN, rfl⟩ := famCls_surj y
      obtain ⟨W, hW⟩ := (hM i).chart T N hN
      exact ⟨W, fun Y a ↦ (exists_congr fun u ↦ (same_iff_map hN (hM i).fam a u).symm).trans (hW Y a)⟩)
    (fun T y p ↦ by
      obtain ⟨K, _, _, s, hs⟩ := GlobalTheory.exists_geomPoint_through T.left p
      let a : Over.mk (s ≫ T.hom) ⟶ T := Over.homMk s rfl
      obtain ⟨N, hN, e⟩ := famCls_surj ((addF A).map a.op y)
      obtain ⟨i, u, h⟩ := hcov K (s ≫ T.hom) N hN
      exact ⟨i, _, a, u, hs, e.symm.trans ((same_id_map hN (hM i).fam u).1 h).symm⟩)
  obtain ⟨P, hP, rfl⟩ := famCls_surj x
  refine ⟨B, P, j, ⟨hP, fun T t N hN ↦ ?_⟩, ho, hc, fun i ↦ (same_id_map (hM i).fam hP _).2 (hj i)⟩
  obtain ⟨g, hg, hg'⟩ := hu T (famCls hN)
  have k : ∀ g : T ⟶ B, LBIso N (ev P (fst A T) (snd A T ≫ g)) ↔ (addF A).map g.op (famCls hP) = famCls hN :=
    fun g ↦ (same_id_iff hN.isLB hP.isLB g).symm.trans (same_id_map hN hP g)
  exact ⟨g, ⟨toUnit_unique _ _, (k g).2 hg⟩, fun g' h ↦ hg' g' ((k g').1 h.2)⟩

end GlobalTheory.PicGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodOfFiniteSurjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.FiniteSurjDim

theorem eq_of_finite_surjective {k : Type} [Field k] {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    (p : Y ⟶ Spec (CommRingCat.of k)) [Nonempty X] {a b : ℕ} (ha : SmoothOfRelativeDimension a (f ≫ p))
    (hb : SmoothOfRelativeDimension b p) : a = b := by
  have : Nonempty Y := ⟨f (Classical.arbitrary X)⟩
  have h1 := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth (f ≫ p) a ha
  have h2 := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth p b hb
  have c1 : topologicalKrullDim Y ≤ topologicalKrullDim X :=
    GlobalTheory.PosBaseChange.dim_le_of_isClosedMap f.isClosedMap f.surjective
  have c2 : topologicalKrullDim X ≤ topologicalKrullDim Y :=
    GlobalTheory.PosBaseChange.dim_le_of_isDiscrete f.continuous fun y => f.isDiscrete_preimage_singleton y
  rw [h1, h2] at c1 c2
  exact_mod_cast le_antisymm c2 c1

end GlobalTheory.FiniteSurjDim
end

