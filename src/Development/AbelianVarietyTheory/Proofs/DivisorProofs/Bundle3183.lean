import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3135
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2967
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3120
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2826
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3131
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2977
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecScalOneVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3143
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingHeckePointsGeometricEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLabelsConstantCompletedLocalRingClosedPoiStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLabels_constant_completedLocalRing_closedPoint : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∃ yy : S.Gam →+ D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : D.toPre.X →+ D.toPre.X).range, ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∀ (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε → ∀ (l : u.Lab) a α, yy a = QuotientAddGroup.mk α ↔ l.yy a = QuotientAddGroup.mk (ε α) := by
  first | exact @GlobalTheory.Poinc.LabConst.main | exact GlobalTheory.Poinc.LabConst.main | (intros; apply GlobalTheory.Poinc.LabConst.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointFrameMulEqIntegralGenerators
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.IntEval

theorem frames_mul_eq_integral : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (g : GtPtF D.toPre (FractionRing V)) (w : Frm D.toPre (FractionRing V) 1 g.b) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (fr : FrAt x), (∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) → w.IsGen → fr.IsGen → LiesOver U.toUnifPre w₀ g w x fr → ∀ (h : (𝟙_ (Over (Sp V))) ⟶ G) (g' : GtPt D.toPre (𝟙_ (Over (Sp V)))) (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => (h).left) (fun _ => 1))) (t : LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, (g'.b).left] (DegPre.lineε 1))), GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre h g' → IntTerm.Ext U.toUnifPre x h → GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g' g → f.IsGen → t.IsGen → (∀ e : ℕ, GlobalTheory.Poinc.IntEval.TRel U.toUnifPre h g'.b f t e) → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι) (JB : ((TF (R := V) (FractionRing V)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good A.L z JA → Good U.LG.L z JG → Good D.toPre.P.L z JB → Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h).left) (fun _ => JA (x).left) * val (Z := (TF (R := V) (FractionRing V)).left) fr (𝟙 _) z JA * val w (𝟙 _) z JB = val f (toUnit (TF (R := V) (FractionRing V))).left z JG * val t (toUnit (TF (R := V) (FractionRing V))).left z JB := by
  intro V _ _ _ hV D A G _ _ hG U w₀ hw₀ N hN g w x fr hg hw hfr hL h g' f t hF hExt hP hf ht htl z JA JG JB hJA hJG hJB
  obtain ⟨z₀⟩ := CoefBasic.exists_pt (R := V) (F := FractionRing V)
  obtain ⟨JA₀, hA₀⟩ := CoefBasic.exists_good' A.isLB z₀
  obtain ⟨JG₀, hG₀⟩ := CoefBasic.exists_good' U.LG.isLB z₀
  obtain ⟨l, hl⟩ := CoefBasic.cstH_surj z₀ (Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀
    (x.left ≫ U.gen.inv.left) z₀ (JG₀ (toUnit (TF (R := V) (FractionRing V)) ≫ h).left) (fun _ => JA₀ x.left) *
      val (Z := (TF (R := V) (FractionRing V)).left) fr (𝟙 _) z₀ JA₀ *
      (val f (toUnit (TF (R := V) (FractionRing V))).left z₀ JG₀)⁻¹).val
  have hl0 : l ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hl
    exact Units.ne_zero _ hl.symm
  have hfv : ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG),
      Good A.L z JA → Good U.LG.L z JG →
      (Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ (x.left ≫ U.gen.inv.left) z
          (JG (toUnit (TF (R := V) (FractionRing V)) ≫ h).left) (fun _ => JA x.left)).val *
        (val (Z := (TF (R := V) (FractionRing V)).left) fr (𝟙 _) z JA).val =
      UT.cst (FractionRing V) z l * (val f (toUnit (TF (R := V) (FractionRing V))).left z JG).val := by
    intro z' JA' JG' hA hG'
    obtain rfl := CoefBasic.pt_eq z₀ z'
    have ind := GlobalTheory.Poinc.FrameIndep.frame_ratio_indep V _ D A G U.toUnifPre w₀ hw₀ x fr hfr h f hf hExt z₀ JA' JA₀ JG' JG₀
      hA hG' hA₀ hG₀
    rw [mul_inv_eq_iff_eq_mul] at ind
    rw [← Units.val_mul, ind, Units.val_mul, CoefBasic.cst_eq, hl]
  have hφ : DegPre.lineφ D.toPre (FractionRing V) g.b = fun i =>
      (toUnit (TF (R := V) (FractionRing V))).left ≫ (![(η[D.toPre.P.A]).left, g'.b.left] : Fin 2 → _) i := by
    funext i
    fin_cases i
    · exact Over.comp_left (f := toUnit (TF (R := V) (FractionRing V))) (g := η[D.toPre.P.A])
    · exact hP.1
  obtain ⟨w₁, hw₁, hv₁⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre (FractionRing V) g.b)
    (ε' := DegPre.lineε 1) (by rw [hφ]; exact fun _ _ _ => rfl)
    (LB.pullGen D.toPre.P.L _ _ t (toUnit (TF (R := V) (FractionRing V))).left) (pullGen_isGen _ _ _ _ ht _)
  obtain ⟨w', hw', hwv⟩ := TorsionValue.exists_frm_scale w₁ hw₁ (inv_ne_zero hl0)
  have hwt : ∀ z J, Good D.toPre.P.L z J → UT.cst (FractionRing V) z l * (val w' (𝟙 _) z J).val =
      (val t (toUnit (TF (R := V) (FractionRing V))).left z J).val := by
    intro z J hJ
    rw [hwv z J hJ, hv₁ _ _ z J hJ, val_pull hJ, Category.id_comp, ← _root_.mul_assoc, GlobalTheory.UT.CoefBasic.cst_eq,
      GlobalTheory.UT.CoefBasic.cst_eq, ← map_mul, mul_inv_cancel₀ hl0, map_one, _root_.one_mul]
  have hLies : LiesOver U.toUnifPre w₀ g w' x fr := by
    intro k hk wk hwk hwkg s s' v hExp hVal
    obtain ⟨σ', hIso, n, c, σ, fs, hE, hσ, hs⟩ := hExp
    choose xs hxs using fun i => GlobalTheory.ExpansionValueZero.exists_coeff (A := V) U.LG.isLB (σ i) h.left
      (GeneratorPullback.powGen U.LG.L _ _ f k) (powGen_isGen _ _ _ _ hf k) (fun W _ q => by simp)
    have hxs' : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp V) z J, Good U.LG.L z J →
        sval (σ i) (r ≫ h.left) z J = Geo.Tor.cst r z (xs i) * (val f r z J ^ k).val :=
      fun i Z r z J hJ => (hxs i Z r z J hJ).trans (by rw [val_pow])
    choose a ha using fun i α => GlobalTheory.T.exists_integral_coefficient_section_coordinate_rig V D.toPre g' t ht k α (fs i α)
    have hv := GlobalTheory.T.section_value_generic_point_integral_section V (maximalIdeal V) D A G U.toUnifPre w₀ x fr h l f hExt hfv k s σ' hIso n c σ hσ xs hxs' v hVal
    have hwk' : ∀ z J, Good D.toPre.P.L z J → UT.cst (FractionRing V) z (l ^ k) * (val wk (𝟙 _) z J).val =
        (val t (toUnit (TF (R := V) (FractionRing V))).left z J ^ k).val := by
      intro z J hJ
      rw [hwk z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← hwt z J hJ, mul_pow,
        GlobalTheory.UT.CoefBasic.cst_eq, GlobalTheory.UT.CoefBasic.cst_eq, map_pow]
    have hc := GlobalTheory.T.integral_combination_terms_rational_point_frame V D.toPre g' g hP t l hl0 k wk hwkg hwk' s' n c fs hs a ha
    have hI := admissibleBase_of_completeNormalLocalCharZero hV
    have key := EvalZero.sumF_comb hI (FractionRing V) Finset.univ (fun i => c i * (l ^ k)⁻¹) _ _ fun i =>
      EvalZero.sumF_map (maximalIdeal V) (FractionRing V) (a i) (xs i) fun e' =>
        GlobalTheory.T.section_value_integral_point_congruent_term_sum V (maximalIdeal V) D A G U.toUnifPre h g' hF f t e' k (htl e') (σ i) (fs i) (hE i e') (xs i) (hxs' i)
          (a i) (ha i)
    have hlk : l ^ k ≠ 0 := pow_ne_zero _ hl0
    convert key using 1
    · funext α
      simp only [Algebra.algebraMap_self, RingHom.id_apply]
      rw [show (∑ i, c i * (l ^ k)⁻¹ * algebraMap V (FractionRing V) (a i α)) =
          (l ^ k)⁻¹ * ∑ i, c i * algebraMap V (FractionRing V) (a i α) by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
        ← hc α, ← _root_.mul_assoc, inv_mul_cancel₀ hlk, _root_.one_mul]
    · simp only [Algebra.algebraMap_self, RingHom.id_apply]
      rw [show (∑ i, c i * (l ^ k)⁻¹ * algebraMap V (FractionRing V) (xs i)) =
          (l ^ k)⁻¹ * ∑ i, c i * algebraMap V (FractionRing V) (xs i) by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring,
        ← hv, mul_comm v, ← _root_.mul_assoc, inv_mul_cancel₀ hlk, _root_.one_mul]
  haveI : CharZero V := hV.2.2.2
  have heq := LiesUniq.frame_unique (admissibleBase_of_completeNormalLocalCharZero hV) hG U hw₀ hw hw' hfr hL hLies z JB hJB
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, hfv z JA JG hJA hJG, ← hwt z JB hJB, heq]
  ring

end GlobalTheory.Poinc.IntEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSplitNormalBase
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HtGen

theorem charFam_of_normal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (S : Scheme.{0}) [IsIntegral S] (ρ : S ⟶ X) (p : ℕ) [Fact p.Prime] (n : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → CharZero S.functionField → (∃ ζ : S.functionField, IsPrimitiveRoot ζ (p ^ n)) → SplitK t (K := S.functionField) (S.fromSpecStalk (genericPoint S) ≫ ρ) (p ^ n) → CharFam t ρ p n := by
  intro E _ _ _ H X _ t S _ ρ p _ n hN hK hζ hsplit
  classical
  haveI : CharZero S.functionField := hK
  haveI := GlobalTheory.LatDRFree.intO_isLocalRing ℂ_[p]
  have hq : p ^ n ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hgen (s : S) : spMap (algebraMap (S.presheaf.stalk s) S.functionField) ≫ (S.fromSpecStalk s ≫ ρ) =
      S.fromSpecStalk (genericPoint S) ≫ ρ := by
    rw [← Category.assoc]
    congr 1
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes s)
  have key (s : S) := by
    haveI := (hN s).1
    haveI := (hN s).2
    exact GlobalTheory.T.integral_point_extension_split E H X t S.functionField _ (p ^ n) hq hζ hsplit (S.presheaf.stalk s) _ (hgen s)
  haveI := (key (genericPoint S)).1
  obtain ⟨N, ⟨eqv⟩⟩ := Finite.exists_equiv_fin (TorsK t (S.fromSpecStalk (genericPoint S) ≫ ρ) (p ^ n) →* S.functionFieldˣ)
  have hz (y : Sp ↥(intO ℂ_[p]) ⟶ S) :
      spMap (Scheme.stalkClosedPointTo y).hom ≫ (S.fromSpecStalk (y (IsLocalRing.closedPoint _)) ≫ ρ) = y ≫ ρ := by
    rw [← Category.assoc]
    exact congrArg (· ≫ ρ) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk y)
  have L (y : Sp ↥(intO ℂ_[p]) ⟶ S) := (key (y (IsLocalRing.closedPoint _))).2 p (Scheme.stalkClosedPointTo y).hom (y ≫ ρ)
    inferInstance (hz y)
  let c : Fin N → ∀ y : Sp ↥(intO ℂ_[p]) ⟶ S, TorsChar t (y ≫ ρ) (p ^ n) :=
    fun j y => Classical.choose ((L y).1 (eqv.symm j))
  have hc (j : Fin N) (y : Sp ↥(intO ℂ_[p]) ⟶ S) := Classical.choose_spec ((L y).1 (eqv.symm j))
  have memU (U : S.Opens) (hU : IsAffineOpen U) (x : Γ(S, U) →+* ↥(intO ℂ_[p])) (y : Sp ↥(intO ℂ_[p]) ⟶ S)
      (hxy : spMap x ≫ hU.fromSpec = y) : y (IsLocalRing.closedPoint _) ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec, ← hxy]
    exact ⟨_, rfl⟩
  refine ⟨N, c, fun y c' => ?_, fun U hU g e he => ?_⟩
  · obtain ⟨χ, hχ⟩ := (L y).2.1 c'
    refine ⟨eqv χ, (L y).2.2 χ c' (c (eqv χ) y) hχ ?_⟩
    have gen : ∀ j, eqv.symm j = χ → InducedBy χ (S.fromSpecStalk (y (IsLocalRing.closedPoint _)) ≫ ρ)
        (algebraMap (S.presheaf.stalk (y (IsLocalRing.closedPoint _))) S.functionField) (Scheme.stalkClosedPointTo y).hom
        (c j y) := by
      rintro j rfl
      exact hc j y
    exact gen _ (eqv.symm_apply_apply χ)
  · by_cases hne : Nonempty U
    swap
    · exact ⟨fun _ _ => 0, fun x y hxy _ => absurd ⟨⟨_, memU U hU x y hxy⟩⟩ hne⟩
    haveI : IsIntegrallyClosed Γ(S, U) := GlobalTheory.LineNorm.Chart.isIntegrallyClosed_sections hN hU
    haveI := functionField_isFractionRing_of_isAffineOpen S U hU
    have hgU : genericPoint S ∈ U := by
      obtain ⟨u⟩ := hne
      exact (genericPoint_specializes u.1).mem_open U.isOpen u.2
    have hchart : spMap (algebraMap Γ(S, U) S.functionField) ≫ (hU.fromSpec ≫ ρ) = S.fromSpecStalk (genericPoint S) ≫ ρ := by
      rw [← Category.assoc, ← hU.fromSpecStalk_eq_fromSpecStalk hgU]
      rfl
    choose hh hhs using fun j : Fin N =>
      GlobalTheory.T.integral_point_torsion_split E H X t S.functionField _ p n hsplit Γ(S, U) (hU.fromSpec ≫ ρ) hchart g e he.1 (eqv.symm j)
    refine ⟨hh, fun x y hxy j => ?_⟩
    have hs := memU U hU x y hxy
    let φ := (S.presheaf.germ U _ hs).hom
    have hu : (algebraMap (S.presheaf.stalk (y (IsLocalRing.closedPoint _))) S.functionField).comp φ =
        algebraMap Γ(S, U) S.functionField := by
      show (S.presheaf.germ U _ hs ≫ S.presheaf.stalkSpecializes (genericPoint_specializes _)).hom = _
      rw [TopCat.Presheaf.germ_stalkSpecializes]
      rfl
    have hx0 : spMap φ ≫ hU.fromSpec ≫ ρ = S.fromSpecStalk (y (IsLocalRing.closedPoint _)) ≫ ρ := by
      rw [← Category.assoc, ← hU.fromSpecStalk_eq_fromSpecStalk hs]
      rfl
    have heq : (Scheme.stalkClosedPointTo y).hom.comp φ = x := by
      apply GlobalTheory.LineNorm.Chart.ringHom_ext hU
      rw [hxy]
      show Spec.map (CommRingCat.ofHom ((Scheme.stalkClosedPointTo y).hom.comp φ)) ≫ hU.fromSpec = y
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      show _ ≫ hU.fromSpecStalk hs = y
      rw [hU.fromSpecStalk_eq_fromSpecStalk hs]
      exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk y
    have k : DlogIs t p n (c j y) (fun i => spMap (dualMap ((Scheme.stalkClosedPointTo y).hom.comp φ)) ≫ e i)
        (fun i => ((Scheme.stalkClosedPointTo y).hom.comp φ) (hh j i)) :=
      hhs j _ φ _ _ _ _ (c j y) hu hx0 inferInstance (hz y) (hc j y)
    rw [heq] at k
    exact k

end GlobalTheory.HtGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTransportCmPeriod
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.ConjRiemann

theorem im_conj_form_eq : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)) (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left),
        X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p →
        ∀ u' : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E)), (∀ w, w ∈ u'.Λ ↔ ∃ x ∈ lattice c (y * (upIdele K E t)⁻¹), w = fun j ↦ GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) 0 x (T.U.e j)) →
          (∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
            v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
              u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') →
          (∀ x x' : E, ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
            (u'.ex (fun j ↦ g (φ (T.U.e j) x'))).left ≫ p = spMap (g : ℂ →+* ℂ) ≫ (T.U.u.ex (fun j ↦ φ (T.U.e j) x)).left) →
          ∀ (u₀ : HolUnif X'.A (X'.diag T.U.c) (Module.finrank ℚ (FR E))) (Hm : Matrix (Fin (Module.finrank ℚ (FR E))) (Fin (Module.finrank ℚ (FR E))) ℂ) (χ : u₀.Λ → ℂ),
            u₀.ex = u'.ex → u₀.IsAH Hm χ →
            ∀ x ∈ lattice c (y * (upIdele K E t)⁻¹), ∀ x' ∈ lattice c (y * (upIdele K E t)⁻¹),
              ((fun j ↦ g (φ (T.U.e j) x)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) x'))).im =
                (modF t)⁻¹ * ∑ i, T.U.h i * (φ i x * starRingEnd ℂ (φ i x')).im := by
  intro hPC hADR hADC K _ _ d δ io hK2 hd hδ g t Λ₀ Λ₁ Ω₀ Ω₁ _hΩ hTT E _ _ _ _ I _ φ _hφ hφK c y hc 𝔠 T X' p hp u' hlat
    _hdiff htors u₀ Hm χ hex hAH
  have W := GlobalTheory.T.galois_conjugate_cm_point hPC hADR hADC K t E I φ g c y hc 𝔠 T X' p hp u' hlat htors u₀ Hm χ hex hAH
  have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hexp : ∀ (r r' : ℝ) (k : ℕ), 0 < k →
      Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (r' : ℂ) / k) →
        ∃ n : ℤ, r' - r = k * n := by
    intro r r' k hk h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
    refine ⟨n, ?_⟩
    have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    have e1 : (2 * (Real.pi : ℂ) * Complex.I) * (((r' - r : ℝ) : ℂ) - ((k * n : ℝ) : ℂ)) = 0 := by
      have hn' := congrArg (fun z => z * (k : ℂ)) hn
      simp only [add_mul, div_mul_cancel₀ _ hk'] at hn'
      push_cast
      linear_combination hn'
    rcases mul_eq_zero.1 e1 with h0 | h0
    · exact absurd h0 h2pi
    · exact_mod_cast sub_eq_zero.1 h0
  have h0L : (0 : E) ∈ lattice c y := by
    show algebraMap E (Af E) 0 * _ ∈ hatO c
    rw [map_zero, zero_mul]; exact (hatO c).zero_mem
  have h0L' : (0 : E) ∈ lattice c (y * (upIdele K E t)⁻¹) := by
    show algebraMap E (Af E) 0 * _ ∈ hatO c
    rw [map_zero, zero_mul]; exact (hatO c).zero_mem
  have htrz : ∀ z ∈ lattice c (y * (upIdele K E t)⁻¹),
      ((upIdele K E t : Af E) * algebraMap E (Af E) (z / ((1 : ℕ) : E)) - algebraMap E (Af E) ((0 : E) / ((1 : ℕ) : E))) *
        ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
    intro z hz
    have hz' : algebraMap E (Af E) z * (((y * (upIdele K E t)⁻¹)⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := hz
    convert hz' using 1
    simp only [Nat.cast_one, div_one, zero_div, map_zero, sub_zero, mul_inv_rev, inv_inv, Units.val_mul]
    ring
  have htrw : ∀ w ∈ lattice c y,
      ((upIdele K E t : Af E) * algebraMap E (Af E) ((0 : E) / ((1 : ℕ) : E)) - algebraMap E (Af E) (w / ((1 : ℕ) : E))) *
        ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
    intro w hw
    have hw' : algebraMap E (Af E) w * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := hw
    have e : ((upIdele K E t : Af E) * algebraMap E (Af E) ((0 : E) / ((1 : ℕ) : E)) - algebraMap E (Af E) (w / ((1 : ℕ) : E))) *
        ((y⁻¹ : (Af E)ˣ) : Af E) = -(algebraMap E (Af E) w * ((y⁻¹ : (Af E)ˣ) : Af E)) := by
      simp only [Nat.cast_one, div_one, zero_div, map_zero, mul_zero, zero_sub, neg_mul]
    rw [e]; exact (hatO c).neg_mem hw'
  have hEg : ∀ z ∈ lattice c (y * (upIdele K E t)⁻¹), ∀ z' ∈ lattice c (y * (upIdele K E t)⁻¹), ∃ n : ℤ,
      ((fun j ↦ g (φ (T.U.e j) z)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) z'))).im = n := by
    intro z hz z' hz'
    have h := W 1 0 0 z z' one_pos h0L h0L hz hz' (htrz z hz) (htrz z' hz')
    have hl : (∑ i, T.U.h i * (φ i 0 * starRingEnd ℂ (φ i 0)).im) = 0 := by simp
    rw [hl] at h
    obtain ⟨n, hn⟩ := hexp 0 _ 1 one_pos (by rw [← h]; simp)
    exact ⟨n, by simpa using hn⟩
  have hEf : ∀ w ∈ lattice c y, ∀ w' ∈ lattice c y, ∃ n : ℤ,
      (∑ i, T.U.h i * (φ i w * starRingEnd ℂ (φ i w')).im) = n := by
    intro w hw w' hw'
    have h := W 1 w w' 0 0 one_pos hw hw' h0L' h0L' (htrw w hw) (htrw w' hw')
    have hl : ((fun j ↦ g (φ (T.U.e j) 0)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) 0))).im = 0 := by
      simp
    rw [hl] at h
    have h1 : Complex.exp (-(2 * Real.pi * Complex.I) * (((∑ i, T.U.h i * (φ i w * starRingEnd ℂ (φ i w')).im : ℝ)) : ℂ) /
        ((1 : ℕ) : ℂ)) = Complex.exp (-(2 * Real.pi * Complex.I) * ((0 : ℝ) : ℂ) / ((1 : ℕ) : ℂ)) :=
      g.injective (by rw [h]; simp)
    obtain ⟨n, hn⟩ := hexp _ 0 1 one_pos h1
    exact ⟨-n, by push_cast at hn ⊢; linarith⟩
  have hsc : ∀ (m : K) (u u' : E), (∑ i, T.U.h i * (φ i (algebraMap K E m * u) * starRingEnd ℂ (φ i (algebraMap K E m * u'))).im) =
      Complex.normSq (io m) * ∑ i, T.U.h i * (φ i u * starRingEnd ℂ (φ i u')).im := by
    intro m u u'
    have hφm : ∀ i, φ i (algebraMap K E m) = io m := fun i => by rw [← hφK i]; rfl
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, hφm, map_mul]
    have e : io m * φ i u * (starRingEnd ℂ (io m) * starRingEnd ℂ (φ i u')) =
        (Complex.normSq (io m) : ℂ) * (φ i u * starRingEnd ℂ (φ i u')) := by
      rw [Complex.normSq_eq_conj_mul_self]; ring
    rw [e, Complex.im_ofReal_mul]; ring
  have hApos : 0 < modF t :=
    finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun v => zpow_pos (by
      have : Ideal.absNorm v.asIdeal ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
      positivity) _
  have hcong : ∀ k : ℕ, 0 < k → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ Nat.Coprime b k ∧ IsCoprime a (k : ℤ) ∧
      ∀ s : {q : E × E // q.1 ∈ lattice c (y * (upIdele K E t)⁻¹) ∧ q.2 ∈ lattice c (y * (upIdele K E t)⁻¹)},
        (∃ n : ℤ, (b : ℝ) / modF t * (∑ i, T.U.h i * (φ i s.1.1 * starRingEnd ℂ (φ i s.1.2)).im) = n) ∧
        ∃ n : ℤ, ((fun j ↦ g (φ (T.U.e j) s.1.1)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) s.1.2))).im -
          a * ((b : ℝ) / modF t * (∑ i, T.U.h i * (φ i s.1.1 * starRingEnd ℂ (φ i s.1.2)).im)) = k * n := by
    intro k hk
    obtain ⟨a, ha, hga⟩ := GlobalTheory.T.galois_action_roots_of_unity g k hk
    obtain ⟨m, b, hb, hbk, hnorm, hm⟩ := GlobalTheory.T.norm_coprime_lattice_multiplier K d δ io hK2 hd hδ E t c y hc k hk
    refine ⟨a, b, hb, hbk, ha, ?_⟩
    rintro ⟨⟨u, u'⟩, hu, hu'⟩
    have hmu := (hm u hu).1
    have hmu' := (hm u' hu').1
    have hbA : (b : ℝ) / modF t * (∑ i, T.U.h i * (φ i u * starRingEnd ℂ (φ i u')).im) =
        ∑ i, T.U.h i * (φ i (algebraMap K E m * u) * starRingEnd ℂ (φ i (algebraMap K E m * u'))).im := by
      rw [hsc, hnorm]
    obtain ⟨n₀, hn₀⟩ := hEf _ hmu _ hmu'
    refine ⟨⟨n₀, by rw [hbA, hn₀]⟩, ?_⟩
    have h := W k (algebraMap K E m * u) (algebraMap K E m * u') u u' hk hmu hmu' hu hu' (hm u hu).2 (hm u' hu').2
    rw [hn₀] at h
    have e3 : Complex.exp (-(2 * Real.pi * Complex.I) * (((n₀ : ℝ)) : ℂ) / k) =
        Complex.exp (2 * Real.pi * Complex.I * ((-n₀ : ℤ) : ℂ) / k) := by
      congr 1; push_cast; ring
    rw [e3, hga (-n₀)] at h
    have e4 : Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * ((-n₀ : ℤ) : ℂ)) / k) =
        Complex.exp (-(2 * Real.pi * Complex.I) * ((((a * n₀ : ℤ) : ℝ)) : ℂ) / k) := by
      congr 1; push_cast; ring
    rw [e4] at h
    obtain ⟨n, hn⟩ := hexp _ _ k hk h
    refine ⟨n, ?_⟩
    show _ - _ * ((b : ℝ) / modF t * (∑ i, T.U.h i * (φ i u * starRingEnd ℂ (φ i u')).im)) = _
    rw [hbA, hn₀]
    push_cast at hn ⊢
    linarith
  have hpos : ∃ s : {q : E × E // q.1 ∈ lattice c (y * (upIdele K E t)⁻¹) ∧ q.2 ∈ lattice c (y * (upIdele K E t)⁻¹)},
      (∑ i, T.U.h i * (φ i s.1.1 * starRingEnd ℂ (φ i s.1.2)).im) ≠ 0 ∧
      0 < (∑ i, T.U.h i * (φ i s.1.1 * starRingEnd ℂ (φ i s.1.2)).im) *
        ((fun j ↦ g (φ (T.U.e j) s.1.1)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) s.1.2))).im := by
    obtain ⟨χT, hT⟩ := T.U.ah
    obtain ⟨u, hu, u', hu', hne, hp⟩ := GlobalTheory.T.cm_riemann_form_galois_conjugate K d δ io hK2 hd hδ g hTT.2.2.1 E I φ hφK c (y * (upIdele K E t)⁻¹) hc _ T.U.e
      T.U.h Hm Module.finrank_pos hT.2.1 hAH.1 hAH.2.1
    exact ⟨⟨(u, u'), hu, hu'⟩, hne, hp⟩
  intro x hx x' hx'
  have key := GlobalTheory.T.rational_function_ratio_determined {q : E × E // q.1 ∈ lattice c (y * (upIdele K E t)⁻¹) ∧ q.2 ∈ lattice c (y * (upIdele K E t)⁻¹)}
    (fun s => ∑ i, T.U.h i * (φ i s.1.1 * starRingEnd ℂ (φ i s.1.2)).im)
    (fun s => ((fun j ↦ g (φ (T.U.e j) s.1.1)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (T.U.e j) s.1.2))).im)
    (modF t) hApos (fun s => hEg _ s.2.1 _ s.2.2) hcong hpos ⟨(x, x'), hx, hx'⟩
  rw [inv_mul_eq_div]
  exact key

end GlobalTheory.ConjRiemann
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionProductOverThickeningOfSumDataStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtension_product_over_thickening_of_sumData : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ) (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (g₁ : GtCoord I D₁ e G₁) (g₂ : GtCoord I D₂ e G₂), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∃ (q : thickObj R I e (G₁ ⊗ G₂) ⟶ thickObj R I e D.P.A) (i : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ thickObj R I e (G₁ ⊗ G₂)), IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ IsAffineHom q.left ∧ IsMonHom i ∧ IsPullback i (toUnit _) q (η[thickObj R I e D.P.A]) ∧ q ≫ (Over.pullback (thick R I e)).map p₁ = ((Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ g₁.q ∧ q ≫ (Over.pullback (thick R I e)).map p₂ = ((Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ g₂.q ∧ (∀ h : D₁.X → D.X, (∀ y, q₁ (h y) = y) → (∀ y, q₂ (h y) = 0) → ∃ τ : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.X, TorusHomOf h τ ∧ i ≫ ((Over.pullback (thick R I e)).map (fst G₁ G₂)) = τ ≫ g₁.i) ∧ (∀ h : D₂.X → D.X, (∀ y, q₁ (h y) = 0) → (∀ y, q₂ (h y) = y) → ∃ τ : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.X, TorusHomOf h τ ∧ i ≫ ((Over.pullback (thick R I e)).map (snd G₁ G₂)) = τ ≫ g₂.i) := by
  first | exact @GlobalTheory.ProdTorusExt.main | exact GlobalTheory.ProdTorusExt.main | (intros; apply GlobalTheory.ProdTorusExt.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitEquivariantBijectionTransportCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem trait_transport : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W))), w₀.IsGen → ∀ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α) → ∀ E' : Fam T.D'.toPre F (C.n ^ j) → SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j), Eqv T.D'.toPre T.A F (C.n ^ j) lab' E' → ∃ (lab : QkPt D.toPre F (C.n ^ j) → (TFK (R := R) F ⟶ C.A.A)) (E : Fam D.toPre F (C.n ^ j) → SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j)) (Φ : Fam D.toPre F (C.n ^ j) → Fam T.D'.toPre F (C.n ^ j)), LabExt em (C.lab j) lab ∧ Eqv D.toPre C.A F (C.n ^ j) lab E ∧ (∀ (s : Fam D.toPre F (C.n ^ j)) (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)), F₀.Over s → (∀ f' : ∀ x, T.D'.toPre.SecB (C.n ^ j) x, (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → ∀ x, GeneratorPullback.SecScal T.D'.toPre.P.L (DegPre.famφ T.D'.toPre F x) (DegPre.famε (C.n ^ j)) ((Φ s).s x) (T.D'.toPre.famφB x) (DegPre.famε (C.n ^ j)) (f' x) (DegPre.prB T.D'.toPre F).left 1)) ∧ ∀ (s : Fam D.toPre F (C.n ^ j)) (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval (E s) p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval (E' (Φ s)) q z Jt := by
  intro R _ _ _ hR D C j wA hwA W _ _ _ T F _ _ _ _ em hc f hf hfst hα w₀ hw₀ lab' hlab' E' hE'
  obtain ⟨Φ, hΦb, hΦa, hΦs, hΦP, hΦp, hΦf⟩ := GlobalTheory.FamPull.fam_transport R D W T.φ T.D' T.hD F hc (C.n ^ j)
  obtain ⟨lab, hLE, hon, hlr⟩ := GlobalTheory.Mum.Trait.exists_lab_push R hR D C j W T F em hc f hf hfst hα lab' hlab' hE'.onto
  obtain ⟨Tr, hTb, hTa, hTs, hTv⟩ := GlobalTheory.Mum.SecMove.exists_trait_transport R hR D C j wA hwA W T F hc f hf hfst hα w₀ hw₀
  have hC2 := GlobalTheory.T.transport_symmetric_lifts_theta_group_trait R hR D C j wA hwA W T F hc f hf hfst hα w₀ hw₀
  refine ⟨lab, fun s => Tr (E' (Φ s)), Φ, hLE, ⟨?_, ?_, ?_, hon, ?_, ?_, ?_⟩, hΦP, fun s => hTv (E' (Φ s))⟩
  · exact hTb.comp (hE'.bij.comp hΦb)
  · intro s s' s'' h i
    exact hTa _ _ _ (hE'.add _ _ _ (hΦa s s' s'' h)) i
  · intro c s s' h i
    exact hTs c _ _ (hE'.smul c _ _ (hΦs c s s' h)) i
  · intro p
    obtain ⟨p', hy, hg⟩ := hΦp p
    exact (hΦf p p' hy hg).1 (hE'.frame p')
  · intro p
    obtain ⟨p', hy, hg⟩ := hΦp p
    exact (hC2 _ _ (hlr p p' hy hg) ((hE'.onto _).2 ⟨p', rfl⟩)).1 (hE'.lift p')
  · intro p w θ s s' hw hθ hr
    obtain ⟨p', hy, hg⟩ := hΦp p
    obtain ⟨w', hw', hr'⟩ := (hΦf p p' hy hg).2 w hw
    obtain ⟨θ', hθ', hact⟩ := (hC2 _ _ (hlr p p' hy hg) ((hE'.onto _).2 ⟨p', rfl⟩)).2 θ hθ
    exact hact _ _ _ _ (hTv _) (hTv _) (hE'.act p' w' θ' _ _ hw' hθ' (hr' s s' hr))

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionDensityHolomorphicChartEtaleStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transgressionDensity_holomorphicChart_etale : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ (c : AlgChart X.str σ X.dim) {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → y ∈ e.source → y ∈ c.e.source → ∀ {A : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → corrTop (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()) (e y) = ‖transDet e c.e y‖ ^ 2 * corrDens E H₀ H ρ c y := by
  first | exact @GlobalTheory.GoodTop.corrTop_holoChart_trans | exact GlobalTheory.GoodTop.corrTop_holoChart_trans | (intros; apply GlobalTheory.GoodTop.corrTop_holoChart_trans <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFunctionalEquationOfAdicSumTermwiseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedFunctionalEquation_of_adicSum_termwise : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)) (F : ∀ β, SecT D.toPre a n j β) (σ : D.toPre.X → Ix ≃ Ix), Small (maximalIdeal R) s → IsSum (maximalIdeal R) s F → (∀ mu i, w (σ mu i) = w i + shift h h' n j mu) → (∀ mu i, TRel h mu (s i) (s (σ mu i))) → TFE h h' F := by
  first | exact @GlobalTheory.TwFam.SumFE.tfe_of_isSum | exact GlobalTheory.TwFam.SumFE.tfe_of_isSum | (intros; apply GlobalTheory.TwFam.SumFE.tfe_of_isSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRelationCocycleInTranslationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedRelation_cocycle_in_translation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (ν mu β₀ β₁ β₂ : D.toPre.X) (s₀ : SecT D.toPre a n j β₀) (s₁ : SecT D.toPre a n j β₁) (s₂ : SecT D.toPre a n j β₂), β₁ = β₀ + shift h h' n j ν → β₂ = β₁ + shift h h' n j mu → TRel h ν s₀ s₁ → TRel h (ν + mu) s₀ s₂ → TRel h mu s₁ s₂ := by
  first | exact @GlobalTheory.TwFam.trel_cocycle | exact GlobalTheory.TwFam.trel_cocycle | (intros; apply GlobalTheory.TwFam.trel_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRelationMulOfRelatedPairsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedRelation_mul_of_related_pairs : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (mu β β' β₁ β₁' : D.toPre.X) (f : SecT D.toPre a n j β) (g : SecT D.toPre a n' j' β') (p : SecT D.toPre a n'' j'' (β + β')) (f₁ : SecT D.toPre a n j β₁) (g₁ : SecT D.toPre a n' j' β₁') (p₁ : SecT D.toPre a n'' j'' (β₁ + β₁')), β₁ = β + shift h h' n j mu → β₁' = β' + shift h h' n' j' mu → IsProdT f g p → IsProdT f₁ g₁ p₁ → TRel h mu f f₁ → TRel h mu g g₁ → TRel h mu p p₁ := by
  first | exact @GlobalTheory.TwFam.ProdRel.trel_prod | exact GlobalTheory.TwFam.ProdRel.trel_prod | (intros; apply GlobalTheory.TwFam.ProdRel.trel_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingHeckePointsGeometricEqOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_heckePoints_geometric_eq_one : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : R →+* K), x ≫ s = spMap β → ∀ u : Γ((Over.mk x).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (toUnit (Over.mk x) ≫ (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A)) (toUnit (Over.mk x) ≫ (lift 1 h₂ : 𝟙_ (Over S) ⟶ G2 o.A)) u → u = 1 := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.weilIs_heckeSub_geom) | (exact GlobalTheory.UPel.HT.Hecke.weilIs_heckeSub_geom) | (intros; apply GlobalTheory.UPel.HT.Hecke.weilIs_heckeSub_geom <;> assumption)
end

