import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0383
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0132
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2049
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2169
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRatiosGenerateAtFlagSpaceGenericPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSApp

theorem stalkClosedPointTo_ger {V : Type} [CommRing V] [IsLocalRing V] {Y : Scheme.{0}} (x : Sp V ⟶ Y) (W : Y.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (g : Γ(Y, W)) (hy : x (IsLocalRing.closedPoint V) ∈ W) :
    (Scheme.stalkClosedPointTo (R := CommRingCat.of V) x).hom (ger _ hy g) = GlobalTheory.TangentOrigin.evalPt x W h g := by
  have key := Scheme.germ_stalkClosedPointTo (R := CommRingCat.of V) x W hy
  have := congrArg (fun φ => φ.hom g) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  refine this.trans ?_
  simp only [GlobalTheory.TangentOrigin.evalPt, Scheme.Hom.appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    CommRingCat.hom_comp, RingHom.comp_apply, Category.assoc]
  congr!

theorem val_eq_lift_residue {k K : Type} [CommRing k] [Field K] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens}
    (x : Sp K ⟶ Y) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hi : ⊤ ≤ x ⁻¹ᵁ B.U i) (hy : ptOf x ∈ O) (hj : ptOf x ∈ B.U i)
    (f : H0 p B O) :
    haveI : IsLocalHom (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x).hom :=
      Scheme.isLocalHom_stalkClosedPointTo' (R := K) x
    H0.val x i hO hi f = IsLocalRing.ResidueField.lift (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x).hom
      ((Y.residue (ptOf x)).hom (germ i (ptOf x) hy hj f)) := by
  haveI : IsLocalHom (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x).hom :=
    Scheme.isLocalHom_stalkClosedPointTo' (R := K) x
  rw [H0.val_apply, H0.germ_apply]
  exact (stalkClosedPointTo_ger x _ _ _ (memInf hy hj)).symm.trans
    (IsLocalRing.ResidueField.lift_residue_apply _ _).symm

open GlobalTheory.CompHt (genVal)
open GlobalTheory.AllWt (exOf secZ)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem ratGen_of_birOn : ∀ {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw),
    Nonempty (Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) → GlobalTheory.DegVal.BirOn U Z (wtOf Dw la 0) → RatGen X Z U la := by
  intro Y X Z r U la ⟨M⟩ hB
  have h : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  obtain ⟨z, hz, hO⟩ := exists_lift_genFr M h
  have hgen := isGenericPoint_of_lift M h hz hO
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := by
    intro s _
    have := hO (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hη : ptOf (z ≫ M.σ) ∈ U₀ X Z := (le_iff_ptOf_mem _ _).1 hU
  have hdense : closure (M.σ '' Set.univ) = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (dense_U₀ X Z).closure_eq]
    refine closure_mono fun u hu => ?_
    have hu' : ⊤ ≤ resPt u ⁻¹ᵁ U₀ X Z := (le_iff_ptOf_mem _ _).2 ((ptOf_resPt u).symm ▸ hu)
    obtain ⟨w, hw, -⟩ := M.existsUnique_lift (resPt u) hu'
    refine ⟨ptOf w, trivial, ?_⟩
    rw [← ptOf_comp, hw, ptOf_resPt]
  have hgen' : IsGenericPoint (ptOf (z ≫ M.σ)) Set.univ := by
    have := hgen.image M.σ.continuous
    rwa [hdense] at this
  refine ⟨ptOf (z ≫ M.σ), hη, hgen', ?_⟩
  haveI : IsLocalHom (Scheme.stalkClosedPointTo (R := CommRingCat.of (Om Z)) (z ≫ M.σ)).hom :=
    Scheme.isLocalHom_stalkClosedPointTo' (R := Om Z) (z ≫ M.σ)
  set ψ := IsLocalRing.ResidueField.lift (Scheme.stalkClosedPointTo (R := CommRingCat.of (Om Z)) (z ≫ M.σ)).hom
    with hψ
  have e₁ : (z ≫ M.σ) ≫ inc₀ X Z = X.pt (genFr h Z) ≫ X.inc := by
    rw [Category.assoc, X.pt_inc]; exact hz
  have hO₂ : ⊤ ≤ ((z ≫ M.σ) ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X := hU
  have key : ∀ (i : (L₀ X Z la).ι) (hi : ptOf (z ≫ M.σ) ∈ (L₀ X Z la).U i), ∃ T : Om Z, T ≠ 0 ∧
      ∀ g : Cusp Z U la, ψ (((Y₀ X Z).residue (ptOf (z ≫ M.σ))).hom
        (germ i (ptOf (z ≫ M.σ)) hη hi (cuspSec X Z U la g))) = T * genVal Z g.1 := by
    intro i hi
    have hi' : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ (L₀ X Z la).U i := (le_iff_ptOf_mem _ _).2 hi
    have hk₂ : ⊤ ≤ ((z ≫ M.σ) ≫ inc₀ X Z) ⁻¹ᵁ X.F.U (i PUnit.unit) := (le_iff_ptOf_mem _ _).2 (mem_pull.1 hi)
    have hk₁ : ⊤ ≤ (X.pt (genFr h Z) ≫ X.inc) ⁻¹ᵁ X.F.U (i PUnit.unit) := e₁ ▸ hk₂
    obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor (genFr h Z) (i PUnit.unit) hk₁
    have hQ₂ : X.F.ChartFr (i PUnit.unit) ((z ≫ M.σ) ≫ inc₀ X Z) hk₂ Q := chartFr_congr e₁.symm hQ
    refine ⟨((∏ ix, t ix ^ exOf Dw la 0 ix : (Om Z)ˣ) : Om Z)⁻¹, inv_ne_zero (Units.ne_zero _), fun g => ?_⟩
    have v₈ := evR_eq_val_secOf ⟨g.1, cusp_le_secZ Z U la g.2⟩ hO₂ hQ₂ ht
    have v₅ : H0.val (z ≫ M.σ) i hU hi' (cuspSec X Z U la g) = H0.val (B := X.LL (exOf Dw la 0))
        ((z ≫ M.σ) ≫ inc₀ X Z) (i PUnit.unit) hO₂ hk₂ (secOf X _ ⟨g.1, cusp_le_secZ Z U la g.2⟩) :=
      H0.val_pull (inc₀ X Z) le_rfl (z ≫ M.σ) i hU hi' hO₂ hk₂ _
    have v₆ : genVal Z g.1 = evR Xo c g.1 (genFr h Z) := rfl
    rw [← val_eq_lift_residue (z ≫ M.σ) i hU hi' hη hi, v₅, v₆, v₈, inv_mul_cancel_left₀ (Units.ne_zero _)]
  have hmap : ∀ v w : Cusp Z U la, ∃ q ∈ ratField (Set.range (cuspSec X Z U la)) (ptOf (z ≫ M.σ)) hη,
      ψ q = genVal Z v.1 / genVal Z w.1 := by
    intro v w
    obtain ⟨i, hi⟩ := exists_chart (isLB_L₀ X Z la) (ptOf (z ≫ M.σ))
    obtain ⟨T, hT, hv⟩ := key i hi
    refine ⟨_, Subfield.subset_closure ⟨i, hi, _, _, ⟨v, rfl⟩, ⟨w, rfl⟩, rfl⟩, ?_⟩
    refine (map_div₀ ψ _ _).trans ?_
    rw [hv, hv, mul_div_mul_left _ _ hT]
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : Cusp Z U la, genVal Z v₀.1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hB.1 (LinearMap.ext fun v => hc v)
  have hsub : (⊤ : IntermediateField c.F (Om Z)).toSubfield ≤
      (ratField (Set.range (cuspSec X Z U la)) (ptOf (z ≫ M.σ)) hη).map ψ := by
    rw [← hB.2, GlobalTheory.DegVal.ratioField, IntermediateField.adjoin_toSubfield]
    refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨a, rfl⟩
      obtain ⟨q, hq, e⟩ := hmap ⟨a • v₀.1, Submodule.smul_mem _ a v₀.2⟩ v₀
      refine ⟨q, hq, e.trans ?_⟩
      show genVal Z (a • v₀.1) / genVal Z v₀.1 = _
      rw [map_smul, Algebra.smul_def, mul_div_cancel_right₀ _ hv₀]
    · rintro _ ⟨v, w, rfl⟩
      exact hmap v w
  refine eq_top_iff.2 fun q _ => ?_
  obtain ⟨q', hq', e⟩ := hsub (show ψ q ∈ (⊤ : IntermediateField c.F (Om Z)).toSubfield from trivial)
  exact (ψ.injective e) ▸ hq'

example : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (la : AllWt.Weight Dw), Nonempty (Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw)) → GlobalTheory.DegVal.BirOn U Z (wtOf Dw la 0) → RatGen X Z U la := @ratGen_of_birOn

end GlobalTheory.HSApp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomLatticeChangeConstantsAwayUnit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove

namespace GlobalTheory.SqTower

theorem bottom_lattices : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (μ₀ : T), Lc.Is μ₀ → ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ →
  ∀ (i j : Fin D.R.m) {A A' WW : HSp D} (X Y : Tri T A A' WW), IsBottomTri W i j X → GlobalTheory.SqTower.IsStageC W i j 0 0 Y →
  ∃ (Z : Tri T A A' WW) (v : T → ℂ), GlobalTheory.SqTower.IsStageC W i j 0 0 Z ∧
    Z.rA.Λ = X.rA.Λ ∧ Z.rA'.Λ = X.rA'.Λ ∧ Z.rW.Λ = X.rW.Λ ∧ (∀ t, v t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ v t = D.what₂.embLL ζ * v μ₀) ∧
    ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → Z.IsConst W.ψ W.θ (fun t => v t * c t) := by
  intro D T Lc sc G μ₀ hL W S hN i j A A' WW X Y hX hY
  have hYi := hY.2.2.2.2.2.2.2
  obtain ⟨g, hg, hgm⟩ := GlobalTheory.FinPl.BasePoint.exists_base A Y.rA.Λ X.rA.Λ hYi.rigA.1 hX.is.rigA.1
  obtain ⟨g', hg', hgm'⟩ := GlobalTheory.FinPl.BasePoint.exists_base A' Y.rA'.Λ X.rA'.Λ hYi.rigA'.1 hX.is.rigA'.1
  obtain ⟨h, hh, hhm⟩ := GlobalTheory.FinPl.BasePoint.exists_base WW Y.rW.Λ X.rW.Λ hYi.rigW.1 hX.is.rigW.1
  obtain ⟨r, r', hr0, hr, hr', hζ⟩ := GlobalTheory.T.moved_vacua_scalar_multiples_reference_tuple μ₀ hL W S hN i j Y hY g hg g' hg' h hh
  have hZi := GlobalTheory.T.thetaSeesawTriple_moved_to_selfDual_isValid Y _ _ _ _ _ _ hYi X.rA.Λ X.rA'.Λ X.rW.Λ hX.is.rigA.1 hX.is.rigA'.1 hX.is.rigW.1 g hg g' hg' h hh
    (hgm _) (hgm' _) (hhm _) μ₀ r r' hr0 hr hr'
  have hI := GlobalTheory.T.movedSeesawTriple_thetaIntegral_eq_scaled Y _ _ _ _ _ _ hYi X.rA.Λ X.rA'.Λ X.rW.Λ g hg g' h hh μ₀ r r' (fun t => (hr0 t).1)
  have hI' := GlobalTheory.T.movedSeesawTriple_primeThetaIntegral_eq_scaled Y _ _ _ _ _ _ hYi X.rA.Λ X.rA'.Λ X.rW.Λ g g' hg' h hh μ₀ r r' (fun t => (hr0 t).2)
  refine ⟨moveTri Y X.rA.Λ X.rA'.Λ X.rW.Λ g g' h μ₀ r r', fun t => r' t / r t,
    ⟨hY.1, hY.2.1, hY.2.2.1, hY.2.2.2.1, hY.2.2.2.2.1, hY.2.2.2.2.2.1, hY.2.2.2.2.2.2.1, hZi⟩,
    rfl, rfl, rfl, fun t => ⟨div_ne_zero (hr0 t).2 (hr0 t).1, hζ t⟩, ?_⟩
  rintro c ⟨⟨t₁, ht₁⟩, P, P', hc⟩
  refine ⟨⟨t₁, mul_ne_zero (div_ne_zero (hr0 t₁).2 (hr0 t₁).1) ht₁⟩, P, P', fun t =>
    ⟨fun y => ⟨(hI t P y).1.2 ((hc t).1 (y * h)).1, (hI' t P' y).1.2 ((hc t).1 (y * h)).2⟩, ?_, fun y => ?_⟩⟩
  · obtain ⟨y₀, hy₀⟩ := (hc t).2.1
    refine ⟨y₀ * h⁻¹, ?_⟩
    rw [(hI' t P' _).2, inv_mul_cancel_right]
    exact mul_ne_zero (inv_ne_zero (hr0 t).2) hy₀
  · rw [(hI t P y).2, (hI' t P' y).2, (hc t).2.2 (y * h)]
    field_simp [(hr0 t).1, (hr0 t).2]

end GlobalTheory.SqTower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformationCaseFiniteComponents
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.DefCore

theorem defCase_core : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), RowsT p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → DefCase (p.T.U ((i : ℕ) + 1)) (xiR D) ∧ Finite (Comp (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c) ∧ Nonempty (Comp (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c) ∧ (∀ σ, GoodEmb p.T.Q.c σ → ∀ g, (p.T.dict ((i : ℕ) + 1) σ g).2 ∈ ((p.T.U ((i : ℕ) + 1) σ).X (p.T.dict ((i : ℕ) + 1) σ g).1).dom) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M _ hm _ hW _ hF
  have hJ : LawsJ p.T := p.fw.laws
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.succ_pos _, hm.le⟩
  obtain ⟨hp, hq, hr⟩ := hW.sig
  have hk := D.R.m_add_three_le_k
  have hq0 : (p.T.Q.Dw ((i : ℕ) + 1)).q = 0 := by
    have : (dat p i).q = D.R.m - ((i : ℕ) + 1) := by rw [hq]; rfl
    simpa [dat, hm] using this
  have hp1 : 1 ≤ (p.T.Q.Dw ((i : ℕ) + 1)).p := by
    have : (dat p i).p = D.R.k + ((i : ℕ) + 1) - 1 := by rw [hp]; rfl
    simp only [dat] at this
    omega
  refine ⟨⟨hq0, hp1, ?_, hJ.pins.2.1.2, hF, hJ.unf _ hj, ?_⟩, CompFin.finite_comp _ _, ?_, ?_⟩
  · exact goodAt_of_two_primes hJ.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  · exact (GlobalTheory.LevGeo.laws_core D p.T _ hJ hj).xiAbs
  · exact (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ _ _ (by omega)).1
  · intro σ hσ g
    exact GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.dict_mem_dom p.T hJ _ hj σ hσ g

end GlobalTheory.DefCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseOpenEqTopOfSmoothOfRelativeDimensionZeroStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_open_eq_univ_of_smooth_relDim_zero : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k), SmoothOfRelativeDimension 0 p → ∀ (U : Y.Opens), Dense (U : Set Y) → U = ⊤ := by
  first | exact @GlobalTheory.dense_open_eq_top_of_smoothOfRelativeDimension_zero | exact GlobalTheory.dense_open_eq_top_of_smoothOfRelativeDimension_zero | (intros; apply GlobalTheory.dense_open_eq_top_of_smoothOfRelativeDimension_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationZeroAboveAndDegreeBoundStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthOscillation_zero_above_and_degreeBound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], (M < p → OscLe Xo c p cx 0) ∧ OscLe Xo c p cx ((F * (Dw.p + Dw.q : ℕ) * Mb + Sm) / ((p : ℝ) - 1)) := by
  first | exact @GlobalTheory.RefSum.oscLe_zero_above_and_degree | exact GlobalTheory.RefSum.oscLe_zero_above_and_degree | (intros; apply GlobalTheory.RefSum.oscLe_zero_above_and_degree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfMemBadPrimes
section
noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.BadLog

theorem logSum_le_log {B : Finset ℕ} {N : ℕ} (hN : N ≠ 0) (h : ∀ p ∈ B, p.Prime ∧ p ∣ N) : logSum B ≤ Real.log N := by
  have h1 : ∏ p ∈ B, p ∣ N :=
    (Finset.prod_dvd_prod_of_subset _ _ (fun p => p) fun p hp =>
      Nat.mem_primeFactors.2 ⟨(h p hp).1, (h p hp).2, hN⟩).trans (Nat.prod_primeFactors_dvd N)
  have h0 : ∀ p ∈ B, (p : ℝ) ≠ 0 := fun p hp => by exact_mod_cast (h p hp).1.ne_zero
  unfold logSum
  rw [← Real.log_prod h0, ← Nat.cast_prod]
  refine Real.log_le_log ?_ (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h1)
  exact_mod_cast Finset.prod_pos fun p hp => (h p hp).1.pos

variable {D : D7} {L : SizeData₂ D}

theorem log_level_le (P : ParameterChoice' D L) :
    LevelStarExponents.condE D * (D.host.g 0 * D.host.g 1) * 15 ≠ 0 ∧
    Real.log ((LevelStarExponents.condE D * (D.host.g 0 * D.host.g 1) * 15 : ℕ) : ℝ) ≤ (2 * |P.CYL| + 17) * zBase L := by
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hc0 : LevelStarExponents.condE D ≠ 0 := by
    unfold LevelStarExponents.condE
    exact mul_ne_zero (mul_ne_zero D.host.QS_pos.ne' D.host.hyp.1.ne_zero) D.host.hyp.2.1.ne_zero
  have hc1 : (1 : ℝ) ≤ LevelStarExponents.condE D := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hc0
  have hc : Real.log (LevelStarExponents.condE D) ≤ L.sc.L := by
    have ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ L.t_win.1
    have a : (LevelStarExponents.condE D : ℝ) ^ 36 ≤ L.sc.b ^ ((1 : ℝ) / 2) :=
      (le_mul_of_one_le_right (by positivity) ht).trans P.condE_le
    have b := Real.log_le_log (by positivity) a
    rw [Real.log_pow, Real.log_rpow hb, Scale.b, Real.log_exp] at b
    push_cast at b
    linarith
  obtain ⟨Y, y1, -, y3, y4⟩ := P.g_Y
  have hY : 0 < Y := lt_of_lt_of_le (by positivity) y1
  have hg0 : ∀ i, (0 : ℝ) < D.host.g i := fun i => hY.trans_le (y4 i).1
  have l2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have l15 : Real.log 15 ≤ 14 := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 15 by norm_num)]
  have hg : ∀ i, Real.log (D.host.g i) ≤ 1 + |P.CYL| * L.sc.L := fun i => by
    have a := Real.log_le_log (hg0 i) (y4 i).2
    rw [Real.log_mul two_ne_zero hY.ne'] at a
    have b : P.CYL * L.sc.L ≤ |P.CYL| * L.sc.L := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    linarith
  have hz : L.sc.L ≤ zBase L := by
    unfold zBase
    exact le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le hf hr)
  refine ⟨mul_ne_zero (mul_ne_zero hc0 (mul_ne_zero ?_ ?_)) (by norm_num), ?_⟩
  · exact_mod_cast (hg0 0).ne'
  · exact_mod_cast (hg0 1).ne'
  have a0 := hg0 0
  have a1 := hg0 1
  push_cast
  rw [Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by positivity),
    Real.log_mul a0.ne' a1.ne']
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hz (by positivity))
  linarith [hg 0, hg 1]

theorem dvd_of_mem_badPrimes {T : Core D} (hQ : T.Q.Pins) {j : ℕ} {Y : Deep T j} {e : ℕ} {o : ℝ} (h : Y.Good e o)
    {p : ℕ} (hp : p ∈ badPrimes T.Q.H Y.d.l₂) : p.Prime ∧ p ∣ LevelStarExponents.condE D * (D.host.g 0 * D.host.g 1) * 15 := by
  obtain ⟨hp, h'⟩ := mem_badPrimes.1 hp
  refine ⟨hp, ?_⟩
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * 15 ^ e := by rw [← h.pd, h.lev.1.2.1, hQ.2.1.1]
  have key : ∀ a, a ∣ LevelStarExponents.condE D → a ∣ LevelStarExponents.condE D * (D.host.g 0 * D.host.g 1) * 15 := fun a ha =>
    (ha.mul_right _).mul_right _
  have cD : ∀ a : ℕ, a.Prime → (a : ℤ) ∣ NumberField.discr D.host.E → a ∣ LevelStarExponents.condE D := D.host.der.discr_primes.1
  have c2 : 2 ∣ LevelStarExponents.condE D := cD 2 Nat.prime_two D.host.der.discr_primes.2.1
  have cd : D.host.d ∣ LevelStarExponents.condE D := cD _ D.host.hyp.2.1 D.host.der.discr_primes.2.2
  rcases h' with rfl | h' | h' | h' | h'
  · exact key _ c2
  · rw [h', hQ.1.1]; exact key _ cd
  · exact key _ (cD p hp (Int.natCast_dvd.2 h'))
  · rw [hM] at h'
    rcases (Nat.Prime.dvd_mul hp).1 h' with h' | h'
    · exact (h'.mul_left _).mul_right _
    · exact (hp.dvd_of_dvd_pow h').mul_left _
  · rw [h.lev.2] at h'
    exact absurd (Nat.dvd_one.1 h') hp.ne_one

theorem logSum_badPrimes_le : Size → Covers fun Fm x _ ι p _ Y _ C => logSum (badPrimes p.T.Q.H Y.d.l₂) ≤ C * zBase (Fm.L x ι) :=
  fun h => Closed.imp h fun Fm _ _ _ => ⟨2 * |Fm.CYL| + 17, by positivity, 0, fun x hx _ ι p _ i _ Y hY => by
    obtain ⟨a, b⟩ := log_level_le (Fm.params x hx ι)
    rw [Fm.params_CYL] at b
    exact (logSum_le_log a fun q hq => dvd_of_mem_badPrimes p.fw.laws.pins hY.1 hq).trans b⟩

end GlobalTheory.BadLog

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffQCartierNumEquivMultipleNonnegSmul
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PairStep

theorem mult_nsmul' {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (D : CartierDiv X) (n : ℕ) (z : X) :
    (n • D).mult z = n * D.mult z := by
  induction n with
  | zero =>
    have h := CartierDiv.mult_add (0 : CartierDiv X) 0 z
    rw [add_zero] at h
    rw [zero_nsmul]; push_cast; omega
  | succ n ih => rw [succ_nsmul, CartierDiv.mult_add, ih]; push_cast; ring

theorem eff_nsmul' {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} (h : D.Eff) (n : ℕ) :
    (n • D).Eff := by
  induction n with
  | zero => rw [zero_nsmul]; exact CartierDiv.eff_zero
  | succ n ih => rw [succ_nsmul]; exact ih.add h

theorem qNum_smul : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (a c : ℚ) (D : X → ℚ), 0 ≤ c → QNum p N a D → QNum p N (c * a) (c • D) := by
  intro X _ _ p hp N a c D hc hD
  letI := algebraΓOfHom p
  obtain ⟨m, D₀, hm, hE, rfl, hI⟩ := hD
  obtain ⟨u, v, hv, rfl⟩ : ∃ u v : ℕ, 0 < v ∧ c = (u : ℚ) / v := by
    refine ⟨c.num.toNat, c.den, c.den_pos, ?_⟩
    have h0 : ((c.num.toNat : ℕ) : ℤ) = c.num := Int.toNat_of_nonneg (Rat.num_nonneg.2 hc)
    have hd : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_pos.ne'
    rw [eq_div_iff hd, Rat.mul_den_eq_num]
    exact_mod_cast h0.symm
  have hv' : (v : ℚ) ≠ 0 := by exact_mod_cast hv.ne'
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨v * m, u • D₀, Nat.mul_pos hv hm, eff_nsmul' hE u, ?_, fun C hC => ?_⟩
  · funext z
    simp only [qWeil, Pi.smul_apply, smul_eq_mul, mult_nsmul']
    push_cast
    field_simp
  · have e := interNumRed_of_cls_eq_nsmul_add ℂ X p hp (toLB (u • D₀)) (toLB D₀) (toLB D₀)
      (isLB_toLB _) (isLB_toLB _) (isLB_toLB _) u 0 C hC
      (by rw [← toPic_apply, ← toPic_apply, map_nsmul, zero_nsmul, add_zero])
    rw [e, Nat.cast_zero, zero_mul, add_zero]
    have h1 := hI C hC
    push_cast
    rw [mul_assoc, ← h1]
    field_simp

end GlobalTheory.PairStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfGermEqZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.Vanishing.ProdNe

theorem eq_zero_of_germ_eq_zero {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y]
    {p : Y ⟶ Sp k} {B : LB Y} (hc : ∀ z : Y, ∃ j, z ∈ B.U j) (f : H0 p B ⊤) (y : Y) (i : B.ι)
    (hi : y ∈ B.U i) (h0 : H0.germ i y (show y ∈ (⊤ : Y.Opens) from trivial) hi f = 0) : f = 0 := by
  have hi0 : f.loc i = 0 := by
    apply germ_injective_of_isIntegral Y y (memInf (U := ⊤) trivial hi)
    rw [map_zero]
    exact h0
  refine H0.ext_germ fun z hz => ?_
  obtain ⟨j, hj⟩ := hc z
  refine ⟨j, hj, ?_⟩
  have hj0 : f.loc j = 0 := by
    obtain ⟨w, hwi, hwj⟩ :=
      nonempty_preirreducible_inter (B.U i).isOpen (B.U j).isOpen ⟨y, hi⟩ ⟨z, hj⟩
    apply germ_injective_of_isIntegral Y w (memInf (U := ⊤) trivial hwj)
    rw [map_zero]
    have e := H0.germ_change (O := ⊤) i j w (show w ∈ (⊤ : Y.Opens) from trivial) hwi hwj f
    have e2 : H0.germ (O := ⊤) i w (show w ∈ (⊤ : Y.Opens) from trivial) hwi f = 0 := by
      rw [H0.germ_apply, hi0, map_zero]
    rw [e2] at e
    rcases mul_eq_zero.mp e.symm with h | h
    · exact absurd h (Units.ne_zero _)
    · exact h
  rw [H0.germ_apply, hj0, map_zero, map_zero]

theorem mul_ne_zero : ∀ {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] {p : Y ⟶ Sp k} {P B N : LB Y} (C : ProdChart P B N) (σ : H0 p P ⊤) (f : H0 p B ⊤), σ ≠ 0 → f ≠ 0 → C.mul σ f ≠ 0 := by
  intro k _ Y _ p P B N C σ f hσ hf hmul
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  obtain ⟨t, ha, hb, hc⟩ := C.cover y
  have e := C.germ_mul σ f t y trivial ha hb hc
  rw [hmul, map_zero] at e
  rcases mul_eq_zero.mp e.symm with h | h
  · exact hσ (eq_zero_of_germ_eq_zero (fun z => let ⟨t, h⟩ := C.cover z; ⟨C.a t, h.1⟩) σ y _ ha h)
  · exact hf (eq_zero_of_germ_eq_zero (fun z => let ⟨t, h⟩ := C.cover z; ⟨C.b t, h.2.1⟩) f y _ hb h)

end GlobalTheory.Vanishing.ProdNe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmGoodReductionPointOnComponentStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cm_goodReduction_point_on_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c), ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra c.F K) (y : FrPt Xo c K) (ρ₀ : 𝓞 K) (σ₁ : K →+* ℂ) (X : GlobalTheory.CM.CMObj H K ρ₀ σ₁ Dw.p Dw.q) (t₀ : SAB H (Sp K)), LiesOn Z y ∧ Nonempty (SABMap t₀ Xo.univ.t y.x) ∧ Nonempty (SABMap t₀ X.B.t (spMap (algebraMap (𝓞 K) K))) ∧ ∀ τ : Psi H, ((ρ₀ : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 H.rt) := by
  first | exact @GlobalTheory.FlatCore.exists_cmPt_on_comp | exact GlobalTheory.FlatCore.exists_cmPt_on_comp | (intros; apply GlobalTheory.FlatCore.exists_cmPt_on_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualWeylTensorLiftCoefficientSpaceStatement
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualWeylTensor_lift_coefficientSpace : ∀ (K C : Type) [Field K] [Field C] (e0 : K →+* C) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ), Shift lam lamW c → ∃ Φ : VV K lam →ₛₗ[e0] NablaT C n lamW, IsPhi e0 lam lamW Φ ∧ LinearIndependent C fun i => Φ (bVV K lam i) := by
  first | exact @GlobalTheory.FrameRead.ExPhi.exists_phi | exact GlobalTheory.FrameRead.ExPhi.exists_phi | (intros; apply GlobalTheory.FrameRead.ExPhi.exists_phi <;> assumption)
end

