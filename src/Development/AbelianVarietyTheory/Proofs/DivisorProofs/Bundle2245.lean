import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2207
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalShareSumBound
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.HeightProofs.OpenImmersionCompStructureEqGeneric
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumOnGoodPlaces
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnramPtsDefinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2196
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureBaseChangeLabelsTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelCarry

theorem linComb_prod' {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ}
    (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) : linComb y a = ∏ i, y i ^ a i := List.prod_ofFn

theorem unitOn_zpow' {R : Type} [CommRing R] (u : Rˣ) (n : ℤ) : unitOn (u ^ n) = unitOn u ^ n :=
  map_zpow _ _ _

theorem unitOn_inj' {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := by
  intro a b h
  apply Units.ext
  have h' := congrArg Units.val h
  simp only [unitOn, Units.coe_map] at h'
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective h'

end GlobalTheory.LevelCarry

open GlobalTheory.LevelCarry in

theorem GlobalTheory.levelPoint_baseChange_label : ∀ (K C : Type) [Field K] [Field C] [IsAlgClosed C] (f : K →+* C) (P : PolAV (Sp K))
    (P' : PolAV (Sp C)) (io : (Over.mk (spMap f) ⟶ P.A) ≃* (baseOver (Sp C) ⟶ P'.A)),
    (∀ (k : ℕ) a b (z : Γ(Sp C, ⊤)ˣ), WeilIs P'.A P'.L k (io a) (io b) z → WeilIs P.A P.L k a b z) →
    ∀ (g k : ℕ) (hg : P'.g = g) (ζ : Cˣ) (lev : Out.Level P' k (unitOn ζ)), 2 ≤ k →
      IsPrimitiveRoot ζ k ∧
      (∀ a b, io.symm (levelPoint lev hg (a + b)) = io.symm (levelPoint lev hg a) * io.symm (levelPoint lev hg b)) ∧
      Function.Injective (fun a => io.symm (levelPoint lev hg a)) ∧
      (∀ z : Over.mk (spMap f) ⟶ P.A, z ^ k = 1 → ∃ a, io.symm (levelPoint lev hg a) = z) ∧
      ∀ i j, WeilIs P.A P.L k (io.symm (levelPoint lev hg (Pi.single i 1))) (io.symm (levelPoint lev hg (Pi.single j 1)))
        (unitOn (ζ ^ stdSymp g i j)) := by
  intro K C _ _ _ f P P' io hW g k hg ζ lev hk
  subst hg
  have := P'.isAb.comm
  have hk0 : NeZero k := ⟨by omega⟩
  have E : ∀ c : Fin (2 * P'.g) → ℕ,
      linComb (fun i => (Over.homMk (𝟙 _) (by simp) : Over.mk (𝟙 _) ⟶ baseOver _) ≫ lev.pt i) c =
      linComb lev.pt c := fun c => congrArg (linComb · _) (funext fun i => Category.id_comp (lev.pt i))
  have LP : ∀ a, levelPoint lev rfl a = ∏ i, lev.pt i ^ (a i).val := fun a => by
    rw [levelPoint_rfl]; exact linComb_prod' _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsPrimitiveRoot.of_map_of_injective
      (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom.toMonoidHom) lev.prim unitOn_inj'
  · intro a b
    rw [← map_mul]
    congr 1
    rw [LP, LP, LP, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_add, pow_eq_pow_mod ((a i).val + (b i).val) (lev.torsion i), Pi.add_apply, ZMod.val_add]
  · have inj : Function.Injective (levelPoint lev rfl) := by
      intro a b h
      have h₀ := lev.indep C (𝟙 _) (fun i => ⟨(a i).val, ZMod.val_lt _⟩) (fun i => ⟨(b i).val, ZMod.val_lt _⟩)
        ((E _).trans (h.trans (E _).symm))
      exact funext fun i => ZMod.val_injective k (congrArg Fin.val (congrFun h₀ i))
    exact io.symm.injective.comp inj
  · intro z hz
    have hz' : (io z) ^ k = 1 := by rw [← map_pow, hz, map_one]
    obtain ⟨c, hc⟩ := lev.span C (𝟙 _) (io z) hz'
    refine ⟨fun i => ((c i : ℕ) : ZMod k), ?_⟩
    rw [MulEquiv.symm_apply_eq, levelPoint_rfl, Level.toPt]
    exact (congrArg (linComb lev.pt) (funext fun i => ZMod.val_natCast_of_lt (c i).isLt)).trans
      ((E _).symm.trans hc)
  · intro i j
    haveI : Fact (1 < k) := ⟨by omega⟩
    have hs : ∀ i, levelPoint lev rfl (Pi.single i 1) = lev.pt i := fun i => by
      rw [LP, Finset.prod_eq_single i]
      · rw [Pi.single_eq_same, ZMod.val_one, pow_one]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, ZMod.val_zero, pow_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hs, hs]
    apply hW
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, unitOn_zpow']
    exact lev.pairing i j
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.MBLow

theorem hypS_of_isPolFibre : ∀ (K K' : Type) [Field K] [Field K'] (f : K →+* K') (P : PolAV (Sp K)) (P' : PolAV (Sp K')) (ψ : P'.A.left ⟶ P.A.left), IsPolFibre f P P' ψ → (letI := P.isAb.comm; GlobalTheory.ZH.HypS P.A P.L) → (letI := P'.isAb.comm; GlobalTheory.ZH.HypS P'.A P'.L) := by
  intro K K' _ _ f P P' ψ h hS
  letI := P.isAb.comm
  letI := P'.isAb.comm
  exact GlobalTheory.SymBaseChange.hypS_baseChange _ _ P.A P'.A (spMap f) ψ P.L P'.L P.isLB P'.isLB h.2.1 h.2.2.symm hS
end GlobalTheory.MBLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleValueAtPointNeZeroIffMemNonzeroLocus
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
open GlobalTheory.Discrepancy GlobalTheory.QCoh

noncomputable section

namespace GlobalTheory.ValNe

theorem evalPt_eq_stalkClosedPointTo {Y : Scheme.{0}} {V : Type} [CommRing V] [IsLocalRing V] (x : Sp V ⟶ Y) (W : Y.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (g : Γ(Y, W)) (hy : x (IsLocalRing.closedPoint V) ∈ W) :
    (Scheme.stalkClosedPointTo (R := CommRingCat.of V) x).hom (GlobalTheory.Vanishing.ger _ hy g) = TangentOrigin.evalPt x W h g := by
  have key := Scheme.germ_stalkClosedPointTo (R := CommRingCat.of V) x W hy
  have := congrArg (fun φ => φ.hom g) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  refine this.trans ?_
  simp only [TangentOrigin.evalPt, Scheme.Hom.appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, CommRingCat.hom_comp, RingHom.comp_apply, Category.assoc]
  congr!

theorem val_ofSec_ne_zero_iff : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (q : Y ⟶ Sp K) (L : LB Y) (σ : L.Sec) (z : Sp K ⟶ Y) (i : L.ι) (hi : ⊤ ≤ z ⁻¹ᵁ L.U i), (H0.val (p := q) z i le_top hi (H0.ofSec q ⊤ σ) ≠ 0 ↔ z (IsLocalRing.closedPoint K) ∈ nonzeroLocus σ) := by
  intro K _ Y q L σ z i hi
  have hy : z (IsLocalRing.closedPoint K) ∈ L.U i := hi (Set.mem_univ _)
  have e : H0.val (p := q) z i le_top hi (H0.ofSec q ⊤ σ) = TangentOrigin.evalPt z _ hi (σ.f i) :=
    H0.val_ofSec z i le_top hi σ
  rw [e, ← evalPt_eq_stalkClosedPointTo z (L.U i) hi (σ.f i) hy, ← isUnit_iff_ne_zero,
    isUnit_map_iff, GlobalTheory.Vanishing.isUnit_ger_iff σ hy]

end GlobalTheory.ValNe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalDepthOverDvrEqOverClosedFieldStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localDepth_over_dvr_eq_over_closed_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), ∀ k : ℕ, nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (polyT B cx) = GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuLocX_vp Ch X cx B k := by
  first | exact @GlobalTheory.DepthDescent.nuLocOf_eq_nuLocX_vp | exact GlobalTheory.DepthDescent.nuLocOf_eq_nuLocX_vp | (intros; apply GlobalTheory.DepthDescent.nuLocOf_eq_nuLocX_vp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalDepthStableUnderPrimePowPerturbationStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localDepth_stable_under_prime_pow_perturbation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (e : ℕ), 0 < e → vV T.V (p : T.Fr) = e → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n N k : ℕ) (ρ B : ℝ) (P₀ R : MvPolynomial (LtN Dw n) T.Fr), ChBound Ch e ρ a n → R ∈ FFV (Dw := Dw) T a n → nuLocOf Ch e k P₀ ≤ (B : EReal) → B + ρ < N → nuLocOf Ch e k (P₀ + ((p : T.Fr) ^ N) • R) = nuLocOf Ch e k P₀ := by
  first | exact @GlobalTheory.nuLocOf_pert | exact GlobalTheory.nuLocOf_pert | (intros; apply GlobalTheory.nuLocOf_pert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalShareSumBoundStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_share_sum_bound : Hypotheses2 → GlobalTheory.Published.GreenCuspidal → Lifts fun Fm x _ ι _ _ _ _ => ∃ ψ₀ : ∀ k : Fin 2, AddChar (ZMod ((Fm.D x ι).host.g k)) ℂ, (∀ k, ψ₀ k ≠ 1) ∧ ∀ S : ∀ k : Fin 2, Finset (Formalism.MainNotions.ArithmeticCylinders.Tup (Fm.D x ι) k), (∀ k, ∀ t ∈ S k, ¬ Formalism.MainNotions.ArithmeticCylinders.goodAt (Fm.D x ι) k t) → Formalism.MainNotions.ArithmeticCylinders.locShare (Fm.D x ι) (fun k _ => Formalism.MainNotions.ArithmeticCylinders.eUk (Fm.D x ι) k (ψ₀ k)) 0 (S 0) + Formalism.MainNotions.ArithmeticCylinders.locShare (Fm.D x ι) (fun k _ => Formalism.MainNotions.ArithmeticCylinders.eUk (Fm.D x ι) k (ψ₀ k)) 1 (S 1) ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) := by
  first | exact @GlobalTheory.CovTop.LocShareNum.locShares_le_exp | exact GlobalTheory.CovTop.LocShareNum.locShares_le_exp | (intros; apply GlobalTheory.CovTop.LocShareNum.locShares_le_exp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLowestKTypeWeylDimensionLeOfSizeBounds
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.OneMeasDim

theorem two_mul_card_pairs_le (p : ℕ) :
    2 * ∑ i : Fin p, (Finset.univ.filter (fun j : Fin p => i < j)).card ≤ p ^ 2 := by
  have e : ∑ i : Fin p, (Finset.univ.filter (fun j : Fin p => i < j)).card = ∑ i ∈ Finset.range p, i := by
    rw [← Finset.sum_range_reflect]
    rw [Fin.sum_univ_eq_sum_range (fun i => p - 1 - i) p |>.symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  rw [e, mul_comm, Finset.sum_range_id_mul_two]
  rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

theorem abs_factor_le (d : ℤ) (i j : ℕ) (hij : i < j) :
    |((((d : ℚ) + (j : ℚ) - (i : ℚ)) / ((j : ℚ) - (i : ℚ)) : ℚ) : ℝ)| ≤ 1 + |(d : ℝ)| := by
  have hs : (1 : ℝ) ≤ (j : ℝ) - (i : ℝ) := by
    have : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
    linarith
  have hs0 : (0 : ℝ) < (j : ℝ) - (i : ℝ) := by linarith
  push_cast
  rw [abs_div, abs_of_pos hs0, div_le_iff₀ hs0]
  have h1 : |(d : ℝ) + (j : ℝ) - (i : ℝ)| ≤ |(d : ℝ)| + ((j : ℝ) - (i : ℝ)) := by
    have := abs_add_le (d : ℝ) ((j : ℝ) - (i : ℝ))
    rw [abs_of_pos hs0] at this
    rw [show (d : ℝ) + (j : ℝ) - (i : ℝ) = (d : ℝ) + ((j : ℝ) - (i : ℝ)) by ring]
    exact this
  nlinarith [abs_nonneg (d : ℝ)]

theorem abs_weylDimU_le {p : ℕ} (lam : Fin p → ℤ) (B : ℝ) (hB : ∀ a b, |((lam a - lam b : ℤ) : ℝ)| ≤ B) :
    |((Formalism.IndefR.Mult.weylDimU lam : ℚ) : ℝ)| ≤
      (1 + B) ^ (∑ i : Fin p, (Finset.univ.filter (fun j : Fin p => i < j)).card) := by
  unfold Formalism.IndefR.Mult.weylDimU
  rw [Rat.cast_prod, Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => ?_
  rw [Rat.cast_prod, Finset.abs_prod, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun j hj => ?_
  have hij : (i : ℕ) < (j : ℕ) := (Finset.mem_filter.1 hj).2
  have := abs_factor_le (lam i - lam j) i j hij
  exact this.trans (by linarith [hB i j])

end GlobalTheory.OneMeasDim

namespace GlobalTheory.OneMeasDim

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem abs_wt_sub_le (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (a b : Fin ((Wc D i).sig (tauE D τ)).1 ⊕ Fin ((Wc D i).sig (tauE D τ)).2) :
    |((Formalism.L2.NTheta.wtOf D (Wc D i) τ a - Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ)| ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize D i := by
  have hw : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize D i :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  by_cases hab : a = b
  · subst hab; simpa using hw
  set c : ℝ := (((D.hc τ).e i : ℚ) : ℝ)
  set g : (Fin ((Wc D i).sig (tauE D τ)).1 ⊕ Fin ((Wc D i).sig (tauE D τ)).2) → ℝ :=
    fun x => |((Formalism.L2.NTheta.wtOf D (Wc D i) τ x : ℤ) : ℝ) + c| with hg
  have h1 : |((Formalism.L2.NTheta.wtOf D (Wc D i) τ a - Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ)| ≤ g a + g b := by
    rw [hg]; push_cast
    have := abs_sub (((Formalism.L2.NTheta.wtOf D (Wc D i) τ a : ℤ) : ℝ) + c) (((Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ) + c)
    rw [show (((Formalism.L2.NTheta.wtOf D (Wc D i) τ a : ℤ) : ℝ) + c) - (((Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ) + c) =
      ((Formalism.L2.NTheta.wtOf D (Wc D i) τ a : ℤ) : ℝ) - ((Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ) by ring] at this
    exact this
  have h2 : g a + g b ≤ ∑ x, g x := by
    rw [← Finset.sum_pair hab]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _
  have h3 : ∑ x, g x ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize D i := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize
    exact Finset.single_le_sum (f := fun τ' => ∑ x, |((Formalism.L2.NTheta.wtOf D (Wc D i) τ' x : ℤ) : ℝ) + (((D.hc τ').e i : ℚ) : ℝ)|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ τ)
  linarith

theorem log_dimAt_le : ∀ (D : D7) (i : Fin D.R.m) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L) (τ : D.what₂.Tau),
    Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ 3 / 2 * (D.R.r : ℝ) ^ 2 * L := by
  intro D i L hL τ
  obtain ⟨hf, hs, -, -⟩ := hL

  have hb2 : (2 : ℝ) ≤ Real.exp L := by
    have hr : 1 ≤ D.R.r := by
      have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Formalism.BasicNotions.Ranks.r; omega
    have hfn : 2 ≤ D.R.f := by
      unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
    have hn : 1 ≤ D.R.nV := by unfold Formalism.BasicNotions.Ranks.nV; omega
    have : (2 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * D.R.nV := by
      have : 2 ≤ D.R.f * D.R.r * D.R.nV := by
        calc 2 ≤ D.R.f := hfn
          _ = D.R.f * 1 * 1 := by ring
          _ ≤ D.R.f * D.R.r * D.R.nV := by gcongr
      exact_mod_cast this
    linarith
  have hL0 : 0 ≤ L := by
    by_contra h; push_neg at h
    have := Real.exp_lt_exp.2 h; rw [Real.exp_zero] at this; linarith
  set b := Real.exp L with hbdef
  set B := b ^ 2
  have h1B : 1 + B ≤ Real.exp (3 * L) := by
    rw [show 3 * L = L + L + L by ring, Real.exp_add, Real.exp_add, ← hbdef]
    nlinarith
  have hlog1B : Real.log (1 + B) ≤ 3 * L := by
    have := Real.log_le_log (by positivity) h1B
    rwa [Real.log_exp] at this

  set p := ((Wc D i).sig (tauE D τ)).1
  set q := ((Wc D i).sig (tauE D τ)).2
  have hpq : p + q = D.R.r := by
    have hr := D.sp.W_rank ((i:ℕ)+1) (by omega) (by have := i.2; omega)
    rw [← hr]; obtain ⟨e, -⟩ := (D.sp.W_sig ((i:ℕ)+1)) (tauE D τ); simpa using (Fintype.card_congr e).symm
  set κ := Formalism.L2.NTheta.wtOf D (Wc D i) τ
  have hent : ∀ a b, |((κ a - κ b : ℤ) : ℝ)| ≤ B := fun a b => (abs_wt_sub_le D i τ a b).trans (hs i)
  set N1 := ∑ a : Fin p, (Finset.univ.filter (fun j : Fin p => a < j)).card
  set N2 := ∑ a : Fin q, (Finset.univ.filter (fun j : Fin q => a < j)).card
  have w1 := abs_weylDimU_le (fun a => κ (Sum.inl a)) B (fun a b => hent _ _)
  have w2 := abs_weylDimU_le (fun a => κ (Sum.inr a)) B (fun a b => hent _ _)
  have hdim : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ =
      ((Formalism.IndefR.Mult.weylDimU (fun a => κ (Sum.inl a)) : ℚ) : ℝ) *
        ((Formalism.IndefR.Mult.weylDimU (fun a => κ (Sum.inr a)) : ℚ) : ℝ) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt Formalism.IndefR.Mult.dimK; push_cast; rfl
  have habs : |GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ| ≤ (1 + B) ^ (N1 + N2) := by
    rw [hdim, abs_mul, pow_add]
    exact mul_le_mul w1 w2 (abs_nonneg _) (by positivity)
  have hlog : Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ ((N1 + N2 : ℕ) : ℝ) * Real.log (1 + B) := by
    rw [← Real.log_abs]
    rcases eq_or_ne (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) 0 with h0 | h0
    · rw [h0, abs_zero, Real.log_zero]
      have hB0 : (0 : ℝ) ≤ B := sq_nonneg b
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
    · have := Real.log_le_log (abs_pos.2 h0) habs
      rwa [Real.log_pow] at this
  have hN : 2 * (N1 + N2) ≤ D.R.r ^ 2 := by
    have a1 : 2 * N1 ≤ p ^ 2 := two_mul_card_pairs_le p
    have a2 : 2 * N2 ≤ q ^ 2 := two_mul_card_pairs_le q
    have a3 : p ^ 2 + q ^ 2 ≤ (p + q) ^ 2 := by ring_nf; omega
    rw [← hpq]; omega
  have hN' : 2 * ((N1 + N2 : ℕ) : ℝ) ≤ (D.R.r : ℝ) ^ 2 := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ ((N1 + N2 : ℕ) : ℝ) := Nat.cast_nonneg _
  calc Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ ((N1 + N2 : ℕ) : ℝ) * Real.log (1 + B) := hlog
    _ ≤ ((N1 + N2 : ℕ) : ℝ) * (3 * L) := mul_le_mul_of_nonneg_left hlog1B hN0
    _ = 3 / 2 * (2 * ((N1 + N2 : ℕ) : ℝ)) * L := by ring
    _ ≤ 3 / 2 * (D.R.r : ℝ) ^ 2 * L := by gcongr

end GlobalTheory.OneMeasDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogPeriodEqKroneckerCharacterLogPeriodOfHostStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logPeriod_eq_kroneckerCharacter_logPeriod_of_host : ∀ (D : D7) (L : SizeData₂ D) (Q : Par D), Q.PinHost → ∀ (Del h0 : ℕ), ∃ (_ : NeZero Q.H.d) (χ : DirichletCharacter ℂ Q.H.d), GlobalTheory.IsKroneckerChar χ ∧ (GlobalTheory.CM.logOm D.host.E χ).re = (ofRecord D L Del h0).logOm ∧ (ofRecord D L Del h0).logOm = L.logOm ∧ GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField Q.H := by
  first | exact @GlobalTheory.CovTop.Period.period_eq_kronecker | exact GlobalTheory.CovTop.Period.period_eq_kronecker | (intros; apply GlobalTheory.CovTop.Period.period_eq_kronecker <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemModelInteriorOfMemAbelianLocusPullback
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.AbInterior

theorem mem_interior_of_mem_abLocus : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) (S : Scheme.{0}) (f : S ⟶ Y.X) (G : SAB H S), SABMap G Y.t f → ∀ s : S, s ∈ abLocus G.G → f s ∈ (LogKS.interior Y : Set Y.X) := by
  intro E _ _ _ H Dw l Xo c Y S f G m s hs
  rw [LogKS.coe_interior]
  exact (OneArcCompare.mem_abLocus_pullback Y.t.semi m.cart.1 s).2 hs

end GlobalTheory.AbInterior
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuBoundNotAlgebraicallyClosedStatement
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mu_bound_not_algebraically_closed : Hypotheses2 → ∃ M : ℝ, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A : ℝ), RowsT p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → ¬ FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → 2 * defBound (dat p i) (wtA (p.κ i)) (p.κ i).n (-flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm) - C₀ * unitE p ≤ muCore p i := by
  first | exact @GlobalTheory.CoreDesc.def_of_not_fnAlgClosed | exact GlobalTheory.CoreDesc.def_of_not_fnAlgClosed | (intros; apply GlobalTheory.CoreDesc.def_of_not_fnAlgClosed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemCuspFormsOfBoundedSectionComponent
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

namespace GlobalTheory.BddCusp

theorem mul_mem_cuspOn_of_bdd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (G₀ : WTZ E) (s : Rul Xo c), Nonempty (KeySec Xo c) → (∀ σ, GoodEmb c σ → IsUnf (U σ)) → 1 ≤ Dw.p + Dw.q → Even G₀.2 → (∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ → G₀.1 (τ, j) ≤ G₀.1 (τ, i)) → s ∈ secZ Xo c (exZ Dw G₀) → s ∈ suppOn Z → (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x G₀ s z ≤ C) → ∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z G, f * s ∈ cuspOn U Z (G + G₀) := by
  intro E _ _ _ H Dw l Xo c r U x Z G₀ s hK hU hpq h0 hdec hs hZ hb G hG f hf
  exact mul_mem_cuspOn_of_isSec h0 hs hZ
    (fun σ hσ k => GlobalTheory.T.isSec_reading_decreasing_integer_exponents E H Dw l Xo c σ r (U σ) hK hσ (hU σ hσ) hpq G₀ h0 hdec s hs k) hb hG hf

end GlobalTheory.BddCusp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NullMeasurableSetClassesOverFramesOn
section
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

namespace GlobalTheory.ClassesMeas

theorem nullMeasurableSet_classesOver_framesOn : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ σ, GoodEmb c σ → ∀ Z : Comp Xo c, NullMeasurableSet (classesOver (V σ) (dict σ) (framesOn (U σ) Z)) (muQ1 (V σ)) := by
  intro D H Dw l Xo c r U V dict hC σ hσ Z
  obtain ⟨hU, ⟨Kf, th, hr, hK, _, hd⟩, _, _⟩ := hC.2 σ hσ
  obtain ⟨d1, d2, ⟨x0, _, d3⟩, d4, _, _⟩ := hd
  haveI : BorelSpace (GA D (V σ)) := ⟨rfl⟩
  let S : Set (U σ).Comp := {k | ∃ y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z}
  have key : ∀ g, dict σ g ∈ framesOn (U σ) Z ↔ (dict σ g).1 ∈ S := by
    intro g
    constructor
    · intro h
      exact ⟨(dict σ g).2, h⟩
    · rintro ⟨y, hy⟩
      exact GlobalTheory.T.framePointsOverComponent_open_set D.host.E H Dw l Xo c r U σ hU Z _ y _ (d4 g) hy
  have hP : IsOpen {g : GA D (V σ) | (dict σ g).1 ∈ S} := by
    rw [isOpen_iff_mem_nhds]
    intro g₀ hg₀
    refine Filter.mem_of_superset
      (GlobalTheory.LevelOpen.level_mem_nhds D (V σ) l.M Kf (by have := l.three_le; omega) hK g₀) ?_
    rintro g ⟨k, hk, h, hh, rfl⟩
    obtain ⟨γ, _, e1⟩ := d2 k hk g₀
    obtain ⟨γ', _, e2⟩ := d3 (g₀ * k) h hh
    have f1 := congrArg Sigma.fst e1
    have f2 := congrArg Sigma.fst e2
    show (dict σ (g₀ * k * h)).1 ∈ S
    rw [f2, f1]
    exact hg₀
  have hpre : (Quotient.mk'' ⁻¹' classesOver (V σ) (dict σ) (framesOn (U σ) Z) : Set (GA D (V σ))) =
      {g : GA D (V σ) | (dict σ g).1 ∈ S} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    show dict σ (Quotient.mk'' g : AutQ (V σ)).out ∈ framesOn (U σ) Z ↔ _
    rw [key]
    have hrel : QuotientGroup.rightRel (GQ (V σ)) (Quotient.mk'' g : AutQ (V σ)).out g :=
      Quotient.exact (Quotient.out_eq _)
    rw [QuotientGroup.rightRel_apply] at hrel
    obtain ⟨γ', _, e⟩ := d1 _ (inv_mem hrel) g
    have f := congrArg Sigma.fst e
    simp only [mul_inv_rev, inv_inv, inv_mul_cancel_right] at f
    rw [f]
  refine MeasurableSet.nullMeasurableSet ?_
  show MeasurableSet (Quotient.mk'' ⁻¹' classesOver (V σ) (dict σ) (framesOn (U σ) Z) : Set (GA D (V σ)))
  rw [hpre]
  exact hP.measurableSet

end GlobalTheory.ClassesMeas
end

