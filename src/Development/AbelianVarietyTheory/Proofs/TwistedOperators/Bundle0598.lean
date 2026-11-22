import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0010
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0379
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0587
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0554
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0404
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0576
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0305
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0407
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0574
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0343
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0580
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeOrbitVectorsMovedPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section
namespace GlobalTheory.MovedHomLat
open Matrix
variable {D : D7}
set_option synthInstance.maxHeartbeats 400000

theorem bridge (V : HSp D) (k : GA D V) (s : Fin V.rank → D.host.E) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((mt V k *ᵥ fun j => incA D (s j)) i)) =
      (Formalism.IndefR.Lev.finE V k).1 *ᵥ (fun j => Formalism.IndefR.Datum.eToEAf D (s j)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rfl

theorem fwd (V : HSp D) (k : GA D V) (C : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hfg : Module.Finite (𝓞 D.host.E) C) (hsp : Submodule.span D.host.E (C : Set (Fin V.rank → D.host.E)) = ⊤)
    (s : Fin V.rank → D.host.E) (hs : s ∈ C) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((mt V k *ᵥ fun j => incA D (s j)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE V k) C) := by
  have hmem : (fun j => Formalism.IndefR.Datum.eToEAf D (s j)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) C :=
    Submodule.subset_span ⟨s, hs, rfl⟩
  have key := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds D.host.F D.host.E (Fin V.rank) C hfg hsp
    (Formalism.IndefR.Lev.finE V k) ((Formalism.IndefR.Lev.finE V k).1 *ᵥ (fun j => Formalism.IndefR.Datum.eToEAf D (s j)))
  have e : ((Formalism.IndefR.Lev.finE V k)⁻¹ : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)).1 *ᵥ ((Formalism.IndefR.Lev.finE V k).1 *ᵥ (fun j => Formalism.IndefR.Datum.eToEAf D (s j))) = (fun j => Formalism.IndefR.Datum.eToEAf D (s j)) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [← e] at hmem
  have k2 := key.2 hmem
  have hb := bridge V k s
  simp only [hb]
  exact k2

theorem bwd (V : HSp D) (k : GA D V) (C : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (s : Fin V.rank → D.host.E) (hs : s ∈ Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE V k) C) :
    (fun i => Formalism.IndefR.Datum.toEAf D ((mt V k⁻¹ *ᵥ fun j => incA D (s j)) i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) C := by
  rw [bridge, map_inv]
  exact hs

theorem mem_globLat_iff {n : ℕ} (g : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (C : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (y : Fin n → D.host.E) :
    y ∈ Formalism.UG.CS.globLat g C ↔ (g⁻¹).1 *ᵥ (fun i => Formalism.IndefR.Datum.eToEAf D (y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) C :=
  Iff.rfl

theorem colLat_fin {n : ℕ} (B : GL (Fin n) D.host.E) : Module.Finite (𝓞 D.host.E) (colLat B) :=
  Module.Finite.iff_fg.2 (Submodule.fg_span (Set.finite_range _))

theorem colLat_span {n : ℕ} (B : GL (Fin n) D.host.E) :
    Submodule.span D.host.E (colLat B : Set (Fin n → D.host.E)) = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  have hcol : ∀ j : Fin n, (fun a : Fin n => (B : Matrix (Fin n) (Fin n) D.host.E) a j) ∈
      Submodule.span D.host.E (colLat B : Set (Fin n → D.host.E)) :=
    fun j => Submodule.subset_span (Submodule.subset_span ⟨j, rfl⟩)
  have e : v = ∑ j, ((B⁻¹ : GL (Fin n) D.host.E).1 *ᵥ v) j • (fun a : Fin n => (B : Matrix (Fin n) (Fin n) D.host.E) a j) := by
    have h1 : (B : Matrix (Fin n) (Fin n) D.host.E) *ᵥ ((B⁻¹ : GL (Fin n) D.host.E).1 *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    conv_lhs => rw [← h1]
    funext a
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hcol j)

set_option maxHeartbeats 1000000 in

theorem globLat_mul_iff {n : ℕ} (a b : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (Λ C : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hb : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) C ↔ b.1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) (y : Fin n → D.host.E) :
    y ∈ Formalism.UG.CS.globLat a Λ ↔ y ∈ Formalism.UG.CS.globLat (a * b) C := by
  rw [mem_globLat_iff, mem_globLat_iff]
  have e : ((a * b)⁻¹ : GL (Fin n) (Formalism.IndefR.Lev.EAf D)).1 = (b⁻¹).1 * (a⁻¹).1 := congrArg Units.val (_root_.mul_inv_rev a b)
  have e2 : b.1 * (b⁻¹).1 = 1 := congrArg Units.val (mul_inv_cancel b)
  rw [e, ← Matrix.mulVec_mulVec, hb ((b⁻¹).1 *ᵥ ((a⁻¹).1 *ᵥ fun i => Formalism.IndefR.Datum.eToEAf D (y i))),
    Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]

theorem movedLat_eq {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node) (hX : DefNode D.R.m X) (x : FinPt G X) :
    inV (S.N.fr X) (GlobalTheory.SumSize.latAt S X x) =
      (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (G.V X) ((x * S.N.u X : FinPt G X) : GA D (G.V X))) (colLat (S.N.fr X)) :
        Set (Fin (G.V X).rank → D.host.E)) := by
  have key : ∀ y, y ∈ Formalism.UG.CS.globLat (finG (G.V X) x) (G.Λ X) ↔
      y ∈ Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (G.V X) ((x * S.N.u X : FinPt G X) : GA D (G.V X))) (colLat (S.N.fr X)) := by
    have e : Formalism.IndefR.Lev.finE (G.V X) ((x * S.N.u X : FinPt G X) : GA D (G.V X)) =
        finG (G.V X) x * Formalism.IndefR.Lev.finE (G.V X) (S.N.u X).1 :=
      map_mul (Formalism.IndefR.Lev.finE (G.V X)) (x : GA D (G.V X)) (S.N.u X).1
    rw [e]
    exact globLat_mul_iff _ _ _ _ (S.N.u_lat X hX)
  ext y
  simp only [inV, GlobalTheory.SumSize.latAt, Set.mem_image, SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply,
    Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (key _).1 hz
  · intro hy
    refine ⟨((S.N.fr X)⁻¹ : GL _ D.host.E).1 *ᵥ y, ?_, ?_⟩ <;>
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    exact (key _).2 hy

theorem actO_latO_le (S T : HSp D) (g : GA D S) (h : GA D T)
    (AS BS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (AT BT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : ∀ s ∈ AS, (fun i => Formalism.IndefR.Datum.toEAf D ((mt S g *ᵥ fun k => incA D (s k)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) BS)
    (hT : ∀ t ∈ AT, (fun i => Formalism.IndefR.Datum.toEAf D ((mt T h *ᵥ fun k => incA D (t k)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) BT) :
    ∀ w ∈ latO S T (AS : Set (Fin S.rank → D.host.E)) (AT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      actO S T g h w ∈ latO S T (BS : Set (Fin S.rank → D.host.E)) (BT : Set (Fin T.rank → D.host.E)) (fun _ => True) :=
  GlobalTheory.T.weilActionO_mem_latticeO_of_integralCombinations S T g h AS BS AT BT (fun s hs => GlobalTheory.T.finitePart_eq_integralCombination_of_mem_completedLattice BS _ (hS s hs)) (fun t ht => GlobalTheory.T.finitePart_eq_integralCombination_of_mem_completedLattice BT _ (hT t ht))

theorem actO_actO_inv (S T : HSp D) (g : GA D S) (h : GA D T) (w : WO S T) : actO S T g h (actO S T g⁻¹ h⁻¹ w) = w := by
  simp only [actO]
  rw [inv_inv, Matrix.mul_assoc (mt T h), Matrix.mul_assoc (mt T h⁻¹ * w), ← GlobalTheory.LatMoveStd.mt_mul'', mul_inv_cancel,
    GlobalTheory.LatMoveStd.mt_one'', Matrix.mul_one, ← Matrix.mul_assoc, ← GlobalTheory.LatMoveStd.mt_mul'', mul_inv_cancel,
    GlobalTheory.LatMoveStd.mt_one'', Matrix.one_mul]

theorem actO_latO_onto (S T : HSp D) (g : GA D S) (h : GA D T)
    (AS BS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (AT BT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hS : ∀ s ∈ AS, (fun i => Formalism.IndefR.Datum.toEAf D ((mt S g *ᵥ fun k => incA D (s k)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) BS)
    (hT : ∀ t ∈ AT, (fun i => Formalism.IndefR.Datum.toEAf D ((mt T h *ᵥ fun k => incA D (t k)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) BT)
    (hS' : ∀ s ∈ BS, (fun i => Formalism.IndefR.Datum.toEAf D ((mt S g⁻¹ *ᵥ fun k => incA D (s k)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) AS)
    (hT' : ∀ t ∈ BT, (fun i => Formalism.IndefR.Datum.toEAf D ((mt T h⁻¹ *ᵥ fun k => incA D (t k)) i)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) AT) :
    (∀ w ∈ latO S T (AS : Set (Fin S.rank → D.host.E)) (AT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      actO S T g h w ∈ latO S T (BS : Set (Fin S.rank → D.host.E)) (BT : Set (Fin T.rank → D.host.E)) (fun _ => True)) ∧
    (∀ w' ∈ latO S T (BS : Set (Fin S.rank → D.host.E)) (BT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ∃ w ∈ latO S T (AS : Set (Fin S.rank → D.host.E)) (AT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        actO S T g h w = w') :=
  ⟨actO_latO_le S T g h AS BS AT BT hS hT, fun w' hw' =>
    ⟨actO S T g⁻¹ h⁻¹ w', actO_latO_le S T g⁻¹ h⁻¹ BS AS BT AT hS' hT' w' hw', actO_actO_inv S T g h w'⟩⟩

end GlobalTheory.MovedHomLat

open GlobalTheory.MovedHomLat in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.MovedDict.actO_latO_moved : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    (∀ w ∈ latO _ _ (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True), actO _ _ (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).1 (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).2 w ∈ latO _ _ (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (fun _ => True)) ∧
    (∀ w' ∈ latO _ _ (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (fun _ => True), ∃ w ∈ latO _ _ (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True), actO _ _ (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).1 (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).2 w = w') := by
  intro _ _ D Γ _ _ Pl0 T A Ks _ _ _ R ch _ p hp x y
  have hn := DefPair.nodes hp
  cases p with
  | chi i j =>
    rw [show inV (frS ch.S.N (.chi i j)) (srcLat ch.S.toGridChoice (.chi i j) x y) = _ from
        movedLat_eq ch.S.toGridChoice _ hn.2 y,
      show inV (frT ch.S.N (.chi i j)) (tgtLat ch.S.toGridChoice (.chi i j) x y) = _ from
        movedLat_eq ch.S.toGridChoice _ hn.1 x]
    let N := ch.S.N
    let ky : Formalism.L2.Theta.GA D (ch.G.V (.grid (i + 1) j)) := ((y * N.u (.grid (i + 1) j) : FinPt ch.G (.grid (i + 1) j)) : Formalism.L2.Theta.GA D _)
    let kx : Formalism.L2.Theta.GA D (ch.G.V (.grid i j)) := ((x * N.u (.grid i j) : FinPt ch.G (.grid i j)) : Formalism.L2.Theta.GA D _)
    have H := actO_latO_onto (negSp (ch.G.V (.grid (i + 1) j))) (ch.G.V (.grid i j)) (negGA _ ky) kx
      (colLat (N.fr (.grid (i + 1) j)))
      (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (ch.G.V (.grid (i + 1) j)) ky) (colLat (N.fr (.grid (i + 1) j))))
      (colLat (N.fr (.grid i j)))
      (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (ch.G.V (.grid i j)) kx) (colLat (N.fr (.grid i j))))
      (fwd (ch.G.V (.grid (i + 1) j)) ky _ (colLat_fin _) (colLat_span _))
      (fwd (ch.G.V (.grid i j)) kx _ (colLat_fin _) (colLat_span _))
      (bwd (ch.G.V (.grid (i + 1) j)) ky _)
      (bwd (ch.G.V (.grid i j)) kx _)
    exact H
  | top t j =>
    rw [show inV (frS ch.S.N (.top t j)) (srcLat ch.S.toGridChoice (.top t j) x y) = _ from
        movedLat_eq ch.S.toGridChoice _ hn.1 x,
      show inV (frT ch.S.N (.top t j)) (tgtLat ch.S.toGridChoice (.top t j) x y) = _ from
        movedLat_eq ch.S.toGridChoice _ hn.2 y]
    let N := ch.S.N
    let kx : Formalism.L2.Theta.GA D (ch.G.V (.top j)) := ((x * N.u (.top j) : FinPt ch.G (.top j)) : Formalism.L2.Theta.GA D _)
    let ky : Formalism.L2.Theta.GA D (ch.G.V (.top (j + 1))) := ((y * N.u (.top (j + 1)) : FinPt ch.G (.top (j + 1))) : Formalism.L2.Theta.GA D _)
    have H := actO_latO_onto (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) kx ky
      (colLat (N.fr (.top j)))
      (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (ch.G.V (.top j)) kx) (colLat (N.fr (.top j))))
      (colLat (N.fr (.top (j + 1))))
      (Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE (ch.G.V (.top (j + 1))) ky) (colLat (N.fr (.top (j + 1)))))
      (fwd (ch.G.V (.top j)) kx _ (colLat_fin _) (colLat_span _))
      (fwd (ch.G.V (.top (j + 1))) ky _ (colLat_fin _) (colLat_span _))
      (bwd (ch.G.V (.top j)) kx _)
      (bwd (ch.G.V (.top (j + 1))) ky _)
    exact H
  | mu t i j => exact absurd hp (by simp [DefPair])
  | core i => exact absurd hp (by simp [DefPair])
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieWordExpansionUniform
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace

namespace GlobalTheory.PlaceDecomp

theorem rankOne_values_gkMap : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → GlobalTheory.FunPr.Hypotheses₂ → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (φ : GA D N.V → ℂ) (S : GA D N.V → List (List (Mx N.V.rank))) (v : GA D N.V → ℕ → N.M.H τ) (ℓ : GA D N.V → ℕ → (N.M.H τ →ₗ[ℂ] ℂ)) (C : GA D N.V → ℕ → ℝ), (∀ x, Words (lieSet (N.M.ε τ)) (S x)) → (∀ x, Ctrl (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) (N.M.σ τ) (S x)) → (∀ x, Expn (N.M.ε τ) (N.M.σ τ) (S x) (v x) (ℓ x) (C x) (res θ N.V τ (N.M.fr τ) φ x)) → ∀ (c : N.M.H τ) (ψ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ → GA D N.V → ℂ), (∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, Moves θ N.V τ (N.M.ε τ) (N.M.σ τ) (N.M.fr τ) (fun w => ⟪c, w⟫_ℂ • (u : N.M.H τ)) φ (ψ u)) → (∀ u x, ψ u x = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i u) ∧ (∀ u u', ψ (u + u') = ψ u + ψ u') ∧ (∀ (z : ℂ) u, ψ (z • u) = z • ψ u) ∧ (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, (w : N.M.H τ) = N.M.rep τ k u → ψ w = rTr N.V (atTau θ N.V τ k) (ψ u)) ∧ (∀ X ∈ lieAt N.V τ, ∀ u w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, (w : N.M.H τ) = dRep (N.M.rep τ) X u → ψ w = Rder θ N.V τ X (ψ u)) := by
  intro D θ hθ hp N τ φ S v ℓ C hS hc h c ψ hψ
  have hσ : Std (N.M.ε τ) (N.M.σ τ) := std_of_isDS hp.harishChandraModules (N.M.ds τ)
  have hP := N.M.fr_unit τ
  haveI : CompleteSpace (N.M.H τ) := (N.M.ds τ).1
  have hJ := N.M.fr_gram τ
  have hb := fun x => (h x).sobFun (hS x) c
  have hsm : ∀ u : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ, Sm (N.M.ε τ) (N.M.σ τ) u := fun u => hσ.2.2.1 _ u.2
  have key : ∀ u x, ∀ y ∈ UJset (N.M.ε τ),
      res θ N.V τ (N.M.fr τ) (ψ u) x y = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i (N.M.σ τ y u) := by
    intro u x y hy
    have := (hψ u x _ _ _ _ (hS x) (hc x) (h x)).1.2.2.2.2 y hy
    simp only [map_smul, smul_eq_mul] at this
    exact this.tsum_eq.symm
  have hval : ∀ u x, ψ u x = ∑' i, ⟪c, v x i⟫_ℂ * ℓ x i u := by
    intro u x
    have := key u x 1 (one_mem_UJ _)
    rwa [res_one hθ hP, sigma_one hσ.1] at this
  refine ⟨hval, fun u u' => funext fun x => ?_, fun z u => funext fun x => ?_, ?_, ?_⟩
  · rw [Pi.add_apply, hval, hval, hval, Submodule.coe_add]
    exact (hb x).1 _ _ (hsm u) (hsm u')
  · rw [Pi.smul_apply, hval, hval, Submodule.coe_smul, smul_eq_mul]
    exact (hb x).2.1 z _ (hsm u)
  · intro k hk u w hw
    funext x
    rw [rTr, ← res_conj hP (ψ u) x k, key u x _ (K_le_UJ hk), hval, hw]
    rfl
  · intro X hX u w hw
    funext x
    have hd := (isUnit_iff_isUnit_det _).1 hP
    have hY : N.M.fr τ * X * (N.M.fr τ)⁻¹ ∈ lieSet (N.M.ε τ) := by
      refine Transport.conj_lie (G := gramAt D N.V τ) (Matrix.nonsing_inv_mul _ hd) ?_ hX
      rw [← hJ]
      calc _ = (N.M.fr τ * (N.M.fr τ)⁻¹)ᴴ * Jm (N.M.ε τ) * (N.M.fr τ * (N.M.fr τ)⁻¹) := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp
    have e : (w : N.M.H τ) = dRep (N.M.σ τ) (N.M.fr τ * X * (N.M.fr τ)⁻¹) u := by
      rw [hw]
      unfold dRep
      congr 1
      funext t
      rw [Transport.exp_smul_conj hP]
      rfl
    have h1 := (hσ.hasDerivAt_sobFun (hb x) (hsm u) hY).deriv
    rw [← e] at h1
    rw [hval]
    refine h1.symm.trans ?_
    unfold Rder oneP
    congr 1
    funext t
    rw [← res_conj hP (ψ u) x, ← Transport.exp_smul_conj hP, key u x _ (exp_mem_UJ hY t)]

end GlobalTheory.PlaceDecomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSelfDualLatticeOfMemAllLatticeCompletions
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.FinPl.LocGlob

variable {D : D7}

theorem swap_finPart_pure (α : Af D.host.F) (e : D.host.E) :
    Formalism.IndefR.Lev.swapAE D (finPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] e)) = e ⊗ₜ[D.host.F] α := by
  have h1 : finPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] e) = α ⊗ₜ[D.host.F] e := by
    unfold finPart
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
    rfl
  rw [h1]
  rfl

theorem mem_of_local {S : HSp D} {L : GlobalTheory.FinPl.Lat S} (hL : IsSelfDualC S L) (z : Fin S.rank → D.host.E)
    (hz : ∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈
      GlobalTheory.FinPl.latV S L (· = v)) : z ∈ L := by
  classical
  have hlat := hL.1
  obtain ⟨d, hd, hdz⟩ := GlobalTheory.FinPl.exists_int_smul_le (Submodule.span (𝓞 D.host.E) {z}) L
    (Submodule.fg_span_singleton z) hlat.span_eq_top
  set T := (GlobalTheory.FinPl.finite_places_int (D := D) d hd).toFinset with hT
  set β : Af D.host.F := 1 - ∑ v ∈ T, GlobalTheory.FinPl.LatMem.indP D.host.F (· = v) with hβ
  have hβv : ∀ w, evalV D.host.F w β = if w ∈ T then 0 else 1 := by
    intro w
    rw [hβ, map_sub, map_one, map_sum]
    simp only [GlobalTheory.FinPl.LatMem.evalV_indP]
    rw [Finset.sum_ite_eq]
    split_ifs <;> simp
  have hoff : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] ((1 : D.host.E) * z i)) ∈
      GlobalTheory.FinPl.latV S L (fun w => w ∉ T) := by
    apply GlobalTheory.FinPl.LocAgree.latV_le_of_int_smul_on S (Submodule.span (𝓞 D.host.E) {z}) L d hd hdz
    · intro v hv hmem
      exact hv ((Set.Finite.mem_toFinset _).2 hmem)
    · apply AddSubgroup.subset_closure
      refine ⟨β, fun w => ?_, fun w hw => ?_, 1, rfl, z, Submodule.mem_span_singleton_self z, rfl⟩
      · rw [hβv]
        split_ifs
        · exact zero_mem _
        · exact one_mem _
      · rw [hβv, if_pos (not_not.1 hw)]
  have hall : (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) ∈ GlobalTheory.FinPl.latV S L (fun _ => True) := by
    have e : (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) =
        ∑ v ∈ T, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) +
          (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] ((1 : D.host.E) * z i)) := by
      funext i
      rw [Pi.add_apply, Finset.sum_apply, one_mul, ← TensorProduct.sum_tmul, ← TensorProduct.add_tmul]
      congr 1
      have hpa : ∀ a b : Af D.host.F, pairA D.host.F 0 a + pairA D.host.F 0 b = pairA D.host.F 0 (a + b) :=
        fun a b => Prod.ext (add_zero 0) rfl
      have hsum : ∀ (s : Finset (Pl D)) (f : Pl D → Af D.host.F),
          ∑ v ∈ s, pairA D.host.F 0 (f v) = pairA D.host.F 0 (∑ v ∈ s, f v) := by
        intro s f
        induction s using Finset.induction_on with
        | empty => exact Prod.ext rfl rfl
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, hpa]
      rw [hsum, hpa, hβ, add_sub_cancel]
    rw [e]
    exact add_mem (sum_mem fun v _ => GlobalTheory.FinPl.KSplit.latV_mono S L (fun _ _ => trivial) (hz v))
      (GlobalTheory.FinPl.KSplit.latV_mono S L (fun _ _ => trivial) hoff)
  have hhat := GlobalTheory.LatVHat.latV_mem_hatL D S L _ _ hall
  have e2 : (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i))) =
      fun i => Formalism.L2.Col.iA D.host.F D.host.E (z i) := by
    funext i
    rw [swap_finPart_pure]
    rfl
  rw [e2] at hhat
  exact (GlobalTheory.CongStdLoc.incl_mem_hatL_iff hlat.fg hlat.span_eq_top z).1 hhat

theorem mem_of_mem_latV_all : ∀ {D : D7} {S : HSp D} {L : Lat S}, IsSelfDualC S L → (∀ z : Fin S.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV S L (· = v)) → z ∈ L) :=
  fun hL z hz => mem_of_local hL z hz

end GlobalTheory.FinPl.LocGlob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelTypeFormExpandsAlongDualFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.TypeExpand

theorem typeAt_expand : ∀ (hU : GlobalTheory.Published.DiscreteSeriesHermitianUnique) {D : D7} (θ : InfFam D) {V : HSp D}
    {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) [FiniteDimensional ℂ (M.H τ)]
    {m : ℕ} (k : Fin m → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hk : ∀ j, k j ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ))
    (B : Fin m → (M.H τ →ₗ[ℂ] M.H τ))
    (hB : ∀ A : M.H τ →ₗ[ℂ] M.H τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A) =
        ∑ j, LinearMap.trace ℂ (M.H τ) ((M.rep τ (k j) : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A) *
          LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j))
    {φ : GA D V → ℂ} (hφ : IsTypeAt θ V τ (S τ) φ) (x : GA D V) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)), φ (x * atTau θ V τ g) = ∑ j, φ (x * atTau θ V τ (k j)) *
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j) := by
  intro hU D θ V S M τ _ m k hk B hB φ hφ x g hg
  obtain ⟨H', _, _, σ, lam, ε, P, hen, hds, hPu, hPg, hx⟩ := hφ
  obtain ⟨v, -, ℓ, -, -, hsum⟩ := hx x
  obtain ⟨hl, he⟩ := GlobalTheory.SignedParTest.isEnum_unique (M.enum τ) hen
  subst hl he
  obtain ⟨U, hU'⟩ := hU _ (M.ε τ) (M.lam τ)
    (GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (M.enum τ).1 (M.ds τ)) _ (M.fr τ) P
    (M.fr_unit τ) hPu (M.fr_gram τ) hPg _ _ (M.σ τ) σ (M.ds τ) hds

  set A : ℕ → (M.H τ →ₗ[ℂ] M.H τ) := fun i =>
    ((ℓ i).comp (U.symm.toLinearEquiv.toLinearMap)).smulRight (U (v i)) with hA
  have key : ∀ i, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      ℓ i (σ (P * h * P⁻¹) (v i)) =
        LinearMap.trace ℂ (M.H τ) ((M.rep τ h : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A i) := by
    intro i h hh
    have e1 : (M.rep τ h : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A i =
        ((ℓ i).comp (U.symm.toLinearEquiv.toLinearMap)).smulRight (M.rep τ h (U (v i))) := by
      ext w
      simp [hA]
    rw [e1, LinearMap.trace_smulRight]
    have e2 : M.rep τ h (U (v i)) = U (σ (P * h * P⁻¹) (v i)) := (hU' h hh (v i)).symm
    rw [e2]
    simp
  have h1 : HasSum (fun i => ∑ j, LinearMap.trace ℂ (M.H τ) ((M.rep τ (k j) : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A i) *
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j))
      (∑ j, φ (x * atTau θ V τ (k j)) *
        LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j)) := by
    refine hasSum_sum fun j _ => ?_
    refine HasSum.mul_right _ ?_
    have := hsum (k j) (hk j)
    refine this.congr_fun ?_
    intro i
    exact (key i (k j) (hk j)).symm
  have h2 : HasSum (fun i => ∑ j, LinearMap.trace ℂ (M.H τ) ((M.rep τ (k j) : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ A i) *
      LinearMap.trace ℂ (M.H τ) ((M.rep τ g : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ B j)) (φ (x * atTau θ V τ g)) := by
    refine (hsum g hg).congr_fun ?_
    intro i
    rw [key i g hg, hB (A i) g hg]
  exact h2.unique h1

end GlobalTheory.TypeExpand

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonvanishingThetaTowerBottomRungStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonvanishing_thetaTower_bottom_rung : FockTot → Rung0 := by
  first | exact @GlobalTheory.AscBottom.rung0 | exact GlobalTheory.AscBottom.rung0 | (intros; apply GlobalTheory.AscBottom.rung0 <;> assumption)
end

