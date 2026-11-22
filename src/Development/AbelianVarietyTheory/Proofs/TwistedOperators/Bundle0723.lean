import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0715
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0360
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0381
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0716
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0425
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0493
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0527
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0553
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0717
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0689
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Definitions.Divisors.GridTestLatticeLargestSlopeBound
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0239
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0722
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHaarVolumeOfConjugateLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0560
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0703
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0668

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicDataUnitaryRelationsFinitePlacePolZeroStatement
section
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicData_unitaryRelations_finitePlace_polZero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.V (GlobalTheory.AdelicU.evFin F v),
    ∀ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (om (g, 1) Φ - Φ) := by
  first | exact @GlobalTheory.PolKer.polZero_relV | exact GlobalTheory.PolKer.polZero_relV | (intros; apply GlobalTheory.PolKer.polZero_relV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CellSumRelationsPassToIntegralsProofStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cellSumRelationsPassToIntegrals_proof : CellVan := by
  first | exact @GlobalTheory.RowVal.cellVan_holds | exact GlobalTheory.RowVal.cellVan_holds | (intros; apply GlobalTheory.RowVal.cellVan_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormFiniteDimInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_finite_dim_invariant : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i j, i ≤ D.R.m → j ≤ D.R.m → ∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) ψ → (∃ W : Submodule ℂ (GA D (G.V i j).V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V i j).V τ), (G.V i j).M.fr τ * g * ((G.V i j).M.fr τ)⁻¹ ∈ Formalism.REAL.Kset ((G.V i j).M.ε τ) → ∀ f ∈ W, Formalism.L2.Theta.rTr (G.V i j).V (Formalism.L2.Theta.atTau R.θ (G.V i j).V τ g) f ∈ W) → ∃ (n : ℕ) (T : Fin n → Formalism.IndefR.Mult.MMap (G.V i j).M) (v : Fin n → (G.V i j).M.Vec), (∀ l, Formalism.IndefR.Mult.IsMultMap R.θ (G.V i j).M ∅ 1 (T l)) ∧ ∀ g, ψ g = ∑ l, T l (v l) g := by
  first | exact @GlobalTheory.KFinCuspSum.eq_sum_values | exact GlobalTheory.KFinCuspSum.eq_sum_values | (intros; apply GlobalTheory.KFinCuspSum.eq_sum_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspLiftFiniteSumApproximationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_cusp_degree_bound : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∃ N : ℕ, ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * φ g ∂(G.mP (i + 1)).ν) - ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε := by
  first | exact @GlobalTheory.DnFormApprox.form_approx | exact GlobalTheory.DnFormApprox.form_approx | (intros; apply GlobalTheory.DnFormApprox.form_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLocalEqCompletedHomLattice
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.RowLoc

variable {D : D7}

theorem gen_negSp (S T : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * (negSp S).gram k j) : WO (negSp S) T) =
      -(Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) := by
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem mem_latO_negSp {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : GlobalTheory.FinPl.Pl D → Prop} {u : WO S T} : u ∈ latO (negSp S) T LS LT P ↔ u ∈ latO S T LS LT P := by
  constructor
  · intro hu
    induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
      rw [gen_negSp]
      exact neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  · intro hu
    induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
      rw [← neg_neg (Matrix.of _), ← gen_negSp]
      exact neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx

theorem latRow_at : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ v ∉ G.pl.S0, ∀ u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)),
    MxAt (· = v) u → (u ∈ latRow G i ↔ u ∈ latO _ _ (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v)) := by
  intro D _ T L μ0 _ sc G W M _ i _ v hv u hu
  have hoff : ∀ e : AE D, IsIdemSum e G.pl.W0 → e • u = 0 := by
    intro e he
    have he' := GlobalTheory.StepComb.idemSum_mem_idAt he
    have hev : e ∈ idOff D (· = v) := by
      rw [idOff, Ideal.mem_iInf]
      rintro ⟨w, rfl⟩
      rw [idAt, Ideal.mem_inf, Ideal.mem_iInf] at he'
      refine he'.2 ⟨w, ?_⟩
      rintro ⟨PP, hPP, hw⟩
      classical
      simp only [Places.W0, Finset.mem_image] at hPP
      obtain ⟨s, hs, rfl⟩ := hPP
      exact hv (by rw [hw, G.pl.under_w hs]; exact hs)
    refine Matrix.ext fun a b => ?_
    rw [Matrix.smul_apply, smul_eq_mul, mul_comm, Matrix.zero_apply]
    exact GlobalTheory.FinPl.FlatUnitPf.idAt_mul_idOff _ _ _ (hu a b) hev
  have k1 : u ∈ latO (negSp (G.V (.grid (i + 1) 0))) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (fun _ => True) ↔
      u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (fun _ => True) := mem_latO_negSp
  have k2 : u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (fun _ => True) ↔
      u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v) :=
    GlobalTheory.AscFinWit.mem_latO_at (LS := G.Λ (.grid (i + 1) 0)) (LT := G.Λ (.grid i 0)) hu
  exact ⟨fun h => k2.1 (k1.1 h.1), fun h => ⟨k1.2 (k2.2 h), fun e he => by rw [hoff e he]; exact zero_mem _⟩⟩

end GlobalTheory.RowLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DeterminantIdeleAtSplitPlaceMovedGridNode
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar
namespace GlobalTheory.RowDetLocal
variable {D : D7}

theorem toFinAd_eq (z : TensorProduct D.host.F (Af D.host.F) D.host.E) :
    GlobalTheory.LFun.toFinAd D.host.F D.host.E z = GlobalTheory.StdFrames.toAd D (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Algebra.TensorProduct.comm_tmul, GlobalTheory.StdFrames.toAd_spec, mul_comm]
    rfl
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]

theorem compAt_eq_cpt (w : Pl D.host.E) (a : AE D) :
    GlobalTheory.LFun.compAt D.host.F w (finPart D a) = GlobalTheory.StdFrames.cpt w (toEAf D a) := by
  show (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.E w) (GlobalTheory.LFun.toFinAd D.host.F D.host.E (finPart D a)) = _
  rw [toFinAd_eq]
  rfl

theorem gdet_inBasis_val (V : HSp D) {n' : ℕ} (h : n' = V.rank) (β : GL (Fin V.rank) (Lev.EAf D)) (w : Pl D.host.E) (k : GfC V) :
    ((gdet (inBasis h β w (finG V k)) : (Kw w)ˣ) : Kw w) =
      GlobalTheory.StdFrames.cpt w (toEAf D (Formalism.L2.Theta.mt V (k : GA D V)).det) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  rw [GlobalTheory.FunObj.inBasis, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, GlobalTheory.TopLevelInv.det_val_reGL, GlobalTheory.TopLevelInv.val_loc, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    GlobalTheory.TopLevelInv.det_val_conj_inv, GlobalTheory.TopLevelInv.val_finG, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

theorem detIdl_eq_locIdele (V : HSp D) (g : GA D V) (w : Pl D.host.E) (hs : ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w)
    (z : (Kw w)ˣ) (hz : (z : Kw w) = GlobalTheory.StdFrames.cpt w (toEAf D (Formalism.L2.Theta.mt V g).det)) :
    detIdl (idemAt w) V g = GlobalTheory.LFun.locIdele D.host.F w z := by
  have he : Formalism.L2.NTheta.IsIdemAt (idemAt w) w := Classical.epsilon_spec hs
  have hee : idemAt w * idemAt w = idemAt w := he.1.1
  have hP : Formalism.IndefR.Mult.IsPrimeIdem w (idemAt w) (idemAt w + cA D (idemAt w)) := Or.inl ⟨he, rfl⟩
  have hx := detIdl_val hee V g
  obtain ⟨y, hy, hxy⟩ := GlobalTheory.WeilAtPlace.exists_eq_locIdele (GlobalTheory.WeilAtPlace.isPrimeIdem_infPart hP)
    (GlobalTheory.LFun.finPart_of_isPrimeIdem hP) (detIdl (idemAt w) V g) (by
      rw [hx]
      linear_combination ((Formalism.L2.Theta.mt V g).det - 1) * hee)
  have hyz : y = z := by
    apply Units.ext
    rw [hy, hx, GlobalTheory.WeilAtPlace.compAt_cut (GlobalTheory.LFun.finPart_of_isPrimeIdem hP), compAt_eq_cpt]
    exact hz.symm
  rw [hxy, hyz]

theorem detIdl_conj_eq_locIdele (V : HSp D) {n' : ℕ} (h : n' = V.rank) (β : GL (Fin V.rank) (Lev.EAf D)) (k u : GfC V)
    (w : Pl D.host.E) (hs : ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w) :
    detIdl (idemAt w) V ((u⁻¹ * k * u : GfC V) : GA D V) =
      GlobalTheory.LFun.locIdele D.host.F w (gdet (inBasis h β w (finG V k))) :=
  detIdl_eq_locIdele V _ w hs _ (by rw [gdet_inBasis_val, GlobalTheory.TopLevelInv.det_mt_conj])
end GlobalTheory.RowDetLocal

theorem GlobalTheory.RowDetLocal.detIdl_moved_eq_locIdele : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m)) (w : Pl D.host.E),
    (∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e w) →
    detIdl (idemAt w) (G.V (.grid (j + 1) D.R.m)) (moved S j k) =
      GlobalTheory.LFun.locIdele D.host.F w (gdet (inBasis (rank_vertex G t w (X := (j + 1, D.R.m)) ⟨hj.le, le_rfl⟩)
        (S.B.β (j + 1) D.R.m) w (finG (G.V (.grid (j + 1) D.R.m)) k))) := by
  intro D T L sc G W U S t j hj k w hs
  exact GlobalTheory.RowDetLocal.detIdl_conj_eq_locIdele _ _ _ k (S.N.u (.grid (j + 1) D.R.m)) w hs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCosetProjectionVolumeConstMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

noncomputable section

namespace GlobalTheory.CellLevel

variable {D : D7}

theorem finE_range_eq (V : HSp D) : ((Lev.finE V).comp (GfC V).subtype).range = (Lev.finE V).range := by
  refine le_antisymm (fun y ⟨g, hg⟩ => ⟨g.1, hg⟩) ?_
  rintro _ ⟨g, rfl⟩
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 _ (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V g)
  refine ⟨⟨k, MonoidHom.mem_ker.2 k1⟩, ?_⟩
  show Formalism.UG.bc (Lev.swapAE D) (finHom V k) = Formalism.UG.bc (Lev.swapAE D) (finHom V g)
  rw [k2]

theorem relIndex_comap_fin (V : HSp D) (K K' : Subgroup (GL (Fin V.rank) (Lev.EAf D))) :
    (K.comap ((Lev.finE V).comp (GfC V).subtype)).relIndex (K'.comap ((Lev.finE V).comp (GfC V).subtype)) =
      (K.comap (Lev.finE V)).relIndex (K'.comap (Lev.finE V)) := by
  rw [Subgroup.relIndex_comap, Subgroup.relIndex_comap, Subgroup.map_comap_eq, Subgroup.map_comap_eq,
    finE_range_eq]

theorem isCompact_comap_fin (V : HSp D) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))} (h : IsCO V K) :
    IsCompact ((K.comap ((Lev.finE V).comp (GfC V).subtype) : Subgroup (GfC V)) : Set (GfC V)) := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  convert h.2 using 1
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact Lev.mem_levA.2 ⟨g.2, hg⟩
  · intro hy
    obtain ⟨h1, h2⟩ := Lev.mem_levA.1 hy
    exact ⟨⟨y, h1⟩, h2, rfl⟩

theorem isOpen_comap_fin (V : HSp D) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}
    (h : IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V))) :
    IsOpen ((K.comap ((Lev.finE V).comp (GfC V).subtype) : Subgroup (GfC V)) : Set (GfC V)) :=
  h.preimage continuous_subtype_val

theorem relIndex_ne_zero (V : HSp D) {K K₃ : Subgroup (GL (Fin V.rank) (Lev.EAf D))} (h : IsCO V K)
    (h₃ : IsOpen ((K₃.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V))) :
    (K₃.comap ((Lev.finE V).comp (GfC V).subtype)).relIndex (K.comap ((Lev.finE V).comp (GfC V).subtype)) ≠ 0 := by
  have := GlobalTheory.LocVec.finiteIndex_of_isOpen (K.comap ((Lev.finE V).comp (GfC V).subtype)) (isCompact_comap_fin V h) subset_rfl
    ((K₃.comap ((Lev.finE V).comp (GfC V).subtype)).subgroupOf (K.comap ((Lev.finE V).comp (GfC V).subtype)))
    ((isOpen_comap_fin V h₃).preimage continuous_subtype_val)
  exact this.index_ne_zero

theorem vol_ratio (V : HSp D) {K₁ K₂ : Subgroup (GL (Fin V.rank) (Lev.EAf D))} (h₁ : IsCO V K₁) (h₂ : IsCO V K₂)
    (ν : Measure (GfC V)) [ν.IsHaarMeasure] {μ μ' : Measure (GA D V)} (hμ : Lev.IsMeasLevDef V K₁ μ)
    (hμ' : Lev.IsMeasLevDef V K₂ μ') (x : ℝ≥0) (hx : μ = x • μ') :
    ν {g | Lev.finE V g.1 ∈ K₂} = ν {g | Lev.finE V g.1 ∈ K₁} * x := by
  obtain ⟨hLC, hSC, hT2, hB, hTG, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hB; haveI := hTG
  haveI : μ.IsHaarMeasure := hμ.1
  have h₃ : IsOpen (((K₁ ⊓ K₂).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := h₁.1.inter h₂.1
  have hA₁ : μ (K₁.comap (Lev.finE V)) = 1 := GlobalTheory.Mass.Levels.measure_comap_finE hμ
  have hA₂ : μ (K₂.comap (Lev.finE V)) = x := by
    rw [hx, Measure.smul_apply, GlobalTheory.Mass.Levels.measure_comap_finE hμ', ENNReal.smul_def, smul_eq_mul, mul_one]
  have n₁ := relIndex_ne_zero V h₁ h₃
  have n₂ := relIndex_ne_zero V h₂ h₃
  rw [relIndex_comap_fin] at n₁ n₂
  haveI : (((K₁ ⊓ K₂).comap (Lev.finE V)).subgroupOf (K₁.comap (Lev.finE V))).FiniteIndex := ⟨n₁⟩
  haveI : (((K₁ ⊓ K₂).comap (Lev.finE V)).subgroupOf (K₂.comap (Lev.finE V))).FiniteIndex := ⟨n₂⟩
  have e₁ := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure _ _ (Subgroup.comap_mono inf_le_left) h₃.measurableSet μ
  have e₂ := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure _ _ (Subgroup.comap_mono inf_le_right) h₃.measurableSet μ
  rw [hA₁] at e₁
  rw [hA₂] at e₂
  have m₁ := relIndex_ne_zero V h₁ h₃
  have m₂ := relIndex_ne_zero V h₂ h₃
  haveI : ((((K₁ ⊓ K₂).comap ((Lev.finE V).comp (GfC V).subtype))).subgroupOf
    (K₁.comap ((Lev.finE V).comp (GfC V).subtype))).FiniteIndex := ⟨m₁⟩
  haveI : ((((K₁ ⊓ K₂).comap ((Lev.finE V).comp (GfC V).subtype))).subgroupOf
    (K₂.comap ((Lev.finE V).comp (GfC V).subtype))).FiniteIndex := ⟨m₂⟩
  have f₁ := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure _ _ (Subgroup.comap_mono inf_le_left)
    (isOpen_comap_fin V h₃).measurableSet ν
  have f₂ := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure _ _ (Subgroup.comap_mono inf_le_right)
    (isOpen_comap_fin V h₃).measurableSet ν
  rw [relIndex_comap_fin] at f₁ f₂
  change ν (K₂.comap ((Lev.finE V).comp (GfC V).subtype)) = ν (K₁.comap ((Lev.finE V).comp (GfC V).subtype)) * x
  rw [← f₁, ← f₂]
  have key : ∀ (p q a m X : ENNReal), p * m = 1 → q * m = X → q * a = p * a * X := by
    intro p q a m X h1 h2
    rw [← h2, ← mul_one (q * a), ← h1]
    ring
  exact key _ _ _ _ _ e₁ e₂

theorem vol_pos (V : HSp D) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))} (h : IsCO V K)
    (ν : Measure (GfC V)) [ν.IsHaarMeasure] : 0 < ν.real {g | Lev.finE V g.1 ∈ K} := by
  obtain ⟨hLC, hSC, hT2, hB, hTG, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hB; haveI := hTG
  refine ENNReal.toReal_pos ?_ ?_
  · exact ((isOpen_comap_fin V h.1).measure_pos ν ⟨1, one_mem _⟩).ne'
  · exact ((isCompact_comap_fin V h).measure_lt_top).ne

end GlobalTheory.CellLevel

namespace GlobalTheory.CellLevel

theorem pr_vol_of (hpr : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ), ∀ j ∈ idx D, ∀ (hj : j < D.R.m) (ν : Measure (GfC (ch.G.V (.top j)))),
    ν.IsHaarMeasure → ∃ c : ℝ, 0 < c ∧ ∀ t Φ β b, IsRep t ch.S.B s β b → ∀ hb : b j ∈ GfC _,
      ν.real (prSet ch.G j ⟨b j, hb⟩) = c * ν.real {g | Lev.finE (ch.G.V (.top j)) g.1 ∈ ch.S.toGridChoice.levTop t Φ β j hj}) : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ), ∀ j ∈ idx D, ∀ ν : Measure (GfC (ch.G.V (.top j))), ν.IsHaarMeasure →
    ∃ κ' : ℝ, 0 < κ' ∧ ∀ t Φ β b, IsRep t ch.S.B s β b → ∀ M M' : Vol ch.G, M.Is t → IsTermVol t ch.S.toGridChoice Φ β M' →
      ∀ x : ℝ≥0, M.ν (.top j) = x • M'.ν (.top j) → ∀ hb : b j ∈ GfC _, ν.real (prSet ch.G j ⟨b j, hb⟩) = κ' * x := by
  refine big_mono ?_ hpr
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch h s j hj ν hν
  have hjm : j < D.R.m := by
    simp only [idx, List.mem_range'_1] at hj
    omega
  have hj1 : 1 ≤ j := by
    simp only [idx, List.mem_range'_1] at hj
    omega
  obtain ⟨c, hc, hcb⟩ := h s j hj hjm ν hν
  have hMax : IsCO (ch.G.V (.top j)) (ch.G.levMax (.top j)) :=
    congLev_open_compact _ (ch.G.isV (X := .top j) (show j ≤ D.R.m by omega) (fun _ h => Node.noConfusion h)).sd.1
      (by simp)
  refine ⟨c * ν.real {g | Lev.finE (ch.G.V (.top j)) g.1 ∈ ch.G.levMax (.top j)}, mul_pos hc (vol_pos _ hMax ν), ?_⟩
  intro t Φ β b hb M M' hM hM' x hx hbj
  rw [hcb t Φ β b hb hbj]
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have h1 : Lev.IsMeasLevDef _ (ch.G.levMax (.top (j' + 1))) (M.ν (.top (j' + 1))) := by
    have := hM.vtx (.top (j' + 1)) (show j' + 1 ≤ D.R.m by omega)
    unfold Vol.IsAt at this
    rw [if_pos (show Node.neg D.R.m (.top (j' + 1)) = 0 from rfl)] at this
    exact this.1
  have h2 : Lev.IsMeasLevDef _ (ch.S.toGridChoice.levTop t Φ β (j' + 1) hjm) (M'.ν (.top (j' + 1))) := by
    have := hM'.1 (j' + 1) hjm
    unfold Vol.IsAt at this
    rw [if_pos (show Node.neg D.R.m (.top (j' + 1)) = 0 from rfl)] at this
    exact this.1
  have e := vol_ratio _ hMax (GridChoice.isCO_levTop _ _ t Φ β hjm) ν h1 h2 x hx
  simp only [Measure.real, e, ENNReal.toReal_mul, ENNReal.coe_toReal, mul_assoc]

end GlobalTheory.CellLevel

namespace GlobalTheory.CellLevel

theorem pr_vol : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ), ∀ j ∈ idx D, ∀ ν : Measure (GfC (ch.G.V (.top j))), ν.IsHaarMeasure →
    ∃ κ' : ℝ, 0 < κ' ∧ ∀ t Φ β b, IsRep t ch.S.B s β b → ∀ M M' : Vol ch.G, M.Is t → IsTermVol t ch.S.toGridChoice Φ β M' →
      ∀ x : ℝ≥0, M.ν (.top j) = x • M'.ν (.top j) → ∀ hb : b j ∈ GfC _, ν.real (prSet ch.G j ⟨b j, hb⟩) = κ' * x := pr_vol_of GlobalTheory.T.volume_periodProjectionSet_eq_familyLevel

end GlobalTheory.CellLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHaarVolumeOfConjugateLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_volume_of_conjugate_lattice : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ), ∀ j ∈ idx D,
    ∀ la : Measure ((rowN ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j)))), la.IsHaarMeasure →
    ∃ V₀ : ℝ, 0 < V₀ ∧ ∀ t β b, IsRep t ch.S.B s β b → ∀ hb : b j ∈ GfC _,
      la.real {n | (⟨b j, hb⟩ : GfC _)⁻¹ * n.1 * ⟨b j, hb⟩ ∈ (latGrp ch.G j).subgroupOf (GfC _)} *
        (GlobalTheory.RowWt.colCoef ch t β j : ℝ) = V₀ := by
  first | exact @GlobalTheory.CellIdx.vol_mul_colCoef | exact GlobalTheory.CellIdx.vol_mul_colCoef | (intros; apply GlobalTheory.CellIdx.vol_mul_colCoef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsVacuumBasePointFamilyEveryTuple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.RowBase

theorem exists_isBase : Big fun ch => ∀ t, ∃ b, IsBase t ch.S.B b := by
  refine GlobalTheory.RowReal.big_mono ?_ (Big.and GlobalTheory.T.representation_at_every_place GlobalTheory.T.exists_unitaryPoint_prescribed_localMatrices)
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch ⟨hrep, hloc⟩ t
  classical
  let β0 : CosFam ch.G t := fun _ _ => DoubleCoset.mk _ _ 1
  obtain ⟨b', hb'⟩ := (hrep 1 t).1 β0
  have H : ∀ j, ∃ x : GA D (ch.G.V (.grid D.R.m j)),
      (j ∈ idx D → ∃ δ, IsTilt ch.G j δ ∧ IsFinOf δ x) ∧ (j ∉ idx D → x = 1) := by
    intro j
    by_cases hj : j ∈ idx D
    · have hle : j ≤ D.R.m := by have := GlobalTheory.RowRep.idx_le hj; omega
      obtain ⟨δ, -, hδ, -⟩ := hb'.2 j hj hle
      obtain ⟨x, hx⟩ := GlobalTheory.RowRep.exists_isFinOf _ δ
      exact ⟨x, fun _ => ⟨δ, hδ, hx⟩, fun h => absurd hj h⟩
    · exact ⟨1, fun h => absurd h hj, fun _ => rfl⟩
  choose f hf using H
  obtain ⟨r, hr⟩ := hloc t 0 (Nat.zero_le _) (fun w => (stair (locGrid ch.G t w.1) (unifAt w.1) (cosExp ch.G w.1) 0)⁻¹)
  refine ⟨Function.update f 0 r, ?_, ?_, ?_⟩
  · rw [Function.update_self]; exact hr
  · intro j hj
    have h0 : j ≠ 0 := by have := GlobalTheory.RowRep.idx_le hj; omega
    rw [Function.update_of_ne h0]
    exact (hf j).1 hj
  · intro j h0 hj
    rw [Function.update_of_ne h0]
    exact (hf j).2 hj

end GlobalTheory.RowBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePointsRowPeriodConjLevelFubiniStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePoints_rowPeriod_conjLevel_fubini : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ j ∈ idx D,
    ∀ ρ : Measure ((rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j)))), ρ.IsHaarMeasure →
    ∃ (κ : ℝ) (la : Measure ((rowN ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))))) (ν : Measure (GfC (ch.G.V (.top j)))),
      0 < κ ∧ la.IsHaarMeasure ∧ ν.IsHaarMeasure ∧ ∀ b : GfC (ch.G.V (.grid D.R.m j)),
        ρ.real {r | b⁻¹ * r.1 * b ∈ (latGrp ch.G j).subgroupOf (GfC _)} =
          κ * la.real {n | b⁻¹ * n.1 * b ∈ (latGrp ch.G j).subgroupOf (GfC _)} * ν.real (prSet ch.G j b) := by
  first | exact @GlobalTheory.CellMass.cell_fubini | exact GlobalTheory.CellMass.cell_fubini | (intros; apply GlobalTheory.CellMass.cell_fubini <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodPlaceOneCosetOfBesselLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodPlace_oneCoset_of_besselLevel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (p : Pieces V₀ W W₀ ρ ρ) (z : Fin V₀.rank → D.host.E) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : GlobalTheory.FinPl.Pl D), GoodAt dV dW (xZero dW) ψ LV LV₀ LW LW₀ v → StdAt dV dW p LV LW v → (0 < ρ → ∀ a ∈ idAt D (· = v), dW.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (LV₀ : Set _) (LW : Set _) (· = v) ↔ a ∈ intAt D (· = v)) → ∀ h ∈ grpAt W (· = v), (∀ κ, GlobalTheory.FinPl.InK W LW (· = v) κ → Cond dW p (xZero dW) (yZero V₀ ρ z) ψ (· = v) (h * κ)) → CosetAt W (Rgrp W (xZero dW)) LW v h := by
  first | exact @GlobalTheory.OneCosetGood.oneCoset_good | exact GlobalTheory.OneCosetGood.oneCoset_good | (intros; apply GlobalTheory.OneCosetGood.oneCoset_good <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFiniteAdelicMatrixLatticeLatOSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin

theorem finLat_latO_selfDual : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → FinLat (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := fun S T ΛS ΛT hS hT => GlobalTheory.AscFinWit.finLat_latO hS.1 hT.1

end GlobalTheory.AscFin
end
end

