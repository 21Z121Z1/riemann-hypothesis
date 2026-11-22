import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0300
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsPin
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1845
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import GroundTheory.IdeleRoots.ConstantFrames.GaugeExistence.QdetSub
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0278
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0139
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0119
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0106
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0109
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0110
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0111
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0108
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0144
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartsRebasedOneOffLevelPrimeKilledStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charts_rebased_one_off_levelPrime_killed : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K0 : Fam I l Z u a i hi bad chOf), I.ReadsK l Z u a i hi chOf K0 → (∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K0 β).lev.chi κ ^ n = 1) → ∃ Kc : Fam I l Z u a i hi bad chOf, ReadsOne I l Z u a i hi chOf Kc ∧ ∀ β, FunKilled (Kc β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, (Kc β).lev.chi κ ^ n = 1 := by
  first | exact @GlobalTheory.TwU.AtTrue.charts_funKilled_one | exact GlobalTheory.TwU.AtTrue.charts_funKilled_one | (intros; apply GlobalTheory.TwU.AtTrue.charts_funKilled_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassSumTermLawStabiliserTargetStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.KerJ Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSum_term_law_stabiliser_target : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ColSide t → ∀ u μ (G : StabDat (D.chTw u μ)), StabPin t u μ G → ∀ i < D.R.m, ∀ c c', ∀ g ∈ G (i + 1) c', TermLaw (t.O u μ) i c c' g := by
  first | exact @GlobalTheory.KerJ.term_law | exact GlobalTheory.KerJ.term_law | (intros; apply GlobalTheory.KerJ.term_law <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientFieldConditionOfStandardKernelCompariStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientFieldCondition_of_standardKernelComparison : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), ColIn.JetsIn I → I.StdKer l Z t → t.RK := by
  first | exact @GlobalTheory.Pdv.rk_of_std | exact GlobalTheory.Pdv.rk_of_std | (intros; apply GlobalTheory.Pdv.rk_of_std <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConsecutiveClassesKernelEqKernelFunctionTransporStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.consecutiveClassesKernel_eq_kernelFunction_transported : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c', (t.rd u μ).Th t.seam t.amb i c c' = kerTh t.B t.χ (ssRec t u μ) (t.rd u μ).lev (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c')) (fun x => (t.rd u μ).Xi i c c' (seamHom t.seam x))) := by
  first | exact @GlobalTheory.TwV.th_eq_kerTh | exact GlobalTheory.TwV.th_eq_kerTh | (intros; apply GlobalTheory.TwV.th_eq_kerTh <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTraceMatrixUnitsActsBySumInfinitesimalCh
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
noncomputable section

namespace GlobalTheory

open Polynomial in

theorem trace_Eop_of_hasInfChar (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (π : GlobalTheory.CuspRep.CuspSub E a) (τ : E →+* ℂ) (m : Multiset ℂ) (h : π.HasInfChar τ m) :
    ∀ φ ∈ π.V, (∑ i : Fin a, GlobalTheory.CuspRep.Eop τ i i) φ = m.sum • φ := by
  intro φ hφ
  obtain ⟨hcard, hcap⟩ := h
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [Multiset.card_eq_zero.1 hcard]; simp
  set c : ℂ := ((a : ℂ) - 1) / 2 with hc
  set P := GroundTheory.BlockD.FourierDecayAlt.GaugeExists.qdetPoly (GlobalTheory.CuspRep.Eop (a := a) τ) with hPdef
  have hP : P.coeff (a - 1) = ∑ i, GlobalTheory.CuspRep.Eop τ i i -
      algebraMap ℂ (Module.End ℂ (GlobalTheory.CuspRep.Sm E a)) (((a : ℂ) * ((a : ℂ) - 1)) / 2) := by
    obtain ⟨-, -, hsub⟩ := GroundTheory.BlockD.FourierDecayAlt.GaugeExists.prod_linear a fun k =>
      GlobalTheory.CuspRep.Eop (a := a) τ k k - algebraMap ℂ (Module.End ℂ (GlobalTheory.CuspRep.Sm E a)) ((k : ℕ) : ℂ)
    rw [hPdef, GroundTheory.BlockD.FourierDecayAlt.GaugeExists.coeff_qdetPoly_top _ (a - 1) (by omega), hsub (a - 1) (by omega),
      Finset.sum_sub_distrib, ← map_sum, GroundTheory.BlockD.FourierDecayAlt.GaugeExists.sum_fin_cast]
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_
  let Q : ℂ[X] := ∑ j ∈ Finset.range (a + 1), C (ℓ (P.coeff j φ)) * X ^ j
  let R : ℂ[X] := C (ℓ φ) * (m.map fun z => X + C (z - c)).prod
  have hdeg : P.natDegree < a + 1 :=
    Nat.lt_succ_of_le (GroundTheory.BlockD.FourierDecayAlt.GaugeExists.natDegree_qdetPoly_le _)
  have hQ : ∀ v : ℂ, Q.eval v = ℓ ((GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU v P) φ) := by
    intro v
    rw [GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU_apply, eval₂_eq_sum_range' _ hdeg, LinearMap.sum_apply, map_sum,
      eval_finset_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eval_mul, eval_C, eval_pow, eval_X, RingHom.id_apply, Module.End.mul_apply, ← map_pow,
      Module.algebraMap_end_apply, map_smul, map_smul, smul_eq_mul, mul_comm]
  have hQR : Q = R := by
    refine Polynomial.funext fun v => ?_
    rw [hQ, GroundTheory.BlockD.FourierDecayAlt.GaugeExists.evU_qdetPoly]
    have e := hcap (v - c) φ hφ
    rw [GlobalTheory.CuspRep.cap, show v - c + ((a : ℂ) - 1) / 2 = v by rw [hc]; ring] at e
    rw [e, map_smul, smul_eq_mul]
    simp only [R, eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_add, eval_X]
    rw [mul_comm]
    congr 2
    refine Multiset.map_congr rfl fun z _ => ?_
    ring
  have hco := congrArg (fun p : ℂ[X] => p.coeff (a - 1)) hQR
  have hlt : a - 1 ∈ Finset.range (a + 1) := Finset.mem_range.2 (by omega)
  simp only [Q, R, finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', if_pos hlt] at hco
  have hm : (m.map fun z => X + C (z - c)).prod =
      ((m.map fun z => z - c).map fun r => X + C r).prod := by rw [Multiset.map_map]; rfl
  rw [hm, Multiset.prod_X_add_C_coeff _ (by simp [hcard]), Multiset.card_map, hcard,
    show a - (a - 1) = 1 by omega, Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map] at hco
  simp only [Function.comp_def, Multiset.prod_singleton, Multiset.map_id', Multiset.sum_map_sub,
    Multiset.map_const', Multiset.sum_replicate, hcard, nsmul_eq_mul] at hco
  rw [hP] at hco
  simp only [LinearMap.sub_apply, map_sub, Module.algebraMap_end_apply, map_smul, smul_eq_mul] at hco ⊢
  rw [hc] at hco
  linear_combination hco

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepLocalFactorLevelValuesTypePrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStep_localFactor_levelValues_typePrime : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (x x₁ : UA D (t.m2 + 1) (Nat.le_of_succ_le hi)) (x' x₁' : UA D (t.m2 + 1 + 1) hi)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' →
    ∀ (P : SB t μ), P.1 ∈ t.Pr.vGs → ∀ g z g' z', A.cplRel β P g z →
      InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 g →
      TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P g' z' →
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 g' →
    ∀ Z, z' * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z *
        rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g : t.X.Eˣ) : t.X.E) *
        rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g' : t.X.Eˣ) : t.X.E) =
      z * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) := by
  first | exact @GlobalTheory.TwTop.locAt_vG | exact GlobalTheory.TwTop.locAt_vG | (intros; apply GlobalTheory.TwTop.locAt_vG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelMovedPointFramesMatrixStepsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelMoved_point_frames_matrixSteps : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ j (hj : j < D.R.m), j ≤ t.m2 → ∀ (β : (St j hj.le).Ch) (x x₁ : UA D j hj.le) (κ : ((St j hj.le).K β).lev.U), x₁.1 = x.1 * κ.1 →
    ∀ p p₁, IsPtAd A a j hj.le β x p → IsPtAd A a j hj.le β x₁ p₁ →
    ∃ (k : GLQ t.X.E (D.R.N j) (SB t μ)) (c : SB t μ → t.X.Kˣ),
      (∀ P, frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * ((k P)⁻¹).1) ∧
      (∀ P, GlobalTheory.TopLaw.LevAt ((t.idx μ).levG j (A.ib j hj β)) ((t.idx μ).levQ j (A.ib j hj β)) P (k P) (c P)) ∧
      ((((St j hj.le).K β).lev.chi κ : ℂˣ) : ℂ) = t.seam.σ₀ (((∏ P, c P : t.X.Kˣ)) : t.X.K) ∧
      ∀ P : SB t μ, IntAtA (F := D.host.F) (seamP t.seam P.1)
        (iA D.host.F D.host.E ((qOf (seamP t.seam P.1) : D.host.E))⁻¹ *
          ((((Matrix.GeneralLinearGroup.det κ.1)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
            iA D.host.F D.host.E (t.seam.iE ((LinearEquiv.det ((k P)⁻¹).1 : t.X.Eˣ) : t.X.E)) - 1))) := by
  first | exact @GlobalTheory.MatFrames.frames_mat | exact GlobalTheory.MatFrames.frames_mat | (intros; apply GlobalTheory.MatFrames.frames_mat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrimeStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localisation_eq_stdAt_of_congruentOne_atPrime : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ} (P : HeightOneSpectrum (𝓞 E)) (d : ℕ), 1 ≤ d → ∀ (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (R : GL (Fin N) E) (M : Submodule (𝓞 E) (Fin N → E)), M.FG → Submodule.span E (M : Set (Fin N → E)) = ⊤ → CongAt (F := F) P d (y⁻¹ * ratA F R) → Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (latAd y M) = mvL R (stdAt E N P) → Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M = stdAt E N P := by
  first | exact @GlobalTheory.CongStdLoc.localization_eq_stdAt_of_congAt | exact GlobalTheory.CongStdLoc.localization_eq_stdAt_of_congAt | (intros; apply GlobalTheory.CongStdLoc.localization_eq_stdAt_of_congAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodBoundOfJetLoss
section
noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound

section Val

variable {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

theorem vAdd_mul_of_ne {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : vAdd w (x * y) = vAdd w x + vAdd w y := by
  unfold vAdd
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy), neg_add]

theorem vAdd_pow_eq (x : K) (n : ℕ) : vAdd w (x ^ n) = n * vAdd w x := by
  unfold vAdd
  rw [map_pow, WithZero.log_pow]
  simp

theorem vAdd_prod_of_ne {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i, f i ≠ 0) :
    vAdd w (∏ i ∈ s, f i) = ∑ i ∈ s, vAdd w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vAdd]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, vAdd_mul_of_ne w (h a) (Finset.prod_ne_zero_iff.2 fun i _ => h i), ih]

theorem vAdd_nonneg_of_le {x : K} (hx : x ≠ 0) (h : w.valuation K x ≤ 1) : 0 ≤ vAdd w x := by
  unfold vAdd
  have := (WithZero.log_le_log ((Valuation.ne_zero_iff _).2 hx) one_ne_zero).2 h
  rw [WithZero.log_one] at this
  omega

theorem mem_of_vAdd_pos {a : 𝓞 K} (h : 0 < vAdd w (a : K)) : a ∈ w.asIdeal := by
  by_contra hn
  have h1 : w.valuation K (a : K) = 1 := (w.valuation_eq_one_iff_notMem (K := K)).2 hn
  rw [vAdd, h1, WithZero.log_one] at h
  omega

end Val

theorem sum_nuW_nonneg {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (u : Pr.Word) {j : ℕ} (hj : j < R.m)
    (τ : X.Tau) : 0 ≤ ∑ a, (W.nuW u (j + 1) τ).w a := by
  obtain ⟨s, s', ⟨h1, h2, -⟩, h3⟩ := chainWeights X Pr R W u j hj
  refine Finset.sum_nonneg fun a _ => ?_
  have h4 := (W.lamTrue u (j + 1) τ).anti (show Fin.castLE (N_lt_succ R j).le a ≤ ⟨R.N j, N_lt_succ R j⟩ from a.2.le)
  rw [h2 τ _ le_rfl] at h4
  rw [← h3, ← h1]
  omega

theorem recWts_ok {D : D7} (EX : ErrX D) : (recWts EX).Ok where
  row_ok τ := ⟨D.hc τ, rfl⟩
  hc_row := recWts_row EX
  u_first u u' τ h := (D.hcW_first u τ h).trans (D.hcW_first u' τ h).symm
  u_last u u' τ h := (D.hcW_last u τ (by omega)).trans (D.hcW_last u' τ (by omega)).symm

theorem emb_star_piG {D : D7} (EX : ErrX D) (i : Fin 2) (τ : D.what₂.Tau) :
    (recFields D).emb τ (@star _ (recFields D).starE.toStar (((recPrimes EX).piG i : 𝓞 D.host.E) : D.host.E)) = tauPib EX i τ := by
  have h : ∀ x : D.host.E, @star _ (recFields D).starE.toStar x = D.host.conj x := fun x => by
    apply D.host.φ₀.injective
    let _ := D.host.isCMField_hostE
    change D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
    rw [NumberField.IsCMField.complexEmbedding_complexConj]
    exact (D.host.toHostAx.conjE_apply D.host.φ₀ x).symm
  rw [h]
  rfl

theorem vG_loss_le {D : D7} (L : SizeData₂ D) (EX : ErrX D) (hPr : (recPrimes EX).Ok) (i : Fin 2) (w : LiftErrorLocal.Pl D)
    (hw : LiftErrorLocal.Over D i w) (u : D.what₂.Word) :
    (∀ j, lossAt (Pr := recPrimes EX) (recWts EX) i u j ≠ 0) ∧
    LiftErrorLocal.vG D w (∏ j ∈ Finset.range D.R.m, lossAt (Pr := recPrimes EX) (recWts EX) i u j) ≤
      (∑ j ∈ LiftErrorLocal.lifts D, vNN EX i u j w) + LiftErrorLocal.errC D L := by
  have hg0 : (D.host.g i : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero
  have hπ : ∀ τ, tauPib EX i τ ≠ 0 := by
    intro τ h
    have h1 : (recFields D).emb τ (((recFields D).conjO (EX.piG i) : 𝓞 D.host.E) : D.host.E) = 0 :=
      (emb_star_piG EX i τ).trans h
    have h2 : (recFields D).conjO (EX.piG i) = 0 := RingOfIntegers.ext ((map_eq_zero _).1 h1)
    have h3 := hPr.piG_norm i
    change EX.piG i * (recFields D).conjO (EX.piG i) = _ at h3
    rw [h2, mul_zero] at h3
    exact (hPr.g_prime i).ne_zero (by exact_mod_cast h3.symm)
  have e : ∀ j, lossAt (Pr := recPrimes EX) (recWts EX) i u j = (D.host.g i : D.what₂.LL) ^ (D.R.f * D.R.N j * D.R.N (j + 1)) *
      ∏ τ, tauPib EX i τ ^ (∑ a, ((recWts EX).nuW u (j + 1) τ).w a).toNat := fun j => by
    rw [← D.what₂.card_Tau]
    simp only [← emb_star_piG]
    rfl
  have hne : ∀ j, lossAt (Pr := recPrimes EX) (recWts EX) i u j ≠ 0 := fun j => by
    rw [e]
    exact mul_ne_zero (pow_ne_zero _ hg0) (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (hπ τ))
  refine ⟨hne, ?_⟩
  have hw' : D.what₂.places.resChar w = D.host.g i := hw
  have hvg : vAdd (D.plEq w) (D.host.g i : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) := by
    have h1 := D.what₂.places.val_resChar w
    rw [hw', D.val_eq w _ hg0] at h1
    exact_mod_cast h1
  have he : (0 : ℝ) < D.what₂.places.ramIdx w := by exact_mod_cast D.what₂.places.ramIdx_pos w
  have h1 : ∀ j ∈ Finset.range D.R.m, (vAdd (D.plEq w) (lossAt (Pr := recPrimes EX) (recWts EX) i u j) : ℝ) / D.what₂.places.ramIdx w ≤
      vNN EX i u (1 + j) w + D.R.f * (D.R.N D.R.m * (D.R.N D.R.m + D.R.t)) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have h2 : (D.R.f : ℝ) * D.R.N j * D.R.N (j + 1) ≤ D.R.f * D.R.N D.R.m * (D.R.N D.R.m + D.R.t) := by
      exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions.exp_le D j hj'
    have h3 : ∀ τ, (((∑ a, ((recWts EX).nuW u (j + 1) τ).w a).toNat : ℕ) : ℝ) = nuAbs D u (1 + j) τ := fun τ => by
      rw [add_comm 1 j, partitionSize D EX u j hj' τ, ← Int.cast_natCast,
        Int.toNat_of_nonneg (sum_nuW_nonneg (Pr := recPrimes EX) (recWts EX) u hj' τ)]
    rw [e, vAdd_mul_of_ne _ (pow_ne_zero _ hg0) (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (hπ τ)),
      vAdd_prod_of_ne _ _ _ fun τ => pow_ne_zero _ (hπ τ)]
    simp only [vAdd_pow_eq, hvg]
    push_cast
    simp only [h3]
    rw [add_div, mul_div_assoc, div_self he.ne', mul_one, vNN]
    linarith
  have h4 : 0 ≤ (D.R.f : ℝ) * ((D.R.m : ℝ) ^ 3 * L.etaSz) := by
    have := L.etaSz_pos.le
    positivity
  unfold LiftErrorLocal.vG
  rw [vAdd_prod_of_ne _ _ _ hne, Int.cast_sum, Finset.sum_div]
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, LiftErrorLocal.lifts, LiftErrorLocal.errC,
    ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  nlinarith

end GlobalTheory.ColPeriod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitCentreDerivativeEqSumDiagonalMatrixUnits
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.CuspRep.ZcTrace

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def conjPerm : Equiv.Perm (E →+* ℂ) where
  toFun := ComplexEmbedding.conjugate
  invFun := ComplexEmbedding.conjugate
  left_inv τ := by ext x; simp [ComplexEmbedding.conjugate_coe_eq]
  right_inv τ := by ext x; simp [ComplexEmbedding.conjugate_coe_eq]

theorem sum_atEmb_I : ∑ τ : E →+* ℂ, atEmb τ Complex.I = 0 := by
  have e : ∀ τ : E →+* ℂ, atEmb (conjPerm τ) Complex.I = -atEmb τ Complex.I := by
    intro τ
    change atEmb (ComplexEmbedding.conjugate τ) Complex.I = _
    rw [atEmb_conj, Complex.conj_I, atEmb_eq]; simp
  have h := Equiv.sum_comp (conjPerm (E := E)) (fun τ => atEmb τ Complex.I)
  simp only [e, Finset.sum_neg_distrib] at h
  have h2 : (2 : ℝ) • ∑ τ : E →+* ℂ, atEmb τ Complex.I = 0 := by
    rw [two_smul]; nth_rewrite 1 [← h]; simp
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

theorem sum_atEmb_one : ∑ τ : E →+* ℂ, atEmb τ 1 = (2 : ℝ) • (1 : Cinf E) := by
  classical
  have e : ∀ τ : E →+* ℂ, atEmb τ 1 = Pi.single (InfinitePlace.mk τ) 1 := by
    intro τ; unfold atEmb; split_ifs <;> simp
  simp only [e]
  funext w
  rw [Finset.sum_apply]
  simp only [Pi.single_apply, Finset.sum_boole]
  have hc : (Finset.univ.filter fun τ : E →+* ℂ => w = InfinitePlace.mk τ).card = 2 := by
    have := InfinitePlace.card_filter_mk_eq w
    rw [InfinitePlace.mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩] at this
    rw [← this]; congr 1; ext τ; simp [eq_comm]
  rw [hc]
  simp

theorem sum_Eop (a : ℕ) (i : Fin a) : ∑ τ : E →+* ℂ, Eop τ i i = lieS E a i i 1 := by
  simp only [Eop, ← Finset.smul_sum, Finset.sum_sub_distrib, ← map_sum, sum_atEmb_I, sum_atEmb_one, map_zero,
    smul_zero, sub_zero, map_smul]
  rw [← Complex.coe_smul, smul_smul]
  norm_num

end GlobalTheory.CuspRep.ZcTrace

namespace GlobalTheory.ResW

open GlobalTheory.CuspRep.ZcTrace in

theorem zc_eq_sum_Eop : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), GlobalTheory.ResW.zc E a = ∑ τ : E →+* ℂ, ∑ i : Fin a, GlobalTheory.CuspRep.Eop τ i i := by
  intro E _ _ _ a
  rw [Finset.sum_comm]
  simp only [sum_Eop, lieS_apply, ← map_sum]
  unfold zc
  congr 1
  funext k l
  simp [toL, Finset.sum_apply, Matrix.single_apply, eq_comm]
  simp only [Finset.sum_apply, Pi.single_apply]
  by_cases h : k = l
  · subst h; simp [ite_apply, Pi.single_apply]
  · simp [ite_apply, Pi.single_apply, h, Ne.symm h]

end GlobalTheory.ResW
end

