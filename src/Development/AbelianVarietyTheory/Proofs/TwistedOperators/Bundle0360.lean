import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0266
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0330
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0341
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorOperatorSplitOneRealPlace
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0343
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpenSubgroupTranslateHeightBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.openSubgroup_translate_height_bound : ∀ (D : D7) (V W : HSp D) (r : ℕ) (P : Matrix (Fin r) (Fin V.rank) D.host.E), ∃ e : ℕ, ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ M : ℕ, 0 < M ∧ ∀ (g : GA D V) (h : GA D W), ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ M * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ e ∧ ∀ x : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ a b, IsIntegral ℤ (x a b)) → ∃ u ∈ U, u.map (infPart D) = 0 ∧ actO V W g h u = HMul.hMul (finLift ((N : D.host.E) • x)) (P.map (incA D)) := by
  first | exact @GlobalTheory.LevelHeight.levelheight | exact GlobalTheory.LevelHeight.levelheight | (intros; apply GlobalTheory.LevelHeight.levelheight <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicDeterminantMultiplicative
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open GlobalTheory.LeviShift

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.LeviShift

section Mult

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {V : HSpace E} (Φ : WittFrame V) (hc : CMData F E) (R : Type) [CommRing R] [Algebra F R]

namespace DetUMul

theorem hLin_coordR (x y : V.V) :
    hLin hc.sig V.gram R (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R x) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R y) = inclR R (V.hD x y) := by
  change hR R hc.sig V.gram _ _ = inclR R (V.hT _ _)
  rw [IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]
  simp [hR, Formalism.UG.hform, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR, JR, inclR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, CMData.sig,
    TensorProduct.tmul_sum, starRingEnd_apply]

theorem hD_bas_dbas (u : SV (wittIndex V)) (i k : Supp u) :
    V.hD (bas Φ u i.1) (dbas Φ u k.1) = if i = k then 1 else 0 := by
  have hi := i.2
  have hk := k.2
  simp only [bas, dbas]
  by_cases ei : u i.1 = -1 <;> by_cases ek : u k.1 = -1
  · rw [if_pos ei, if_pos ek]
    have h1 := V.herm.eq (Φ.f i.1) (Φ.e k.1)
    have h2 := Φ.ef k.1 i.1
    simp only [HSpace.hD] at h2 ⊢
    rw [← h1, h2]
    by_cases e : i = k
    · subst e; simp
    · rw [if_neg (fun h => e (Subtype.ext h.symm)), if_neg e]; simp
  · rw [if_pos ei, if_neg ek, Φ.ff, if_neg]
    rintro rfl; exact ek ei
  · rw [if_neg ei, if_pos ek, Φ.ee, if_neg]
    rintro rfl; exact ei ek
  · rw [if_neg ei, if_neg ek, Φ.ef]
    by_cases e : i = k
    · subst e; simp
    · rw [if_neg (fun h => e (Subtype.ext h)), if_neg e]

theorem coordR_zero : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := F) V R (0 : V.V) = (0 : Fin V.rank → R ⊗[F] E) := by
  funext j; simp [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR]

theorem coordR_add (x y : V.V) : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := F) V R (x + y) =
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R x + GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R y := by
  funext j; simp [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR]

theorem coordR_smul (c : E) (x : V.V) : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := F) V R (c • x) =
    inclR (F := F) R c • GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := F) V R x := by
  funext j; simp [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR]

def hLinL (x : Fin V.rank → R ⊗[F] E) : (Fin V.rank → R ⊗[F] E) →ₗ[R ⊗[F] E] R ⊗[F] E where
  toFun y := hLin hc.sig V.gram R y x
  map_add' y y' := hLin_add_left _ _ _ y y' _
  map_smul' c y := hLin_smul_left _ _ _ c y _

def projU (u : SV (wittIndex V)) : (Fin V.rank → R ⊗[F] E) →ₗ[R ⊗[F] E] (Fin V.rank → R ⊗[F] E) :=
  ∑ k : Supp u, (hLinL hc R (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R (dbas Φ u k.1))).smulRight
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R (bas Φ u k.1))

theorem expand (u : SV (wittIndex V)) {y : Fin V.rank → R ⊗[F] E}
    (hy : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.extSub (F := F) V R (Φ.sub u)) :
    y = ∑ k : Supp u, hLin hc.sig V.gram R y (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R (dbas Φ u k.1)) •
      GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R (bas Φ u k.1) := by
  suffices h : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.extSub (F := F) V R (Φ.sub u) ≤ LinearMap.eqLocus LinearMap.id (projU Φ hc R u) by
    have := h hy
    simpa [projU, hLinL, LinearMap.sum_apply] using this
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    have key : ∀ i : Supp u, x = bas Φ u i.1 →
        GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := F) V R x ∈ LinearMap.eqLocus LinearMap.id (projU Φ hc R u) := by
      rintro i rfl
      show _ = _
      simp only [LinearMap.id_apply, projU, LinearMap.sum_apply, LinearMap.smulRight_apply, hLinL,
        LinearMap.coe_mk, AddHom.coe_mk, hLin_coordR, hD_bas_dbas, apply_ite (inclR R), map_one, map_zero,
        ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rcases hx with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
    · refine key ⟨i, by rw [show u i = 1 from hi]; decide⟩ ?_
      simp only [bas]; rw [if_neg]; rw [show u i = 1 from hi]; decide
    · refine key ⟨i, by rw [show u i = -1 from hi]; decide⟩ ?_
      simp only [bas]; rw [if_pos (show u i = -1 from hi)]
  | zero => rw [coordR_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [coordR_add]; exact add_mem hx hy
  | smul c x _ hx => rw [coordR_smul]; exact Submodule.smul_mem _ _ hx

theorem detMat_mul (u : SV (wittIndex V)) (g g' : HA R hc.sig V.gram)
    (hg' : g' ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab hc V R (Φ.sub u)) :
    detMat Φ hc R u (g * g') = detMat Φ hc R u g * detMat Φ hc R u g' := by
  ext i j
  have hb : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := F) V R (bas Φ u j.1) ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.extSub (F := F) V R (Φ.sub u) := by
    refine GlobalTheory.Cusp.coordR_mem V R (Submodule.subset_span ?_)
    by_cases h : u j.1 = -1
    · right; exact ⟨j.1, h, by simp [bas, h]⟩
    · have h1 : u j.1 = 1 := by
        have := j.2
        revert h this; cases u j.1 <;> decide
      left; exact ⟨j.1, h1, by simp [bas, h]⟩
  have key : ∀ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.extSub (F := F) V R (Φ.sub u),
      hLin hc.sig V.gram R (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act hc V g y) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R (dbas Φ u i.1)) =
      ∑ k : Supp u, hLin hc.sig V.gram R (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act hc V g (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R (bas Φ u k.1)))
          (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R (dbas Φ u i.1)) *
        hLin hc.sig V.gram R y (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR V R (dbas Φ u k.1)) := by
    intro y hy
    conv_lhs => rw [expand Φ hc R u hy]
    have e1 : ∀ z : Fin V.rank → R ⊗[F] E, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act hc V g z =
        Matrix.mulVecLin ((HA.mat R hc.sig V.gram g : GL (Fin V.rank) (R ⊗[F] E)) : Matrix (Fin V.rank) (Fin V.rank) (R ⊗[F] E)) z :=
      fun _ => rfl
    have e2 : ∀ z x : Fin V.rank → R ⊗[F] E, hLin hc.sig V.gram R z x = hLinL hc R x z := fun _ _ => rfl
    simp only [e1, e2, map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  simp only [detMat, Matrix.of_apply, Matrix.mul_apply]
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, key _ (GlobalTheory.Cusp.mem_parab_iff_maps.1 hg' _ hb)]

end DetUMul

open DetUMul in

theorem detU_mul (u : SV (wittIndex V)) (g g' : HA R hc.sig V.gram)
    (_hg : g ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab hc V R (Φ.sub u)) (hg' : g' ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab hc V R (Φ.sub u)) :
    detU Φ hc R u (g * g') = detU Φ hc R u g * detU Φ hc R u g' := by
  rw [detU, detMat_mul Φ hc R u g g' hg', Matrix.det_mul]; rfl

end Mult

end GlobalTheory.LeviShift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicMatrixCoordinatesTriangularStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_matrix_coordinates_triangular : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (v : HeightOneSpectrum (𝓞 D.host.F)) (p : GLoc D.sp.cm.sig V.gram v) (b : Matrix (Fin (wittIndex V)) (Fin (wittIndex V)) (TensorProduct D.host.F (Fv D.host.F v) D.host.E)), b.BlockTriangular id → (HA.mat (F := D.host.F) (Fv D.host.F v) D.sp.cm.sig V.gram p).1 * (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) = (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) * b → p ∈ PLoc Φ.flag0 v := by
  first | exact @GlobalTheory.IwasawaTri.mem_pLoc_flag0_of_mul_eq_upper | exact GlobalTheory.IwasawaTri.mem_pLoc_flag0_of_mul_eq_upper | (intros; apply GlobalTheory.IwasawaTri.mem_pLoc_flag0_of_mul_eq_upper <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchLinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.PolMatchLin

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section Ext
variable {ι : Type} (P : ι → Type) [∀ v, AddCommGroup (P v)] [∀ v, Module ℂ (P v)]

open Classical in

def extFam {S T : Finset ι} (w : ∀ v, P v) (g : ∀ v : S, P v) : ∀ v : T, P v :=
  fun v => if h : v.1 ∈ S then g ⟨v.1, h⟩ else w v.1

theorem extFam_update {S T : Finset ι} (hST : S ⊆ T) (w : ∀ v, P v) [DecidableEq S] [DecidableEq T]
    (g : ∀ v : S, P v) (i : S) (z : P i) :
    extFam P (T := T) w (Function.update g i z) = Function.update (extFam P w g) ⟨i.1, hST i.2⟩ z := by
  funext v
  by_cases hv : v = ⟨i.1, hST i.2⟩
  · subst hv
    simp [extFam, i.2]
  · rw [Function.update_of_ne hv]
    unfold extFam
    split_ifs with h
    · rw [Function.update_of_ne]
      intro e
      apply hv
      apply Subtype.ext
      simp [← e]
    · rfl

def extML {S T : Finset ι} (hST : S ⊆ T) (w : ∀ v, P v) :
    MultilinearMap ℂ (fun v : S => P v) (PiTensorProduct ℂ fun v : T => P v) where
  toFun g := PiTensorProduct.tprod ℂ (extFam P w g)
  map_update_add' g i x y := by
    classical
    simp only [extFam_update P hST]
    exact MultilinearMap.map_update_add _ _ _ _ _
  map_update_smul' g i c x := by
    classical
    simp only [extFam_update P hST]
    exact MultilinearMap.map_update_smul _ _ _ _ _

def extL {S T : Finset ι} (hST : S ⊆ T) (w : ∀ v, P v) :
    (PiTensorProduct ℂ fun v : S => P v) →ₗ[ℂ] PiTensorProduct ℂ fun v : T => P v :=
  PiTensorProduct.lift (extML P hST w)

theorem extL_tprod {S T : Finset ι} (hST : S ⊆ T) (w : ∀ v, P v) (g : ∀ v : S, P v) (g' : ∀ v : T, P v)
    (h1 : ∀ (v : T) (h : v.1 ∈ S), g' v = g ⟨v.1, h⟩) (h2 : ∀ v : T, v.1 ∉ S → g' v = w v.1) :
    extL P hST w (PiTensorProduct.tprod ℂ g) = PiTensorProduct.tprod ℂ g' := by
  unfold extL
  rw [PiTensorProduct.lift.tprod]
  show PiTensorProduct.tprod ℂ (extFam P w g) = _
  congr 1
  funext v
  unfold extFam
  split_ifs with h
  · exact (h1 v h).symm
  · exact (h2 v h).symm

end Ext

section Main

theorem pure_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, smul_eq_mul, mul_assoc]

theorem transport {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a') (hF : IsFinMaps B G X om om' Rf)
    {T₁ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)} (hX : X.T ⊆ T₁) (hST : T₁ ⊆ T) {m m' : ℕ} (f : Fin m → SInf F (Fin a × Fin (a + a')))
    (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ) (f' : Fin m' → SInf F (Fin a' × Fin (a + a')))
    (φ' : Fin m' → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ)
    (hφ : ∀ i, ∀ v ∉ T₁, φ i v = G.M.vac v) (hφ' : ∀ j, ∀ v ∉ T₁, φ' j v = G.M'.vac v)
    (he : ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T₁ => Rf.p v (φ i v)) =
      ∑ j, R.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T₁ => Rf.p' v (φ' j v))) :
    ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v)) =
      ∑ j, R.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ' j v)) := by
  set w : ∀ v, Rf.Pi v := fun v => Rf.p v (G.M.vac v)
  have k1 : ∀ i, extL Rf.Pi hST w (PiTensorProduct.tprod ℂ fun v : T₁ => Rf.p v (φ i v)) =
      PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v) := fun i =>
    extL_tprod _ _ _ _ _ (fun v h => rfl) (fun v h => by simp only [w]; rw [hφ i v h])
  have k2 : ∀ j, extL Rf.Pi hST w (PiTensorProduct.tprod ℂ fun v : T₁ => Rf.p' v (φ' j v)) =
      PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ' j v) := fun j =>
    extL_tprod _ _ _ _ _ (fun v h => rfl) (fun v h => by
      simp only [w]; rw [hφ' j v h, (hF.sph v.1 (fun hv => h (hX hv))).1])
  have := congrArg (LinearMap.lTensor R.Pi (extL Rf.Pi hST w)) he
  simp only [map_sum, LinearMap.lTensor_tmul, k1, k2] at this
  exact this

theorem polMatch_linear : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ} (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsFinMaps B G X om om' Rf → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf 0 0 ∧ ∀ (Φ Ψ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' Ψ' : (Fin a' × Fin (a + a') → AF F) → ℂ) (c : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Ψ Ψ' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf (Φ + c • Ψ) (Φ' + c • Ψ') := by
  intro F E _ _ _ _ _ σ a a' B G X om om' R Rf hF
  refine ⟨?_, ?_⟩
  · refine ⟨X.T, subset_rfl, 0, 0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  · rintro Φ Ψ Φ' Ψ' c ⟨T₁, hX₁, m₁, m₁', f₁, φ₁, f₁', φ₁', h1, h1', rfl, rfl, e1⟩
      ⟨T₂, hX₂, m₂, m₂', f₂, φ₂, f₂', φ₂', h2, h2', rfl, rfl, e2⟩
    classical
    have s1 : T₁ ⊆ T₁ ∪ T₂ := Finset.subset_union_left
    have s2 : T₂ ⊆ T₁ ∪ T₂ := Finset.subset_union_right
    refine ⟨T₁ ∪ T₂, hX₁.trans s1, m₁ + m₂, m₁' + m₂', Fin.append f₁ (fun j => c • f₂ j), Fin.append φ₁ φ₂,
      Fin.append f₁' (fun j => c • f₂' j), Fin.append φ₁' φ₂', ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simp only [Fin.append_left]
        exact ⟨(h1 i).1, (h1 i).2.1, fun v hv => (h1 i).2.2 v (fun h => hv (s1 h))⟩
      · simp only [Fin.append_right]
        exact ⟨Submodule.smul_mem _ c (h2 j).1, (h2 j).2.1, fun v hv => (h2 j).2.2 v (fun h => hv (s2 h))⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simp only [Fin.append_left]
        exact ⟨(h1' i).1, (h1' i).2.1, fun v hv => (h1' i).2.2 v (fun h => hv (s1 h))⟩
      · simp only [Fin.append_right]
        exact ⟨Submodule.smul_mem _ c (h2' j).1, (h2' j).2.1, fun v hv => (h2' j).2.2 v (fun h => hv (s2 h))⟩
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, pure_smul, Finset.smul_sum]
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, pure_smul, Finset.smul_sum]
    · rw [Fin.sum_univ_add, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, map_smul, ← TensorProduct.smul_tmul', ← Finset.smul_sum]
      rw [transport B G X om om' R Rf hF hX₁ s1 f₁ φ₁ f₁' φ₁' (fun i v hv => (h1 i).2.2 v hv)
          (fun j v hv => (h1' j).2.2 v hv) e1,
        transport B G X om om' R Rf hF hX₂ s2 f₂ φ₂ f₂' φ₂' (fun i v hv => (h2 i).2.2 v hv)
          (fun j v hv => (h2' j).2.2 v hv) e2]

end Main

end GlobalTheory.PolMatchLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchOnto
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

theorem polMatch_onto : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ} (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ Φ ∈ algD G.M B.ψ B.emb, ∃ Φ' ∈ algD G.M' B.ψ B.emb, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ' := by
  intro F E _ _ _ _ _ σ a a' B G X om om' R Rf hM Φ hΦ
  classical
  obtain ⟨n, c, g, rfl⟩ := (Submodule.mem_span_set').1 hΦ
  choose f φ hf hφ hfin hg using fun i => (g i).2
  have hfin' : ∀ i, {v | ¬ φ i v = G.M.vac v}.Finite := fun i => Filter.eventually_cofinite.1 (hfin i)
  set T : Finset (Pl F) := X.T ∪ Finset.univ.biUnion (fun i => (hfin' i).toFinset) with hT
  have hout : ∀ i, ∀ v ∉ T, φ i v = G.M.vac v := by
    intro i v hv
    by_contra h
    exact hv (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, (hfin' i).mem_toFinset.2 h⟩))
  have hreal : ∀ i, ∃ f' ∈ G.M'.Pol B.ψ B.emb, R.p' f' = R.p (c i • f i) := by
    intro i
    have : R.p (c i • f i) ∈ (G.M'.Pol B.ψ B.emb).map R.p' := by rw [hM.real.quot'.onto]; trivial
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 this
    exact ⟨y, hy, e⟩
  choose f' hf' hf'eq using hreal
  have hloc : ∀ i v, ∃ y ∈ GlobalTheory.WeilM.SB _, Rf.p' v y = Rf.p v (φ i v) := by
    intro i v
    have : Rf.p v (φ i v) ∈ (GlobalTheory.WeilM.SB _).map (Rf.p' v) := by rw [hM.fin.onto' v]; trivial
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 this
    exact ⟨y, hy, e⟩
  choose φ₀ hφ₀ hφ₀eq using hloc
  let φ' : Fin n → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ :=
    fun i v => if v ∈ T then φ₀ i v else G.M'.vac v
  have hvac' : ∀ v, G.M'.vac v ∈ GlobalTheory.WeilM.SB _ := fun v => (hM.triple.geo.hM'.vac v).1
  have hφ'SB : ∀ i v, φ' i v ∈ GlobalTheory.WeilM.SB _ := by
    intro i v
    by_cases hv : v ∈ T
    · simp only [φ', if_pos hv]; exact hφ₀ i v
    · simp only [φ', if_neg hv]; exact hvac' v
  have hφ'out : ∀ i, ∀ v ∉ T, φ' i v = G.M'.vac v := by
    intro i v hv; simp only [φ', if_neg hv]
  have hpure : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c i • f i) (φ i) = c i • (g i : (Fin a × Fin (a + a') → AF F) → ℂ) := by
    intro i
    rw [hg i]
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
  refine ⟨∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f' i) (φ' i), ?_, T, Finset.subset_union_left, n, n, fun i => c i • f i, φ, f', φ', ?_, ?_, ?_, rfl, ?_⟩
  · refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f' i, φ' i, hf' i, hφ'SB i, ?_, rfl⟩
    exact Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by
      by_contra h; exact hv (hφ'out i v h))
  · exact fun i => ⟨Submodule.smul_mem _ _ (hf i), hφ i, hout i⟩
  · exact fun i => ⟨hf' i, hφ'SB i, hφ'out i⟩
  · exact Finset.sum_congr rfl fun i _ => (hpure i).symm
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf'eq i]
    congr 2
    funext v
    simp only [φ', if_pos v.2]
    exact (hφ₀eq i v).symm

end GlobalTheory.SquareAgree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorOperatorSplitOneRealPlaceStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pureTensorOperator_split_oneRealPlace : ∀ (D : D7) (V : HSp D) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)), IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ → ∀ (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), (∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w) → IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsUnitaryRep π → ∀ w, ∃ Q : H →L[ℂ] H, (∀ g, Q * π (embArch D.sp.cm.sig V.gram w g) = π (embArch D.sp.cm.sig V.gram w g) * Q) ∧ repOp π μ (tensor D.sp.cm.sig V.gram fa ff) = repOp (π.comp (embArch D.sp.cm.sig V.gram w)) (μa w) (fa w) * Q := by
  first | exact @GlobalTheory.TrSplit.repOp_tensor_split | exact GlobalTheory.TrSplit.repOp_tensor_split | (intros; apply GlobalTheory.TrSplit.repOp_tensor_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalUnitaryActsOnThetaRestrictionSmaller
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TowerEmbRat

open GlobalTheory.MixModel

private theorem mt_mul_mt_inv' {D : D7} {S : HSp D} (γ : GA D S) : mt S γ * mt S γ⁻¹ = 1 := by
  simp [Formalism.L2.Theta.mt, map_inv]

private theorem actO_mul_mt_one {D : D7} {S T : HSp D} (γ : GA D S) (u : WO S T) :
    actO S T γ 1 (u ⬝ mt S γ) = u := by
  unfold actO
  have h1 : Formalism.L2.Theta.mt T (1 : GA D T) = 1 := by simp [Formalism.L2.Theta.mt]
  rw [h1, Matrix.one_mul, Matrix.mul_assoc, mt_mul_mt_inv', Matrix.mul_one]

theorem om_rat_right {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (H : IsWeilDatumO ψ S T χS χT om) {γ : GA D S}
    (hγ : γ ∈ GQ S) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (u : WO S T) :
    om (γ, 1) f u = f (u ⬝ mt S γ) := by

  have hback : actO S T γ 1 (u ⬝ mt S γ) = u := actO_mul_mt_one γ u
  have key := GlobalTheory.WeilRat.om_rat_actO D ψ H.std S T χS χT om H γ hγ 1 (one_mem _) f hf (u ⬝ mt S γ)
  rwa [hback] at key

theorem rational_unitary_acts_on_thetaRestriction_smaller_alt : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (d : GlobalTheory.MixModel.HypDec V V' r), d.e = C → d.i₀ = B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (χS' χT' : (AE D)ˣ →* Circle) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V' W χS' χT' ω' → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ g' ∈ GQ V', ∀ (f : WO V W → ℂ), IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (d.emb0 g', 1) f) = ω' (g', 1) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f) := by
  intro D V V' W r C B hs d hdC hdB ψ χS χT ω hω χS' χT' ω' hω' μ 𝓨 hμ g' hg' f hf

  have hiso : ∀ y : Mx D W.rank r, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y = y ⬝ d.pY := by
    intro y
    subst hdC
    rfl
  have hmid : ∀ x : WO V' W, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x = x ⬝ d.p0 := by
    intro x
    subst hdB
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart, HypDec.p0, HypDec.q0, rat, Matrix.mul_assoc]
    rfl
  have hθ : IsThetaFunO ψ V' W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f) :=
    ((GlobalTheory.TowerRestrict.res_theta D V V' W r C B hs ψ hω.std μ 𝓨 hμ).1 f hf).2.1
  funext x
  rw [om_rat_right hω' hg' hθ x]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res]
  congr 1
  funext y
  rw [om_rat_right hω (d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hg') hf, hiso, hmid, hmid, Matrix.add_mul, Matrix.mul_assoc, d.wittDecomp_projY_anisotropicEmbedding,
    Matrix.mul_assoc, d.wittDecomp_projAnisotropic_anisotropicEmbedding, Matrix.mul_assoc]

end GlobalTheory.TowerEmbRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacePointCommuteOfNePlaceStatement
section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlacePoint_commute_of_ne_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ τ' : D.what₂.Tau), τ ≠ τ' → ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'), atTau θ V τ g * atTau θ V τ' g' = atTau θ V τ' g' * atTau θ V τ g := by
  first | exact @GlobalTheory.PointAtPlaceComm.atTau_comm | exact GlobalTheory.PointAtPlaceComm.atTau_comm | (intros; apply GlobalTheory.PointAtPlaceComm.atTau_comm <;> assumption)
end

