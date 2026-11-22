import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0462
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0310
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0397
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1630
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1553
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermsRationalUnipotentInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.UnipMixed

variable {D : D7}

theorem mt_mul_frame (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (g : GA D V) (hg : g ∈ NI V C) :
    mt V g * C.map (incA D) = C.map (incA D) := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨h, -, -⟩ := hg
    have h' : (mt V g - 1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) * (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) = 0 := h
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h'
  | one => rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.one_mul]
  | mul g h _ _ hg hh => rw [GlobalTheory.AdelicLatMove.mt_mul, Matrix.mul_assoc, hh, hg]
  | inv g _ hg =>
    conv_lhs => rw [← hg]
    rw [← Matrix.mul_assoc, ← GlobalTheory.AdelicLatMove.mt_mul, inv_mul_cancel, GlobalTheory.AdelicLatMove.mt_one, Matrix.one_mul]

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace (S.gram⁻¹.map (incA D) * (y.map (cA D))ᵀ * T.gram.map (incA D) * x) := by
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_
  exact Finset.sum_comm

theorem symplOH_isoPart_eq_zero (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (t : Mx D W.rank r)
    (δ : WO V W) (hδ : δ * C.map (incA D) = 0) : symplOH V W (isoPart V W C t) δ = 0 := by
  have hh : hO V W (isoPart V W C t) δ = 0 := by
    rw [hO_eq_trace]
    have hP : (adj D C * V.gram).map (incA D) = ((C.map (incA D)).map (cA D))ᵀ * V.gram.map (incA D) := by
      rw [Matrix.map_mul]; rfl
    have hC : ((C.map (incA D)).map (cA D))ᵀ * (δ.map (cA D))ᵀ = 0 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hδ, Matrix.map_zero _ (map_zero _), Matrix.transpose_zero]
    simp only [isoPart]
    rw [hP, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Matrix.mul_assoc _ (V.gram.map (incA D)), GlobalTheory.SplitOnto.gram_mul_inv, Matrix.mul_one, hC,
      Matrix.zero_mul, Matrix.zero_mul, Matrix.trace_zero]
  simp only [symplOH, symplO, hh, mul_zero, map_zero]

theorem heisO_add_rat (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (x δ : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (hδ : δ.map (incA D) * C.map (incA D) = 0) (t : Mx D W.rank r) :
    heisO ψ V W (x.map (incA D) + δ.map (incA D)) f (isoPart V W C t) =
      heisO ψ V W (x.map (incA D)) f (isoPart V W C t) := by
  have o := symplOH_isoPart_eq_zero V W C t _ hδ
  have ha := GlobalTheory.OrientedFormLaws.symplOH_rat (S := V) (T := W) δ x
  generalize (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat V W δ x)) = a at ha
  have q := hf.quasi δ (isoPart V W C t + x.map (incA D))
  have e : isoPart V W C t + (x.map (incA D) + δ.map (incA D)) = ratW W V δ + (isoPart V W C t + x.map (incA D)) := by
    simp only [ratW]; abel
  have s1 : symplOH V W (ratW W V δ) (isoPart V W C t + x.map (incA D)) = algebraMap D.host.F (AF D.host.F) a := by
    rw [GlobalTheory.FinTranslate.symplOH_add_right, GlobalTheory.FinTranslate.symplOH_skew, ratW, o, neg_zero, zero_add, ha]
  have s2 : ψ (-(algebraMap D.host.F (AF D.host.F) a)) = 1 := by
    rw [← map_neg]; exact hψ.1.2.2.1 (-a)
  simp only [heisO]
  rw [e, q, s1, s2, GlobalTheory.FinTranslate.symplOH_add_right, o, add_zero, one_mul]

theorem res_heisO_unip : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ n ∈ NI V C, n ∈ GQ V → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) (ω (n, 1) f)) 0 = res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) f) 0 := by
  intro D V V' W r C C' B hs _ _ _ ψ χS χT ω hω μ 𝓨 hcov n hnN hnQ y f hf
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E, mt V n = n₀.map (incA D) := by
    obtain ⟨γ', -, e⟩ := hnQ
    exact ⟨γ'.1, (congrArg Units.val e).symm⟩
  set X₀ : Matrix (Fin W.rank) (Fin V.rank) D.host.E := y * (adj D C' * V.gram) with hX₀
  have hx : isoPart V W C' (y.map (incA D)) = X₀.map (incA D) := by
    simp only [isoPart, hX₀, Matrix.map_mul]
  set δ : Matrix (Fin W.rank) (Fin V.rank) D.host.E := X₀ * (n₀ - 1) with hδdef
  have hδ : δ.map (incA D) * C.map (incA D) = 0 := by
    rw [hδdef, Matrix.map_mul, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), ← hn₀, Matrix.mul_assoc,
      Matrix.sub_mul, Matrix.one_mul, mt_mul_frame V C n hnN, sub_self, Matrix.mul_zero]
  have hx' : actO V W n⁻¹ 1 (X₀.map (incA D)) = X₀.map (incA D) + δ.map (incA D) := by
    simp only [actO, inv_inv, GlobalTheory.AdelicLatMove.mt_one, Matrix.one_mul, hn₀, hδdef]
    rw [← Matrix.map_mul, Matrix.mul_sub, Matrix.mul_one, ← Matrix.map_add _ (map_add _), add_sub_cancel]
  have hA : heisO ψ V W (X₀.map (incA D)) (ω (n, 1) f) =
      ω (n, 1) (heisO ψ V W (actO V W n⁻¹ 1 (X₀.map (incA D))) f) := by
    rw [hω.om_heis n 1 _ f hf]
    congr 1
    have := GlobalTheory.AdelicLatMove.actO_actO_inv V W n 1 (X₀.map (incA D))
    rw [inv_one] at this
    exact this.symm
  have hK := GlobalTheory.T.wittTower_restriction_unipotentRadical_invariant D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hcov ⟨n, hnN⟩ _
    (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hω.std hf (actO V W n⁻¹ 1 (X₀.map (incA D))))
  rw [hx, hA, show res V V' W C B μ 𝓨 (ω (n, 1) (heisO ψ V W (actO V W n⁻¹ 1 (X₀.map (incA D))) f)) =
    res V V' W C B μ 𝓨 (heisO ψ V W (actO V W n⁻¹ 1 (X₀.map (incA D))) f) from hK, hx']
  have hm : midPart V V' W B 0 = 0 := by simp [midPart]
  simp only [res, hm, add_zero]
  congr 1
  funext t
  exact heisO_add_rat V W C hω.std hf X₀ δ hδ t

end GlobalTheory.UnipMixed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParameterOperatorUniqueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_parameter_operator_unique : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W,
    ∀ T : ℝ → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')),
    (∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
    ∀ (μ : Measure (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure →
    ∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  first | exact @GlobalTheory.ArchimedeanUnitaryL2.integral_norm_sq_eq | exact GlobalTheory.ArchimedeanUnitaryL2.integral_norm_sq_eq | (intros; apply GlobalTheory.ArchimedeanUnitaryL2.integral_norm_sq_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrientedPairFockMapsLieEquivariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.RealQuot

theorem oriented_maps : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO M X → ℂ) →ₗ[ℂ] Pi), IsCoinvMap θ ω (algF ψ θ ε A B) Pi rf rl p →
  (∀ f, IsFinF ψ θ ε A B f → ∀ τ, ∀ Y ∈ lieAt X τ, ∀ P,
      p (fockF ψ θ ε A B f (GlobalTheory.RealQuot.actT ε A B eS τ Y P)) = rl τ Y (p (fockF ψ θ ε A B f P))) ∧
  (∀ f, IsFinF ψ θ ε A B f → ∀ P ∈ GlobalTheory.RealQuot.coinv ε A B eT, p (fockF ψ θ ε A B f P) = 0) ∧
  ∀ h ∈ GfC X, ∀ f, IsFinF ψ θ ε A B f → ∃ f', IsFinF ψ θ ε A B f' ∧
    ∀ P, rf h (p (fockF ψ θ ε A B f P)) = p (fockF ψ θ ε A B f' P) := by
  intro D ψ θ hθ ε M X A B χS χT ω eS eT hW hexp Pi rf rl p hp
  have hW' : IsWeilDatumO ψ (sgn ε M) X χS χT (ω.toSgn ε) := hW
  have hmem : ∀ f P, IsFinF ψ θ ε A B f → fockF ψ θ ε A B f P ∈ algF ψ θ ε A B :=
    fun f P hf => Submodule.subset_span ⟨f, P, hf, rfl⟩
  have e1 : ∀ h : GA D X, (ω.toSgn ε) (1, h) = ω (1, h) := by
    intro h
    show ω ((ofSgn ε M) 1, h) = ω (1, h)
    rw [map_one]
  have hL := fun f τ (hf : IsFinF ψ θ ε A B f) =>
    GlobalTheory.LieScalar.lieFockAll D (sgn ε M) X (frSgn ε A) B θ ψ χS χT (ω.toSgn ε) f τ (eS τ) (eT τ) hθ hW'
      (hexp τ).1 (hexp τ).2 hf
  refine ⟨?_, ?_, ?_⟩
  · intro f hf τ Y hY P
    refine hp.eql τ Y hY _ (hmem f P hf) _ (hmem f _ hf) ?_
    intro z
    have h := (hL f τ hf).2 Y hY P z
    simp only [e1] at h
    have e2 : actT ε A B eS τ Y P =
        GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ((frSgn ε A).ε τ) (B.ε τ) (B.fr τ * Y * (B.fr τ)⁻¹) P + ((eS τ : ℂ) * Y.trace) • P := by
      rw [actT, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [e2]
    exact h
  · intro f hf P hP
    have hle : coinv ε A B eT ≤ LinearMap.ker (p ∘ₗ fockF ψ θ ε A B f) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨τ, Z, hZ, P₀, rfl⟩
      have hZ' : Z ∈ lieAt (sgn ε M) τ := by rw [GlobalTheory.SgnIdent.lieAt_sgn]; exact hZ
      show p (fockF ψ θ ε A B f (actS ε A B eT τ Z P₀)) = 0
      refine hp.invl τ Z hZ _ (hmem f P₀ hf) _ (hmem f _ hf) ?_
      intro z
      have h := (hL f τ hf).1 Z hZ' P₀ z
      have e : ∀ t : ℝ, (ω.toSgn ε) (oneP θ (sgn ε M) τ Z t, 1) = ω (oneP θ M τ Z t, 1) := by
        intro t
        show ω ((ofSgn ε M) (oneP θ (sgn ε M) τ Z t), 1) = _
        unfold oneP
        rw [GlobalTheory.SgnIdent.atTau_sgn θ hθ]
      simp only [e] at h
      have e3 : actS ε A B eT τ Z P₀ =
          GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ((frSgn ε A).ε τ) (B.ε τ) ((A.fr τ * Z * (A.fr τ)⁻¹).map (starRingEnd ℂ)) P₀ +
            (-((eT τ : ℂ) * Z.trace)) • P₀ := by
        rw [actS, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, neg_smul, sub_eq_add_neg]
      rw [e3]
      exact h
    exact hle hP
  · intro h hh f hf
    refine ⟨ω (1, h) f, ?_, fun P => ?_⟩
    · obtain ⟨hth, hvac⟩ := hf
      have e : ∀ τ z, Formalism.IndefR.Datum.dRho (heisO ψ (sgn ε M) X) θ τ z (ω (1, h) f) =
          ω (1, h) (Formalism.IndefR.Datum.dRho (heisO ψ (sgn ε M) X) θ τ z f) := by
        intro τ z
        rw [← e1, GlobalTheory.OrientedHeis.om_dRho hW' hθ 1 h τ z hth, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ X hh,
          GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ (sgn ε M) (inv_mem (one_mem _)), Matrix.one_mul, Matrix.mul_one]
      refine ⟨?_, fun τ z => ?_⟩
      · rw [← e1]; exact hW'.om_pres _ f hth
      · have h0 := hvac τ z
        unfold annih at h0 ⊢
        rw [e, e, ← map_smul, ← map_add, h0, map_zero]
    · have ht := GlobalTheory.OrientedHeis.om_fin_pureTensorO ψ (sgn ε M) X χS χT (ω.toSgn ε) hW' θ hθ 1 (one_mem _) h hh
        (frSgn ε A).cart B.cart A.onb B.onb f P hf.1
      rw [e1] at ht
      rw [← hp.eqf h hh _ (hmem f P hf)]
      exact congrArg p ht

end GlobalTheory.RealQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSumHalfWittHeisenbergLevelOfZeroCore
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

open scoped Topology

namespace GlobalTheory.BumpMixLevel

variable {D : D7}

theorem symplOH_ext_fin {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x a : Mx D T.rank ρ)
    (ha : a.map (infPart D) = 0) :
    symplOH S T (d.extX T x) (d.extY T a) = pairA D.host.F 0 (symplOH S T (d.extX T x) (d.extY T a)).2 := by
  have hfin : (d.extY T a).map (infPart D) = 0 := by
    rw [HypDec.extY_apply, Matrix.map_mul, ha, Matrix.zero_mul]
  have h3 : GlobalTheory.FinTranslate.eInf D * symplOH S T (d.extX T x) (d.extY T a) = 0 := by
    rw [← GlobalTheory.FinTranslate.symplOH_smul_right, GlobalTheory.FinTranslate.smul_fin hfin, GlobalTheory.FinTranslate.symplOH_zero_right]
  exact Prod.ext ((one_mul _).symm.trans (congrArg Prod.fst h3)) rfl

theorem exists_level_pair (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) {S S₀ T : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) (K : Set (Mx D T.rank ρ)) (hK : IsCompact K) :
    ∃ U : AddSubgroup (Mx D T.rank ρ), IsOpen (U : Set (Mx D T.rank ρ)) ∧
      ∀ a ∈ U, a.map (infPart D) = 0 → ∀ k ∈ K, ψ (symplOH S T (d.extX T k) (d.extY T a)) = 1 := by
  have hX : Continuous (d.extX T) := continuous_id.matrix_mul continuous_const
  have hY : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
  have hs : Continuous fun p : Mx D T.rank ρ × Mx D T.rank ρ => (symplOH S T (d.extX T p.1) (d.extY T p.2)).2 :=
    continuous_snd.comp (GlobalTheory.OrientedHeis.continuous_symplOH (hX.comp continuous_fst) (hY.comp continuous_snd))
  have hZ := GlobalTheory.FinTranslate.ker_mem_nhds hψ.1.1 hψ.1.2.1
  have hO := (isOpen_interior (s := {b : Af D.host.F | ψ (pairA D.host.F 0 b) = 1})).preimage hs
  have hsub : K ×ˢ ({0} : Set (Mx D T.rank ρ)) ⊆
      (fun p : Mx D T.rank ρ × Mx D T.rank ρ => (symplOH S T (d.extX T p.1) (d.extY T p.2)).2) ⁻¹'
        interior {b : Af D.host.F | ψ (pairA D.host.F 0 b) = 1} := by
    rintro ⟨k, a⟩ ⟨-, ha⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    simp only [Set.mem_preimage, map_zero, GlobalTheory.FinTranslate.symplOH_zero_right, Prod.snd_zero]
    exact mem_interior_iff_mem_nhds.2 hZ
  obtain ⟨u, v, -, hv, hKu, h0v, huv⟩ := generalized_tube_lemma hK isCompact_singleton hO hsub
  obtain ⟨U, hUo, hU⟩ := GlobalTheory.MixSumBound.finite_points_in_nhds D T.rank ρ v (hv.mem_nhds (h0v rfl))
  refine ⟨U, hUo, fun a ha hfin k hk => ?_⟩
  have h1 := huv (Set.mk_mem_prod (hKu hk) (hU a ha hfin))
  have h2 : (symplOH S T (d.extX T k) (d.extY T a)).2 ∈ {b : Af D.host.F | ψ (pairA D.host.F 0 b) = 1} :=
    interior_subset h1
  rw [symplOH_ext_fin d k a hfin]
  exact h2

theorem poinX_heis_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), S₀.rank = 0 → ∀ (β : Mx D T.rank ρ → ℂ), IsBump β → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (poinX ψ d T β) = poinX ψ d T β := by
  intro D ψ hψ S S₀ T ρ d h0 β hβ
  haveI : LocallyCompactSpace (Mx D T.rank ρ) := (GlobalTheory.MixModel.lattice_Mx D T.rank ρ).2.1
  obtain ⟨Uβ, hUβo, hUβ⟩ := hβ.level
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : Mx D T.rank ρ)
  obtain ⟨UC, hUCo, hUC⟩ := GlobalTheory.MixSumBound.finite_points_in_nhds D T.rank ρ C hC0
  obtain ⟨UY, hUYo, hUY⟩ := GlobalTheory.BumpMixLevel.exists_level_pair ψ hψ d (tsupport β ∪ C) (hβ.supp.isCompact.union hC)
  let pX : WO S T →+ Mx D T.rank ρ :=
    { toFun := fun u => u ⬝ d.jX, map_zero' := Matrix.zero_mul _, map_add' := fun _ _ => Matrix.add_mul _ _ _ }
  let pY : WO S T →+ Mx D T.rank ρ :=
    { toFun := fun u => u ⬝ d.jY, map_zero' := Matrix.zero_mul _, map_add' := fun _ _ => Matrix.add_mul _ _ _ }
  have hpX : Continuous pX := continuous_id.matrix_mul continuous_const
  have hpY : Continuous pY := continuous_id.matrix_mul continuous_const
  refine ⟨(Uβ ⊓ UC).comap pX ⊓ UY.comap pY, ((hUβo.inter hUCo).preimage hpX).inter (hUYo.preimage hpY), ?_⟩
  intro u hu hfin
  have hsub0 : ∀ z : WO S₀ T, z = 0 := fun z => Matrix.ext fun i j => absurd j.isLt (by omega)
  have hw : ∀ w : WO S T, w = d.extX T (w ⬝ d.jX) + d.extY T (w ⬝ d.jY) := fun w => by
    conv_lhs => rw [eq_coords d w]
    rw [hsub0 (w ⬝ d.j0), map_zero, add_zero]
  have hx₀ : u ⬝ d.jX ∈ Uβ ∧ u ⬝ d.jX ∈ UC := hu.1
  have ha₀ : u ⬝ d.jY ∈ UY := hu.2
  have hfx : (u ⬝ d.jX).map (infPart D) = 0 := by rw [Matrix.map_mul, hfin, Matrix.zero_mul]
  have hfa : (u ⬝ d.jY).map (infPart D) = 0 := by rw [Matrix.map_mul, hfin, Matrix.zero_mul]
  have h00 : ψ (symplOH S T (d.extX T (u ⬝ d.jX)) (d.extY T (u ⬝ d.jY))) = 1 :=
    hUY _ ha₀ hfa _ (Or.inr (hUC _ hx₀.2 hfx))
  funext w
  have hs : symplOH S T w u = symplOH S T (d.extX T (w ⬝ d.jX)) (d.extY T (u ⬝ d.jY)) -
      symplOH S T (d.extX T (u ⬝ d.jX)) (d.extY T (w ⬝ d.jY)) := by
    conv_lhs => rw [hw w, hw u]
    simp only [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, d.symplOH_extX_extX,
      d.symplOH_extY_extY, zero_add, add_zero]
    rw [GlobalTheory.MixModel.symplOH_skew S T (d.extX T (u ⬝ d.jX)) (d.extY T (w ⬝ d.jY))]
    abel
  simp only [heisO, poinX]
  rw [← tsum_mul_left]
  refine tsum_congr fun γ => ?_
  rw [Matrix.add_mul, Matrix.add_mul]
  have hb : β (w ⬝ d.jX + u ⬝ d.jX + rat γ) = β (w ⬝ d.jX + rat γ) := by
    rw [add_right_comm]; exact hUβ _ hx₀.1 hfx _
  rw [hb]
  by_cases hk : β (w ⬝ d.jX + rat γ) = 0
  · rw [hk, mul_zero, mul_zero, mul_zero]
  have hkK : ψ (symplOH S T (d.extX T (w ⬝ d.jX + rat γ)) (d.extY T (u ⬝ d.jY))) = 1 :=
    hUY _ ha₀ hfa _ (Or.inl (subset_tsupport β hk))
  rw [← mul_assoc, ← d.symplOH_extX_extY T, ← d.symplOH_extX_extY T, ← AddChar.map_add_eq_mul, hs]
  have he : symplOH S T (d.extX T (w ⬝ d.jX)) (d.extY T (u ⬝ d.jY)) -
      symplOH S T (d.extX T (u ⬝ d.jX)) (d.extY T (w ⬝ d.jY)) +
      symplOH S T (d.extX T (w ⬝ d.jX + u ⬝ d.jX + 2 • rat γ)) (d.extY T (w ⬝ d.jY + u ⬝ d.jY)) =
      symplOH S T (d.extX T (w ⬝ d.jX + 2 • rat γ)) (d.extY T (w ⬝ d.jY)) +
        (symplOH S T (d.extX T (w ⬝ d.jX + rat γ)) (d.extY T (u ⬝ d.jY)) +
          symplOH S T (d.extX T (w ⬝ d.jX + rat γ)) (d.extY T (u ⬝ d.jY))) +
        symplOH S T (d.extX T (u ⬝ d.jX)) (d.extY T (u ⬝ d.jY)) := by
    simp only [map_add, two_nsmul, GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right]
    abel
  rw [he]
  simp only [AddChar.map_add_eq_mul, hkK, h00, mul_one]

end GlobalTheory.BumpMixLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankPolynomialFockSchrodingerModelLeAleph0
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM

noncomputable section

namespace GlobalTheory.FockCount

open NumberField

theorem incM_map_piInf' {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n m : Type}
    (J : Matrix n m E) {w : InfinitePlace F} (τ : GlobalTheory.AdelicU.EmbOver E w) :
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf τ) = J.map τ.1 := by
  ext i j
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf, GlobalTheory.AdelicU.compInf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR,
    GlobalTheory.AdelicU.infEmb_tmul]

theorem rank_tens_le (F : Type) [Field F] [NumberField F] (P Q R S : ℕ) :
    Module.rank ℂ (GlobalTheory.RealLift.Tens F P Q R S) ≤ Cardinal.aleph0 := by
  classical
  let b := _root_.Basis.piTensorProduct (R := ℂ)
    (fun _ : InfinitePlace F => MvPolynomial.basisMonomials (Formalism.BasicNotions.TH.Ix P Q × Formalism.BasicNotions.TH.Ix R S) ℂ)
  rw [← b.mk_eq_rank'']
  exact Cardinal.mk_le_aleph0

theorem rank_pol_le_aleph0 : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d r s r' s' : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ →
    Module.rank ℂ (M.Pol B.ψ B.emb) ≤ Cardinal.aleph0 := by
  intro F E _ _ _ _ _ σ B n d r s r' s' X W M hB hX hW _hM
  classical
  have hcm := hB.cm
  have hstd := hB.std
  have hFr : ∀ w, ∃ A : Matrix (Fin n) (Formalism.BasicNotions.TH.Ix r s) ℂ,
      GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) A ∧ X.θ w * A = A * Formalism.BasicNotions.TH.Jm r s := by
    intro w
    rw [incM_map_piInf', one_smul]
    exact GlobalTheory.T.cartanEigen_orthonormalFrame_exists n r s _ _ (hX.sig w) (hX.cartan w)
  have hFrW : ∀ w, ∃ C : Matrix (Fin d) (Formalism.BasicNotions.TH.Ix r' s') ℂ,
      GlobalTheory.RealLift.IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) C ∧
        W.θ w * C = C * Formalism.BasicNotions.TH.Jm r' s' := by
    intro w
    rw [incM_map_piInf']
    exact GlobalTheory.T.cartanEigen_orthonormalFrame_exists d r' s' _ _ (hW.sig w) (hW.cartan w)
  choose A hA hAθ using hFr
  choose C hC hCθ using hFrW
  have hFramed : GlobalTheory.RealLift.Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C :=
    ⟨one_mul _, hA, hC⟩
  have hder := GlobalTheory.T.archHeisenbergDerivatives_exist
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hder F E σ (Fin n) (Fin d) (Fin n × Fin d) r s r' s' B.ψ B.emb (incM F X.J)
    (incM F W.J) M.co 1 Complex.I A C hcm hstd hFramed
  have hrange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.RealLift.actsLaws hder (GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder) F E σ n d r s r' s' X W M B.ψ B.emb A C Φ
    hcm hstd hFramed hAθ hCθ hΦ
  rw [← hrange]
  exact (rank_range_le Φ).trans (rank_tens_le F r s r' s')

end GlobalTheory.FockCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueConjugatePlaceHermitianDualBasisStabilise
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjChar

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf

theorem cpt_cP_eq_zero_of_orth {D : D7} {PP : Pl D.host.E} {e : EAf D} (ho : e * GlobalTheory.StdFrames.sg D e = 0)
    (h1 : GlobalTheory.StdFrames.cpt PP e = 1) : GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP PP) e = 0 := by
  have h2 := GlobalTheory.StdFrames.cpt_sg_eq_zero (Q := GlobalTheory.IdemSupport.cP PP) (z := 1 - e)
    (by rw [GlobalTheory.StdFrames.cP_cP, RingHom.map_sub, h1, RingHom.map_one, sub_self])
  rw [RingHom.map_sub, RingHom.map_one, RingHom.map_sub, RingHom.map_one, sub_eq_zero] at h2
  have h3 := congrArg (GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP PP)) ho
  rwa [RingHom.map_mul, ← h2, mul_one, RingHom.map_zero] at h3

theorem resT_eq_zero_of_fixed {D : D7} {Q : Pl D.host.E} {e x : EAf D} (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (he : GlobalTheory.StdFrames.cpt Q e = 0) (hf : x = e * x) : resT Q x = 0 := by
  unfold resT
  rw [dif_pos hx]
  refine (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt Q ⟨x, hx⟩).2 ?_
  have h0 : GlobalTheory.StdFrames.cpt Q x = 0 := by rw [hf, RingHom.map_mul, he, zero_mul]
  show Valued.v (GlobalTheory.StdFrames.cpt Q x) < 1
  rw [h0, Valuation.map_zero]
  exact zero_lt_one

theorem resT_cP_hT_bwd_eq_zero : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ PP : Pl D.host.E, GlobalTheory.SeeConjChar.sideAt X h PP = true → ∀ M ∈ St β, ∀ i j : Fin D.R.k, GlobalTheory.SeeConjChar.hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h j)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.hT X h (bwdT X h i) (Matrix.mulVec M.val (bwT X h j))) = 0 := by
  intro D X h β hF PP hs M hM i j
  have hb := X.vectorsInLattice.2.2
  have ho := X.ew_orth
  have hw := X.bwd_w i
  have h1 : GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 := by
    unfold sideAt at hs
    simpa only [decide_eq_true_eq] using hs
  have hfix : ∀ v, hA X.B.I (X.bwd i) v = X.ew * hA X.B.I (X.bwd i) v := fun v => by
    conv_lhs => rw [hw, unitaryCongruence.hA_smul_left, unitaryCongruence.sigA_sigA]
  obtain ⟨⟨I⟩⟩ := X
  dsimp only at h hb ho hfix
  subst h
  have hv := (hb j).1
  rw [GlobalTheory.SeeMatchOnto.Lf_eq] at hv
  have hv2 := (GlobalTheory.SeeMatchOnto.mem_hatL_iff_of_St hF hM _).1 hv
  have hv3 := (GlobalTheory.SeeMatchOnto.Lf_eq (D := D)).ge hv2
  have hint := unitaryCongruence.hA_int _ (hb i).2 hv3
  exact ⟨hint, resT_eq_zero_of_fixed hint (cpt_cP_eq_zero_of_orth ho h1) (hfix _)⟩

end GlobalTheory.SeeConjChar
end

