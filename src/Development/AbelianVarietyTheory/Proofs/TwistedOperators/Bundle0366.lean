import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0243
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.BesselDatum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0347
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeHypothesisFormsAgree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0339
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0338
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0259
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0246

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionComplementTranslatesLocallyConst
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.HalfAverage

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfSupport

variable {D : D7}

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace (HMul.hMul (HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D)) (Matrix.transpose (y.map (cA D))))
      (T.gram.map (incA D))) x) := by
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans
    (Finset.sum_comm.trans (Finset.sum_congr rfl fun d _ => Finset.sum_comm))

theorem trace_inverseGram_conj_smul_eq {R : Type} [CommRing R] {w r n : ℕ} (Gi : Matrix (Fin n) (Fin n) R) (Nt : Matrix (Fin n) (Fin r) R)
    (Tt : Matrix (Fin r) (Fin w) R) (GW : Matrix (Fin w) (Fin w) R) (a : Matrix (Fin w) (Fin r) R)
    (M : Matrix (Fin r) (Fin n) R) (hP : M * Gi * Nt = 1) :
    Matrix.trace (Gi * (Nt * Tt) * GW * (a * M)) = Matrix.trace (Tt * (GW * a)) := by
  rw [show Gi * (Nt * Tt) * GW * (a * M) = (Gi * Nt * Tt * GW * a) * M by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm, show M * (Gi * Nt * Tt * GW * a) = (M * Gi * Nt) * (Tt * (GW * a)) by
      simp only [Matrix.mul_assoc], hP, Matrix.one_mul]

theorem adj_mul_conj {r n : ℕ} (C : Matrix (Fin n) (Fin r) D.host.E) (K : Matrix (Fin r) (Fin n) D.host.E)
    (hKC : K * C = 1) : adj D C * Matrix.transpose (K.map star) = 1 := by
  have e1 : adj D C = Matrix.conjTranspose C := rfl
  have e2 : Matrix.transpose (K.map star) = Matrix.conjTranspose K := rfl
  rw [e1, e2, ← Matrix.conjTranspose_mul, hKC, Matrix.conjTranspose_one]

theorem symplO_isoPart_restEmb (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (K : Matrix (Fin r) (Fin V.rank) D.host.E) (hKC : K * C = 1) (a t : Mx D W.rank r) :
    symplO V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C a) (restEmb V W K t) =
      Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 *
        ∑ i, ∑ j, cA D (t i j) * (HMul.hMul (W.gram.map (incA D)) a : Mx D W.rank r) i j) := by
  rw [symplO, hO_eq_trace]
  congr 2
  have hN : (restEmb V W K t).map (cA D) =
      HMul.hMul (t.map (cA D)) ((K.map star).map (incA D)) := by
    rw [restEmb, Matrix.map_mul]
    congr 1
  have hP : HMul.hMul (HMul.hMul ((adj D C * V.gram).map (incA D)) ((V.gram⁻¹).map (incA D)))
      (Matrix.transpose ((K.map star).map (incA D))) = (1 : Matrix (Fin r) (Fin r) (AE D)) := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.mul_assoc (adj D C),
      Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit V), Matrix.mul_one, adj_mul_conj C K hKC,
      Matrix.map_one _ (map_zero _) (map_one _)]
  rw [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart, hN, Matrix.transpose_mul]
  rw [trace_inverseGram_conj_smul_eq _ _ _ _ _ _ hP]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  exact Finset.sum_comm

theorem res_smul (V V' W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (c : ℂ) (g : WO V W → ℂ) :
    res V V' W C B μ 𝓨 (c • g) = c • res V V' W C B μ 𝓨 g := by
  funext x
  simp only [res, Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

theorem res_eq_zero_of_ne {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V V' W : HSp D} {r : ℕ}
    {C : Matrix (Fin V.rank) (Fin r) D.host.E} {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E}
    (hs : IsIsoSplit V V' C B) {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (hμ : IsCovolOne (ratMx D W.rank r) μ 𝓨) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (w : WO V W)
    {y : Mx D W.rank r} (hy : heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) f = f)
    (hne : ψ (symplO V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) w) ≠ 1) :
    res V V' W C B μ 𝓨 (heisO ψ V W w f) = 0 := by
  have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w
  have h4 := ((GlobalTheory.TowerRestrict.res_theta D V V' W r C B hs ψ hψ μ 𝓨 hμ).1 _ hg).2.2.2 y
  rw [GlobalTheory.SplitScalar.heisO_comm, hy, res_smul] at h4
  have h5 : (ψ (symplO V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) w) - 1) • res V V' W C B μ 𝓨 (heisO ψ V W w f) = 0 := by
    rw [sub_smul, h4, one_smul, sub_self]
  exact (smul_eq_zero.1 h5).resolve_left (sub_ne_zero.2 hne)

theorem sum_single {m n : ℕ} (t : Mx D m n) (i : Fin m) (j : Fin n) (s : AE D) :
    ∑ k, ∑ l, cA D (t k l) * (Matrix.single i j s : Mx D m n) k l = cA D (t i j) * s := by
  simp [Matrix.single_apply, mul_ite, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem continuous_isoPart_single (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (G : Matrix (Fin W.rank) (Fin W.rank) (AE D)) (i : Fin W.rank) (j : Fin r) :
    Continuous fun s : AE D =>
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C (HMul.hMul G (Matrix.single i j s : Mx D W.rank r) : Mx D W.rank r) := by
  have : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  have h1 : Continuous fun s : AE D => (Matrix.single i j s : Matrix (Fin W.rank) (Fin r) (AE D)) := by
    have e : (fun s : AE D => (Matrix.single i j s : Matrix (Fin W.rank) (Fin r) (AE D))) =
        fun s => s • (Matrix.single i j 1 : Matrix (Fin W.rank) (Fin r) (AE D)) := by
      funext s; rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [e]
    exact continuous_id.smul continuous_const
  exact (continuous_const.matrix_mul h1).matrix_mul continuous_const

set_option maxHeartbeats 800000 in

theorem supp_locConst : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ K : Matrix (Fin r) (Fin V.rank) D.host.E, K * C = 1 → K * B = 0 → ∀ e, IsSplitIdem D e → ∀ f, IsThetaFunO ψ V W f → ∃ (L : AddSubgroup (halfMx (cA D e) W.rank r)) (Kc : Set (halfMx (cA D e) W.rank r)), IsOpen (L : Set (halfMx (cA D e) W.rank r)) ∧ IsCompact Kc ∧ (∀ t, t ∉ Kc → res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t) f) = 0) ∧ ∀ t, ∀ l ∈ L, heisO ψ V W (restEmb V W K (t + l : halfMx (cA D e) W.rank r)) f = heisO ψ V W (restEmb V W K t) f := by
  intro D ψ hψ V V' W r C B hs μ 𝓨 hμ K hKC _ e he f hf
  have : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  obtain ⟨U, hUo, hU⟩ := hf.level
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  let R : halfMx (cA D e) W.rank r →+ WO V W :=
    { toFun := fun t => restEmb V W K t
      map_zero' := Matrix.zero_mul _
      map_add' := fun x y => restEmb_add V W K x y }
  have hRc : Continuous R := continuous_subtype_val.matrix_mul continuous_const

  let Gi : Matrix (Fin W.rank) (Fin W.rank) (AE D) := (W.gram⁻¹).map (incA D)
  have hGG : HMul.hMul (W.gram.map (incA D)) Gi = (1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit W),
      Matrix.map_one _ (map_zero _) (map_one _)]

  have key : ∀ (i : Fin W.rank) (j : Fin r), ∃ Cij : Set (AE D), IsCompact Cij ∧ ∀ x, e * x = x →
      (∀ s ∈ (fun s : AE D => GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C
        (HMul.hMul Gi (Matrix.single i j s : Mx D W.rank r) : Mx D W.rank r)) ⁻¹' (U : Set (WO V W)),
        e * s = s → ψ (Algebra.trace (AF D.host.F) (AE D) (x * s)) = 1) → x ∈ Cij := fun i j => by
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C
        (HMul.hMul Gi (Matrix.single i j (0 : AE D) : Mx D W.rank r) : Mx D W.rank r) = 0 := by
      rw [Matrix.single_zero, Matrix.mul_zero]
      exact Matrix.zero_mul _
    refine GlobalTheory.SplitAnnihilator.annihilator_subset_compact D ψ (GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ) e he _ ?_
    refine (continuous_isoPart_single V W C Gi i j).continuousAt.preimage_mem_nhds ?_
    rw [h0]
    exact hUo.mem_nhds U.zero_mem
  choose Cij hCc hCm using key
  let Kij : Fin W.rank → Fin r → Set (AE D) := fun i j =>
    (fun x => cA D (incA D D.host.xi0⁻¹ * x)) '' Cij i j
  refine ⟨U.comap R, {t | ∀ i j, (t : Mx D W.rank r) i j ∈ Kij i j}, hUo.preimage hRc, ?_, ?_, ?_⟩
  · have hK : IsCompact (Set.pi Set.univ fun i => Set.pi Set.univ fun j => Kij i j :
        Set (Fin W.rank → Fin r → AE D)) :=
      isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
        (hCc i j).image (GlobalTheory.FockCompare.ThetaCont.continuous_conj.comp (continuous_const.mul continuous_id))
    have := (isClosed_halfMx (cA D e) W.rank r).isClosedEmbedding_subtypeVal.isCompact_preimage hK
    have e : {t : halfMx (cA D e) W.rank r | ∀ i j, (t : Mx D W.rank r) i j ∈ Kij i j} =
        Subtype.val ⁻¹' (Set.pi Set.univ fun i => Set.pi Set.univ fun j => Kij i j :
          Set (Fin W.rank → Fin r → AE D)) := by
      ext t
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [e]
    exact this
  · intro t ht
    by_contra hne
    apply ht
    intro i j
    have hti : cA D e * (t : Mx D W.rank r) i j = (t : Mx D W.rank r) i j := t.2 i j
    have hti' : e * cA D ((t : Mx D W.rank r) i j) = cA D ((t : Mx D W.rank r) i j) := by
      have := congrArg (cA D) hti
      rwa [map_mul, GlobalTheory.DualPairCheck.cA_cA] at this
    refine ⟨incA D D.host.xi0 * cA D ((t : Mx D W.rank r) i j), hCm i j _ (by rw [mul_left_comm, hti']) ?_, ?_⟩
    · intro s hsU hse
      by_contra hψ1
      have ha : IsHalf e (HMul.hMul Gi (Matrix.single i j s : Mx D W.rank r) : Mx D W.rank r) := by
        refine mul_isHalf (fun k l => ?_) Gi
        simp only [Matrix.single_apply]
        split_ifs
        · exact hse
        · exact mul_zero e
      have hfin := GlobalTheory.SplitScalar.half_fin he (isHalf_mul ha ((adj D C * V.gram).map (incA D)))
      apply hne
      refine res_eq_zero_of_ne hψ hs hμ hf _ (hU _ hsU hfin) ?_
      rw [symplO_isoPart_restEmb V W C K hKC, ← Matrix.mul_assoc, hGG, Matrix.one_mul, sum_single, ← mul_assoc]
      exact hψ1
    · show cA D (incA D D.host.xi0⁻¹ * (incA D D.host.xi0 * cA D ((t : Mx D W.rank r) i j))) = _
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (GlobalTheory.IndefiniteRowSideFullHecke.BesselData.embedding_xi_zero_ne_zero D), map_one, one_mul,
        GlobalTheory.DualPairCheck.cA_cA]
  · intro t l hl
    have hl' : restEmb V W K l ∈ U := hl
    have hlh : IsHalf (cA D e) (restEmb V W K l) := isHalf_mul l.2 _
    have hth : IsHalf (cA D e) (restEmb V W K t) := isHalf_mul t.2 _
    have hfin := GlobalTheory.SplitScalar.half_fin he' hlh
    rw [AddSubgroup.coe_add, restEmb_add, GlobalTheory.SplitScalar.heisO_add_of_orth ψ V W
      (GlobalTheory.SplitScalar.symplO_eq_zero V W (by rw [GlobalTheory.DualPairCheck.cA_cA, he.2.1]) hth hlh), hU _ hl' hfin]

end GlobalTheory.HalfSupport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceMulEndomorphismIsotypicRepStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_mul_endomorphism_isotypicRep : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N] [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X), π.IsIrreducible → (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) → IsIsotypicAlg π ρ → ∀ H : X →ₗ[ℂ] X, (∀ g x, H (ρ g x) = ρ g (H x)) → (∃ s : Finset (π.IntertwiningMap ρ), LinearMap.range H ≤ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap) → ∃ c : ℂ, ∀ (A : N →ₗ[ℂ] N) (B : X →ₗ[ℂ] X), (∀ φ : π.IntertwiningMap ρ, B ∘ₗ φ.toLinearMap = φ.toLinearMap ∘ₗ A) → ∀ b, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace A b → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace (H ∘ₗ B) (c * b) := by
  first | exact @GlobalTheory.IsoTrace.trace_mul_isotypic | exact GlobalTheory.IsoTrace.trace_mul_isotypic | (intros; apply GlobalTheory.IsoTrace.trace_mul_isotypic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransposeGramUnitarySurjectiveFinitePlaceSupport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.SquareAgree.KapOnto

variable {D : D7}

theorem inv_mem (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (x : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) :
    Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom x.1 ∈
      HR (AF D.host.F) D.sp.cm.sig X.gram := by
  have hx : (x.1.1 : Matrix (Fin d) (Fin d) (AE D))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J *
      (x.1.1 : Matrix (Fin d) (Fin d) (AE D)).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := x.2
  show (((x.1.1 : Matrix (Fin d) (Fin d) (AE D)).submatrix e e).map (cA D))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram *
    (x.1.1 : Matrix (Fin d) (Fin d) (AE D)).submatrix e e = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram
  generalize (x.1.1 : Matrix (Fin d) (Fin d) (AE D)) = Y at hx ⊢
  rw [hJ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at hx
  have hx' := congrArg (fun y => incA D (D.host.xi0)⁻¹ • y) hx
  simp only [smul_smul, ← map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_smul] at hx'
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (reindex e e X.gramᵀ) = reindex e e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram)ᵀ := rfl
  rw [e1] at hx'
  have hs := congrArg (fun y => y.submatrix e e) hx'
  simp only [reindex_apply] at hs
  rw [← submatrix_mul_equiv _ _ _ e _, ← submatrix_mul_equiv _ _ _ e _] at hs
  simp only [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id, ← transpose_submatrix,
    ← Matrix.submatrix_map] at hs
  have ht := congrArg transpose hs
  rw [transpose_mul, transpose_mul, transpose_transpose, transpose_transpose, ← Matrix.mul_assoc] at ht
  exact ht

set_option maxHeartbeats 1600000 in

theorem kapX_onto : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d)
    (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F),
    ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Wd (GlobalTheory.AdelicU.evFin D.host.F v), ∃ h' ∈ GfC X, kapX X e hJ h' = h := by
  intro D X d e Wd hJ v h hh
  let h' : GA D X := ⟨Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom h.1, inv_mem X e hJ h⟩
  refine ⟨h', ?_, ?_⟩
  · set a : AF D.host.F := 1 - GlobalTheory.EmbChart.atPlace v 1 with ha
    have h0 : GlobalTheory.AdelicU.evFin D.host.F v a = 0 := by
      rw [ha, map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
    have h1 : fstA D.host.F a = 1 := by
      show (1 : Ainf D.host.F) - (0 : Ainf D.host.F) = 1
      exact sub_zero 1
    let f := Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
    have hf1 : f (a ⊗ₜ[D.host.F] (1 : D.host.E)) = 1 := by
      simp only [f, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, h1]
      rfl
    have hz : ∀ i j, f ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h - 1) i j) = 0 := by
      intro i j
      have k := congrFun (congrFun (hh a h0) i) j
      rw [Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply] at k
      have k2 := congrArg f k
      rw [map_mul, map_zero, hf1, one_mul] at k2
      exact k2
    rw [GfC, MonoidHom.mem_ker]
    apply Units.ext
    ext i j
    show f (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h (e i) (e j)) = (1 : Matrix (Fin X.rank) (Fin X.rank) _) i j
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h (e i) (e j) =
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h - 1) (e i) (e j) + (1 : Matrix (Fin d) (Fin d) (AE D)) (e i) (e j) := by
      rw [Matrix.sub_apply, sub_add_cancel]
    rw [e2, map_add, hz, zero_add]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq (α := AF D.host.F ⊗[D.host.F] D.host.E), map_one,
        Matrix.one_apply_eq (α := Ainf D.host.F ⊗[D.host.F] D.host.E)]
    · rw [Matrix.one_apply_ne (α := AF D.host.F ⊗[D.host.F] D.host.E) (e.injective.ne hij), map_zero,
        Matrix.one_apply_ne (α := Ainf D.host.F ⊗[D.host.F] D.host.E) hij]
  · apply Subtype.ext
    apply Units.ext
    ext i j
    show (h.1.1 : Matrix (Fin d) (Fin d) (AE D)) (e (e.symm i)) (e (e.symm j)) = h.1.1 i j
    simp only [Equiv.apply_symm_apply]

end GlobalTheory.SquareAgree.KapOnto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncatedKernelOrbitSumStatement
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
theorem _root_.GlobalTheory.T.truncated_kernel_orbit_sum : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (K : Subgroup (GA D V)) (f : GA D V → ℂ), (∀ 𝔉 : IsoFlag V, 𝔉.Proper → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.UnipIntegralsVanish 𝔉 f) → ∀ 𝔬 : Set (GF V), (∀ δ ∈ 𝔬, ∀ g, g * δ * g⁻¹ ∈ 𝔬) → ∀ Tr x, kT Φ K 𝔬 f Tr x = ∑' δ : 𝔬, f (x⁻¹ * rat V δ * x) := by
  first | exact @GlobalTheory.TruncKer.kT_eq_of_unipIntegralsVanish | exact GlobalTheory.TruncKer.kT_eq_of_unipIntegralsVanish | (intros; apply GlobalTheory.TruncKer.kT_eq_of_unipIntegralsVanish <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncationFamilyUnipotentInvariantStatement
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
theorem _root_.GlobalTheory.T.truncation_family_unipotent_invariant : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ Q, IsPar Q → ∀ u ∈ Q, ∀ hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V (Φ.sub u), ∀ n ∈ NA (IsoFlag.single hW), ∀ x Tr, Yfam Φ (levelAll D.sp.cm.sig V.gram L a) (n * x) Tr Q = Yfam Φ (levelAll D.sp.cm.sig V.gram L a) x Tr Q := by
  first | exact @GlobalTheory.TruncKer.yfam_unipRad_mul | exact GlobalTheory.TruncKer.yfam_unipRad_mul | (intros; apply GlobalTheory.TruncKer.yfam_unipRad_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeHypothesisFormsAgreeStatement
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
theorem _root_.GlobalTheory.T.typeHypothesis_forms_agree : ∀ (D : D7) (V : HSp D) (T : TypeDataG V), NoFixed T → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ ∧ GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.NoRadicalFixed T := by
  first | exact @GlobalTheory.TypeHypForms.hypH_and_noRadicalFixed | exact GlobalTheory.TypeHypForms.hypH_and_noRadicalFixed | (intros; apply GlobalTheory.TypeHypForms.hypH_and_noRadicalFixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeIdempotentOperatorFixSpanImages
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

namespace GlobalTheory

theorem idemOp_fix_span : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ (v : T.S) (x : W), x ∈ Submodule.span ℂ {y | ∃ φ : T.W v →ₗ[ℂ] W, (∀ (k : Kv V v) z, φ (T.τ v ((T.frame v).red k) z) = σ (locFin V v k) (φ z)) ∧ y ∈ LinearMap.range φ} → smoothOp (σ.comp (locFin V v)) (μf v) (T.idem μf v) x = x := by
  intro D V T μf hμ W _ _ σ hσ v x hx
  haveI := hμ v
  have hc : Continuous (locFin V v) := (continuous_emb _ _ _).subtype_mk _
  have hs : IsSmooth (σ.comp (locFin V v)) := fun y => (hσ y).preimage hc
  have hk : IsOpen (((T.frame v).red.ker : Subgroup (Kv V v)) : Set (Kv V v)) := by
    rw [show ((T.frame v).red.ker : Set (Kv V v)) =
        (↑) ⁻¹' (stabLocOne D.sp.cm.sig V.gram (T.frame v).emb (frameLat V) : Set (GLoc D.sp.cm.sig V.gram v)) from
      Set.ext (T.frame v).red_eq_one_iff]
    exact (isOpen_stabLocOne _ (T.frame v).emb _ (T.frame v).cm).preimage continuous_subtype_val
  obtain ⟨-, h2, h3, -⟩ := (typeIdem_projector (μf v) (isOpen_stabLoc _ _ _ v.1) (isCompact_stabLoc _ _ _ v.1)
    (T.frame v).red_surjective hk (T.irred v)).2.1 _ _ hs
  change smoothOp (σ.comp (locFin V v)) (μf v) (typeIdem (μf v) (T.frame v).red (T.τ v)) x = x
  have hle : Submodule.span ℂ {y | ∃ φ : T.W v →ₗ[ℂ] W, (∀ (k : Kv V v) z,
      φ (T.τ v ((T.frame v).red k) z) = σ (locFin V v k) (φ z)) ∧ y ∈ LinearMap.range φ} ≤
      LinearMap.range (smoothOp (σ.comp (locFin V v)) (μf v) (typeIdem (μf v) (T.frame v).red (T.τ v))) := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨φ, hφ, z, rfl⟩
    rw [SetLike.mem_coe, h3]
    exact GlobalTheory.LocGL.apply_mem_isotypic ⟨φ, fun k => LinearMap.ext fun z => hφ k z⟩ z
  obtain ⟨w, rfl⟩ := hle hx
  exact LinearMap.congr_fun h2 w

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryFactorEquivalence
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.UnitaryFromModules

theorem uEquiv_of_isFactor : GlobalTheory.Published.HarishChandraAnalyticity → ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsIrrAdm ε ρ → IsURepOn (UJset ε) ρ → IsIrrAdm ε π → IsURepOn (UJset ε) π → ∀ Z, IsFactor ε ρ Z (kFinVec ε ρ) π → UEquiv ε π ρ := by
  intro hHC n ε H _ _ _ ρ V _ _ _ π hρ hρU hπ hπU Z hF
  obtain ⟨-, hY, -, T, hmap, -, hK, hL⟩ := hF
  haveI : Nontrivial V := hπ.1
  obtain ⟨w, hwK, hw0⟩ := GlobalTheory.T.exists_nonzero_k_finite n ε V π hπU
  have hw : w ∈ (kFinVec ε ρ).map T := hmap ▸ hwK
  obtain ⟨y₀, hy₀, rfl⟩ := hw
  have hTK : ∀ y, IsKFin ε ρ y → IsKFin ε π (T y) := fun y hy =>
    (hmap ▸ Submodule.mem_map_of_mem (f := T) (show y ∈ kFinVec ε ρ from hy) : T y ∈ kFinVec ε π)
  obtain ⟨a₀, ha₀, hrz⟩ := (GlobalTheory.T.intertwiner_of_k_finite_vectors n ε H ρ V π hρ.2.1 hπ.2.1 T hmap
    (fun k hk y hy => hK k hk y hy)).2 (T y₀) hwK
  have hsm := (GlobalTheory.T.irreducible_K_stable_finite_subspace n ε V π hπU hπ.2.2).2
  have hco := GlobalTheory.T.smooth_intertwiner_extension hHC n ε H ρ V π hρ.2.1 hπ.2.1 hY hsm T hTK (fun k hk y hy => hK k hk y hy)
    (fun X hX y hy => hL X hX y hy) a₀ (T y₀) ha₀ hwK hrz
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.T.intertwiner_nonzero_on_generating_set n ε H ρ V π hρU hρ.2.2 hπU T {y | IsKFin ε ρ y} y₀ a₀ hy₀ hw0 hco
  exact GlobalTheory.T.bounded_intertwiner_schur n ε H ρ V π hρU hρ.2.2 hπU hπ.2.2 B hB0 hB

end GlobalTheory.UnitaryFromModules

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTypeLevelFamilyIsOpenLeLatticeStabilizer
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

namespace GlobalTheory.TrIdem

theorem levelFam_open_le : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), U.u ∉ T.S → ∀ v, IsOpen (levelFam T U v : Set (GLoc D.sp.cm.sig V.gram v)) ∧ levelFam T U v ≤ Kv V v := by
  intro D V T U hu v
  by_cases hvu : v = U.u
  · subst hvu
    rw [levelFam_u]
    exact ⟨U.frame.isOpen_iwahori, U.frame.iwahori_le⟩
  by_cases hv : v ∈ T.S
  · have h := levelFam_of_mem T U hu ⟨v, hv⟩
    simp only at h
    rw [h, kerSub]
    refine ⟨?_, Subgroup.map_subtype_le _⟩
    rw [Subgroup.coe_map]
    exact (isOpen_stabLoc _ _ _ v).isOpenMap_subtype_val _ (T.frame ⟨v, hv⟩).isOpen_ker_red
  · rw [levelFam_of_notMem T U hv hvu]
    exact ⟨isOpen_stabLoc _ _ _ v, le_refl _⟩

end GlobalTheory.TrIdem
end

