import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0320
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0325
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0321
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0039
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0278

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCardCosetsDiagonalDoubleCosetGL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FinZeta.TrivCount

theorem trivial_isUnitarisable {G : Type} [Group G] :
    IsUnitarisable (Representation.trivial ℂ G ℂ) := by
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => x * starRingEnd ℂ y)
      (fun _ _ _ => add_mul _ _ _) (fun _ _ _ => by simp [mul_assoc])
      (fun _ _ _ => by simp [mul_add]) (fun _ _ _ => by simp [mul_left_comm]), ?_, ?_, ?_⟩
  · intro v w; simp [mul_comm]
  · intro v hv; simpa [Complex.mul_conj] using hv
  · intro g v w; simp

theorem heckeVec_trivial_dosetInd {G : Type} [Group G] {K : Subgroup G} (hK : IsCommensurated K) (t : G) :
    heckeVec (Representation.trivial ℂ G ℂ) K (dosetInd ℂ K t) 1 =
      ((Nat.card {a : G ⧸ K // a.out ∈ DoubleCoset.doubleCoset t (K : Set G) K} : ℝ) : ℂ) • 1 := by
  classical
  set D := DoubleCoset.doubleCoset t (K : Set G) K
  have hfin : {a : G ⧸ K | a.out ∈ D}.Finite := by
    refine (Formalism.UG.P.finite_support_cosets hK (Formalism.UG.Final.DosetIndMem G K ℂ t).2).subset ?_
    intro a ha
    have h' : a.out ∈ D := ha
    simp only [Set.mem_setOf_eq, dosetInd]
    rw [Set.indicator_of_mem h']
    simp
  have e : (fun c : G ⧸ K => dosetInd ℂ K t c.out • (Representation.trivial ℂ G ℂ) c.out (1 : ℂ)) =
      Set.indicator {a : G ⧸ K | a.out ∈ D} 1 := by
    funext c
    by_cases h : c.out ∈ D <;> simp [dosetInd, D, h, Set.indicator]
  rw [heckeVec, e, ← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hc : Nat.card {a : G ⧸ K // a.out ∈ D} = hfin.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact Nat.card_coe_set_eq {a : G ⧸ K | a.out ∈ D}
  rw [hc]
  simp

theorem hasSum_card_cosets_diag : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ T : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E), (∀ d, (T d).1 = Matrix.diagonal fun i => ϖ ^ d i) → ∃ B₀ : Multiset ℂˣ, (∀ β ∈ B₀, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2)) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℝ, 0 < X → X < δ → HasSum (fun d : {d : Fin r → ℤ // Antitone d} => ((Nat.card {a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r // a.out ∈ DoubleCoset.doubleCoset (T d.1) (KGL w r : Set (GL (Fin r) (w.adicCompletion E))) (KGL w r)} : ℝ) : ℂ) * (X : ℂ) ^ (∑ i, |d.1 i|).toNat) (eulerFac B₀ ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * eulerFac (B₀.map (·⁻¹)) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * (X : ℂ) ^ 2)) := by
  intro hP E _ _ w r ϖ hϖ T hT
  have hK : IsCommensurated (KGL w r) := Formalism.UG.Final.GLintComm E w r
  let ρ := Representation.trivial ℂ (GL (Fin r) (w.adicCompletion E)) ℂ
  have hu : IsUnitarisable ρ := trivial_isUnitarisable
  have hfix : (1 : ℂ) ∈ fixed ρ (KGL w r) := GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl
  have heig : ∀ h ∈ Hecke ℂ (KGL w r), ∃ c : ℂ, heckeVec ρ (KGL w r) h 1 = c • (1 : ℂ) :=
    fun h _ => ⟨heckeVec ρ (KGL w r) h 1, by rw [smul_eq_mul, mul_one]⟩
  obtain ⟨B, hB, hbd⟩ := GlobalTheory.T.exists_satakeParam_trivialBound_unitaryGL E w r ℂ ρ hu 1 one_ne_zero hfix heig
  have hc : ∀ d, heckeVec ρ (KGL w r) (dosetInd ℂ (KGL w r) (T d)) 1 =
      (fun d => ((Nat.card {a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r // a.out ∈
        DoubleCoset.doubleCoset (T d) (KGL w r : Set (GL (Fin r) (w.adicCompletion E))) (KGL w r)} : ℝ) : ℂ)) d
        • (1 : ℂ) := fun d => heckeVec_trivial_dosetInd hK (T d)
  refine ⟨B, hbd, ?_⟩
  have key := GlobalTheory.T.hasSum_heckeEigenvalue_generatingSeries_GL hP E w r ℂ ρ 1 B hB ϖ hϖ T hT _ hc
  beta_reduce at key
  exact key

end GlobalTheory.FinZeta.TrivCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCuspidalMultiplicityTrace
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed

noncomputable section

namespace GlobalTheory.CuspTraceSum

open GlobalTheory.OpTrace GlobalTheory.DiscreteSum ContinuousLinearMap
open scoped InnerProductSpace

theorem hasSum_trace_restrict {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {ι : Type}
    {W : ι → Submodule ℂ K} [hW : ∀ i, CompleteSpace (W i)]
    (hs : IsHilbertSum ℂ (fun i => W i) fun i => (W i).subtypeₗᵢ) {T : K →L[ℂ] K} (hT : IsTraceClass T)
    (hTW : ∀ i, ∀ x ∈ W i, T x ∈ W i) :
    (∀ i, IsTraceClass (T.restrict (hTW i))) ∧ Summable (fun i => ‖trace (T.restrict (hTW i))‖) ∧
      HasSum (fun i => trace (T.restrict (hTW i))) (trace T) := by
  let b : ∀ i, HilbertBasis (stdIndex (W i)) ℂ (W i) := fun i => stdBasis (W i)
  let v : (Σ i, stdIndex (W i)) → K := fun a => (W a.1).subtypeₗᵢ (b a.1 a.2)
  have ho : Orthonormal ℂ v := hs.OrthogonalFamily.orthonormal_sigma_orthonormal fun i => (b i).orthonormal
  have hsp : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    refine eq_zero_of_isHilbertSum hs fun i y hy => ?_
    have h1 := ((b i).hasSum_repr ⟨y, hy⟩).mapL ((innerSL ℂ x).comp (W i).subtypeL)
    have h2 : ∀ j, ((innerSL ℂ x).comp (W i).subtypeL) ((b i).repr ⟨y, hy⟩ j • b i j) = 0 := fun j => by
      have h3 : ⟪v ⟨i, j⟩, x⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal _ _).1 hx _ (Submodule.subset_span ⟨⟨i, j⟩, rfl⟩)
      have h4 : ⟪x, (b i j : K)⟫_ℂ = 0 := inner_eq_zero_symm.1 h3
      simp [inner_smul_right, h4]
    have h5 : ⟪x, y⟫_ℂ = 0 := by
      have := h1.unique (hasSum_zero.congr_fun fun j => (h2 j))
      simpa using this
    exact inner_eq_zero_symm.1 h5
  let e : HilbertBasis (Σ i, stdIndex (W i)) ℂ K := HilbertBasis.mkOfOrthogonalEqBot ho hsp
  have he : ∀ a, e a = v a := fun a => by simp [e]
  have hR : ∀ i, (T.restrict (hTW i)) = (W i).orthogonalProjection ∘L T ∘L (W i).subtypeL := fun i => by
    ext x
    simp [Submodule.orthogonalProjection_mem_subspace_eq_self (K := W i) ⟨_, hTW i x x.2⟩]
  have htc : ∀ i, IsTraceClass (T.restrict (hTW i)) := fun i => by
    rw [hR i]; exact hT.comp_comp _ _
  have hterm : ∀ a : Σ i, stdIndex (W i), ⟪e a, T (e a)⟫_ℂ = ⟪b a.1 a.2, T.restrict (hTW a.1) (b a.1 a.2)⟫_ℂ :=
    fun a => by rw [he]; rfl
  have hsum := hT.hasSum_trace e
  have hnorm := hT.summable_norm e
  simp only [hterm] at hsum hnorm
  refine ⟨htc, ?_, hsum.sigma fun i => (htc i).hasSum_trace (b i)⟩
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) hnorm.sigma
  rw [← ((htc i).hasSum_trace (b i)).tsum_eq]
  exact norm_tsum_le_tsum_norm ((htc i).summable_norm (b i))

end GlobalTheory.CuspTraceSum

namespace GlobalTheory.CuspTraceSum

open GlobalTheory.OpTrace GlobalTheory.DiscreteSum GlobalTheory.AutMult GlobalTheory.AutomorphicL2Unitary MeasureTheory

theorem hasSum_multIn_repTrace {G K : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {ρ : G →* (K →L[ℂ] K)} (hρ : IsUnitaryRep ρ) (hD : IsDiscreteSum ρ) (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] {f : G → ℂ} (hf : Continuous f) (hfs : HasCompactSupport f)
    (hT : IsTraceClass (repOp ρ μ f)) :
    (∀ c : UDual G, multIn c.rep.π ρ ⊤ ≠ 0 → IsTraceClass (repOp c.rep.π μ f)) ∧
      (Summable fun c : UDual G => ‖((multIn c.rep.π ρ ⊤).toNat : ℂ) * repTrace c.rep.π μ f‖) ∧
      HasSum (fun c : UDual G => ((multIn c.rep.π ρ ⊤).toNat : ℂ) * repTrace c.rep.π μ f) (trace (repOp ρ μ f)) := by
  obtain ⟨⟨ι, W, hWi, hs⟩, hfin⟩ := hD
  haveI : ∀ i, CompleteSpace (W i) := fun i => (hWi i).1.completeSpace
  have hR : IsRepOp ρ μ f (repOp ρ μ f) := hρ.isRepOp hf hfs
  have hTW : ∀ i, ∀ x ∈ W i, repOp ρ μ f x ∈ W i := fun i x hx => (hWi i).1.map_mem_of_isRepOp hR hx
  obtain ⟨htc, hsn, hsum⟩ := hasSum_trace_restrict hs hT hTW
  have hrest : ∀ i, repOp (hWi i).1.rep μ f = (repOp ρ μ f).restrict (hTW i) := fun i =>
    ContinuousLinearMap.ext fun x => Subtype.ext (((hWi i).1.coe_repOp_rep hR).2 x)
  let cls : ι → UDual G := fun i => (⟨W i, (hWi i).1.rep, isIrrUnitary_rep hρ (hWi i)⟩ : IrrU G).cl
  have hcls : ∀ c i, cls i = c ↔ IsCopy c.rep.π ρ (W i) := fun c i => by
    conv_lhs => rw [← UDual.cl_rep c]
    rw [IrrU.cl_eq_iff]
    exact ⟨fun h => ⟨(hWi i).1, h.symm⟩, fun ⟨_, h⟩ => h.symm⟩
  have htr : ∀ c i, cls i = c →
      IsTraceClass (repOp c.rep.π μ f) ∧ repTrace c.rep.π μ f = trace ((repOp ρ μ f).restrict (hTW i)) := by
    intro c i hi
    obtain ⟨_, e, he⟩ := (hcls c i).1 hi
    have h2 : IsTraceClass (repOp (hWi i).1.rep μ f) := by rw [hrest]; exact htc i
    obtain ⟨h3, h4⟩ := ((hWi i).1.isUnitaryRep hρ).repTrace_eq_of_equiv c.rep.isIrr.unitary hf hfs
      e.symm.toContinuousLinearEquiv (fun g x => by
        apply e.injective
        rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv, he, LinearIsometryEquiv.apply_symm_apply,
          LinearIsometryEquiv.apply_symm_apply]) h2
    refine ⟨h3, h4.trans ?_⟩
    rw [repTrace, hrest]
  have hmult : ∀ c : UDual G, (cls ⁻¹' {c}).Finite ∧ multIn c.rep.π ρ ⊤ = (cls ⁻¹' {c}).ncard := by
    intro c
    obtain ⟨h1, h2⟩ := multIn_eq_ncard hρ c.rep.isIrr (hfin c.rep) hWi hs
    have e : cls ⁻¹' {c} = {i | IsCopy c.rep.π ρ (W i)} := Set.ext fun i => hcls c i
    rw [e]
    exact ⟨h1, h2⟩
  have hfib : ∀ c : UDual G, ∑' b : ↑(cls ⁻¹' {c}), trace ((repOp ρ μ f).restrict (hTW b)) =
      ((multIn c.rep.π ρ ⊤).toNat : ℂ) * repTrace c.rep.π μ f := by
    intro c
    rw [tsum_congr fun b : ↑(cls ⁻¹' {c}) => (htr c b b.2).2.symm, tsum_const, nsmul_eq_mul, (hmult c).2,
      Cardinal.toNat_natCast, Nat.card_coe_set_eq]
  refine ⟨fun c hc => ?_, ?_, ?_⟩
  · rw [(hmult c).2] at hc
    obtain ⟨i, hi⟩ := Set.nonempty_of_ncard_ne_zero (by exact_mod_cast hc)
    exact (htr c i hi).1
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun c => ?_)
      (hsn.hasSum.tsum_fiberwise cls).summable
    rw [← hfib]
    exact norm_tsum_le_tsum_norm (hsn.subtype _)
  · exact (hsum.tsum_fiberwise cls).congr_fun fun c => (hfib c).symm

end GlobalTheory.CuspTraceSum

namespace GlobalTheory.CuspTraceSum

open GlobalTheory.DiscreteSum

theorem hasSum_mCusp_repTrace : GlobalTheory.Published.CuspTraceClass → ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ f ∈ CcGA V, (∀ c : UDual (GA D V), mCusp V μ c.rep.π ≠ 0 → IsTraceClass (repOp c.rep.π μ f)) ∧ (Summable fun c : UDual (GA D V) => ‖((mCusp V μ c.rep.π).toNat : ℂ) * repTrace c.rep.π μ f‖) ∧ HasSum (fun c : UDual (GA D V) => ((mCusp V μ c.rep.π).toNat : ℂ) * repTrace c.rep.π μ f) (trace (RcuspOp V μ f)) := by
  intro hP D V μ _ _ f hf
  have hfc := continuous_of_mem_ccAd hf
  have h := hasSum_multIn_repTrace (isUnitaryRep_Rcusp V μ)
    (Published.cuspDiscreteDecomposition_of_traceClass hP D V μ) μ hfc.1 hfc.2 (hP D V μ f hf)
  have e : ∀ c : UDual (GA D V), mCusp V μ c.rep.π = multIn c.rep.π (Rcusp V μ) ⊤ := fun c =>
    (multIn_rep (isSubrep_L2cusp V μ)).symm
  simp only [e]
  exact h

end GlobalTheory.CuspTraceSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumNormSphericalZetaKernelUnramifiedUnitary
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ZetaAbsU

theorem hasSum_norm_kerU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q r t : ℕ), IsUnramInv ϖ σ q → r ≤ t → ∀ (z : ℂˣ) (φ : GU σ r → ℂ), ‖(z : ℂ)‖ = 1 → KerU ϖ q (r + t) z φ → ∃ α : Fin (r / 2) → ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α ∧ HasSum (fun a : GU σ r ⧸ KU σ r => ((‖φ a.out‖ : ℝ) : ℂ)) (eulerFac (bcParam r α) (((q : ℂ) ^ (t + 1))⁻¹) * ∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ (r + t))⁻¹)) := by
  intro L _ _ _ ϖ σ q r t hU hrt z φ hz hK
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq0 : q ≠ 0 := by omega
  obtain ⟨-, -, hS⟩ := GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.trivial_hyp hU hq0 r
  obtain ⟨x, hx⟩ := hS.exists_vec
  have bound : GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r (GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.trivParam q r hq0) := by
    intro i
    have hi := i.2
    have h2 : 2 * i.val + 2 ≤ r := by omega
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    have hn : ‖(GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.trivParam q r hq0 i : ℂ)‖ = (q : ℝ) ^ ((r : ℝ) - 1 - 2 * (i.val : ℝ)) := by
      rw [GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.trivParam, Units.val_zpow_eq_zpow_val, norm_zpow, Units.val_mk0, Complex.norm_natCast,
        ← Real.rpow_intCast]
      congr 1
      push_cast
      ring
    have hlow : ((q : ℝ) ^ 2) ^ (-(((r : ℝ) - 1) / 2)) = (q : ℝ) ^ (-((r : ℝ) - 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]
      congr 1
      push_cast
      ring
    rw [hn, hlow, GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.bound_eq]
    have h2' : 2 * (i.val : ℝ) + 2 ≤ r := by exact_mod_cast h2
    have h0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    constructor <;> apply Real.rpow_le_rpow_of_exponent_le hq1 <;> linarith
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.trivParam q r hq0, bound, ?_⟩
  have hKψ : KerU ϖ q (r + t) 1 (fun g => ((‖φ g‖ : ℝ) : ℂ)) := by
    intro d g hg k₁ hk₁ k₂ hk₂
    simp only
    rw [hK d g hg k₁ hk₁ k₂ hk₂]
    simp [norm_zpow, hz]
  have h := GlobalTheory.T.hasSum_unramifiedZetaSum_unitary_inert L ϖ σ q r t hU hrt 1 _ (by simp) hKψ ℂ (GlobalTheory.LGrp.charRep 1) x _ hx bound LinearMap.id
    ⟨‖x‖, fun g => by simp⟩
  have hx0 : x ≠ 0 := hx.1
  have h' := h.mul_right x⁻¹
  simpa [mul_assoc, mul_inv_cancel₀ hx0] using h'

end GlobalTheory.ZetaAbsU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeOperatorConvolutionAndLeftTranslate
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

open scoped Pointwise

namespace GlobalTheory.OpConv

theorem isIntegralOp_conv_and_translate : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W), GlobalTheory.PRep.IsSmooth σ → ∀ f ∈ GlobalTheory.SplitWeil.SB G, ∀ f' ∈ GlobalTheory.SplitWeil.SB G, ∀ A B, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ f A → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ f' B → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ (conv μ f f') (A ∘ₗ B) ∧ ∀ g : G, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ (fun x => f' (g⁻¹ * x)) (σ g ∘ₗ B) := by
  intro G _ _ _ _ _ _ μ _ W _ _ σ hσ f hf f' hf' A B hA hB
  have hfc : Continuous f := hf.1.continuous
  have hf'c : Continuous f' := hf'.1.continuous
  have horb : ∀ (l : Module.Dual ℂ W) (v : W), Continuous fun y => l (σ y v) := fun l v =>
    ((hσ.isLocallyConstant_orbit v).comp l).continuous
  refine ⟨fun v l => ?_, fun g v l => ?_⟩
  ·
    have h0 : ∀ x y : G, (x, y) ∉ tsupport f ×ˢ (tsupport f * tsupport f') →
        f x * f' (x⁻¹ * y) = 0 := by
      intro x y h
      by_contra hne
      have h1 := subset_tsupport f (left_ne_zero_of_mul hne)
      have h2 := subset_tsupport f' (right_ne_zero_of_mul hne)
      exact h ⟨h1, x, h1, _, h2, by simp⟩
    have hK : IsCompact (tsupport f ×ˢ (tsupport f * tsupport f')) := hf.2.prod (hf.2.mul hf'.2)
    have hcont : Continuous fun y => ∫ x, f x * f' (x⁻¹ * y) ∂μ := by
      refine continuousOn_univ.1 (continuousOn_integral_of_compact_support
        (f := fun y x => f x * f' (x⁻¹ * y)) (s := Set.univ) hf.2 ?_ fun y x _ hx => ?_)
      · exact ((hfc.comp continuous_snd).mul
          (hf'c.comp (continuous_snd.inv.mul continuous_fst))).continuousOn
      · simp [image_eq_zero_of_notMem_tsupport hx]
    have hcs : HasCompactSupport fun y => ∫ x, f x * f' (x⁻¹ * y) ∂μ :=
      HasCompactSupport.intro (hf.2.mul hf'.2) fun y hy => by
        simp [fun x => h0 x y fun h => hy h.2]
    have hF : Continuous (Function.uncurry fun x y : G => f x * f' (x⁻¹ * y) * l (σ y v)) :=
      ((hfc.comp continuous_fst).mul (hf'c.comp (continuous_fst.inv.mul continuous_snd))).mul
        ((horb l v).comp continuous_snd)
    have hFc : HasCompactSupport (Function.uncurry fun x y : G => f x * f' (x⁻¹ * y) * l (σ y v)) :=
      HasCompactSupport.intro hK fun p hp => by simp [Function.uncurry, h0 p.1 p.2 hp]
    have hconv : conv μ f f' = fun y => ∫ x, f x * f' (x⁻¹ * y) ∂μ := rfl
    rw [hconv]
    refine ⟨(hcont.mul (horb l v)).integrable_of_hasCompactSupport (hcs.mul_right), ?_⟩
    have hx : ∀ x, l (σ x (B v)) = ∫ y, f' (x⁻¹ * y) * l (σ y v) ∂μ := by
      intro x
      have := (hB v (l ∘ₗ σ x)).2
      simp only [LinearMap.comp_apply] at this
      rw [this, ← integral_mul_left_eq_self (fun y => f' (x⁻¹ * y) * l (σ y v)) x]
      refine integral_congr_ae (.of_forall fun y => ?_)
      simp [map_mul, Module.End.mul_apply]
    rw [LinearMap.comp_apply, (hA (B v) l).2]
    simp_rw [hx, ← integral_const_mul, ← mul_assoc]
    rw [integral_integral_swap_of_hasCompactSupport hF hFc]
    simp_rw [integral_mul_const]
  ·
    have hx : ∀ y, f' y * l (σ g (σ y v)) = (fun x => f' (g⁻¹ * x) * l (σ x v)) (g * y) := by
      intro y
      simp [map_mul, Module.End.mul_apply]
    have hc : Continuous fun x => f' (g⁻¹ * x) * l (σ x v) :=
      (hf'c.comp (continuous_const.mul continuous_id)).mul (horb l v)
    have hs : HasCompactSupport fun x => f' (g⁻¹ * x) * l (σ x v) :=
      ((hf'.2.comp_homeomorph (Homeomorph.mulLeft g⁻¹))).mul_right
    refine ⟨hc.integrable_of_hasCompactSupport hs, ?_⟩
    have := (hB v (l ∘ₗ σ g)).2
    simp only [LinearMap.comp_apply] at this
    rw [LinearMap.comp_apply, this,
      ← integral_mul_left_eq_self (fun x => f' (g⁻¹ * x) * l (σ x v)) g]
    exact integral_congr_ae (.of_forall fun y => hx y)

end GlobalTheory.OpConv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCompressionRealPlaceFockVacuaScalarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_compression_real_place_fock_vacua_scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsInfFam θ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (τ : D.what₂.Tau) (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ), IsCartanInv (gramAt D S τ) sS → IsCartanInv (gramAt D T τ) sT → ∀ w : WO S T, ∃ γ : ℂ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) g → ipO μ 𝓕 g (heisO ψ S T (wAt (.inr τ) w) f) = γ * ipO μ 𝓕 g f := by
  first | exact @GlobalTheory.VacCompress.compress | exact GlobalTheory.VacCompress.compress | (intros; apply GlobalTheory.VacCompress.compress <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorPureTensorPlaceByPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → ∀ w : WO S T, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun p => heisO ψ S T (wAt p w) (x p)) (heisO ψ S T w f) := by
  first | exact @GlobalTheory.PlaceTensorHeis.isPure_heisO | exact GlobalTheory.PlaceTensorHeis.isPure_heisO | (intros; apply GlobalTheory.PlaceTensorHeis.isPure_heisO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HilbertTensorTraceClassHasTraceProdStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertTensor_traceClass_hasTrace_prod : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] [∀ i, CompleteSpace (Hs i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Φ Φ' : ContinuousMultilinearMap ℂ Hs H) (κ κ' : ℂ), (∀ y y', inner ℂ (Φ y') (Φ y) = ∏ i, inner ℂ (y' i) (y i)) → (∀ y y', inner ℂ (Φ y') (Φ' y) = κ * ∏ i, inner ℂ (y' i) (y i)) → (∀ y y', inner ℂ (Φ' y') (Φ' y) = κ' * ∏ i, inner ℂ (y' i) (y i)) → ∀ (B : ∀ i, Hs i →L[ℂ] Hs i) (b : ι → ℂ), (∀ i, HasTrace (B i) (b i)) → ∀ X : H →L[ℂ] H, (∀ y, X (Φ y) = Φ' fun i => B i (y i)) → (∀ v, (∀ y, inner ℂ (Φ y) v = 0) → X v = 0) → HasTrace X (κ * ∏ i, b i) := by
  first | exact @GlobalTheory.tensorTrace_hasTrace | exact GlobalTheory.tensorTrace_hasTrace | (intros; apply GlobalTheory.tensorTrace_hasTrace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePartActDiscreteSeriesHomFactorwise
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.TrAct

open Classical in

noncomputable def partAt {D : D7} (V : HSp D) (g : GA D V) (s : Finset D.what₂.Tau) : GA D V :=
  ofInf D.sp.cm.sig V.gram (embArchPi D.sp.cm.sig V.gram fun w =>
    if w ∈ s.image (placeOf D) then projArch D.sp.cm.sig V.gram w g else 1)

open Classical in
theorem projArch_partAt {D : D7} (V : HSp D) (g : GA D V) (s : Finset D.what₂.Tau) (w : InfinitePlace D.host.F) :
    projArch D.sp.cm.sig V.gram w (partAt V g s) =
      if w ∈ s.image (placeOf D) then projArch D.sp.cm.sig V.gram w g else 1 := by
  rw [partAt, projArch_ofInf, projInfArch_embArchPi]

theorem proj_partAt {D : D7} (V : HSp D) (g : GA D V) (s : Finset D.what₂.Tau) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    proj D.sp.cm.sig V.gram v (partAt V g s) = 1 := by
  rw [partAt, proj_ofInf]

open Classical in
theorem partAt_insert {D : D7} (V : HSp D) (g : GA D V) {s : Finset D.what₂.Tau} {τ : D.what₂.Tau} (hτ : τ ∉ s) :
    partAt V g (insert τ s) =
      embW V (placeOf D τ) (projArch D.sp.cm.sig V.gram (placeOf D τ) g) * partAt V g s := by
  refine GAd_ext D.sp.cm.sig V.gram (fun w => ?_) (fun v => ?_)
  · rw [map_mul, projArch_partAt, projArch_partAt]
    by_cases hw : w = placeOf D τ
    · subst hw
      have h1 : placeOf D τ ∈ (insert τ s).image (placeOf D) := Finset.mem_image_of_mem _ (Finset.mem_insert_self τ s)
      have h2 : placeOf D τ ∉ s.image (placeOf D) := fun h => by
        obtain ⟨ρ, hρ, e⟩ := Finset.mem_image.1 h
        exact hτ ((placeOf_bijective D).1 e ▸ hρ)
      rw [if_pos h1, if_neg h2, mul_one]
      exact (projArch_embArch_self _ _ _ _).symm
    · rw [projArch_embArch_ne _ _ hw, one_mul]
      congr 1
      simp only [Finset.image_insert, Finset.mem_insert, hw, false_or]
  · rw [map_mul, proj_partAt, proj_partAt, proj_embArch, one_mul]

theorem partAt_univ {D : D7} (V : HSp D) (g : GA D V) [Fintype D.what₂.Tau] :
    partAt V g Finset.univ = (toInf V g : GA D V) := by
  classical
  refine GAd_ext D.sp.cm.sig V.gram (fun w => ?_) (fun v => ?_)
  · rw [projArch_partAt, if_pos]
    · show _ = projArch D.sp.cm.sig V.gram w (ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g))
      rw [projArch_ofInf, projInfArch_projInf]
    · obtain ⟨τ, rfl⟩ := (placeOf_bijective D).2 w
      exact Finset.mem_image_of_mem _ (Finset.mem_univ τ)
  · rw [proj_partAt]
    show _ = proj D.sp.cm.sig V.gram v (ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g))
    rw [proj_ofInf]

end GlobalTheory.TrAct

open GlobalTheory.TrAct in

theorem GlobalTheory.TrAct.toInf_apply_homDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : GA D V →* (H →L[ℂ] H)) (U : Submodule ℂ H), ∀ Φ ∈ homDS M ρ U, ∀ (g : GA D V) y, ρ (toInf V g : GA D V) (Φ y) = Φ fun τ => dsRep M τ (projArch D.sp.cm.sig V.gram (placeOf D τ) g) (y τ) := by
  intro D V S M H _ _ _ ρ U Φ hΦ g y
  classical
  haveI : Finite D.what₂.Tau := Finite.of_injective _ (placeOf_bijective D).1
  haveI : Fintype D.what₂.Tau := Fintype.ofFinite _
  have key : ∀ s : Finset D.what₂.Tau, ρ (partAt V g s) (Φ y) = Φ fun τ =>
      if τ ∈ s then dsRep M τ (projArch D.sp.cm.sig V.gram (placeOf D τ) g) (y τ) else y τ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : partAt V g ∅ = 1 := by
        rw [partAt]
        have : (fun w => if w ∈ (∅ : Finset D.what₂.Tau).image (placeOf D) then
            projArch D.sp.cm.sig V.gram w g else (1 : GArch D.sp.cm.sig V.gram w)) = 1 := by
          funext w; simp
        rw [this, map_one, map_one]
      simp [this]
    | insert τ s hτ ih =>
      rw [partAt_insert V g hτ, map_mul, ContinuousLinearMap.mul_apply, ih, ← (mem_homPi.1 hΦ).2 τ]
      congr 1
      funext τ'
      by_cases e : τ' = τ
      · subst e
        simp [hτ]
      · rw [Function.update_of_ne e]
        simp [e]
  have := key Finset.univ
  rw [partAt_univ] at this
  simpa using this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralHomFundamentalDomainIsotropicSplitCoordsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_hom_fundamental_domain_isotropic_split_coords : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∃ κ : ℝ, 0 < κ ∧ (∀ H : WO V W → ℂ, Continuous H → (∃ b : ℝ, ∀ w, ‖H w‖ ≤ b) → (∀ γ ∈ ratL W V, ∀ w, H (γ + w) = H w) → ∫ w in 𝓕V, H w ∂μV = κ • ∫ t in 𝓨, ∫ y in 𝓨, ∫ x in 𝓕', H (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∂μ' ∂μ ∂μ) := by
  first | exact @GlobalTheory.TwistHaar.integral_fundamentalDomain_eq_iterated | exact GlobalTheory.TwistHaar.integral_fundamentalDomain_eq_iterated | (intros; apply GlobalTheory.TwistHaar.integral_fundamentalDomain_eq_iterated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLeviPhaseChangeOfVariablesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_levi_phase_change_of_variables : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W : HSp D) (r : ℕ) (μ : Measure (Mx D W.rank r)), μ.IsAddHaarMeasure → ∀ (h : GA D W), GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det (matHom W h)) = 1 → ∀ (a : GL (Fin r) (AE D)) (N : Mx D W.rank r → ℂ), Continuous N → Integrable N μ → Integrable (fun u : Mx D W.rank r => N (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val)) μ ∧ ∀ y : Mx D W.rank r, ∫ u, GlobalTheory.LeviNorm.phase ψ W (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) y) (GlobalTheory.MixModel.adj (a⁻¹).val)) u * N u ∂μ = ((GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ℝ) : ℂ) ^ W.rank * ∫ u, GlobalTheory.LeviNorm.phase ψ W y u * N (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) u) a.val) ∂μ := by
  first | exact @GlobalTheory.LeviNorm.integral_phase_sandwich | exact GlobalTheory.LeviNorm.integral_phase_sandwich | (intros; apply GlobalTheory.LeviNorm.integral_phase_sandwich <;> assumption)
end

