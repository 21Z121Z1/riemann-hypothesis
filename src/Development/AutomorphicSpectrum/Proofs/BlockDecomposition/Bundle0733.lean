import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0611
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0591
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0730
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0594
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0600
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0650
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0729
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0006
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0723
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnitScalingSelfdualHermMeasures
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SelfDualTransport
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDensityOfImmersion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0391
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftSideFormula
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0557
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinUnfoldingSecondTerm
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold

theorem unfold2 : Unfold2 := by
  intro D ψ hψ θ hθ V n r hrn μ 𝓕 hμ μr h𝓕r c a hca b Φ hΦ
  obtain ⟨𝓕r, hμr⟩ := h𝓕r
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hrn
  obtain ⟨μs, 𝓕s, hμs⟩ := exists_isCovolOne D V.rank s
  obtain ⟨hΦc, B, hB⟩ := GlobalTheory.T.schwartz_lattice_sum_bounded D θ hθ V.rank (r + s) Φ hΦ
  have ha : IsUnit a.det := hca.1

  let e : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E ≃
      Matrix (Fin V.rank) (Fin (r + s)) D.host.E :=
    joinEquiv.trans
      { toFun := fun ξ => ξ * a
        invFun := fun ξ => ξ * a⁻¹
        left_inv := fun ξ => Matrix.mul_nonsing_inv_cancel_right a ξ ha
        right_inv := fun ξ => Matrix.nonsing_inv_mul_cancel_right a ξ ha }
  set T : Mx D V.rank (r + s) → ℂ := fun y => ∑' ξ : Matrix (Fin V.rank) (Fin (r + s)) D.host.E,
    Heisenberg₂ ψ V (HMul.hMul (zy y) ((repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b.1 a).map (incA D))) Φ
      (ξ.map (incA D)) with hT
  have hform : ∀ y₁ y₂, T (colJoin y₁ y₂) =
      ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b.1 a Φ pq.1 pq.2 y₁ y₂ := by
    intro y₁ y₂
    obtain ⟨hx, hy⟩ := GlobalTheory.T.weil_action_block_matrix_components D V.rank r s b.1 a y₁ y₂
    rw [hT]
    dsimp only
    rw [← e.tsum_eq]
    exact tsum_congr fun pq => GlobalTheory.T.block_weil_action_theta_unfolding D ψ hψ V r s b.1 b.2 a ha Φ y₁ y₂ _ hx hy pq.1 pq.2
  have hper : ∀ γ ∈ ratMx D V.rank (r + s), ∀ y, T (γ + y) = T y := by
    intro γ hγ y
    obtain ⟨g, rfl⟩ := mem_ratMx.1 hγ
    rw [← colJoin_colL_colR g, ← colJoin_colL_colR y, rat_colJoin, ← colJoin_add, hform, hform,
      add_comm (rat (colL g)), add_comm (rat (colR g))]
    exact GlobalTheory.T.lattice_sum_shift_invariant D ψ hψ V r s b.1 a Φ (colL g) (colR g) (colL y) (colR y)
  have hE := GlobalTheory.T.covolume_one_column_join_product D V.rank r s μr 𝓕r μs 𝓕s hμr hμs
  show ∫ y in 𝓕, T y ∂μ = _
  rw [covolOne_integral_eq hE hμ T hper]
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D V.rank r
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D V.rank s
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := lattice_Mx D V.rank (r + s)
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D V.rank s) := ⟨rfl⟩
  haveI : BorelSpace (Mx D V.rank (r + s)) := ⟨rfl⟩
  have hc : Continuous fun z : Mx D V.rank r × Mx D V.rank s => colJoin z.1 z.2 := by
    refine continuous_matrix fun i k => ?_
    simp only [colJoin, Matrix.of_apply]
    rcases finSumFinEquiv.symm k with j | j
    · exact (continuous_apply_apply i j).comp continuous_fst
    · exact (continuous_apply_apply i j).comp continuous_snd
  have hc' : Continuous fun y : Mx D V.rank (r + s) => ((colL y, colR y) : Mx D V.rank r × Mx D V.rank s) := by
    refine Continuous.prodMk (continuous_matrix fun i j => ?_) (continuous_matrix fun i j => ?_)
    · exact continuous_apply_apply i (Fin.castAdd s j)
    · exact continuous_apply_apply i (Fin.natAdd r j)
  let hj : (Mx D V.rank r × Mx D V.rank s) ≃ₜ Mx D V.rank (r + s) :=
    { (joinEquiv : (Mx D V.rank r × Mx D V.rank s) ≃ Mx D V.rank (r + s)) with
      continuous_toFun := hc
      continuous_invFun := hc' }
  have hmp : MeasurePreserving hj.toMeasurableEquiv (μr.prod μs)
      ((μr.prod μs).map fun z => colJoin z.1 z.2) := ⟨hj.toMeasurableEquiv.measurable, rfl⟩
  have h1 := hmp.setIntegral_image_emb hj.toMeasurableEquiv.measurableEmbedding T (𝓕r ×ˢ 𝓕s)
  erw [h1]
  have h2 : ∀ z : Mx D V.rank r × Mx D V.rank s, T (hj.toMeasurableEquiv z) =
      ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b.1 a Φ pq.1 pq.2 z.1 z.2 := fun z => hform z.1 z.2
  simp only [h2]
  rw [GlobalTheory.T.eisenstein_coefficient_block_unfolding D ψ hψ V r s μr 𝓕r μs 𝓕s hμr hμs b.1 a ha Φ hΦc B hB]
  exact GlobalTheory.T.eisenstein_hermitian_integral_unfolding D ψ V r s μr 𝓕r hμr c a hca b Φ

end GlobalTheory.CompanionTheory.EisUnfold

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSumFiberDecompositionStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_sum_fiber_decomposition : ∀ {Γ H : Type} [Group Γ] [Group H] (p : Γ →* H) (e : H →* Γ) (hpe : ∀ m, p (e m) = m)
    (L : Subgroup Γ) (V : Subgroup H) (hLV : ∀ u ∈ L, p u ∈ V) (φ : Γ → ℂ)
    (hφ : ∀ u ∈ L, ∀ x, φ (x * u) = φ x) (hfin : {q : Γ ⧸ L | φ q.out ≠ 0}.Finite),
    ∑ᶠ q : Γ ⧸ L, φ q.out =
      ∑ᶠ m : H ⧸ V, ∑ᶠ q : Γ ⧸ L, (V : Set H).indicator (1 : H → ℂ) (p q.out) * φ (e m.out * q.out) := by
  first | exact @GlobalTheory.CompanionTheory.FinActS.SumFiber.finsum_cosets_retraction | exact GlobalTheory.CompanionTheory.FinActS.SumFiber.finsum_cosets_retraction | (intros; apply GlobalTheory.CompanionTheory.FinActS.SumFiber.finsum_cosets_retraction <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTestFunctionProductStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_test_function_product : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂)
    (y : Hf E a b), finFn S φ₁ φ₂ y = ∏ᶠ i : Slot S, sf φ₁ φ₂ i (i.cp a b y) := by
  first | exact @GlobalTheory.CompanionTheory.FinActS.finFn_eq_finprod_factor | exact GlobalTheory.CompanionTheory.FinActS.finFn_eq_finprod_factor | (intros; apply GlobalTheory.CompanionTheory.FinActS.finFn_eq_finprod_factor <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCovolumeFormula
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HermSd
open scoped TensorProduct ENNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HermCov

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def ratVec {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) [FiniteDimensional F E]
    (A : Matrix (Fin n) (Fin n) E) : Idx n d → F :=
  Sum.elim (fun a => 1 / 2 * Algebra.trace F E (A a a)) fun q => b.repr (A q.1.1.1 q.1.1.2) q.2

def ofVec (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) (k : Idx n d → F) :
    Matrix (Fin n) (Fin n) E := fun a c =>
  if h : a < c then ∑ l, k (Sum.inr (⟨(a, c), h⟩, l)) • b l
  else if h' : c < a then σ (∑ l, k (Sum.inr (⟨(c, a), h'⟩, l)) • b l)
  else algebraMap F E (k (Sum.inl a))

theorem ofVec_herm {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (n : ℕ) (k : Idx n d → F) (a c : Fin n) : σ (ofVec σ b n k c a) = ofVec σ b n k a c := by
  rcases lt_trichotomy a c with h | h | h
  · simp only [ofVec, dif_pos h, dif_neg (not_lt_of_gt h), hinv]
  · subst h
    simp only [ofVec, lt_irrefl, dite_false, AlgHom.commutes]
  · simp only [ofVec, dif_pos h, dif_neg (not_lt_of_gt h)]

theorem ratVec_ofVec [FiniteDimensional F E] [CharZero F] (h2 : Module.finrank F E = 2)
    (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) (k : Idx n d → F) :
    ratVec b n (ofVec σ b n k) = k := by
  funext i
  cases i with
  | inl a =>
    simp only [ratVec, Sum.elim_inl, ofVec, lt_irrefl, dite_false, Algebra.trace_algebraMap, h2]
    simp
  | inr q =>
    obtain ⟨p, l⟩ := q
    simp only [ratVec, Sum.elim_inr, ofVec, dif_pos p.2]
    rw [b.repr_sum_self]

variable (R : Type) [CommRing R] [Algebra F R]

theorem repr_inclR {d : ℕ} (b : Module.Basis (Fin d) F E) (x : E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (inclR R x) k = algebraMap F R (b.repr x k) := by
  change (Algebra.TensorProduct.basis R b).repr ((1 : R) ⊗ₜ[F] x) k = _
  rw [Algebra.TensorProduct.basis_repr_tmul]
  simp

variable [TopologicalSpace R]

theorem hermVec_map [FiniteDimensional F E] (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) E) (S : HermR R σ n)
    (hS : (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = A.map (inclR R)) (i : Idx n d) :
    hermVec R σ b n S i = algebraMap F R (ratVec b n A i) := by
  cases i with
  | inl a =>
    simp only [hermVec, toVec, HaarCoord.hermCoord, Sum.elim_inl, ratVec, hS, Matrix.map_apply]
    change _ * Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] A a a) = _
    rw [trace_tmul, one_mul, map_mul]
  | inr q =>
    simp only [hermVec, toVec, HaarCoord.hermCoord, Sum.elim_inr, ratVec, hS, Matrix.map_apply]
    exact repr_inclR R b _ _

end Alg

section Main

open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth PositivityTheory.SiegelWeilFormula.KWhit.MeasP
attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_ratHerm_iff {σ : E →ₐ[F] E} (hinv : ∀ x, σ (σ x) = x) (h2 : Module.finrank F E = 2)
    [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ)
    (hinj : Function.Injective (hermVec (AF F) σ b n)) (S : HermR (AF F) σ n) :
    S ∈ ratHerm F E σ n ↔ ∃ k : Idx n d → F, ∀ i, hermVec (AF F) σ b n S i = algebraMap F (AF F) (k i) := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨ratVec b n A, hermVec_map (AF F) σ b n A S hA.symm⟩
  · rintro ⟨k, hk⟩
    have hmem : (ofVec σ b n k).map (inclR (AF F)) ∈ HermR (AF F) σ n := by
      intro a c
      simp only [Matrix.map_apply]
      rw [← ofVec_herm hinv b n k a c]
      change sigR (AF F) σ ((1 : AF F) ⊗ₜ[F] _) = (1 : AF F) ⊗ₜ[F] _
      rw [HaarCoord.sigR_tmul]
    have hT : (⟨_, hmem⟩ : HermR (AF F) σ n) = S := by
      apply hinj
      funext i
      rw [hermVec_map (AF F) σ b n (ofVec σ b n k) _ rfl i, ratVec_ofVec h2, hk]
    refine ⟨ofVec σ b n k, ?_⟩
    rw [← hT]
    rfl

theorem existsUnique_sub_mem_pi {ι : Type} (x : ι → AF F) :
    ∃! k : ι → F, (fun i => x i - algebraMap F (AF F) (k i)) ∈
      Set.univ.pi fun _ : ι => fundamentalSet F := by
  choose k hk huniq using fun i => existsUnique_sub_mem_fundamentalSet F (x i)
  refine ⟨k, fun i _ => hk i, fun k' hk' => funext fun i => huniq i _ (hk' i (Set.mem_univ i))⟩

theorem hermCovol : HermCovol := by
  intro F E _ _ _ _ _ σ hCM ψ hψ n ν hν
  obtain ⟨hinv, δ, hδ, hσδ⟩ := HaarCoord.conj_facts hCM
  have h2 := hCM.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h2]; omega)
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E h2
  let e := (hermVec_isHomeomorph hCM (AF F) b n).homeomorph _
  have he : ∀ S, e S = hermVec (AF F) σ b n S := fun _ => rfl
  obtain ⟨ξ, hξ⟩ := GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ hψ.1 hψ.2.2.1
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hψ.2.2.2
    apply hx
    rw [hξ x, map_zero, zero_mul, AddChar.map_zero_eq_one]
    simp
  have hs : (ξ • formB σ b n).IsSymm := (formB_isSymm hinv b n).smul ξ
  have hdet : (ξ • formB σ b n).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hξ0) (formB_det hinv b n)
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (HermR (AF F) σ n) := inferInstance
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  have hsd : ν.map e = adeleMeasurePi F := by
    refine GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth.selfDual_eq _ hs hdet _
      (GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth.selfDual_transport e ?_ _ _ ?_ ν hν)
    · intro x y
      exact hermVec_add (AF F) b n x y
    · intro S T
      have h3 : (ξ • formB σ b n).map (algebraMap F (AF F)) =
          algebraMap F (AF F) ξ • (formB σ b n).map (algebraMap F (AF F)) := by
        ext p q
        exact map_mul (algebraMap F (AF F)) ξ (formB σ b n p q)
      rw [hξ, pair_eq (AF F) hinv h2 hδ hσδ b n S T, chiG, h3, Matrix.smul_mulVec, dotProduct_smul,
        smul_eq_mul]
      rfl
  set D : Set (Idx n 2 → AF F) := Set.univ.pi fun _ => fundamentalSet F with hD
  have hDm : MeasurableSet D := MeasurableSet.univ_pi fun _ => measurableSet_fundamentalSet F
  have hinj : Function.Injective (hermVec (AF F) σ b n) := e.injective
  refine ⟨e ⁻¹' D, IsAddFundamentalDomain.mk' (hDm.preimage e.measurable).nullMeasurableSet ?_, ?_⟩
  · intro S
    obtain ⟨k, hk, huniq⟩ := existsUnique_sub_mem_pi (e S)
    have hg : e.symm (fun i => algebraMap F (AF F) (-k i)) ∈ ratHerm F E σ n :=
      (mem_ratHerm_iff hinv h2 b n hinj _).2 ⟨fun i => -k i, fun i => by
        rw [← he, e.apply_symm_apply]⟩
    refine ⟨⟨_, hg⟩, ?_, ?_⟩
    · change e (e.symm _ + S) ∈ D
      rw [he, hermVec_add, ← he, ← he, e.apply_symm_apply]
      convert hk using 2 with i
      simp [sub_eq_add_neg, add_comm]
    · rintro ⟨g, hgm⟩ hg'
      obtain ⟨k', hk'⟩ := (mem_ratHerm_iff hinv h2 b n hinj _).1 hgm
      change e (g + S) ∈ D at hg'
      rw [he, hermVec_add, ← he] at hg'
      have hkk : (fun i => -k' i) = k := huniq _ (by
        convert hg' using 2 with i
        simp [he, hk', sub_eq_add_neg, add_comm])
      refine Subtype.ext (e.injective ?_)
      rw [e.apply_symm_apply]
      funext i
      rw [he, hk', ← hkk]
      simp
  · rw [← Measure.map_apply e.measurable hDm, hsd, adeleMeasurePi, hD, Measure.pi_pi]
    simp [adeleMeasure_fundamentalSet]

end Main

end GlobalTheory.CompanionTheory.SW.HermCov
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfimumOfEqualityStatement
section
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infimum_of_equality : GlobalTheory.CompanionTheory.EGlue.InfOfEq := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.infOfEq_holds | exact GlobalTheory.CompanionTheory.EGlue.infOfEq_holds | (intros; apply GlobalTheory.CompanionTheory.EGlue.infOfEq_holds <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JBConjTranspose
section
noncomputable section

open Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary GlobalTheory.LinRed
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.GLK

open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

variable {n : ℕ} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

def jB (A : Mat n) (c : ℂ) : Mat (n + 1) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 (c • (1 : Matrix (Fin 1) (Fin 1) ℂ)))

def rB (m : Mat (n + 1)) : Mat n := m.submatrix Fin.castSucc Fin.castSucc

def cB (m : Mat (n + 1)) : ℂ := m (Fin.last n) (Fin.last n)

theorem jB_mul (A B : Mat n) (c d : ℂ) : jB A c * jB B d = jB (A * B) (c * d) := by
  simp only [jB, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
  congr 1
  simp [smul_smul, mul_comm]

theorem jB_one : jB (1 : Mat n) 1 = 1 := by
  simp [jB, Matrix.fromBlocks_one]

theorem jB_add (A B : Mat n) (c d : ℂ) : jB (A + B) (c + d) = jB A c + jB B d := by
  have h := (Matrix.reindexLinearEquiv ℂ ℂ (finSumFinEquiv (m := n) (n := 1)) finSumFinEquiv).map_add
    (fromBlocks A 0 0 (c • (1 : Matrix (Fin 1) (Fin 1) ℂ))) (fromBlocks B 0 0 (d • (1 : Matrix (Fin 1) (Fin 1) ℂ)))
  simp only [Matrix.coe_reindexLinearEquiv, fromBlocks_add, add_zero, ← add_smul] at h
  exact h

def gp (n : ℕ) : Set (Mat (n + 1)) := {m | jB (rB m) (cB m) = m ∧ m.det = 1}

def sg (π : G n →* (U →L[ℂ] U)) (m : Mat (n + 1)) : U →L[ℂ] U := piM π (rB m)

def lift (X : Mat n) : Mat (n + 1) := jB X (-X.trace)

def jR : (Mat n × ℂ) →+* Mat (n + 1) where
  toFun x := jB x.1 x.2
  map_one' := jB_one
  map_mul' x y := (jB_mul x.1 y.1 x.2 y.2).symm
  map_zero' := by simp [jB]
  map_add' x y := jB_add x.1 y.1 x.2 y.2

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

end

end GlobalTheory.CompanionTheory.GLK

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProductStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_cuspidal_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {l c N : ℕ} (x : Fin l → IrrGL k) (y : Fin c → IrrGL k) (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N) (hxc : ∀ a, (x a).IsCusp) (hyc : ∀ a, (y a).IsCusp), jm y hy (prodIrr x hx) = (Set.ncard {e : Fin c ≃ Fin l | ∀ a, y a = x (e a)} : ℕ∞) := by
  first | exact @GlobalTheory.CompanionTheory.CuspJm.main | exact GlobalTheory.CompanionTheory.CuspJm.main | (intros; apply GlobalTheory.CompanionTheory.CuspJm.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeStabilizerVolumeAlmostAllStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_stabilizer_volume_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam : Measure (Fv F v), IsStdV v lam → ∀ (m : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (g : HA (Fv F v) σ (hypOne J)), latStab σ (hypOne J) b v g → stageInt (Fv F v) σ J b lam m ((latV b v).indicator 1) g = m (latV b v) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Stab.stageInt_latStab | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Stab.stageInt_latStab | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Stab.stageInt_latStab <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftSideFormulaStatement
section
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.left_side_formula : Equi → CoCpt → LSide := by
  first | exact @GlobalTheory.CompanionTheory.SW.LS.lside | exact GlobalTheory.CompanionTheory.SW.LS.lside | (intros; apply GlobalTheory.CompanionTheory.SW.LS.lside <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieDerivativeConvolutionKernel
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GroundTheory.Automorphic

noncomputable section

namespace GlobalTheory.CompanionTheory.LieConv

theorem mMap_surjective (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) :
    Function.Surjective (GlobalTheory.CompanionTheory.ArchSmooth.mMap E a) := fun X =>
  ⟨(fun i j => ((0, fun w => X i j w.1) : mixedEmbedding.mixedSpace E) :
    Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace E)), rfl⟩

theorem exists_kernel_basis (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)]
    (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure] (φ : Sm E a) (hφ : IsAutForm φ)
    (j : Fin (CuspidalSpectrum.archDim E a)) :
    ∃ D : AutomorphicForm.archGroup E a → ℂ, Continuous D ∧ HasCompactSupport D ∧ ∀ g : GA E a,
      (lie E a (GlobalTheory.CompanionTheory.ArchSmooth.mMap E a (CuspidalSpectrum.archBasis E a j)) φ).1 g =
        ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * D y ∂ν := by
  obtain ⟨D, hD, hDc, h⟩ := GlobalTheory.CompanionTheory.HCRep.uJ_eq_conv E a φ (GlobalTheory.CompanionTheory.ArchSmooth.sm_mem_archSmooth E a φ) hφ ν 1
    (fun _ => j)
  refine ⟨D, hD, hDc, fun g => ?_⟩
  rw [← h g, CuspidalSpectrum.uAction_uJ_succ]
  have e := GlobalTheory.CompanionTheory.HCRep.smL_liB (E := E) (a := a) (CuspidalSpectrum.lieOf (CuspidalSpectrum.archBasis E a j)) φ
  have e2 := congrArg (fun ψ : AutomorphicForm.archSmooth E a => ψ.1 g) e
  have e0 : ∀ ψ : AutomorphicForm.archSmooth E a,
      AutomorphicForm.uAction (CuspidalSpectrum.uJ (K := E) (n := a) 0 (Fin.tail fun _ => j)) ψ = ψ := fun ψ => by
    rw [CuspidalSpectrum.uJ, map_one]
    rfl
  rw [e0]
  exact e2

theorem hasCompactSupport_sum {G ι : Type*} [TopologicalSpace G] (s : Finset ι) (c : ι → ℂ) (D : ι → G → ℂ)
    (h : ∀ j, HasCompactSupport (D j)) : HasCompactSupport fun y => ∑ j ∈ s, c j * D j y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact ((h j).mul_left (f := fun _ => c j)).add ih

theorem lie_eq_conv : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)] (ν : Measure (AutomorphicForm.archGroup E a)) [ν.IsHaarMeasure] (φ : Sm E a), IsAutForm φ → ∀ X : Lie E a, ∃ D : AutomorphicForm.archGroup E a → ℂ, Continuous D ∧ HasCompactSupport D ∧ ∀ g : GA E a, (lie E a X φ).1 g = ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * D y ∂ν := by
  intro E _ _ _ a _ _ ν _ φ hφ X
  obtain ⟨Y, rfl⟩ := mMap_surjective E a X
  choose D hD hDc hconv using exists_kernel_basis E a ν φ hφ
  set b := CuspidalSpectrum.archBasis E a with hb
  set c : Fin (CuspidalSpectrum.archDim E a) → ℂ := fun j => ((b.repr Y j : ℝ) : ℂ) with hc
  refine ⟨fun y => ∑ j, c j * D j y, continuous_finsetSum _ fun j _ => continuous_const.mul (hD j),
    hasCompactSupport_sum _ c D hDc, fun g => ?_⟩
  have hf : Continuous fun y => φ.1 (g * AutomorphicForm.infEmb E a y) :=
    IsExpLieAlgebra.continuous_of_isSmoothFun (GlobalTheory.CompanionTheory.ArchSmooth.sm_mem_archSmooth E a φ g)
  have hint : ∀ j, Integrable (fun y => φ.1 (g * AutomorphicForm.infEmb E a y) * D j y) ν := fun j =>
    (hf.mul (hD j)).integrable_of_hasCompactSupport ((hDc j).mul_left)
  have hY : (lie E a (GlobalTheory.CompanionTheory.ArchSmooth.mMap E a Y) φ).1 g =
      ∑ j, c j * (lie E a (GlobalTheory.CompanionTheory.ArchSmooth.mMap E a (b j)) φ).1 g := by
    conv_lhs => rw [← b.sum_repr Y]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_apply, Pi.smul_apply,
      Complex.real_smul, hc]
  rw [hY]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun j _ => ?_]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [hconv j g, ← integral_const_mul]
    congr 1
    funext y
    ring
  · exact ((hint j).const_mul (c j)).congr (Filter.Eventually.of_forall fun y => by ring)

end GlobalTheory.CompanionTheory.LieConv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCurveIntersectionFormulaStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_curve_intersection_formula : GlobalTheory.CompanionTheory.MixZ.CurveInt := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.curveInt | exact GlobalTheory.CompanionTheory.MixZ.curveInt | (intros; apply GlobalTheory.CompanionTheory.MixZ.curveInt <;> assumption)
end

