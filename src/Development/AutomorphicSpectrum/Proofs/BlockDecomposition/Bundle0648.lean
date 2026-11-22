import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0616
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0180
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0567
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0620
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0624
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0615
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.StepsD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0643
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0601
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0617
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOrbitalIntegralUnipotent
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem jn_firstCols {D : D7} {a r t n : ℕ} (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) :
    (jn hn w v).submatrix id (fun j : Fin r => finCongr hn (Fin.castAdd t j)) = w := by
  ext i j
  have e : (finSumFinEquiv.trans (finCongr hn)).symm (finCongr hn (Fin.castAdd t j)) = Sum.inl j := by
    rw [Equiv.symm_apply_eq]
    simp
  simp only [jn, Matrix.submatrix_apply, id, e, Matrix.fromCols_apply_inl]

theorem continuous_jn_pair {D : D7} {a r t n : ℕ} (hn : r + t = n) :
    Continuous fun p : Mx D a r × Mx D a t => jn hn p.1 p.2 := by
  refine continuous_matrix fun i j => ?_
  simp only [jn, Matrix.submatrix_apply, id]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm j with k | k
  · simpa using (continuous_fst.matrix_elem i k)
  · simpa using (continuous_snd.matrix_elem i k)

theorem continuous_orb_shear : IkSch → Dom → OrbFin → Shift → JnBl → Ext0 → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t)
    (hn : W.rank + t = n) (I : IkD d n) θ, IsInfFam θ → ∀ (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E), x₀.det ≠ 0 →
    ∀ Φ ∈ schwartzA θ B.rank n,
      Continuous (fun y : Mx D W.rank t => orb W I.m (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (ext0 hn x₀)) := by
  intro hIk hDom hOrb hShift hJn hExt D n t B W d hn I θ hθ x₀ hx Φ hΦ
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨hT, -, hS, -, -⟩ := top_mx (D := D) W.rank t
  obtain ⟨hT', -, -, -, -⟩ := top_mx (D := D) W.rank W.rank
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hBor : BorelSpace (GA D W) := ⟨rfl⟩
  have hΨ : ikp I Φ ∈ schwartzA θ W.rank n := (hIk D n t B W d I θ hθ Φ hΦ).2
  have hcΨ : Continuous (ikp I Φ) := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ _ hΨ).1
  have hinj : Function.Injective fun j : Fin W.rank => finCongr hn (Fin.castAdd t j) := by
    intro a b h
    exact Fin.castAdd_injective _ _ ((finCongr hn).injective h)
  obtain ⟨M, hM, -, hMd⟩ := hDom D θ hθ W.rank n W.rank _ hinj _ hΨ
  have hcM : Continuous M := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ M hM).1
  have hform : ∀ (y : Mx D W.rank t) (h : GA D W),
      (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (mm (mt W h⁻¹) (rat (ext0 hn x₀))) =
        ikp I Φ (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0)) := by
    intro y h
    rw [hShift D n t B W d hn I Φ y, hExt D n t W hn x₀ h, hJn D n t W.rank W.rank hn]
  have hfun : (fun y : Mx D W.rank t => orb W I.m (ikp I fun X => Φ (mm X (bl hn 1 y 0 1))) (ext0 hn x₀)) =
      fun y => ∫ h, ikp I Φ (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0)) ∂I.m := by
    funext y
    exact integral_congr_ae (Eventually.of_forall fun h => hform y h)
  rw [hfun]
  have hcw := continuous_ww (D := D) (W := W) x₀
  have hb : Integrable (fun h => M (ww W x₀ h)) I.m :=
    ⟨(hcM.comp hcw).aestronglyMeasurable, hOrb D θ hθ W I.m I.haar x₀ hx M hM⟩
  have hpt : ∀ (h : GA D W), Continuous fun y : Mx D W.rank t => ikp I Φ (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0)) := by
    intro h
    refine hcΨ.comp ((continuous_jn_pair hn).comp (continuous_const.prodMk ?_))
    exact (continuous_const.matrix_mul continuous_id).add continuous_const
  have hmeas : ∀ y : Mx D W.rank t, Continuous fun h : GA D W => ikp I Φ (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0)) := by
    intro y
    refine hcΨ.comp ((continuous_jn_pair hn).comp (hcw.prodMk ?_))
    exact (hcw.matrix_mul continuous_const).add continuous_const
  have hF : FirstCountableTopology (Mx D W.rank t) :=
    @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ hS
  refine continuous_of_dominated (bound := fun h => ‖M (ww W x₀ h)‖)
    (fun y => (hmeas y).aestronglyMeasurable) (fun y => Eventually.of_forall fun h => ?_) hb.norm
    (Eventually.of_forall hpt)
  have h1 := hMd (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0))
  rw [jn_firstCols] at h1
  exact h1.trans (Complex.re_le_norm _)

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceStripStatement
section
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergence_strip : GlobalTheory.CompanionTheory.EGlue.ConvStrip := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.ConvStripProof.convStrip | exact GlobalTheory.CompanionTheory.EGlue.ConvStripProof.convStrip | (intros; apply GlobalTheory.CompanionTheory.EGlue.ConvStripProof.convStrip <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverIntersectionGradedIsoStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_intersection_graded_iso : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a n : ℕ)
    (i : Fin (n + 1) → U.ι) (r : ℕ), Nonempty (HU (Fk q U a) (capT (Vk q U a) i) r ≃+ HQ (KS q (a + 1) {capO U.U i}) (a : ℤ) ((a : ℤ) + 1) r) := by
  first | exact @GlobalTheory.CompanionTheory.CapKC.cap_kc | exact GlobalTheory.CompanionTheory.CapKC.cap_kc | (intros; apply GlobalTheory.CompanionTheory.CapKC.cap_kc <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverStarIsCosieve
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.OmGlob

theorem vk_cosieve {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a : ℕ) (α : U.ι) :
    Cosieve (Vk q U a α) :=
  fun _ _ φ h => Site.inU_hom φ.hom h

end GlobalTheory.CompanionTheory.OmGlob
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalL2NormOneIsometry
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum

noncomputable section
namespace GlobalTheory.CompanionTheory.CuspTransfer

theorem sq_norm_toLp {X : Type*} [MeasurableSpace X] {m : Measure X} {F : X → ℂ} (h : MemLp F 2 m) :
    ENNReal.ofReal (‖h.toLp F‖ ^ 2) = ∫⁻ q, ‖F q‖ₑ ^ 2 ∂m := by
  have h1 := eLpNorm_nnreal_pow_eq_lintegral (f := F) (μ := m) (p := 2) (by norm_num)
  have h2 : ENNReal.ofReal ‖h.toLp F‖ = eLpNorm F 2 m := by
    rw [Lp.norm_toLp, ENNReal.ofReal_toReal h.2.ne]
  rw [ENNReal.ofReal_pow (norm_nonneg _), h2]
  simpa using h1

theorem exists_extend {S H K : Type*} [AddCommGroup S] [Module ℂ S] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (A : S →ₗ[ℂ] H) (B : S →ₗ[ℂ] K)
    (hd : DenseRange A) (r : ℝ) (hn : ∀ s, ‖B s‖ = r * ‖A s‖) :
    ∃ Φ : H →L[ℂ] K, (∀ s, Φ (A s) = B s) ∧ ∀ F, ‖Φ F‖ = r * ‖F‖ := by
  have h1 : ∀ s, (B.extendOfNorm A) (A s) = B s := fun s =>
    LinearMap.extendOfNorm_eq hd ⟨r, fun s => (hn s).le⟩ s
  refine ⟨B.extendOfNorm A, h1, fun F => ?_⟩
  exact hd.induction_on F (isClosed_eq (by fun_prop) (by fun_prop)) fun s => by rw [h1, hn]

theorem exists_extend_equivariant {S H K X : Type*} [AddCommGroup S] [Module ℂ S] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (A : S →ₗ[ℂ] H)
    (B : S →ₗ[ℂ] K) (hd : DenseRange A) (r : ℝ) (hn : ∀ s, ‖B s‖ = r * ‖A s‖) (π : X → H →L[ℂ] H)
    (ρ : X → K →L[ℂ] K) (t : X → S → S) (hπ : ∀ x s, π x (A s) = A (t x s)) (hρ : ∀ x s, ρ x (B s) = B (t x s)) :
    ∃ Φ : H →L[ℂ] K, (∀ F, ‖Φ F‖ = r * ‖F‖) ∧ ∀ x F, Φ (π x F) = ρ x (Φ F) := by
  obtain ⟨Φ, hΦ, hΦn⟩ := exists_extend A B hd r hn
  refine ⟨Φ, hΦn, fun x F => ?_⟩
  refine hd.induction_on F (isClosed_eq ?_ ?_) fun s => ?_
  · exact Φ.continuous.comp (π x).continuous
  · exact (ρ x).continuous.comp Φ.continuous
  · rw [hπ, hΦ, hΦ, hρ]

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem lintegral_resQ (ha : 0 < a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ν : Measure (normOneGL E a))
    [ν.IsHaarMeasure] (c : ENNReal)
    (hmap : Measure.map (fun p : normOneGL E a × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ)
    (φ : GA E a → ℂ) (hc : Continuous φ) (hl : ∀ γ g, φ (ratGL E a γ * g) = φ g)
    (hz : ∀ t g, φ (splitCentre E a t * g) = φ g) :
    ∫⁻ q, ‖resQ φ q‖ₑ ^ 2 ∂(RightCosetSpace.quotientMeasure (rationalGLOne E a) ν) =
      c * ∫⁻ q, ‖descend (latticeGL E a) φ q‖ₑ ^ 2 ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) := by
  have hd := GlobalTheory.T.fundamental_domain_split_centre_product E a ha μ
  have hL : LeftInv (latticeGL E a) φ := leftInv_latticeGL hl hz
  rw [RightCosetSpace.lintegral_quotientMeasure, lintegral_quotMeasure hd]
  simp only [resQ_mk hl, hL.descend_mk]
  rw [← GlobalTheory.T.integral_split_centre_invariant E a ha μ ν c hmap φ hc hz, Measure.restrict_smul, lintegral_smul_measure]
  rfl

def cuspidalL2Functions (μ : Measure (GA E a)) [μ.IsHaarMeasure] : Submodule ℂ (GA E a → ℂ) where
  carrier := {φ | φ ∈ cuspCont E a ∧ MemL2Quotient (latticeGL E a) μ φ}
  zero_mem' := ⟨zero_mem _, fun _ _ _ => rfl, MemLp.zero⟩
  add_mem' := fun {φ ψ} h h' => ⟨add_mem h.1 h'.1, fun γ hγ g => congrArg₂ (· + ·) (h.2.1 γ hγ g) (h'.2.1 γ hγ g),
    h.2.2.add h'.2.2⟩
  smul_mem' := fun z φ h => ⟨Submodule.smul_mem _ z h.1, fun γ hγ g => congrArg (z • ·) (h.2.1 γ hγ g),
    h.2.2.const_smul z⟩

section Maps

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ν : Measure (normOneGL E a)) [ν.IsHaarMeasure]

def toL2cusp : cuspidalL2Functions μ →ₗ[ℂ] L2cusp μ where
  toFun φ := ⟨φ.2.2.toL2, toL2_mem_cuspidal φ.2.2 φ.2.1⟩
  map_add' φ ψ := Subtype.ext (MemLp.toLp_add φ.2.2.2 ψ.2.2.2)
  map_smul' z φ := Subtype.ext (MemLp.toLp_const_smul z φ.2.2.2)

theorem coe_toL2cusp (φ : cuspidalL2Functions μ) : (toL2cusp μ φ : L2 (latticeGL E a) μ) = φ.2.2.toL2 := rfl

theorem denseRange_toL2cusp : DenseRange (toL2cusp μ) := by
  rw [DenseRange, Subtype.dense_iff]
  intro y hy
  refine closure_mono ?_ (show y ∈ closure (cuspContinuousL2 μ : Set (L2 (latticeGL E a) μ)) from hy)
  rintro F ⟨φ, hφ, e⟩
  have h2 := memL2_of_ae_eq (leftInv_of_mem_cuspCont hφ) e
  refine ⟨toL2cusp μ ⟨φ, hφ, h2⟩, ⟨_, rfl⟩, ?_⟩
  rw [coe_toL2cusp]
  exact l2DiscreteQuotient_ext_iff_lift_ae_eq.2 (h2.lift_toL2_ae_eq.trans e.symm)

variable {μ ν} in

def toCusp (hm : ∀ φ : cuspidalL2Functions μ, MemLp (resQ φ.1) 2 (RightCosetSpace.quotientMeasure (rationalGLOne E a) ν)) :
    cuspidalL2Functions μ →ₗ[ℂ] cuspidalL2 ν where
  toFun φ := ⟨(hm φ).toLp _, GlobalTheory.T.cuspidal_restrict_mem_cuspidal_l2 E a ν φ.1 φ.2.1 (hm φ)⟩
  map_add' φ ψ := Subtype.ext (MemLp.toLp_add (hm φ) (hm ψ))
  map_smul' z φ := Subtype.ext (MemLp.toLp_const_smul z (hm φ))

variable {μ ν} in
theorem coe_toCusp (hm : ∀ φ : cuspidalL2Functions μ, MemLp (resQ φ.1) 2 (RightCosetSpace.quotientMeasure (rationalGLOne E a) ν))
    (φ : cuspidalL2Functions μ) :
    (toCusp hm φ : Lp ℂ 2 (RightCosetSpace.quotientMeasure (rationalGLOne E a) ν)) = (hm φ).toLp _ := rfl

end Maps

end GlobalTheory.CompanionTheory.CuspTransfer
end

noncomputable section
namespace GlobalTheory.CompanionTheory.CuspTransfer

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
variable {μ : Measure (GA E a)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {ν : Measure (normOneGL E a)} [ν.IsHaarMeasure]

def trFn (x : GA E a) (φ : cuspidalL2Functions μ) : cuspidalL2Functions μ :=
  ⟨fun g => φ.1 (g * x), mul_right_mem_cuspCont φ.2.1 x, φ.2.2.mul_right x⟩

theorem Rcusp_toL2cusp (x : GA E a) (φ : cuspidalL2Functions μ) : Rcusp μ x (toL2cusp μ φ) = toL2cusp μ (trFn x φ) :=
  Subtype.ext (right_translate_toL2 φ.2.2 x)

theorem cuspRep_toCusp (hm : ∀ φ : cuspidalL2Functions μ, MemLp (resQ φ.1) 2 (RightCosetSpace.quotientMeasure (rationalGLOne E a) ν))
    (x : normOneGL E a) (φ : cuspidalL2Functions μ) : cuspRep ν x (toCusp hm φ) = toCusp hm (trFn (x : GA E a) φ) := by
  refine Subtype.ext (Lp.ext ?_)
  have e0 : ((cuspRep ν x (toCusp hm φ) : cuspidalL2 ν) : Lp ℂ 2 (RightCosetSpace.quotientMeasure (rationalGLOne E a) ν)) =
      RightCosetSpace.rightRegularRep (rationalGLOne E a) ν x (toCusp hm φ) := rfl
  rw [e0, coe_toCusp, coe_toCusp]
  refine (RightCosetSpace.coeFn_rightRegularRep _ ν x _).trans ?_
  refine (((RightCosetSpace.measurePreserving_rightMul ν x).quasiMeasurePreserving.ae_eq_comp
    (hm φ).coeFn_toLp).trans ?_).trans (hm (trFn (x : GA E a) φ)).coeFn_toLp.symm
  refine Filter.Eventually.of_forall fun q => ?_
  obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
  simp only [Function.comp_apply, RightCosetSpace.rightMul_mk]
  rw [resQ_mk φ.2.1.2.1]
  exact (resQ_mk (φ := (trFn (x : GA E a) φ).1) (fun γ g => by
    simp only [trFn, mul_assoc, φ.2.1.2.1]) y).symm

theorem memLp_resQ (ha : 0 < a) (c : ENNReal) (hct : c ≠ ⊤)
    (hmap : Measure.map (fun p : normOneGL E a × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ)
    (φ : cuspidalL2Functions μ) : MemLp (resQ φ.1) 2 (RightCosetSpace.quotientMeasure (rationalGLOne E a) ν) := by
  refine ⟨(continuous_resQ φ.2.1.1 φ.2.1.2.1).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  rw [lintegral_resQ ha μ ν c hmap φ.1 φ.2.1.1 φ.2.1.2.1 φ.2.1.2.2.1, ← sq_norm_toLp φ.2.2.2]
  exact ENNReal.mul_lt_top hct.lt_top ENNReal.ofReal_lt_top

theorem norm_toCusp (ha : 0 < a) (c : ENNReal)
    (hmap : Measure.map (fun p : normOneGL E a × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ)
    (hm : ∀ φ : cuspidalL2Functions μ, MemLp (resQ φ.1) 2 (RightCosetSpace.quotientMeasure (rationalGLOne E a) ν))
    (φ : cuspidalL2Functions μ) : ‖toCusp hm φ‖ = Real.sqrt c.toReal * ‖toL2cusp μ φ‖ := by
  have h3 : ‖toCusp hm φ‖ ^ 2 = c.toReal * ‖toL2cusp μ φ‖ ^ 2 := by
    have h4 := lintegral_resQ ha μ ν c hmap φ.1 φ.2.1.1 φ.2.1.2.1 φ.2.1.2.2.1
    rw [← sq_norm_toLp (hm φ), ← sq_norm_toLp φ.2.2.2] at h4
    have h5 := congrArg ENNReal.toReal h4
    rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h5
    exact h5
  rw [← Real.sqrt_sq (norm_nonneg (toCusp hm φ)), h3, Real.sqrt_mul ENNReal.toReal_nonneg, Real.sqrt_sq (norm_nonneg _)]

end GlobalTheory.CompanionTheory.CuspTransfer
end

noncomputable section
namespace GlobalTheory.CompanionTheory.CuspTransfer
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
variable {μ : Measure (GA E a)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {ν : Measure (normOneGL E a)} [ν.IsHaarMeasure]

theorem exists_transfer_op (ha : 0 < a) (c : ENNReal) (hct : c ≠ ⊤)
    (hmap : Measure.map (fun p : normOneGL E a × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ) :
    ∃ Φ : L2cusp μ →L[ℂ] cuspidalL2 ν, (∀ F, ‖Φ F‖ = Real.sqrt c.toReal * ‖F‖) ∧
      ∀ (x : normOneGL E a) (F : L2cusp μ), Φ (Rcusp μ (x : GA E a) F) = cuspRep ν x (Φ F) :=
  have hm := memLp_resQ (μ := μ) (ν := ν) ha c hct hmap
  exists_extend_equivariant (toL2cusp μ) (toCusp hm) (denseRange_toL2cusp μ) (Real.sqrt c.toReal)
    (norm_toCusp ha c hmap hm) (fun x : normOneGL E a => Rcusp μ (x : GA E a)) (fun x => cuspRep ν x)
    (fun x => trFn (x : GA E a)) (fun x s => Rcusp_toL2cusp _ s) (fun x s => cuspRep_toCusp hm x s)

end GlobalTheory.CompanionTheory.CuspTransfer
end

noncomputable section
namespace GlobalTheory.CompanionTheory.CuspTransfer

theorem comp_repOp_eq_integrated {G Y H K : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [OpensMeasurableSpace G] {m : Measure G} [IsFiniteMeasureOnCompacts m] [Group Y] [TopologicalSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] {n : Measure Y} [IsFiniteMeasureOnCompacts n]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {π : G →* (H →L[ℂ] H)} (hU : IsUnitaryRep π) (ρ : UnitaryRep Y K) (ι : Y → G) (Φ : H →L[ℂ] K)
    (hact : ∀ y v, Φ (π (ι y) v) = ρ y (Φ v)) {f : G → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (f₁ : CompactlySupportedContinuousMap Y ℂ)
    (h₁ : ∀ v, ∫ g, f g • Φ (π g v) ∂m = ∫ y, f₁ y • Φ (π (ι y) v) ∂n) :
    Φ ∘L repOp π m f = ρ.integrated n (UnitaryRep.ccToL1 n f₁) ∘L Φ := by
  refine ContinuousLinearMap.ext fun v => ?_
  have h2 := hU.isRepOp (μ := m) hf hfc v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h2.2, ← Φ.integral_comp_comm h2.1,
    UnitaryRep.integrated_ccToL1_apply]
  simp only [map_smul]
  rw [h₁]
  exact integral_congr_ae (.of_forall fun x => by simp only [hact])

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
variable {μ : Measure (GA E a)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {ν : Measure (normOneGL E a)} [ν.IsHaarMeasure]

theorem comp_repOp_eq (Φ : L2cusp μ →L[ℂ] cuspidalL2 ν)
    (hact : ∀ (x : normOneGL E a) (F : L2cusp μ), Φ (Rcusp μ (x : GA E a) F) = cuspRep ν x (Φ F))
    {f : GA E a → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (f₁ : CompactlySupportedContinuousMap (normOneGL E a) ℂ)
    (h₁ : ∀ (K : Type) [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K] (W : GA E a → K), Continuous W →
      (∀ t g, W (splitCentre E a t * g) = W g) → ∫ g, f g • W g ∂μ = ∫ x, f₁ x • W (x : GA E a) ∂ν) :
    Φ ∘L repOp (Rcusp μ) μ f = (cuspRep ν).integrated ν (UnitaryRep.ccToL1 ν f₁) ∘L Φ :=
  comp_repOp_eq_integrated (isUnitaryRep_Rcusp μ) (cuspRep ν) (fun x : normOneGL E a => (x : GA E a)) Φ hact hf hfc f₁
    fun v => h₁ (cuspidalL2 ν) (fun g => Φ (Rcusp μ g v)) (Φ.continuous.comp ((isUnitaryRep_Rcusp μ).continuous_apply v))
      (fun t g => by simp only [map_mul, Rcusp_splitCentre, one_mul])

end GlobalTheory.CompanionTheory.CuspTransfer
end

namespace GlobalTheory.CompanionTheory.CuspTransfer

theorem transfer : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
      (ν : Measure (GroundTheory.Automorphic.Reduction.normOneGL E a)) [ν.IsHaarMeasure],
      ∃ (Φ : L2cusp μ →L[ℂ] GroundTheory.Automorphic.CuspidalSpectrum.cuspidalL2 ν) (c : ℝ), 0 < c ∧ (∀ F, ‖Φ F‖ = c * ‖F‖) ∧
        ∀ f : GA E a → ℂ, Continuous f → HasCompactSupport f →
          ∃ f₁ : CompactlySupportedContinuousMap (GroundTheory.Automorphic.Reduction.normOneGL E a) ℂ,
            Φ ∘L repOp (Rcusp μ) μ f = (GroundTheory.Automorphic.CuspidalSpectrum.cuspRep ν).integrated ν
              (GroundTheory.Automorphic.UnitaryRep.ccToL1 ν f₁) ∘L Φ := fun E _ _ _ a ha μ _ _ ν _ =>
  (GlobalTheory.T.haar_measure_norm_one_product E a ha μ ν).elim fun c h =>
    (exists_transfer_op ha c h.2.1 h.2.2).elim fun Φ h' =>
      ⟨Φ, Real.sqrt c.toReal, Real.sqrt_pos.2 (ENNReal.toReal_pos h.1 h.2.1), h'.1, fun f hf hfc =>
        (GlobalTheory.T.compact_support_split_centre_factor E a ha μ ν c h.1 h.2.1 h.2.2 f hf hfc).elim fun f₁ h₁ =>
          ⟨f₁, comp_repOp_eq Φ h'.2 hf hfc f₁ fun K _ _ _ W => h₁ K W⟩⟩

end GlobalTheory.CompanionTheory.CuspTransfer
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalMultiplicityProductZeroStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_multiplicity_product_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ (ρ : IrrGL k) {h : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = ρ.1), ρ.IsCusp → 2 ≤ h → (∀ a, 0 < (x a).1) → jhMult ρ.rep (prodIrr x hd) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CuspNotInd.jhMult_eq_zero_of_isCusp | exact GlobalTheory.CompanionTheory.CuspNotInd.jhMult_eq_zero_of_isCusp | (intros; apply GlobalTheory.CompanionTheory.CuspNotInd.jhMult_eq_zero_of_isCusp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegenerateQuadraticWeightTerm
section
noncomputable section

open Ad3.LR Filter Topology

namespace GlobalTheory.CompanionTheory.RowPolarization

def HD (f : M22 → ℂ) (h e : M22) (d : ℂ) : Prop :=
  ∃ L : M22 →L[ℝ] ℂ, HasFDerivAt f L h ∧ L e = d

variable {f g : M22 → ℂ} {h e : M22} {d d' : ℂ}

def Dl (x : M22) : ℂ := (x 0 0 : ℂ) * (x 1 1 : ℂ) - (x 0 1 : ℂ) * (x 1 0 : ℂ)

def Ac (x : M22) : ℂ := (x 0 0 : ℂ) + (x 1 0 : ℂ) * Complex.I

def Bc (x : M22) : ℂ := (x 0 1 : ℂ) + (x 1 1 : ℂ) * Complex.I

def Gc (x : M22) : ℂ := (Ac x)⁻¹

def Tc : ℂ := 2 * Real.pi * Complex.I

def Fk (p : ℕ) (x : M22) : ℂ :=
  Dl x ^ (p + 1) * Gc x ^ (2 * p + 2 + 1) * Complex.exp (Tc * (Bc x * Gc x))

def Xc (p : ℕ) (x : M22) : ℂ :=
  (-(2 * (p : ℂ) + 3)) * Gc x * (x 0 0 : ℂ) + Tc * (Gc x * (x 0 1 : ℂ) - Bc x * (Gc x * Gc x) * (x 0 0 : ℂ))

def Yc (p : ℕ) (x : M22) : ℂ :=
  (-(2 * (p : ℂ) + 3)) * Gc x * (x 1 0 : ℂ) + Tc * (Gc x * (x 1 1 : ℂ) - Bc x * (Gc x * Gc x) * (x 1 0 : ℂ))

end GlobalTheory.CompanionTheory.RowPolarization
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetNeZeroOfGramNondegenerate
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.Frame

theorem det_ne_zero_of_gramQ : ∀ (D : D7) (W : HSp D) (b₀ : HermE D W.rank), b₀.1.det ≠ 0 →
    ∀ x₀, gramQ W x₀ = b₀.1 → x₀.det ≠ 0 := by
  intro D W b₀ hb x₀ hx h0
  apply hb
  rw [← hx]
  unfold gramQ
  simp [Matrix.det_mul, h0]

end GlobalTheory.CompanionTheory.ColumnSplitting.Frame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetRowRep
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

theorem det_rowRep_eq_zpow : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (i j : ℕ) (c : Fin j → 𝓀[F]), GeneralLinearGroup.det (rowRep i j c) = uniformizerUnit F ^ ((i : ℤ) + j) := by
  intro F _ _ _ _ i j c
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_rowRep, Matrix.det_fin_two_of]
  have h : ((i : ℤ) + j) = ((i + j : ℕ) : ℤ) := by push_cast; rfl
  rw [h, zpow_natCast, Units.val_pow_eq_pow_val, coe_uniformizerUnit, pow_add]
  simp

end GlobalTheory.CompanionTheory.LFUDom
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetTorusPower
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

theorem det_torusPow_eq (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (l : Fin n → ℤ) :
    GeneralLinearGroup.det (torusPow F n l) = uniformizerUnit F ^ (∑ i, l i) := by
  have key : ∀ s : Finset (Fin n),
      ∏ i ∈ s, uniformizerUnit F ^ l i = uniformizerUnit F ^ (∑ i ∈ s, l i) := by
    intro s
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, _root_.zpow_add]
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, coe_torusPow, det_diagonal, ← key Finset.univ]
  simp [Units.coe_prod, Iwasawa.coe_uniformizerUnit, Units.val_zpow_eq_zpow_val]

end GlobalTheory.CompanionTheory.LFUDom
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiscreteInfimumStatement
section
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_infimum : GlobalTheory.CompanionTheory.EGlue.DiscInf := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.discInf | exact GlobalTheory.CompanionTheory.EGlue.discInf | (intros; apply GlobalTheory.CompanionTheory.EGlue.discInf <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisintegrationParameterContinuousStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.disintegration_parameter_continuous : ∀ (V H Y P : Type) [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace H] [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] [TopologicalSpace P] [T2Space P] [LocallyCompactSpace P] (μ : Measure V) (ν : Measure H) (f : V → Y) (ι : H → Y) (q : V → H) (U : Set V) (fam : H → Measure V), IsOpen U → Continuous q → Function.Injective ι → (∀ v, f v = ι (q v)) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fam → ∀ ψ : P × V → ℝ, Continuous ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, p.2 ∈ U) → Continuous (fun z : P × H => ∫ v, ψ (z.1, v) ∂(fam z.2)) ∧ HasCompactSupport (fun z : P × H => ∫ v, ψ (z.1, v) ∂(fam z.2)) ∧ ∀ z ∈ tsupport (fun z : P × H => ∫ v, ψ (z.1, v) ∂(fam z.2)), ∃ v, (z.1, v) ∈ tsupport ψ ∧ q v = z.2 := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.FibParam.fibre_param_continuous | exact GlobalTheory.CompanionTheory.WeilSiegel.FibParam.fibre_param_continuous | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.FibParam.fibre_param_continuous <;> assumption)
end

