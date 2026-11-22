import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0747
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0505
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0736
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0741
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0752
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0749
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0742
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteL2SmoothRepresentative
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0750
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0526
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0514

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedHermSVal
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
namespace GlobalTheory.CompanionTheory.MuC

theorem isClosed_hermS_val (D : D7) (p : ℕ) (e : AE D) :
    IsClosed ((hermS D p e : AddSubgroup (hermA D p)) : Set (hermA D p)) := by
  obtain ⟨_, _, _, _, _⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hc : Continuous fun x : hermA D p => e • (x : Formalism.IndefR.Datum.Mx D p p) :=
    (continuous_const_smul e).comp continuous_subtype_val
  exact isClosed_eq hc continuous_subtype_val

set_option synthInstance.maxHeartbeats 400000 in

theorem hermS_facts : ∀ (D : D7) (p : ℕ) (e : AE D), LocallyCompactSpace (hermS D p e) ∧ T2Space (hermS D p e) ∧
    SecondCountableTopology (hermS D p e) ∧ BorelSpace (hermS D p e) ∧ IsTopologicalAddGroup (hermS D p e) := by
  intro D p e
  obtain ⟨_, _, _, _, _⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hS := isClosed_hermS_val D p e
  have hA : IsClosed ((hermA D p : AddSubgroup (Formalism.IndefR.Datum.Mx D p p)) : Set (Formalism.IndefR.Datum.Mx D p p)) :=
    GlobalTheory.CompanionTheory.HermVol.isClosed_hermA
  haveI : LocallyCompactSpace (Formalism.IndefR.Datum.Mx D p p) :=
    show LocallyCompactSpace (Fin p → Fin p → AE D) from inferInstance
  haveI : SecondCountableTopology (Formalism.IndefR.Datum.Mx D p p) :=
    show SecondCountableTopology (Fin p → Fin p → AE D) from inferInstance
  haveI : BorelSpace (Formalism.IndefR.Datum.Mx D p p) := by
    first
    | exact show BorelSpace (Fin p → Fin p → AE D) from inferInstance
    | exact ⟨rfl⟩
    | exact Matrix.borelSpace
  haveI : SecondCountableTopology (hermA D p) := by
    first
    | exact Topology.IsInducing.subtypeVal.secondCountableTopology
    | exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
    | exact show SecondCountableTopology ((hermA D p : Set (Formalism.IndefR.Datum.Mx D p p))) from inferInstance
  haveI : SecondCountableTopology (hermS D p e) := by
    first
    | exact Topology.IsInducing.subtypeVal.secondCountableTopology
    | exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
    | exact show SecondCountableTopology ((hermS D p e : Set (hermA D p))) from inferInstance
  haveI : LocallyCompactSpace (hermA D p) := hA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact ⟨hS.isClosedEmbedding_subtypeVal.locallyCompactSpace, inferInstance, inferInstance, inferInstance,
    inferInstance⟩

end GlobalTheory.CompanionTheory.MuC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenStandardLatticeStabilizer
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology

namespace GlobalTheory.CompanionTheory.BZCore

theorem isOpen_preserve_standard_lattice {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {d : ℕ} :
    IsOpen {g : GL (Fin d) k | ∀ y ∈ (lat0 : COSub k d).sub,
      (g : Matrix (Fin d) (Fin d) k).mulVec y ∈ (lat0 : COSub k d).sub} := by
  have hc : Continuous fun p : GL (Fin d) k × (Fin d → k) =>
      ((p.1 : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec p.2 :=
    Continuous.matrix_mulVec (Units.continuous_val.comp continuous_fst) continuous_snd
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have hK : IsCompact ((lat0 : COSub k d).sub : Set (Fin d → k)) := lat0.isCompact
  exact hK.eventually_forall_of_forall_eventually
    (P := fun (h : GL (Fin d) k) (y : Fin d → k) =>
      (h : Matrix (Fin d) (Fin d) k).mulVec y ∈ (lat0 : COSub k d).sub)
    fun y hy => hc.continuousAt.eventually_mem (lat0.isOpen.mem_nhds (hg y hy))

theorem isOpen_stabilizer_standard_lattice {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {d : ℕ} :
    IsOpen {g : GL (Fin d) k | (lat0 : COSub k d).act g = lat0} := by
  have h1 := isOpen_preserve_standard_lattice (k := k) (d := d)
  have h2 := h1.preimage (continuous_inv (G := GL (Fin d) k))
  convert h1.inter h2 using 1
  ext g
  constructor
  · intro hg
    have hg' : (lat0 : COSub k d).act g = lat0 := hg
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · have := (COSub.mulVec_mem_act (L := (lat0 : COSub k d)) g (y := y)).2 hy
      rwa [hg'] at this
    · have hy' : y ∈ ((lat0 : COSub k d).act g).sub := by rwa [hg']
      exact COSub.mem_act.1 hy'
  · rintro ⟨ha, hb⟩
    refine COSub.ext (AddSubgroup.ext fun y => ?_)
    rw [COSub.mem_act]
    refine ⟨fun hy => ?_, fun hy => hb y hy⟩
    have := ha _ hy
    rwa [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at this

end GlobalTheory.CompanionTheory.BZCore
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsRhoRight
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.MuC

theorem isRho_right {D : D7} {p : ℕ} {f : G D p → ℂ} (hf : IsRho f) (x : G D p) :
    IsRho (fun g => f (g * x)) := by
  refine ⟨hf.1.comp (continuous_mul_const x), ?_⟩
  intro q hq a ha g
  have := hf.2 q hq a ha (g * x)
  simpa [mul_assoc] using this

end GlobalTheory.CompanionTheory.MuC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCompactnessStatement
section
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_compactness : IwaCpt := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.iwaCpt | exact GlobalTheory.CompanionTheory.ThTot.iwaCpt | (intros; apply GlobalTheory.CompanionTheory.ThTot.iwaCpt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaParabolicUnitaryStatement
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_parabolic_unitary : ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ g ∈ GLs n, ∃ p ∈ GlobalTheory.CompanionTheory.ModelS.Pb lev, ∃ k : Matrix.unitaryGroup (Fin n) ℂ, g = p * k.1 := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.exists_Pb_mul_unitary | exact GlobalTheory.CompanionTheory.ModelS.exists_Pb_mul_unitary | (intros; apply GlobalTheory.CompanionTheory.ModelS.exists_Pb_mul_unitary <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KActionSkewAdjointL2Statement
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.k_action_skew_adjoint_l2 : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ], (∀ u : Mat n → ℂ, ContDiffOn ℝ ∞ u (GLs n) → ∀ X : Mat n, Xᴴ = -X → ∫ k : Matrix.unitaryGroup (Fin n) ℂ, Rd X u k.1 ∂κ = 0) → ∀ (a b : Fin n) (x y : GlobalTheory.CompanionTheory.ModelS.SmF n), GlobalTheory.CompanionTheory.ModelS.ipK κ (GlobalTheory.CompanionTheory.ModelS.Kf a b x) y = GlobalTheory.CompanionTheory.ModelS.ipK κ x (GlobalTheory.CompanionTheory.ModelS.Kf b a y) := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.ipK_Kf_transpose | exact GlobalTheory.CompanionTheory.ModelS.ipK_Kf_transpose | (intros; apply GlobalTheory.CompanionTheory.ModelS.ipK_Kf_transpose <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteL2SmoothRepresentativeStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.K_finite_L2_smooth_representative : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ F ∈ H, IsKFinL2 μ F → ∃ φ : Sm E a, lift (latticeGL E a) F =ᵐ[μ] φ.1 ∧ MemL2Quotient (latticeGL E a) μ φ.1 ∧ (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) ∧ (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) ∧ IsOpen {k | finRep E a k φ = φ} ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) ∧ FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.smoothRep | exact GlobalTheory.CompanionTheory.SmoothRep.smoothRep | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.smoothRep <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2InnerProductHermitianFormStatement
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.l2_inner_product_hermitian_form : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ] [κ.IsOpenPosMeasure], (∀ x y : GlobalTheory.CompanionTheory.ModelS.SmF n, conj (GlobalTheory.CompanionTheory.ModelS.ipK κ y x) = GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ (∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, 0 ≤ (GlobalTheory.CompanionTheory.ModelS.ipK κ x x).re) ∧ (∀ x y z : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ (x + y) z = GlobalTheory.CompanionTheory.ModelS.ipK κ x z + GlobalTheory.CompanionTheory.ModelS.ipK κ y z) ∧ (∀ (c : ℂ) (x y : GlobalTheory.CompanionTheory.ModelS.SmF n), GlobalTheory.CompanionTheory.ModelS.ipK κ (c • x) y = conj c * GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ ∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ x x = 0 → ∀ k : Matrix.unitaryGroup (Fin n) ℂ, x.1 k.1 = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.L2InnerProduct.ipK_form | exact GlobalTheory.CompanionTheory.ModelS.L2InnerProduct.ipK_form | (intros; apply GlobalTheory.CompanionTheory.ModelS.L2InnerProduct.ipK_form <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsInjectiveOfSocleStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_injective_of_socle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → LInjective k := by
  first | exact @GlobalTheory.CompanionTheory.Multisegment.lInjective | exact GlobalTheory.CompanionTheory.Multisegment.lInjective | (intros; apply GlobalTheory.CompanionTheory.Multisegment.lInjective <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSumSubquotientProductStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_sum_subquotient_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → LOrderFree k → (∀ x : IrrGL k, ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep) → ∀ (𝔪 𝔫 : Multiset (Segment k)) (x : Fin 2 → IrrGL k) (y : IrrGL k) (hd : ∑ a, (x a).1 = y.1), IsL 𝔪 (x 0).rep → IsL 𝔫 (x 1).rep → IsL (𝔪 + 𝔫) y.rep → IsSubquotient y.rep (prodIrr x hd) := by
  first | exact @GlobalTheory.CompanionTheory.LangSumSub.main | exact GlobalTheory.CompanionTheory.LangSumSub.main | (intros; apply GlobalTheory.CompanionTheory.LangSumSub.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeVolumeScalingLaws
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore

theorem exists_vol_cosub {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) :
    ∃ vol : COSub k d → ℝ, (∀ L, 0 < vol L) ∧
      (∀ (L' L : COSub k d) (S : Finset (Fin d → k)), L'.sub ≤ L.sub → IsReps L' L S →
        vol L = (S.card : ℝ) * vol L') ∧
      ∀ (g : GL (Fin d) k) (L : COSub k d),
        ((vol (L.act g) : ℝ) : ℂ) ^ 2 * ((dpow d (-2) g : ℂˣ) : ℂ) = ((vol L : ℝ) : ℂ) ^ 2 := by
  classical
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  let ν : Measure k := Measure.addHaar
  haveI : ν.IsAddHaarMeasure := inferInstanceAs (Measure.addHaar : Measure k).IsAddHaarMeasure
  haveI hμ : (piHaar ν d).IsAddHaarMeasure := GlobalTheory.CompanionTheory.MirStable.isAddHaar_piHaar ν d
  have hfin : ∀ L : COSub k d, piHaar ν d (L.sub : Set (Fin d → k)) ≠ ⊤ := fun L =>
    L.isCompact.measure_lt_top.ne
  have hne : ∀ L : COSub k d, piHaar ν d (L.sub : Set (Fin d → k)) ≠ 0 := fun L =>
    L.isOpen.measure_ne_zero _ ⟨0, L.sub.zero_mem⟩
  refine ⟨fun L => (piHaar ν d (L.sub : Set (Fin d → k))).toReal, fun L => ENNReal.toReal_pos (hne L) (hfin L), ?_, ?_⟩
  · intro L' L S hle hS
    have hU : (L.sub : Set (Fin d → k)) = ⋃ s ∈ S, {y | y - s ∈ L'.sub} := by
      ext y
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, SetLike.mem_coe, exists_prop]
      constructor
      · intro hy
        obtain ⟨s, ⟨hs, hys⟩, -⟩ := hS.2 y hy
        exact ⟨s, hs, hys⟩
      · rintro ⟨s, hs, hys⟩
        have := L.sub.add_mem (hle hys) (hS.1 s hs)
        simpa using this
    have hdisj : Set.PairwiseDisjoint (S : Set (Fin d → k)) fun s => {y | y - s ∈ L'.sub} := by
      intro s hs t ht hst
      refine Set.disjoint_left.2 fun y hys hyt => hst ?_
      have hy : y ∈ L.sub := by
        have := L.sub.add_mem (hle hys) (hS.1 s hs)
        simpa using this
      exact (hS.2 y hy).unique ⟨hs, hys⟩ ⟨ht, hyt⟩
    have hcos : ∀ s : Fin d → k, piHaar ν d {y | y - s ∈ L'.sub} = piHaar ν d (L'.sub : Set (Fin d → k)) := by
      intro s
      have : {y | y - s ∈ L'.sub} = (fun y => y + (-s)) ⁻¹' (L'.sub : Set (Fin d → k)) := by
        ext y
        simp [sub_eq_add_neg]
      rw [this, measure_preimage_add_right]
    have hm : piHaar ν d (L.sub : Set (Fin d → k)) = (S.card : ENNReal) * piHaar ν d (L'.sub : Set (Fin d → k)) := by
      rw [hU, measure_biUnion_finset hdisj fun s _ => (isClopen_coset L' s).isOpen.measurableSet]
      simp [hcos]
    show (piHaar ν d (L.sub : Set (Fin d → k))).toReal = _
    rw [hm, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  · intro g L
    have hI := setIntegral_inv_mulVec ν d g ((L.act g).sub : Set (Fin d → k)) (fun _ => (1 : ℂ))
    have hset : {y | (g : Matrix (Fin d) (Fin d) k) *ᵥ y ∈ ((L.act g).sub : Set (Fin d → k))} = (L.sub : Set (Fin d → k)) := by
      ext y
      exact COSub.mulVec_mem_act g
    rw [hset, setIntegral_const, setIntegral_const] at hI
    simp only [Measure.real, Complex.real_smul, mul_one] at hI
    have hn := nabs_pos' k (Matrix.GeneralLinearGroup.det g)
    have hd : ((dpow d (-2) g : ℂˣ) : ℂ) = (((nabs k (Matrix.GeneralLinearGroup.det g)) ^ (-2 : ℝ) : ℝ) : ℂ) := by
      simp only [dpow, detChar_apply]
      exact val_absPow_ofReal k (-2) _
    rw [hd, hI]
    have hr : (nabs k (Matrix.GeneralLinearGroup.det g)) ^ (-2 : ℝ) = ((nabs k (Matrix.GeneralLinearGroup.det g)) ^ 2)⁻¹ := by
      rw [Real.rpow_neg hn.le, Real.rpow_two]
    rw [hr]
    have hn' : ((nabs k (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp

end GlobalTheory.CompanionTheory.BZCore

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrbitGLNearOne
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ}

theorem latZ_subset_of_mem_nhds (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) {A : Set (Fin d → k)} (hA : A ∈ 𝓝 (0 : Fin d → k)) :
    ∃ r : ℕ, ∀ y, y ∈ (latZ z (r : ℤ)).sub → y ∈ A := by
  have hall : ∀ᶠ t : k in 𝓝 0, ∀ w ∈ ((lat0 : COSub k d).sub : Set (Fin d → k)), t • w ∈ A := by
    refine (lat0 : COSub k d).isCompact.eventually_forall_of_forall_eventually fun w _ => ?_
    have hc : Continuous fun p : k × (Fin d → k) => p.1 • p.2 := continuous_fst.smul continuous_snd
    have h0 : A ∈ 𝓝 (((0 : k), w).1 • ((0 : k), w).2) := by simpa using hA
    exact hc.continuousAt.eventually h0
  have ht : Filter.Tendsto (fun n : ℕ => ϖ ^ n) Filter.atTop (𝓝 0) := by
    rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
    intro γ hγ
    have : MulArchimedean (ValuativeRel.ValueGroupWithZero k) :=
      ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ (Units.mk0 γ hγ)
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    rw [map_pow]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hϖ.le hm) hn
  obtain ⟨r, hr⟩ := (ht.eventually hall).exists
  refine ⟨r, fun y hy => ?_⟩
  have h1 : ϖ ^ r • ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y) ∈ A := hr _ hy
  have h2 : ϖ ^ r • ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y) = y := by
    have := zpow_mulVec z ϖ hz hϖ0 (r : ℤ) ((((z ^ (r : ℤ) : GL (Fin d) k)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).mulVec y)
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, zpow_natCast] at this
    exact this.symm
  rwa [h2] at h1

theorem vecMulVec_single_mul_self (i : Fin d) (u : Fin d → k) :
    vecMulVec u (Pi.single i (1 : k)) * vecMulVec u (Pi.single i (1 : k)) =
      u i • vecMulVec u (Pi.single i (1 : k)) := by
  ext a b
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, Pi.single_apply]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, one_mul]
  simp
  split_ifs <;> simp [mul_comm]

theorem exists_mem_nhds_one_mulVec_eq (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (U : Set (GL (Fin d) k))
    (hU : U ∈ 𝓝 (1 : GL (Fin d) k)) (x : Fin d → k) (hx : x ≠ 0) :
    ∃ s : ℕ, ∀ y : Fin d → k, y - x ∈ (latZ z (s : ℤ)).sub →
      ∃ g ∈ U, (g : Matrix (Fin d) (Fin d) k).mulVec x = y := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  let P : (Fin d → k) → Matrix (Fin d) (Fin d) k := fun y => vecMulVec (y - x) (Pi.single i (1 : k))
  let M : (Fin d → k) → Matrix (Fin d) (Fin d) k := fun y => 1 + (x i)⁻¹ • P y
  let N : (Fin d → k) → Matrix (Fin d) (Fin d) k := fun y => 1 - (y i)⁻¹ • P y
  have hPc : Continuous P := (continuous_id.sub continuous_const).matrix_vecMulVec continuous_const
  have hPx : P x = 0 := by
    ext a b
    simp [P, vecMulVec_apply]
  have hMc : ContinuousAt M x := by
    have h : Continuous fun y => (1 : Matrix (Fin d) (Fin d) k) + (x i)⁻¹ • P y := by fun_prop
    exact h.continuousAt
  have hNc : ContinuousAt N x := by
    have h1 : ContinuousAt (fun y : Fin d → k => (y i)⁻¹) x := (continuous_apply i).continuousAt.inv₀ hi
    have h2 : ContinuousAt (fun y => (y i)⁻¹ • P y) x := h1.fun_smul hPc.continuousAt
    have h3 : ContinuousAt (fun y => (1 : Matrix (Fin d) (Fin d) k) - (y i)⁻¹ • P y) x := continuousAt_const.fun_sub h2
    exact h3
  have hMx : M x = 1 := by simp [M, hPx]
  have hNx : N x = 1 := by simp [N, hPx]
  have hMN : ∀ y, y i ≠ 0 → M y * N y = 1 := by
    intro y hy
    have hsq : P y * P y = (y i - x i) • P y := by
      simpa [P] using vecMulVec_single_mul_self i (y - x)
    simp only [M, N, mul_sub, add_mul, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hsq, smul_smul]
    have h3 : (y i)⁻¹ + ((y i)⁻¹ * ((x i)⁻¹ * y i) - (y i)⁻¹ * ((x i)⁻¹ * x i)) = (x i)⁻¹ := by
      field_simp
      ring
    rw [← add_smul, h3, add_sub_cancel_right]
  have hNM : ∀ y, y i ≠ 0 → N y * M y = 1 := fun y hy => mul_eq_one_comm.1 (hMN y hy)
  have hMv : ∀ y, (M y).mulVec x = y := by
    intro y
    have h1 : (P y).mulVec x = x i • (y - x) := by
      ext a
      simp [P, vecMulVec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
    simp only [M, Matrix.add_mulVec, one_mulVec, Matrix.smul_mulVec, h1, smul_smul, inv_mul_cancel₀ hi, one_smul]
    abel
  have hT : Filter.Tendsto (fun y => (M y, MulOpposite.op (N y))) (𝓝 x)
      (𝓝 (Units.embedProduct (Matrix (Fin d) (Fin d) k) 1)) := by
    have e : Units.embedProduct (Matrix (Fin d) (Fin d) k) 1 = (M x, MulOpposite.op (N x)) := by
      rw [hMx, hNx, map_one]
      rfl
    rw [e]
    exact hMc.tendsto.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp hNc.tendsto)
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨W, hW, hWU⟩ := hU
  have hgood : ∀ᶠ y in 𝓝 x, y i ≠ 0 ∧ (M y, MulOpposite.op (N y)) ∈ W :=
    ((continuous_apply i).continuousAt.eventually_ne hi).and (hT.eventually hW)
  have hA : {l : Fin d → k | (x + l) i ≠ 0 ∧ (M (x + l), MulOpposite.op (N (x + l))) ∈ W} ∈ 𝓝 (0 : Fin d → k) := by
    have hc : Filter.Tendsto (fun l : Fin d → k => x + l) (𝓝 0) (𝓝 x) := by
      have h : Continuous fun l : Fin d → k => x + l := by fun_prop
      simpa using h.tendsto 0
    exact hc.eventually hgood
  obtain ⟨s, hs⟩ := latZ_subset_of_mem_nhds z ϖ hz hϖ hϖ0 hA
  refine ⟨s, fun y hy => ?_⟩
  have hy' := hs _ hy
  rw [Set.mem_setOf_eq, add_sub_cancel] at hy'
  refine ⟨⟨M y, N y, hMN y hy'.1, hNM y hy'.1⟩, hWU ?_, hMv y⟩
  exact hy'.2

end GlobalTheory.CompanionTheory.BZCore

end
end

