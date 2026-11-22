import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0633
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0634
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1190
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0635
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0616
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0636
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.Bundle0001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureTranslationInvariant
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

theorem nuT_shear_invariant : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n)
    (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀ (y : Mx D W.rank t),
    (nuT hn I μ x₀).map (fun z => (z.1, z.2 + mm z.1 y)) = nuT hn I μ x₀ := by
  intro D n t B W d hn I μ hμ x₀ y
  have hring := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨i1, i2, i3, i4, i5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) t n
  obtain ⟨k1, -, -, -, -⟩ := top_mx (D := D) B.rank t
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨hc, 𝓕, hf⟩ := I.cov₁
  have := hf.1
  have := I.haar
  have := I.probK
  have hQ := sigmaFinite_parameter_product_measure I μ hμ
  obtain ⟨p1, p2⟩ := top_pair (D := D) B.rank W.rank t
  have o1 : OpensMeasurableSpace (Mx D B.rank W.rank × Mx D B.rank t) := p1.opensMeasurable
  have hS : Measurable fun z : Mx D B.rank W.rank × Mx D B.rank t => (z.1, z.2 + mm z.1 y) :=
    (continuous_fst.prodMk (continuous_snd.add (continuous_fst.matrix_mul continuous_const))).measurable
  have hτ : MeasurePreserving (fun p : I.l.K × Par D n t W => (p.1, p.2.1, p.2.2.1, p.2.2.2 + y))
      (I.νK.prod (Q0 I μ)) (I.νK.prod (Q0 I μ)) := by
    unfold Q0
    exact (MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod
      ((MeasurePreserving.id _).prod (measurePreserving_add_right μ y)))
  have hπ := measurable_pi (d := d) hn I x₀
  have hcomp : (fun z : Mx D B.rank W.rank × Mx D B.rank t => (z.1, z.2 + mm z.1 y)) ∘
        (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) =
      (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) ∘
        (fun p : I.l.K × Par D n t W => (p.1, p.2.1, p.2.2.1, p.2.2.2 + y)) := by
    funext p
    refine Prod.ext rfl ?_
    have key : ∀ {a b c : ℕ} (g : Mx D a a) (ξ : Mx D a b) (u : Mx D a c) (y' y : Mx D b c),
        mm g (mm ξ y' + u) + mm (mm g ξ) y = mm g (mm ξ (y' + y) + u) := by
      intro a b c g ξ u y' y
      simp only [mm, Matrix.mul_add, Matrix.mul_assoc]
      abel
    exact key _ _ _ _ _
  unfold nuT
  rw [Measure.map_map hS hπ, hcomp, ← Measure.map_map hπ hτ.measurable, hτ.map_eq]

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureUnitaryGroupInvariant
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

namespace GlobalTheory.CompanionTheory.ColumnSplitting.InvU

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem ac_mul (V : HSp D) {a b : ℕ} (g h : GA D V) (z : Mx D V.rank a × Mx D V.rank b) :
    ac V (g * h) z = ac V g (ac V h z) := by
  simp only [ac, mm, mt_mul, Matrix.mul_assoc]

theorem measurable_ac (V : HSp D) {a b : ℕ} (g : GA D V) :
    Measurable (ac V g : Mx D V.rank a × Mx D V.rank b → Mx D V.rank a × Mx D V.rank b) := by
  obtain ⟨g1, g2⟩ := top_pair (D := D) V.rank a b
  have o1 : OpensMeasurableSpace (Mx D V.rank a × Mx D V.rank b) := g1.opensMeasurable
  have hc : Continuous (ac V g : Mx D V.rank a × Mx D V.rank b → Mx D V.rank a × Mx D V.rank b) :=
    (continuous_ac V).comp (continuous_const.prodMk continuous_id)
  exact hc.measurable

theorem rho_apply {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    {A : Set (Mx D B.rank W.rank × Mx D B.rank t)} (hA : MeasurableSet A) :
    rho hn I μ x₀ A = Q0 I μ (zp d hn x₀ ⁻¹' A) :=
  Measure.map_apply (measurable_zp d hn x₀) hA

def sA {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (A : Set (Mx D B.rank W.rank × Mx D B.rank t)) (x : GA D B) : ℝ≥0∞ :=
  rho hn I μ x₀ {z | ac B x⁻¹ z ∈ A}

theorem measurable_sA {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (hμ : μ.IsAddHaarMeasure) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    {A : Set (Mx D B.rank W.rank × Mx D B.rank t)} (hA : MeasurableSet A) : Measurable (sA hn I μ x₀ A) := by
  obtain ⟨h1, h2⟩ := top_par (D := D) n t W
  obtain ⟨g1, g2⟩ := top_pair (D := D) B.rank W.rank t
  obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have hB : BorelSpace (GA D B) := ⟨rfl⟩
  have o0 : OpensMeasurableSpace (Par D n t W) := h1.opensMeasurable
  have oB : OpensMeasurableSpace (GA D B) := hB.opensMeasurable
  have e1 : SecondCountableTopologyEither (GA D B) (Par D n t W) := ⟨Or.inr h2⟩
  have o1 : OpensMeasurableSpace (GA D B × Par D n t W) := Prod.opensMeasurableSpace
  have := sigmaFinite_parameter_product_measure I μ hμ
  have hc : Continuous fun p : GA D B × Par D n t W => ac B p.1⁻¹ (zp d hn x₀ p.2) :=
    (continuous_ac B).comp ((continuous_fst.inv).prodMk ((continuous_zp d hn x₀).comp continuous_snd))
  have hS : MeasurableSet {p : GA D B × Par D n t W | ac B p.1⁻¹ (zp d hn x₀ p.2) ∈ A} := hc.measurable hA
  have key := measurable_measure_prodMk_left (ν := Q0 I μ) hS
  have e : sA hn I μ x₀ A = fun x => Q0 I μ (Prod.mk x ⁻¹' {p : GA D B × Par D n t W | ac B p.1⁻¹ (zp d hn x₀ p.2) ∈ A}) := by
    funext x
    exact rho_apply hn I μ x₀ (measurable_ac B x⁻¹ hA)
  rw [e]
  exact key

theorem sA_stab (hL : Law) {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (hμ : μ.IsAddHaarMeasure) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    {A : Set (Mx D B.rank W.rank × Mx D B.rank t)} (hA : MeasurableSet A) (q : GlobalTheory.RegSW.stab d) (x : GA D B) :
    sA hn I μ x₀ A (q * x) = ((GlobalTheory.RegSW.absDet d q ^ (W.rank + t) : ℝ≥0) : ℝ≥0∞) * sA hn I μ x₀ A x := by
  have hA' : MeasurableSet {z | ac B x⁻¹ z ∈ A} := measurable_ac B x⁻¹ hA
  have h1 := congrArg (fun ν : Measure _ => ν {z | ac B x⁻¹ z ∈ A}) (hL D n t B W d hn I μ hμ x₀ q⁻¹)
  beta_reduce at h1
  rw [Measure.map_apply (measurable_ac B _) hA'] at h1
  have e : sA hn I μ x₀ A (q * x) = rho hn I μ x₀ (ac B ((q⁻¹ : GlobalTheory.RegSW.stab d) : GA D B) ⁻¹' {z | ac B x⁻¹ z ∈ A}) := by
    unfold sA
    congr 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, ← ac_mul, mul_inv_rev, Subgroup.coe_inv]
  rw [e, h1, map_inv, inv_inv]
  rfl

theorem nuT_apply {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t))
    (hμ : μ.IsAddHaarMeasure) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    {A : Set (Mx D B.rank W.rank × Mx D B.rank t)} (hA : MeasurableSet A) :
    nuT hn I μ x₀ A = ∫⁻ k : I.l.K, sA hn I μ x₀ A (k : GA D B) ∂I.νK := by
  have := sigmaFinite_parameter_product_measure I μ hμ
  unfold nuT
  rw [Measure.map_apply (measurable_pi hn I x₀) hA, Measure.prod_apply (measurable_pi hn I x₀ hA)]
  refine lintegral_congr fun k => ?_
  exact (rho_apply hn I μ x₀ (measurable_ac B (k : GA D B)⁻¹ hA)).symm

theorem nuT_map_ac (hQ : QK) (hL : Law) (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n)
    (I : IkD d n) (μ : Measure (Mx D W.rank t)) (hμ : μ.IsAddHaarMeasure) (x₀) (h : GA D B) :
    (nuT hn I μ x₀).map (fun z => (mm (mt B h) z.1, mm (mt B h) z.2)) = nuT hn I μ x₀ := by
  change (nuT hn I μ x₀).map (ac B h) = nuT hn I μ x₀
  refine Measure.ext fun A hA => ?_
  have hA' : MeasurableSet (ac B h ⁻¹' A) := measurable_ac B h hA
  rw [Measure.map_apply (measurable_ac B h) hA, nuT_apply hn I μ hμ x₀ hA', nuT_apply hn I μ hμ x₀ hA]
  have key := hQ D t B W d I.l I.good I.νK I.haarK (sA hn I μ x₀ A) (measurable_sA hn I μ hμ x₀ hA)
    (fun q x => sA_stab hL hn I μ hμ x₀ hA q x) h⁻¹
  rw [← key]
  refine lintegral_congr fun k => ?_
  unfold sA
  congr 1
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_preimage, ← ac_mul, mul_inv_rev, inv_inv]

end GlobalTheory.CompanionTheory.ColumnSplitting.InvU

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairEmbeddingStatement
section
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_embedding : GlobalTheory.CompanionTheory.EGlue.PairSlices → GlobalTheory.CompanionTheory.EGlue.PairStep₁ → GlobalTheory.CompanionTheory.EGlue.PairStep₂ → GlobalTheory.CompanionTheory.EGlue.PairEmb := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.pairEmb_of_steps | exact GlobalTheory.CompanionTheory.EGlue.pairEmb_of_steps | (intros; apply GlobalTheory.CompanionTheory.EGlue.pairEmb_of_steps <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairFiniteDimensionalStatement
section
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_finite_dimensional : GlobalTheory.CompanionTheory.EGlue.PairFD := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.pairFD_holds | exact GlobalTheory.CompanionTheory.EGlue.pairFD_holds | (intros; apply GlobalTheory.CompanionTheory.EGlue.pairFD_holds <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairInvolutionContinuous
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.LocalHypotheses

theorem thetaGL_id_mem {E : Type} [Field E] [NumberField E] (n : ℕ) (w : Pl E) {g : GLw n w}
    (hg : g ∈ GlobalTheory.LFun.KGL w n) : thetaGL n (RingHom.id _) g ∈ GlobalTheory.LFun.KGL w n := by
  have hid : GeneralLinearGroup.map (RingHom.id (w.adicCompletion E)) g = g :=
    Units.ext (Matrix.ext fun _ _ => rfl)
  change PhiU n _ * invT n _ (GeneralLinearGroup.map (RingHom.id _) g) * (PhiU n _)⁻¹ ∈ _
  exact mul_mem (mul_mem (GlobalTheory.ThetaSatake.phiU_mem _ n)
    (GlobalTheory.BCT.LocGlue.intst E n w w (RingHom.id _) (fun _ => rfl) g hg))
    (inv_mem (GlobalTheory.ThetaSatake.phiU_mem _ n))

theorem sgP_facts : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (w : Pl E),
    Continuous (sgP a b w) ∧ (∀ g, sgP a b w (sgP a b w g) = g) ∧
      ∀ k ∈ K2 (E := E) a b w, sgP a b w k ∈ K2 (E := E) a b w := by
  intro E _ _ a b w
  refine ⟨?_, ?_, ?_⟩
  · exact (GlobalTheory.LocTwist.continuous_thetaGL a (RingHom.id _) continuous_id).prodMap
      (GlobalTheory.LocTwist.continuous_thetaGL b (RingHom.id _) continuous_id)
  · rintro ⟨g₁, g₂⟩
    exact Prod.ext (GlobalTheory.LocTwist.thetaGL_thetaGL a (RingHom.id _) (fun _ => rfl) g₁)
      (GlobalTheory.LocTwist.thetaGL_thetaGL b (RingHom.id _) (fun _ => rfl) g₂)
  · rintro ⟨k₁, k₂⟩ hk
    exact ⟨thetaGL_id_mem a w hk.1, thetaGL_id_mem b w hk.2⟩

end GlobalTheory.CompanionTheory.LocalHypotheses

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSlicesStatement
section
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_slices : GlobalTheory.CompanionTheory.EGlue.PairSlices := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.pairSlices | exact GlobalTheory.CompanionTheory.EGlue.pairSlices | (intros; apply GlobalTheory.CompanionTheory.EGlue.pairSlices <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodUnipotentOfParts
section
noncomputable section

open MeasureTheory Complex Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.PerUAssembled

def rtEquiv (g : GL (Fin 3) ℝ) : M23 ≃L[ℝ] M23 :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun X => Matrix.of.symm (Matrix.of X * (g : Matrix (Fin 3) (Fin 3) ℝ))
      map_add' := fun X Y => by
        have : Matrix.of (X + Y) = Matrix.of X + Matrix.of Y := rfl
        rw [this, Matrix.add_mul]
        rfl
      map_smul' := fun c X => by
        have : Matrix.of (c • X) = c • Matrix.of X := rfl
        rw [this, Matrix.smul_mul]
        rfl
      invFun := fun X => Matrix.of.symm (Matrix.of X * ((g⁻¹ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ))
      left_inv := fun X => by
        simp [Matrix.mul_assoc]
      right_inv := fun X => by
        simp [Matrix.mul_assoc] }

theorem rtEquiv_apply (g : GL (Fin 3) ℝ) (X : M23) :
    rtEquiv g X = Matrix.of.symm (Matrix.of X * (g : Matrix (Fin 3) (Fin 3) ℝ)) := rfl

def rtS (g : GL (Fin 3) ℝ) (Φ : Sw) : Sw :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rtEquiv g) Φ

theorem rtS_coe (g : GL (Fin 3) ℝ) (Φ : Sw) : (rtS g Φ : M23 → ℂ) = B.rt g Φ := by
  funext X
  simp [rtS, B.rt, rtEquiv_apply]

theorem schwartz_bounds (f : Sw) (n : ℕ) :
    ∃ C : ℝ, ∀ m ≤ n, ∀ X : M23, (1 + ‖X‖) ^ n * ‖iteratedFDeriv ℝ m f X‖ ≤ C :=
  ⟨2 ^ n * (Finset.Iic (n, n)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) f, fun m hm X =>
    SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (n, n)) le_rfl hm f X⟩

theorem ae_det_ne_zero : ∀ᵐ h : M22, (Matrix.of h).det ≠ 0 := by
  rw [ae_iff]
  have h : volume {h : M22 | (Matrix.of h).det = 0} = 0 := GlobalTheory.CompanionTheory.GodementNull.dNull
  simpa using h

theorem perU : UnipotentSubstitution → UnipotentJointIntegrability → UnipotentTateFunctionalEquation → PuBound → PerU := by
  intro h1 h2 h3 h4 k hk Φ δ s hs0 hs1 u
  obtain ⟨C, M, hb⟩ := h4 k hk Φ δ s hs0 hs1
  have hI := (hb u).1
  refine ⟨hI, ?_⟩
  let G : M22 → ℂ := fun h => Wm k (Matrix.of h)⁻¹ * sg (Matrix.of h).det *
    ((|(Matrix.of h).det| ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)
  let Ψ : M23 → ℂ := B.rt (cyc u) Φ
  let F : ℝˣ → M22 → ℂ := fun t h => chR δ s t * sg t * (((|(t : ℝ)|)⁻¹ : ℝ) : ℂ) *
    (G h * B.innB Ψ h (t : ℝ)⁻¹)
  have hsm : ContDiff ℝ (⊤ : ℕ∞) Ψ := by
    have := (rtS (cyc u) Φ).smooth ⊤
    rw [rtS_coe] at this
    exact this
  have hbd : ∀ n : ℕ, ∃ C : ℝ, ∀ m ≤ n, ∀ X : M23, (1 + ‖X‖) ^ n * ‖iteratedFDeriv ℝ m Ψ X‖ ≤ C := by
    intro n
    have := schwartz_bounds (rtS (cyc u) Φ) n
    rw [rtS_coe] at this
    exact this
  have e1 : ∀ t : ℝˣ, sec k Φ (mm t u) * chR δ s t = ∫ h, F t h := by
    intro t
    simp only [F]
    rw [h1 k hk Φ t u, integral_const_mul]
    ring
  have e2 : ∫ t, (∫ h, F t h) ∂mulR = ∫ h, (∫ t, F t h ∂mulR) :=
    integral_integral_swap (h2 k hk Φ δ s hs0 hs1 u)
  have e3 : ∀ᵐ h : M22, ∫ t, F t h ∂mulR =
      cr (!δ) 0 (-1) * gT (!δ) s * ∫ x, pI k Φ δ s u (h, x) := by
    filter_upwards [ae_det_ne_zero] with h hdet
    have hF : ∀ t : ℝˣ, F t h = G h * (chR δ s t * sg t * (((|(t : ℝ)|)⁻¹ : ℝ) : ℂ) *
        B.innB Ψ h (t : ℝ)⁻¹) := fun t => by
      simp only [F]
      ring
    simp only [hF]
    rw [integral_const_mul, h3 Ψ δ s hs0 hs1 hsm hbd h hdet]
    have hp : ∀ x : Fin 2 → ℝ, pI k Φ δ s u (h, x) =
        G h * (cr (!δ) (s - 1) (x 1) * Ψ (Matrix.of.symm (Matrix.of h * blk x))) := fun x => by
      simp only [pI, G, Ψ, B.rt, Equiv.apply_symm_apply]
      ring
    simp only [hp]
    rw [integral_const_mul]
    ring
  calc ∫ t, sec k Φ (mm t u) * chR δ s t ∂mulR
      = ∫ t, (∫ h, F t h) ∂mulR := integral_congr_ae (Filter.Eventually.of_forall e1)
    _ = ∫ h, (∫ t, F t h ∂mulR) := e2
    _ = ∫ h : M22, cr (!δ) 0 (-1) * gT (!δ) s * ∫ x, pI k Φ δ s u (h, x) := integral_congr_ae e3
    _ = cr (!δ) 0 (-1) * gT (!δ) s * Pu k Φ δ s u := by
      rw [integral_const_mul, Pu, Measure.volume_eq_prod, integral_prod _ hI]

end GlobalTheory.CompanionTheory.PerUAssembled
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdCloseStatement
section
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_facts_alt : GlobalTheory.CompanionTheory.EGlue.MCloseFacts := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.mCloseFacts_holds | exact GlobalTheory.CompanionTheory.EGlue.mCloseFacts_holds | (intros; apply GlobalTheory.CompanionTheory.EGlue.mCloseFacts_holds <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLengthStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_irreducible_finite_length : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), HasFiniteLength (prodIrr x hd) := by
  first | exact @GlobalTheory.CompanionTheory.ProdFL.main | exact GlobalTheory.CompanionTheory.ProdFL.main | (intros; apply GlobalTheory.CompanionTheory.ProdFL.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductMeasureStatementStatement
section
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_measure_statement : ProdMeas := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.ProdMeasPf.prodMeas | exact GlobalTheory.CompanionTheory.ThTot.ProdMeasPf.prodMeas | (intros; apply GlobalTheory.CompanionTheory.ThTot.ProdMeasPf.prodMeas <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductThetaOfSchwartzTensorStatement
section
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_theta_of_schwartz_tensor : SchwTensor → ProdTh := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.ProductTheta.prodTh_of_schwTensor | exact GlobalTheory.CompanionTheory.ThTot.ProductTheta.prodTh_of_schwTensor | (intros; apply GlobalTheory.CompanionTheory.ThTot.ProductTheta.prodTh_of_schwTensor <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackCoverStarCompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section

namespace GlobalTheory.CompanionTheory.OmGlobPush

theorem push_kc : ∀ {K : Type} [CommRing K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K))
    (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι)
    (hτ : ∀ n (i : Fin (n + 1) → U.ι), capO U.U i ≤ u ⁻¹ᵁ capO W.U (τ ∘ i)) (a : ℕ),
    ∃ hG : ∀ T, KC q U a T → KC p W a ((pullM u hu a).G.obj T),
      ∀ α T, Vk q U a α T → Vk p W a (τ α) ((morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).G.obj T) := by
  intro K _ X Y q p u hu U W τ hτ a
  have key : ∀ (T : GlobalTheory.LogCris.Thick (CrystallineSemistableComparison.smFun X q)) (α : U.ι),
      CrystallineSemistableComparison.Pb.InU (U.U α) T → CrystallineSemistableComparison.Pb.InU (W.U (τ α)) ((pullM u hu a).G.obj T) := by
    intro T α h
    have h0 : U.U α ≤ u ⁻¹ᵁ W.U (τ α) := by
      have h1 := hτ 0 (fun _ => α)
      simpa [CrystallineSemistableComparison.Pb.capO] using h1
    unfold CrystallineSemistableComparison.Pb.InU at h ⊢
    change ⊤ ≤ (TopologicalSpace.Opens.map (pt T ≫ u).base).obj (W.U (τ α))
    exact h.trans ((TopologicalSpace.Opens.map (pt T).base).monotone h0)
  have ktf : ∀ (T : GlobalTheory.LogCris.Thick (CrystallineSemistableComparison.smFun X q)),
      CrystallineSemistableComparison.Pb.TF 1 (a + 1) T → CrystallineSemistableComparison.Pb.TF 1 (a + 1) ((pullM u hu a).G.obj T) := by
    intro T h
    exact h
  refine ⟨fun T hT => ?_, fun α T hT => ?_⟩
  · obtain ⟨hTF, V, ⟨α, rfl⟩, hV⟩ := hT
    exact ⟨ktf T hTF, W.U (τ α), ⟨τ α, rfl⟩, key T α hV⟩
  · exact key T.obj α hT

end GlobalTheory.CompanionTheory.OmGlobPush
end
end

