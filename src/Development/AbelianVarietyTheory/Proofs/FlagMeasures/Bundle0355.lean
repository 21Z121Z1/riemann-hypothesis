import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0346
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdmissibleFamilySatisfiesRowEstimates
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0347
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0348
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Formalism.PeriodIntegrals.Bundle0008
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0104
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0303
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0352
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0335
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0349
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingReindex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0278
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeLipschitzProperties
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0015
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0343
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0311

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicColumnLatticeEqSpanPartTransportedFrameStatement
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → (∀ x, x ∈ hat D.host.F (Mq wt) ↔ embA X wt ιA x ∈ X.B.I.Lf) ∧ (∀ x y, ιA (hA X.B.I (embA X wt ιA x) (embA X wt ιA y)) = hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F) x y) ∧ Function.Injective (embA X wt ιA) ∧ (∀ x a, hA X.B.I (incl X.B.I (X.eR a)) (embA X wt ιA x) = 0 ∧ hA X.B.I (incl X.B.I (X.fR a)) (embA X wt ιA x) = 0) ∧ (∀ x, hA X.B.I (incl X.B.I (X.zR u)) (embA X wt ιA x) = 0) ∧ ∀ (h : Hfin X u) (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)), RepF X wt ιA (h : X.B.I.Gf) y → ∀ x, X.B.I.fmat (h : X.B.I.Gf) *ᵥ embA X wt ιA x = embA X wt ιA (y.1.1 *ᵥ x) := by
  first | exact @GlobalTheory.St.G.MHat.mhat_coords | exact GlobalTheory.St.G.MHat.mhat_coords | (intros; apply GlobalTheory.St.G.MHat.mhat_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdmissibleFamilySatisfiesRowEstimatesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.BridgeLemma₂ Formalism.L2.SG.RowsU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_family_satisfies_row_estimates : ∀ (eps : ℝ) (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)) (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1) (Cg cb Cu cT CT C0 A : ℝ), VanishingOnXAndXPlus.FamilyRowsExist Fm → VanishingOnXAndXPlus.admF6 Fm Cg cb Cu cT CT C0 → VanishingOnXAndXPlus.admF7 Fm Cg cb Cu cT CT C0 → VanishingOnXAndXPlus.admF8 Fm Cg cb Cu cT CT C0 A → VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0 → rows_TiesF Fm C1 X Y → (∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairTermInjective (X x hx i) (Y x hx i u u')) → (∀ x (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word), wordPairBetaLattice (Fm.D x i) u u') → ∀ U : UC, UAdm Fm C1 X Y Cg cb Cu cT CT C0 A U → ∀ C ≥ c0U CT A C0 Fm.CGam U, OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) u u', Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A → RowsND (X x hx i) (Y x hx i u u') C ∧ RowsDeg (X x hx i) (Y x hx i u u') C ∧ RowsOne (X x hx i) (Y x hx i u u') C := by
  first | exact @GlobalTheory.RowsFive.rows_three_bounds | exact GlobalTheory.RowsFive.rows_three_bounds | (intros; apply GlobalTheory.RowsFive.rows_three_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ArchimedeanDensityProductTestFunctionAtSignStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_density_product_testFunction_at_sign : ∀ (I : AutInst) (θ : InfinitePlace I.F → (Ainf I.F ⊗[I.F] I.E →+* ℂ)), (∀ v, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) (θ v)) → ∀ (lamv : InfinitePlace I.F → ℝ) (χ : Ainf I.F → ℂ), (∀ v, lamv v ≠ 0) → (∀ x, χ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ v, lamv v * (θ v (x ⊗ₜ[I.F] (1 : I.E))).re : ℝ) : ℂ))) → ∀ (μi : Measure (Fin 1 → Fin I.n → Ainf I.F ⊗[I.F] I.E)) (νi : Measure (Ainf I.F)), SelfDual μi (fun X Y => χ (BR (Ainf I.F) I.cm.sig I.J X Y)) → SelfDual νi (fun s t => χ (s * t)) → ∀ (φ : InfinitePlace I.F → (Fin I.n → ℂ) → ℝ) (D : InfinitePlace I.F → ℝ → ℝ), (∀ v, Continuous (φ v) ∧ HasCompactSupport (φ v) ∧ IsDens (I.ε v) (φ v) (D v)) → ∀ Fi : Ainf I.F → ℂ, IsContDensityOn μi (fun X => qR (Ainf I.F) I.cm.sig I.J (X 0)) id νi {c | IsUnit c} (fun X => ((∏ v, φ v ((I.P v)⁻¹ *ᵥ fun i => θ v (X 0 i)) : ℝ) : ℂ)) Fi → ∀ s : Bool, Fi (sgn (Ainf I.F) s) = ((∏ v, 2 ^ I.n * |lamv v| ^ ((I.n : ℝ) - 1 / 2) * D v (sgn ℝ s) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.GaussMean.RealDensityCc.density_at_sign | exact GlobalTheory.GaussMean.RealDensityCc.density_at_sign | (intros; apply GlobalTheory.GaussMean.RealDensityCc.density_at_sign <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphicKernelConvergencePropertiesStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphicKernel_convergence_properties : KernelA := by
  first | exact @GlobalTheory.KernelConv.kernelA | exact GlobalTheory.KernelConv.kernelA | (intros; apply GlobalTheory.KernelConv.kernelA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelSchurOfFormalDegreeDensityStatement
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselModel_schur_of_formalDegree_density : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (ε : Fin (2 * r + k + 1) → Bool) (cd : Formalism.BasicNotions.CDHaar) (sc : NNReal) (P : Mat k r) (d c : ℝ) (μG : Measure (Mt k r)), (∀ (p q : ℕ) (e : Fin p ⊕ Fin q ≃ Fin (2 * r + k + 1)), (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) → ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A → ((sc : ℝ≥0∞) • Formalism.REAL.muG ε) A = cd.cd p q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}) → IsCayley k r ε P → IsFdeg ((sc : ℝ≥0∞) • Formalism.REAL.muG ε) (fun g => σ (P⁻¹ * g * P)) d → 0 < c → IsHaarOn (GG k r) μG → HasDens (GG k r) μG (ENNReal.ofReal c) → SchurH μG σ (d / (c * volUn (2 * r + k + 1))) := by
  first | exact @GlobalTheory.FdegDens.schur_of_dens | exact GlobalTheory.FdegDens.schur_of_dens | (intros; apply GlobalTheory.FdegDens.schur_of_dens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassificationOfSpecialUnitaryStatement
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classification_of_special_unitary : ∀ (n : ℕ), 1 ≤ n → ∀ ε : Fin n → Bool, ClassS ε → ClassF ε := by
  first | exact @GlobalTheory.SUtoU.classF_of_classS | exact GlobalTheory.SUtoU.classF_of_classS | (intros; apply GlobalTheory.SUtoU.classF_of_classS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryIntoStepZeroForms
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

theorem colDictInto_of_levelMatch : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (Tr : Transport X u F) (hK : X.LevelSubgroupCharacter), (∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a)) → LevelMatch X Tr hK → ColDictInto X Tr hK := by
  intro D X u F Tr hK hσ hL T
  have hW : WittX X u Tr.wt := ⟨Tr.wt_isom, Tr.wt_e, Tr.wt_f, Tr.weight_z⟩
  have hA : IsAdeleIso X Tr.ιA := ⟨Tr.ιA_rat, Tr.ιA_int⟩
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.frameAction_mulEquiv_finiteAdelic_unitary D X u Tr.wt Tr.ιA hW hA hσ
  obtain ⟨-, hΓ, hsT⟩ := GlobalTheory.T.transport_rational_points_stabiliser_frame D X u Tr.wt Tr.ιA hW hA Φ hΦ
  obtain ⟨hψ, -, hφ, -, -⟩ := cols_sharp_dictionary D X u hK
  have key := GlobalTheory.adForms_of_equivariant D.host.F D.host.E (Formalism.L2.Forms.sigD D) (D.R.N 0)
    (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) _ _ _ F.cls0.lev (Gam X u) (Hinf X u) (Hfin X u)
    (iotaI X u) (iotaF X u) (Ku X u hK) (psiK X u hK) Φ Tr.h0 D.what₂.Tau (Formalism.L2.Forms.embT D)
    ((D.fm u).lam 0) (X.Vpi u) (piRep X u) Tr.J hψ
    (fun h => (hL.2 h (Φ h) ((hΦ h (Φ h)).2 rfl)).1)
    (fun h hk hy => (hL.2 h (Φ h) ((hΦ h (Φ h)).2 rfl)).2 hk hy)
    hΓ
    (fun γ g hγ ξ y y' hy => Tr.J_eqv _ (iotaI X u γ).2 ξ y y' (by rw [hsT γ g hγ]; exact hy))
    (fun ξ => by rw [← Formalism.L2.Forms.lamT_zero]; exact Tr.J_val ξ)
    (shP X u T.1) (hφ T)
  rw [Formalism.L2.Forms.Mu0_iff F.val0]
  refine ⟨_, key, ?_⟩
  funext c z
  have hc : Φ.symm (F.cls0.y c * Tr.h0⁻¹) = Tr.hc c :=
    Φ.symm_apply_eq.2 ((hΦ (Tr.hc c) _).1 (Tr.hc_rep c)).symm
  simp only [Formalism.L2.Forms.res, LinearMap.funLeft_apply, hc]
  show Tr.J (shP X u T.1 (Tr.hc c)) z = Tr.J (shP X u T.1 (Tr.hc c)) (F.val0.eY (F.val0.eY.symm z))
  rw [Equiv.apply_symm_apply]

end GlobalTheory.St
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeIntegralUnipotentRadicalRealPointsStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_integral_unipotentRadical_real_points : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → IsHermND σ J → GlobalTheory.SgGlob.SelfDual (σ : E →+* E) J Λ → IsFrame (σ : E →+* E) J (algebraMap F E T) P → IsDual (σ : E →+* E) J P f → tupLat (id1 E r) (sideM P f) ≤ Λ → IsModelAt J A → (∀ a, 0 < s a) → Adapted A P f s → AllSome (IsDomN (σ : E →+* E) J Λ P A) fun 𝓓 => Measure.pi (fun _ : InfinitePlace E => haarLie (Nset k r) 1) 𝓓 = ENNReal.ofReal (|(NumberField.discr F : ℝ)| ^ (-(((k : ℝ) + 1) * (r : ℝ) ^ 2) - 4 * ((r : ℝ) ^ 3 - r) / 3 - 3 * (r : ℝ) / 2) * (∏ a : Fin r, s a ^ (4 * (r - (a : ℕ)) + 2 * k)) ^ Fintype.card (InfinitePlace E)) := by
  first | exact @GlobalTheory.SnMass.VolN.covolume_N | exact GlobalTheory.SnMass.VolN.covolume_N | (intros; apply GlobalTheory.SnMass.VolN.covolume_N <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivativeClosedClassBoundedByInverseLeastSize
section
open MeasureTheory NumberField Matrix Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

namespace GlobalTheory.SobolevBound

private lemma exists_re_trace_orthonormal_gLie {n : ℕ} (ε : Fin n → Bool) :
    ∃ E : Fin (n ^ 2) → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε,
      ∀ i j, (((E i : Matrix (Fin n) (Fin n) ℂ) * (E j : Matrix (Fin n) (Fin n) ℂ)ᴴ).trace).re =
        if i = j then 1 else 0 := by

  classical
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := Formalism.REAL.Jm_conjTranspose ε
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJJ' : ∀ M : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hmem : ∀ X : Matrix (Fin n) (Fin n) ℂ,
      X ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε ↔ Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := fun X => Iff.rfl

  have hA : ∀ Z : Matrix (Fin n) (Fin n) ℂ,
      Z - Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε := by
    intro Z
    rw [hmem]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hJh, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hJJ, Matrix.mul_one, hJJ']
    abel
  have hB : ∀ Z : Matrix (Fin n) (Fin n) ℂ,
      Complex.I • (Z + Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε) ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε := by
    intro Z
    rw [hmem]
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hJh, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hJJ,
      Matrix.mul_one, hJJ', smul_mul_assoc, mul_smul_comm, Complex.star_def, Complex.conj_I, neg_smul,
      smul_add, neg_mul]
    abel
  let L : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε × GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun p => (p.1 : Matrix (Fin n) (Fin n) ℂ) + Complex.I • (p.2 : Matrix (Fin n) (Fin n) ℂ)
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]
        abel
      map_smul' := fun r p => by
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, RingHom.id_apply, smul_add]
        rw [smul_comm r Complex.I] }
  have hsurj : Function.Surjective L := by
    intro Z
    refine ⟨(⟨(2⁻¹ : ℝ) • (Z - Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε),
      (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε).smul_mem _ (hA Z)⟩,
      ⟨(-2⁻¹ : ℝ) • (Complex.I • (Z + Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε)),
      (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε).smul_mem _ (hB Z)⟩), ?_⟩
    change (2⁻¹ : ℝ) • (Z - Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε) +
      Complex.I • ((-2⁻¹ : ℝ) • (Complex.I • (Z + Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε))) = Z
    generalize Formalism.REAL.Jm ε * Zᴴ * Formalism.REAL.Jm ε = W
    ext a b
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    linear_combination (-(1 : ℂ) / 2 * (Z a b + W a b)) * Complex.I_sq
  have hfin : n ^ 2 ≤ Module.finrank ℝ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε) := by
    have h1 := LinearMap.finrank_le_finrank_of_surjective hsurj
    rw [Module.finrank_prod, Module.finrank_matrix, Fintype.card_fin, Complex.finrank_real_complex] at h1
    nlinarith [h1]

  let Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin n × Bool) :=
    { toFun := fun X => WithLp.toLp 2 (fun q => if q.2.2 then (X q.1 q.2.1).re else (X q.1 q.2.1).im)
      map_add' := fun X Y => by
        ext q
        by_cases h : q.2.2 <;> simp [h]
      map_smul' := fun r X => by
        ext q
        by_cases h : q.2.2 <;> simp [h] }
  have hΦapp : ∀ X q, (Φ X) q = if q.2.2 then (X q.1 q.2.1).re else (X q.1 q.2.1).im := fun _ _ => rfl
  have hΦ : ∀ X Y, inner ℝ (Φ X) (Φ Y) = ((X * Yᴴ).trace).re := by
    intro X Y
    rw [PiLp.inner_apply]
    simp only [hΦapp, Fintype.sum_prod_type, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
      Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hΦinj : Function.Injective Φ := by
    intro X Y h
    ext a b
    apply Complex.ext
    · have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin n × Fin n × Bool) => v (a, b, true)) h
      simpa [hΦapp] using h1
    · have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin n × Fin n × Bool) => v (a, b, false)) h
      simpa [hΦapp] using h1
  let Ψ := Φ ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε).subtype
  have hΨ : Function.Injective Ψ := by
    intro x y h
    apply Subtype.ext
    apply hΦinj
    simpa [Ψ] using h
  have hS : n ^ 2 ≤ Module.finrank ℝ (LinearMap.range Ψ) := by
    rw [LinearMap.finrank_range_of_inj hΨ]
    exact hfin
  let b := stdOrthonormalBasis ℝ (LinearMap.range Ψ)
  have hbo : Orthonormal ℝ (fun i => ((b i : LinearMap.range Ψ) : EuclideanSpace ℝ (Fin n × Fin n × Bool))) :=
    b.orthonormal.comp_linearIsometry (LinearMap.range Ψ).subtypeₗᵢ
  have hpre : ∀ i, ∃ X : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie ε, Φ (X : Matrix (Fin n) (Fin n) ℂ) = b i := by
    intro i
    obtain ⟨X, hX⟩ := LinearMap.mem_range.1 (b i).2
    exact ⟨X, by simpa [Ψ] using hX⟩
  choose X hX using hpre
  refine ⟨fun j => X (Fin.castLE hS j), fun i j => ?_⟩
  dsimp only
  rw [← hΦ, hX, hX]
  have h2 := orthonormal_iff_ite.1 hbo (Fin.castLE hS i) (Fin.castLE hS j)
  rw [h2]
  simp

theorem derivative_closed_class_bound : ∀ (B : RowsAut), 1 ≤ B.I.n → 1 ≤ B.g → ∃ m : ℕ, ∀ W : Set (B.I.GA → ℂ), (∀ f ∈ W, (∃ F, GlobalTheory.Dec.IsContRep B F f) ∧ (∀ k ∈ B.I.Kg B.g, ∀ y, f (y * (1, k)) = f y) ∧ ∀ (v : InfinitePlace B.I.F) (E : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.gLie (B.I.ε v)), ∃ f' ∈ W, ∀ y, HasDerivAt (fun t : ℝ => f (y * GlobalTheory.SobolevBound.onePar B (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.atPlace B v E) t)) (f' y) 0) → ∀ f ∈ W, ∃ C : ℝ, ∀ y, ‖f y‖ ≤ C * (GlobalTheory.Count.tau1 B.I y)⁻¹ ^ m := by
  intro B hn hg
  classical
  refine ⟨2 * (B.I.n ^ 2 * B.I.f), ?_⟩
  intro W hW f hf

  choose E hE using fun v : InfinitePlace B.I.F => exists_re_trace_orthonormal_gLie (B.I.ε v)
  choose c hc using fun v : InfinitePlace B.I.F => GlobalTheory.GaugeConst.gauge_exists_pos_unique B.I.n (B.I.ε v)
  let e : Fin (Fintype.card (InfinitePlace B.I.F)) ≃ InfinitePlace B.I.F :=
    (Fintype.equivFin (InfinitePlace B.I.F)).symm

  have hnr : (1 : ℝ) ≤ B.I.n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < B.I.n := by linarith
  have hp5 : (0 : ℝ) < (B.I.n : ℝ) ^ 5 := pow_pos hn0 5
  have h35 : (B.I.n : ℝ) ^ 3 ≤ (B.I.n : ℝ) ^ 5 := pow_le_pow_right₀ hnr (by norm_num)
  have hden : (0 : ℝ) < 12 * (B.I.n : ℝ) ^ 5 := by linarith
  have hs : (0 : ℝ) < 1 / (12 * (B.I.n : ℝ) ^ 5) := div_pos one_pos hden
  have h3 : 12 * (B.I.n : ℝ) ^ 3 * (1 / (12 * (B.I.n : ℝ) ^ 5)) ≤ 1 := by
    rw [mul_one_div, div_le_one hden]
    linarith
  have h5 : 8 * (B.I.n : ℝ) ^ 5 * (1 / (12 * (B.I.n : ℝ) ^ 5)) ≤ 1 := by
    rw [mul_one_div, div_le_one hden]
    linarith
  obtain ⟨C0, hC0, hsob⟩ := GlobalTheory.sobolev_iterated_one_parameter_subgroups_words B.I.GA
    (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2)
    (fun l => onePar B (atPlace B (e l.divNat) (E _ l.modNat))) (1 / (12 * (B.I.n : ℝ) ^ 5)) hs
    (fun l => onePar_spec B _)

  have hder : ∀ g ∈ W, ∀ l : Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2), ∃ g' ∈ W, ∀ y,
      HasDerivAt (fun t : ℝ => g (y * onePar B (atPlace B (e l.divNat) (E _ l.modNat)) t)) (g' y) 0 :=
    fun g hgW l => (hW g hgW).2.2 (e l.divNat) (E _ l.modNat)
  choose! D hDW hD using hder
  let F : List (Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2)) → B.I.GA → ℂ :=
    fun l => l.foldr (fun i g => D g i) f
  have hFW : ∀ l, F l ∈ W := by
    intro l
    induction l with
    | nil => exact hf
    | cons i l ih => exact hDW _ ih i
  have hrep : ∀ l, ∃ Fv, GlobalTheory.Dec.IsContRep B Fv (F l) := fun l => (hW (F l) (hFW l)).1
  choose Fv hFv using hrep

  set Mx : ℝ := ∑ k ∈ Finset.range ((Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) + 1), ∑ w : Fin k → Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2), ‖Fv (List.ofFn w)‖ ^ 2 with hMx
  have hMx0 : 0 ≤ Mx := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hle : ∀ l : List (Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2)), l.length ≤ (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) → ‖Fv l‖ ^ 2 ≤ Mx := by
    intro l hl
    calc ‖Fv l‖ ^ 2 = ‖Fv (List.ofFn l.get)‖ ^ 2 := by rw [List.ofFn_get]
      _ ≤ ∑ w : Fin l.length → Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2), ‖Fv (List.ofFn w)‖ ^ 2 :=
          Finset.single_le_sum (f := fun w : Fin l.length → Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) => ‖Fv (List.ofFn w)‖ ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ _)
      _ ≤ Mx :=
          Finset.single_le_sum (f := fun k => ∑ w : Fin k → Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2), ‖Fv (List.ofFn w)‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
            (Finset.mem_range.2 (Nat.lt_succ_of_le hl))
  have hP : 0 ≤ ∏ v, c v := Finset.prod_nonneg fun v _ => (hc v).1.le
  set K : ℝ := Real.exp B.I.f * (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal with hK
  have hK0 : 0 ≤ K := div_nonneg (mul_nonneg (Real.exp_pos _).le hP) ENNReal.toReal_nonneg
  set a : ℝ := 4 * Real.sqrt B.I.n with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  set p := 2 * (B.I.n ^ 2 * B.I.f) with hp
  refine ⟨Real.sqrt (C0 * K * Mx * (1 + a) ^ p), fun y => ?_⟩
  have hτ : 0 < tau1 B.I y := GlobalTheory.TauLipschitz.trunc_pos B.I hn y
  have hτ1 : tau1 B.I y ≤ 1 := by
    have : tau1 B.I y ≤ 1 / 2 := by
      unfold GlobalTheory.Count.tau1
      exact min_le_left _ _
    linarith
  have hu0 : 0 < (tau1 B.I y)⁻¹ := inv_pos.2 hτ
  have hu1 : 1 ≤ (tau1 B.I y)⁻¹ := by
    have h1 := mul_le_mul_of_nonneg_right hτ1 hu0.le
    rw [mul_inv_cancel₀ hτ.ne', one_mul] at h1
    exact h1
  have hu2 : 1 ≤ ((tau1 B.I y)⁻¹) ^ 2 := by nlinarith
  have hfrac : a / tau1 B.I y ^ 2 = a * ((tau1 B.I y)⁻¹) ^ 2 := by rw [div_eq_mul_inv, inv_pow]
  have hbase : 1 + a / tau1 B.I y ^ 2 ≤ (1 + a) * ((tau1 B.I y)⁻¹) ^ 2 := by
    rw [hfrac]
    nlinarith
  have hX1 : 0 ≤ 1 + a / tau1 B.I y ^ 2 := by
    have := div_nonneg ha0 (sq_nonneg (tau1 B.I y))
    linarith
  have hpow : (1 + a / tau1 B.I y ^ 2) ^ p ≤ (1 + a) ^ p * (((tau1 B.I y)⁻¹) ^ p) ^ 2 := by
    calc (1 + a / tau1 B.I y ^ 2) ^ p ≤ ((1 + a) * ((tau1 B.I y)⁻¹) ^ 2) ^ p :=
          pow_le_pow_left₀ hX1 hbase p
      _ = (1 + a) ^ p * (((tau1 B.I y)⁻¹) ^ p) ^ 2 := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 p]

  have hcube : ∀ l : List (Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2)), l.length ≤ (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) →
      ∫ t in Set.pi Set.univ (fun _ : Fin (Fintype.card (InfinitePlace B.I.F) * B.I.n ^ 2) => Set.Icc (0 : ℝ) (1 / (12 * (B.I.n : ℝ) ^ 5))),
        ‖F l (y * (List.ofFn fun i => onePar B (atPlace B (e i.divNat) (E _ i.modNat)) (t i)).prod)‖ ^ 2 ≤
        K * (1 + a / tau1 B.I y ^ 2) ^ p * Mx := by
    intro l hl
    have h1 := cube_bound B c (1 / (12 * (B.I.n : ℝ) ^ 5)) e E hn hg (fun v => (hc v).2.1) hE hs h3 h5
      (Fv l) (F l) (hFv l) (hW (F l) (hFW l)).2.1 y
    have h2 : Real.exp B.I.f * (1 + 4 * Real.sqrt B.I.n / tau1 B.I y ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) *
        (∏ v, c v) / (B.μf (B.I.Kg B.g)).toReal = K * (1 + a / tau1 B.I y ^ 2) ^ p := by
      rw [hK, ha, hp]
      ring
    rw [h2] at h1
    refine h1.trans ?_
    have hX0 : 0 ≤ K * (1 + a / tau1 B.I y ^ 2) ^ p := mul_nonneg hK0 (pow_nonneg hX1 _)
    exact mul_le_mul_of_nonneg_left (hle l hl) hX0
  have hmain := hsob F (fun l => (hFv l).1) (fun l i x => hD (F l) (hFW l) i x) y
    (K * (1 + a / tau1 B.I y ^ 2) ^ p * Mx) hcube
  have hsq : ‖f y‖ ^ 2 ≤ (Real.sqrt (C0 * K * Mx * (1 + a) ^ p) * ((tau1 B.I y)⁻¹) ^ p) ^ 2 := by
    have hA : 0 ≤ C0 * K * Mx * (1 + a) ^ p :=
      mul_nonneg (mul_nonneg (mul_nonneg hC0 hK0) hMx0) (pow_nonneg (by linarith) _)
    rw [mul_pow, Real.sq_sqrt hA]
    have hQ : 0 ≤ C0 * K * Mx := mul_nonneg (mul_nonneg hC0 hK0) hMx0
    calc ‖f y‖ ^ 2 ≤ C0 * (K * (1 + a / tau1 B.I y ^ 2) ^ p * Mx) := hmain
      _ = (C0 * K * Mx) * (1 + a / tau1 B.I y ^ 2) ^ p := by ring
      _ ≤ (C0 * K * Mx) * ((1 + a) ^ p * (((tau1 B.I y)⁻¹) ^ p) ^ 2) :=
          mul_le_mul_of_nonneg_left hpow hQ
      _ = C0 * K * Mx * (1 + a) ^ p * (((tau1 B.I y)⁻¹) ^ p) ^ 2 := by ring
  have hnn : 0 ≤ Real.sqrt (C0 * K * Mx * (1 + a) ^ p) * ((tau1 B.I y)⁻¹) ^ p :=
    mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hu0.le _)
  calc ‖f y‖ = Real.sqrt (‖f y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((Real.sqrt (C0 * K * Mx * (1 + a) ^ p) * ((tau1 B.I y)⁻¹) ^ p) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (C0 * K * Mx * (1 + a) ^ p) * (tau1 B.I y)⁻¹ ^ p := Real.sqrt_sq hnn

end GlobalTheory.SobolevBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryGroupModelsEquivStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_unitaryGroup_models_equiv : ∀ I : AutInst, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt I.F I.E I.cm.sig ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND I.cm.sig I.J ∧ ∃ T : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J ≃ₜ* I.GA, (∀ h, (show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J from h) ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J ↔ T h ∈ I.GFset) ∧ (∀ h, I.fmat (T h).2 = (Formalism.MainNotions.StandardLattice.finMat I.cm.sig I.J h).map (Algebra.TensorProduct.comm I.F _ _)) ∧ ∀ v θ, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) θ → ∀ h, uMat ((T h).1 v) = (I.P v)⁻¹ * Formalism.MainNotions.StandardLattice.infMat I.cm.sig I.J θ h * I.P v := by
  first | exact @GlobalTheory.AdelicModels.exists_adelic_equiv | exact GlobalTheory.AdelicModels.exists_adelic_equiv | (intros; apply GlobalTheory.AdelicModels.exists_adelic_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBesselCellGapConstantStatement
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_besselCell_gap_constant : ∃ Cgf : ℝ, ∀ (D : Formalism.BasicNotions.D7) (ε : Fin (2 * D.R.rS + D.R.k + 1) → Bool) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), Formalism.QuantumDeterminants.GapAtLeast ε lam (Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)) → ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h ∧ GlobalTheory.CellAmp.GapCell D.R.k D.R.rS h := by
  first | exact @GlobalTheory.GapConstant.gap_constant_exists | exact GlobalTheory.GapConstant.gap_constant_exists | (intros; apply GlobalTheory.GapConstant.gap_constant_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundamentalDomainMeasureEq
section
open MeasureTheory NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst)

namespace GlobalTheory.AdelicVol

theorem exists_fundamentalDomain_measure_eq (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    (fund : Set I.GA) (hfund : I.IsFundDom (I.muA μf) fund) :
    ∃ (μ : Measure (HA (AF I.F) I.cm.sig I.J)) (S : Set (HA (AF I.F) I.cm.sig I.J)), μ.IsHaarMeasure ∧
      IsFundamentalDomain (HFinIn (AF I.F) I.cm.sig I.J) S μ ∧ μ S = I.muA μf fund := by
  obtain ⟨-, -, T, hT, -, -⟩ := GlobalTheory.AdelicModels.exists_adelic_equiv I
  obtain ⟨Γ, hΓ, -, -, hdom⟩ := GlobalTheory.RatDiscrete.rational_points I
  have hF : IsFundamentalDomain Γ fund (I.muA μf) := hdom μf fund hfund
  haveI : BorelSpace (HA (AF I.F) I.cm.sig I.J) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA _ _
  haveI : IsTopologicalGroup (HA (AF I.F) I.cm.sig I.J) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : SecondCountableTopology I.Gf := (GlobalTheory.CongTop.adelic_topology I).2.2.1
  haveI : BorelSpace I.GA := inferInstance
  haveI hG1 : ∀ v, (Formalism.REAL.muG (I.ε v)).IsHaarMeasure := fun v => inferInstance
  haveI hG2 : ∀ v, SigmaFinite (Formalism.REAL.muG (I.ε v)) := fun v => inferInstance
  haveI hP : (Measure.pi fun v => Formalism.REAL.muG (I.ε v)).IsHaarMeasure := inferInstance
  haveI hPs : SigmaFinite (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) := inferInstance
  haveI : (I.muA μf).IsHaarMeasure := by unfold AutInst.muA; infer_instance
  have hTm : Measurable T := T.continuous.measurable
  have hTsm : Measurable T.symm := T.symm.continuous.measurable
  let μ : Measure (HA (AF I.F) I.cm.sig I.J) := Measure.map T.symm (I.muA μf)
  haveI hμ : μ.IsHaarMeasure :=
    T.symm.toMulEquiv.isHaarMeasure_map (I.muA μf) T.symm.continuous T.continuous
  let e : Γ → HFinIn (AF I.F) I.cm.sig I.J := fun g =>
    ⟨T.symm g, (hT (T.symm g)).2 (by
      rw [ContinuousMulEquiv.apply_symm_apply, ← hΓ]
      exact g.2)⟩
  have he : Function.Bijective e := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply T.symm.injective
      exact congrArg Subtype.val hab
    · intro h
      have hm : T h.1 ∈ I.GFset := (hT h.1).1 h.2
      rw [← hΓ] at hm
      refine ⟨⟨T h.1, hm⟩, Subtype.ext ?_⟩
      exact T.symm_apply_apply _
  have hsc : ∀ g : Γ, Function.Semiconj T (fun x : HA (AF I.F) I.cm.sig I.J => e g • x) (fun y : I.GA => (g : I.GA) * y) := by
    intro g x
    show T ((T.symm (g : I.GA)) * x) = (g : I.GA) * T x
    rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
  have hmp : MeasurePreserving T μ (I.muA μf) := by
    refine ⟨hTm, ?_⟩
    rw [Measure.map_map hTm hTsm]
    have : (T ∘ T.symm) = id := funext fun y => T.apply_symm_apply y
    rw [this, Measure.map_id]
  refine ⟨μ, T ⁻¹' fund, hμ, hF.preimage_of_equiv hmp.quasiMeasurePreserving he hsc, ?_⟩
  rw [Measure.map_apply hTsm (hTm hfund.1), ← Set.preimage_comp]
  have : (T ∘ T.symm) = id := funext fun y => T.apply_symm_apply y
  rw [this, Set.preimage_id]

theorem vol_finite_pos : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA),
    I.IsFundDom (I.muA μf) fund → I.muA μf fund < ⊤ ∧ I.muA μf fund ≠ 0 ∧ 0 < I.vol μf fund := by
  intro I μf _ _ fund hfund
  obtain ⟨hcm, hJ, -⟩ := GlobalTheory.AdelicModels.exists_adelic_equiv I
  obtain ⟨μ, S, hμ, hS, hμS⟩ := exists_fundamentalDomain_measure_eq I μf fund hfund
  have hfin : μ S < ⊤ := GlobalTheory.Mem.VolFin.finVol I.F I.E I.cm.sig hcm I.n I.J hJ μ hμ S hS
  have hne : μ S ≠ 0 :=
    ((GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary I.F I.E I.cm.sig I.n I.J μ hμ).2 S S hS hS).2
  rw [← hμS]
  refine ⟨hfin, hne, ?_⟩
  show 0 < ((I.muA μf) fund).toReal
  rw [← hμS]
  exact ENNReal.toReal_pos hne hfin.ne

end GlobalTheory.AdelicVol
end

