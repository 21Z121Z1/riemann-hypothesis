import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeDimensionUpper
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0092
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0050
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0042
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternGroupStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColumnRecursion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0246
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0117
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0244
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0205
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0245
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorCenterExpansion
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0204
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyClosedOfDictClosed
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0226
import GroundTheory.LocalFields.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeDimensionUpperStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lattice_dimension_upper : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (a b : K → ℤ), 1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → NefOnGenericDeg (mCoordIdeal y) a → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + b) 1) : ℝ) ≤ ((genDeg (mCoordIdeal y) D a : ℝ) + ε) * (n : ℝ) ^ D / (D.factorial : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.NefSections.finrank_chartLatQ_nsmul_add_le | exact GlobalTheory.CompanionTheory.NefSections.finrank_chartLatQ_nsmul_add_le | (intros; apply GlobalTheory.CompanionTheory.NefSections.finrank_chartLatQ_nsmul_add_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClauseAToL
section
open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFinAL

open ReciprocityTheory.Ty.Fin.Lq

theorem lt_isPat (N : ℕ) : IsPat (fun i j : Fin N => i < j) :=
  ⟨fun i => lt_irrefl i, fun _ _ _ h h' => lt_trans h h'⟩

theorem colPat_isPat (N k : ℕ) : IsPat (colPat N k) :=
  ⟨fun i h => lt_irrefl i h.1, fun _ _ _ h h' => ⟨lt_trans h.1 h'.1, h'.2⟩⟩

theorem cutE_ne (K : Type) [Field K] [Fintype K] [DecidableEq K] {N k : ℕ} {i j : Fin N}
    (h : cutE K N k i j ≠ 0) : (j : ℕ) = i + 1 ∧ (j : ℕ) ≠ k := by
  by_contra hc
  exact h (by simp only [cutE]; rw [if_neg hc])

theorem cutE_lt (K : Type) [Field K] [Fintype K] [DecidableEq K] (N k : ℕ) :
    IsPatChar (fun i j : Fin N => i < j) (cutE K N k) := by
  refine ⟨fun i j h => ?_, fun i j l h h' => ?_⟩
  · have := (cutE_ne K h).1
    exact Fin.lt_def.2 (by omega)
  · by_contra hc
    have := (cutE_ne K hc).1
    have h1 := Fin.lt_def.1 h
    have h2 := Fin.lt_def.1 h'
    omega

theorem cutE_col (K : Type) [Field K] [Fintype K] [DecidableEq K] (N k : ℕ) :
    IsPatChar (colPat N k) (cutE K N k) := by
  refine ⟨fun i j h => ?_, fun i j l h h' => (cutE_lt K N k).2 i j l h.1 h'.1⟩
  exact ⟨(cutE_lt K N k).1 i j h, (cutE_ne K h).2⟩

theorem wh_nat {K : Type} [Field K] [Fintype K] [DecidableEq K] {N : ℕ} {Φ : Fin N → Fin N → Prop}
    (hΦ : IsPat Φ) {E : Fin N → Fin N → K} (hE : IsPatChar Φ E) (ψ₀ : AddChar K ℂ)
    (τ : FDRep ℂ (GL (Fin N) K)) : ∃ m : ℕ, wh Φ E ψ₀ τ.character = m :=
  (GlobalTheory.CompanionTheory.PatGrp.patGroup K (Fin N) Φ hΦ).2.2 E ψ₀ hE |>.2.2.2 τ τ.ρ

theorem exists_rec {K : Type} [Field K] [Fintype K] [DecidableEq K] (N : ℕ) (ψ₀ : AddChar K ℂ)
    (hψ : ψ₀ ≠ 1) (τ : FDRep ℂ (GL (Fin N) K)) :
    ∃ D n : ℕ → ℕ, (∀ i, wh (fun i j : Fin N => i < j) (cutE K N i) ψ₀ τ.character = D i) ∧
      (∀ k, wh (colPat N k) (cutE K N k) ψ₀ τ.character = n k) ∧
      ∀ k, k < N → (n k : ℝ) = D k + ((Fintype.card K : ℝ) - 1) *
        ∑ a ∈ Finset.range k, (n (k - 1 - a) : ℝ) := by
  choose D hD using fun i => wh_nat (lt_isPat N) (cutE_lt K N i) ψ₀ τ
  choose n hn using fun k => wh_nat (colPat_isPat N k) (cutE_col K N k) ψ₀ τ
  refine ⟨D, n, hD, hn, fun k hk => ?_⟩
  have hcl : ∀ x y, τ.character (x * y * x⁻¹) = τ.character y := fun x y => by
    simpa using FDRep.char_conj τ y x
  have h1 := GlobalTheory.CompanionTheory.TyFin.colRec K N k ψ₀ τ.character hψ hcl hk
  have h2 := (GlobalTheory.CompanionTheory.TyFinRow.rowToCol K N ψ₀ τ.character hψ hcl).1
  have h3 : ∑ a ∈ Finset.range k, wh (rowPat N k a) (rowE K N k a) ψ₀ τ.character =
      ∑ a ∈ Finset.range k, (n (k - 1 - a) : ℂ) :=
    Finset.sum_congr rfl fun a ha => by rw [h2 k a (Finset.mem_range.1 ha) hk, hn]
  rw [h3, hn, hD] at h1
  apply Complex.ofReal_injective
  push_cast
  exact h1

end GlobalTheory.CompanionTheory.TyFinAL
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnergyEstimateOfLengthFunctionStatement
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.energy_estimate_of_length_function : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (ℓ : Mat n → ℝ), ContDiffOn ℝ ∞ ℓ (GLs n) → (∀ R : ℝ, IsCompact {y : G n | ℓ y.val ≤ R}) → ∀ (C₁ : ℝ), 0 ≤ C₁ → (∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ ℓ y (y * hm p)| ≤ C₁) → (∀ Ψ : Mat n → ℝ, ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < ℓ y → Ψ y = 0) → ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0) → ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → (∀ x, deriv χ x ≤ 0) → (∀ x, 0 ≤ χ x) → (∀ x, 1 ≤ x → χ x = 0) → ∀ (u : ℝ → Mat n → W), Sm u → ∀ (A : W →L[ℝ] W), (∀ s, ∀ y ∈ GLs n, dt (dt u) s y = (1 / 4 : ℝ) • ∑ p : Ix n, Rr (hm p) (Rt (hm p) u s) y + A (u s y)) → ∀ (C : ℝ), C₁ * (1 + Fintype.card (Ix n)) ≤ C → ∀ (r : ℝ), ∃ K : ℝ, ∀ s, ∃ e' : ℝ, HasDerivAt (fun s' => ∫ y : G n, χ (ℓ y.val + C * s' - r) * dens u s' y.val ∂μ) e' s ∧ e' ≤ K * ∫ y : G n, χ (ℓ y.val + C * s - r) * dens u s y.val ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.LocEnergy.energy_diff_ineq | exact GlobalTheory.CompanionTheory.WaveSpd.LocEnergy.energy_diff_ineq | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.LocEnergy.energy_diff_ineq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCuspidalWithLabelStatement
section
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspidal_with_label : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K) (d : ℕ), 1 ≤ d → ∀ P : K[X], P.Monic → Irreducible P → P ≠ X → P.natDegree = d →
    ∃ τ : FDRep ℂ (GL (Fin d) K), Simple τ ∧ IsCuspidal K τ ∧ HasCuspLabel C τ P := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.CuspLabel.exists_cuspidal_label | exact GlobalTheory.CompanionTheory.TyFin.CuspLabel.exists_cuspidal_label | (intros; apply GlobalTheory.CompanionTheory.TyFin.CuspLabel.exists_cuspidal_label <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisCharacterArtinCompatStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_character_artin_compat : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (art : Ideles E →* Gab E Ω) (χ : HChar E) (n : (E →+* ℂ) → ℤ)
    (μ : G E Ω →* (Qbar l)ˣ), IsLAdicOf art ι χ n μ → ∀ (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ)
    (σ : G E Ω), art (localIdele E w x) = toAb E Ω σ →
    ((μ σ : (Qbar l)ˣ) : Qbar l) = ι.symm (((χ.1 (localIdele E w x) : ℂˣ) : ℂ)) * locPow ι n w (x : w.adicCompletion E) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeLocal.isLAdicOf_localIdele | exact GlobalTheory.CompanionTheory.HeckeLocal.isLAdicOf_localIdele | (intros; apply GlobalTheory.CompanionTheory.HeckeLocal.isLAdicOf_localIdele <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisOpenSubgroupLocalUnitsStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_open_subgroup_local_units : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (U : Subgroup (w.adicCompletion E)ˣ), IsOpen (U : Set (w.adicCompletion E)ˣ) → (∀ x ∈ U, IsUnitAt w x) →
    ∃ V : Subgroup (G E Ω), IsOpen (V : Set (G E Ω)) ∧
      ∀ σ ∈ V, σ ∈ Ine (F := E) A → ∃ x ∈ U, art (localIdele E w x) = toAb E Ω σ := by
  first | exact @GlobalTheory.CompanionTheory.InertOpen.exists_openSubgroup_ine_art_units | exact GlobalTheory.CompanionTheory.InertOpen.exists_openSubgroup_ine_art_units | (intros; apply GlobalTheory.CompanionTheory.InertOpen.exists_openSubgroup_ine_art_units <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorCenterExpansionStatement
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_operator_center_expansion : ∀ (n m : ℕ), ∃ (N : ℕ) (c : Fin N → ℂ) (w : Fin N → List ℕ), (∀ cc : Fin n → ℂ, (-1 : ℂ) ^ m * GlobalTheory.Dec.gelfVal (fun a => - cc a) m = ∑ i, c i * ((w i).map (GlobalTheory.Dec.gelfVal cc)).prod) ∧ (RCalc → ∀ (s : Bool) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → ∀ x ∈ GLs n, gelT s m f x = ∑ i, c i • zOp ((w i).map (fun j => (s, j))) f x) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.GenTr.transposed_invariants | exact GlobalTheory.CompanionTheory.WaveMult.GenTr.transposed_invariants | (intros; apply GlobalTheory.CompanionTheory.WaveMult.GenTr.transposed_invariants <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitDetEmbMat
section
noncomputable section

namespace GlobalTheory.CompanionTheory.DeRhamChar

open Module TensorProduct Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cmp.JumpDict GlobalTheory.Cmp.SmallJumps
open scoped Classical

section Coord

variable {Qp Om LL BdR : Type} [Field Qp] [Field Om] [Field LL] [CommRing BdR]
  [Algebra Qp Om] [Algebra Qp LL] [Algebra Qp BdR] [Algebra Om BdR] [IsScalarTower Qp Om BdR]

def ev (σ : LL →ₐ[Qp] Om) : (Fin 1 → LL) ⊗[Qp] BdR →ₗ[Qp] BdR :=
  TensorProduct.lift
    ((LinearMap.mul Qp BdR).comp
      (((IsScalarTower.toAlgHom Qp Om BdR).toLinearMap.comp σ.toLinearMap).comp
        (LinearMap.proj 0 : (Fin 1 → LL) →ₗ[Qp] LL)))

@[simp] theorem ev_tmul (σ : LL →ₐ[Qp] Om) (v : Fin 1 → LL) (b : BdR) :
    ev σ (v ⊗ₜ[Qp] b) = algebraMap Om BdR (σ (v 0)) * b := by
  simp [ev]

theorem ev_smul (σ : LL →ₐ[Qp] Om) (c : LL) (z : (Fin 1 → LL) ⊗[Qp] BdR) :
    ev σ (c • z) = algebraMap Om BdR (σ c) * ev σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [TensorProduct.smul_tmul', mul_assoc]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy, mul_add]

variable [FiniteDimensional Qp LL] [Algebra.IsSeparable Qp LL] [IsAlgClosed Om]

variable (Qp Om LL) in

def embBasis : Basis (LL →ₐ[Qp] Om) Qp LL :=
  (finBasis Qp LL).reindex (Fintype.equivFinOfCardEq (AlgHom.card Qp LL Om)).symm

variable (Qp Om LL) in

def embMat : Matrix (LL →ₐ[Qp] Om) (LL →ₐ[Qp] Om) Om :=
  Algebra.embeddingsMatrixReindex Qp Om (embBasis Qp Om LL) (Equiv.refl _)

theorem embMat_apply (i j : LL →ₐ[Qp] Om) : embMat Qp Om LL i j = j (embBasis Qp Om LL i) := rfl

theorem isUnit_det_embMat : IsUnit (embMat Qp Om LL).det := by
  refine isUnit_iff_ne_zero.2 fun h => ?_
  have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two Qp Om (embBasis Qp Om LL) (Equiv.refl _)
  have h2 : algebraMap Qp Om (Algebra.discr Qp (embBasis Qp Om LL)) = 0 := by
    rw [h1]; change (embMat Qp Om LL).det ^ 2 = 0; rw [h]; simp
  exact Algebra.discr_not_zero_of_basis Qp (embBasis Qp Om LL)
    ((map_eq_zero_iff _ (algebraMap Qp Om).injective).1 h2)

def coordInv (f : (LL →ₐ[Qp] Om) → BdR) : (Fin 1 → LL) ⊗[Qp] BdR :=
  ∑ i, (fun _ => embBasis Qp Om LL i) ⊗ₜ[Qp]
    ∑ j, algebraMap Om BdR ((embMat Qp Om LL)⁻¹ j i) * f j

theorem ev_coordInv (f : (LL →ₐ[Qp] Om) → BdR) (k : LL →ₐ[Qp] Om) :
    ev k (coordInv f) = f k := by
  have hN : (embMat Qp Om LL)⁻¹ * embMat Qp Om LL = 1 := Matrix.nonsing_inv_mul _ isUnit_det_embMat
  have h1 : ∀ j, ∑ i, embMat Qp Om LL i k * (embMat Qp Om LL)⁻¹ j i = if j = k then 1 else 0 := fun j => by
    have := congrFun (congrFun hN j) k
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  simp only [coordInv, map_sum, ev_tmul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 : ∀ j, ∑ i, algebraMap Om BdR (k (embBasis Qp Om LL i)) *
      (algebraMap Om BdR ((embMat Qp Om LL)⁻¹ j i) * f j) =
      algebraMap Om BdR (if j = k then 1 else 0) * f j := fun j => by
    rw [← h1 j, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, embMat_apply, mul_assoc]
  simp only [h2]
  simp

theorem coordInv_add (f g : (LL →ₐ[Qp] Om) → BdR) : coordInv (f + g) = coordInv f + coordInv g := by
  simp only [coordInv, Pi.add_apply, mul_add, Finset.sum_add_distrib, tmul_add]

theorem coordInv_ev (z : (Fin 1 → LL) ⊗[Qp] BdR) :
    coordInv (fun σ : LL →ₐ[Qp] Om => ev σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp [coordInv]
  | add x y hx hy =>
    nth_rw 2 [← hx]
    nth_rw 2 [← hy]
    rw [← coordInv_add]
    congr 1
    funext σ
    simp
  | tmul v b =>
    have hM : embMat Qp Om LL * (embMat Qp Om LL)⁻¹ = 1 := Matrix.mul_nonsing_inv _ isUnit_det_embMat
    set a := (embBasis Qp Om LL).repr (v 0) with ha
    have hv : v 0 = ∑ k, a k • embBasis Qp Om LL k := ((embBasis Qp Om LL).sum_repr (v 0)).symm
    have h1 : ∀ i, ∑ j, (embMat Qp Om LL)⁻¹ j i * j (v 0) = algebraMap Qp Om (a i) := fun i => by
      have h2 : ∀ j : LL →ₐ[Qp] Om, j (v 0) = ∑ k, algebraMap Qp Om (a k) * embMat Qp Om LL k j := fun j => by
        rw [hv, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, Algebra.smul_def, embMat_apply]
      simp only [h2, Finset.mul_sum]
      rw [Finset.sum_comm]
      have h3 : ∀ k, ∑ j, (embMat Qp Om LL)⁻¹ j i * (algebraMap Qp Om (a k) * embMat Qp Om LL k j) =
          algebraMap Qp Om (a k) * (if k = i then 1 else 0) := fun k => by
        have := congrFun (congrFun hM k) i
        rw [Matrix.mul_apply, Matrix.one_apply] at this
        rw [← this, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      simp only [h3]
      simp
    have h4 : ∀ i, ∑ j, algebraMap Om BdR ((embMat Qp Om LL)⁻¹ j i) *
        (algebraMap Om BdR (j (v 0)) * b) = a i • b := fun i => by
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply Qp Om BdR, ← h1, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, mul_assoc]
    simp only [coordInv, ev_tmul, h4, tmul_smul]
    have h5 : v = ∑ i, a i • (fun _ : Fin 1 => embBasis Qp Om LL i) := by
      funext i
      rw [Subsingleton.elim i 0]
      simp only [Finset.sum_apply, Pi.smul_apply]
      exact hv
    conv_rhs => rw [h5, sum_tmul]
    exact Finset.sum_congr rfl fun i _ => rfl

theorem ev_injective {z w : (Fin 1 → LL) ⊗[Qp] BdR} (h : ∀ σ : LL →ₐ[Qp] Om, ev σ z = ev σ w) : z = w := by
  rw [← coordInv_ev (Om := Om) z, ← coordInv_ev (Om := Om) w]
  exact congrArg _ (funext h)

end Coord

section Period

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem mem_DdR_iff (ρ : Representation LL G V) (z : V ⊗[Qp] BdR) :
    z ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g z = z := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_DdRE_iff (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (z : V ⊗[Qp] BdR) :
    z ∈ DdRE PD ρ τ ↔ z ∈ DdR PD ρ ∧
      ∀ c, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c z = τ c • z := by
  simp only [DdRE, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem exists_gen (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (J : ℤ)
    (h : ∀ a, multV PD ρ τ a = if a = J then 1 else 0) :
    ∃ z ∈ DdRE PD ρ τ, (∀ w ∈ DdRE PD ρ τ, ∃ c : LL, w = c • z) ∧
      z ∈ FilV PD (LL := LL) (V := V) J ∧ z ∉ FilV PD (LL := LL) (V := V) (J + 1) := by
  haveI : FiniteDimensional LL (DdRE PD ρ τ) :=
    finite_ddRE_of_multV PD ρ τ {J} (by simp) fun a => by
      rw [h, Multiset.count_singleton]; split_ifs <;> rfl
  have hanti : ∀ a, FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a := fun a =>
    inf_le_inf_left _ (filV_anti PD (by omega : a ≤ a + 1))
  have h1 : finrank LL (DdRE PD ρ τ) = 1 :=
    finrank_eq_one_of_jump (FildR PD ρ τ) _ (fun _ => inf_le_left) hanti
      (fun x hx => (filV_exh PD (LL := LL) x).imp fun _ ha => ⟨hx, ha⟩)
      (fun x hx => filV_sep PD (LL := LL) x fun a => (hx a).2) J h
  have hJ := h J
  rw [if_pos rfl] at hJ
  unfold multV at hJ
  have hle : finrank LL (FildR PD ρ τ J) ≤ 1 := by
    rw [← h1]; exact Submodule.finrank_mono inf_le_left
  have h2 : finrank LL (FildR PD ρ τ J) = 1 := by omega
  have h3 : finrank LL (FildR PD ρ τ (J + 1)) = 0 := by omega
  have h4 : FildR PD ρ τ J = DdRE PD ρ τ :=
    Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1, h2])
  haveI : FiniteDimensional LL (FildR PD ρ τ (J + 1)) := Submodule.finiteDimensional_of_le inf_le_left
  have h5 : FildR PD ρ τ (J + 1) = ⊥ := Submodule.finrank_eq_zero.1 h3
  obtain ⟨z, hz0, hz⟩ := finrank_eq_one_iff'.1 h1
  have hz1 : (z : V ⊗[Qp] BdR) ∈ FildR PD ρ τ J := by rw [h4]; exact z.2
  refine ⟨z, z.2, fun w hw => ?_, hz1.2, fun hz2 => ?_⟩
  · obtain ⟨c, hc⟩ := hz ⟨w, hw⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  · have : (z : V ⊗[Qp] BdR) ∈ FildR PD ρ τ (J + 1) := ⟨z.2, hz2⟩
    rw [h5, Submodule.mem_bot] at this
    exact hz0 (Subtype.ext this)

theorem multV_of_gen (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (J : ℤ) (z : V ⊗[Qp] BdR)
    (hz : z ∈ DdRE PD ρ τ) (hgen : ∀ w ∈ DdRE PD ρ τ, ∃ c : LL, w = c • z)
    (h1 : z ∈ FilV PD (LL := LL) (V := V) J) (h2 : z ∉ FilV PD (LL := LL) (V := V) (J + 1)) (a : ℤ) :
    multV PD ρ τ a = if a = J then 1 else 0 := by
  have hz0 : z ≠ 0 := fun h => h2 (h ▸ Submodule.zero_mem _)
  have hlo : ∀ a ≤ J, FildR PD ρ τ a = LL ∙ z := fun a ha => by
    refine le_antisymm (fun w hw => ?_) ?_
    · obtain ⟨c, rfl⟩ := hgen w hw.1
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)
    · rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨hz, filV_anti PD ha h1⟩
  have hhi : ∀ a, J < a → FildR PD ρ τ a = ⊥ := fun a ha => by
    refine eq_bot_iff.2 fun w hw => ?_
    obtain ⟨c, rfl⟩ := hgen w hw.1
    by_cases hc : c = 0
    · simp [hc]
    · refine absurd ?_ h2
      have := filV_anti PD (by omega : J + 1 ≤ a) hw.2
      simpa [hc] using (Submodule.smul_mem_iff _ hc).1 this
  have hone : finrank LL (LL ∙ z) = 1 := finrank_span_singleton hz0
  unfold multV
  rcases lt_trichotomy a J with ha | ha | ha
  · rw [hlo a ha.le, hlo (a + 1) (by omega), if_neg ha.ne]; simp
  · subst ha
    rw [hlo a le_rfl, hhi (a + 1) (by omega), if_pos rfl, hone]; simp
  · rw [hhi a ha, hhi (a + 1) (by omega), if_neg ha.ne']; simp

end Period

end GlobalTheory.CompanionTheory.DeRhamChar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRegularityStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_regularity : PositivityTheory.RgBcC.Fc.KerCore := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.kerCore | exact GlobalTheory.CompanionTheory.KerFc.kerCore | (intros; apply GlobalTheory.CompanionTheory.KerFc.kerCore <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollificationAeEqConvolutionStatement
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mollification_ae_eq_convolution : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ φ : Mat n → ℝ, IsTest φ → ∀ x : Lp V 2 μ, (fun y : G n => Mol μ φ (⇑x) y.val) =ᵐ[μ] lConv μ V φ x := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.mol_ae_lConv | exact GlobalTheory.CompanionTheory.PresSobA.mol_ae_lConv | (intros; apply GlobalTheory.CompanionTheory.PresSobA.mol_ae_lConv <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFromKummerUnramifiedUnit
section
open ValuativeRel IntermediateField

namespace GlobalTheory.CompanionTheory.LocalField

open GroundTheory.LocalField

theorem exists_norm_fixedField_ker_eq_unit :
    ∀ {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
      [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (N : ℕ), N ≠ 0 → ∀ ξ : Ω,
      IsPrimitiveRoot ξ (Nat.card 𝓀[K] ^ N - 1) →
      ∀ ψ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N), IsOpen (ψ.ker : Set (Ω ≃ₐ[K] Ω)) →
      (∀ g : Ω ≃ₐ[K] Ω, g ξ = ξ → ψ g = 1) → ∀ U : Kˣ, GroundTheory.LocalField.ord (U : K) = 0 →
      ∃ y : IntermediateField.fixedField ψ.ker, Algebra.norm K y = (U : K) := by
  intro K Ω _ _ _ _ _ _ _ N hN ξ hξ ψ hopen hψ U hU
  have hgal : IsGalois K Ω := inferInstance
  obtain ⟨hL, -⟩ := isUnramifiedSubextension_adjoin hN hξ
  have := hL.1
  have := hL.isGalois
  have hclosed : IsClosed (ψ.ker : Set (Ω ≃ₐ[K] Ω)) := Subgroup.isClosed_of_isOpen _ hopen
  let C : ClosedSubgroup (Ω ≃ₐ[K] Ω) := ⟨ψ.ker, hclosed⟩
  set M : IntermediateField K Ω := fixedField ψ.ker with hM
  have hMU : M.fixingSubgroup = ψ.ker := InfiniteGalois.fixingSubgroup_fixedField C
  have hML : M ≤ K⟮ξ⟯ := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup K⟮ξ⟯]
    intro x hx
    rw [mem_fixedField_iff]
    intro g hg
    have hgξ : g ξ = ξ := (mem_fixingSubgroup_iff _ _).1 hg ξ (mem_adjoin_simple_self K ξ)
    exact (mem_fixedField_iff _ _).1 hx g (hψ g hgξ)
  have : FiniteDimensional K M := FiniteDimensional.of_injective (IntermediateField.inclusion hML).toLinearMap
    (IntermediateField.inclusion hML).toRingHom.injective
  have : IsGalois K M := IsGalois.of_fixedField_normal_subgroup ψ.ker
  have : IsMulCommutative (M ≃ₐ[K] M) := ⟨⟨fun τ₁ τ₂ => by
    obtain ⟨g₁, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := Ω) τ₁
    obtain ⟨g₂, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := Ω) τ₂
    rw [← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker,
      IntermediateField.restrictNormalHom_ker, hMU, MonoidHom.mem_ker]
    simp only [map_mul, map_inv, mul_inv_rev]
    rw [mul_comm (ψ g₁) (ψ g₂)]
    group⟩⟩
  have : IsAbelianGalois K M := ⟨⟩
  have hle := hL.le_maximalUnramifiedExtension
  have h1 := restrictAb_localArtinMap_of_le_maximalUnramifiedExtension K⟮ξ⟯ hle U
  rw [hU, zpow_zero] at h1
  have h2 : restrictAb M (le_maximalAbelianExtension M) (localArtinMap K Ω U) = 1 := by
    ext x
    have e1 := restrictAb_apply M (le_maximalAbelianExtension M) (localArtinMap K Ω U) x
    have e2 := restrictAb_apply K⟮ξ⟯
      (hle.trans maximalUnramifiedExtension_le_maximalAbelianExtension) (localArtinMap K Ω U)
      ⟨x, hML x.2⟩
    rw [h1] at e2
    exact e1.trans e2.symm
  have h3 : U ∈ (normUnits K M).range := by
    rw [← ker_restrictAb_localArtinMap M, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact h2
  obtain ⟨y, hy⟩ := h3
  exact ⟨y, by simpa using congrArg Units.val hy⟩

end GlobalTheory.CompanionTheory.LocalField
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueFieldCardEqNorm
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ValuativeRel

namespace GlobalTheory.CompanionTheory.LocRes

theorem natCard_residueField_eq_normV : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)), Nat.card 𝓀[v.adicCompletion F] = normV v := by
  intro F _ _ v
  rw [GroundTheory.Global.natCard_residueField_adicCompletion v, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]
  rfl

end GlobalTheory.CompanionTheory.LocRes
end

