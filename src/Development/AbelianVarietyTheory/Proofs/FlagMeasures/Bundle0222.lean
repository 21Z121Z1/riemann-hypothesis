import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0208
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0220
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselBigCellCoordinatesUnique
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0133
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0209
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0170
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0177
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0216
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0210
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeExpansionOverFinitePlacesStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_expansion_over_finite_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ d : G.Dat, (∃ Λ₀, G.IsTerm d Λ₀) → ∀ S1 : Finset (HeightOneSpectrum (𝓞 F)), G.Om ⊆ S1 → ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ Q : Prop → Prop, G.amp d (fun Λ => Q (¬ G.Gen d Λ)) = κ * ∑ B ∈ S1.powerset.filter (fun B => Q B.Nonempty), ∏ p ∈ S1, (if p ∈ B then (G.S p).amp (d p) (fun Λ => ¬ (G.S p).BBzero (d p) Λ) else (G.S p).amp (d p) ((G.S p).BBzero (d p))) := by
  first | exact @GlobalTheory.HL.DefectPhase.amp_sum_defect_sets | exact GlobalTheory.HL.DefectPhase.amp_sum_defect_sets | (intros; apply GlobalTheory.HL.DefectPhase.amp_sum_defect_sets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutBallCount
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec

namespace GlobalTheory.AutBall

theorem pow_bound (s t R : ℝ) (m f : ℕ) (hs : 1 ≤ s) (ht : 0 < t) (ht1 : t ≤ 1 / 2) (hR : 0 ≤ R) (hf : 0 < f) :
    (1 + 2 * s * Real.exp (R / f) / (t * t)) ^ (2 * (m * f)) ≤
      (3 * s / t ^ 2) ^ (2 * (m * f)) * Real.exp (2 * (m : ℝ) * R) := by
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have hE : 1 ≤ Real.exp (R / f) := Real.one_le_exp (div_nonneg hR hf'.le)
  have htt : 0 < t * t := mul_pos ht ht
  have h1 : 1 ≤ s * Real.exp (R / f) / (t * t) := by
    rw [le_div_iff₀ htt]; nlinarith
  have h2 : 1 + 2 * s * Real.exp (R / f) / (t * t) ≤ 3 * s / t ^ 2 * Real.exp (R / f) := by
    have e1 : 2 * s * Real.exp (R / f) / (t * t) = 2 * (s * Real.exp (R / f) / (t * t)) := by ring
    have e2 : 3 * s / t ^ 2 * Real.exp (R / f) = 3 * (s * Real.exp (R / f) / (t * t)) := by ring
    rw [e1, e2]; linarith
  have h3 : Real.exp (2 * (m : ℝ) * R) = Real.exp (R / f) ^ (2 * (m * f)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
  rw [h3, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) h2 _

theorem autBallCount : GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount.AutBallCount := by
  intro I hn x r hr
  obtain ⟨hfin, hle⟩ := GlobalTheory.RationalCount.count_le I x x r hn hr
  have hsub : GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount.ballSet I x r ⊆
      {a : I.GA | a ∈ I.GFset ∧ (x⁻¹ * a * x).2 ∈ I.Kset ∧ ∀ v, dOp (uMat ((x⁻¹ * a * x).1 v)) ≤ r v} := by
    rintro a ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun v => le_trans ?_ (h3 v)⟩
    obtain ⟨h0, -, -, h4, -⟩ :=
      (GlobalTheory.Count.Cartan.cartan_distances I.n (I.ε v)).2.1 ((x⁻¹ * a * x).1 v) ((x⁻¹ * a * x).1 v) hn
    have h5 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
    exact (le_mul_of_one_le_left h0 h5).trans h4
  refine ⟨hfin.subset hsub, ?_⟩
  have hc := Set.ncard_le_ncard hsub hfin
  have hf : 0 < I.f := Module.finrank_pos (R := ℚ) (M := I.F)
  have hs : 1 ≤ Real.sqrt (I.n : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have hb := pow_bound (Real.sqrt (I.n : ℝ)) (tau1 I x) (∑ v, r v) (I.n ^ 2) I.f hs
    (GlobalTheory.RationalCount.truncatedLeastLatticeSize_pos I hn x) (min_le_left _ _) (Finset.sum_nonneg fun v _ => hr v) hf
  refine (Nat.cast_le.mpr hc).trans (hle.trans (hb.trans (le_of_eq ?_)))
  unfold GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount.bigA
  push_cast
  rfl

end GlobalTheory.AutBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselBigCellCoordinatesUniqueStatement
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselBigCell_coordinates_unique : ∀ (k r : ℕ) (x y : Fin r → ℂ), (∀ a, x a ≠ 0) → (∀ a, y a ≠ 0) → ∀ n₁ ∈ Nset k r, ∀ n₂ ∈ Nset k r, ∀ n₁' ∈ Nset k r, ∀ n₂' ∈ Nset k r, ∀ m₁ ∈ Formalism.FourierDecayAlt.B2.UWb k r, ∀ m₂ ∈ Formalism.FourierDecayAlt.B2.UWb k r, n₁⁻¹ * bigCell k r x 1 * m₁ * n₁' = n₂⁻¹ * bigCell k r y 1 * m₂ * n₂' → n₁ = n₂ ∧ x = y ∧ m₁ = m₂ ∧ n₁' = n₂' := by
  first | exact @GlobalTheory.CellDens.bigCell_coords_unique | exact GlobalTheory.CellDens.bigCell_coords_unique | (intros; apply GlobalTheory.CellDens.bigCell_coords_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormCoeffProductFubiniIntegrableStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselForm_coeff_product_fubini_integrable : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ v₁ ∈ DD σ w, Integrable (fun p : Mt k r × Mt k r => coef σ u v (Matrix.of p.1) * star (coef σ u₁ v₁ (Matrix.of p.2 * Matrix.of p.1))) (μG.prod μS) := by
  first | exact @GlobalTheory.SgInf.fubini_bound | exact GlobalTheory.SgInf.fubini_bound | (intros; apply GlobalTheory.SgInf.fubini_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitianStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselForm_converges_equivariant_hermitian : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ V : Set H, (∀ g ∈ GG k r, ∀ v ∈ V, σ g v ∈ V) → Decay σ V a → ∀ u ∈ V, ∀ u' ∈ V, Integrable (fun s : Mt k r => coef σ u u' (Matrix.of s) • PiS (psiGen k r z c) π (Matrix.of s)⁻¹) μS ∧ (∀ t ∈ Sset k r z, be (psiGen k r z c) π μS σ (σ t u) u' = (PiS (psiGen k r z c) π t).comp (be (psiGen k r z c) π μS σ u u') ∧ be (psiGen k r z c) π μS σ u (σ t u') = (be (psiGen k r z c) π μS σ u u').comp (PiS (psiGen k r z c) π t⁻¹)) ∧ ContinuousLinearMap.adjoint (be (psiGen k r z c) π μS σ u u') = be (psiGen k r z c) π μS σ u' u ∧ ContinuousOn (fun x => be (psiGen k r z c) π μS σ (σ x u) u') (GG k r) := by
  first | exact @GlobalTheory.SgInf.BeForm.be_converges_equivariant_hermitian_continuous | exact GlobalTheory.SgInf.BeForm.be_converges_equivariant_hermitian_continuous | (intros; apply GlobalTheory.SgInf.BeForm.be_converges_equivariant_hermitian_continuous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelMatrixSkewCoordinatesRationalAutStatement
section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselModelMatrix_skew_coordinates_rational_aut : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V) (r : ℕ) (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ) (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r), 0 < ρ → IsFrameOf N k σ ρ β Φ z z' g → ∀ (s : V ≃ₗ[K] V) (q : (UTin β → ℂ) × PTop k r N.j), (∀ x, crd k r N.j β q *ᵥ Φ x = Φ (s x)) → q.1 = 0 → q.2.1 = 0 → (∀ b : Fin r, N.j ≤ b.val → s (N.ist b) - N.ist b ∈ II N.F N.F') ∧ (∀ p : {p : UT r // N.j ≤ p.1.1.val}, q.2.2.1 p = ((ρ ^ ((r - p.1.1.1.val) + (r - p.1.1.2.val)) : ℝ) : ℂ) * σ (H.B (s (N.ist p.1.1.2)) (N.ist p.1.1.1))) ∧ ∀ a : {a : Fin r // N.j ≤ a.val}, q.2.2.2 a = ρ ^ (2 * (r - a.1.val)) * (σ (H.B (s (N.ist a.1)) (N.ist a.1))).im := by
  first | exact @GlobalTheory.DegVol.RefCovSkew.coords_skew | exact GlobalTheory.DegVol.RefCovSkew.coords_skew | (intros; apply GlobalTheory.DegVol.RefCovSkew.coords_skew <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselRegularDoubleCosetPolynomialPropernessStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselRegularDoubleCoset_polynomial_properness : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsCompact C → C ⊆ Greg k r z z' → ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ γ ∈ C, ∀ s ∈ Sset k r z, ∀ s' ∈ Sset k r z', max (opn s) (opn s') ≤ C0 * opn (s * γ * s'⁻¹) ^ (2 * (r ^ 2 + r + 1)) := by
  first | exact @GlobalTheory.SgInf.PolyProper.poly_proper | exact GlobalTheory.SgInf.PolyProper.poly_proper | (intros; apply GlobalTheory.SgInf.PolyProper.poly_proper <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellChartDifferentialSurjectiveSkew
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens.Onto

open Formalism.QuantumDeterminants.GBasic

lemma wC_eq (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    wC k r i j = if j = sig k r i then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  have hs := sig_val k r i
  unfold wC bigCell esI
  simp only [Fin.ext_iff, Matrix.one_apply, star_one, inv_one]
  split_ifs at * <;> first | rfl | (exfalso; omega)

lemma conj_apply (k r : ℕ) (M : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (wC k r * M * wC k r) i j = M (sig k r i) (sig k r j) := by
  simp only [Matrix.mul_apply, wC_eq k r i, ite_mul, zero_mul, one_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [wC_eq, eq_sig_iff k r j, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

lemma skew_apply (k r : ℕ) (M : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (Mᴴ * Hpk k r + Hpk k r * M) i j =
      star (M (sig k r j) i) * sgn k r j + sgn k r i * M (sig k r i) j := by
  simp only [Matrix.add_apply, Matrix.mul_apply, conjTranspose_apply, Hpk_eq k r i, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Hpk_eq, eq_sig_iff k r j, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, sgn_sig]

lemma skew_iff (k r : ℕ) (M : Mat k r) :
    Mᴴ * Hpk k r + Hpk k r * M = 0 ↔
      ∀ i j, star (M (sig k r j) i) * sgn k r j + sgn k r i * M (sig k r i) j = 0 := by
  rw [← Matrix.ext_iff]
  simp only [skew_apply, Matrix.zero_apply]

lemma lev_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : lev k r (sig k r i) + lev k r i = 2 * r := by
  have hi := i.isLt
  have hs := sig_val k r i
  unfold lev
  split_ifs at * <;> omega

lemma unre {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
  ext i j
  apply Complex.ext <;> simp [unrealify, realifyFun]

lemma exists_N (k r : ℕ) (M : Mat k r) (h : Mᴴ * Hpk k r + Hpk k r * M = 0) :
    ∃ X : lieE (Nset k r), um X = Matrix.of fun i j => if lev k r i < lev k r j then M i j else 0 := by
  refine ⟨⟨(WithLp.equiv 2 _).symm (realifyFun
    (Matrix.of fun i j => if lev k r i < lev k r j then M i j else 0)), ?_⟩, unre _⟩
  rw [(GlobalTheory.T.lieEntries_unipotentBesselN_characterization k r _).1, unre]
  refine ⟨?_, fun i j hij => by simp [not_lt.2 hij]⟩
  rw [skew_iff] at h ⊢
  intro i j
  have h1 := lev_sig k r i
  have h2 := lev_sig k r j
  simp only [Matrix.of_apply]
  by_cases c : lev k r (sig k r j) < lev k r i
  · rw [if_pos c, if_pos (by omega)]; exact h i j
  · rw [if_neg c, if_neg (by omega)]; simp

lemma exists_lieElement_middleBlockPart (k r : ℕ) (M : Mat k r) (h : Mᴴ * Hpk k r + Hpk k r * M = 0) :
    ∃ Y : lieE (Formalism.FourierDecayAlt.B2.UWb k r), um Y = Matrix.of fun i j =>
      if (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then M i j else 0 := by
  refine ⟨⟨(WithLp.equiv 2 _).symm (realifyFun (Matrix.of fun i j =>
      if (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then M i j else 0)), ?_⟩, unre _⟩
  rw [(GlobalTheory.T.lieAlgebra_besselModel_middleUnitary_entries k r _).2.1, unre]
  refine ⟨?_, fun i j hij => by simp only [Matrix.of_apply, if_neg hij]⟩
  rw [skew_iff] at h ⊢
  intro i j
  have h1 := sig_val k r i
  have h2 := sig_val k r j
  have hi := i.isLt
  have hj := j.isLt
  simp only [Matrix.of_apply]
  by_cases c : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)
  · rw [if_pos (by split_ifs at h1 h2 <;> omega), if_pos (by split_ifs at h1 h2 <;> omega)]
    exact h i j
  · rw [if_neg (by split_ifs at h1 h2 <;> omega), if_neg (by split_ifs at h1 h2 <;> omega)]
    simp

theorem dchart_onto : ∀ (k r : ℕ) (Z : Mat k r), Zᴴ * Hpk k r + Hpk k r * Z = 0 →
    ∃ v : EE k r, dchart k r v = Z := by
  intro k r Z hZ
  have hZ' := (skew_iff k r Z).1 hZ
  obtain ⟨X', hX'⟩ := exists_N k r Z hZ
  obtain ⟨Y, hY⟩ := exists_lieElement_middleBlockPart k r Z hZ
  obtain ⟨X, hX⟩ := exists_N k r (Matrix.of fun i j => -Z (sig k r i) (sig k r j)) (by
    rw [skew_iff]
    intro i j
    have := hZ' (sig k r i) (sig k r j)
    simp only [sig_sig, sgn_sig] at this
    simp only [Matrix.of_apply, sig_sig, star_neg]
    linear_combination -this)
  refine ⟨((X, X'), (fun a => Z (eI k r a) (eI k r a), Y)), ?_⟩
  ext i j
  have h1 := lev_sig k r i
  have h2 := lev_sig k r j
  have hi := i.isLt
  have hj := j.isLt
  simp only [dchart, Matrix.add_apply, Matrix.neg_apply, conj_apply, hX, hX', hY, Matrix.of_apply,
    sig_sig, torD, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp only [lt_irrefl, if_false, if_true, neg_zero, zero_add, add_zero, and_self]
    by_cases c : i.val < r
    · rw [dif_pos c, if_neg (by omega), add_zero]; rfl
    · rw [dif_neg c]
      by_cases c' : r + k < i.val
      · rw [dif_pos c', if_neg (by omega), add_zero]
        have e : eI k r ⟨2 * r + k - i.val, by omega⟩ = sig k r i :=
          Fin.ext (by rw [sig_hi k r i c']; rfl)
        rw [e]
        have := hZ' (sig k r i) i
        rw [sgn_sig, sig_sig] at this
        have hs : sgn k r i = 1 := by unfold sgn; rw [if_neg (by omega)]
        rw [hs] at this
        linear_combination -this
      · rw [dif_neg c', if_pos (by omega), zero_add]
  · rw [if_neg hij, add_zero]
    have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have l1 : lev k r i = if i.val < r then i.val else if i.val ≤ r + k then r else i.val - k := rfl
    have l2 : lev k r j = if j.val < r then j.val else if j.val ≤ r + k then r else j.val - k := rfl
    rcases lt_trichotomy (lev k r i) (lev k r j) with c | c | c
    · rw [if_neg (by omega), if_neg (by split_ifs at l1 l2 <;> omega), if_pos c]; simp
    · rw [if_neg (by omega), if_pos (by split_ifs at l1 l2 <;> omega), if_neg (by omega)]; simp
    · rw [if_pos (by omega), if_neg (by split_ifs at l1 l2 <;> omega), if_neg (by omega)]; simp

end GlobalTheory.CellDens.Onto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFlagIsotropicSelfDualStatement
section
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalLatticeFlag_isotropic_selfDual : ∀ (I : AutInst) (x : I.GA), (∀ y ∈ stepLt I x (1 / 2), ∀ z ∈ stepLt I x (1 / 2), Formalism.UG.hform (starRingEnd I.E) I.J y z = 0) ∧ (∀ v, rkK (stepLt I x (1 / 2)) ≤ rkR (I.ε v)) ∧ ∀ R : Submodule (𝓞 I.E) (Fin I.n → I.E), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≤ perpIn I x R → ∀ y ∈ Submodule.span I.E (perpIn I x R : Set (Fin I.n → I.E)), (∀ z ∈ perpIn I x R, Formalism.UG.hform (starRingEnd I.E) I.J z y ∈ (algebraMap (𝓞 I.E) I.E).range) → ∃ y' ∈ perpIn I x R, y - y' ∈ Submodule.span I.E (R : Set (Fin I.n → I.E)) := by
  first | exact @GlobalTheory.FlagIso.flag_isotropic | exact GlobalTheory.FlagIso.flag_isotropic | (intros; apply GlobalTheory.FlagIso.flag_isotropic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassNumberRootDiscFactorLeHHZStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classNumber_rootDisc_factor_le_HHZ : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ Z : GramM D, (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f * (classNumber D.host.E : ℝ) * 2 ^ D.R.f * 9 ^ D.R.f ≤ HHZ D large₂.sc.b C Z := by
  first | exact @GlobalTheory.LoopC.SizeQ.main | exact GlobalTheory.LoopC.SizeQ.main | (intros; apply GlobalTheory.LoopC.SizeQ.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContDensityOnEqFibreIntegralStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDensity_eq_fibre_integral : ∀ (V X : Type) [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (f : V → X) (ν : Measure X) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] (B : Set X) (fib : X → Measure V) (φ : V → ℝ) (g : X → ℂ), Continuous f → IsOpen B → IsFibreFamily μ f id Set.univ ν B fib → Continuous φ → HasCompactSupport φ → (∀ v, 0 ≤ φ v) → IsContDensityOn μ f id ν B (fun v => (φ v : ℂ)) g → ∀ b ∈ B, g b = ((∫ v, φ v ∂(fib b) : ℝ) : ℂ) ∧ ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) = ENNReal.ofReal (g b).re := by
  first | exact @GlobalTheory.FibreDensity.contDensityOn_eq_fibre_integral | exact GlobalTheory.FibreDensity.contDensityOn_eq_fibre_integral | (intros; apply GlobalTheory.FibreDensity.contDensityOn_eq_fibre_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountRationalElementsBoundedDistance
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec

namespace GlobalTheory.Dec.BoundedDistance

theorem bound_le (s la R : ℝ) (m f : ℕ) (hs : 1 ≤ s) (hla : 0 < la) (hla1 : la ≤ 1) (hR : 0 ≤ R) (hf : 0 < f) :
    (1 + 2 * s * Real.exp (R / f) / la) ^ (2 * (m * f)) ≤ (3 * s / la) ^ (2 * m * f) * Real.exp (2 * (m : ℝ) * R) := by
  have hf' : (f : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
  have he : 1 ≤ Real.exp (R / f) := Real.one_le_exp (div_nonneg hR (Nat.cast_nonneg _))

  have hone : 1 ≤ s * Real.exp (R / f) / la := by
    rw [le_div_iff₀ hla]
    nlinarith
  have hbase0 : 0 ≤ 1 + 2 * s * Real.exp (R / f) / la := by positivity
  have hbase : 1 + 2 * s * Real.exp (R / f) / la ≤ 3 * s / la * Real.exp (R / f) := by
    have h3 : 3 * s / la * Real.exp (R / f) =
        s * Real.exp (R / f) / la + 2 * s * Real.exp (R / f) / la := by ring
    linarith
  have hk : 2 * (m * f) = 2 * m * f := by ring
  rw [hk]
  calc (1 + 2 * s * Real.exp (R / f) / la) ^ (2 * m * f)
      ≤ (3 * s / la * Real.exp (R / f)) ^ (2 * m * f) := pow_le_pow_left₀ hbase0 hbase _
    _ = (3 * s / la) ^ (2 * m * f) * Real.exp (2 * (m : ℝ) * R) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      field_simp

theorem countRat : CountRat := by
  intro I x y r hn hr
  obtain ⟨hfin, hcard⟩ := GlobalTheory.RationalCount.count_le I x y r hn hr
  have hx := GlobalTheory.RationalCount.truncatedLeastLatticeSize_pos I hn x
  have hy := GlobalTheory.RationalCount.truncatedLeastLatticeSize_pos I hn y

  have hx2 : tau1 I x ≤ 1 / 2 := by unfold tau1; exact min_le_left _ _
  have hy2 : tau1 I y ≤ 1 / 2 := by unfold tau1; exact min_le_left _ _
  have hs : (1 : ℝ) ≤ Real.sqrt I.n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hf : 0 < I.f := Module.finrank_pos
  have hla1 : tau1 I x * tau1 I y ≤ 1 := by nlinarith
  have key := bound_le (Real.sqrt I.n) (tau1 I x * tau1 I y) (∑ v, r v) (I.n ^ 2) I.f hs
    (mul_pos hx hy) hla1 (Finset.sum_nonneg fun v _ => hr v) hf
  push_cast at key
  exact ⟨hfin, hcard.trans key⟩

end GlobalTheory.Dec.BoundedDistance
end

