import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0769
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1355
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1525
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0771
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0107
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommuteOfMemZalg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1524
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0333
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1457
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyNotMemChartBallSaturation
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.SaturationClosed

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

omit [NumberField E] [IsCMField E] in

def adjEnt {Ψ : Finset (E →+* ℂ)} (k w : Frame Ψ r) (τ : Ψ) (a c : Fin r) : ℂ :=
  (Matrix.adjugate (mat k τ) * mat w τ) a c

omit [NumberField E] [IsCMField E] in
theorem lact_lact {Ψ : Finset (E →+* ℂ)} (a b : GL (Fin r) E) (x : Frame Ψ r) :
    lact a (lact b x) = lact (a * b) x := by
  funext τ
  show ((a : Matrix (Fin r) (Fin r) E).map τ.1 * ((b : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) :
    Matrix (Fin r) (Fin r) ℂ) = (((a * b : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

omit [NumberField E] [IsCMField E] in
theorem lact_one {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show (((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]; rfl

omit [NumberField E] [IsCMField E] in

theorem adjEnt_rmul {Ψ : Finset (E →+* ℂ)} (k b : Frame Ψ r) (hb : b ∈ Bor Ψ r) (τ : Ψ) (a c : Fin r)
    (hca : c < a) : adjEnt k (rmul k b) τ a c = 0 := by
  have h1 : mat (rmul k b) τ = mat k τ * mat b τ := rfl
  rw [adjEnt, h1, ← Matrix.mul_assoc, Matrix.adjugate_mul]
  simp [Matrix.smul_mul, mat, (hb τ).2 a c hca]

omit [NumberField E] [IsCMField E] in

theorem exists_of_adjEnt {Ψ : Finset (E →+* ℂ)} (k w : Frame Ψ r) (hk : ∀ τ, (mat k τ).det ≠ 0)
    (hw : ∀ τ, (mat w τ).det ≠ 0) (h0 : ∀ τ a c, c < a → adjEnt k w τ a c = 0) :
    ∃ b ∈ Bor Ψ r, w = rmul k b := by
  refine ⟨fun τ => ((mat k τ)⁻¹ * mat w τ : Matrix (Fin r) (Fin r) ℂ), fun τ => ⟨?_, fun a c hca => ?_⟩, ?_⟩
  · show ((mat k τ)⁻¹ * mat w τ).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (inv_ne_zero (hk τ)) (hw τ)
  · show ((mat k τ)⁻¹ * mat w τ) a c = 0
    rw [Matrix.inv_def, Matrix.smul_mul, Matrix.smul_apply]
    have := h0 τ a c hca
    rw [adjEnt] at this
    rw [this, smul_zero]
  · funext τ
    show mat w τ = mat k τ * ((mat k τ)⁻¹ * mat w τ)
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 (hk τ))]

omit [NumberField E] [IsCMField E] in
theorem continuous_mat {α : Type} [TopologicalSpace α] {Ψ : Finset (E →+* ℂ)} {f : α → Frame Ψ r}
    (hf : Continuous f) (τ : Ψ) : Continuous fun p => mat (f p) τ :=
  (continuous_apply τ).comp hf

omit [NumberField E] [IsCMField E] in
theorem continuous_lact {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) :
    Continuous (lact (Ψ := Ψ) γ) := by
  refine continuous_pi fun τ => ?_
  exact continuous_const.matrix_mul (continuous_mat continuous_id τ)

omit [NumberField E] [IsCMField E] in
theorem continuous_adjEnt {α : Type} [TopologicalSpace α] {Ψ : Finset (E →+* ℂ)} {f g : α → Frame Ψ r}
    (hf : Continuous f) (hg : Continuous g) (τ : Ψ) (a c : Fin r) :
    Continuous fun p => adjEnt (f p) (g p) τ a c :=
  (((continuous_mat hf τ).matrix_adjugate).matrix_mul (continuous_mat hg τ)).matrix_elem a c

theorem eventually_not_mem_saturation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (x : Frame X.Ψ r) (ρ : ℝ), (∀ z : V (nd X), ‖z‖ ≤ ρ → z ∈ OmF X x) →
    ∀ y ∈ X.dom, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧
      y = lact γ (rmul (cpt X x z) b)) →
    ∀ᶠ y' in 𝓝 y, ¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧
      y' = lact γ (rmul (cpt X x z) b) := by
  intro E _ _ _ r X x ρ hΩ y hy hny
  have hcpt : Continuous (cpt X x) := (GlobalTheory.InterpCompare.differentiable_chart X x).continuous
  have hK : IsCompact (Metric.closedBall (0 : V (nd X)) ρ) := isCompact_closedBall 0 ρ
  have key : ∀ z ∈ Metric.closedBall (0 : V (nd X)) ρ, ∀ᶠ p : Frame X.Ψ r × V (nd X) in 𝓝 (y, z),
      ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, p.1 ≠ lact γ (rmul (cpt X x p.2) b) := by
    intro z hz
    have hz' : ‖z‖ ≤ ρ := by simpa using hz
    have hk : cpt X x z ∈ X.dom := hΩ z hz'
    obtain ⟨U, hU, U', hU', hfin⟩ := GlobalTheory.ClosedDiscontinuity.propDisc_closed r X y hy _ hk
    have h1 : ∀ᶠ p : Frame X.Ψ r × V (nd X) in 𝓝 (y, z), p.1 ∈ U ∧ cpt X x p.2 ∈ U' := by
      refine Filter.Eventually.and (continuous_fst.continuousAt.preimage_mem_nhds hU) ?_
      exact (hcpt.comp continuous_snd).continuousAt.preimage_mem_nhds hU'
    have h2 : ∀ᶠ p : Frame X.Ψ r × V (nd X) in 𝓝 (y, z),
        ∀ δ ∈ {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ u ∈ U, ∃ u' ∈ U', ∃ b ∈ Bor X.Ψ r, lact γ u = rmul u' b},
          ∃ τ : X.Ψ, ∃ a c : Fin r, c < a ∧ adjEnt (cpt X x p.2) (lact δ p.1) τ a c ≠ 0 := by
      refine (Filter.eventually_all_finite hfin).2 fun δ hδ => ?_
      have hopen : IsOpen {p : Frame X.Ψ r × V (nd X) |
          ∃ τ : X.Ψ, ∃ a c : Fin r, c < a ∧ adjEnt (cpt X x p.2) (lact δ p.1) τ a c ≠ 0} := by
        simp only [Set.setOf_exists]
        refine isOpen_iUnion fun τ => isOpen_iUnion fun a => isOpen_iUnion fun c => ?_
        by_cases hca : c < a
        · simp only [hca, true_and]
          exact isOpen_ne_fun (continuous_adjEnt (hcpt.comp continuous_snd)
            ((continuous_lact δ).comp continuous_fst) τ a c) continuous_const
        · simp [hca]
      refine hopen.mem_nhds ?_
      by_contra hcon
      simp only [Set.mem_setOf_eq, not_exists, not_and, not_not] at hcon
      have hdk : ∀ τ, (mat (cpt X x z) τ).det ≠ 0 := fun τ => (hk τ).1
      have hdw : ∀ τ, (mat (lact δ y) τ).det ≠ 0 := by
        intro τ h0
        have e : y = lact δ⁻¹ (lact δ y) := by rw [lact_lact, inv_mul_cancel, lact_one]
        have : (mat y τ).det = 0 := by
          rw [e]
          show (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat (lact δ y) τ).det = 0
          rw [Matrix.det_mul, h0, mul_zero]
        exact (hy τ).1 this
      obtain ⟨b, hb, hwb⟩ := exists_of_adjEnt _ _ hdk hdw hcon
      refine hny ⟨δ⁻¹, X.Γ.inv_mem hδ.1, b, hb, z, hz', ?_⟩
      rw [← hwb, lact_lact, inv_mul_cancel, lact_one]
    filter_upwards [h1, h2] with p hp1 hp2
    intro γ hγ b hb he
    have hδ : γ⁻¹ ∈ {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ u ∈ U, ∃ u' ∈ U', ∃ b ∈ Bor X.Ψ r, lact γ u = rmul u' b} := by
      refine ⟨X.Γ.inv_mem hγ, p.1, hp1.1, cpt X x p.2, hp1.2, b, hb, ?_⟩
      rw [he, lact_lact, inv_mul_cancel, lact_one]
    obtain ⟨τ, a, c, hca, hne⟩ := hp2 _ hδ
    apply hne
    rw [he, lact_lact, inv_mul_cancel, lact_one]
    exact adjEnt_rmul _ _ hb τ a c hca
  filter_upwards [hK.eventually_forall_of_forall_eventually
    (P := fun y' z => ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, y' ≠ lact γ (rmul (cpt X x z) b)) key] with y' hy'
  rintro ⟨γ, hγ, b, hb, z, hz, he⟩
  exact hy' z (by simpa using hz) γ hγ b hb he

end GlobalTheory.SaturationClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockProjectionFlagUnipotentRadical
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.BlockForms.Proj

open GlobalTheory.StdPar

section Abstract

variable {A : Type} [CommRing A] {n r : ℕ} {X : Matrix (Fin n) (Fin r) A} {K : Matrix (Fin r) (Fin n) A}

theorem mulVec_left_inv (hKX : K * X = 1) {I : Set (Fin r)} {y : Fin n → A}
    (hy : y ∈ Submodule.span A ((fun i => Xᵀ i) '' I)) : X *ᵥ (K *ᵥ y) = y := by
  have : Submodule.span A ((fun i => Xᵀ i) '' I) ≤ LinearMap.eqLocus (X * K).mulVecLin LinearMap.id := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, -, rfl⟩
    change (X * K * X).col i = _
    rw [Matrix.mul_assoc, hKX, Matrix.mul_one]
    rfl
  rw [mulVec_mulVec]
  exact this hy

theorem mulVec_mem_span {I : Set (Fin r)} {a : Fin r → A} (ha : ∀ i, i ∉ I → a i = 0) :
    X *ᵥ a ∈ Submodule.span A ((fun i => Xᵀ i) '' I) := by
  rw [mulVec_eq_sum]
  refine sum_mem fun i _ => ?_
  rw [op_smul_eq_smul]
  by_cases hi : i ∈ I
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · rw [ha i hi, zero_smul]
    exact zero_mem _

theorem coef_mul (hKX : K * X = 1) (M N : Matrix (Fin n) (Fin n) A) (hN : (N - 1) * X = X * (K * ((N - 1) * X))) :
    K * ((M * N - 1) * X) = K * ((M - 1) * X) + K * ((N - 1) * X) + K * ((M - 1) * X) * (K * ((N - 1) * X)) := by
  have e : M * N - 1 = (M - 1) + (N - 1) + (M - 1) * (N - 1) := by noncomm_ring
  rw [e, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_assoc K, Matrix.mul_assoc (M - 1) X, ← hN,
    Matrix.mul_assoc (M - 1)]

end Abstract

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X : Matrix (Fin n) (Fin r) E}
  {K : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)}

omit [NumberField E] in

theorem col_mem {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) (j : Fin r) :
    (((matHom _ σ J g).1 - 1) * adMat F X).col j ∈ colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j} := by
  have := (Subgroup.mem_iInf.1 hg.1 j).2 _ (Submodule.subset_span ⟨j, rfl, rfl⟩)
  rw [Matrix.sub_mul, Matrix.one_mul]
  exact this

omit [NumberField E] in

theorem coef_eq_zero (hKX : K * adMat F X = 1) {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) {i j : Fin r}
    (hi : ¬ ∃ k ∈ T, i ≤ k ∧ k < j) : (K * (((matHom _ σ J g).1 - 1) * adMat F X) : Matrix (Fin r) (Fin r) _) i j = 0 :=
  Norm.row_span (Z := K) (a := i) (fun m hm => by
    rw [hKX, Matrix.one_apply_ne]
    rintro rfl
    exact hi hm) (col_mem hg j)

omit [NumberField E] in

theorem eq_mul_coef (hKX : K * adMat F X = 1) {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ unip σ J X T) :
    ((matHom _ σ J g).1 - 1) * adMat F X = adMat F X * (K * (((matHom _ σ J g).1 - 1) * adMat F X)) :=
  Matrix.ext_col fun j => (mulVec_left_inv hKX (col_mem hg j)).symm

theorem exists_blockProj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (r' : ℕ), 0 < r' → r' < d → ∀ k : Fin r, k.val + 1 = l + r' →
        ∃ π : GlobalTheory.StdPar.unip σ J Xf (insert k S) → (GlobalTheory.CuspRep.BlockIx d r' → GlobalTheory.CuspRep.Ad E), Continuous π ∧
          (∀ a b, π (a * b) = π a + π b) ∧
          (∀ (a : GlobalTheory.StdPar.unip σ J Xf (insert k S)) x, (a : GAd σ J) = ι (GlobalTheory.CuspRep.unip x) → π a = x) ∧
          (∀ a : GlobalTheory.StdPar.unip σ J Xf (insert k S), π a = 0 ↔ (a : GAd σ J) ∈ GlobalTheory.StdPar.unip σ J Xf S) ∧
          (∀ a : GlobalTheory.StdPar.unip σ J Xf (insert k S), (a : GAd σ J) ∈ ratPts σ J → π a ∈ GlobalTheory.CuspRep.ratN E d r') := by
  intro F E _ _ _ _ _ _ σ hσ n J hJ r X Y hW S l d h ι ⟨Φ, jj, hΦc, _, hj, hΦ, hι⟩ hS ⟨k₀, hk₀, hk₀'⟩ hl r' hr0 hrd k hk
  obtain ⟨_, _⟩ := ring_facts (F := F) (E := E)
  let e : Fin d → Fin r := fun a => ⟨l + a.val, by omega⟩
  have hm : ∀ {a b c : ℕ} (U : Matrix (Fin a) (Fin b) E) (V : Matrix (Fin b) (Fin c) E),
      adMat F U * adMat F V = adMat F (U * V) := fun U V => (Matrix.map_mul).symm
  have hKX : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [hm, yx hσ hJ hW]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hKY : adMat F (cT (σ : E →+* E) Y * J) * adMat F Y = 0 := by
    rw [hm, hW.yy]; exact Matrix.map_zero _ (map_zero _)
  have hΦE : ∀ x : E, Φ (inclR (F := F) (AF F) x) = algebraMap E (AdeleRing (𝓞 E) E) x := fun x => by
    rw [hΦ]
    refine Prod.ext ?_ ?_
    · show jj (GlobalTheory.LFun.infTens F E ((1 : AF F) ⊗ₜ[F] x)) = algebraMap E (InfiniteAdeleRing E) x
      rw [← hj x]
      congr 1
    · show GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x)) =
        algebraMap E (FiniteAdeleRing (𝓞 E) E) x
      have e : GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x) = (1 : Af F) ⊗ₜ[F] x := by simp [GlobalTheory.LFun.finTens]
      rw [e, show GlobalTheory.LFun.finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from GlobalTheory.LFun.toFinAd_tmul 1 x, map_one, one_mul]
  let c : GAd σ J → Matrix (Fin r) (Fin r) (AF F ⊗[F] E) := fun g =>
    adMat F (cT (σ : E →+* E) Y * J) * (((matHom _ σ J g).1 - 1) * adMat F X)
  have hc : Continuous c := continuous_const.matrix_mul ((continuous_mat.sub continuous_const).matrix_mul continuous_const)
  refine ⟨fun a p => Φ (c a (e p.1.1) (e p.1.2)), ?_, fun a b => ?_, fun a x hx => ?_, fun a => ⟨fun h0 => ?_, fun ha => ?_⟩,
    fun a ha => ?_⟩
  · exact continuous_pi fun p => hΦc.comp ((hc.comp continuous_subtype_val).matrix_elem _ _)
  · funext p
    have h1 : c (a * b : unip σ J X (insert k S)) = c a + c b + c a * c b := by
      simp only [c]
      rw [Subgroup.coe_mul, map_mul, Units.val_mul]
      exact coef_mul hKX _ _ (eq_mul_coef hKX b.2)
    have h2 : (c a * c b) (e p.1.1) (e p.1.2) = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun m _ => ?_
      have hp2 := p.1.2.2
      by_cases hmk : m ≤ k
      · rw [show c a (e p.1.1) m = 0 from coef_eq_zero hKX a.2 ?_, zero_mul]
        rintro ⟨k', hk', h3, h4⟩
        have h3' : l + p.1.1.val ≤ k'.val := h3
        have h4' : k'.val < m.val := h4
        have h5 : m.val ≤ k.val := hmk
        rcases Finset.mem_insert.1 hk' with rfl | hk'
        · omega
        · exact hS k' (by omega) (by omega) hk'
      · rw [show c b m (e p.1.2) = 0 from coef_eq_zero hKX b.2 ?_, mul_zero]
        rintro ⟨k', hk', h3, h4⟩
        have h3' : m.val ≤ k'.val := h3
        have h4' : k'.val < l + p.1.2.val := h4
        have h5 : ¬ m.val ≤ k.val := hmk
        rcases Finset.mem_insert.1 hk' with rfl | hk'
        · omega
        · exact hS k' (by omega) (by omega) hk'
    change Φ (c (a * b : unip σ J X (insert k S)) _ _) = Φ _ + Φ _
    rw [h1, Matrix.add_apply, h2, add_zero, Matrix.add_apply, map_add]
  · funext p
    have b1 : adMat F (cT (σ : E →+* E) (blkCols h Y) * J) * adMat F (blkCols h X) = 1 := Matrix.ext fun i j =>
      (congrFun (congrFun hKX (e i)) (e j)).trans (by simp [Matrix.one_apply, e, Fin.ext_iff])
    have b2 : adMat F (cT (σ : E →+* E) (blkCols h Y) * J) * adMat F (blkCols h Y) = 0 := Matrix.ext fun i j =>
      congrFun (congrFun hKY (e i)) (e j)
    have h1 : c a (e p.1.1) (e p.1.2) = (adMat F (cT (σ : E →+* E) (blkCols h Y) * J) *
        (((matHom _ σ J (a : GAd σ J)).1 - 1) * adMat F (blkCols h X)) : Matrix (Fin d) (Fin d) _) p.1.1 p.1.2 := rfl
    have hne : p.1.1 ≠ p.1.2 := fun h' => by have := p.2; rw [h'] at this; omega
    change Φ (c a _ _) = _
    rw [h1, hx, hι, add_assoc, add_sub_cancel_left, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc, b1,
      Matrix.mul_one, ← Matrix.mul_assoc, b1, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (adMat F _),
      b2, Matrix.zero_mul, add_zero, Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero, Matrix.map_apply,
      RingEquiv.apply_symm_apply]
    change (1 + GlobalTheory.CuspRep.nilM x : Matrix (Fin d) (Fin d) _) p.1.1 p.1.2 = _
    rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, GlobalTheory.CuspRep.nilM, Matrix.of_apply, dif_pos p.2]
  · have ha := a.2
    have hset : {i | ∃ k' ∈ insert k S, i ≤ k'} = {i | ∃ k' ∈ S, i ≤ k'} := Set.ext fun i =>
      ⟨fun ⟨k', hk', h1⟩ => by
        rcases Finset.mem_insert.1 hk' with rfl | hk'
        · exact ⟨k₀, hk₀, h1.trans (show k'.val ≤ k₀.val by omega)⟩
        · exact ⟨k', hk', h1⟩,
      fun ⟨k', hk', h1⟩ => ⟨k', Finset.mem_insert_of_mem hk', h1⟩⟩
    refine ⟨Subgroup.mem_iInf.2 fun j => ⟨unip_iff_colSpan ha ?_, fun y hy => ?_⟩, hset ▸ ha.2⟩
    · rintro i ⟨k', hk', hik, hkj⟩ m hm
      exact ⟨k', hk', hm.le.trans hik, hkj⟩
    · unfold colSpan at hy
      rw [Set.image_singleton, Submodule.mem_span_singleton] at hy
      obtain ⟨t, rfl⟩ := hy
      rw [mulVec_smul, ← smul_sub]
      refine Submodule.smul_mem _ t ?_
      have h1 : (matHom _ σ J (a : GAd σ J)).1 *ᵥ (adMat F X)ᵀ j - (adMat F X)ᵀ j = adMat F X *ᵥ (c a).col j := by
        have := congrArg (fun Z => Matrix.col Z j) (eq_mul_coef hKX ha)
        rw [Matrix.sub_mul, Matrix.one_mul] at this
        refine Eq.trans ?_ (this.trans ?_)
        · rfl
        · simp only [c]
          rw [Matrix.sub_mul, Matrix.one_mul]
          rfl
      rw [h1]
      refine mulVec_mem_span fun i hi => ?_
      by_cases hi' : ∃ k' ∈ insert k S, i ≤ k' ∧ k' < j
      · obtain ⟨k', hk', h2, h3⟩ := hi'
        rcases Finset.mem_insert.1 hk' with rfl | hk'
        · have h2' : i.val ≤ k'.val := h2
          have h3' : k'.val < j.val := h3
          have h4 : j.val < l + d := by
            by_contra h4
            exact hi ⟨k₀, hk₀, show i.val ≤ k₀.val by omega, show k₀.val < j.val by omega⟩
          have h5 : l ≤ i.val := by
            by_contra h5
            rcases hl with hl | ⟨p, hp, hp'⟩
            · omega
            · exact hi ⟨p, hp, show i.val ≤ p.val by omega, show p.val < j.val by omega⟩
          have h6 := congrFun h0 ⟨(⟨i.val - l, by omega⟩, ⟨j.val - l, by omega⟩), by constructor <;> dsimp only <;> omega⟩
          have h7 : e ⟨i.val - l, by omega⟩ = i := Fin.ext (show l + (i.val - l) = i.val by omega)
          have h8 : e ⟨j.val - l, by omega⟩ = j := Fin.ext (show l + (j.val - l) = j.val by omega)
          change Φ (c a (e ⟨i.val - l, _⟩) (e ⟨j.val - l, _⟩)) = 0 at h6
          rw [h7, h8] at h6
          exact (map_eq_zero_iff Φ Φ.injective).1 h6
        · exact absurd ⟨k', hk', h2, h3⟩ hi
      · exact coef_eq_zero hKX ha hi'
  · funext p
    change Φ (c a _ _) = 0
    rw [show c a (e p.1.1) (e p.1.2) = 0 from coef_eq_zero hKX ha ?_, map_zero]
    rintro ⟨k', hk', h3, h4⟩
    have h3' : l + p.1.1.val ≤ k'.val := h3
    have h4' : k'.val < l + p.1.2.val := h4
    have hp2 := p.1.2.2
    exact hS k' (by omega) (by omega) hk'
  · obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 ha)
    have h1 : (matHom _ σ J (a : GAd σ J)).1 = adMat F γ.1 := (congrArg Units.val hγ).symm
    refine ⟨fun p => (cT (σ : E →+* E) Y * J * ((γ.1 - 1) * X) : Matrix (Fin r) (Fin r) E) (e p.1.1) (e p.1.2), funext fun p => ?_⟩
    have h2 : c a = adMat F (cT (σ : E →+* E) Y * J * ((γ.1 - 1) * X)) := by
      simp only [c]
      rw [h1, ← hm (cT (σ : E →+* E) Y * J), ← hm (γ.1 - 1)]
      congr 2
      rw [adMat, adMat, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    change _ = Φ (c a _ _)
    rw [h2]
    exact (hΦE _).symm

end GlobalTheory.BlockForms.Proj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpand
section
noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.CuspRep

namespace GlobalTheory.LeviGL.ZGood

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem zalg_commute {z z' : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (hz' : z' ∈ Zalg E a) : Commute z z' := by
  first
  | exact @_root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg
  | exact _root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg
  | (apply _root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg ..)

theorem chart_left (φ : GA E a → ℂ) (h g : GA E a) :
    chart (fun x => φ (h * x)) g = chart φ (h * g) := by
  funext x
  simp only [chart, mul_assoc]

def leftRat (γ : GL (Fin a) E) : Module.End ℂ (Sm E a) where
  toFun φ := ⟨fun g => φ.1 (ratGL E a γ * g), fun g => by
    rw [chart_left]
    exact φ.2 _⟩
  map_add' φ ψ := rfl
  map_smul' c φ := rfl

@[simp] theorem leftRat_apply (γ : GL (Fin a) E) (φ : Sm E a) (g : GA E a) :
    (leftRat γ φ).1 g = φ.1 (ratGL E a γ * g) := rfl

end GlobalTheory.LeviGL.ZGood

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeHermitianPairing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open MeasureTheory

namespace GlobalTheory.MultPetersson

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem integrableOn_star_mul (μ : Measure (GA D V)) (𝓕 C : Set (GA D V)) (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (hC : IsCompact C)
    (hcov : ∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c)
    {f f' : GA D V → ℂ} (hf : Continuous f) (hf' : Continuous f')
    (hl : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) (hl' : ∀ γ ∈ GQ V, ∀ g, f' (γ * g) = f' g) :
    IntegrableOn (fun g => star (f g) * f' g) 𝓕 μ :=
  GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain V μ 𝓕 C hμ h𝓕 hC hcov _
    ((continuous_star.comp hf).mul hf') (fun γ hγ g => by simp only [hl γ hγ, hl' γ hγ])

def pet (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) {ι : Type} [Fintype ι] (M : DSModel V S) (w : ι → M.Vec)
    (x y : MMap M) : ℂ :=
  ∑ i, ∫ g in 𝓕, star (x (w i) g) * y (w i) g ∂μ

variable (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) {ι : Type} [Fintype ι] (M : DSModel V S) (w : ι → M.Vec)

end GlobalTheory.MultPetersson

namespace GlobalTheory.MultPetersson

open MeasureTheory

end GlobalTheory.MultPetersson
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelDomainReductionStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegel_domain_reduction : GlobalTheory.Published.SiegelSetUnitary → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∃ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y ∧ ∃ (Cc : Set (UA σ X.J)) (c C : ℝ) (A : ℕ),
      IsCompact Cc ∧ 0 < c ∧ ∀ g : UA σ X.J, ∃ γ ∈ ratU σ X.J, ∃ (t : Fin q → ℝ) (a κ : UA σ X.J),
        (∀ i, c ≤ t i) ∧ IsTorusU x y t a ∧ κ ∈ Cc ∧ γ * g = a * κ ∧ (ht (a * κ) : ℝ) ≤ C * (1 + ∏ i, t i) ^ A := by
  first | exact @GlobalTheory.SiegelHt.siegel_reduction | exact GlobalTheory.SiegelHt.siegel_reduction | (intros; apply GlobalTheory.SiegelHt.siegel_reduction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEllipticCharpolyCompactSectionStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_ellipticCharpoly_compact_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ C : ∀ w : Pl E, Set (GLw n w), (∀ w, IsCompact (C w)) → (∀ᶠ w in cofinite, C w ⊆ GlobalTheory.LFun.KGL w n) → {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, ∃ g ∈ C w, g.val.charpoly = atPl w P}.Finite := by
  first | exact @GlobalTheory.FinChar.finite_ell_charpoly | exact GlobalTheory.FinChar.finite_ell_charpoly | (intros; apply GlobalTheory.FinChar.finite_ell_charpoly <;> assumption)
end

