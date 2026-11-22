import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0610
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealTemperedBounds.StepsD
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0612
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaFourierCoefficientWeylIntegral
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.RCellInv

variable {D : D7} {t ρ : ℕ}

theorem block_matrix_mul {n : ℕ} (a b c d a' b' c' d' : Mx D n n) :
    (blk4 a b c d * blk4 a' b' c' d' : Mx D (n + n) (n + n)) =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [blk4]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem mat_mul_mat {n : ℕ} (g h : G D n) : mat (g * h) = mat g * mat h := by
  simp only [mat, map_mul, Units.val_mul]

theorem trace_adj_eq {n : ℕ} (M : Mx D n n) : Matrix.trace (adj M) = cA D (Matrix.trace M) := by
  rw [adj, Matrix.trace_transpose]
  exact (AddMonoidHom.map_trace (cA D).toAddMonoidHom M).symm

theorem adj_gram (b₀ : HermE D ρ) : adj (b₀.1.map (incA D)) = b₀.1.map (incA D) := by
  ext i j
  have h := congrFun (congrFun b₀.2 i) j
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply] at h ⊢
  rw [GlobalTheory.DualPairCheck.cA_incA]
  exact congrArg (incA D) h

theorem adj_pr (b₀ : HermE D ρ) (x y : Mx D ρ t) : adj (pr b₀ x y) = pr b₀ y x := by
  simp only [pr, adj_mul, adj_adj, adj_gram, Matrix.mul_assoc]

theorem pr_neg_left (b₀ : HermE D ρ) (x y : Mx D ρ t) : pr b₀ (-x) y = -pr b₀ x y := by
  simp only [pr, adj_neg, Matrix.neg_mul]

theorem trA_trace_pr_swap (b₀ : HermE D ρ) (x y : Mx D ρ t) :
    trA (Matrix.trace (pr b₀ y x)) = trA (Matrix.trace (pr b₀ x y)) := by
  rw [← adj_pr b₀ x y, trace_adj_eq]
  exact GlobalTheory.DualPairCheck.trace_cA _

theorem conj_char {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (u : AF D.host.F) :
    conj (ψ u) = ψ (-u) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 u)]

theorem det_neg_one (t : ℕ) :
    Matrix.GeneralLinearGroup.det (-1 : GL (Fin t) (AE D)) =
      Units.map (incA D).toMonoidHom ((-1 : (D.host.E)ˣ) ^ t) := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_neg]

theorem absA_det_neg_one (t : ℕ) : absA D (Matrix.GeneralLinearGroup.det (-1 : GL (Fin t) (AE D))) = 1 := by
  have h : absA D (Matrix.GeneralLinearGroup.det (-1 : GL (Fin t) (AE D))) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, neg_one_sq, map_one, map_one]
  exact (pow_eq_one_iff.1 h).resolve_right two_ne_zero

theorem weyl_sq {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) {θ : InfFam D}
    {b₀ : HermE D ρ} {μ : Measure (Mx D ρ t)} {Ω : G D t → Mx D ρ t → ℂ} (hΩ : IsTh ψ χ θ b₀ μ Ω)
    {w : G D t} (hw : IsW w) (h : G D t) (y : Mx D ρ t) : Ω (w * (w * h)) y = Ω h (-y) := by
  have hm : mat (w * w) = blk4 (-1 : GL (Fin t) (AE D)).1 0 0 (adj ((-1 : GL (Fin t) (AE D))⁻¹).1) := by
    have hi : ((-1 : GL (Fin t) (AE D))⁻¹) = -1 := by
      rw [inv_eq_iff_mul_eq_one]
      simp
    have ha : adj (-1 : Mx D t t) = -1 := by
      rw [adj_neg, adj_one]
    rw [hi, mat_mul_mat, show mat w = _ from hw, block_matrix_mul]
    simp [ha]
  have hl := hΩ.levi (w * w) (-1) hm h y
  have hc : (χ (Matrix.GeneralLinearGroup.det (-1 : GL (Fin t) (AE D))) : ℂ) = 1 := by
    rw [det_neg_one]
    have := hχ.2 ((-1 : (D.host.E)ˣ) ^ t)
    rw [this]
    simp
  rw [← mul_assoc, hl, hc, absA_det_neg_one]
  simp [npow]

end GlobalTheory.CompanionTheory.RCellInv

open GlobalTheory.CompanionTheory.RCellInv in

theorem GlobalTheory.CompanionTheory.RCellInv.fourier_inv : ∀ {D : D7} {t ρ : ℕ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) {θ : InfFam D} {b₀ : HermE D ρ} {μ : Measure (Mx D ρ t)} {Ω : G D t → Mx D ρ t → ℂ} (hΩ : IsTh ψ χ θ b₀ μ Ω) {nb : hermA D t → G D t} (hnb : IsNMap nb) {w : G D t} (hw : IsW w) (b : hermA D t) (y₀ : Mx D ρ t), ∫ y, ψ (trA (Matrix.trace (pr b₀ y y₀))) * conj (Ω (w * nb b) y) ∂μ = conj (ψ (halfTr (Matrix.trace (mm b.1 (pr b₀ y₀ y₀)))) * Ω 1 y₀) := by
  intro D t ρ ψ hψ χ hχ θ b₀ μ Ω hΩ nb hnb w hw b y₀
  have hint : ∀ y, ψ (trA (Matrix.trace (pr b₀ y y₀))) * conj (Ω (w * nb b) y) =
      conj (Ω (w * nb b) y * ψ (trA (Matrix.trace (pr b₀ (-y₀) y)))) := by
    intro y
    have hneg : -trA (Matrix.trace (pr b₀ (-y₀) y)) = trA (Matrix.trace (pr b₀ y y₀)) := by
      rw [pr_neg_left, Matrix.trace_neg, trA_trace_pr_swap b₀ y₀ y]
      simp only [trA, map_neg, neg_neg]
    rw [map_mul, conj_char hψ, hneg, mul_comm]
  have hu := hΩ.unip (nb b) b.1 (hnb b) 1 y₀
  rw [mul_one] at hu
  simp only [hint]
  rw [integral_conj, ← hΩ.weyl w hw (w * nb b) (-y₀), weyl_sq hχ hΩ hw, neg_neg, hu]
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceConjTransposeMulSelf
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn GlobalTheory.CompanionTheory.ThTot
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot.Orb
variable {D : D7}

def fro {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

theorem fro_nonneg {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) : 0 ≤ fro A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem fro_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (B : Matrix (Fin b) (Fin c) ℂ) :
    fro (A * B) ≤ fro A * fro B := by
  have key : ∀ i j, ‖(A * B) i j‖ ^ 2 ≤ (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) := by
    intro i j
    have h1 : ‖(A * B) i j‖ ≤ ∑ k, ‖A i k‖ * ‖B k j‖ := by
      rw [Matrix.mul_apply]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => (norm_mul _ _).le)
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖A i k‖) (fun k => ‖B k j‖)
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  unfold fro
  calc ∑ i, ∑ j, ‖(A * B) i j‖ ^ 2 ≤ ∑ i, ∑ j, (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
    _ = (∑ i, ∑ k, ‖A i k‖ ^ 2) * ∑ k, ∑ j, ‖B k j‖ ^ 2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum, Finset.sum_comm]

theorem norm_entry_sq_le {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (i : Fin a) (j : Fin b) :
    ‖A i j‖ ^ 2 ≤ fro A := by
  unfold fro
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖A i j‖ ^ 2) (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => ‖A i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)

theorem continuous_fro {a b : ℕ} : Continuous (fro : Matrix (Fin a) (Fin b) ℂ → ℝ) := by
  unfold fro
  fun_prop

theorem trace_conjTranspose_mul_self {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) :
    Matrix.trace (Aᴴ * A) = ((fro A : ℝ) : ℂ) := by
  unfold fro
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.conj_mul']
  rfl

def nrm {m : ℕ} {n : ℕ} (l : D.what₂.Tau → ℝ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  ∑ τ, |l τ| * fro (z τ)

theorem nrm_nonneg {m n : ℕ} (l : D.what₂.Tau → ℝ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : 0 ≤ nrm l z :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (fro_nonneg _)

theorem entry_le_nrm {m n : ℕ} (l : D.what₂.Tau → ℝ) (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) (τ) (i j) :
    |l τ| * ‖z τ i j‖ ^ 2 ≤ nrm l z := by
  refine le_trans (mul_le_mul_of_nonneg_left (norm_entry_sq_le _ i j) (abs_nonneg _)) ?_
  exact Finset.single_le_sum (f := fun τ => |l τ| * fro (z τ)) (fun _ _ => mul_nonneg (abs_nonneg _) (fro_nonneg _)) (Finset.mem_univ τ)

theorem norm_le_exp {w : ℂ} {d : ℝ} (hd : 0 < d) : ‖w‖ ≤ (1 / Real.sqrt d) * Real.exp (d * ‖w‖ ^ 2) := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have h1 : Real.sqrt d * ‖w‖ ≤ Real.exp (d * ‖w‖ ^ 2) := by
    have h2 : d * ‖w‖ ^ 2 + 1 ≤ Real.exp (d * ‖w‖ ^ 2) := Real.add_one_le_exp _
    have h3 : (Real.sqrt d * ‖w‖) ^ 2 = d * ‖w‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hd.le]
    nlinarith [sq_nonneg (Real.sqrt d * ‖w‖ - 1)]
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hs]
  linarith [mul_comm (Real.sqrt d) ‖w‖]

theorem evalPoly_bound {m n : ℕ} (l : D.what₂.Tau → ℝ) (hl : ∀ τ, l τ ≠ 0)
    (q : MvPolynomial (D.what₂.Tau × Fin m × Fin n × Bool) ℂ) :
    ∀ e : ℝ, 0 < e → ∃ C : ℝ, 0 ≤ C ∧ ∀ z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ,
      ‖evalPoly q z‖ ≤ C * Real.exp (e * nrm l z) := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    intro e he
    refine ⟨‖a‖, norm_nonneg _, fun z => ?_⟩
    simp only [evalPoly, MvPolynomial.eval_C]
    have : 1 ≤ Real.exp (e * nrm l z) := Real.one_le_exp (mul_nonneg he.le (nrm_nonneg _ _))
    nlinarith [norm_nonneg a]
  | add p q hp hq =>
    intro e he
    obtain ⟨C₁, h₁, b₁⟩ := hp e he
    obtain ⟨C₂, h₂, b₂⟩ := hq e he
    refine ⟨C₁ + C₂, add_nonneg h₁ h₂, fun z => ?_⟩
    have : evalPoly (p + q) z = evalPoly p z + evalPoly q z := by simp [evalPoly]
    rw [this, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (b₁ z) (b₂ z))
  | mul_X p k hp =>
    intro e he
    obtain ⟨C₁, h₁, b₁⟩ := hp (e / 2) (by positivity)
    obtain ⟨τ, i, j, b⟩ := k
    have hlt : 0 < |l τ| := abs_pos.2 (hl τ)
    set d : ℝ := e / 2 * |l τ| with hd
    have hd0 : 0 < d := by positivity
    refine ⟨C₁ * (1 / Real.sqrt d), by positivity, fun z => ?_⟩
    have hm : evalPoly (p * MvPolynomial.X (τ, i, j, b)) z = evalPoly p z *
        (if b then conj (z τ i j) else z τ i j) := by simp [evalPoly]
    have hx : ‖(if b then conj (z τ i j) else z τ i j)‖ = ‖z τ i j‖ := by
      split_ifs <;> simp
    rw [hm, norm_mul, hx]
    have h1 := norm_le_exp (w := z τ i j) hd0
    have h2 : Real.exp (d * ‖z τ i j‖ ^ 2) ≤ Real.exp (e / 2 * nrm l z) := by
      apply Real.exp_le_exp.2
      have := entry_le_nrm l z τ i j
      rw [hd, mul_assoc]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have h3 : ‖z τ i j‖ ≤ (1 / Real.sqrt d) * Real.exp (e / 2 * nrm l z) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    calc ‖evalPoly p z‖ * ‖z τ i j‖
        ≤ (C₁ * Real.exp (e / 2 * nrm l z)) * ((1 / Real.sqrt d) * Real.exp (e / 2 * nrm l z)) :=
          mul_le_mul (b₁ z) h3 (norm_nonneg _) (by positivity)
      _ = C₁ * (1 / Real.sqrt d) * Real.exp (e * nrm l z) := by
          have : Real.exp (e * nrm l z) = Real.exp (e / 2 * nrm l z) * Real.exp (e / 2 * nrm l z) := by
            rw [← Real.exp_add]; ring_nf
          rw [this]; ring

end GlobalTheory.CompanionTheory.ThTot.Orb

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoSegmentNongenericQuotient
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZSeg.TwoSeg

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem range_le_comap (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (f : σ.IntertwiningMap π) (g : GL (Fin N) k) :
    LinearMap.range f.toLinearMap ≤ (LinearMap.range f.toLinearMap).comap (π g) := by
  rintro _ ⟨w, rfl⟩
  exact ⟨σ g w, Representation.IntertwiningMap.isIntertwining _ _ f g w⟩

def quotRep (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (f : σ.IntertwiningMap π) : Representation ℂ (GL (Fin N) k) (V ⧸ LinearMap.range f.toLinearMap) where
  toFun g := (LinearMap.range f.toLinearMap).mapQ _ (π g) (range_le_comap π σ f g)
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp

@[simp] theorem quotRep_mk (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (f : σ.IntertwiningMap π) (g : GL (Fin N) k) (v : V) :
    quotRep π σ f g ((LinearMap.range f.toLinearMap).mkQ v) = (LinearMap.range f.toLinearMap).mkQ (π g v) := rfl

theorem mkQ_mem_twKer (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (f : σ.IntertwiningMap π) (U : Subgroup (GL (Fin N) k)) (θ : U →* ℂˣ) {v : V} (hv : v ∈ twKer π U θ) :
    (LinearMap.range f.toLinearMap).mkQ v ∈ twKer (quotRep π σ f) U θ := by
  have hle : twKer π U θ ≤ (twKer (quotRep π σ f) U θ).comap (LinearMap.range f.toLinearMap).mkQ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, u, rfl⟩
    refine Submodule.subset_span ⟨n, (LinearMap.range f.toLinearMap).mkQ u, ?_⟩
    simp only [LinearMap.map_sub, LinearMap.map_smul]
    rfl
  exact hle hv

theorem isSmooth_of_injective (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (f : σ.IntertwiningMap π) (hf : Function.Injective f) (hπ : IsSmooth π) : IsSmooth σ := by
  intro w
  have : {g : GL (Fin N) k | σ g w = w} = {g | π g (f w) = f w} := by
    ext g
    simp only [Set.mem_setOf_eq]
    rw [← Representation.IntertwiningMap.isIntertwining _ _ f g w, hf.eq_iff]
  rw [this]
  exact hπ _

theorem not_isGeneric_quotRep {ψ : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (f : σ.IntertwiningMap π) (hf : Function.Injective f) (hπ : IsSmooth π)
    (hr : Module.rank ℂ (TwJacquet π (unipB k (Fin N)) (whitChar ψ N)) ≤ 1) (hσ : IsGeneric σ) :
    ¬ IsGeneric (quotRep π σ f) := by
  rw [isGeneric_iff_isGenericFor hψ h1] at hσ ⊢
  have hσs := isSmooth_of_injective π σ f hf hπ
  unfold IsGenericFor at hσ ⊢
  rw [not_nontrivial_iff_subsingleton]

  obtain ⟨q, hq⟩ := exists_ne (0 : TwJacquet σ (unipB k (Fin N)) (whitChar ψ N))
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hw : w ∉ twKer σ (unipB k (Fin N)) (whitChar ψ N) := fun h => hq ((Submodule.Quotient.mk_eq_zero _).2 h)
  have hfw : f w ∉ twKer π (unipB k (Fin N)) (whitChar ψ N) := fun h =>
    hw (GlobalTheory.CompanionTheory.PRep.WhitExact.twKer_whitChar_reflect k ψ hψ N σ π hσs hπ f.toLinearMap hf
      (fun g v => Representation.IntertwiningMap.isIntertwining _ _ f g v) w h)
  obtain ⟨e, he⟩ := rank_le_one_iff.1 hr
  refine subsingleton_of_forall_eq 0 fun t => ?_
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  obtain ⟨a, ha⟩ := he (Submodule.Quotient.mk (f w))
  obtain ⟨b, hb⟩ := he (Submodule.Quotient.mk v)
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hfw ((Submodule.Quotient.mk_eq_zero _).1 (by rw [← ha, zero_smul]))
  have hk : v - (b / a) • f w ∈ twKer π (unipB k (Fin N)) (whitChar ψ N) := by
    refine (Submodule.Quotient.mk_eq_zero _).1 ?_
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, ← ha, ← hb, smul_smul,
      div_mul_cancel₀ _ ha0, sub_self]
  have h2 := mkQ_mem_twKer π σ f _ _ hk
  have h3 : (LinearMap.range f.toLinearMap).mkQ (f w) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 ⟨w, rfl⟩
  rw [map_sub, map_smul, h3, smul_zero, sub_zero] at h2
  exact h2

theorem exists_nonGeneric_quot {ψ : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W)
    (f : σ.IntertwiningMap π) (hf : Function.Injective f) (hns : ¬ Function.Surjective f) (hπ : IsSmooth π)
    (hr : Module.rank ℂ (TwJacquet π (unipB k (Fin N)) (whitChar ψ N)) ≤ 1) (hσ : IsGeneric σ) :
    ∃ (X : Type) (_ : AddCommGroup X) (_ : Module ℂ X) (τ : Representation ℂ (GL (Fin N) k) X)
      (q : π.IntertwiningMap τ), Function.Surjective q ∧ Nontrivial X ∧ ¬ IsGeneric τ := by
  refine ⟨V ⧸ LinearMap.range f.toLinearMap, inferInstance, inferInstance, quotRep π σ f,
    ⟨(LinearMap.range f.toLinearMap).mkQ, fun g => ?_⟩, ?_, ?_, not_isGeneric_quotRep hψ h1 π σ f hf hπ hr hσ⟩
  · ext v; rfl
  · exact Submodule.mkQ_surjective _
  · refine Submodule.Quotient.nontrivial_iff.2 fun h => hns ?_
    exact LinearMap.range_eq_top.1 h

end GlobalTheory.CompanionTheory.BZSeg.TwoSeg

namespace GlobalTheory.CompanionTheory.BZSeg

open GlobalTheory.CompanionTheory.BZSeg.TwoSeg

set_option maxHeartbeats 3000000 in

theorem twoSegNonGenQuot_of_char {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ψ : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (hsub : GlobalTheory.BZSeg.TwoSegGenericSub k) (hrank : GlobalTheory.BZSeg.WhitRankTwoSeg k) : GlobalTheory.BZSeg.TwoSegNonGenQuot k := by
  intro Δ Δ' x y N hd hpre hx hy
  obtain ⟨W, _, _, σ, f, hinj, hns, hgen⟩ := hsub Δ Δ' x y N hd hpre hx hy
  exact exists_nonGeneric_quot hψ h1 _ σ f hinj hns (isSmooth_prodIrr _ hd) (hrank ψ hψ h1 Δ Δ' x y N hd hx hy) hgen

theorem twoSegNonGenQuot : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.BZSeg.TwoSegGenericSub k → GlobalTheory.BZSeg.WhitRankTwoSeg k → GlobalTheory.BZSeg.TwoSegNonGenQuot k := by
  intro k _ _ _ _ hsub hrank
  obtain ⟨ψ, hψ, h1⟩ := exists_continuous_addChar_ne_one k
  exact twoSegNonGenQuot_of_char hψ h1 hsub hrank

end GlobalTheory.CompanionTheory.BZSeg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightVectorExplicitFormula
section
noncomputable section

open Ad3.LR

namespace GlobalTheory.CompanionTheory.WeightClosed

theorem real_factor (k : ℕ) (hk : 1 ≤ k) (Δ : ℝ) (hΔ : 0 < Δ) :
    (Δ⁻¹) ^ ((2 * (k : ℝ) - 1) / 2) * Δ ^ (-(1 : ℝ) / 2) * Δ ^ (2 * (k : ℤ) - 1) = Δ ^ (k - 1) := by
  have h1 : Δ ^ (2 * (k : ℤ) - 1) = Δ ^ (2 * (k : ℝ) - 1) := by
    rw [← Real.rpow_intCast]
    push_cast
    rfl
  rw [h1, Real.inv_rpow hΔ.le, ← Real.rpow_neg hΔ.le, ← Real.rpow_add hΔ, ← Real.rpow_add hΔ,
    ← Real.rpow_natCast]
  congr 1
  push_cast [Nat.cast_sub hk]
  ring

theorem inv_entries (h : M22) :
    ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = ((Matrix.of h).det)⁻¹ * h 1 1 ∧
    ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = -(((Matrix.of h).det)⁻¹ * h 0 1) ∧
    ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = -(((Matrix.of h).det)⁻¹ * h 1 0) ∧
    ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = ((Matrix.of h).det)⁻¹ * h 0 0 := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.adjugate_fin_two]
  simp

theorem alpha_ne_zero (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    (h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I ≠ 0 := by
  intro h0
  have hre := congrArg Complex.re h0
  have him := congrArg Complex.im h0
  simp at hre him
  rw [Matrix.det_fin_two] at hΔ
  simp [hre, him] at hΔ

theorem finiteRing_sq_sub_mul_sq_eq_of_card (k : ℕ) (hk : 3 ≤ k) (h : M22) (hΔ : 0 < (Matrix.of h).det) :
    w0 k h = (((Matrix.of h).det : ℝ) : ℂ) ^ (k - 1) *
      ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) ^ (-(2 * (k : ℤ) - 1)) *
      Complex.exp (2 * Real.pi * Complex.I *
        (((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I))) := by
  have hα := alpha_ne_zero h hΔ
  obtain ⟨i00, i01, i10, i11⟩ := inv_entries h
  have hdi : ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det = ((Matrix.of h).det)⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hreal := real_factor k (by omega) _ hΔ
  have hD : (((Matrix.of h).det : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hΔ.ne'
  have hsg : sg (Matrix.of h).det = 1 := by
    unfold sg
    exact if_neg (not_lt.mpr hΔ.le)
  have hdp : 0 < ((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [hdi]
    exact inv_pos.mpr hΔ
  have hab : |(Matrix.of h).det| = (Matrix.of h).det := abs_of_pos hΔ
  have e1 : ((((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℝ) : ℂ) -
      ((((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℝ) : ℂ) * Complex.I =
      ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) / (((Matrix.of h).det : ℝ) : ℂ) := by
    rw [i11, i10]
    push_cast
    field_simp
    ring
  have e2 : ((((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℝ) : ℂ) -
      ((((Matrix.of h)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℝ) : ℂ) * Complex.I =
      -((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / (((Matrix.of h).det : ℝ) : ℂ) := by
    rw [i01, i00]
    push_cast
    field_simp
    ring
  have hz : (((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) / (((Matrix.of h).det : ℝ) : ℂ)) ^
      (-(2 * (k : ℤ) - 1)) = ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) ^ (-(2 * (k : ℤ) - 1)) *
        (((Matrix.of h).det : ℝ) : ℂ) ^ (2 * (k : ℤ) - 1) := by
    rw [div_zpow, zpow_neg (((Matrix.of h).det : ℝ) : ℂ), div_inv_eq_mul]
  have hq : -2 * (Real.pi : ℂ) * Complex.I *
      ((-((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / (((Matrix.of h).det : ℝ) : ℂ)) /
        (((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) / (((Matrix.of h).det : ℝ) : ℂ))) =
      2 * Real.pi * Complex.I *
        (((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I)) := by
    field_simp
  have hc : (((((Matrix.of h).det)⁻¹ ^ ((2 * (k : ℝ) - 1) / 2) : ℝ)) : ℂ) *
      (((Matrix.of h).det ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) *
      (((Matrix.of h).det : ℝ) : ℂ) ^ (2 * (k : ℤ) - 1) =
      (((Matrix.of h).det : ℝ) : ℂ) ^ (k - 1) := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hreal
    simpa using this
  unfold w0 Wm
  rw [if_pos hdp, hsg, hab, hdi, e1, e2, hz, hq]
  linear_combination (((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) ^ (-(2 * (k : ℤ) - 1)) *
    Complex.exp (2 * Real.pi * Complex.I *
      (((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I)))) * hc

end GlobalTheory.CompanionTheory.WeightClosed

theorem GlobalTheory.CompanionTheory.WeightClosed.main : ∀ (k : ℕ), 3 ≤ k → ∀ h : Ad3.LR.M22, 0 < (Matrix.of h).det → Ad3.LR.w0 k h = (((Matrix.of h).det : ℝ) : ℂ) ^ (k - 1) * ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I) ^ (-(2 * (k : ℤ) - 1)) * Complex.exp (2 * Real.pi * Complex.I * (((h 0 1 : ℂ) + (h 1 1 : ℂ) * Complex.I) / ((h 0 0 : ℂ) + (h 1 0 : ℂ) * Complex.I))) :=
  GlobalTheory.CompanionTheory.WeightClosed.finiteRing_sq_sub_mul_sq_eq_of_card
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerIwasawaGrowthBound
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal

namespace GlobalTheory.CompanionTheory.WhittakerIwasawa

theorem diagonal_mul_unipotent {F : Type} [Field F] (t₁ t₂ : Fˣ) (x : F) :
    Ad3.dg2 t₁ t₂ * Ad3.uni2 x =
      Ad3.uni2 ((t₁ : F) * x * ((t₂⁻¹ : Fˣ) : F)) * Ad3.dg2 t₁ t₂ := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ad3.uni2, Ad3.dg2, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc]

theorem diagonal_mul_diagonal_alt {F : Type} [Field F] (t₁ t₂ b₁ b₂ : Fˣ) :
    Ad3.dg2 t₁ t₂ * Ad3.dg2 b₁ b₂ =
      Ad3.dg2 (t₂ * b₂) (t₂ * b₂) * Ad3.dg2 (t₁ * b₁ * (t₂ * b₂)⁻¹) 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ad3.dg2, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem whittaker_bound_iwasawa :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ψ : AddChar F Circle) (W' : GL (Fin 2) F → ℂ) (C : ℝ), (∀ x g, W' (Ad3.uni2 x * g) = (ψ x : ℂ) * W' g) → (∀ (a : Fˣ) g, W' (Ad3.dg2 a a * g) = W' g) → (∀ (a : Fˣ), ∀ κ ∈ GLnLocal.integralGL F 2, ‖W' (Ad3.dg2 a 1 * κ)‖ ≤ C * (modulus (a : F) : ℝ) ^ (1 / 4 : ℝ)) → ∀ (t₁ t₂ b₁ b₂ : Fˣ) (x : F), ∀ κ ∈ GLnLocal.integralGL F 2, ‖W' (Ad3.dg2 t₁ t₂ * (Ad3.uni2 x * Ad3.dg2 b₁ b₂ * κ))‖ ≤ C * (modulus ((t₁ * b₁ * (t₂ * b₂)⁻¹ : Fˣ) : F) : ℝ) ^ (1 / 4 : ℝ) := by
  intro F _ _ _ _ ψ W' C hu hd hb t₁ t₂ b₁ b₂ x κ hκ
  have e : Ad3.dg2 t₁ t₂ * (Ad3.uni2 x * Ad3.dg2 b₁ b₂ * κ) =
      Ad3.uni2 ((t₁ : F) * x * ((t₂⁻¹ : Fˣ) : F)) * (Ad3.dg2 (t₂ * b₂) (t₂ * b₂) *
        (Ad3.dg2 (t₁ * b₁ * (t₂ * b₂)⁻¹) 1 * κ)) := by
    rw [← mul_assoc (Ad3.dg2 (t₂ * b₂) (t₂ * b₂)), ← diagonal_mul_diagonal_alt, ← mul_assoc, ← mul_assoc,
      ← mul_assoc, diagonal_mul_unipotent]
    simp only [mul_assoc]
  rw [e, hu, hd, norm_mul, Circle.norm_coe, one_mul]
  exact hb _ κ hκ

end GlobalTheory.CompanionTheory.WhittakerIwasawa
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSmoothnessStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_smoothness : Ad3.SchwartzSpaceL2.SSmooth := by
  first | exact @GlobalTheory.CompanionTheory.WhittakerSmooth.sSmooth | exact GlobalTheory.CompanionTheory.WhittakerSmooth.sSmooth | (intros; apply GlobalTheory.CompanionTheory.WhittakerSmooth.sSmooth <;> assumption)
end

