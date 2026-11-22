import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0014
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0015
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.Bundle0002
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0001

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayInD
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct SchwartzMap ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.AwayPf

variable {D : D7} {n : ℕ}

open Classical in
theorem gen_sch (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hfr : IsUnit fr.det)
    (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) (hl : ∀ τ', l τ' ≠ 0)
    (p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ) (hp : ∀ v ∈ p.vars, v.1 ≠ τ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E))
    (f : (Fin V.rank → Fin n → ℂ) → ℂ) (hf : IsSch f) :
    tens θ τ fr f (fun x => evalPoly p (fun τ => compAt θ τ x) * gAway V l s τ (fun τ => compAt θ τ x) *
      g (fun i j => finPart D (x i j))) ∈ schwartzA θ V.rank n := by
  obtain ⟨S, hS⟩ := hf
  set A : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun t => gramAt D V t * s t with hAdef
  have hA : ∀ t, t ≠ τ → (A t).PosDef := fun t _ => (hs t).2.2
  have hw : ∀ t, t ≠ τ → 0 < |l t| := fun t _ => abs_pos.mpr (hl t)
  obtain ⟨G, hG⟩ := exists_gauss (n := n) τ A hA (fun t => |l t|) hw
  set poly : Bsp τ V.rank n → ℂ := fun b => MvPolynomial.eval (fun k => vC τ k b) p with hpoly
  have hpolyT : poly.HasTemperateGrowth := tg_poly τ p
  set h : 𝓢(Bsp τ V.rank n, ℂ) := SchwartzMap.smulLeftCLM ℂ poly G with hh
  have hhv : ∀ b, h b = poly b * G b := fun b => by
    rw [hh, SchwartzMap.smulLeftCLM_apply_apply hpolyT, smul_eq_mul]
  obtain ⟨Fp, hFp⟩ := GlobalTheory.SchwartzHadamard.exists_schwartz_prod S h
  let e := (eL (n := n) τ fr hfr).toContinuousLinearEquiv
  let Fz : 𝓢(D.what₂.Tau → Fin V.rank → Fin n → ℂ, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e Fp
  have hFz : ∀ z, Fz z = S (Matrix.of.symm (fr⁻¹ * Matrix.of (z τ))) * (poly (fun t => z t.1) * G (fun t => z t.1)) := by
    intro z
    simp only [Fz, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hFp, hhv]
    rfl
  have hpolyz : ∀ z : D.what₂.Tau → Fin V.rank → Fin n → ℂ,
      poly (fun t => z t.1) = evalPoly p (fun t => Matrix.of (z t)) := by
    intro z
    rw [evalPoly_congr p τ hp (fun t => Matrix.of (z t)) (extF τ (fun t => z t.1)) (fun t ht => by simp only [extF, dif_neg ht]; rfl)]
    rfl
  have hGz : ∀ z : D.what₂.Tau → Fin V.rank → Fin n → ℂ,
      G (fun t => z t.1) = gAway V l s τ (fun t => Matrix.of (z t)) := by
    intro z
    rw [hG]
    unfold gAway qf
    congr 1
    rw [Finset.sum_subtype _ (p := fun τ' => τ' ≠ τ) (fun x => by simp)]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [← tr_im_zero (hA t.1 t.2).isHermitian (Matrix.of (z t.1))]
    simp only [hAdef]
    ring
  have key : ∀ z : D.what₂.Tau → Fin V.rank → Fin n → ℂ, Fz z = f (Matrix.of.symm (fr⁻¹ * Matrix.of (z τ))) *
      (evalPoly p (fun t => Matrix.of (z t)) * gAway V l s τ (fun t => Matrix.of (z t))) := by
    intro z
    rw [hFz, hpolyz, hGz, hS]
  refine Submodule.subset_span ⟨Fz, g, hg, ?_⟩
  funext x
  rw [key]
  simp only [tens, mul_assoc]
  rfl

end PositivityTheory.Rg.Sw.Glob.AwayPf
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DBoundA
section
noncomputable section

open Matrix Topology Filter
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob

namespace DBoundAH

variable {n : ℕ}

def rowC {m : ℕ} (u : Fin m → Fin n → ℂ) (a : Fin m) : Fin n → ℂ := fun j => star (u a j)

theorem trace_gramB {m : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    (Z * gramB ε b u).trace = ∑ a ∈ Finset.univ.filter (fun a => ε a = b),
      star (rowC u a) ⬝ᵥ (Z *ᵥ rowC u a) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramB, evX, Qb, map_sum, map_mul, MvPolynomial.eval_X,
    dotProduct, Matrix.mulVec, rowC, Pi.star_apply, star_star, Finset.mul_sum, Finset.sum_mul]
  simp only [Bool.true_eq_false, if_true, if_false]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun a _ => ?_))
  simp only [Bool.false_eq_true, if_false]
  ring

theorem star_dot_conjTranspose (Z : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) :
    star w ⬝ᵥ (Zᴴ *ᵥ w) = star (star w ⬝ᵥ (Z *ᵥ w)) := by
  simp only [dotProduct, mulVec, conjTranspose_apply, Pi.star_apply, star_sum, star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem im_eq_re (Z : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) :
    (star w ⬝ᵥ (Z *ᵥ w)).im = (star w ⬝ᵥ (((-(Complex.I / 2)) • (Z - Zᴴ)) *ᵥ w)).re := by
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec, dotProduct_smul, dotProduct_sub, star_dot_conjTranspose]
  simp only [smul_eq_mul, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

private theorem norm_star_dotProduct_mulVec_le_sum_norm_mul (M : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) :
    ‖star w ⬝ᵥ (M *ᵥ w)‖ ≤ (∑ i, ∑ j, ‖M i j‖) * ∑ j, ‖w j‖ ^ 2 := by
  have hS : ∀ i j, ‖w i‖ * ‖w j‖ ≤ ∑ k, ‖w k‖ ^ 2 := by
    intro i j
    have hi : ‖w i‖ ^ 2 ≤ ∑ k, ‖w k‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖w k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ i)
    have hj : ‖w j‖ ^ 2 ≤ ∑ k, ‖w k‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖w k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)
    nlinarith [sq_nonneg (‖w i‖ - ‖w j‖), norm_nonneg (w i), norm_nonneg (w j)]
  calc ‖star w ⬝ᵥ (M *ᵥ w)‖ = ‖∑ i, ∑ j, star (w i) * (M i j * w j)‖ := by
        simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, ‖star (w i) * (M i j * w j)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ = ∑ i, ∑ j, ‖M i j‖ * (‖w i‖ * ‖w j‖) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          rw [norm_mul, norm_mul, norm_star]
          ring
    _ ≤ ∑ i, ∑ j, ‖M i j‖ * ∑ k, ‖w k‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hS i j) (norm_nonneg _)
    _ = (∑ i, ∑ j, ‖M i j‖) * ∑ k, ‖w k‖ ^ 2 := by simp [Finset.sum_mul]

private theorem exists_pos_mul_sum_sq_le_re_of_posDef (H0 : Matrix (Fin n) (Fin n) ℂ) (h0 : H0.PosDef) :
    ∃ c > 0, ∀ w : Fin n → ℂ, c * ∑ j, ‖w j‖ ^ 2 ≤ (star w ⬝ᵥ (H0 *ᵥ w)).re := by
  classical
  have hA := h0.1
  have hspec : H0 = (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  obtain ⟨c, hc, hcle⟩ : ∃ c > 0, ∀ i, c ≤ hA.eigenvalues i := by
    rcases isEmpty_or_nonempty (Fin n) with hn | hn
    · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
    · obtain ⟨i0, _, hi0⟩ := Finset.exists_min_image Finset.univ hA.eigenvalues Finset.univ_nonempty
      exact ⟨hA.eigenvalues i0, h0.eigenvalues_pos i0, fun i => hi0 i (Finset.mem_univ i)⟩
  refine ⟨c, hc, fun w => ?_⟩
  have hsv : star w ᵥ* (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) =
      star (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) := by
    rw [Matrix.star_mulVec, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have h1 : star w ⬝ᵥ (H0 *ᵥ w) = ∑ i, ((hA.eigenvalues i : ℝ) : ℂ) *
      (star ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) i) *
        ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) i)) := by
    conv_lhs => rw [hspec]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hsv]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have h2 : star (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) ⬝ᵥ
      (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) = star w ⬝ᵥ w := by
    rw [← hsv, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Unitary.mul_star_self_of_mem (hA.eigenvectorUnitary).2, Matrix.one_mulVec]
  have hre : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := by
    intro z
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  have h2' : ∑ i, ‖(star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ w) i‖ ^ 2 = ∑ j, ‖w j‖ ^ 2 := by
    have := congrArg Complex.re h2
    simp only [dotProduct, Pi.star_apply, Complex.re_sum, hre] at this
    exact this
  rw [h1, Complex.re_sum, ← h2', Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Complex.re_ofReal_mul, hre]
  exact mul_le_mul_of_nonneg_right (hcle i) (by positivity)

theorem posDef_unif {P : Type} [TopologicalSpace P] {p₀ : P} (H : P → Matrix (Fin n) (Fin n) ℂ)
    (hH : ∀ i j, ContinuousAt (fun p => H p i j) p₀) (h0 : (H p₀).PosDef) :
    ∃ δ > 0, ∀ᶠ p in 𝓝 p₀, ∀ w : Fin n → ℂ, δ * ∑ j, ‖w j‖ ^ 2 ≤ (star w ⬝ᵥ (H p *ᵥ w)).re := by
  obtain ⟨c, hc, hcoer⟩ := exists_pos_mul_sum_sq_le_re_of_posDef (H p₀) h0
  have hf : Tendsto (fun p => ∑ i, ∑ j, ‖H p i j - H p₀ i j‖) (𝓝 p₀) (𝓝 0) := by
    have h00 : (0 : ℝ) = ∑ i : Fin n, ∑ j : Fin n, ‖H p₀ i j - H p₀ i j‖ := by simp
    rw [h00]
    exact tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ =>
      ((hH i j).tendsto.sub tendsto_const_nhds).norm
  have hev := (tendsto_order.1 hf).2 (c / 2) (by positivity)
  refine ⟨c / 2, by positivity, hev.mono fun p hp w => ?_⟩
  have hb := norm_star_dotProduct_mulVec_le_sum_norm_mul (H p - H p₀) w
  have hsplit : (star w ⬝ᵥ (H p *ᵥ w)).re =
      (star w ⬝ᵥ (H p₀ *ᵥ w)).re + (star w ⬝ᵥ ((H p - H p₀) *ᵥ w)).re := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
    simp
  have hlow : -‖star w ⬝ᵥ ((H p - H p₀) *ᵥ w)‖ ≤ (star w ⬝ᵥ ((H p - H p₀) *ᵥ w)).re :=
    (abs_le.mp (Complex.abs_re_le_norm _)).1
  have hS : 0 ≤ ∑ j, ‖w j‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  have hcw := hcoer w
  have hp' : ∑ i, ∑ j, ‖(H p - H p₀) i j‖ < c / 2 := by simpa [Matrix.sub_apply] using hp
  have hK := mul_le_mul_of_nonneg_right hp'.le hS
  linarith

end DBoundAH

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcD
section
noncomputable section

open MeasureTheory Filter Topology MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcDH

open DCalcH DCalcBH

variable {m n : ℕ}

def sqN (v : Fin m → Fin n → ℂ) : ℝ := ∑ a, ∑ j, ‖v a j‖ ^ 2

theorem sqN_nonneg (v : Fin m → Fin n → ℂ) : 0 ≤ sqN v := by
  unfold sqN; positivity

theorem norm_le_one_add_sq (v : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) : ‖v a j‖ ≤ 1 + sqN v := by
  have h1 : ‖v a j‖ ^ 2 ≤ sqN v := by
    unfold sqN
    have ha : ‖v a j‖ ^ 2 ≤ ∑ j', ‖v a j'‖ ^ 2 :=
      Finset.single_le_sum (f := fun j' => ‖v a j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    exact ha.trans (Finset.single_le_sum (f := fun a' => ∑ j', ‖v a' j'‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ a))
  nlinarith [norm_nonneg (v a j), sq_nonneg (‖v a j‖ - 1)]

theorem norm_crd (v : Fin m → Fin n → ℂ) (k : Fin m × Fin n × Bool) : ‖crd v k‖ = ‖v k.1 k.2.1‖ := by
  unfold crd; split_ifs <;> simp

theorem evX_growth (Q : PX m n) : ∃ C N, 0 ≤ C ∧ ∀ v, ‖evX Q v‖ ≤ C * (1 + sqN v) ^ N := by
  induction Q using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, 0, norm_nonneg _, fun v => by simp [evX_eq]⟩
  | add p q hp hq =>
    obtain ⟨C1, N1, hC1, h1⟩ := hp
    obtain ⟨C2, N2, hC2, h2⟩ := hq
    refine ⟨C1 + C2, max N1 N2, by positivity, fun v => ?_⟩
    have hs : 1 ≤ 1 + sqN v := by linarith [sqN_nonneg v]
    have e1 := pow_le_pow_right₀ hs (le_max_left N1 N2)
    have e2 := pow_le_pow_right₀ hs (le_max_right N1 N2)
    calc ‖evX (p + q) v‖ ≤ ‖evX p v‖ + ‖evX q v‖ := by rw [evX_eq, map_add]; exact norm_add_le _ _
      _ ≤ C1 * (1 + sqN v) ^ N1 + C2 * (1 + sqN v) ^ N2 := add_le_add (h1 v) (h2 v)
      _ ≤ C1 * (1 + sqN v) ^ max N1 N2 + C2 * (1 + sqN v) ^ max N1 N2 :=
          add_le_add (mul_le_mul_of_nonneg_left e1 hC1) (mul_le_mul_of_nonneg_left e2 hC2)
      _ = (C1 + C2) * (1 + sqN v) ^ max N1 N2 := by ring
  | mul_X p k hp =>
    obtain ⟨C, N, hC, h⟩ := hp
    refine ⟨C, N + 1, hC, fun v => ?_⟩
    have hk : ‖crd v k‖ ≤ 1 + sqN v := by rw [norm_crd]; exact norm_le_one_add_sq v _ _
    calc ‖evX (p * X k) v‖ = ‖evX p v‖ * ‖crd v k‖ := by rw [evX_eq, map_mul, eval_X, norm_mul]; rfl
      _ ≤ C * (1 + sqN v) ^ N * (1 + sqN v) :=
          mul_le_mul (h v) hk (norm_nonneg _) (mul_nonneg hC (pow_nonneg (by linarith [sqN_nonneg v]) _))
      _ = C * (1 + sqN v) ^ (N + 1) := by ring

theorem poly_exp (N : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ C, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → (1 + x) ^ N * Real.exp (-(a * x)) ≤ C * Real.exp (-(a / 2 * x)) :=
  _root_.UpperTheory.Reformulated.B.P6.r23b.PositivityTheory.Rg.Sw.Glob.DCalcDH.poly_exp N a ha

theorem integrable_gauss_C (a : ℝ) (ha : 0 < a) : Integrable (fun z : ℂ => Real.exp (-(a * ‖z‖ ^ 2))) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (a : ℂ)) (by simpa using ha) 0 0
  refine h.norm.congr (Eventually.of_forall fun z => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, ← Complex.ofReal_pow]

theorem integrable_gauss (a : ℝ) (ha : 0 < a) : Integrable (fun u : Fin m → Fin n → ℂ => Real.exp (-(a * sqN u))) := by
  have hinner : Integrable (fun w : Fin n → ℂ => ∏ j, Real.exp (-(a * ‖w j‖ ^ 2))) :=
    Integrable.fintype_prod (ι := Fin n) (E := ℂ) (μ := fun _ => (volume : Measure ℂ))
      (f := fun _ z => Real.exp (-(a * ‖z‖ ^ 2))) fun _ => integrable_gauss_C a ha
  have houter : Integrable (fun u : Fin m → Fin n → ℂ => ∏ i, ∏ j, Real.exp (-(a * ‖u i j‖ ^ 2))) :=
    Integrable.fintype_prod (ι := Fin m) (E := Fin n → ℂ) (μ := fun _ => (volume : Measure (Fin n → ℂ)))
      (f := fun _ w => ∏ j, Real.exp (-(a * ‖w j‖ ^ 2))) fun _ => hinner
  refine houter.congr (Eventually.of_forall fun u => ?_)
  simp only [sqN]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]

end DCalcDH

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DRCosSubSin
section
noncomputable section

open Matrix Complex

namespace PositivityTheory.Rg.Sw.Glob.VacG

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacD PositivityTheory.Rg.Sw.Glob.VacU

variable {n : ℕ}

theorem inK_blocks (k : M2 n) (hk : InK k) :
    k.toBlocks₂₁ = -k.toBlocks₁₂ ∧ k.toBlocks₂₂ = k.toBlocks₁₁ := by
  unfold InK InG at hk
  obtain ⟨hG, hU⟩ := hk
  have hU' : k * kᴴ = 1 := mul_eq_one_comm.mp hU
  have hc : JJ n * k = k * JJ n := by
    calc JJ n * k = (k * kᴴ) * JJ n * k := by rw [hU', Matrix.one_mul]
      _ = k * (kᴴ * JJ n * k) := by simp only [Matrix.mul_assoc]
      _ = k * JJ n := by rw [hG]
  rw [← fromBlocks_toBlocks k] at hc
  unfold JJ at hc
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at hc
  simp at hc
  exact ⟨hc.1, hc.2.1⟩

theorem mM_unitary (u : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) : mM u = fromBlocks u 0 0 u := by
  rw [mM, Matrix.inv_eq_right_inv hu]

theorem dR_cos_add_sin (θ : Fin n → ℝ) :
    (dR fun j => Real.cos (θ j)) + I • (dR fun j => Real.sin (θ j)) = diagonal fun j => cexp (I * (θ j : ℂ)) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [dR, Matrix.diagonal_apply_eq, Complex.ofReal_cos, Complex.ofReal_sin, mul_comm I, Complex.exp_mul_I]
  · simp [dR, Matrix.diagonal_apply_ne _ h]

theorem dR_cos_sub_sin (θ : Fin n → ℝ) :
    (dR fun j => Real.cos (θ j)) - I • (dR fun j => Real.sin (θ j)) = diagonal fun j => cexp (-(I * (θ j : ℂ))) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [dR, Matrix.diagonal_apply_eq, Complex.ofReal_cos, Complex.ofReal_sin, ← neg_mul, mul_comm I,
      Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  · simp [dR, Matrix.diagonal_apply_ne _ h]

theorem uni_I (A B : Matrix (Fin n) (Fin n) ℂ) (e11 : Aᴴ * A + Bᴴ * B = 1) (e12 : Aᴴ * B + -(Bᴴ * A) = 0) :
    (A + I • B)ᴴ * (A + I • B) = 1 := by
  have hs : star (I : ℂ) = -I := by rw [Complex.star_def, Complex.conj_I]
  simp only [conjTranspose_add, conjTranspose_smul, hs, add_mul, mul_add, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  rw [← e11, ← sub_eq_zero]
  have hI : I * (-I) = (1 : ℂ) := by rw [mul_neg, Complex.I_mul_I, neg_neg]
  have h2 : Aᴴ * B = Bᴴ * A := by rw [← sub_eq_zero, sub_eq_add_neg]; exact e12
  rw [hI, one_smul, h2, neg_smul]
  abel

theorem uni_mI (A B : Matrix (Fin n) (Fin n) ℂ) (e11 : Aᴴ * A + Bᴴ * B = 1) (e12 : Aᴴ * B + -(Bᴴ * A) = 0) :
    (A - I • B)ᴴ * (A - I • B) = 1 := by
  have hs : star (I : ℂ) = -I := by rw [Complex.star_def, Complex.conj_I]
  simp only [conjTranspose_sub, conjTranspose_smul, hs, sub_mul, mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]
  rw [← e11, ← sub_eq_zero]
  have hI : I * (-I) = (1 : ℂ) := by rw [mul_neg, Complex.I_mul_I, neg_neg]
  have h2 : Aᴴ * B = Bᴴ * A := by rw [← sub_eq_zero, sub_eq_add_neg]; exact e12
  rw [hI, one_smul, h2, neg_smul]
  abel

theorem kak (k : M2 n) (hk : InK k) :
    ∃ (u u' : Matrix (Fin n) (Fin n) ℂ) (θ : Fin n → ℝ), uᴴ * u = 1 ∧ u'ᴴ * u' = 1 ∧
      (∀ j, -(Real.pi / 2) < θ j ∧ θ j ≤ Real.pi / 2) ∧ k = mM u * kth θ * mM u' := by
  obtain ⟨h21, h22⟩ := inK_blocks k hk
  have hU : kᴴ * k = 1 := hk.2
  set A := k.toBlocks₁₁ with hA0
  set B := k.toBlocks₁₂ with hB0
  have hkA : k = fromBlocks A B (-B) A := by
    conv_lhs => rw [← fromBlocks_toBlocks k]
    rw [h21, h22]
  have hE : Aᴴ * A + Bᴴ * B = 1 ∧ Aᴴ * B + -(Bᴴ * A) = 0 := by
    rw [hkA, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hU
    obtain ⟨h1, h2, -, -⟩ := hU
    refine ⟨?_, ?_⟩
    · simpa [conjTranspose_neg] using h1
    · simpa [conjTranspose_neg] using h2
  set W := A + I • B with hW0
  set V := A - I • B with hV0
  have hW : Wᴴ * W = 1 := uni_I A B hE.1 hE.2
  have hV : Vᴴ * V = 1 := uni_mI A B hE.1 hE.2
  have hV' : V * Vᴴ = 1 := mul_eq_one_comm.mp hV
  have hX : (W * Vᴴ)ᴴ * (W * Vᴴ) = 1 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ, hW,
      Matrix.one_mul, hV']
  obtain ⟨P, w, hP, hP', hw, hXd⟩ := VacU.unitary_diag (W * Vᴴ) hX
  set θ : Fin n → ℝ := fun j => Complex.arg (w j) / 2 with hθ
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => cexp (I * (θ j : ℂ)) with hD
  set Db : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => cexp (-(I * (θ j : ℂ))) with hDb
  have hDDb : D * Db = 1 := by
    rw [hD, hDb, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext j
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hDbH : Dbᴴ = D := by
    rw [hD, hDb, diagonal_conjTranspose]
    congr 1; funext j
    simp only [Pi.star_apply]
    rw [Complex.star_def, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal,
      neg_mul, neg_neg]
  have hDb2 : Db * Db = (diagonal w)ᴴ := by
    rw [hDb, diagonal_mul_diagonal, diagonal_conjTranspose]
    congr 1; funext j
    simp only [Pi.star_apply]
    have hwj : w j = cexp (↑(Complex.arg (w j)) * I) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (w j)]
      rw [hw j, Complex.ofReal_one, one_mul]
    rw [← Complex.exp_add]
    conv_rhs => rw [hwj]
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
    congr 1
    simp only [hθ]
    push_cast
    ring
  set u' := Db * Pᴴ * W with hu0
  have hu' : u'ᴴ * u' = 1 := by
    rw [hu0, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hDbH]
    calc Wᴴ * (P * D) * (Db * Pᴴ * W) = Wᴴ * (P * (D * Db) * Pᴴ) * W := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hDDb, Matrix.mul_one, hP', Matrix.mul_one, hW]
  have hPD : P * D * u' = W := by
    calc P * D * u' = P * (D * Db) * Pᴴ * W := by simp only [hu0, Matrix.mul_assoc]
      _ = W := by rw [hDDb, Matrix.mul_one, hP', Matrix.one_mul]
  have hPDb : P * Db * u' = V := by
    calc P * Db * u' = (P * (Db * Db) * Pᴴ) * W := by simp only [hu0, Matrix.mul_assoc]
      _ = (W * Vᴴ)ᴴ * W := by
          rw [hDb2, hXd, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
            Matrix.mul_assoc]
          simp only [Matrix.mul_assoc]
      _ = V := by
          rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, hW, Matrix.mul_one]
  have hCS := dR_cos_add_sin θ
  have hCSm := dR_cos_sub_sin θ
  rw [← hD] at hCS
  rw [← hDb] at hCSm
  set C := dR fun j => Real.cos (θ j) with hC0
  set S := dR fun j => Real.sin (θ j) with hS0
  have e1 : P * C * u' + I • (P * S * u') = W := by
    rw [← hPD, ← hCS, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have e2 : P * C * u' - I • (P * S * u') = V := by
    rw [← hPDb, ← hCSm, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hXA : P * C * u' = A := by
    have h := congrArg₂ (· + ·) e1 e2
    simp only [hW0, hV0] at h
    have h2 : (2 : ℂ) • (P * C * u') = (2 : ℂ) • A := by
      rw [two_smul, two_smul]
      convert h using 1 <;> abel
    exact smul_right_injective _ two_ne_zero h2
  have hYB : P * S * u' = B := by
    have h := congrArg₂ (· - ·) e1 e2
    simp only [hW0, hV0] at h
    have h2 : (2 * I) • (P * S * u') = (2 * I) • B := by
      rw [mul_smul, mul_smul, two_smul, two_smul]
      convert h using 1 <;> abel
    exact smul_right_injective _ (mul_ne_zero two_ne_zero Complex.I_ne_zero) h2
  refine ⟨P, u', θ, hP, hu', fun j => ⟨?_, ?_⟩, ?_⟩
  · have := Complex.neg_pi_lt_arg (w j)
    simp only [hθ]
    linarith
  · have := Complex.arg_le_pi (w j)
    simp only [hθ]
    linarith
  · refine hkA.trans ?_
    rw [mM_unitary P hP, mM_unitary u' hu', kth_eq, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul]
    rw [← hC0, ← hS0]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_zero, add_zero, hXA, hYB]

end PositivityTheory.Rg.Sw.Glob.VacG
end
end

