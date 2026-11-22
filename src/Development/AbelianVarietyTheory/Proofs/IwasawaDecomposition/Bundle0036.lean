import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedFlagsIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniMatBlockTriangular
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0035
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0032
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0033
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotInjOnOfFderivEqZero
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCellMap
section
set_option autoImplicit false

noncomputable section

open Module TopologicalSpace GlobalTheory.FlagPts

namespace GlobalTheory.FlagPts.CellCont

variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

def polyMat (i : ι) :
    Matrix (Fin (finrank k (V i))) (Fin (finrank k (V i))) (MvPolynomial (CellIdx k V) k) :=
  fun a c => if a = c then 1 else if h : c < a then MvPolynomial.X ⟨i, (a, c), h⟩ else 0

theorem map_polyMat (u : AffPts k (CellIdx k V)) (i : ι) :
    (polyMat (k := k) (V := V) i).map (MvPolynomial.eval u) = uniMat u i := by
  ext a c
  simp only [Matrix.map_apply, polyMat, uniMat]
  split_ifs
  · exact map_one _
  · exact MvPolynomial.eval_X (f := u) _
  · exact map_zero _

theorem eval_adjugate_polyMat (u : AffPts k (CellIdx k V)) (i : ι) (a c : Fin (finrank k (V i))) :
    MvPolynomial.eval u ((polyMat (k := k) (V := V) i).adjugate a c) = (uniMat u i).adjugate a c := by
  have := RingHom.map_adjugate (MvPolynomial.eval u) (polyMat (k := k) (V := V) i)
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, map_polyMat] at this
  exact congrFun (congrFun this a) c

def polyOnCell (b : Frames k V) : Subalgebra k (Frames k V → k) where
  carrier := {f | ∃ P : MvPolynomial (CellIdx k V) k, ∀ u, f (cellFrame b u) = MvPolynomial.eval u P}
  mul_mem' := by
    rintro f g ⟨P, hP⟩ ⟨Q, hQ⟩
    exact ⟨P * Q, fun u => by simp [hP, hQ]⟩
  add_mem' := by
    rintro f g ⟨P, hP⟩ ⟨Q, hQ⟩
    exact ⟨P + Q, fun u => by simp [hP, hQ]⟩
  algebraMap_mem' := fun c => ⟨MvPolynomial.C c, fun u => (MvPolynomial.eval_C (f := u) c).symm⟩

theorem dual_mem_polyOnCell (b : Frames k V) (i : ι) (φ : Dual k (V i)) (a : Fin (finrank k (V i))) :
    (fun b' : Frames k V => φ (b' i a)) ∈ polyOnCell b :=
  ⟨∑ l, MvPolynomial.C (φ (b i l)) * polyMat (k := k) (V := V) i l a, fun u => by
    simp only [cellFrame_apply, map_sum, map_smul, smul_eq_mul, map_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [MvPolynomial.eval_C (f := u), ← map_polyMat u i, Matrix.map_apply, mul_comm]⟩

theorem repr_cellFrame (b : Frames k V) (u : AffPts k (CellIdx k V)) (i : ι) (v : V i) :
    (cellFrame b u i).repr v = (uniMat u i).adjugate.mulVec ((b i).repr v) := by
  have hu : IsUnit (uniMat u i).det := by rw [det_uniMat]; exact isUnit_one
  have hM : (uniMat u i)⁻¹ = (uniMat u i).adjugate := by
    rw [Matrix.inv_def, det_uniMat]; simp
  rw [← hM]
  have he : (Matrix.toLinearEquiv (b i) (uniMat u i) hu).symm v =
      Matrix.toLin (b i) (b i) (uniMat u i)⁻¹ v := by
    rw [LinearEquiv.symm_apply_eq, Matrix.toLinearEquiv_apply, ← LinearMap.comp_apply, ← Matrix.toLin_mul,
      Matrix.mul_nonsing_inv _ hu, Matrix.toLin_one]
    rfl
  simp only [cellFrame, Basis.map_repr, LinearEquiv.trans_apply]
  rw [he, ← LinearMap.toMatrix_mulVec_repr (b i) (b i), LinearMap.toMatrix_toLin]

theorem repr_mem_polyOnCell (b : Frames k V) (i : ι) (v : V i) (a : Fin (finrank k (V i))) :
    (fun b' : Frames k V => (b' i).repr v a) ∈ polyOnCell b :=
  ⟨∑ c, (polyMat (k := k) (V := V) i).adjugate a c * MvPolynomial.C ((b i).repr v c), fun u => by
    show (cellFrame b u i).repr v a = _
    rw [repr_cellFrame]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [MvPolynomial.eval_C (f := u), eval_adjugate_polyMat]⟩

theorem regFns_le_polyOnCell (b : Frames k V) : regFns k V ≤ polyOnCell b := by
  refine Algebra.adjoin_le ?_
  rintro f (⟨i, φ, a, rfl⟩ | ⟨i, v, a, rfl⟩)
  · exact dual_mem_polyOnCell b i φ a
  · exact repr_mem_polyOnCell b i v a

theorem continuous_cellFrame (b : Frames k V) : Continuous (cellFrame b) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨P, hP⟩ := regFns_le_polyOnCell b hf
  have : cellFrame b ⁻¹' {b' | f b' ≠ 0} = {u | MvPolynomial.eval u P ≠ 0} := by
    refine Set.ext fun u => ?_
    show f (cellFrame b u) ≠ 0 ↔ _
    rw [hP]
    rfl
  rw [this]
  exact isOpen_affPts_ne_zero P

end GlobalTheory.FlagPts.CellCont

namespace GlobalTheory.FlagPts

theorem continuous_cellMap : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V), Continuous (cellMap b) := by
  intro k _ ι _ V _ _ _ b
  exact continuous_coinduced_rng.comp (CellCont.continuous_cellFrame b)

end GlobalTheory.FlagPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DedekindZetaFactorizationRay
section
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder

namespace GlobalTheory.Mem

def PosDirichlet (F : ℂ → ℂ) : Prop :=
  ∃ (ι : Type) (w : ι → ℝ) (N : ι → ℕ), (∀ i, 0 ≤ w i) ∧ (∀ i, N i ≠ 0) ∧
    ∀ s : ℂ, 1 < s.re → HasSum (fun i => (w i : ℂ) * (N i : ℂ) ^ (-s)) (F s)

namespace PosDirichlet

lemma congr {F G : ℂ → ℂ} (h : PosDirichlet F) (e : ∀ s : ℂ, 1 < s.re → F s = G s) :
    PosDirichlet G := by
  obtain ⟨ι, w, N, hw, hN, h⟩ := h
  exact ⟨ι, w, N, hw, hN, fun s hs => e s hs ▸ h s hs⟩

lemma const {c : ℝ} (hc : 0 ≤ c) : PosDirichlet (fun _ => (c : ℂ)) :=
  ⟨Unit, fun _ => c, fun _ => 1, fun _ => hc, fun _ => one_ne_zero, fun s _ => by
    simpa using hasSum_unique (fun _ : Unit => (c : ℂ))⟩

lemma hasSum_mul_of_norm_summable {ι κ : Type} {f : ι → ℂ} {g : κ → ℂ} {a b : ℂ} (hf : HasSum f a)
    (hg : HasSum g b) : HasSum (fun p : ι × κ => f p.1 * g p.2) (a * b) :=
  hf.mul hg (summable_mul_of_summable_norm hf.summable.norm hg.summable.norm)

lemma mul {F G : ℂ → ℂ} (hF : PosDirichlet F) (hG : PosDirichlet G) :
    PosDirichlet (fun s => F s * G s) := by
  obtain ⟨ι, w, N, hw, hN, h⟩ := hF
  obtain ⟨κ, w', N', hw', hN', h'⟩ := hG
  refine ⟨ι × κ, fun p => w p.1 * w' p.2, fun p => N p.1 * N' p.2,
    fun p => mul_nonneg (hw _) (hw' _), fun p => mul_ne_zero (hN _) (hN' _), fun s hs => ?_⟩
  have e : ∀ p : ι × κ, ((w p.1 * w' p.2 : ℝ) : ℂ) * ((N p.1 * N' p.2 : ℕ) : ℂ) ^ (-s) =
      ((w p.1 : ℂ) * (N p.1 : ℂ) ^ (-s)) * ((w' p.2 : ℂ) * (N' p.2 : ℂ) ^ (-s)) := by
    intro p
    push_cast
    rw [Complex.natCast_mul_natCast_cpow]
    ring
  have h1 := hasSum_mul_of_norm_summable (h s hs) (h' s hs)
  beta_reduce at h1 ⊢
  rw [funext e]
  exact h1

lemma pow {F : ℂ → ℂ} (hF : PosDirichlet F) (j : ℕ) : PosDirichlet (fun s => F s ^ j) := by
  induction j with
  | zero => simpa using const zero_le_one
  | succ j ih => simpa only [pow_succ] using ih.mul hF

lemma norm_term {w : ℝ} (hw : 0 ≤ w) {N : ℕ} (hN : N ≠ 0) (s : ℂ) :
    ‖(w : ℂ) * (N : ℂ) ^ (-s)‖ = ((w : ℂ) * (N : ℂ) ^ (-(s.re : ℂ))).re := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hN), Complex.norm_real,
    Real.norm_of_nonneg hw, ← Complex.ofReal_neg, ← Complex.ofReal_natCast,
    ← Complex.ofReal_cpow (Nat.cast_nonneg N), ← Complex.ofReal_mul, Complex.ofReal_re, neg_re]

lemma tsum {J : Type} {F : J → ℂ → ℂ} (hF : ∀ j, PosDirichlet (F j))
    (hs : ∀ s : ℂ, 1 < s.re → Summable (fun j => F j s)) :
    PosDirichlet (fun s => ∑' j, F j s) := by
  choose ι w N hw hN h using hF
  refine ⟨Σ j, ι j, fun p => w p.1 p.2, fun p => N p.1 p.2, fun p => hw _ _, fun p => hN _ _,
    fun s hs' => ?_⟩
  have hσ : 1 < ((s.re : ℝ) : ℂ).re := by simpa using hs'
  have key : ∀ j, HasSum (fun i => ‖(w j i : ℂ) * (N j i : ℂ) ^ (-s)‖) (F j s.re).re := by
    intro j
    simp only [norm_term (hw _ _) (hN _ _)]
    exact Complex.hasSum_re (h j _ hσ)
  have hsum : Summable (fun p : Σ j, ι j => (w p.1 p.2 : ℂ) * (N p.1 p.2 : ℂ) ^ (-s)) := by
    apply Summable.of_norm
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun j => (key j).summable, ?_⟩
    simp only [fun j => (key j).tsum_eq]
    exact (Complex.hasSum_re (hs _ hσ).hasSum).summable
  have h2 := hsum.hasSum.sigma (fun j => h j s hs')
  show HasSum _ (∑' j, F j s)
  rw [h2.tsum_eq]
  exact hsum.hasSum

lemma exists_LSeries {F : ℂ → ℂ} (hF : PosDirichlet F) :
    ∃ b : ℕ → ℂ, 0 ≤ b ∧ ∀ s : ℂ, 1 < s.re → LSeriesHasSum b s (F s) := by
  obtain ⟨ι, w, N, hw, hN, h⟩ := hF
  refine ⟨fun n => ∑' i : N ⁻¹' {n}, (w i : ℂ), fun n => tsum_nonneg fun i =>
    Complex.zero_le_real.2 (hw i.1), fun s hs => ?_⟩
  have h1 := (h s hs).tsum_fiberwise N
  unfold LSeriesHasSum
  suffices e : ∀ n, LSeries.term (fun n => ∑' i : N ⁻¹' {n}, (w i : ℂ)) s n =
      ∑' i : N ⁻¹' {n}, (w i : ℂ) * (N i : ℂ) ^ (-s) by
    rw [funext e]; exact h1
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · haveI : IsEmpty (N ⁻¹' {0}) := ⟨fun i => hN i i.2⟩
    simp
  · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, ← tsum_mul_right]
    refine tsum_congr fun i => ?_
    have : N i = n := i.2
    rw [this]

lemma exp_sub_one {F : ℂ → ℂ} (hF : PosDirichlet F) :
    PosDirichlet (fun s => Complex.exp (F s) - 1) := by
  have h1 : ∀ z : ℂ, HasSum (fun j : ℕ => z ^ (j + 1) / ((j + 1).factorial : ℂ))
      (Complex.exp z - 1) := by
    intro z
    have := NormedSpace.expSeries_div_hasSum_exp z
    rw [← Complex.exp_eq_exp_ℂ, ← hasSum_nat_add_iff' 1] at this
    simpa using this
  refine (tsum (F := fun (j : ℕ) s => F s ^ (j + 1) / ((j + 1).factorial : ℂ)) (fun j => ?_)
    (fun s _ => (h1 _).summable)).congr fun s _ => (h1 _).tsum_eq
  refine ((hF.pow (j + 1)).mul (const (c := ((j + 1).factorial : ℝ)⁻¹) (by positivity))).congr
    fun s _ => ?_
  push_cast
  rw [div_eq_mul_inv]

lemma exists_LSeries_exp {F : ℂ → ℂ} (hF : PosDirichlet F) :
    ∃ b : ℕ → ℂ, 0 ≤ b ∧ 0 < b 1 ∧ LSeries.abscissaOfAbsConv b ≤ 1 ∧
      ∀ s : ℂ, 1 < s.re → LSeries b s = Complex.exp (F s) := by
  obtain ⟨b, hb, h⟩ := hF.exp_sub_one.exists_LSeries
  have hδ : (0 : ℕ → ℂ) ≤ LSeries.delta := fun n => by
    by_cases hn : n = 1 <;> simp [LSeries.delta, hn]
  have h2 : ∀ s : ℂ, 1 < s.re → LSeriesHasSum (LSeries.delta + b) s (Complex.exp (F s)) := by
    intro s hs
    have h0 : LSeriesHasSum LSeries.delta s 1 := by
      unfold LSeriesHasSum
      have := hasSum_ite_eq (1 : ℕ) (1 : ℂ)
      convert this using 2 with n
      rw [LSeries.term_delta]
    simpa using h0.add (h s hs)
  refine ⟨LSeries.delta + b, add_nonneg hδ hb, ?_, ?_, fun s hs => (h2 s hs).LSeries_eq⟩
  · have : LSeries.delta 1 = 1 := by simp [LSeries.delta]
    rw [Pi.add_apply, this]
    exact add_pos_of_pos_of_nonneg one_pos (hb 1)
  · refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1) fun y hy => ?_
    exact (h2 y (by simpa using hy)).LSeriesSummable

end PosDirichlet

lemma sum_characters_nonneg {G : Type} [CommGroup G] [Fintype (G →* ℂˣ)] (g : G) :
    0 ≤ ∑ χ : G →* ℂˣ, (χ g : ℂ) := by
  by_cases h : ∀ χ : G →* ℂˣ, χ g = 1
  · exact Finset.sum_nonneg fun χ _ => by simp [h χ]
  · push_neg at h
    obtain ⟨ψ, hψ⟩ := h
    have h1 : ∑ χ : G →* ℂˣ, (χ g : ℂ) = (ψ g : ℂ) * ∑ χ : G →* ℂˣ, (χ g : ℂ) := by
      rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft ψ)]
      simp
    have h2 : (1 - (ψ g : ℂ)) * ∑ χ : G →* ℂˣ, (χ g : ℂ) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (Units.ext (sub_eq_zero.1 h3).symm) hψ
    · exact h3.ge

lemma norm_character {G : Type} [CommGroup G] [Fintype G] (χ : G →* ℂˣ) (g : G) :
    ‖(χ g : ℂ)‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card G) _ Fintype.card_ne_zero
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]

lemma natCast_pow_cpow_comm (q k : ℕ) (z : ℂ) : ((q : ℂ) ^ k) ^ z = ((q : ℂ) ^ z) ^ k := by
  rw [← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

lemma posDirichlet_local {G : Type} [CommGroup G] [Fintype G] [Fintype (G →* ℂˣ)] (g : G)
    {q : ℕ} (hq : 2 ≤ q) :
    PosDirichlet (fun s => ∑ χ : G →* ℂˣ, -Complex.log (1 - (χ g : ℂ) * (q : ℂ) ^ (-s))) := by
  refine ⟨ℕ, fun k => (∑ χ : G →* ℂˣ, (χ (g ^ k) : ℂ)).re / k, fun k => q ^ k,
    fun k => div_nonneg (Complex.nonneg_iff.1 (sum_characters_nonneg _)).1 (Nat.cast_nonneg _),
    fun k => pow_ne_zero _ (by omega), fun s hs => ?_⟩
  have h1 : ∀ χ : G →* ℂˣ, ‖(χ g : ℂ) * (q : ℂ) ^ (-s)‖ < 1 := by
    intro χ
    rw [norm_mul, norm_character, one_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · exact_mod_cast hq
    · simp only [neg_re]; linarith
  have h2 := hasSum_sum (s := Finset.univ)
    (fun χ _ => Complex.hasSum_taylorSeries_neg_log (h1 χ))
  convert h2 using 2 with k
  have h3 : (((∑ χ : G →* ℂˣ, (χ (g ^ k) : ℂ)).re : ℝ) : ℂ) = ∑ χ : G →* ℂˣ, (χ (g ^ k) : ℂ) :=
    (Complex.eq_re_of_ofReal_le (r := 0) (by simpa using sum_characters_nonneg (g ^ k))).symm
  rw [Complex.ofReal_div, h3, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [Nat.cast_pow, natCast_pow_cpow_comm, mul_pow, map_pow, Units.val_pow_eq_pow_val]
  push_cast
  ring

theorem ray_prod_LSeries_nonneg : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) [Fintype (D.G →* ℂˣ)], ∃ b : ℕ → ℂ, 0 ≤ b ∧ 0 < b 1 ∧ LSeries.abscissaOfAbsConv b ≤ 1 ∧ ∀ s : ℂ, 1 < s.re → LSeries b s = ∏ χ : D.G →* ℂˣ, LSeries (D.coef χ) s := by
  intro K _ _ M hM D _
  have hsum : ∀ (χ : D.G →* ℂˣ) (s : ℂ), 1 < s.re → Summable (fun v : D.Pr =>
      -Complex.log (1 - (χ (D.cls v.1.asIdeal) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))) := by
    intro χ s hs
    refine (Summable.clog_one_sub (Summable.of_norm ?_)).neg
    simpa only [norm_mul, norm_character, one_mul] using (GlobalTheory.T.ray_L_series_euler_product K M hM D χ s hs).2.1
  have hq : ∀ v : D.Pr, 2 ≤ Ideal.absNorm v.1.asIdeal := fun v =>
    NumberField.HeightOneSpectrum.one_lt_absNorm v.1
  obtain ⟨b, h0, h1, h2, h3⟩ := (PosDirichlet.tsum
    (fun v : D.Pr => posDirichlet_local (D.cls v.1.asIdeal) (hq v))
    (fun s hs => summable_sum fun χ _ => hsum χ s hs)).exists_LSeries_exp
  refine ⟨b, h0, h1, h2, fun s hs => ?_⟩
  rw [h3 s hs, Summable.tsum_finsetSum (fun χ _ => hsum χ s hs), Complex.exp_sum]
  exact Finset.prod_congr rfl fun χ _ => (GlobalTheory.T.ray_L_series_euler_product K M hM D χ s hs).2.2.symm

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableAtCoordinateCauchyIntegralStatement
section
open Metric Filter Topology Set
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableAt_coordinate_cauchy_integral : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ) (z₀ : Fin n → ℂ) (r : ℝ), 0 < r → z₀ k = 0 → IsOpen U → Metric.closedBall z₀ r ⊆ U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → DifferentiableAt ℂ (fun z => ∮ t in C(0, r), (t - z k)⁻¹ • f (Function.update z k t)) z₀ := by
  first | exact @GlobalTheory.cauchyCoord_differentiableAt | exact GlobalTheory.cauchyCoord_differentiableAt | (intros; apply GlobalTheory.cauchyCoord_differentiableAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscrMulMemOfIsIntegralStatement
section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_mul_integral_eq_tensor : ∀ (T U C : Type) [CommRing T] [IsDomain T] [IsIntegrallyClosed T] [CharZero T] [CommRing U] [IsDomain U] [IsIntegrallyClosed U] [Algebra T U] [Module.Flat T U] [CommRing C] [IsDomain C] [Algebra T C] [Module.Finite T C], Function.Injective (algebraMap T U) → Function.Injective (algebraMap T C) → ∃ d : T, d ≠ 0 ∧ ∀ c : FractionRing (U ⊗[T] C), IsIntegral (U ⊗[T] C) c → ∃ s : (U ⊗[T] C), algebraMap (U ⊗[T] C) (FractionRing (U ⊗[T] C)) s = algebraMap (U ⊗[T] C) (FractionRing (U ⊗[T] C)) (algebraMap T (U ⊗[T] C) d) * c := by
  first | exact @GlobalTheory.DiscConductor.discr_mul_mem_of_isIntegral | exact GlobalTheory.DiscConductor.discr_mul_mem_of_isIntegral | (intros; apply GlobalTheory.DiscConductor.discr_mul_mem_of_isIntegral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenspaceRankOneSpan
section
open scoped TensorProduct NumberField
open GlobalTheory.EigenSplit

namespace GlobalTheory.EigenSplit

theorem baseChangeAction_toModuleEnd_self_apply {O R : Type} [CommRing O] [CommRing R] (a : O)
    (t : R ⊗[ℤ] O) :
    baseChangeAction R (Module.toModuleEnd ℤ O : O →+* Module.End ℤ O) a t = t * (1 ⊗ₜ a) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r b => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
  | add s t hs ht => simp only [map_add, hs, ht, add_mul]

theorem eigenSub_eq_range_tensorAction_of_le_span {O R Λ : Type} [CommRing O] [CommRing R]
    [AddCommGroup Λ] [Module O Λ] [Module.Finite O Λ] [Module.Projective O Λ] (χ : O →+* R)
    (e : R ⊗[ℤ] O)
    (he : e ∈ eigenSub (baseChangeAction R (Module.toModuleEnd ℤ O : O →+* Module.End ℤ O)) χ)
    (hspan : eigenSub (baseChangeAction R (Module.toModuleEnd ℤ O : O →+* Module.End ℤ O)) χ
      ≤ Submodule.span R {e}) :
    eigenSub (baseChangeAction R (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ)) χ
      = LinearMap.range
          (tensorAction (baseChangeAction R (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ)) e) := by
  set ρO := (Module.toModuleEnd ℤ O : O →+* Module.End ℤ O)
  set ρ := (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ)
  have hact : ∀ a, baseChangeAction R ρ a = tensorAction (baseChangeAction R ρ) (1 ⊗ₜ a) := by
    intro a; ext y; simp
  apply le_antisymm
  · intro x hx
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' O Λ
    obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
    let F : Fin n → R ⊗[ℤ] Λ →ₗ[R] R ⊗[ℤ] O := fun k =>
      (((LinearMap.proj k : (Fin n → O) →ₗ[O] O) ∘ₗ s).restrictScalars ℤ).baseChange R
    let lam : Fin n → Λ := fun k => π (Pi.single k 1)
    have hsum : ∀ l, ∑ k, s l k • lam k = l := by
      intro l
      have h1 := LinearMap.congr_fun hs l
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
      conv_rhs => rw [← h1]
      rw [← Finset.univ_sum_single (s l), map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [lam, ← map_smul]
      congr 1
      ext j
      by_cases hj : j = k <;> simp [Pi.single_apply, hj]
    have hid : ∀ y, y = ∑ k, tensorAction (baseChangeAction R ρ) (F k y) (1 ⊗ₜ lam k) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r l =>
        simp only [F, LinearMap.baseChange_tmul, tensorAction_tmul, baseChangeAction_apply,
          LinearMap.restrictScalars_apply, LinearMap.comp_apply, LinearMap.proj_apply]
        simp [ρ, ← TensorProduct.tmul_sum, hsum, TensorProduct.smul_tmul']
      | add y z hy hz =>
        conv_lhs => rw [hy, hz]
        simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib]
    have hF : ∀ k, IsEquivariant (baseChangeAction R ρ) (baseChangeAction R ρO) (F k) := by
      intro k a y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r l => simp [F, ρ, ρO]
      | add y z hy hz => simp only [map_add, hy, hz]
    have hc : ∀ k, ∃ c : R, c • e = F k x := fun k =>
      Submodule.mem_span_singleton.1 (hspan ((hF k).map_mem hx))
    choose c hc using hc
    refine ⟨∑ k, c k • (1 ⊗ₜ lam k), ?_⟩
    rw [map_sum]
    conv_rhs => rw [hid x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hc k, map_smul, map_smul, LinearMap.smul_apply]
  · rintro _ ⟨m, rfl⟩
    refine mem_eigenSub.2 fun a => ?_
    rw [hact a, ← Module.End.mul_apply, ← map_mul, mul_comm,
      ← baseChangeAction_toModuleEnd_self_apply, mem_eigenSub.1 he a, map_smul, LinearMap.smul_apply]

end GlobalTheory.EigenSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZeroStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_coefficients_separatingCharacters_eq_zero : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ x, χ 0 x = 1) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → (∀ a, ∫ x in 𝓕, χ a x * Φ x ∂μ = 0) → Φ = 0 := by
  first | exact @GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero | exact GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero | (intros; apply GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharpolyBaseChangeIntegrallyClosed
section
open CategoryTheory Polynomial GlobalTheory.NormalDescent TensorProduct

namespace GlobalTheory.NormalDescent

theorem exists_map_eq_charK : ∀ {A B K : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [Field K]
    [Algebra A K] [IsFractionRing A K] (φ : A →+* B) (hφ : φ.Finite) (b : B),
    ∃ P : A[X], P.map (algebraMap A K) = charK φ hφ K b := by
  intro A B K _ _ _ _ _ _ _ φ hφ b
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  obtain ⟨g, hgm, hg⟩ := (Algebra.IsIntegral.isIntegral (R := A) b)
  have hT : aeval (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)) (g.map (algebraMap A K)) = 0 := by
    rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_map_algebraMap]
    have : (1 : K) ⊗ₜ[A] b = Algebra.TensorProduct.includeRight b := rfl
    rw [this, Polynomial.aeval_algHom_apply, show aeval b g = 0 from hg, map_zero, map_zero]
  have hd := GlobalTheory.T.charpoly_dvd_pow_finrank_of_aeval_eq_zero _ _ hT
  rw [← Polynomial.map_pow] at hd
  obtain ⟨P, hP⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K (hgm.pow _) hd
  refine ⟨P, ?_⟩
  have hm : (charK φ hφ K b).Monic := charK_monic φ hφ K b
  have : (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)).charpoly = charK φ hφ K b := rfl
  rw [this, hm.leadingCoeff, C_1, mul_one] at hP
  exact hP

end GlobalTheory.NormalDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicLocalInverseOfInjOn
section
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.InjHol

theorem analyticAt_of_differentiableOn_euclidean {n : ℕ} {W : Set (V n)} {g : V n → V n} {a : V n}
    (hW : IsOpen W) (ha : a ∈ W) (hg : DifferentiableOn ℂ g W) : AnalyticAt ℂ g a := by
  let e : V n ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  have hU : IsOpen (e.symm ⁻¹' W) := hW.preimage e.symm.continuous
  have hf : DifferentiableOn ℂ (fun x => e (g (e.symm x))) (e.symm ⁻¹' W) :=
    e.differentiable.comp_differentiableOn
      (hg.comp e.symm.differentiable.differentiableOn (fun _ hx => hx))
  have ha' : e a ∈ e.symm ⁻¹' W := by simpa using ha
  have han : AnalyticAt ℂ (fun x => e (g (e.symm x))) (e a) := analyticAt_pi_iff.mpr fun i =>
    ReciprocityTheory.AnForm.Osgood.osgood n _ (fun x => e (g (e.symm x)) i) hU
      (differentiableOn_pi.mp hf i) _ ha'
  have h2 : AnalyticAt ℂ (fun y => e.symm (e (g (e.symm (e y))))) a :=
    ((e.symm : (Fin n → ℂ) →L[ℂ] V n).analyticAt _).comp
      (han.comp ((e : V n →L[ℂ] (Fin n → ℂ)).analyticAt a))
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using h2

theorem exists_local_inverse_of_injOn :
    ∀ (n : ℕ) (W : Set (V n)) (g : V n → V n) (a : V n), IsOpen W → a ∈ W →
      DifferentiableOn ℂ g W → Set.InjOn g W →
      ∃ h : V n → V n, ∀ᶠ u in 𝓝 (g a), h u ∈ W ∧ g (h u) = u ∧ DifferentiableAt ℂ h u := by
  intro n W g a hW ha hg hinj
  have han := analyticAt_of_differentiableOn_euclidean hW ha hg
  have hi : Function.Injective (fderiv ℂ g a) :=
    localStatement n _ _ (by simp) (by simp) g a han ⟨W, hW.mem_nhds ha, hinj⟩
  have hs : Function.Surjective (fderiv ℂ g a) := LinearMap.injective_iff_surjective.mp
    (show Function.Injective (fderiv ℂ g a : V n →ₗ[ℂ] V n) from hi)
  let f' : V n ≃L[ℂ] V n := ContinuousLinearEquiv.ofBijective (fderiv ℂ g a)
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs)
  have hf' : HasFDerivAt g (f' : V n →L[ℂ] V n) a := han.differentiableAt.hasFDerivAt
  have hc : ContDiffAt ℂ 1 g a := han.contDiffAt
  have hn : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  have hG := hc.to_localInverse hf' hn
  have hGv := hc.localInverse_apply_image hf' hn
  refine ⟨hc.localInverse hf' hn, ?_⟩
  have hT : Filter.Tendsto (hc.localInverse hf' hn) (𝓝 (g a)) (𝓝 a) := by
    have := hG.continuousAt.tendsto
    rwa [hGv] at this
  have hr : ∀ᶠ u in 𝓝 (g a), g (hc.localInverse hf' hn u) = u :=
    (hc.hasStrictFDerivAt' hf' hn).eventually_right_inverse
  filter_upwards [hT.eventually (hW.mem_nhds ha), hr, hG.eventually (by simp)] with u h1 h2 h3
  exact ⟨h1, h2, h3.differentiableAt hn⟩

end GlobalTheory.InjHol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalSectionOfIsIntegralElemNormalSchemeStatement
section
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_section_of_isIntegralElem_normal_scheme : ∀ {T Z : Scheme.{0}} [GlobalTheory.IsNormalScheme Z] [IsLocallyNoetherian Z] (j : T ⟶ Z) [IsOpenImmersion j],
    Dense (Set.range j) → ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (j.app U).hom.IsIntegralElem s →
    ∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s := by
  first | exact @GlobalTheory.exists_section_of_isIntegralElem_of_isOpenImmersion | exact GlobalTheory.exists_section_of_isIntegralElem_of_isOpenImmersion | (intros; apply GlobalTheory.exists_section_of_isIntegralElem_of_isOpenImmersion <;> assumption)
end

