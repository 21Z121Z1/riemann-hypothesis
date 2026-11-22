import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0234
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0246
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.PolarLatticePairs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormEqRelIndexMul
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0244

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdaptedPointChangeOfRationalBasisStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_point_change_of_rational_basis : ∀ (D : D7), admG1 D → galStar D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), FixK D M ρ → DataIn D (tor0 D cc δ) M → ∀ (N N' r s : ℕ) (B : Fin r → Matrix (Fin N') (Fin N) D.host.E) (b : Fin s → Matrix (Fin N') (Fin N) D.host.E), OnB D B → ∃ R : ℕ, 0 < R ∧ ∀ (n : ℕ) (c c' : Fin s → ℂ), 0 < n → (∀ j, InRationalLattice (lamOf D cc δ) (c j)) → (∀ j, Adp1 M ρ (lamOf D cc δ) (n * R) (c j) (c' j)) → AdpB D (tor0 D cc δ) M ρ B n (∑ j, c j • embV D (tor0 D cc δ) (b j)) (∑ j, c' j • embV D (torConj D (tor0 D cc δ) M ρ) (b j)) := by
  first | exact @GlobalTheory.AdaptedBasis.adpB_of_family | exact GlobalTheory.AdaptedBasis.adpB_of_family | (intros; apply GlobalTheory.AdaptedBasis.adpB_of_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdaptedTorsionLiftDeeperLevelStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_torsion_lift_deeper_level : ∀ (D : D7), galStar D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ, FixK D ⊤ σ → ∀ (c c' : ℂ) (n₀ n : ℕ), 0 < n₀ → 0 < n → InRationalLattice (lamOf D cc δ) c → Adp1 ⊤ σ (lamOf D cc δ) n₀ c c' → ∃ ω ∈ lamOf D cc δ, Adp1 ⊤ σ (lamOf D cc δ) (n₀ * n) (c + (n₀ : ℂ) * ω) c' := by
  first | exact @GlobalTheory.GalTheta.adapted_lift_deeper | exact GlobalTheory.GalTheta.adapted_lift_deeper | (intros; apply GlobalTheory.GalTheta.adapted_lift_deeper <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdelicHermitianCharacterPairingProperties
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.GamAlg

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [D.host.toHostAx.conjE_apply, D.host.toHostAx.conjE_apply]
  simp

theorem sgA_sgA (D : D7) (y : AE D) : sgA D (sgA D y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sgA, Formalism.UG.sigR, conj_conj]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sum_eq_trace {R : Type} [CommRing R] (s : R →+* R) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    ∑ i, ∑ j, x i j * s (y i j) = Matrix.trace (x * (y.map s).transpose) := by
  simp [Matrix.trace, Matrix.mul_apply]

theorem trace_inv {R : Type} [CommRing R] (s : R →+* R) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R)
    (p : Matrix (Fin a) (Fin a) R) (q : Matrix (Fin b) (Fin b) R)
    (hp : (p.map s).transpose * p = 1) (hq : (q.map s).transpose * q = 1) :
    Matrix.trace (p * x * q * ((p * y * q).map s).transpose) = Matrix.trace (x * (y.map s).transpose) := by
  have hq' : q * (q.map s).transpose = 1 := mul_eq_one_comm.1 hq
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  have h : p * x * q * ((q.map s).transpose * ((y.map s).transpose * (p.map s).transpose)) =
      p * (x * (q * (q.map s).transpose) * (y.map s).transpose * (p.map s).transpose) := by
    simp only [Matrix.mul_assoc]
  rw [h, hq', Matrix.mul_one, Matrix.trace_mul_comm, Matrix.mul_assoc, hp, Matrix.mul_one]

end GlobalTheory.FinWeil.GamAlg

open GlobalTheory.FinWeil.GamAlg GlobalTheory.NormSum.PtsMem in

theorem GlobalTheory.FinWeil.gamA_alg : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ ψ : AE D → ℂ, IsPsi D cc δ ψ → ∀ (N N' : ℕ), (∀ u ζ η, gamA ψ (actA D N N' u ζ) (actA D N N' u η) = gamA ψ ζ η) ∧ (∀ ζ : XA D N N', gamA ψ ζ ζ = 1) ∧ (∀ (r : 𝓞 D.host.E) (ζ η : XA D N N'), gamA ψ (r • ζ) η = gamA ψ ζ (sgO D r • η)) ∧ (∀ ζ η ξ : XA D N N', gamA ψ (ζ + η) ξ = gamA ψ ζ ξ * gamA ψ η ξ) ∧ (∀ ζ η ξ : XA D N N', gamA ψ ζ (η + ξ) = gamA ψ ζ η * gamA ψ ζ ξ) := by
  intro D _ cc δ _ ψ hψ N N'
  obtain ⟨hadd, -, -, hsg, -⟩ := hψ
  refine ⟨?_, fun ζ => ?_, fun r ζ η => ?_, fun ζ η ξ => ?_, fun ζ η ξ => ?_⟩
  · rintro ⟨g, g'⟩ ζ η
    unfold gamA
    rw [sum_eq_trace, sum_eq_trace, actA_apply, actA_apply,
      trace_inv _ _ _ _ _ ((mem_GA D _).1 g'.2) ((mem_GA D _).1 (inv_mem g.2))]
  · unfold gamA
    set t := ∑ i, ∑ j, ζ i j * sgA D (ζ i j) with ht
    have h1 : sgA D t = t := by
      simp only [ht, map_sum, map_mul, sgA_sgA]
      simp only [mul_comm]
    have h2 : t = inc D (1 / 2) * t + sgA D (inc D (1 / 2) * t) := by
      rw [map_mul, sgA_inc, h1, ← add_mul, ← map_add, map_div₀, map_one, map_ofNat, add_halves, map_one, one_mul]
    rw [h2]
    exact hsg _
  · unfold gamA
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_AE, smul_AE, map_mul, sgA_inc, coe_sgO, conj_conj]
    ring
  · unfold gamA
    rw [← hadd]
    simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  · unfold gamA
    rw [← hadd]
    simp only [Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleAtOfIrreducibleTame
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.WdCocycle

section General

variable {D : D7} {T : Tor D} {N N' : ℕ}

theorem hf_add_left (x y z : VC D N N') : Hf D T (x + y) z = Hf D T x z + Hf D T y z := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

theorem hf_add_right (x y z : VC D N N') : Hf D T x (y + z) = Hf D T x y + Hf D T x z := by
  simp only [Hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_div]

theorem hf_conj (x z : VC D N N') : Hf D T z x = (starRingEnd ℂ) (Hf D T x z) := by
  simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem wd_wd (x y : VC D N N') (F : VC D N N' → ℂ) :
    Wd D T x (Wd D T y F) = ee (-(w0 D * Hf D T x y).im) • Wd D T (x + y) F := by
  funext z
  have h1 : Hf D T x y = ((Hf D T x y).re : ℂ) + ((Hf D T x y).im : ℂ) * Complex.I := (Complex.re_add_im _).symm
  have h2 : Hf D T y x = ((Hf D T x y).re : ℂ) - ((Hf D T x y).im : ℂ) * Complex.I := by
    rw [hf_conj x y]
    apply Complex.ext <;> simp
  have h3 : (Hf D T y x).re = (Hf D T x y).re := by
    rw [hf_conj x y, Complex.conj_re]
  have h4 : (w0 D * Hf D T x y).im = ((Hf D T x y).im + Real.sqrt D.host.d * (Hf D T x y).re) / 2 := by
    have : w0 D = ((1 / 2 : ℝ) : ℂ) + ((Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I := by
      rw [w0]; push_cast; ring
    rw [this]
    simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have key : ee (qH D T x / 2) * ee (qH D T y / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T (z + x) y - (Real.pi : ℂ) * Hf D T y y / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z x - (Real.pi : ℂ) * Hf D T x x / 2) =
      ee (-(w0 D * Hf D T x y).im) * ee (qH D T (x + y) / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z (x + y) - (Real.pi : ℂ) * Hf D T (x + y) (x + y) / 2) := by
    simp only [ee, ← Complex.exp_add, qH]
    congr 1
    rw [h4]
    simp only [hf_add_left, hf_add_right, Complex.add_re, h3]
    rw [h2]
    generalize (Hf D T x y).re = a at h1 ⊢
    generalize (Hf D T x y).im = b at h1 ⊢
    rw [h1]
    push_cast
    ring
  simp only [Wd, U, wdPh, Pi.smul_apply, smul_eq_mul]
  rw [add_assoc z x y]
  linear_combination F (z + (x + y)) * key

end General

variable {D : D7}

theorem emb_conj (φ : D.host.E →+* ℂ) (x : D.host.E) : φ (D.host.conj x) = starRingEnd ℂ (φ x) :=
  D.host.conjE_apply φ x

theorem hf_pt (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z y : Matrix (Fin N') (Fin N) D.host.E) :
    Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ y) =
      ((‖δ‖ ^ 2 / area (lamOf D cc δ) : ℝ) : ℂ) * ∑ τ, embT D τ (∑ i, ∑ j, z i j * D.host.conj (y i j)) := by
  have h : δ * starRingEnd ℂ δ = (‖δ‖ : ℂ) ^ 2 := Complex.mul_conj' δ
  simp only [Hf, pt, embV, tor0, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, emb_conj]
  push_cast
  rw [← h, div_mul_eq_mul_div]
  congr 1
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem pt_add (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z y : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (z + y) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ y := by
  funext τ i j
  simp only [pt, embV, tor0, Pi.smul_apply, Pi.add_apply, Matrix.add_apply, smul_eq_mul, map_add, mul_add]

theorem wd_cocycle : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ w : 𝓞 D.host.E, w + sgO D w = 1 ∧ ∀ (N N' : ℕ) (z y : Matrix (Fin N') (Fin N) D.host.E), ee (-(Hf D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (pt D (tor0 D cc δ) δ y)).im) = psi0 D cc δ (∑ i, ∑ j, z i j * D.host.conj (y i j)) ∧ pt D (tor0 D cc δ) δ (z + y) = pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ y ∧ ∀ F, Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ y) F) = psi0 D cc δ (∑ i, ∑ j, (w : D.host.E) * z i j * D.host.conj (y i j)) • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z + y)) F := by
  intro D hg cc δ _
  obtain ⟨a, ha⟩ := exists_integer_map_eq_w0 D
  let w : 𝓞 D.host.E := algebraMap (𝓞 D.host.K) (𝓞 D.host.E) a
  have hw : (w : D.host.E) = ((a : D.host.K) : D.host.E) := rfl
  have hτ : ∀ τ, embT D τ (w : D.host.E) = w0 D := fun τ => by
    rw [hw, ← ha]
    exact hg.1 τ _
  refine ⟨w, ?_, fun N N' z y => ⟨?_, pt_add cc δ z y, fun F => ?_⟩⟩
  · apply RingOfIntegers.ext
    apply D.host.φ₀.injective
    change D.host.φ₀ ((w : D.host.E) + D.host.conj (w : D.host.E)) = D.host.φ₀ 1
    rw [map_add, emb_conj, hw, ha, map_one, w0]
    simp only [map_div₀, map_add, map_mul, map_one, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  · rw [hf_pt, psi0, Complex.im_ofReal_mul]
  · rw [wd_wd, pt_add, hf_pt, psi0]
    congr 3
    rw [mul_left_comm, Complex.im_ofReal_mul, Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← hτ τ, ← map_mul]
    simp only [Finset.mul_sum, mul_assoc]

end GlobalTheory.FinWeil.WdCocycle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlgebraicTaylorTorsionTranslateEvenTheta
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.EvenThetaTorsion

variable {Λ : AddSubgroup ℂ}

def phase (Λ : AddSubgroup ℂ) (x y : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * (y * (starRingEnd ℂ) x - x * (starRingEnd ℂ) y) / (2 * (area Λ : ℂ)))

theorem phase_ne_zero (x y : ℂ) : phase Λ x y ≠ 0 := Complex.exp_ne_zero _

theorem thetaTranslate_comp_eq_phase_mul_add (x y : ℂ) (G : ℂ → ℂ) (z : ℂ) :
    U1 Λ x (U1 Λ y G) z = phase Λ x y * U1 Λ (x + y) G z := by
  simp only [U1, phase]
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, add_assoc]
  congr 2
  simp only [map_add]
  ring

theorem rationalLatticePoint_add {x y : ℂ} (hx : InRationalLattice Λ x) (hy : InRationalLattice Λ y) : InRationalLattice Λ (x + y) := by
  obtain ⟨m, hm, hx⟩ := hx
  obtain ⟨n, hn, hy⟩ := hy
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  have := Λ.add_mem (Λ.nsmul_mem hx n) (Λ.nsmul_mem hy m)
  convert this using 1
  simp only [nsmul_eq_mul]
  push_cast
  ring

theorem rationalLatticePoint_of_mem_lattice {x : ℂ} (hx : x ∈ Λ) : InRationalLattice Λ x := ⟨1, one_pos, by simpa using hx⟩

theorem phase_mem (h : IsLat Λ) {x y : ℂ} (hx : InRationalLattice Λ x) (hy : InRationalLattice Λ y) :
    phase Λ x y ∈ Qbar := by
  obtain ⟨m, hm, hx⟩ := hx
  obtain ⟨n, hn, hy⟩ := hy
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  obtain ⟨k, hk⟩ := GlobalTheory.exists_int_im_latticeForm L ((hL _).1 hy) ((hL _).1 hx)
  have hA := GlobalTheory.latticeArea_pos L
  rw [GlobalTheory.latticeForm, Complex.div_ofReal_im, div_eq_iff hA.ne', ← GlobalTheory.OddTheta.area_eq L Λ hL] at hk
  rw [← GlobalTheory.OddTheta.area_eq L Λ hL] at hA
  have hA' : (area Λ : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  have e := Complex.sub_conj ((n : ℂ) * y * (starRingEnd ℂ) ((m : ℂ) * x))
  rw [hk] at e
  simp only [map_mul, map_natCast, Complex.conj_conj] at e
  push_cast at e
  have hp : phase Λ x y ^ (2 * m * n) = 1 := by
    rw [phase, ← Complex.exp_nat_mul, ← Complex.exp_int_mul_two_pi_mul_I k]
    congr 1
    push_cast
    field_simp
    linear_combination e
  rw [mem_algebraicClosure_iff]
  refine IsAlgebraic.of_pow (n := 2 * m * n) (by positivity) ?_
  rw [hp]
  exact isAlgebraic_one

theorem algEnt_const_mul {F : ℂ → ℂ} (hF : AlgEnt F) {κ : ℂ} (hκ : κ ∈ Qbar) :
    AlgEnt fun z => κ * F z := by
  refine ⟨hF.1.const_mul κ, fun n => ?_⟩
  have : coef1 (fun z => κ * F z) n = κ * coef1 F n := by
    rw [coef1, coef1, iteratedDeriv_const_mul_field, mul_div_assoc]
  rw [this]
  exact Qbar.mul_mem hκ (hF.2 n)

theorem thetaTranslate_evenTheta_eq_sigmaStar_translate (t x z : ℂ) : U1 Λ x (GL3Theta.th0 Λ t) z =
    (phase Λ x t / U1 Λ t (sgStar Λ) 0) * U1 Λ (x + t) (sgStar Λ) z := by
  rw [div_mul_eq_mul_div, ← thetaTranslate_comp_eq_phase_mul_add]
  simp only [U1, GL3Theta.th0]
  ring

theorem sigmaStarTranslate_add_lattice_sign_phase (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) (y z : ℂ) :
    U1 Λ (y + ω) (sgStar Λ) z =
      ((if ω / 2 ∈ Λ then 1 else -1) / phase Λ y ω) * U1 Λ y (sgStar Λ) z := by
  have e := thetaTranslate_comp_eq_phase_mul_add (Λ := Λ) y ω (sgStar Λ) z
  rw [funext (h.sg_law hω)] at e
  rw [div_mul_eq_mul_div, eq_div_iff (phase_ne_zero _ _), mul_comm, ← e]
  simp only [U1]
  ring

theorem algebraicTaylor_torsionTranslate_evenTheta_alt : ∀ Λ : AddSubgroup ℂ, IsLat Λ → (∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (sgStar Λ))) → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (GL3Theta.th0 Λ t₀)) ∧ ∀ ω ∈ Λ, ∃ κ ∈ Qbar, κ ≠ 0 ∧ ∀ z, U1 Λ (x + ω) (GL3Theta.th0 Λ t₀) z = κ * U1 Λ x (GL3Theta.th0 Λ t₀) z := by
  intro Λ h halg t _ h2 x hx
  have ht : InRationalLattice Λ t := ⟨2, two_pos, by simpa using h2⟩
  have hc : U1 Λ t (sgStar Λ) 0 ∈ Qbar := by
    simpa [coef1] using (halg t ht).2 0
  refine ⟨?_, fun ω hω => ?_⟩
  · rw [funext (thetaTranslate_evenTheta_eq_sigmaStar_translate t x)]
    exact algEnt_const_mul (halg _ (rationalLatticePoint_add hx ht)) (Qbar.div_mem (phase_mem h hx ht) hc)
  · have hω' := rationalLatticePoint_of_mem_lattice hω
    have hs : (if ω / 2 ∈ Λ then 1 else -1 : ℂ) ∈ Qbar := by
      split_ifs
      · exact Qbar.one_mem
      · exact Qbar.neg_mem Qbar.one_mem
    have hs0 : (if ω / 2 ∈ Λ then 1 else -1 : ℂ) ≠ 0 := by
      split_ifs <;> norm_num
    refine ⟨phase Λ (x + ω) t / phase Λ x t * ((if ω / 2 ∈ Λ then 1 else -1) / phase Λ (x + t) ω),
      Qbar.mul_mem (Qbar.div_mem (phase_mem h (rationalLatticePoint_add hx hω') ht) (phase_mem h hx ht))
        (Qbar.div_mem hs (phase_mem h (rationalLatticePoint_add hx ht) hω')),
      mul_ne_zero (div_ne_zero (phase_ne_zero _ _) (phase_ne_zero _ _))
        (div_ne_zero hs0 (phase_ne_zero _ _)), fun z => ?_⟩
    rw [thetaTranslate_evenTheta_eq_sigmaStar_translate, thetaTranslate_evenTheta_eq_sigmaStar_translate, add_right_comm, sigmaStarTranslate_add_lattice_sign_phase h hω]
    have := phase_ne_zero (Λ := Λ) x t
    generalize (if ω / 2 ∈ Λ then 1 else -1 : ℂ) / phase Λ (x + t) ω = s
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    generalize (U1 Λ t (sgStar Λ) 0)⁻¹ = c
    field_simp

end GlobalTheory.EvenThetaTorsion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardLatticeQuotIdeal
section
open NumberField IsDedekindDomain Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs
open scoped Pointwise

noncomputable section

namespace GlobalTheory.MatrixLatticeIndex

theorem card_matIn (D : D7) (a d : ℕ) (A B : Submodule (𝓞 D.host.E) D.host.E) :
    Nat.card (matIn D a d A ⧸ (matIn D a d B).addSubgroupOf (matIn D a d A)) =
      (B.toAddSubgroup.relIndex A.toAddSubgroup) ^ (a * d) := by
  let Q := A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup
  let f : matIn D a d A →+ (Fin d → Fin a → Q) :=
    { toFun := fun z i j => QuotientAddGroup.mk (⟨z.1 i j, z.2 i j⟩ : A.toAddSubgroup)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := by
    intro y
    refine ⟨⟨fun i j => ((y i j).out : A.toAddSubgroup), fun i j => (y i j).out.2⟩, ?_⟩
    funext i j
    exact QuotientAddGroup.out_eq' (y i j)
  have hker : f.ker = (matIn D a d B).addSubgroupOf (matIn D a d A) := by
    ext z
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro h i j
      exact (QuotientAddGroup.eq_zero_iff _).1 (congrFun (congrFun h i) j)
    · intro h
      funext i j
      exact (QuotientAddGroup.eq_zero_iff _).2 (h i j)
  rw [← hker, Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv,
    Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a), Nat.card_eq_fintype_card (α := Fin d),
    Fintype.card_fin, Fintype.card_fin, ← pow_mul]
  rfl

theorem relIndex_smul {K : Type} [Field K] [NumberField K]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hJ : J ≠ 0) (q : Ideal (𝓞 K)) (hq : q ≠ ⊥) :
    (q • (J : Submodule (𝓞 K) K)).toAddSubgroup.relIndex (J : Submodule (𝓞 K) K).toAddSubgroup =
      Ideal.absNorm q := by
  have hq' : (q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hq
  have hle : (q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J ≤ J := by
    calc (q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J ≤ 1 * J :=
          mul_le_mul' FractionalIdeal.coeIdeal_le_one le_rfl
      _ = J := one_mul J
  have h := Formalism.L2.LamCM.Dx.absNorm_eq_relIndex_mul J _ (mul_ne_zero hq' hJ) hle
  have he : (((q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) = q • (J : Submodule (𝓞 K) K) := by
    apply le_antisymm
    · rw [FractionalIdeal.coe_mul]
      refine Submodule.mul_le.2 fun x hx y hy => ?_
      obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem_smul hb hy
    · refine Submodule.smul_le.2 fun b hb y hy => ?_
      rw [Algebra.smul_def]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hb) hy
  rw [he, map_mul, FractionalIdeal.coeIdeal_absNorm] at h
  have h0 : FractionalIdeal.absNorm J ≠ 0 := fun h' => hJ (FractionalIdeal.absNorm_eq_zero_iff.1 h')
  exact_mod_cast (mul_right_cancel₀ h0 h).symm

open GlobalTheory.NormSum.MovedLattice in

theorem coefLat_eq (D : D7) (cc : Ideal (𝓞 D.host.K)) :
    coefLat D cc = ((ext D cc * D.host.AA0 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
      Submodule (𝓞 D.host.E) D.host.E) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro t ⟨c, hc, m, hm, rfl⟩
    exact FractionalIdeal.mul_mem_mul (mem_ext D hc) hm
  · rw [FractionalIdeal.coe_mul]
    refine Submodule.mul_le.2 fun x hx y hy => ?_
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
    clear hx
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨c, hc, rfl⟩ := hb
      exact Submodule.subset_span ⟨c, hc, y, hy, rfl⟩
    | zero => rw [map_zero, zero_mul]; exact zero_mem _
    | add b b' _ _ hb hb' => rw [map_add, add_mul]; exact add_mem hb hb'
    | smul r b _ hb =>
      rw [smul_eq_mul, map_mul, mul_assoc, ← Algebra.smul_def]
      exact Submodule.smul_mem _ r hb

end GlobalTheory.MatrixLatticeIndex

open GlobalTheory.NormSum.MovedLattice GlobalTheory.MatrixLatticeIndex in

theorem GlobalTheory.MatrixLatticeIndex.card_lattice_quot_ideal : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (a d : ℕ) (q : Ideal (𝓞 D.host.E)), cc ≠ ⊥ → q ≠ ⊥ → Nat.card (lat0 D cc a d ⧸ (latQ D cc a d q).addSubgroupOf (lat0 D cc a d)) = Ideal.absNorm q ^ (a * d) := by
  intro D cc a d q hcc hq
  rw [card_matIn, coefLat_eq, relIndex_smul _ (mul_ne_zero (ext_ne_zero D hcc) (inverseHalfDifferent_ne_zero D)) q hq]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaLatticePointMemThetaLatticeOfAdelicStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmThetaLatticePoint_mem_thetaLattice_of_adelic : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' : ℕ) (g : GA D N) (g' : GA D N') (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → ∀ z : Matrix (Fin N') (Fin N) D.host.E, (∀ i j, ((((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) * ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) i j ∈ IhE D cc) → pt D (tor0 D cc δ) δ z ∈ La D (tor0 D cc δ) L₁ L₁' := by
  first | exact @GlobalTheory.NormSum.pt_mem_La_of_adelic | exact GlobalTheory.NormSum.pt_mem_La_of_adelic | (intros; apply GlobalTheory.NormSum.pt_mem_La_of_adelic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjProdCompLinearFormsOfCoeffConjStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_prod_comp_linearForms_of_coeff_conj : ∀ (D : D7) (N N' r : ℕ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (g g' : Fin r → ℂ → ℂ) (l l' : Fin r → VC D N N'), (∀ j, Differentiable ℂ (g j)) → (∀ j, Differentiable ℂ (g' j)) → (∀ j n, coef1 (g j) n ∈ M ∧ coef1 (g' j) n = cj M ρ (coef1 (g j) n)) → (∀ j τ a c, l j τ a c ∈ M ∧ l' j τ a c = cj M ρ (l j τ a c)) → CjF D M ρ (fun z : VC D N N' => ∏ j, g j (∑ τ, ∑ a, ∑ c, z τ a c * l j τ a c)) (fun z : VC D N N' => ∏ j, g' j (∑ τ, ∑ a, ∑ c, z τ a c * l' j τ a c)) := by
  first | exact @GlobalTheory.ThetaConj.ProdLin.cjF_prod | exact GlobalTheory.ThetaConj.ProdLin.cjF_prod | (intros; apply GlobalTheory.ThetaConj.ProdLin.cjF_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateLatticeEqClosureIndependentPairStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateLattice_eq_closure_independent_pair : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M → ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ lamConj M ρ (lamOf D cc δ) = AddSubgroup.closure {w₁, w₂} := by
  first | exact @GlobalTheory.ConjugateLattice.lamConj_eq_closure_pair | exact GlobalTheory.ConjugateLattice.lamConj_eq_closure_pair | (intros; apply GlobalTheory.ConjugateLattice.lamConj_eq_closure_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupKummerDlogModPrimePowLevelLStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_kummer_dlog_mod_primePow_levelL : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → 1 ≤ n → ∀ ι : On p L →ₐ[O0 p] Ω, IsEmb T L ι →
  ∀ (u v : (On p L)ˣ) (α β α' β' : On p L), IsDlog p L (u : On p L) α β → IsDlog p L (v : On p L) α' β' →
  ∀ r s : Ω, r ^ (p ^ n) = ι u → s ^ (p ^ n) = ι v →
  ∀ a b lz lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Gn T L) r a → IsKum T n (Gn T L) s b → IsKum T n (Gn T L) (T.ζ (L + n)) lz → IsKum T n (Gn T L) (T.qq (L + n)) lq →
  Cob2 n (Gn T L) (fun g h => (p : Ω) ^ c * (((a g).val : Ω) * ((b h).val : Ω)) + (p : Ω) ^ c * ι (α * β' - β * α') * (((lz g).val : Ω) * ((lq h).val : Ω))) := by
  first | exact @GlobalTheory.K5.LevelDown.cup_kummer_dlog_mod | exact GlobalTheory.K5.LevelDown.cup_kummer_dlog_mod | (intros; apply GlobalTheory.K5.LevelDown.cup_kummer_dlog_mod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefGramSelfDualAfterFieldEmbeddingStatement
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.defGram_selfDual_after_field_embedding : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] (cE : E →+* E), (∀ (φ : E →+* ℂ) (x : E), φ (cE x) = starRingEnd ℂ (φ x)) → ∀ (ι : Type) (emb : ι → E →+* K), (∀ τ x, star (emb τ x) = emb τ (cE x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ φ : E →+* ℂ, (J.map φ).PosDef) → ∀ τ, IsDefGram (gramK emb J τ) ∧ IsDefGram (gramKd emb J τ) ∧ ∀ L : Submodule (𝓞 E) (Fin n → E), IsSelfDualE cE J L → IsSelfDualK (gramK emb J τ) (tauLat emb τ L) ∧ IsSelfDualK (gramKd emb J τ) (dualFr (tauLat emb τ L)) := by
  first | exact @GlobalTheory.TestLat.defGram_selfDual_of_embedding | exact GlobalTheory.TestLat.defGram_selfDual_of_embedding | (intros; apply GlobalTheory.TestLat.defGram_selfDual_of_embedding <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetRationalMatrixTwoSidedMulEqProdEmbeddingsStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_rationalMatrixTwoSidedMul_eq_prod_embeddings : ∀ (D : D7) (N N' : ℕ) (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E), LinearMap.det (mulV D M' M) = ∏ τ, embT D τ M'.det ^ N * embT D τ M.det ^ N' := by
  first | exact @GlobalTheory.TwoSidedDet.det_mulV | exact GlobalTheory.TwoSidedDet.det_mulV | (intros; apply GlobalTheory.TwoSidedDet.det_mulV <;> assumption)
end

