import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InstSecondCountable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0274
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0267
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoshConstNumericalBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

namespace GlobalTheory.CartanInt

theorem cosh_const_numerical_bound (p q : ℕ) :
    (18 / 5 * max 1 (3 / 2 * ((p + q : ℕ) : ℝ) ^ 2) / ((p + q : ℕ) : ℝ)) ^ ((p + q) ^ 2) * (9 / 2) ^ (p ^ 2 + q ^ 2) / Real.pi ^ (p * q) * (2 ^ (2 * (p + q) * min p q) * (2 * Real.pi / (2 / ((((p + q : ℕ) : ℝ) + 1) / 2)) ^ 2) ^ (p * q)) ≤ Real.exp (3 * ((p + q : ℕ) : ℝ) ^ 2 * Real.log (((p + q : ℕ) : ℝ) + 2)) := by
  rcases Nat.eq_zero_or_pos (p + q) with h0 | hpos
  · have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst hp hq
    simp
  have hsq : (p + q) ^ 2 = (p ^ 2 + q ^ 2) + 2 * (p * q) := by ring
  have hmin : 2 * (p + q) * min p q ≤ 4 * (p * q) := by
    rcases le_total p q with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  have hR : Real.exp (3 * ((p + q : ℕ) : ℝ) ^ 2 * Real.log (((p + q : ℕ) : ℝ) + 2))
      = (((p + q : ℕ) : ℝ) + 2) ^ (3 * (p + q) ^ 2) := by
    have : (3 * ((p + q : ℕ) : ℝ) ^ 2) = ((3 * (p + q) ^ 2 : ℕ) : ℝ) := by push_cast; ring
    rw [this, Real.exp_nat_mul, Real.exp_log (by positivity)]
  rw [hR, hsq]
  have ha : (1 : ℝ) ≤ ((p + q : ℕ) : ℝ) := by exact_mod_cast hpos
  generalize ((p + q : ℕ) : ℝ) = a at ha
  generalize p ^ 2 + q ^ 2 = d
  generalize 2 * (p + q) * min p q = m at hmin
  generalize p * q = n at hmin
  have ha0 : 0 < a := by linarith
  have hpi := Real.pi_pos
  have hmax : max 1 (3 / 2 * a ^ 2) = 3 / 2 * a ^ 2 := max_eq_right (by nlinarith)
  have h1 : 18 / 5 * (3 / 2 * a ^ 2) / a = 27 / 5 * a := by field_simp; ring
  have h2 : 2 * Real.pi / (2 / ((a + 1) / 2)) ^ 2 = Real.pi * ((a + 1) ^ 2 / 8) := by
    field_simp; ring
  rw [hmax, h1, h2]
  have h3 : (2 : ℝ) ^ m ≤ 16 ^ n := by
    calc (2 : ℝ) ^ m ≤ 2 ^ (4 * n) := pow_le_pow_right₀ (by norm_num) hmin
      _ = 16 ^ n := by rw [pow_mul]; norm_num
  have h4 : 27 / 5 * a * (9 / 2) ≤ (a + 2) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (a - 1)) (show (0 : ℝ) ≤ a + 8 by linarith)]
  have h5 : 8 * a * (a + 1) ≤ (a + 2) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (a - 1)) ha0.le]
  have h6 : (27 / 5 * a) ^ 2 * 16 * ((a + 1) ^ 2 / 8) ≤ (a + 2) ^ 6 := by
    have h7 : (8 * a * (a + 1)) ^ 2 ≤ ((a + 2) ^ 3) ^ 2 := by gcongr
    have h8 : 0 ≤ (a * (a + 1)) ^ 2 := by positivity
    nlinarith
  calc (27 / 5 * a) ^ (d + 2 * n) * (9 / 2) ^ d / Real.pi ^ n *
        (2 ^ m * (Real.pi * ((a + 1) ^ 2 / 8)) ^ n)
      ≤ (27 / 5 * a) ^ (d + 2 * n) * (9 / 2) ^ d / Real.pi ^ n *
        (16 ^ n * (Real.pi * ((a + 1) ^ 2 / 8)) ^ n) := by gcongr
    _ = (27 / 5 * a * (9 / 2)) ^ d * ((27 / 5 * a) ^ 2 * 16 * ((a + 1) ^ 2 / 8)) ^ n := by
        rw [pow_add, pow_mul, mul_pow Real.pi, mul_pow (27 / 5 * a) (9 / 2),
          mul_pow _ ((a + 1) ^ 2 / 8), mul_pow _ (16 : ℝ)]
        field_simp
    _ ≤ ((a + 2) ^ 3) ^ d * ((a + 2) ^ 6) ^ n := by gcongr
    _ = (a + 2) ^ (3 * (d + 2 * n)) := by
        rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring

end GlobalTheory.CartanInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOneOfSmulHaarEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.HolDS Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.HolDS

theorem eq_one_of_smul_haar_eq {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
    [BorelSpace H] [LocallyCompactSpace H] (ν : Measure H) [ν.IsHaarMeasure] {c : NNReal} (h : c • ν = ν) :
    c = 1 := by
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts H) := inferInstance
  have h0 : ν K ≠ 0 := (Measure.measure_pos_of_nonempty_interior ν K.interior_nonempty).ne'
  have h1 : ν K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have h2 : (c : ENNReal) * ν K = 1 * ν K := by
    conv_rhs => rw [← h]
    rw [one_mul, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [ENNReal.mul_left_inj h0 h1] at h2
  exact_mod_cast h2

theorem haar_unimodular : ∀ (p q : ℕ) (T : GrpData p q), T.haar.IsMulRightInvariant ∧ T.haar.IsInvInvariant := by
  intro p q T
  have h := blockOrd_finSumFinEquiv p q
  haveI := GlobalTheory.RealPar.SqInt.isHaarMeasure_map_covU h T
  set ε : Fin (p + q) → Bool := fun i => (finSumFinEquiv.symm i).isLeft
  set f := GlobalTheory.RealPar.SqInt.covU h T
  have hf : Measurable f := (GlobalTheory.RealPar.SqInt.continuous_covU h T).measurable
  obtain ⟨c, hc⟩ : ∃ c : NNReal, T.haar.map f = c • Formalism.REAL.muG ε :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  have hR : T.haar.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    have hg := Measure.map_right_mul_eq_modularCharacterFun_smul T.haar g
    have h1 : (T.haar.map (· * g)).map f = T.haar.map f := by
      have h2 : (T.haar.map (· * g)).map f = (T.haar.map f).map (· * f g) := by
        rw [Measure.map_map hf (measurable_mul_const g), Measure.map_map (measurable_mul_const _) hf]
        congr 1
        funext x
        simp
      rw [h2, hc, Measure.map_smul, Formalism.REAL.indefinite_unitary_unimodular _ ε (f g)]
    rw [hg, Measure.map_smul] at h1
    rw [hg, eq_one_of_smul_haar_eq _ h1, one_smul]
  refine ⟨hR, ⟨?_⟩⟩
  haveI : T.haar.inv.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance }
  obtain ⟨d, hd⟩ : ∃ d : NNReal, T.haar.inv = d • T.haar := ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  have h1 : T.haar.inv.map f = T.haar.map f := by
    have h2 : T.haar.inv.map f = (T.haar.map f).map (fun x => x⁻¹) := by
      rw [Measure.inv_def, Measure.map_map hf measurable_inv, Measure.map_map measurable_inv hf]
      congr 1
      funext x
      simp
    rw [h2, hc, Measure.map_smul, Formalism.REAL.invInvariant_of Formalism.REAL.indefinite_unitary_unimodular _ ε]
  rw [hd, Measure.map_smul] at h1
  rw [hd, eq_one_of_smul_haar_eq _ h1, one_smul]

end GlobalTheory.HolDS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdelicWeilRepresentationModel
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.Model

theorem conjE_conjE (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply]
  simp

theorem sgA_incE (D : D7) (x : D.host.E) : sgA D (inc D x) = inc D (D.host.conj x) := by
  simp [sgA, inc, Formalism.UG.sigR, Formalism.UG.inclE]

theorem wd_at_zero (D : D7) (T : Tor D) {a d : ℕ} (G : VC D a d → ℂ) : Wd D T 0 G = G := by
  funext z
  simp [Wd, wdPh, ee, qH, U, Hf]

theorem pt_zero (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} :
    pt D (tor0 D cc δ) δ (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
  funext τ i j
  simp [pt, embV, tor0]

theorem pt_nsmul (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (m : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (m • z) = m • pt D (tor0 D cc δ) δ z := by
  funext τ i j
  simp only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
  ring

def incM (D : D7) (N N' : ℕ) : Matrix (Fin N') (Fin N) D.host.E →+ XA D N N' :=
  (inc D).toAddMonoidHom.mapMatrix

theorem incM_apply (D : D7) (N N' : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E) : incM D N N' z = z.map (inc D) := rfl

theorem exists_div (D : D7) {N N' : ℕ} {m : ℕ} (hm : 0 < m) (z : Matrix (Fin N') (Fin N) D.host.E) (a : XA D N N')
    (h : z.map (inc D) = m • a) : ∃ z' : Matrix (Fin N') (Fin N) D.host.E, z = m • z' ∧ z'.map (inc D) = a := by
  have hm' : (m : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  refine ⟨Matrix.of fun i j => (m : D.host.E)⁻¹ * z i j, ?_, ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
    field_simp
  · ext i j
    have h1 := congrFun (congrFun h i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul] at h1
    simp only [Matrix.map_apply, Matrix.of_apply, map_mul, h1]
    rw [← mul_assoc, ← map_natCast (inc D) m, ← map_mul, inv_mul_cancel₀ hm', map_one, one_mul]

theorem mul_nsmul_left {X : Type} [AddCommGroup X] (f : X → ℂ) (h0 : f 0 = 1) (h : ∀ x y, f (x + y) = f x * f y)
    (m : ℕ) (x : X) : f (m • x) = f x ^ m := by
  induction m with
  | zero => simp [h0]
  | succ n ih => rw [succ_nsmul, h, ih, pow_succ]

theorem exists_isModel (D : D7) (hD : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) (N N' : ℕ) :
    ∃ w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA := by
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_finiteAdeleExtendedCharacter_of_curve D hD cc δ hc
  obtain ⟨w, hw, hwd⟩ := GlobalTheory.T.theta_point_additive_form D hD cc δ hc
  obtain ⟨hinv, halt, hadj, hl, hr⟩ := GlobalTheory.T.adelicHermitianCharacterPairing_properties D hD cc δ hc ψ hψ N N'
  have hsd := GlobalTheory.T.completedStandardAdelicLattice_selfDual D hD cc δ hc ψ hψ N N'
  obtain ⟨hrat, -, hdense, hden, -, -⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D hD cc δ hc N N'
  have htt := GlobalTheory.T.weilOperator_rationalTranslate_mem_thetaFunctions D hD cc δ hc N N'
  let W₀ : Matrix (Fin N') (Fin N) D.host.E → TTs D (tor0 D cc δ) N N' →ₗ[ℂ] TTs D (tor0 D cc δ) N N' := fun z =>
    { toFun := fun F => ⟨Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F, htt z F F.2⟩
      map_add' := fun F G => Subtype.ext (wd_add _ _ _)
      map_smul' := fun c F => Subtype.ext (wd_smul _ _ _) }
  have hz1 : ∀ y : XA D N N', gamA ψ 0 y = 1 := fun y => by simp [gamA, hψ.2.1]
  have hz2 : ∀ y : XA D N N', gamA ψ y 0 = 1 := fun y => by simp [gamA, hψ.2.1]
  have hn1 : ∀ (m : ℕ) (x y : XA D N N'), gamA ψ (m • x) y = gamA ψ x y ^ m := fun m x y =>
    mul_nsmul_left (fun x => gamA ψ x y) (hz1 y) (fun a b => hl a b y) m x
  have hn2 : ∀ (m : ℕ) (x y : XA D N N'), gamA ψ x (m • y) = gamA ψ x y ^ m := fun m x y =>
    mul_nsmul_left (fun y => gamA ψ x y) (hz2 x) (fun a b => hr x a b) m y
  have hiso : ∀ a ∈ latA D cc N N', ∀ b ∈ latA D cc N N', gamA ψ (w • a) b = 1 := fun a ha b hb =>
    (hsd _).1 ((latA D cc N N').smul_mem w ha) b hb
  obtain ⟨WA, h1, h2, h3⟩ := GlobalTheory.FinWeil.exists_extension_of_dense (incM D N N') (latA D cc N N').toAddSubgroup
    (fun x y => gamA ψ (w • x) y) W₀
    (fun x y z => by simp only [smul_add, hl]) (fun x y z => hr _ _ _) hiso
    (fun x => by
      obtain ⟨m, hm, hx⟩ := hden x
      refine ⟨m, hm, fun a ha => ⟨?_, ?_⟩⟩
      · have := hiso _ hx a ha
        rw [smul_comm, hn1] at this
        simp only [hn2, this]
      · have := hiso a ha _ hx
        rw [hn2] at this
        show gamA ψ (w • m • a) x = 1
        rw [smul_comm, hn1, this])
    (fun x y v => by
      apply Subtype.ext
      have h := (hwd N N' x y).2.2 v
      have h' : gamA ψ (w • incM D N N' x) (incM D N N' y) =
          psi0 D cc δ (∑ i, ∑ j, (w : D.host.E) * x i j * D.host.conj (y i j)) := by
        rw [← hψ.2.2.1]
        simp only [gamA, incM_apply, Matrix.smul_apply, Matrix.map_apply, smul_AE, sgA_incE, map_sum, map_mul]
      show Wd D _ _ (Wd D _ _ _) = gamA ψ (w • incM D N N' x) (incM D N N' y) • Wd D _ _ _
      rw [h', h])
    (fun x m hm => hdense x m hm)
    (fun v => by
      obtain ⟨m, hm, hv⟩ := v.2.2
      refine ⟨m, hm, ?_⟩
      rintro z ⟨a, ha, hz⟩
      obtain ⟨z', rfl, rfl⟩ := exists_div D hm z a hz
      apply Subtype.ext
      show Wd D _ (pt D _ δ (m • z')) _ = _
      rw [pt_nsmul]
      exact hv _ ((hrat z').1 ha))
  refine ⟨w, gamA ψ, WA, ⟨fun r => ?_, hw, hl, hr, halt, hadj, fun v => ?_, h2⟩, hsd, hinv, fun z F => ?_, h3⟩
  · apply RingOfIntegers.ext
    rw [coe_sgO, coe_sgO, conjE_conjE]
  · have := h1 0
    rw [map_zero] at this
    rw [this]
    apply Subtype.ext
    show Wd D _ (pt D _ δ 0) _ = _
    rw [pt_zero, wd_at_zero]
  · rw [← incM_apply, h1]
    rfl

end GlobalTheory.FinWeil.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHermitianLogUnitaryBlockDiagonal
section
noncomputable section
namespace GlobalTheory.CartanInt.UnitLog
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator

theorem norm_entry_le {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (a b : n) :
    ‖A a b‖ ≤ ‖A‖ := by
  have h := A.l2_opNorm_mulVec (EuclideanSpace.single b (1 : ℂ))
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm (A *ᵥ (EuclideanSpace.single b (1 : ℂ)))) a
  simp only [EuclideanSpace.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ (h2.trans h)
  simp

theorem exists_log {n : Type} [Fintype n] [DecidableEq n] (u : Matrix n n ℂ)
    (hu : u ∈ unitary (Matrix n n ℂ)) :
    ∃ H : Matrix n n ℂ, Hᴴ = H ∧ ‖H‖ ≤ Real.pi ∧ u = NormedSpace.exp (Complex.I • H) ∧
      ∀ J, Commute u J → Commute (star u) J → Commute H J := by
  have hn : IsStarNormal u := isStarNormal_of_mem_unitary hu
  have hfin : (spectrum ℂ u).Finite := Matrix.finite_spectrum u
  have hsph : ∀ z ∈ spectrum ℂ u, ‖z‖ = 1 := fun z hz => by
    simpa using spectrum.subset_circle_of_unitary hu hz
  refine ⟨cfc (fun z : ℂ => (Complex.arg z : ℂ)) u, ?_, ?_, ?_, fun J h1 h2 => h1.cfc h2 _⟩
  · rw [← Matrix.star_eq_conjTranspose, ← cfc_star]
    refine cfc_congr fun z _ => ?_
    simp
  · refine norm_cfc_le Real.pi_pos.le fun z _ => ?_
    simpa using Complex.abs_arg_le_pi z
  · rw [← cfc_const_mul Complex.I _ u (hf := hfin.continuousOn _),
      ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← Complex.exp_eq_exp_ℂ,
      ← cfc_comp' Complex.exp _ u (hf := hfin.continuousOn _)]
    conv_lhs => rw [← cfc_id' ℂ u]
    refine cfc_congr fun z hz => ?_
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hsph z hz, mul_comm _ Complex.I] at this
    simpa using this.symm

theorem isKC_iff_commute {p q : ℕ} (X : Mat p q) : IsKC X ↔ Commute X (Formalism.UG.Jpq p q) := by
  constructor
  · intro h
    ext a b
    have h1 := h a b
    rcases a with i | i <;> rcases b with j | j <;>
      simp_all [sameBlock, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  · intro h a b hab
    have h1 := congrFun (congrFun h.eq a) b
    rcases a with i | i <;> rcases b with j | j <;>
      simp [sameBlock, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] at h1 hab ⊢
    · linear_combination (-1 / 2 : ℂ) * h1
    · linear_combination (1 / 2 : ℂ) * h1

theorem exists_unitlog : ∀ (p q : ℕ) (k : UpqT p q), k ∈ Kc p q → ∃ H : Mat p q, Hᴴ = H ∧ IsKC H ∧
    (∀ a b, ‖H a b‖ ≤ Real.pi) ∧ UpqT.mat k = NormedSpace.exp (Complex.I • H) := by
  intro p q k hk
  have hu : (UpqT.mat k : Mat p q) ∈ unitary (Mat p q) :=
    Matrix.mem_unitaryGroup_iff'.2 (star_mul_of_mem_Kc hk)
  obtain ⟨H, h1, h2, h3, h4⟩ := exists_log _ hu
  refine ⟨H, h1, (isKC_iff_commute H).2 (h4 _ ((isKC_iff_commute _).1 hk) ?_),
    fun a b => (norm_entry_le H a b).trans h2, h3⟩
  rw [Matrix.star_eq_conjTranspose, ← mat_inv_of_mem_Kc hk]
  exact (isKC_iff_commute _).1 ((Ksg p q).inv_mem hk)

end GlobalTheory.CartanInt.UnitLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsometricChartBlockHermitian
section
noncomputable section
namespace GlobalTheory.CartanInt.HermChart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

def herm {n : Type} (S : n → n → ℝ) : Matrix n n ℂ :=
  Matrix.of fun i j => (⟨(S i j + S j i) / 2, (S i j - S j i) / 2⟩ : ℂ)

theorem herm_apply {n : Type} (S : n → n → ℝ) (i j : n) :
    herm S i j = (⟨(S i j + S j i) / 2, (S i j - S j i) / 2⟩ : ℂ) := rfl

theorem herm_conjTranspose {n : Type} (S : n → n → ℝ) : (herm S)ᴴ = herm S := by
  ext i j
  rw [Matrix.conjTranspose_apply, herm_apply, herm_apply]
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re]; ring
  · simp only [Complex.star_def, Complex.conj_im]; ring

theorem continuous_herm_entry {X n : Type} [TopologicalSpace X] {f : X → n → n → ℝ}
    (hf : ∀ i j, Continuous fun x => f x i j) (i j : n) : Continuous fun x => herm (f x) i j := by
  have e : (fun x => herm (f x) i j) = fun x => (((f x i j + f x j i) / 2 : ℝ) : ℂ) +
      (((f x i j - f x j i) / 2 : ℝ) : ℂ) * Complex.I := by
    funext x
    rw [herm_apply, Complex.mk_eq_add_mul_I]
  rw [e]
  have h1 := hf i j
  have h2 := hf j i
  fun_prop

theorem sum_norm_sq_herm_sub {n : Type} [Fintype n] (S T : n → n → ℝ) :
    ∑ i, ∑ j, ‖herm S i j - herm T i j‖ ^ 2 = ∑ i, ∑ j, (S i j - T i j) ^ 2 := by
  have h : ∀ i j, ‖herm S i j - herm T i j‖ ^ 2 =
      (S i j - T i j) ^ 2 / 2 + (S j i - T j i) ^ 2 / 2 := by
    intro i j
    rw [Complex.sq_norm, Complex.normSq_apply, herm_apply, herm_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  simp only [h, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => (S j i - T j i) ^ 2 / 2), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem herm_re_add_im {n : Type} (H : n → n → ℂ) (hH : ∀ i j, star (H j i) = H i j) (i j : n) :
    herm (fun i j => (H i j).re + (H i j).im) i j = H i j := by
  have h1 := congrArg Complex.re (hH i j)
  have h2 := congrArg Complex.im (hH i j)
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im] at h1 h2
  rw [herm_apply]
  apply Complex.ext
  · show _ / (2 : ℝ) = _
    linarith
  · show _ / (2 : ℝ) = _
    linarith

theorem abs_re_add_im_le {z : ℂ} (hz : ‖z‖ ≤ Real.pi) : |z.re + z.im| ≤ 89 / 20 := by
  have h1 : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by rw [Complex.sq_norm, Complex.normSq_apply]
  have h2 : ‖z‖ ≤ 3.1416 := hz.trans Real.pi_lt_d4.le
  have h3 : ‖z‖ ^ 2 ≤ 3.1416 ^ 2 := pow_le_pow_left₀ (norm_nonneg z) h2 2
  refine abs_le_of_sq_le_sq' ?_ (by norm_num) |> abs_le.2
  nlinarith [sq_nonneg (z.re - z.im)]

theorem exists_chart : ∀ (p q : ℕ), ∃ Φ : ((Fin p × Fin p) ⊕ (Fin q × Fin q) → ℝ) → Mat p q,
    Continuous Φ ∧ (∀ R, (Φ R)ᴴ = Φ R ∧ IsKC (Φ R)) ∧
    (∀ R R', ∑ a, ∑ b, ‖(Φ R - Φ R') a b‖ ^ 2 = ∑ i, (R i - R' i) ^ 2) ∧
    ∀ H : Mat p q, Hᴴ = H → IsKC H → (∀ a b, ‖H a b‖ ≤ Real.pi) →
      ∃ R, Φ R = H ∧ ∀ i, |R i| ≤ 89 / 20 := by
  intro p q
  refine ⟨fun R => Matrix.fromBlocks (herm fun i j => R (Sum.inl (i, j))) 0 0
    (herm fun i j => R (Sum.inr (i, j))), ?_, fun R => ⟨?_, isKC_fromBlocks _ _⟩, fun R R' => ?_,
    fun H hH hK hb => ?_⟩
  · refine continuous_matrix fun a b => ?_
    rcases a with a | a <;> rcases b with b | b
    · exact continuous_herm_entry (f := fun (R : (Fin p × Fin p) ⊕ (Fin q × Fin q) → ℝ) i j =>
        R (Sum.inl (i, j))) (fun i j => continuous_apply _) a b
    · exact continuous_const
    · exact continuous_const
    · exact continuous_herm_entry (f := fun (R : (Fin p × Fin p) ⊕ (Fin q × Fin q) → ℝ) i j =>
        R (Sum.inr (i, j))) (fun i j => continuous_apply _) a b
  · simp only [Matrix.fromBlocks_conjTranspose, herm_conjTranspose, Matrix.conjTranspose_zero]
  · rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type,
      ← sum_norm_sq_herm_sub (fun i j => R (Sum.inl (i, j))) (fun i j => R' (Sum.inl (i, j))),
      ← sum_norm_sq_herm_sub (fun i j => R (Sum.inr (i, j))) (fun i j => R' (Sum.inr (i, j)))]
    simp [Fintype.sum_sum_type]
  · have hs : ∀ a b, star (H b a) = H a b := fun a b => by
      rw [← Matrix.conjTranspose_apply, hH]
    refine ⟨Sum.elim (fun x => (H (Sum.inl x.1) (Sum.inl x.2)).re + (H (Sum.inl x.1) (Sum.inl x.2)).im)
      (fun x => (H (Sum.inr x.1) (Sum.inr x.2)).re + (H (Sum.inr x.1) (Sum.inr x.2)).im), ?_, ?_⟩
    · ext a b
      rcases a with a | a <;> rcases b with b | b
      · exact herm_re_add_im (fun i j => H (Sum.inl i) (Sum.inl j)) (fun i j => hs _ _) a b
      · exact (hK _ _ (by simp [sameBlock])).symm
      · exact (hK _ _ (by simp [sameBlock])).symm
      · exact herm_re_add_im (fun i j => H (Sum.inr i) (Sum.inr j)) (fun i j => hs _ _) a b
    · rintro (x | x)
      · exact abs_re_add_im_le (hb _ _)
      · exact abs_re_add_im_le (hb _ _)

end GlobalTheory.CartanInt.HermChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpLogNearOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
open Filter Topology

namespace GlobalTheory.CartanInt.ExpLocal

attribute [local instance] GlobalTheory.CompactDualExists.sumNormedAddCommGroup
  GlobalTheory.CompactDualExists.sumNormedSpace

theorem l1_eq_norm {n : Type} [Fintype n] (A : Matrix n n ℂ) : l1 A = ‖A‖ :=
  (GlobalTheory.CompactDualExists.sum_norm_def A).symm

theorem exists_exp_approx (n : Type) [Fintype n] [DecidableEq n] :
    ∃ r : ℝ, 0 < r ∧ ∀ Y : Matrix n n ℂ, ‖Y‖ < r →
      ‖NormedSpace.exp Y - 1 - Y‖ ≤ 1 / 21 * ‖Y‖ := by
  have h := (GlobalTheory.CompactDualExists.exp_strict (n := n)).hasFDerivAt
  have h2 := h.isLittleO.def (c := 1 / 21) (by norm_num)
  obtain ⟨r, hr, H⟩ := Metric.eventually_nhds_iff_ball.1 h2
  refine ⟨r, hr, fun Y hY => ?_⟩
  have h3 := H Y (mem_ball_zero_iff.2 hY)
  rw [NormedSpace.exp_zero, sub_zero] at h3
  exact h3

theorem exp_log_near_one : ∀ (p q : ℕ), ∃ ρ : ℝ, 0 < ρ ∧ (∀ Y : Mat p q, l1 Y < ρ → l1 (NormedSpace.exp Y - 1) ≤ 21 / 20 * l1 Y) ∧ ∀ g : UpqT p q, l1 (UpqT.mat g - 1) < ρ → ∃ X : lieU p q, UpqT.mat g = NormedSpace.exp (X : Mat p q) ∧ l1 (X : Mat p q) ≤ 21 / 20 * l1 (UpqT.mat g - 1) := by
  intro p q
  obtain ⟨r, hr, H⟩ := exists_exp_approx (Fin p ⊕ Fin q)
  have hN := GlobalTheory.ExpBallNhds.exp_ballU_mem_nhds p q r hr
  rw [GlobalTheory.UpqTopology.isInducing_mat.nhds_eq_comap, Filter.mem_comap] at hN
  obtain ⟨T, hT, hsub⟩ := hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hT
  refine ⟨min r ε, lt_min hr hε, fun Y hY => ?_, fun g hg => ?_⟩
  · rw [l1_eq_norm] at hY
    rw [l1_eq_norm, l1_eq_norm]
    have h1 := H Y (hY.trans_le (min_le_left _ _))
    have h2 := norm_le_norm_add_norm_sub' (NormedSpace.exp Y - 1) Y
    have h3 := norm_nonneg Y
    linarith
  · rw [l1_eq_norm] at hg
    have hg' : UpqT.mat g ∈ Metric.ball (UpqT.mat (1 : UpqT p q)) ε := by
      rw [mem_ball_iff_norm, mat_one]
      exact hg.trans_le (min_le_right _ _)
    obtain ⟨X, hX, hgX⟩ := hsub (show g ∈ UpqT.mat ⁻¹' T from hball hg')
    refine ⟨X, hgX, ?_⟩
    have hX' : l1 (X : Mat p q) < r := hX
    rw [l1_eq_norm] at hX'
    rw [l1_eq_norm, l1_eq_norm, hgX]
    have h1 := H X hX'
    have h2 := norm_le_norm_add_norm_sub (NormedSpace.exp (X : Mat p q) - 1) (X : Mat p q)
    linarith

end GlobalTheory.CartanInt.ExpLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrameEmbeddingUniqueFixedStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_module_sign_eq_neg_one_pow_length : ∀ (D : D7) (M : Type) [AddCommGroup M] [Module (𝓞 D.host.E) M] [Finite M], Ev D (Nat.card M) ∧ ((∀ q : ℕ, q.Prime → q ∣ Nat.card M → InertQ D q) → sgn D (Nat.card M) = (-1 : ℂ) ^ (Module.length (𝓞 D.host.E) M).toNat) := by
  first | exact @GlobalTheory.InertParity.FiniteOrder.ev_card_and_sgn_card | exact GlobalTheory.InertParity.FiniteOrder.ev_card_and_sgn_card | (intros; apply GlobalTheory.InertParity.FiniteOrder.ev_card_and_sgn_card <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsogenyFibresEvenThetaSigmaStarSquareQuotientStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_fibres_even_theta_sigmaStarSquareQuotient : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (β t₀ : ℂ) (k : ℕ), (∀ ω ∈ Λ, β * ω ∈ Λ) → β + starRingEnd ℂ β = 1 → β * starRingEnd ℂ β = ((2 * k : ℕ) : ℂ) → 2 * t₀ ∈ Λ → β * t₀ ∉ Λ → (1 - β) * t₀ ∉ Λ → ∃ (Q : Fin k → ℂ) (Q' : Fin (2 * k) → ℂ), (∀ i, Q i ∉ Λ ∧ InRationalLattice Λ (Q i)) ∧ (∀ j, Q' j ∉ Λ ∧ InRationalLattice Λ (Q' j)) ∧ (∀ z, GL3Theta.th0 Λ t₀ (β * z) = ∏ i, sqTh Λ (Q i) z) ∧ (∀ z, sqTh Λ (β * t₀) (β * z) = ∏ j, sqTh Λ (Q' j) z) ∧ (∀ i j, wpF Λ (Q i) ≠ wpF Λ (Q' j)) ∧ (∃ j, wpF Λ (Q' j) = wpF Λ t₀) ∧ (∃ j, wpF Λ (Q' j) = wpF Λ (β * t₀)) ∧ wpF Λ t₀ ≠ wpF Λ (β * t₀) := by
  first | exact @GlobalTheory.EvenTheta.Fibres.isogeny_fibres | exact GlobalTheory.EvenTheta.Fibres.isogeny_fibres | (intros; apply GlobalTheory.EvenTheta.Fibres.isogeny_fibres <;> assumption)
end

