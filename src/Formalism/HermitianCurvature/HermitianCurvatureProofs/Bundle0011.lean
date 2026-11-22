import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0008
import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0005
import Formalism.RealPlaceAnalysis.Bundle0003
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.GroupTheory.Perm.Support
import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BasePointMemHalfPlane
section
open Set Filter Topology Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

def An (TT : ℝ) : Set ℂ := {ζ | TT < Complex.normSq ζ}

theorem isOpen_An (TT : ℝ) : IsOpen (An TT) :=
  isOpen_lt continuous_const Complex.continuous_normSq

theorem exp_mem_An {w : ℂ} (hw : w ∈ Hh TT) : Complex.exp w ∈ An TT := by
  exact hw

theorem hasFDerivAt_exp_real (w : ℂ) :
    HasFDerivAt Complex.exp ((ContinuousLinearMap.mul ℝ ℂ) (Complex.exp w)) w := by
  have h : HasFDerivAt Complex.exp
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (Complex.exp w)).restrictScalars ℝ) w :=
    (Complex.hasDerivAt_exp w).hasFDerivAt.restrictScalars ℝ
  convert h using 1
  refine ContinuousLinearMap.ext fun v => ?_
  simp [mul_comm]

theorem hasFDerivAt_bet (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) {w : ℂ} (hw : w ∈ Hh TT) :
    HasFDerivAt (bet α)
      (α (Complex.exp w) • (ContinuousLinearMap.mul ℝ ℂ) (Complex.exp w) +
        Complex.exp w • (fderiv ℝ α (Complex.exp w)).comp ((ContinuousLinearMap.mul ℝ ℂ) (Complex.exp w))) w := by
  have he := hasFDerivAt_exp_real w
  have hmem : Complex.exp w ∈ An TT := exp_mem_An hw
  have hdα : DifferentiableAt ℝ α (Complex.exp w) :=
    (hα.contDiffAt ((isOpen_An TT).mem_nhds hmem)).differentiableAt
      (by first | simp | exact le_top)
  have hc : HasFDerivAt (fun z => α (Complex.exp z))
      ((fderiv ℝ α (Complex.exp w)).comp ((ContinuousLinearMap.mul ℝ ℂ) (Complex.exp w))) w :=
    hdα.hasFDerivAt.comp w he
  exact hc.mul he

theorem fderiv_bet_apply (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) {w : ℂ} (hw : w ∈ Hh TT) (v : ℂ) :
    fderiv ℝ (bet α) w v = (α (Complex.exp w) * Complex.exp w + wZ α (Complex.exp w) * Complex.exp w ^ 2) * v +
      wZb α (Complex.exp w) * Complex.exp w * (starRingEnd ℂ) (Complex.exp w) * (starRingEnd ℂ) v := by
  rw [(hasFDerivAt_bet hα hw).fderiv]
  unfold wZ wZb
  obtain ⟨L, hL⟩ : ∃ L, L = fderiv ℝ α (Complex.exp w) := ⟨_, rfl⟩
  rw [← hL]
  have hL' : ∀ u : ℂ, 2 * L u = (u + (starRingEnd ℂ) u) * L 1 + Complex.I * ((starRingEnd ℂ) u - u) * L Complex.I := by
    intro u
    have hre : L u = (u.re : ℂ) * L 1 + (u.im : ℂ) * L Complex.I := by
      have hu : u.re • (1 : ℂ) + u.im • Complex.I = u := by
        rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
      conv_lhs => rw [← hu]
      rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    have h1 := Complex.add_conj u
    have h2 := Complex.sub_conj u
    push_cast at h1 h2
    rw [hre]
    linear_combination (-(L 1)) * h1 + (Complex.I * L Complex.I) * h2 +
      (2 * (u.im : ℂ) * L Complex.I) * Complex.I_sq
  have key := hL' (Complex.exp w * v)
  have hcj : (starRingEnd ℂ) (Complex.exp w * v) = (starRingEnd ℂ) (Complex.exp w) * (starRingEnd ℂ) v :=
    map_mul (starRingEnd ℂ) _ _
  rw [hcj] at key
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', smul_eq_mul]
  linear_combination (Complex.exp w / 2) * key

theorem sym_alg (A b ζ h k : ℂ) (hb : b.re = 0) :
    ((A * h + b * ζ * (starRingEnd ℂ) ζ * (starRingEnd ℂ) h) * k).im =
      ((A * k + b * ζ * (starRingEnd ℂ) ζ * (starRingEnd ℂ) k) * h).im := by
  simp only [Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re, Complex.conj_re,
    Complex.conj_im, hb]
  ring

theorem contDiffOn_bet (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bet α) (Hh TT) := by
  have he : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Complex.exp (Hh TT) :=
    Complex.contDiff_exp.contDiffOn
  exact (hα.comp he (fun w hw => exp_mem_An hw)).mul he

theorem contDiffOn_om (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (om α) (Hh TT) :=
  omL.contDiff.comp_contDiffOn (contDiffOn_bet hα)

theorem fderiv_om_apply (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) {w : ℂ} (hw : w ∈ Hh TT) (h k : ℂ) :
    fderiv ℝ (om α) w h k = 2 * (fderiv ℝ (bet α) w h * k).im := by
  have hb := hasFDerivAt_bet hα hw
  have hom : HasFDerivAt (om α) (omL.comp (fderiv ℝ (bet α) w)) w :=
    omL.hasFDerivAt.comp w hb.differentiableAt.hasFDerivAt
  rw [hom.fderiv]
  simp [omL, two_smul, two_mul]

theorem om_sym (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) :
    ∀ p ∈ Hh TT, ∀ h k : ℂ, fderiv ℝ (om α) p h k = fderiv ℝ (om α) p k h := by
  intro p hp h k
  rw [fderiv_om_apply hα hp, fderiv_om_apply hα hp, fderiv_bet_apply hα hp, fderiv_bet_apply hα hp,
    sym_alg _ _ _ h k (hcurv _ (exp_mem_An hp))]

def x0 (TT : ℝ) : ℂ := (Real.log (TT + 1) : ℂ)

theorem base_point_mem_half_plane (hTT : 0 ≤ TT) : x0 TT ∈ Hh TT := by
  show TT < Complex.normSq (Complex.exp (x0 TT))
  unfold x0
  rw [← Complex.ofReal_exp, Complex.normSq_ofReal, Real.exp_log (by linarith)]
  nlinarith

def th (TT : ℝ) (α : ℂ → ℂ) (w : ℂ) : ℝ := prim (om α) (x0 TT) w

theorem hasFDerivAt_th (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) {w : ℂ} (hw : w ∈ Hh TT) :
    HasFDerivAt (th TT α) (om α w) w :=
  hasFDerivAt_prim (isOpen_Hh TT) (convex_Hh TT) (base_point_mem_half_plane hTT) ((contDiffOn_om hα).of_le (by simp))
    (om_sym hα hcurv) hw

theorem contDiffOn_th (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (th TT α) (Hh TT) := by
  have hHo : IsOpen (Hh TT) :=
    isOpen_lt continuous_const (Complex.continuous_normSq.comp Complex.continuous_exp)
  rw [contDiffOn_infty_iff_fderiv_of_isOpen hHo]
  refine ⟨fun y hy => (hasFDerivAt_th hTT hα hcurv hy).differentiableAt.differentiableWithinAt, ?_⟩
  exact (contDiffOn_om hα).congr (fun y hy => (hasFDerivAt_th hTT hα hcurv hy).fderiv)

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.Block32EqZeroOfUnipotent
section
namespace Formalism.FourierDecayAlt.P.S3x9

open Matrix Finset
open Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni upUniG)

def revRows (A : Type) (r : ℕ) : Matrix (Fin r) (Fin r) A ≃ Matrix (Fin r) (Fin r) A where
  toFun X := X.submatrix Fin.rev id
  invFun X := X.submatrix Fin.rev id
  left_inv X := by ext i j; simp
  right_inv X := by ext i j; simp

theorem cornerCount (K : Type) [Field K] [Fintype K] (r : ℕ) :
    Nat.card {X : Matrix (Fin r) (Fin r) K // ∀ (l : ℕ) (hl : l ≤ r), cm X l hl ≠ 0} =
      Fintype.card K ^ (r ^ 2 - r) * (Fintype.card K - 1) ^ r := by
  rw [← Formalism.FourierDecayAlt.P.leading_minors_count K r]
  exact Nat.card_congr ((revRows K r).subtypeEquiv fun X => Iff.rfl)

theorem block31_add {A : Type} [CommRing A] {r k : ℕ} (x y : Matrix (Idx r k) (Idx r k) A) :
    b31 (x + y) = b31 x + b31 y := rfl

theorem block31_sub {A : Type} [CommRing A] {r k : ℕ} (x y : Matrix (Idx r k) (Idx r k) A) :
    b31 (x - y) = b31 x - b31 y := rfl

theorem block31_smul {A : Type} [CommRing A] {r k : ℕ} (c : A) (x : Matrix (Idx r k) (Idx r k) A) :
    b31 (c • x) = c • b31 x := rfl

theorem block31_mul {A : Type} [CommRing A] {r k : ℕ} (x y : Matrix (Idx r k) (Idx r k) A) :
    b31 (x * y) = b31 x * b11 y + b32 x * b21 y + b33 x * b31 y := by
  ext a b
  simp [b31, b11, b32, b21, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block32_mul {A : Type} [CommRing A] {r k : ℕ} (x y : Matrix (Idx r k) (Idx r k) A) :
    b32 (x * y) = b31 x * b12 y + b32 x * b22 y + b33 x * b32 y := by
  ext a b
  simp [b31, b12, b32, b22, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]

theorem block32_levi_embedding {A : Type} [CommRing A] {r k : ℕ} (h : Matrix (Fin k) (Fin k) A) :
    b32 (hEmb r h) = 0 := by
  ext a b
  simp [b32, hEmb]

theorem block32_eq_zero_of_unipotent {A : Type} [CommRing A] {r k : ℕ} {x : Matrix (Idx r k) (Idx r k) A}
    (hx : IsNU x) : b32 x = 0 := by
  obtain ⟨n, u, hn, ⟨u', -, rfl⟩, rfl⟩ := hx
  obtain ⟨-, -, -, -, h31, h32⟩ := hn
  rw [block32_mul, h31, h32, block32_levi_embedding]
  simp

theorem block32_map {A B : Type} {r k : ℕ} (f : A → B) (x : Matrix (Idx r k) (Idx r k) A) :
    b32 (x.map f) = (b32 x).map f := rfl

def lowerLeftBlockMatrix {A : Type} [Zero A] (r k : ℕ) (Y : Matrix (Fin r) (Fin r) A) : Matrix (Idx r k) (Idx r k) A :=
  Matrix.of fun i j =>
    match i, j with
    | Sum.inr (Sum.inr a), Sum.inl b => Y a b
    | _, _ => 0

theorem block31_lowerLeftBlockMatrix {A : Type} [Zero A] (r k : ℕ) (Y : Matrix (Fin r) (Fin r) A) :
    b31 (lowerLeftBlockMatrix r k Y) = Y := rfl

def splitEquiv (A : Type) [CommRing A] (r k : ℕ) (P : Matrix (Fin r) (Fin r) A → Prop) :
    {M : Matrix (Idx r k) (Idx r k) A // P (b31 M)} ≃
      {Y : Matrix (Fin r) (Fin r) A // P Y} × {Z : Matrix (Idx r k) (Idx r k) A // b31 Z = 0} where
  toFun M := (⟨b31 M.1, M.2⟩, ⟨M.1 - lowerLeftBlockMatrix r k (b31 M.1), by rw [block31_sub, block31_lowerLeftBlockMatrix, sub_self]⟩)
  invFun p := ⟨p.2.1 + lowerLeftBlockMatrix r k p.1.1, by
    rw [block31_add, block31_lowerLeftBlockMatrix, p.2.2, zero_add]; exact p.1.2⟩
  left_inv M := by
    apply Subtype.ext
    simp
  right_inv p := by
    obtain ⟨⟨Y, hY⟩, ⟨Z, hZ⟩⟩ := p
    have h : b31 (Z + lowerLeftBlockMatrix r k Y) = Y := by rw [block31_add, block31_lowerLeftBlockMatrix, hZ, zero_add]
    apply Prod.ext
    · exact Subtype.ext h
    · apply Subtype.ext
      simp [h]

noncomputable def affEquiv {A : Type} [CommRing A] {r : ℕ} (X₀ u : Matrix (Fin r) (Fin r) A)
    (hu : IsUnit u.det) : Matrix (Fin r) (Fin r) A ≃ Matrix (Fin r) (Fin r) A where
  toFun Y := X₀ + u * Y
  invFun X := u⁻¹ * (X - X₀)
  left_inv Y := by
    simp only [add_sub_cancel_left]
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul u hu, Matrix.one_mul]
  right_inv X := by
    simp only
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv u hu, Matrix.one_mul, add_sub_cancel]

end Formalism.FourierDecayAlt.P.S3x9

open Formalism.FourierDecayAlt.P.S3x9 Formalism.FourierDecayAlt.S3 Matrix in
theorem Formalism.FourierDecayAlt.P.cornerMinorsCount_true : Formalism.FourierDecayAlt.S3.CornerMinorsCount :=
  fun K _ _ r => cornerCount K r

open Formalism.FourierDecayAlt.P.S3x9 Formalism.FourierDecayAlt.S3 Matrix in
theorem Formalism.FourierDecayAlt.P.unit_stratum_coset : Formalism.FourierDecayAlt.S3.UnitStratumCoset := by
  intro o _ _ _ ϖ hϖ r k j₀ M X₀ hj h31
  have hres : IsLocalRing.residue o ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hϖ.not_isUnit
  have h32 : (b32 j₀).map (IsLocalRing.residue o) = 0 := by
    rw [← block32_map]; exact block32_eq_zero_of_unipotent hj.2
  refine ⟨X₀ + b31 (j₀ * M), ?_, ?_⟩
  · rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, block31_add, block31_smul, h31, smul_add]
  · rw [block31_mul, h31]
    have e : ∀ a b : Matrix (Fin r) (Fin r) o,
        (a + b).map (IsLocalRing.residue o) = a.map (IsLocalRing.residue o) + b.map (IsLocalRing.residue o) :=
      fun a b => Matrix.map_add (IsLocalRing.residue o) (map_add _) a b
    have z1 : ((ϖ • X₀) * b11 M).map (IsLocalRing.residue o) = 0 := by
      rw [Matrix.smul_mul]
      ext a b
      simp [hres]
    have z2 : (b32 j₀ * b21 M).map (IsLocalRing.residue o) = 0 := by
      rw [Matrix.map_mul, h32, Matrix.zero_mul]
    rw [e, e, e, e, z1, z2]
    simp

open Formalism.FourierDecayAlt.P.S3x9 Formalism.FourierDecayAlt.S3 Matrix in
theorem Formalism.FourierDecayAlt.P.unit_stratum_share : Formalism.FourierDecayAlt.S3.UnitStratumShare := by
  intro K _ _ r k X₀ u hu
  classical
  set q := Fintype.card K with hq
  have hq1 : 1 ≤ q := Fintype.card_pos
  set κ := Nat.card {Z : Matrix (Idx r k) (Idx r k) K // b31 Z = 0} with hκ
  have c1 : Nat.card {M : Matrix (Idx r k) (Idx r k) K //
        ∀ (l : ℕ) (hl : l ≤ r), cm (X₀ + u * b31 M) l hl ≠ 0} =
      (q ^ (r ^ 2 - r) * (q - 1) ^ r) * κ := by
    rw [Nat.card_congr (splitEquiv K r k
      (fun Y => ∀ (l : ℕ) (hl : l ≤ r), cm (X₀ + u * Y) l hl ≠ 0)), Nat.card_prod,
      ← cornerCount K r]
    congr 1
    exact Nat.card_congr ((affEquiv X₀ u hu).subtypeEquiv fun Y => Iff.rfl)
  have c2 : Nat.card (Matrix (Idx r k) (Idx r k) K) = q ^ (r ^ 2) * κ := by
    have h0 : Nat.card (Matrix (Idx r k) (Idx r k) K) =
        Nat.card {M : Matrix (Idx r k) (Idx r k) K // (fun _ => True) (b31 M)} :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial).symm
    rw [h0, Nat.card_congr (splitEquiv K r k (fun _ => True)), Nat.card_prod,
      Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)]
    congr 1
    show Nat.card (Fin r → Fin r → K) = _
    simp [← pow_mul, sq, hq]
  rw [c1, c2]
  have hr : r ^ 2 = (r ^ 2 - r) + r := by
    have : r ≤ r ^ 2 := by nlinarith [Nat.zero_le r]
    omega
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  push_cast [Nat.cast_sub hq1]
  conv_rhs => rw [hr, pow_add]
  have : (1 - 1 / (q : ℝ)) ^ r * (q : ℝ) ^ r = ((q : ℝ) - 1) ^ r := by
    rw [← mul_pow]; congr 1; field_simp
  calc (q : ℝ) ^ (r ^ 2 - r) * ((q : ℝ) - 1) ^ r * κ
      = (q : ℝ) ^ (r ^ 2 - r) * ((1 - 1 / (q : ℝ)) ^ r * (q : ℝ) ^ r) * κ := by rw [this]
    _ = _ := by ring

theorem Formalism.FourierDecayAlt.P.unit_stratum_mass : Formalism.FourierDecayAlt.S3.UnitStratumMass := by
  intro volNo volJH volKpp volOm cUk c J h1 h2 h3 h4 hc hJ
  subst hc; subst hJ
  refine ⟨?_, ?_, ?_⟩ <;> field_simp
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRTopActAlg
section
open Polynomial Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

open Formalism.REAL

def QTopAlg : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) (h : ℂ),
    ∃ d : ℕ → A, (∀ Y : ℂ, qminor E id id (Y + h) = ∑ j ∈ Finset.range (n + 1), Y ^ j • d j) ∧
      (1 ≤ n → d (n - 1) = ∑ a, E a a + algebraMap ℂ A ((n : ℂ) * h - (n : ℂ) * ((n : ℂ) - 1) / 2))

namespace TopAlg

variable {A : Type*} [Ring A] [Algebra ℂ A]

def fac (lin : Prop) [Decidable lin] (B : A) : A[X] := (if lin then X else 0) + C B

theorem natDegree_fac (lin : Prop) [Decidable lin] (B : A) :
    (fac lin B).natDegree ≤ if lin then 1 else 0 := by
  unfold fac
  split_ifs
  · exact (natDegree_add_le _ _).trans (by simp [natDegree_X_le])
  · simp

def prodP {m : ℕ} (lin : Fin m → Prop) [DecidablePred lin] (B : Fin m → A) : A[X] :=
  (List.ofFn fun l => fac (lin l) (B l)).prod

theorem natDegree_prodP : ∀ {m : ℕ} (lin : Fin m → Prop) [DecidablePred lin] (B : Fin m → A),
    (prodP lin B).natDegree ≤ ∑ l, (if lin l then 1 else 0)
  | 0, lin, _, B => by simp [prodP]
  | m + 1, lin, _, B => by
    unfold prodP
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    refine (natDegree_mul_le).trans (add_le_add (natDegree_fac _ _) ?_)
    exact natDegree_prodP (fun l => lin l.succ) (fun l => B l.succ)

theorem eval_prodP {m : ℕ} (lin : Fin m → Prop) [DecidablePred lin] (B : Fin m → A) (Y : ℂ) :
    eval₂ (RingHom.id A) (algebraMap ℂ A Y) (prodP lin B) =
      (List.ofFn fun l => (if lin l then algebraMap ℂ A Y else 0) + B l).prod := by
  unfold prodP
  rw [eval₂_list_prod_noncomm]
  · rw [List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun l => ?_))
    simp only [Function.comp, fac, eval₂_add, eval₂_C, RingHom.id_apply]
    split_ifs <;> simp
  · intro p _ k
    exact (Algebra.commutes Y _).symm

theorem coeff_all : ∀ {m : ℕ} (B : Fin m → A),
    (List.ofFn fun l => (X + C (B l) : A[X])).prod.coeff m = 1 ∧
      (1 ≤ m → (List.ofFn fun l => (X + C (B l) : A[X])).prod.coeff (m - 1) = ∑ l, B l)
  | 0, B => by simp
  | m + 1, B => by
    have ih := coeff_all (fun l : Fin m => B l.succ)
    have hdeg : (List.ofFn fun l : Fin m => (X + C (B l.succ) : A[X])).prod.natDegree ≤ m := by
      have := natDegree_prodP (fun _ : Fin m => True) (fun l => B l.succ)
      simp only [if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
      simpa [prodP, fac] using this
    rw [List.ofFn_succ, List.prod_cons]
    set Q := (List.ofFn fun l : Fin m => (X + C (B l.succ) : A[X])).prod with hQ
    refine ⟨?_, fun _ => ?_⟩
    · rw [add_mul, coeff_add, coeff_X_mul, ih.1, coeff_C_mul,
        coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < m + 1), mul_zero, add_zero]
    · rw [Fin.sum_univ_succ, add_mul, coeff_add, coeff_C_mul, Nat.add_sub_cancel, ih.1, mul_one]
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        simp
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        rw [coeff_X_mul, add_comm]
        congr 1
        have := ih.2 (by omega)
        simpa using this

end TopAlg

open TopAlg in
theorem quadratic_top_algebra_holds : QTopAlg := by
  intro A _ _ n E h
  classical

  let lin : Equiv.Perm (Fin n) → Fin n → Prop := fun σ l => σ l = l
  let B : Equiv.Perm (Fin n) → Fin n → A := fun σ l =>
    (if σ l = l then algebraMap ℂ A (h - ((l : ℕ) : ℂ)) else 0) + E (σ l) l
  let Pσ : Equiv.Perm (Fin n) → A[X] := fun σ => prodP (lin σ) (B σ)
  refine ⟨fun j => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : A) * (Pσ σ).coeff j, fun Y => ?_, fun hn => ?_⟩
  ·
    have hfac : ∀ σ : Equiv.Perm (Fin n),
        (List.ofFn fun k : Fin n => Tm E (Y + h - (k : ℂ)) (id (σ k)) (id k)).prod =
          ∑ j ∈ Finset.range (n + 1), Y ^ j • (Pσ σ).coeff j := by
      intro σ
      have e1 : (List.ofFn fun k : Fin n => Tm E (Y + h - (k : ℂ)) (id (σ k)) (id k)) =
          List.ofFn fun l => (if lin σ l then algebraMap ℂ A Y else 0) + B σ l := by
        congr 1
        funext l
        simp only [Tm, id, lin, B]
        split_ifs with hl
        · have : Y + h - ((l : ℕ) : ℂ) = Y + (h - ((l : ℕ) : ℂ)) := by ring
          rw [this, map_add]
          abel
        · simp
      rw [e1, ← eval_prodP]
      have hdeg : (Pσ σ).natDegree < n + 1 := by
        have := natDegree_prodP (lin σ) (B σ)
        have h2 : ∑ l : Fin n, (if lin σ l then 1 else 0) ≤ n := by
          calc ∑ l : Fin n, (if lin σ l then 1 else 0) ≤ ∑ _l : Fin n, 1 :=
                Finset.sum_le_sum fun l _ => by split_ifs <;> simp
            _ = n := by simp
        show (prodP (lin σ) (B σ)).natDegree < n + 1
        omega
      rw [eval₂_eq_sum_range' (RingHom.id A) hdeg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [RingHom.id_apply, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def]
    unfold qminor
    simp_rw [hfac, Finset.mul_sum, mul_smul_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.smul_sum]
  ·
    dsimp only
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul]
      have e1 : Pσ 1 = (List.ofFn fun l => (X + C (B 1 l) : A[X])).prod := by
        show prodP (lin 1) (B 1) = _
        unfold prodP fac
        congr 1
        congr 1
        funext l
        rw [if_pos (show lin 1 l from rfl)]
      rw [e1, (coeff_all (B 1)).2 hn]
      simp only [B, Equiv.Perm.one_apply, if_true]
      rw [Finset.sum_add_distrib, add_comm, ← map_sum]
      congr 1
      congr 1
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hs : ∑ l : Fin n, ((l : ℕ) : ℂ) = (n : ℂ) * ((n : ℂ) - 1) / 2 := by
        rw [Fin.sum_univ_eq_sum_range (fun l => ((l : ℕ) : ℂ)) n]
        have := Finset.sum_range_id_mul_two n
        have hc : ((∑ i ∈ Finset.range n, i : ℕ) : ℂ) * 2 = (n : ℂ) * ((n : ℂ) - 1) := by
          rw [← Nat.cast_ofNat, ← Nat.cast_mul, this]
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · subst h0; simp
          · rw [Nat.cast_mul, Nat.cast_sub (by omega)]
            simp
        push_cast at hc
        linear_combination hc / 2
      rw [hs]
    · intro σ _ hσ
      have h2 : 2 ≤ σ.support.card := Equiv.Perm.two_le_card_support_of_ne_one hσ
      have hdeg := natDegree_prodP (lin σ) (B σ)
      have hcount : ∑ l : Fin n, (if lin σ l then 1 else 0) + σ.support.card = n := by
        have hsupp : σ.support.card = ∑ l : Fin n, (if ¬ lin σ l then 1 else 0) := by
          rw [Finset.sum_boole, Nat.cast_id]
          rfl
        rw [hsupp, ← Finset.sum_add_distrib]
        calc ∑ l : Fin n, ((if lin σ l then 1 else 0) + (if ¬lin σ l then 1 else 0)) = ∑ _l : Fin n, 1 :=
              Finset.sum_congr rfl fun l _ => by split_ifs <;> simp_all
          _ = n := by simp
      have : (Pσ σ).coeff (n - 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (by show (prodP (lin σ) (B σ)).natDegree < n - 1; omega)
      rw [this, mul_zero]
    · intro h1
      exact absurd (Finset.mem_univ _) h1

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GermExpansionOfSteps
section
noncomputable section

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology

namespace Formalism.FourierDecayAlt.P

theorem germExpansionOfSteps : Formalism.FourierDecayAlt.A6.GermAssemble := by
  intro hHead hPhi K _ _ _ R ψ hD hn m hm γ hγ h Q hQ hQu
  obtain ⟨L₀, Λ₀, hL₀, hΛ₀, hΦ⟩ := hHead K R ψ hD hn m h Q hQ hQu
  obtain ⟨V, hV, hG⟩ := hPhi K R ψ hD hn m hm γ hγ L₀ Λ₀ Q hL₀ hΛ₀ hQ hQu
  refine ⟨V, hV, fun t c ht hc n' Z' => ?_⟩
  obtain ⟨Φ, hyp, h1, h2⟩ := hΦ n' Z'
  rw [h1 t c, hG Φ hyp t c ht hc]
  congr 1
  funext z
  exact (h2 z).symm

end Formalism.FourierDecayAlt.P
end
end

