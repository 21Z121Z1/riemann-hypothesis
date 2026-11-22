import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0033
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0087
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.Expand
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0088

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtInvpow
section
open Matrix MvPolynomial
open scoped ComplexConjugate ContDiff Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.MinorPolynomials

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

private lemma exists_zhat_eq_eval_poly_deg_le_one (z z' : Fin (2 * r + k + 1) → ℂ) :
    ∃ P : Fin (r + 1) → Fin (r + 1) → MvPolynomial (Vr (2 * r + k + 1)) ℂ,
      (∀ a b, (P a b).totalDegree ≤ 1) ∧
        ∀ (g : Mat k r) a b, eval (vars g) (P a b) = Zhat k r z z' g a b := by
  refine ⟨fun a b => ∑ i, ∑ j, C (((Fm k r z)ᴴ * Hpk k r) a i * Fm k r z' j b) *
    MvPolynomial.X (Sum.inl (i, j)), ?_, ?_⟩
  · intro a b
    refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
    refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun j _ => ?_)
    exact deg_CX _ _
  · intro g a b
    rw [Zhat_eq]
    simp only [map_sum, map_mul, eval_C, eval_X, PI.UnitaryGroupMassFormula.UsCompose.vars, Sum.elim_inl, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_congr rfl fun x _ => by ring

private lemma exists_star_zhat_eq_eval_poly_deg_le_one (z z' : Fin (2 * r + k + 1) → ℂ) :
    ∃ P : Fin (r + 1) → Fin (r + 1) → MvPolynomial (Vr (2 * r + k + 1)) ℂ,
      (∀ a b, (P a b).totalDegree ≤ 1) ∧
        ∀ (g : Mat k r) a b, eval (vars g) (P a b) = star (Zhat k r z z' g a b) := by
  refine ⟨fun a b => ∑ i, ∑ j, C (star (((Fm k r z)ᴴ * Hpk k r) a i * Fm k r z' j b)) *
    MvPolynomial.X (Sum.inr (i, j)), ?_, ?_⟩
  · intro a b
    refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
    refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun j _ => ?_)
    exact deg_CX _ _
  · intro g a b
    rw [Zhat_eq]
    simp only [map_sum, map_mul, eval_C, eval_X, PI.UnitaryGroupMassFormula.UsCompose.vars, Sum.elim_inr, Matrix.mul_apply, Finset.sum_mul,
      star_sum, star_mul']
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_congr rfl fun x _ => by ring

private lemma exists_det_submatrix_poly_deg_le_of_entries_deg_le_one {m : ℕ} (f : Mat k r → Matrix (Fin m) (Fin m) ℂ)
    (P : Fin m → Fin m → MvPolynomial (Vr (2 * r + k + 1)) ℂ) (hP : ∀ a b, (P a b).totalDegree ≤ 1)
    (hf : ∀ g a b, eval (vars g) (P a b) = f g a b) (n : ℕ) (e : Fin n → Fin m) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ n ∧
      ∀ g, ((f g).submatrix e e).det = eval (vars g) q := by
  refine ⟨(Matrix.of fun a b => P (e a) (e b)).det, deg_det _ (fun a b => hP _ _), fun g => ?_⟩
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [RingHom.mapMatrix_apply, hf]

private lemma exists_dmin_eq_eval_poly_deg_le (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ l.val ∧
      ∀ g : Mat k r, Dmin k r z z' g l = eval (vars g) q := by
  obtain ⟨P, hP, hPe⟩ := exists_zhat_eq_eval_poly_deg_le_one (k := k) (r := r) z z'
  obtain ⟨q, hq, hqe⟩ := exists_det_submatrix_poly_deg_le_of_entries_deg_le_one (fun g => Zhat k r z z' g) P hP hPe l.val
    (Fin.castLE (Nat.le_of_lt_succ l.isLt))
  exact ⟨q, hq, fun g => by rw [Dmin]; exact hqe g⟩

private lemma exists_star_dmin_eq_eval_poly_deg_le (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ l.val ∧
      ∀ g : Mat k r, star (Dmin k r z z' g l) = eval (vars g) q := by
  obtain ⟨P, hP, hPe⟩ := exists_star_zhat_eq_eval_poly_deg_le_one (k := k) (r := r) z z'
  obtain ⟨q, hq, hqe⟩ := exists_det_submatrix_poly_deg_le_of_entries_deg_le_one (fun g => (Zhat k r z z' g).map (starRingEnd ℂ)) P hP
    (fun g a b => by simp [hPe]) l.val (Fin.castLE (Nat.le_of_lt_succ l.isLt))
  refine ⟨q, hq, fun g => ?_⟩
  rw [← hqe g, Dmin, ← starRingEnd_apply, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map]

lemma dminPoly (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ 2 * r + 2 ∧
      ∀ g : Mat k r, Dmin k r z z' g l = eval (vars g) q := by
  obtain ⟨q, hq, hqe⟩ := exists_dmin_eq_eval_poly_deg_le (k := k) z z' l
  exact ⟨q, hq.trans (by have := l.isLt; omega), hqe⟩

lemma dminStarPoly (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ 2 * r + 2 ∧
      ∀ g : Mat k r, star (Dmin k r z z' g l) = eval (vars g) q := by
  obtain ⟨q, hq, hqe⟩ := exists_star_dmin_eq_eval_poly_deg_le (k := k) z z' l
  exact ⟨q, hq.trans (by have := l.isLt; omega), hqe⟩

lemma gfPoly (z z' : Fin (2 * r + k + 1) → ℂ) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ 2 * r + 2 ∧
      ∀ g : Mat k r, ((Gf k r z z' g : ℝ) : ℂ) = eval (vars g) q := by
  obtain ⟨qa, ha, hae⟩ := exists_dmin_eq_eval_poly_deg_le (k := k) z z' (Fin.last (r + 1))
  obtain ⟨qab, hab, habe⟩ := exists_star_dmin_eq_eval_poly_deg_le (k := k) z z' (Fin.last (r + 1))
  obtain ⟨qb, hb, hbe⟩ := exists_dmin_eq_eval_poly_deg_le (k := k) z z' ⟨r, by omega⟩
  obtain ⟨qbb, hbb, hbbe⟩ := exists_star_dmin_eq_eval_poly_deg_le (k := k) z z' ⟨r, by omega⟩
  simp only [Fin.val_last] at ha hab hb hbb
  refine ⟨qa * qab - C ((Tz k r z * Tz k r z' : ℝ) : ℂ) * qb * qbb, ?_, fun g => ?_⟩
  · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
    · exact (deg_cmul _ _ _).trans (by omega)
  · simp only [map_sub, map_mul, eval_C]
    rw [← hae g, ← habe g, ← hbe g, ← hbbe g, Gf]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    simp only [Complex.star_def]
    ring

def qDl (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) : MvPolynomial (Vr (2 * r + k + 1)) ℂ :=
  Classical.choose (dminPoly (k := k) z z' l)

def qDbl (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) : MvPolynomial (Vr (2 * r + k + 1)) ℂ :=
  Classical.choose (dminStarPoly (k := k) z z' l)

def qGf (z z' : Fin (2 * r + k + 1) → ℂ) : MvPolynomial (Vr (2 * r + k + 1)) ℂ :=
  Classical.choose (gfPoly (k := k) z z')

lemma qDl_deg (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) : (qDl (k := k) z z' l).totalDegree ≤ 2 * r + 2 :=
  (Classical.choose_spec (dminPoly (k := k) z z' l)).1
lemma qDl_eval (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) (g : Mat k r) :
    eval (vars g) (qDl z z' l) = Dmin k r z z' g l :=
  ((Classical.choose_spec (dminPoly (k := k) z z' l)).2 g).symm
lemma qDbl_deg (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) : (qDbl (k := k) z z' l).totalDegree ≤ 2 * r + 2 :=
  (Classical.choose_spec (dminStarPoly (k := k) z z' l)).1
lemma qDbl_eval (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) (g : Mat k r) :
    eval (vars g) (qDbl z z' l) = star (Dmin k r z z' g l) :=
  ((Classical.choose_spec (dminStarPoly (k := k) z z' l)).2 g).symm
lemma qGf_deg (z z' : Fin (2 * r + k + 1) → ℂ) : (qGf (k := k) z z').totalDegree ≤ 2 * r + 2 :=
  (Classical.choose_spec (gfPoly (k := k) z z')).1
lemma qGf_eval (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) :
    eval (vars g) (qGf z z') = ((Gf k r z z' g : ℝ) : ℂ) :=
  ((Classical.choose_spec (gfPoly (k := k) z z')).2 g).symm

structure CT (k r nf : ℕ) where
  q : MvPolynomial (Vr (2 * r + k + 1)) ℂ
  a : Fin (r + 2) → ℕ
  b : Fin (r + 2) → ℕ
  c : ℕ
  es : List (Fin nf × List (Mat k r))

section vals

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def cvs (D : RealPlaceData k r Wp Wq) {nf : ℕ} (t : CT k r nf) (g : Mat k r) : ℂ :=
  eval (vars g) t.q * C6.monoM D t.a t.b t.c g

def cv (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq) (t : CT k r nf) (g : Mat k r) :
    C6.EndH Wp Wq :=
  cvs D t g • C6.Epart fib t.es g

def dscal (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (t : CT k r nf) : List (CT k r nf) :=
  [{ t with q := dP X t.q }] ++
  List.ofFn (fun l : Fin (r + 2) => if t.a l = 0 then { t with q := 0 } else
    { t with q := C (-(t.a l : ℂ)) * t.q * dP X (qDl D.z D.z' l), a := t.a + Pi.single l 1 }) ++
  List.ofFn (fun l : Fin (r + 2) => if t.b l = 0 then { t with q := 0 } else
    { t with q := C (-(t.b l : ℂ)) * t.q * dP X (qDbl D.z D.z' l), b := t.b + Pi.single l 1 }) ++
  [if t.c = 0 then { t with q := 0 } else { t with q := C (-(t.c : ℂ)) * t.q * dP X (qGf D.z D.z'), c := t.c + 1 }]

def dfib {nf : ℕ} (X : Mat k r) (t : CT k r nf) : List (CT k r nf) :=
  List.ofFn (fun i : Fin t.es.length => { t with es := t.es.set i ((t.es.get i).1, X :: (t.es.get i).2) })

def dco (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (t : CT k r nf) : List (CT k r nf) :=
  dscal D X t ++ dfib X t

end vals

lemma hasDerivAt_invpow' {c : ℝ → ℂ} {c' : ℂ} (hc : HasDerivAt c c' 0) {a : ℕ} (h0 : a = 0 ∨ c 0 ≠ 0) :
    HasDerivAt (fun t => (c t)⁻¹ ^ a) (-(a : ℂ) * c' * (c 0)⁻¹ ^ (a + 1)) 0 := by
  cases a with
  | zero => simpa using hasDerivAt_const (0 : ℝ) (1 : ℂ)
  | succ n =>
    have hc0 : c 0 ≠ 0 := h0.resolve_left (Nat.succ_ne_zero n)
    have h2 := ((hasDerivAt_inv hc0).pow (n + 1)).comp (0 : ℝ) hc
    have h3 : HasDerivAt (fun t => (c t)⁻¹ ^ (n + 1))
        (((n + 1 : ℕ) : ℂ) * (c 0)⁻¹ ^ (n + 1 - 1) * -(c 0 ^ 2)⁻¹ * c') 0 := h2
    refine h3.congr_deriv ?_
    rw [Nat.add_sub_cancel, ← inv_pow]
    push_cast
    ring

lemma hasDerivAt_polyD (X g : Mat k r) (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    HasDerivAt (fun t => Dmin k r z z' (crv (false, X) g t) l) (eval (vars g) (dP X (qDl z z' l))) 0 := by
  have h := hasDerivAt_poly X g (qDl (k := k) z z' l)
  simp only [qDl_eval] at h
  exact h

lemma hasDerivAt_polyDb (X g : Mat k r) (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    HasDerivAt (fun t => star (Dmin k r z z' (crv (false, X) g t) l)) (eval (vars g) (dP X (qDbl z z' l))) 0 := by
  have h := hasDerivAt_poly X g (qDbl (k := k) z z' l)
  simp only [qDbl_eval] at h
  exact h

lemma hasDerivAt_polyG (X g : Mat k r) (z z' : Fin (2 * r + k + 1) → ℂ) :
    HasDerivAt (fun t => ((Gf k r z z' (crv (false, X) g t) : ℝ) : ℂ)) (eval (vars g) (dP X (qGf z z'))) 0 := by
  have h := hasDerivAt_poly X g (qGf (k := k) z z')
  simp only [qGf_eval] at h
  exact h

end Formalism.FourierDecayAlt.P.MinorPolynomials
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedR
section
open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.NFRadRedR

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def LocLog : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∃ O : Set (Q.Mx k r), IsOpen O ∧ (1 : Q.Mx k r) ∈ O ∧ ∃ Λ : Q.Mx k r → Q.Mx k r, ContDiffOn ℝ ∞ Λ O ∧
      ∀ g ∈ O, g ∈ UWset k r z → InLieW k r z (Λ g) ∧ NormedSpace.exp (Λ g) = g

variable {k r : ℕ}

def lieW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Submodule ℝ (Q.Mx k r) where
  carrier := {X | InLieW k r z X}
  zero_mem' := ⟨⟨by simp, fun a _ => ⟨by simp, by simp⟩⟩, by simp⟩
  add_mem' := by
    rintro X Y ⟨⟨hX1, hX2⟩, hX3⟩ ⟨⟨hY1, hY2⟩, hY3⟩
    refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
    · rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
        show Xᴴ * Hpk k r + Yᴴ * Hpk k r + (Hpk k r * X + Hpk k r * Y) =
          (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) by abel, hX1, hY1, add_zero]
    · rw [Matrix.add_mulVec, (hX2 a ha).1, (hY2 a ha).1, add_zero]
    · rw [Matrix.add_mulVec, (hX2 a ha).2, (hY2 a ha).2, add_zero]
    · rw [Matrix.add_mulVec, hX3, hY3, add_zero]
  smul_mem' := by
    rintro c X ⟨⟨hX1, hX2⟩, hX3⟩
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    refine ⟨⟨?_, fun a ha => ⟨?_, ?_⟩⟩, ?_⟩
    · rw [Matrix.conjTranspose_smul]
      simp only [RCLike.star_def, RCLike.conj_ofReal]
      rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX1, smul_zero]
    · rw [Matrix.smul_mulVec, (hX2 a ha).1, smul_zero]
    · rw [Matrix.smul_mulVec, (hX2 a ha).2, smul_zero]
    · rw [Matrix.smul_mulVec, hX3, smul_zero]

def dOpL {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (hπ : Qr.IsRepW k r z π) :
    lieW k r z →ₗ[ℝ] (Wp →L[ℂ] Wp) where
  toFun X := dOp π (X : Q.Mx k r)
  map_add' X Y := (P.differential_operator_linear Wp k r z π hπ X Y X.2 Y.2).1
  map_smul' s X := by
    have h := (P.differential_operator_linear Wp k r z π hπ X X X.2 X.2).2 s
    show dOp π (s • (X : Q.Mx k r)) = s • dOp π (X : Q.Mx k r)
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    exact h

private lemma rep_exp_smul_eq_exp_dOp {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)} (hπ : IsCRepOn (UWset k r z) π)
    (hc : ContinuousOn π (UWset k r z)) {X : Q.Mx k r} (hX : InLieW k r z X) (t : ℝ) :
    π (NormedSpace.exp ((t : ℂ) • X)) = NormedSpace.exp (t • dOp π X) := by
  set A := dOp π X with hA
  set f : ℝ → (Wp →L[ℂ] Wp) := fun s => π (NormedSpace.exp ((s : ℂ) • X)) with hf
  have hmul : ∀ s u : ℝ, f (s + u) = f s * f u := by
    intro s u
    simp only [hf]
    rw [show ((s + u : ℝ) : ℂ) • X = (s : ℂ) • X + (u : ℂ) • X by push_cast; rw [add_smul],
      Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _),
      hπ.2 _ (exp_uw hX s) _ (exp_uw hX u), ContinuousLinearMap.mul_def]
  have h0 : HasDerivAt f A 0 := dOp_hasDeriv hπ hc hX
  have hd : ∀ s, HasDerivAt f (f s * A) s := by
    intro s
    have h2 : HasDerivAt (fun u => f s * f u) (f s * A) (s - s) := by
      rw [sub_self]
      exact h0.const_mul (f s)
    have h1 : HasDerivAt (fun u => f s * f (u - s)) (f s * A) s := HasDerivAt.comp_sub_const s s h2
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    show f u = f s * f (u - s)
    rw [← hmul]
    congr 1
    ring
  have hg : ∀ s, HasDerivAt (fun u => f u * NormedSpace.exp (u • -A)) 0 s := by
    intro s
    have := (hd s).mul (hasDerivAt_exp_smul_const (-A) s)
    have hcomm : Commute A (NormedSpace.exp (s • -A)) :=
      ((Commute.refl A).neg_right.smul_right s).exp_right
    have h0' : f s * A * NormedSpace.exp (s • -A) + f s * (NormedSpace.exp (s • -A) * -A) = 0 := by
      rw [mul_assoc, hcomm.eq, mul_neg, mul_neg, add_neg_cancel]
    exact this.congr_deriv h0'
  have hconst : ∀ s, f s * NormedSpace.exp (s • -A) = 1 := by
    intro s
    have hdiff : Differentiable ℝ (fun u => f u * NormedSpace.exp (u • -A)) := fun u => (hg u).differentiableAt
    have := is_const_of_deriv_eq_zero hdiff (fun u => (hg u).deriv) s 0
    rw [this]
    simp only [hf, zero_smul, Complex.ofReal_zero, NormedSpace.exp_zero, mul_one, hπ.1]
  have hk : ∀ s, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • -A) * NormedSpace.exp (u • A)) 0 s := by
    intro s
    have := (hasDerivAt_exp_smul_const (-A) s).mul (hasDerivAt_exp_smul_const A s)
    have hcomm2 : Commute A (NormedSpace.exp (s • A)) := ((Commute.refl A).smul_right s).exp_right
    have h0' : NormedSpace.exp (s • -A) * -A * NormedSpace.exp (s • A) +
        NormedSpace.exp (s • -A) * (NormedSpace.exp (s • A) * A) = 0 := by
      rw [mul_assoc, neg_mul, hcomm2.eq, mul_neg, neg_add_cancel]
    exact this.congr_deriv h0'
  have hinv : NormedSpace.exp (t • -A) * NormedSpace.exp (t • A) = 1 := by
    have hdiff : Differentiable ℝ (fun u : ℝ => NormedSpace.exp (u • -A) * NormedSpace.exp (u • A)) :=
      fun u => (hk u).differentiableAt
    have := is_const_of_deriv_eq_zero hdiff (fun u => (hk u).deriv) t 0
    rw [this]
    simp only [zero_smul, NormedSpace.exp_zero, mul_one]
  calc f t = f t * (NormedSpace.exp (t • -A) * NormedSpace.exp (t • A)) := by rw [hinv, mul_one]
    _ = NormedSpace.exp (t • A) := by rw [← mul_assoc, hconst t, one_mul]

private lemma contDiff_exp_hermitian_curvature {A : Type} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] :
    ContDiff ℝ ∞ (NormedSpace.exp : A → A) := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  have hx : x ∈ EMetric.ball (0 : A) (NormedSpace.expSeries ℝ A).radius := by
    rw [NormedSpace.expSeries_radius_eq_top]
    exact EMetric.mem_ball.mpr (edist_lt_top _ _)
  first
  | exact (NormedSpace.analyticAt_exp_of_mem_ball x hx).contDiffAt
  | exact (analyticAt_exp_of_mem_ball (𝕂 := ℝ) x hx).contDiffAt
  | (have hps := (NormedSpace.expSeries ℝ A).hasFPowerSeriesOnBall
        (by rw [NormedSpace.expSeries_radius_eq_top]; exact ENNReal.zero_lt_top)
     rw [NormedSpace.expSeries_sum_eq] at hps
     exact (hps.analyticAt_of_mem hx).contDiffAt)

theorem repSmooth_of (hLL : LocLog) : NFRadRedS.RepSmooth := by
  unfold NFRadRedS.RepSmooth
  intro Wp _ _ _ k r z π hz hTz hπ hc h₀ hh₀
  obtain ⟨O, hO, h1O, Λ, hΛ, hΛe⟩ := hLL k r z hz hTz
  have hrep : Qr.IsRepW k r z π := ⟨hπ, hc⟩
  have hdetH : IsUnit (Hpk k r).det := by
    have h := congrArg Matrix.det (Formalism.QuantumDeterminants.GBasic.Hpk_sq k r)
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact isUnit_iff_exists_inv.mpr ⟨_, h⟩
  have hdet0 : IsUnit h₀.det := ((Formalism.QuantumDeterminants.uHGroup _ (Hpk k r) hdetH).2.2 h₀ hh₀.1).1
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (lieW k r z)
  let T : Q.Mx k r →ₗ[ℝ] (Wp →L[ℂ] Wp) := (dOpL z π hrep).comp (Submodule.linearProjOfIsCompl _ q hq)
  have hT1 : ∀ Y, InLieW k r z Y → T Y = dOp π Y := by
    intro Y hY
    have hp := Submodule.linearProjOfIsCompl_apply_left hq ⟨Y, hY⟩
    show dOpL z π hrep (Submodule.linearProjOfIsCompl _ q hq Y) = dOp π Y
    rw [show Submodule.linearProjOfIsCompl _ q hq Y = ⟨Y, hY⟩ from hp]
    rfl
  let Tc := LinearMap.toContinuousLinearMap T
  let Lm : Q.Mx k r →ₗ[ℝ] Q.Mx k r :=
    { toFun := fun h => h₀⁻¹ * h
      map_add' := fun a b => Matrix.mul_add _ _ _
      map_smul' := fun c a => by simp [Matrix.mul_smul] }
  let Lc := LinearMap.toContinuousLinearMap Lm
  have hV : IsOpen {h : Q.Mx k r | h₀⁻¹ * h ∈ O} := hO.preimage Lc.continuous
  refine ⟨{h : Q.Mx k r | h₀⁻¹ * h ∈ O}, hV, ?_, fun h => π h₀ * NormedSpace.exp (Tc (Λ (h₀⁻¹ * h))), ?_, ?_⟩
  · show h₀⁻¹ * h₀ ∈ O
    rw [Matrix.nonsing_inv_mul h₀ hdet0]
    exact h1O
  · have h1 : ContDiffOn ℝ ∞ (fun h => Λ (Lc h)) {h : Q.Mx k r | h₀⁻¹ * h ∈ O} :=
      hΛ.comp Lc.contDiff.contDiffOn (fun h hh => hh)
    exact contDiffOn_const.mul (contDiff_exp_hermitian_curvature.comp_contDiffOn (Tc.contDiff.comp_contDiffOn h1))
  · intro h hV' hU
    have hg : h₀⁻¹ * h ∈ UWset k r z := Formalism.QuantumDeterminants.WeylGroupFacts.uw_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh₀) hU
    obtain ⟨hlie, hexp⟩ := hΛe _ hV' hg
    have hpi := rep_exp_smul_eq_exp_dOp hπ hc hlie 1
    simp only [Complex.ofReal_one, one_smul] at hpi
    rw [hexp] at hpi
    calc π h = π (h₀ * (h₀⁻¹ * h)) := by
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv h₀ hdet0, Matrix.one_mul]
      _ = (π h₀).comp (π (h₀⁻¹ * h)) := hπ.2 _ hh₀ _ hg
      _ = π h₀ * NormedSpace.exp (Tc (Λ (h₀⁻¹ * h))) := by
          rw [ContinuousLinearMap.mul_def, hpi,
            show Tc (Λ (h₀⁻¹ * h)) = dOp π (Λ (h₀⁻¹ * h)) from hT1 _ hlie]

end Formalism.FourierDecayAlt.P.NFRadRedR

namespace Formalism.FourierDecayAlt.P

theorem representation_smooth_of_log : NFRadRedR.LocLog → NFRadRedS.RepSmooth := fun h => NFRadRedR.repSmooth_of h

end Formalism.FourierDecayAlt.P
end
end

