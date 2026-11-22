import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1039
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchwartzIntertwinesMetaplecticQuadratic
section
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

noncomputable section

namespace GlobalTheory.RealLift.QuadFock

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

def atPlLin (w : ι) : Module.End ℂ (V w) →ₗ[ℂ] Module.End ℂ (⨂[ℂ] i, V i) :=
  (PiTensorProduct.mapMultilinear ℂ V V).toLinearMap (fun _ => LinearMap.id) w

theorem atPlLin_apply (w : ι) (L : Module.End ℂ (V w)) : atPlLin w L = atPl w L := by
  simp only [atPlLin, MultilinearMap.toLinearMap_apply, PiTensorProduct.mapMultilinear_apply, atPl]

theorem atPl_zero (w : ι) : atPl w (0 : Module.End ℂ (V w)) = 0 := by
  rw [← atPlLin_apply, map_zero]

theorem atPl_mul (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L * L') = atPl w L * atPl w L' := by
  unfold atPl
  rw [← PiTensorProduct.map_mul]
  congr 1
  funext i
  by_cases h : i = w
  · subst h
    simp
  · rw [Function.update_of_ne h, Function.update_of_ne h, Function.update_of_ne h]
    rfl

end Tensor

variable {P Q R S : ℕ}

theorem heisOp_smul (r : ℝ) (c : Matrix (Ix P Q) (Ix R S) ℂ) : heisOp (r • c) = (r : ℂ) • heisOp c := by
  unfold heisOp
  rw [smul_comm (r : ℂ) ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Matrix.smul_apply, Complex.real_smul, star_mul', Complex.star_def, Complex.conj_ofReal, smul_sub, smul_smul]
  congr 2 <;> ring

theorem heisOp_zero : heisOp (0 : Matrix (Ix P Q) (Ix R S) ℂ) = 0 := by
  simpa using heisOp_smul (P := P) (Q := Q) (R := R) (S := S) 0 0

theorem sumPl_single {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι) (M : Matrix (Ix P Q) (Ix R S) ℂ) :
    sumPl (V := fun _ : ι => Pol P Q R S) (fun w' => heisOp ((Pi.single w M : ι → Matrix (Ix P Q) (Ix R S) ℂ) w')) = atPl w (heisOp M) := by
  unfold sumPl
  rw [Finset.sum_eq_single w]
  · simp
  · intro b _ hb
    dsimp only
    rw [Pi.single_eq_of_ne hb, heisOp_zero, atPl_zero]
  · simp

end GlobalTheory.RealLift.QuadFock

namespace GlobalTheory.RealLift.QuadFock

variable {P Q R S : ℕ}

def sgn (a : Ix P Q) (b : Ix R S) : ℝ := (lineSign a b).re

theorem lineSign_eq_sgn (a : Ix P Q) (b : Ix R S) : lineSign a b = ((sgn a b : ℝ) : ℂ) := by
  rcases a with a | a <;> rcases b with b | b <;> simp [sgn, lineSign]

theorem sgn_mul_self (a : Ix P Q) (b : Ix R S) : sgn a b * sgn a b = 1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [sgn, lineSign]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def eS (w : ι) (a : Ix P Q) (b : Ix R S) (x : ℂ) : ι → Matrix (Ix P Q) (Ix R S) ℂ :=
  Pi.single w (Matrix.single a b x)

theorem eS_apply (w : ι) (a : Ix P Q) (b : Ix R S) (x : ℂ) (w' : ι) (a' : Ix P Q) (b' : Ix R S) :
    eS w a b x w' a' b' = if w' = w ∧ a' = a ∧ b' = b then x else 0 := by
  by_cases hw : w' = w
  · subst hw
    simp only [eS, Pi.single_eq_same, Matrix.single_apply, true_and]
    by_cases h : a' = a ∧ b' = b
    · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
    · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]
  · simp [eS, hw]

theorem sum_eS (w : ι) (a : Ix P Q) (b : Ix R S) (x : ℂ) (c : ι → Matrix (Ix P Q) (Ix R S) ℂ) :
    (∑ w', ∑ a', ∑ b', lineSign a' b' * eS w a b x w' a' b' * star (c w' a' b')) =
      lineSign a b * x * star (c w a b) := by
  rw [Finset.sum_eq_single w, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp [eS_apply]
  all_goals first
    | (intro y _ hy; simp [eS_apply, hy, Ne.symm hy]; done)
    | simp

theorem decomp (c : ι → Matrix (Ix P Q) (Ix R S) ℂ) :
    c = ∑ w, ∑ a, ∑ b, ((c w a b).re • eS w a b 1 + (c w a b).im • eS w a b Complex.I) := by
  funext w
  ext a b
  simp only [Finset.sum_apply, Matrix.sum_apply, Pi.add_apply, Pi.smul_apply, Matrix.add_apply,
    Matrix.smul_apply]
  rw [Finset.sum_eq_single w, Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp only [eS_apply, and_self, if_true, Complex.real_smul, mul_one]
    exact (Complex.re_add_im _).symm
  all_goals first
    | (intro y _ hy; simp [eS_apply, hy, Ne.symm hy]; done)
    | simp

end GlobalTheory.RealLift.QuadFock

namespace GlobalTheory.RealLift.QuadFock

variable {P Q R S : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

def cu (i : ι × Ix P Q × Ix R S × Bool) : ι → Matrix (Ix P Q) (Ix R S) ℂ :=
  if i.2.2.2 then (sgn i.2.1 i.2.2.1 / 2) • eS i.1 i.2.1 i.2.2.1 1
  else (-(sgn i.2.1 i.2.2.1 / 2)) • eS i.1 i.2.1 i.2.2.1 Complex.I

def cv (i : ι × Ix P Q × Ix R S × Bool) : ι → Matrix (Ix P Q) (Ix R S) ℂ :=
  if i.2.2.2 then eS i.1 i.2.1 i.2.2.1 Complex.I else eS i.1 i.2.1 i.2.2.1 1

theorem dual {l : Type} [Fintype l] (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ))
    (hφ : ∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im)
    (x : l ⊕ l → ℝ) : ∑ i, sympl (φ (cv i)) x • φ (cu i) = x := by
  obtain ⟨c, rfl⟩ := φ.surjective x
  have e1 : ∀ i, sympl (φ (cv i)) (φ c) • φ (cu i) = φ (sympl (φ (cv i)) (φ c) • cu i) :=
    fun i => (map_smul φ _ _).symm
  simp only [e1, ← map_sum]
  congr 1
  conv_rhs => rw [decomp c]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, cu, cv, if_true, Bool.false_eq_true, if_false, hφ, sum_eS]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [smul_smul, smul_smul, lineSign_eq_sgn]
  have h2 := sgn_mul_self a b
  congr 2
  · simp [Complex.mul_im, Complex.mul_re]
    linear_combination (c w a b).re * h2
  · simp [Complex.mul_im, Complex.mul_re]
    linear_combination (c w a b).im * h2

theorem cu_true_mul (Y : ι → Mat R S) (w : ι) (a : Ix P Q) (b : Ix R S) (w' : ι) :
    cu (w, a, b, true) w' * (Y w')ᵀ =
      (Pi.single w ((sgn a b / 2) • (Matrix.single a b (1 : ℂ) * (Y w)ᵀ)) : ι → Matrix (Ix P Q) (Ix R S) ℂ) w' := by
  by_cases h : w' = w
  · subst h
    simp only [cu, eS, if_true, Bool.false_eq_true, if_false, Pi.smul_apply, Pi.single_eq_same, Matrix.smul_mul]
  · simp [cu, eS, h]

theorem cu_false_mul (Y : ι → Mat R S) (w : ι) (a : Ix P Q) (b : Ix R S) (w' : ι) :
    cu (w, a, b, false) w' * (Y w')ᵀ =
      (Pi.single w ((-(sgn a b / 2)) • (Matrix.single a b Complex.I * (Y w)ᵀ)) : ι → Matrix (Ix P Q) (Ix R S) ℂ) w' := by
  by_cases h : w' = w
  · subst h
    simp only [cu, eS, if_true, Bool.false_eq_true, if_false, Pi.smul_apply, Pi.single_eq_same, Matrix.smul_mul]
  · simp [cu, eS, h]

theorem cv_true (w : ι) (a : Ix P Q) (b : Ix R S) :
    cv (w, a, b, true) = (Pi.single w (Matrix.single a b Complex.I) : ι → Matrix (Ix P Q) (Ix R S) ℂ) := by
  simp [cv, eS]

theorem cv_false (w : ι) (a : Ix P Q) (b : Ix R S) :
    cv (w, a, b, false) = (Pi.single w (Matrix.single a b (1 : ℂ)) : ι → Matrix (Ix P Q) (Ix R S) ℂ) := by
  simp [cv, eS]

theorem atPlLin_mul {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module ℂ (V i)] (w : ι) (L L' : Module.End ℂ (V w)) :
    atPlLin w (L * L') = atPlLin w L * atPlLin w L' := by
  simp only [atPlLin_apply, atPl_mul]

end GlobalTheory.RealLift.QuadFock

namespace GlobalTheory.RealLift.QuadFock

theorem quad_fock : (∀ (l κ : Type) [Fintype l] [DecidableEq l] [Fintype κ] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (u v : κ → (l ⊕ l → ℝ)),
    (∀ w, ∑ i, sympl (v i) w • u i = w) →
    quad X = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i, (1 / 2 : ℂ) •
      (dRho (X *ᵥ u i) * dRho (v i) + dRho (v i) * dRho (X *ᵥ u i))) → (∀ (P Q R S : ℕ) (Y : Mat R S), Y ∈ upq R S →
    fockAct2 P Q R S Y = (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ a : Ix P Q, ∑ b : Ix R S, (lineSign a b / 4) •
      ((heisOp (Matrix.single a b (1 : ℂ) * Yᵀ) * heisOp (Matrix.single a b Complex.I) +
          heisOp (Matrix.single a b Complex.I) * heisOp (Matrix.single a b (1 : ℂ) * Yᵀ)) -
        (heisOp (Matrix.single a b Complex.I * Yᵀ) * heisOp (Matrix.single a b (1 : ℂ)) +
          heisOp (Matrix.single a b (1 : ℂ)) * heisOp (Matrix.single a b Complex.I * Yᵀ)))) → ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (Ψ : (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) →ₗ[ℂ] Sch l),
    (∀ c T, Ψ (sumPl (fun w => heisOp (c w)) T) = dRho (φ c) (Ψ T)) →
    ∀ Y : ι → Mat R S, (∀ w, Y w ∈ upq R S) → ∀ Z : Matrix (l ⊕ l) (l ⊕ l) ℝ,
    (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) →
    ∀ T, quad Z (Ψ T) = Ψ (sumPl (fun w => fockAct2 P Q R S (Y w)) T) := by
  intro H1 H2 ι l _ _ _ _ P Q R S φ hφ Ψ hΨ Y hY Z hZ T
  have hq := H1 l (ι × Ix P Q × Ix R S × Bool) Z (fun i => φ (cu i)) (fun i => φ (cv i)) (dual φ hφ)
  have hop : sumPl (V := fun _ : ι => Pol P Q R S) (fun w => fockAct2 P Q R S (Y w)) =
      (4 * Real.pi * Complex.I : ℂ)⁻¹ • ∑ i, (1 / 2 : ℂ) •
        (sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (cu i w * (Y w)ᵀ)) *
            sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (cv i w)) +
          sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (cv i w)) *
            sumPl (V := fun _ : ι => Pol P Q R S) (fun w => heisOp (cu i w * (Y w)ᵀ))) := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, cu_true_mul, cu_false_mul, cv_true, cv_false, sumPl_single,
      heisOp_smul]
    unfold sumPl
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    dsimp only
    rw [H2 P Q R S (Y w) (hY w)]
    simp only [← atPlLin_apply, map_smul, map_sum, map_sub, map_add, atPlLin_mul]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [lineSign_eq_sgn]
    simp only [smul_mul_assoc, mul_smul_comm]
    push_cast
    module
  rw [hop, hq]
  clear H1 H2 hq hop hφ hY
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.add_apply, Module.End.mul_apply, map_smul, map_sum, map_add, hΨ, hZ]

end GlobalTheory.RealLift.QuadFock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupTestFunctionSupportBoundedDenominators
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.BoundedDen

theorem den_factorization_le (p : ℕ) [Fact p.Prime] (q : ℚ) (M : ℕ) (hM : 0 < M) (k : ℤ) (e : ℕ)
    (h : q * ((M : ℚ) * (p : ℚ) ^ e) = k) (ℓ : ℕ) (hℓ : ℓ ≠ p) :
    q.den.factorization ℓ ≤ M.factorization ℓ := by
  have hp : p.Prime := Fact.out
  have hN : ((M * p ^ e : ℕ) : ℚ) ≠ 0 := by
    have : 0 < M * p ^ e := Nat.mul_pos hM (pow_pos hp.pos e)
    exact_mod_cast this.ne'
  have hq : q = Rat.divInt k ((M * p ^ e : ℕ) : ℤ) := by
    rw [Rat.divInt_eq_div]
    push_cast at hN ⊢
    rw [eq_div_iff hN]; exact h
  have hd : q.den ∣ M * p ^ e := by
    have := Rat.den_dvd k ((M * p ^ e : ℕ) : ℤ)
    rw [← hq] at this
    exact_mod_cast this
  have hle := (Nat.factorization_le_iff_dvd q.den_nz (Nat.mul_pos hM (pow_pos hp.pos e)).ne').2 hd ℓ
  rw [Nat.factorization_mul hM.ne' (pow_pos hp.pos e).ne', Nat.factorization_pow, hp.factorization] at hle
  simpa [Finsupp.single_apply, Ne.symm hℓ] using hle

end GlobalTheory.LKCx.BoundedDen

namespace GlobalTheory.LKCx.BoundedDen

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (h₁ : G.GAf), ∃ D : ℕ, 0 < D ∧ ∀ y : grp G β, f (h₁⁻¹ * toAfF G β x t hx y * h₁) ≠ 0 → ∀ ℓ : ℕ, ℓ ≠ p → (∀ i, ((Module.finBasis ℚ G.C).repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i).den.factorization ℓ ≤ D.factorization ℓ) ∧ (((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)).den.factorization ℓ ≤ D.factorization ℓ := by
  intro p _ G β x t hx L f hf h₁
  obtain ⟨Ω, Ω', hΩ, hΩ', hmem⟩ := exists_compact_toAfF p G L f hf β x t hx h₁
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  let b := Module.finBasis ℚ G.C
  let b' := b.baseChange (AfP p)
  have hcpt : ∀ i, IsCompact ((b'.coord i) '' Ω) := fun i =>
    hΩ.image (IsModuleTopology.continuous_of_linearMap (b'.coord i))
  choose m hm0 hm using fun i => GlobalTheory.DenAway.den_bounded_of_isCompact p _ (hcpt i)
  obtain ⟨M', hM'0, hM'⟩ := GlobalTheory.DenAway.den_bounded_of_isCompact p Ω' hΩ'
  refine ⟨(∏ i, m i) * M', Nat.mul_pos (Finset.prod_pos fun i _ => hm0 i) hM'0, fun y hy ℓ hℓ => ⟨fun i => ?_, ?_⟩⟩
  · have hval : b'.coord i (inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) =
        algebraMap ℚ (AfP p) (b.repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i) := by
      simp only [inC, b', RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, Module.Basis.coord_apply,
        Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
    obtain ⟨k, e, hk⟩ := hm i (b.repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i) (by rw [← hval]; exact ⟨_, (hmem y hy).1, rfl⟩)
    have h1 := den_factorization_le p _ (m i) (hm0 i) k e hk ℓ hℓ
    have hd : m i ∣ (∏ j, m j) * M' := (Finset.dvd_prod_of_mem m (Finset.mem_univ i)).mul_right _
    exact h1.trans ((Nat.factorization_le_iff_dvd (hm0 i).ne'
      (Nat.mul_pos (Finset.prod_pos fun i _ => hm0 i) hM'0).ne').2 hd ℓ)
  · have e0 : ((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ) = (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)⁻¹ := Units.val_inv_eq_inv_val _
    obtain ⟨k, e, hk⟩ := hM' _ (hmem y hy).2
    rw [e0]
    have h1 := den_factorization_le p _ M' hM'0 k e hk ℓ hℓ
    exact h1.trans ((Nat.factorization_le_iff_dvd hM'0.ne'
      (Nat.mul_pos (Finset.prod_pos fun i _ => hm0 i) hM'0).ne').2 (dvd_mul_left _ _) ℓ)

end GlobalTheory.LKCx.BoundedDen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupToPadicPointsDegreeOneEqUnitaryPoints
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.TorCls

variable {p : ℕ} [Fact p.Prime]

def InT (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (β y : G.C) (z : (R ⊗[ℚ] G.C)ˣ × Rˣ) : Prop :=
  (z.1 : R ⊗[ℚ] G.C) * inC G R β * (starT G.star R (z.1 : R ⊗[ℚ] G.C)).unop =
      algebraMap R (R ⊗[ℚ] G.C) (z.2 : R) * inC G R β ∧
    Commute (z.1 : R ⊗[ℚ] G.C) (inC G R y)

def psiAway (G : HTGroup p) (x : (AfP p ⊗[ℚ] G.C)ˣ) :
    (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ →* (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ :=
  (MulAut.conj x).toMonoidHom.prodMap (MonoidHom.id _)

def psiP (G : HTGroup p) : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ →* Gr G 1 :=
  (inclG G 1).comp ((MonoidHom.snd _ _).prod (Pi.monoidHom fun w =>
    (Units.map ((G.locW w).toRingHom.toMonoidHom)).comp (MonoidHom.fst _ _)))

@[simp] theorem psiAway_apply (G : HTGroup p) (x : (AfP p ⊗[ℚ] G.C)ˣ) (z : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) :
    psiAway G x z = (x * z.1 * x⁻¹, z.2) := rfl

def dg (D : Type) [Ring D] [Algebra ℚ D] (p : ℕ) [Fact p.Prime] :
    Dˣ × ℚˣ →* ((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ) :=
  ((Units.map (Algebra.TensorProduct.includeRight : D →ₐ[ℚ] AfP p ⊗[ℚ] D).toMonoidHom).prodMap
      (Units.map (algebraMap ℚ (AfP p)).toMonoidHom)).prod
    ((Units.map (Algebra.TensorProduct.includeRight : D →ₐ[ℚ] ℚ_[p] ⊗[ℚ] D).toMonoidHom).prodMap
      (Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom))

theorem toAfF_eq_psiAway (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y : grp G β) :
    ((toAfF G β x t hx y : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) =
      psiAway G x ((dg G.C p (y : G.Cˣ × ℚˣ)).1) := rfl

theorem formGroupToPadicPointsDegreeOne_eq_unitaryPoints (G : HTGroup p) (β : G.Cˣ) (y : grp G β) :
    toP1 G β y = psiP G ((dg G.C p (y : G.Cˣ × ℚˣ)).2) := by
  simp only [toP1, psiP, MonoidHom.comp_apply]
  congr 1
  refine Prod.ext rfl (funext fun w => Units.ext ?_)
  change G.rho w _ = G.locW w ((1 : ℚ_[p]) ⊗ₜ _)
  change _ = (Algebra.ofId ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw w)) (1 : ℚ_[p])) * (G.rho w).toRatAlgHom _
  rw [map_one, one_mul]
  rfl

theorem form_mul_inv {D : Type} [Ring D] [Algebra ℚ D] (σ : D →+* Dᵐᵒᵖ) (β : D) (a e : Dˣ) (α η : ℚˣ)
    (ha : (a : D) * β * (σ a).unop = algebraMap ℚ D α * β) (he : (e : D) * β * (σ e).unop = algebraMap ℚ D η * β) :
    ((a * e⁻¹ : Dˣ) : D) * β * (σ ((a * e⁻¹ : Dˣ) : D)).unop = algebraMap ℚ D ((α * η⁻¹ : ℚˣ) : ℚ) * β := by
  have hs : (σ (e : D)).unop * (σ ((e⁻¹ : Dˣ) : D)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have hs' : (σ ((e⁻¹ : Dˣ) : D)).unop * (σ (e : D)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]
  have hη : algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * algebraMap ℚ D (η : ℚ) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have key : ((e⁻¹ : Dˣ) : D) * β * (σ ((e⁻¹ : Dˣ) : D)).unop = algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * β := by
    calc ((e⁻¹ : Dˣ) : D) * β * (σ ((e⁻¹ : Dˣ) : D)).unop
        = algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * (((e⁻¹ : Dˣ) : D) * (algebraMap ℚ D (η : ℚ) * β) *
            (σ ((e⁻¹ : Dˣ) : D)).unop) := by
          simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, smul_smul]
          rw [show (η : ℚ) * ((η⁻¹ : ℚˣ) : ℚ) = 1 by simp, one_smul]
      _ = algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * ((((e⁻¹ : Dˣ) : D) * e) * β *
            ((σ (e : D)).unop * (σ ((e⁻¹ : Dˣ) : D)).unop)) := by
          rw [← he]; simp only [mul_assoc]
      _ = _ := by rw [Units.inv_mul, hs, one_mul, mul_one]
  have hsm : (σ ((a * e⁻¹ : Dˣ) : D)).unop = (σ ((e⁻¹ : Dˣ) : D)).unop * (σ (a : D)).unop := by
    rw [Units.val_mul, map_mul, MulOpposite.unop_mul]
  rw [hsm, Units.val_mul, Units.val_mul, map_mul]
  calc (a : D) * ((e⁻¹ : Dˣ) : D) * β * ((σ ((e⁻¹ : Dˣ) : D)).unop * (σ (a : D)).unop)
      = (a : D) * (((e⁻¹ : Dˣ) : D) * β * (σ ((e⁻¹ : Dˣ) : D)).unop) * (σ (a : D)).unop := by
        simp only [mul_assoc]
    _ = algebraMap ℚ D ((η⁻¹ : ℚˣ) : ℚ) * ((a : D) * β * (σ (a : D)).unop) := by
        rw [key, ← mul_assoc (a : D), ← Algebra.commutes ((η⁻¹ : ℚˣ) : ℚ) (a : D)]; simp only [mul_assoc]
    _ = _ := by
        rw [ha, ← mul_assoc, ← map_mul, mul_comm ((η⁻¹ : ℚˣ) : ℚ), map_mul]

theorem conj_back {S A : Type*} [Ring S] [CommRing A] [Algebra A S] (σ : S →+* Sᵐᵒᵖ) (b : S) (x g : Sˣ)
    (t c : A) (hx : (x : S) * b * (σ x).unop = algebraMap A S t)
    (hg : (g : S) * (σ g).unop = algebraMap A S c) :
    ((x⁻¹ * g * x : Sˣ) : S) * b * (σ ((x⁻¹ * g * x : Sˣ) : S)).unop = algebraMap A S c * b := by
  have h1 : (σ (x : S)).unop * (σ ((x⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have hb : b = algebraMap A S t * (((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop) := by
    calc b = (((x⁻¹ : Sˣ) : S) * x) * b * ((σ (x : S)).unop * (σ ((x⁻¹ : Sˣ) : S)).unop) := by
          rw [Units.inv_mul, h1, one_mul, mul_one]
      _ = ((x⁻¹ : Sˣ) : S) * ((x : S) * b * (σ (x : S)).unop) * (σ ((x⁻¹ : Sˣ) : S)).unop := by
          simp only [mul_assoc]
      _ = _ := by rw [hx, ← Algebra.commutes, mul_assoc]
  have hσ : (σ ((x⁻¹ * g * x : Sˣ) : S)).unop =
      (σ (x : S)).unop * (σ (g : S)).unop * (σ ((x⁻¹ : Sˣ) : S)).unop := by
    simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
  rw [hσ]
  calc ((x⁻¹ * g * x : Sˣ) : S) * b * ((σ (x : S)).unop * (σ (g : S)).unop * (σ ((x⁻¹ : Sˣ) : S)).unop)
      = ((x⁻¹ : Sˣ) : S) * ((g : S) * ((x : S) * b * (σ (x : S)).unop) * (σ (g : S)).unop) *
          (σ ((x⁻¹ : Sˣ) : S)).unop := by
        simp only [Units.val_mul, mul_assoc]
    _ = ((x⁻¹ : Sˣ) : S) * (algebraMap A S t * ((g : S) * (σ (g : S)).unop)) *
          (σ ((x⁻¹ : Sˣ) : S)).unop := by
        rw [hx, ← Algebra.commutes t (g : S)]; simp only [mul_assoc]
    _ = algebraMap A S (c * t) * (((x⁻¹ : Sˣ) : S) * (σ ((x⁻¹ : Sˣ) : S)).unop) := by
        rw [hg, ← map_mul, ← Algebra.commutes, mul_assoc, mul_comm t c]
    _ = algebraMap A S c * b := by rw [hb, map_mul, mul_assoc]

theorem inT_psiAway_inv_of_commute : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y₀ : grp G β) (c : G.GAf), c * toAfF G β x t hx y₀ = toAfF G β x t hx y₀ * c →
    InT G (AfP p) β (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) (psiAway G x⁻¹ (c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ)) := by
  intro p _ G β x t hx y₀ c hc
  have hxx : ((x⁻¹)⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) = x := inv_inv x
  refine ⟨?_, ?_⟩
  · have hg : (((c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) *
        (starT G.star (AfP p) (((c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) :
          AfP p ⊗[ℚ] G.C)).unop =
        algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) ((c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p) := c.2
    have h := conj_back (starT G.star (AfP p)) (inC G (AfP p) β) x _ (t : AfP p) _ hx hg
    simp only [psiAway_apply, hxx]
    exact h
  · have hU := congrArg (fun g : G.GAf => ((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1)) hc
    simp only [Subgroup.coe_mul, Prod.fst_mul] at hU
    rw [toAfF_eq_psiAway, psiAway_apply] at hU
    simp only [psiAway_apply, hxx]
    set c1 := (c : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1
    set Y := (dg G.C p (y₀ : G.Cˣ × ℚˣ)).1.1
    have hUU : (x⁻¹ * c1 * x) * Y = Y * (x⁻¹ * c1 * x) := by
      calc (x⁻¹ * c1 * x) * Y = x⁻¹ * (c1 * (x * Y * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * Y * x⁻¹) * c1) * x := by rw [hU]
        _ = Y * (x⁻¹ * c1 * x) := by group
    exact congrArg Units.val hUU

end GlobalTheory.TorCls
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianPositivityInvariant
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem pos_iff_smul_toV (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (g : grp G β)
    (z : Fin G.n → ℂ) (c : ℂ) : c ≠ 0 →
    (0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ↔ 0 < (star (c • ((toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)) ⬝ᵥ
      (herm G v β *ᵥ (c • ((toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)))).re) := by
  intro hc
  set M : Matrix (Fin G.n) (Fin G.n) ℂ := (toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) with hM
  set H := herm G v β
  have hsim := GlobalTheory.LKCx.grp_similitude_herm p G v β g
  have hs : (0 : ℚ) < (((g : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := g.2.2
  set s : ℚ := (((g : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)
  have key : star (c • (M *ᵥ z)) ⬝ᵥ (H *ᵥ (c • (M *ᵥ z))) =
      ((Complex.normSq c * s : ℝ) : ℂ) * (star z ⬝ᵥ (H *ᵥ z)) := by
    have e1 : star (M *ᵥ z) ⬝ᵥ (H *ᵥ (M *ᵥ z)) = star z ⬝ᵥ ((Mᴴ * H * M) *ᵥ z) := by
      rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
    rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, e1, hsim, Matrix.smul_mulVec,
      dotProduct_smul]
    simp only [smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    push_cast
    rw [Complex.normSq_eq_conj_mul_self]
    simp [mul_comm]
  rw [key, Complex.re_ofReal_mul]
  have hpos : 0 < Complex.normSq c * (s : ℝ) :=
    mul_pos (Complex.normSq_pos.2 hc) (by exact_mod_cast hs)
  exact (mul_pos_iff_of_pos_left hpos).symm

end GlobalTheory.LKCx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentSumConjSumOrthogonalDvdStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentSum_conjSum_orthogonal_dvd : ∀ (D : D7) (e e' : AE D) (P P' : Finset (Formalism.L2.DIV.Pl D.host.E)) (n : ℕ), IsIdemSum e P → IsIdemSum e' P' → (∀ PP ∈ P, ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ PP ∈ P', ((n : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (e + cA D e) * (e' + cA D e') = 0 := by
  first | exact @GlobalTheory.IdemOrth.idemSum_orth | exact GlobalTheory.IdemOrth.idemSum_orth | (intros; apply GlobalTheory.IdemOrth.idemSum_orth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentSupportHermitianDecompositionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_support_hermitian_decomposition : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (S : Finset ℕ), (∀ q ∈ S, q.Prime) →
    ∀ x : GA D V, x ∈ GfC V →
    ∃ (γ : GL (Fin V.rank) D.host.E) (h k : GA D V),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1 = V.gram ∧ h ∈ GfC V ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V h ∧ ∀ w ∈ P, Off S w) ∧
      k ∈ GfC V ∧ (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE V k).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr)) ∧
      (Formalism.IndefR.Lev.finE V x).1 = γ.1.map (eToEAf D) * (Formalism.IndefR.Lev.finE V h).1 * (Formalism.IndefR.Lev.finE V k).1 := by
  first | exact @GlobalTheory.FunObj.StdReps.exists_rep_std | exact GlobalTheory.FunObj.StdReps.exists_rep_std | (intros; apply GlobalTheory.FunObj.StdReps.exists_rep_std <;> assumption)
end

