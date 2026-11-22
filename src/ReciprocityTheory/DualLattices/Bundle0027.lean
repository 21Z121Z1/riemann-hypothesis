import ReciprocityTheory.DualLattices.Bundle0023
import ReciprocityTheory.DualLattices.PowMemCarrier
import ReciprocityTheory.DualLattices.Bundle0022
import ReciprocityTheory.DualLattices.Bundle0024
import ReciprocityTheory.DualLattices.Bundle0014
import ReciprocityTheory.DualLattices.Bundle0025

-- bundled from ReciprocityTheory.DualLattices.EigenLiftsFrobenius
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section FrobA

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

private theorem hasLen_of_linearEquiv {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    {x : NNReal} (e : M ≃ₗ[R] M') (h : HasLen v R M' x) : HasLen v R M x := by
  obtain ⟨m, c, ⟨φ⟩, hx⟩ := h
  exact ⟨m, c, ⟨e.trans φ⟩, hx⟩

lemma coefX_int (D : Lifts H U X) (hdet : (valM D).det ≠ 0)
    (hbasis : H.AA.carrier = Submodule.span R (Set.range fun (α : Nb p g) (y : Nb p g) =>
      ∏ j, (algebraMap R C (D.ε j) * D.u j y) ^ (α j).val))
    {f : Nb p g → C} (hf : f ∈ H.AA.carrier) :
    ∃ r : Nb p g → R, coefX D f = algebraMap R C ∘ r := by
  rw [hbasis] at hf
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hf
  refine ⟨r, ?_⟩
  have hfv : f = valM D *ᵥ (algebraMap R C ∘ r) := by
    rw [← hr]
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, valM, Matrix.of_apply,
      Function.comp_apply, monX, xL, Algebra.smul_def]
    exact Finset.sum_congr rfl fun α _ => mul_comm _ _
  rw [coefX, hfv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mulVec]

lemma coefX_add (D : Lifts H U X) (f f' : Nb p g → C) :
    coefX D (f + f') = coefX D f + coefX D f' := by
  simp only [coefX, Matrix.mulVec_add]

lemma coefX_smul (D : Lifts H U X) (c : C) (f : Nb p g → C) :
    coefX D (c • f) = c • coefX D f := by
  simp only [coefX, Matrix.mulVec_smul]

lemma xL_pow_mem (D : Lifts H U X) (hp : 2 ≤ p) (j : Ix g) :
    (fun y => xL D j y ^ p) ∈ sqIdeal (augIdeal H.AA.carrier) := by
  have hx : xL D j ∈ augIdeal H.AA.carrier := D.x_mem j
  have hxA : xL D j ∈ H.AA.carrier := hx.1
  have hx0 : xL D j 0 = 0 := hx.2
  have hpow : ∀ n : ℕ, xL D j ^ (n + 1) ∈ augIdeal H.AA.carrier := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      refine ⟨?_, ?_⟩
      · rw [pow_succ]
        exact H.AA.mul_mem _ _ ih.1 hxA
      · show (xL D j ^ (n + 1 + 1)) 0 = 0
        rw [Pi.pow_apply, hx0, zero_pow (by omega)]
  have heq : (fun y => xL D j y ^ p) = xL D j * xL D j ^ (p - 1 - 1 + 1) := by
    funext y
    rw [Pi.mul_apply, Pi.pow_apply, ← pow_succ']
    congr 1
    omega
  rw [heq]
  exact Submodule.subset_span ⟨_, hx, _, hpow _, rfl⟩

def blockEquiv (D : Lifts H U X) (τ : Fin U.m) :
    blockL D τ ≃ₗ[R] ({l // D.κ l = τ} → R) where
  toFun c l := c.1 l.1
  invFun d := ⟨fun k => if h : D.κ k = τ then d ⟨k, h⟩ else 0, fun k hk => by simp [hk]⟩
  left_inv c := by
    apply Subtype.ext
    funext k
    by_cases h : D.κ k = τ
    · simp [h]
    · simp [h, c.2 k h]
  right_inv d := by funext l; simp [l.2]
  map_add' c c' := rfl
  map_smul' r c := rfl

end FrobA

theorem frob_of (h1 : LiftMonomialDeterminantStatement) (h2 : FrobeniusBlockStatement) (h3 : FrobeniusLengthBoundStatement) :
    EigenLiftsFrobeniusStatement := by
  unfold EigenLiftsFrobeniusStatement
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hp2 hS H U X D hbasis i
  have hv := hS.integers
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdet := h1 p g C v R O σ cp hS H U X D
  obtain ⟨h2a, h2b⟩ := h2 p g C v R O σ cp hp2 hS H U X D
  have hsq : sqIdeal (augIdeal H.AA.carrier) ≤ H.AA.carrier := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, hf, f', hf', rfl⟩
    exact H.AA.mul_mem _ _ hf.1 hf'.1
  have hfS : ∀ j, (fun y => xL D j y ^ p) ∈ sqIdeal (augIdeal H.AA.carrier) :=
    fun j => xL_pow_mem D hp j
  have hrex : ∀ j : Ix g, ∃ r : Nb p g → R,
      coefX D (fun y => xL D j y ^ p) = algebraMap R C ∘ r :=
    fun j => coefX_int D hdet hbasis (hsq (hfS j))
  choose r hr using hrex
  let c : Ix g → Ix g → R := fun j k => if D.κ k = U.φ i then r j (Pi.single k 1) else 0
  have hc : ∀ j, D.κ j = i → ∀ k, algebraMap R C (c j k) = linX D (fun y => xL D j y ^ p) k := by
    intro j hj k
    by_cases hk : D.κ k = U.φ i
    · simp only [c, if_pos hk, linX, hr j, Function.comp_apply]
    · simp only [c, if_neg hk, map_zero]
      exact (h2a j k (by rw [hj]; exact hk)).symm
  have hcard : Fintype.card {j // D.κ j = i} = Fintype.card {l // D.κ l = U.φ i} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, D.card_phi i]
  let e'' : {j // D.κ j = i} ≃ {l // D.κ l = U.φ i} := Fintype.equivOfCardEq hcard
  let eτ : {l // D.κ l = U.φ i} ≃ Fin (Fintype.card {l // D.κ l = U.φ i}) := Fintype.equivFin _
  let σE : Fin (Fintype.card {l // D.κ l = U.φ i}) ≃ {j // D.κ j = i} := eτ.symm.trans e''.symm
  let Y : Matrix (Fin (Fintype.card {l // D.κ l = U.φ i})) (Fin (Fintype.card {l // D.κ l = U.φ i})) R :=
    fun a b => c (σE b).1 (eτ.symm a).1
  let Ψ : blockL D (U.φ i) ≃ₗ[R] (Fin (Fintype.card {l // D.κ l = U.φ i}) → R) :=
    (blockEquiv D (U.φ i)).trans (LinearEquiv.funCongrLeft R R eτ.symm)
  let N : Submodule R (Ix g → R) :=
    ((LinearMap.range Y.mulVecLin).comap Ψ.toLinearMap).map (blockL D (U.φ i)).subtype
  have hcomap : N.comap (blockL D (U.φ i)).subtype = (LinearMap.range Y.mulVecLin).comap Ψ.toLinearMap :=
    Submodule.comap_map_eq_of_injective (blockL D (U.φ i)).injective_subtype _
  have hmapΨ : ((LinearMap.range Y.mulVecLin).comap Ψ.toLinearMap).map Ψ.toLinearMap = LinearMap.range Y.mulVecLin :=
    Submodule.map_comap_eq_of_surjective Ψ.surjective _
  have hlen : HasLen v R (blockL D (U.φ i) ⧸ N.comap (blockL D (U.φ i)).subtype)
      (v (algebraMap R C Y.det)) := by
    rw [hcomap]
    exact hasLen_of_linearEquiv (Submodule.Quotient.equiv _ _ Ψ hmapΨ) (Smith.hasLen_coker_det hv Y)
  have hNle : N ≤ blockL D (U.φ i) := Submodule.map_subtype_le _ _
  have hreal : ∀ x ∈ N, ∃ f ∈ sqIdeal (augIdeal H.AA.carrier),
      ∀ k, algebraMap R C (x k) = linX D f k := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp (Submodule.mem_comap.mp hy)
    refine ⟨∑ b, w b • (fun t => xL D (σE b).1 t ^ p),
      Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hfS _), ?_⟩
    intro k
    have hyΨ : y = Ψ.symm (Y.mulVecLin w) := by rw [hw]; exact (Ψ.symm_apply_apply y).symm
    have hyk : (y : Ix g → R) k = ∑ b, c (σE b).1 k * w b := by
      rw [hyΨ]
      by_cases h : D.κ k = U.φ i
      · show (if h' : D.κ k = U.φ i then (Y.mulVecLin w) (eτ ⟨k, h'⟩) else 0) = _
        rw [dif_pos h]
        show ∑ b, Y (eτ ⟨k, h⟩) b * w b = _
        simp only [Y, Equiv.symm_apply_apply]
      · show (if h' : D.κ k = U.φ i then (Y.mulVecLin w) (eτ ⟨k, h'⟩) else 0) = _
        rw [dif_neg h]
        simp [c, h]
    show algebraMap R C ((y : Ix g → R) k) = _
    rw [hyk, map_sum]
    simp only [linX, coefX, Matrix.mulVec_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← algebraMap_smul C (w b), Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul,
      mul_comm]
    congr 1
    exact hc (σE b).1 (σE b).2 k
  have hYdet : v (algebraMap R C Y.det) = X i ^ p / X (U.φ i) := by
    rw [RingHom.map_det]
    have hYZ : (algebraMap R C).mapMatrix Y = (Matrix.of fun j l : {j // D.κ j = i} =>
        linX D (fun y => xL D j.1 y ^ p) (e'' l).1)ᵀ.submatrix σE σE := by
      ext a b
      show algebraMap R C (c (σE b).1 (eτ.symm a).1) =
        linX D (fun y => xL D (σE b).1 y ^ p) (e'' (σE a)).1
      rw [hc (σE b).1 (σE b).2]
      simp [σE]
    rw [hYZ, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
    exact h2b i e''
  have hz := h3 p g C v R O σ cp hp2 hS H U X D hdet hbasis (U.φ i) N _ hNle hreal hlen
  rw [hYdet] at hz
  have hXne : X (U.φ i) ≠ 0 := by
    rw [← D.ε_prod (U.φ i)]
    exact Finset.prod_ne_zero_iff.mpr fun j _ =>
      (Valuation.ne_zero_iff v).mpr ((map_ne_zero_iff _ hinj).mpr (D.ε_ne j))
  rw [div_le_iff₀ (pos_iff_ne_zero.mpr hXne)] at hz
  exact hz.trans_eq (mul_comm _ _)

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.MatEquivApply
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

variable {R : Type} [CommRing R]

def matEquiv {d : ℕ} (P : Matrix (Fin d) (Fin d) R) (hP : IsUnit P.det) :
    (Fin d → R) ≃ₗ[R] (Fin d → R) :=
  LinearEquiv.ofLinear (Matrix.toLin' P) (Matrix.toLin' P⁻¹)
    (by rw [← Matrix.toLin'_mul, mul_nonsing_inv _ hP, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, nonsing_inv_mul _ hP, Matrix.toLin'_one])

lemma matEquiv_apply {d : ℕ} (P : Matrix (Fin d) (Fin d) R) (hP : IsUnit P.det) (x : Fin d → R) :
    matEquiv P hP x = P *ᵥ x := by
  show Matrix.toLin' P x = P *ᵥ x
  rw [Matrix.toLin'_apply]

lemma sum_val_eq {n : ℕ} (j : ℕ) (f : Fin n → R) :
    ∑ k : Fin n, (if (k : ℕ) = j then f k else 0) = if h : j < n then f ⟨j, h⟩ else 0 := by
  split_ifs with h
  · rw [Fintype.sum_eq_single ⟨j, h⟩ (fun k hk => if_neg fun h' => hk (Fin.ext h'))]
    exact if_pos rfl
  · exact Finset.sum_eq_zero fun k _ => if_neg fun (h' : (k : ℕ) = j) => h (h' ▸ k.isLt)

lemma hasLen_pi {C : Type} [Field C] (v : Valuation C NNReal) [Algebra R C] {d : ℕ} (a : Fin d → R) :
    HasLen v R ((Fin d → R) ⧸ Submodule.pi Set.univ (fun j => (Ideal.span {a j} : Submodule R R)))
      (∏ j, v (algebraMap R C (a j))) :=
  ⟨d, a, ⟨Submodule.quotientPi _⟩, rfl⟩

private lemma hasLen_of_linearEquiv' {C : Type} [Field C] {v : Valuation C NNReal} [Algebra R C]
    {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] {x : NNReal}
    (h : HasLen v R M x) (e : M ≃ₗ[R] M') : HasLen v R M' x := by
  obtain ⟨m, c, ⟨e0⟩, hc⟩ := h
  exact ⟨m, c, ⟨e.symm.trans e0⟩, hc⟩

theorem dualLen_fin {C : Type} [Field C] {v : Valuation C NNReal} [Algebra R C]
    (hv : v.Integers R) {d n : ℕ} (A : Matrix (Fin d) (Fin n) R) (c : R) (hc : c ≠ 0)
    (hkill : ∀ w : Fin d → R, ∃ t, A *ᵥ t = c • w) {c₁ : NNReal}
    (hc₁ : HasLen v R ((Fin d → R) ⧸ LinearMap.range A.mulVecLin) c₁) :
    ∃ y : NNReal, HasLen v R ((Fin d → R) ⧸ zSub A c) y ∧ y * c₁ = v (algebraMap R C c) ^ d := by
  classical
  obtain ⟨P, Q, a, hP, hQ, hD⟩ := Smith.smith_mat hv d n A
  have hPQ : ∀ t : Fin n → R, (P * A * Q) *ᵥ (Q⁻¹ *ᵥ t) = P *ᵥ (A *ᵥ t) := by
    intro t
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (P * A), Matrix.mul_nonsing_inv _ hQ,
      Matrix.mul_one, ← Matrix.mulVec_mulVec]
  have hDv : ∀ (s : Fin n → R) (j : Fin d),
      ((P * A * Q) *ᵥ s) j = if h : (j : ℕ) < n then a j * s ⟨j, h⟩ else 0 := by
    intro s j
    have h1 := sum_val_eq (j : ℕ) (fun k => a j * s k)
    rw [← h1]
    simp only [Matrix.mulVec, dotProduct, hD, ite_mul, zero_mul]
  have hDt : ∀ (y : Fin d → R) (k : Fin n),
      ((P * A * Q)ᵀ *ᵥ y) k = if h : (k : ℕ) < d then a ⟨k, h⟩ * y ⟨k, h⟩ else 0 := by
    intro y k
    have h1 := sum_val_eq (k : ℕ) (fun j => a j * y j)
    rw [← h1]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hD, ite_mul, zero_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : (k : ℕ) = (j : ℕ)
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  have hdiv : ∀ j : Fin d, (j : ℕ) < n ∧ ∃ b, a j * b = c := by
    intro j
    obtain ⟨t, ht⟩ := hkill (P⁻¹ *ᵥ Pi.single j 1)
    have h1 : (P * A * Q) *ᵥ (Q⁻¹ *ᵥ t) = c • Pi.single j 1 := by
      rw [hPQ, ht, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP,
        Matrix.one_mulVec]
    have h2 := congrFun h1 j
    rw [hDv] at h2
    by_cases h : (j : ℕ) < n
    · rw [dif_pos h] at h2
      exact ⟨h, (Q⁻¹ *ᵥ t) ⟨j, h⟩, by simpa using h2⟩
    · rw [dif_neg h] at h2
      have h3 : c = 0 := by simpa using h2.symm
      exact absurd h3 hc
  choose hlt b hb using hdiv
  have ha0 : ∀ j, a j ≠ 0 := fun j h => hc (by rw [← hb j, h, zero_mul])
  have hcancel : ∀ j (x z : R), a j * x = a j * z → x = z := by
    intro j x z h
    apply hv.hom_inj
    have h' := congrArg (algebraMap R C) h
    rw [map_mul, map_mul] at h'
    have hne : algebraMap R C (a j) ≠ 0 := by
      intro h0
      apply ha0 j
      apply hv.hom_inj
      rw [h0, map_zero]
    exact mul_left_cancel₀ hne h'
  have e1 : ((Fin d → R) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[R]
      ((Fin d → R) ⧸ Submodule.pi Set.univ (fun j => (Ideal.span {a j} : Submodule R R))) := by
    refine Submodule.Quotient.equiv _ _ (matEquiv P hP) ?_
    ext x
    rw [Submodule.mem_map, Submodule.mem_pi]
    constructor
    · rintro ⟨y, hy, rfl⟩ j -
      obtain ⟨t, rfl⟩ := LinearMap.mem_range.mp hy
      rw [Ideal.mem_span_singleton']
      refine ⟨(Q⁻¹ *ᵥ t) ⟨j, hlt j⟩, ?_⟩
      simp only [LinearEquiv.coe_coe, matEquiv_apply, Matrix.mulVecLin_apply]
      rw [← hPQ, hDv, dif_pos (hlt j), mul_comm]
    · intro hx
      have hx' : ∀ j, ∃ s, s * a j = x j := fun j =>
        Ideal.mem_span_singleton'.mp (hx j (Set.mem_univ _))
      choose s hs using hx'
      refine ⟨A *ᵥ (Q *ᵥ fun k => if h : (k : ℕ) < d then s ⟨k, h⟩ else 0),
        LinearMap.mem_range.mpr ⟨_, rfl⟩, ?_⟩
      simp only [LinearEquiv.coe_coe, matEquiv_apply]
      funext j
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hDv, dif_pos (hlt j)]
      show a j * (if h : (j : ℕ) < d then s ⟨j, h⟩ else 0) = x j
      rw [dif_pos j.isLt, mul_comm]
      exact hs j
  have hT : ∀ x : Fin d → R, (P * A * Q)ᵀ *ᵥ x = Qᵀ *ᵥ (Aᵀ *ᵥ (Pᵀ *ᵥ x)) := by
    intro x
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  have e2 : ((Fin d → R) ⧸ zSub A c) ≃ₗ[R]
      ((Fin d → R) ⧸ Submodule.pi Set.univ (fun j => (Ideal.span {b j} : Submodule R R))) := by
    have hPt : IsUnit Pᵀ.det := by rwa [Matrix.det_transpose]
    refine Submodule.Quotient.equiv _ _ (matEquiv Pᵀ hPt).symm ?_
    ext x
    rw [Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm, Submodule.mem_comap,
      Submodule.mem_pi]
    show (∃ z, Aᵀ *ᵥ ((matEquiv Pᵀ hPt) x) = c • z) ↔ _
    rw [matEquiv_apply]
    constructor
    · rintro ⟨z, hz⟩ j -
      have h1 : (P * A * Q)ᵀ *ᵥ x = c • (Qᵀ *ᵥ z) := by rw [hT, hz, Matrix.mulVec_smul]
      have h2 := congrFun h1 ⟨j, hlt j⟩
      rw [hDt, dif_pos j.isLt, Pi.smul_apply, smul_eq_mul] at h2
      rw [Ideal.mem_span_singleton']
      refine ⟨(Qᵀ *ᵥ z) ⟨j, hlt j⟩, hcancel j _ _ ?_⟩
      rw [mul_comm ((Qᵀ *ᵥ z) _) (b j), ← mul_assoc, hb j]
      exact h2.symm
    · intro hx
      have hx' : ∀ j, ∃ s, s * b j = x j := fun j =>
        Ideal.mem_span_singleton'.mp (hx j (Set.mem_univ _))
      choose s hs using hx'
      have h1 : (P * A * Q)ᵀ *ᵥ x =
          c • (fun k : Fin n => if h : (k : ℕ) < d then s ⟨k, h⟩ else 0) := by
        funext k
        rw [hDt, Pi.smul_apply, smul_eq_mul]
        by_cases h : (k : ℕ) < d
        · rw [dif_pos h, dif_pos h, ← hs ⟨k, h⟩, ← hb ⟨k, h⟩]
          ring
        · rw [dif_neg h, dif_neg h, mul_zero]
      refine ⟨(Q⁻¹)ᵀ *ᵥ (fun k : Fin n => if h : (k : ℕ) < d then s ⟨k, h⟩ else 0), ?_⟩
      calc Aᵀ *ᵥ (Pᵀ *ᵥ x) = (Q⁻¹)ᵀ *ᵥ ((P * A * Q)ᵀ *ᵥ x) := by
            rw [hT, Matrix.mulVec_mulVec (M := (Q⁻¹)ᵀ) (N := Qᵀ), ← Matrix.transpose_mul,
              Matrix.mul_nonsing_inv _ hQ,
              Matrix.transpose_one, Matrix.one_mulVec]
        _ = _ := by rw [h1, Matrix.mulVec_smul]
  have hA1 : HasLen v R ((Fin d → R) ⧸ LinearMap.range A.mulVecLin)
      (∏ j, v (algebraMap R C (a j))) := hasLen_of_linearEquiv' (hasLen_pi v a) e1.symm
  have hc1 := hasLen_unique hv hc₁ hA1
  refine ⟨∏ j, v (algebraMap R C (b j)), hasLen_of_linearEquiv' (hasLen_pi v b) e2.symm, ?_⟩
  rw [hc1, ← Finset.prod_mul_distrib]
  simp_rw [← map_mul, mul_comm (b _) (a _), hb]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem dualLen : DualLenStatement := by
  intro C _ v R _ _ hv d κ _ _ A c hc hkill c₁ hc₁
  classical
  let e := Fintype.equivFin κ
  let A' : Matrix (Fin d) (Fin (Fintype.card κ)) R := A.submatrix id e.symm
  have hmv : ∀ t : Fin (Fintype.card κ) → R, A' *ᵥ t = A *ᵥ (t ∘ e) := by
    intro t
    funext i
    simp only [Matrix.mulVec, dotProduct]
    exact (Fintype.sum_equiv e (fun j => A i j * t (e j)) _ (fun j => by simp [A'])).symm
  have hmv' : ∀ y : Fin d → R, A'ᵀ *ᵥ y = (Aᵀ *ᵥ y) ∘ e.symm := fun y => by funext k; rfl
  have hrange : LinearMap.range A'.mulVecLin = LinearMap.range A.mulVecLin := by
    ext x
    simp only [LinearMap.mem_range, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t ∘ e, (hmv t).symm⟩
    · rintro ⟨t, rfl⟩
      refine ⟨t ∘ e.symm, ?_⟩
      rw [hmv]
      congr 1
      funext j
      simp
  have hz : zSub A' c = zSub A c := by
    ext y
    show (∃ z, A'ᵀ *ᵥ y = c • z) ↔ (∃ z, Aᵀ *ᵥ y = c • z)
    rw [hmv']
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z ∘ e, ?_⟩
      funext j
      have h1 := congrFun hz (e j)
      simpa using h1
    · rintro ⟨z, hz⟩
      refine ⟨z ∘ e.symm, ?_⟩
      rw [hz]
      rfl
  have hk : ∀ w : Fin d → R, ∃ t, A' *ᵥ t = c • w := by
    intro w
    obtain ⟨t, ht⟩ := hkill w
    have h1 : (t ∘ e.symm) ∘ e = t := by funext j; simp
    exact ⟨t ∘ e.symm, by rw [hmv, h1, ht]⟩
  have hc₁' : HasLen v R ((Fin d → R) ⧸ LinearMap.range A'.mulVecLin) c₁ := by
    rw [hrange]; exact hc₁
  obtain ⟨y, hy, hyc⟩ := dualLen_fin hv A' c hc hk hc₁'
  rw [hz] at hy
  exact ⟨y, hy, hyc⟩

theorem lenId : LenIdStatement := lenId_of_B (lenIdB_of dualLen)

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.NsmulKerZero
section
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace ATower

variable {p : ℕ} (Tw : ATower R₀ p)

lemma ξmul_surj (n : ℕ) : Function.Surjective (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) := by
  rintro ⟨k, hk⟩
  have hk' : k ∈ Ideal.span {Tw.ξ n} := by
    rw [← Tw.ker_eq n]
    simpa using hk
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hk'
  refine ⟨a, Subtype.ext ?_⟩
  show Tw.ξ n * a = k
  rw [← ha, mul_comm]

lemma exists_factor (n : ℕ) : ∃ g' : (Tw.π n).ker →ₗ[R₀] (Tw.R n : Type u),
    g' ∘ₗ ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n) = (Tw.π n).1.toLinearMap := by
  have hle : LinearMap.ker (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) ≤
      LinearMap.ker (Tw.π n).1.toLinearMap := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    have h0 : Tw.ξ n * a = 0 := congrArg Subtype.val ha
    have hm : a ∈ Ideal.span {Tw.ξ n} := Tw.ann n a (by rw [mul_comm]; exact h0)
    rw [← Tw.ker_eq n, RingHom.mem_ker] at hm
    exact hm
  have hs := Tw.ξmul_surj n
  refine ⟨(LinearMap.ker _).liftQ _ hle ∘ₗ
    (LinearMap.quotKerEquivOfSurjective _ hs).symm.toLinearMap, ?_⟩
  refine LinearMap.ext fun a => ?_
  have h1 : (LinearMap.quotKerEquivOfSurjective _ hs).symm (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n) a) =
      Submodule.Quotient.mk a := by
    rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h1, Submodule.liftQ_apply]

end ATower

namespace BX

variable (B : BX R₀) {p : ℕ}

lemma nsmul_ker_zero (Tw : ATower R₀ p) (n : ℕ) (V : B.gg ⊗[R₀] (Tw.π n).ker) :
    (p ^ (n + 1)) • V = 0 := by
  have hc : ((p : (Tw.R' n : Type u))) ^ (n + 1) = 0 := by exact_mod_cast Tw.char n
  induction V using TensorProduct.induction_on with
  | zero => simp
  | tmul g k =>
    have hk : (p ^ (n + 1)) • k = 0 := by
      apply Subtype.ext
      simp [nsmul_eq_mul, hc]
    rw [← TensorProduct.tmul_smul, hk, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

lemma exists_lift (Tw : ATower R₀ p) (n : ℕ) (y : B.G (Tw.R n)) (hy : (p ^ (n + 1)) • y = 0) :
    ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)), B.map (Tw.π n) th = y ∧
      (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
        (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) := by
  obtain ⟨th, hth⟩ := B.surj (Tw.π n) (Tw.sqZero n) y
  have h0 : B.map (Tw.π n) ((p ^ (n + 1)) • th) = 0 := by rw [map_nsmul, hth, hy]
  obtain ⟨v, hv⟩ := (B.tg_ker (Tw.π n) (Tw.sqZero n) _).1 h0
  obtain ⟨w, hw⟩ := LinearMap.lTensor_surjective B.gg (Tw.ξmul_surj n) v
  exact ⟨th, w, hth, by rw [← hv, ← hw]; rfl⟩

lemma lift_indep (Tw : ATower R₀ p) (n : ℕ) (th th' : B.G (Tw.R' n)) (w w' : B.gg ⊗[R₀] (Tw.R' n : Type u))
    (he : B.map (Tw.π n) th = B.map (Tw.π n) th')
    (hw : (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
      (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w))
    (hw' : (p ^ (n + 1)) • th' = B.tg (Tw.π n) (Tw.sqZero n)
      (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w')) :
    LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w = LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w' := by
  have hd : B.map (Tw.π n) (th - th') = 0 := by rw [map_sub, he, sub_self]
  obtain ⟨v0, hv0⟩ := (B.tg_ker (Tw.π n) (Tw.sqZero n) _).1 hd
  have hp : (p ^ (n + 1)) • th = (p ^ (n + 1)) • th' := by
    have h : (p ^ (n + 1)) • (th - th') = 0 := by
      rw [← hv0, ← map_nsmul, B.nsmul_ker_zero Tw n v0, map_zero]
    rwa [smul_sub, sub_eq_zero] at h
  rw [hw, hw'] at hp
  have hx := B.tg_inj (Tw.π n) (Tw.sqZero n) hp
  obtain ⟨g', hg'⟩ := Tw.exists_factor n
  rw [← hg', LinearMap.lTensor_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  exact congrArg (LinearMap.lTensor B.gg g') hx

end BX

end ReciprocityTheory.PGsh
end
end

