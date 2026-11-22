import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ReInnerLeOnImageOfIntertwining
section
open Finset
open scoped InnerProductSpace

namespace GlobalTheory

theorem re_inner_sum_eigen_le {N ι : Type} [NormedAddCommGroup N] [InnerProductSpace ℂ N]
    [Fintype ι] (B : N →ₗ[ℂ] N) (hB : B.IsSymmetric) (C : ℝ) (v : ι → N) (l : ι → ℝ)
    (hv : ∀ i, B (v i) = (l i : ℂ) • v i) (hl : ∀ i, l i ≤ C) :
    (⟪∑ i, v i, B (∑ i, v i)⟫_ℂ).re ≤ C * ‖∑ i, v i‖ ^ 2 := by
  have key : ∀ i j, ((C : ℂ) - l j) * ⟪v i, v j⟫_ℂ =
      ⟪((√(C - l i) : ℝ) : ℂ) • v i, ((√(C - l j) : ℝ) : ℂ) • v j⟫_ℂ := by
    intro i j
    rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc]
    by_cases h : l i = l j
    · rw [h, ← Complex.ofReal_mul, Real.mul_self_sqrt (sub_nonneg.2 (hl j))]
      push_cast
      rfl
    · have h1 := hB (v i) (v j)
      rw [hv, hv, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
      have h2 : ((l i : ℂ) - l j) * ⟪v i, v j⟫_ℂ = 0 := by rw [sub_mul, h1, sub_self]
      have h3 : ((l i : ℂ) - l j) ≠ 0 := by
        rw [sub_ne_zero]; exact_mod_cast h
      have h4 : ⟪v i, v j⟫_ℂ = 0 := (mul_eq_zero.1 h2).resolve_left h3
      rw [h4, mul_zero, mul_zero]
  have hsum : (C : ℂ) * ⟪∑ i, v i, ∑ i, v i⟫_ℂ - ⟪∑ i, v i, B (∑ i, v i)⟫_ℂ =
      ⟪∑ i, ((√(C - l i) : ℝ) : ℂ) • v i, ∑ i, ((√(C - l i) : ℝ) : ℂ) • v i⟫_ℂ := by
    rw [map_sum]
    simp only [sum_inner, inner_sum, ← key, hv, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_right, sub_mul]
  have hre := congrArg Complex.re hsum
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hre
  simp only [Complex.coe_algebraMap, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.sub_re, Complex.ofReal_re] at hre
  nlinarith [sq_nonneg ‖∑ i, ((√(C - l i) : ℝ) : ℂ) • v i‖]

theorem re_inner_le_on_image_of_intertwining :
    ∀ (T N : Type) [NormedAddCommGroup T] [InnerProductSpace ℂ T] [FiniteDimensional ℂ T]
      [NormedAddCommGroup N] [InnerProductSpace ℂ N] (Φ : T →ₗ[ℂ] N) (A : T →ₗ[ℂ] T)
      (B : N →ₗ[ℂ] N) (C : ℝ), A.IsSymmetric → B.IsSymmetric → (∀ x, Φ (A x) = B (Φ x)) →
      (∀ x, (⟪x, A x⟫_ℂ).re ≤ C * ‖x‖ ^ 2) →
      ∀ x, (⟪Φ x, B (Φ x)⟫_ℂ).re ≤ C * ‖Φ x‖ ^ 2 := by
  intro T N _ _ _ _ _ Φ A B C hA hB hΦ hC x
  set b := hA.eigenvectorBasis (n := Module.finrank ℂ T) rfl with hb
  set l := hA.eigenvalues (n := Module.finrank ℂ T) rfl with hl
  have hAb : ∀ i, A (b i) = (l i : ℂ) • b i := fun i => hA.apply_eigenvectorBasis rfl i
  have hle : ∀ i, l i ≤ C := by
    intro i
    have h := hC (b i)
    rw [hAb, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i] at h
    simpa using h
  have hx : Φ x = ∑ i, Φ (b.repr x i • b i) := by
    rw [← map_sum, b.sum_repr]
  rw [hx]
  refine re_inner_sum_eigen_le B hB C _ l (fun i => ?_) hle
  rw [← hΦ, map_smul A, hAb, smul_comm, map_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SideSucc
section
open Finset

namespace GlobalTheory.CloudProd

theorem side_succ (c : ℝ) (δ : ℕ → ℝ) (hc : 1 ≤ c) (n : ℕ)
    (h : ∀ j : ℕ, j < n + 1 → 2 * c * (j : ℝ) ≤ δ j) :
    ∏ j ∈ Finset.range (n + 1), (1 + (1 + c) / max (δ j) 1) ≤ (2 + c) * ((n : ℝ) + 1) := by
  induction n with
  | zero =>
    have h1 : (1 + c) / max (δ 0) 1 ≤ 1 + c :=
      div_le_self (by linarith) (le_max_right _ _)
    simp only [zero_add, Finset.prod_range_one, Nat.cast_zero, mul_one]
    linarith
  | succ m ih =>
    rw [Finset.prod_range_succ]
    have ih' := ih (fun j hj => h j (by omega))
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hd := h (m + 1) (by omega)
    push_cast at hd ⊢
    have hmax : (1 + c) * ((m : ℝ) + 1) ≤ max (δ (m + 1)) 1 := by
      refine le_trans ?_ (le_trans hd (le_max_left _ _))
      nlinarith
    have hpos : (0 : ℝ) < max (δ (m + 1)) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hf : (1 + c) / max (δ (m + 1)) 1 ≤ 1 / ((m : ℝ) + 1) := by
      rw [div_le_div_iff₀ hpos (by linarith)]
      linarith
    have hf0 : 0 ≤ 1 + (1 + c) / max (δ (m + 1)) 1 := by positivity
    calc _ ≤ ((2 + c) * ((m : ℝ) + 1)) * (1 + 1 / ((m : ℝ) + 1)) :=
          mul_le_mul ih' (by linarith) hf0 (by positivity)
      _ = (2 + c) * ((m : ℝ) + 1 + 1) := by field_simp

theorem side (c : ℝ) (δ : ℕ → ℝ) (hc : 1 ≤ c) (n : ℕ)
    (h : ∀ j : ℕ, j < n → 2 * c * (j : ℝ) ≤ δ j) :
    ∏ j ∈ Finset.range n, (1 + (1 + c) / max (δ j) 1) ≤ (2 + c) * ((n : ℝ) + 1) := by
  cases n with
  | zero => simp; linarith
  | succ m =>
    refine (side_succ c δ hc m h).trans ?_
    push_cast
    nlinarith

theorem main : ∀ (k : ℕ) (c y : ℝ) (lam : ℕ → ℝ), 1 ≤ k → 1 ≤ c → (∀ s : ℕ, 1 ≤ s → s + 1 ≤ k - 1 → lam (s + 1) + 2 * c ≤ lam s) → ∏ s ∈ Finset.Icc 1 (k - 1), (1 + (1 + c) / max |lam s - y| 1) ≤ ((2 + c) * (k : ℝ)) ^ 2 := by
  intro k c y lam hk hc hstep
  classical
  have mono : ∀ s d : ℕ, 1 ≤ s → s + d ≤ k - 1 → lam (s + d) + 2 * c * (d : ℝ) ≤ lam s := by
    intro s d hs
    induction d with
    | zero => intro _; simp
    | succ e ih =>
      intro hle
      have h1 := ih (by omega)
      have h2 := hstep (s + e) (by omega) (by omega)
      rw [← add_assoc]
      push_cast
      linarith
  obtain ⟨p, hp, hup, hlo⟩ : ∃ p : ℕ, p ≤ k - 1 ∧ (p ≠ 0 → y < lam p) ∧
      (p + 1 ≤ k - 1 → lam (p + 1) ≤ y) := by
    refine ⟨Nat.findGreatest (fun s => y < lam s) (k - 1), Nat.findGreatest_le _, ?_, ?_⟩
    · intro h0
      exact Nat.findGreatest_of_ne_zero (P := fun s => y < lam s) rfl h0
    · intro h1
      exact not_lt.mp (Nat.findGreatest_is_greatest (P := fun s => y < lam s)
        (Nat.lt_succ_self _) h1)
  have hI : Finset.Icc 1 (k - 1) = Finset.Ico 1 k := by
    ext s; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hI, ← Finset.prod_Ico_consecutive _ (show 1 ≤ p + 1 by omega) (show p + 1 ≤ k by omega),
    Finset.prod_Ico_eq_prod_range, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel,
    ← Finset.prod_range_reflect]
  have hA := side c (fun j => |lam (1 + (p - 1 - j)) - y|) hc p (by
    intro j hj
    have h1 := mono (1 + (p - 1 - j)) j (by omega) (by omega)
    rw [show 1 + (p - 1 - j) + j = p by omega] at h1
    have h2 := hup (by omega)
    refine le_trans ?_ (le_abs_self _)
    linarith)
  have hB := side c (fun j => |lam (p + 1 + j) - y|) hc (k - (p + 1)) (by
    intro j hj
    have h1 := mono (p + 1) j (by omega) (by omega)
    have h2 := hlo (by omega)
    refine le_trans ?_ (neg_le_abs _)
    linarith)
  have e1 : ((p : ℝ) + 1) ≤ k := by exact_mod_cast (show p + 1 ≤ k by omega)
  have e2 : (((k - (p + 1) : ℕ) : ℝ) + 1) ≤ k := by
    exact_mod_cast (show k - (p + 1) + 1 ≤ k by omega)
  have hc2 : (0 : ℝ) ≤ 2 + c := by linarith
  rw [sq]
  refine mul_le_mul (hA.trans (mul_le_mul_of_nonneg_left e1 hc2))
    (hB.trans (mul_le_mul_of_nonneg_left e2 hc2)) ?_ (by positivity)
  exact Finset.prod_nonneg (fun j _ => by positivity)

end GlobalTheory.CloudProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumPosOfTensorPos
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PointStepCompare

open NumberField Matrix
open scoped MatrixOrder

section Evaluations

variable {Y : Type} [AddCommGroup Y] {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Y)

def evalOn (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) : (ι × ι → ℤ) →ₗ[ℤ] ℝ where
  toFun n := ∑ p, (n p : ℝ) * B (b p.1) (b p.2)
  map_add' n n' := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' k n := by simp [Finset.mul_sum, mul_assoc]

def tensorCoord : Y →ₗ[ℤ] Y →ₗ[ℤ] (ι × ι → ℤ) :=
  LinearMap.mk₂ ℤ (fun x y p => b.repr x p.1 * b.repr y p.2)
    (fun _ _ _ => by funext p; simp [add_mul]) (fun _ _ _ => by funext p; simp [mul_assoc])
    (fun _ _ _ => by funext p; simp [mul_add]) (fun _ _ _ => by funext p; simp [mul_left_comm])

theorem evalOn_tensorCoord (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x y : Y) :
    evalOn b B (tensorCoord b x y) = B x y := by
  conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
  change ∑ p : ι × ι, ((b.repr x p.1 * b.repr y p.2 : ℤ) : ℝ) * B (b p.1) (b p.2) = _
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    Fintype.sum_prod_type, Int.cast_mul, zsmul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Evaluations

theorem exists_eq_sum_eval : ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (S : Submodule ℝ (Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)), (∀ γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ, (∀ a b c d : Y, (∀ β ∈ S, β a b = β c d) → γ a b = γ c d) → γ ∈ S) → ∀ l : S →ₗ[ℝ] ℝ, (∀ β : S, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l β = z) → ∃ (m : ℕ) (x x' : Fin m → Y), ∀ β : S, l β = ∑ i, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x i) (x' i) := by
  intro Y _ _ _ S hS l hl
  classical
  let b := Module.Free.chooseBasis ℤ Y
  let A : Submodule ℤ (_ × _ → ℤ) := ⨅ β : S, LinearMap.ker (evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ))
  have hA : ∀ n, n ∈ A ↔ ∀ β : S, evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) n = 0 := fun n => by
    simp [A, Submodule.mem_iInf]
  have : NoZeroSMulDivisors ℤ ((_ × _ → ℤ) ⧸ A) := by
    refine ⟨fun {k q} h => ?_⟩
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    by_cases hk : k = 0
    · exact Or.inl hk
    right
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hA] at h
    rw [Submodule.Quotient.mk_eq_zero, hA]
    intro β
    have h1 := h β
    rw [map_zsmul, zsmul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left (by exact_mod_cast hk)
  have : Module.Free ℤ ((_ × _ → ℤ) ⧸ A) := Module.free_of_finite_type_torsion_free'
  let eb := Module.Free.chooseBasis ℤ ((_ × _ → ℤ) ⧸ A)
  let γ : Module.Free.ChooseBasisIndex ℤ ((_ × _ → ℤ) ⧸ A) → Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ := fun k =>
    (tensorCoord b).compr₂ ((Int.castAddHom ℝ).toIntLinearMap ∘ₗ eb.coord k ∘ₗ A.mkQ)
  have hγ : ∀ k x y, γ k x y = (eb.repr (Submodule.Quotient.mk (tensorCoord b x y)) k : ℤ) :=
    fun _ _ _ => rfl
  have hγS : ∀ k, γ k ∈ S := fun k => hS _ fun x y x' y' h => by
    have e : Submodule.Quotient.mk (p := A) (tensorCoord b x y) =
        Submodule.Quotient.mk (tensorCoord b x' y') := (Submodule.Quotient.eq A).2 ((hA _).2 fun β => by
      rw [map_sub, evalOn_tensorCoord, evalOn_tensorCoord, h β β.2, sub_self])
    rw [hγ, hγ, e]
  choose z hz using fun k => hl ⟨γ k, hγS k⟩ fun x y => ⟨_, hγ k x y⟩
  obtain ⟨n, hn⟩ := Submodule.Quotient.mk_surjective A (∑ k, z k • eb k)
  let e := (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ Y × Module.Free.ChooseBasisIndex ℤ Y)).symm
  refine ⟨_, fun t => n (e t) • b (e t).1, fun t => b (e t).2, fun β => ?_⟩
  have hR : ∑ t, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (n (e t) • b (e t).1) (b (e t).2) =
      evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) n := by
    rw [e.sum_comp (fun p => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (n p • b p.1) (b p.2))]
    simp [evalOn, zsmul_eq_mul]
  rw [hR]
  let ψ := A.liftQ (evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ)) (iInf_le _ β)
  have hψ : ∀ m, ψ (Submodule.Quotient.mk m) = evalOn b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) m := fun m =>
    Submodule.liftQ_apply _ _ _
  have hβ : β = ∑ k, ψ (eb k) • (⟨γ k, hγS k⟩ : S) := by
    apply Subtype.ext
    apply LinearMap.ext₂
    intro x y
    rw [Submodule.coe_sum, LinearMap.sum_apply, LinearMap.sum_apply]
    simp only [Submodule.coe_smul, LinearMap.smul_apply, hγ, smul_eq_mul]
    rw [← evalOn_tensorCoord b (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) x y, ← hψ]
    conv_lhs => rw [← eb.sum_repr (Submodule.Quotient.mk (tensorCoord b x y))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, zsmul_eq_mul, mul_comm]
  rw [congrArg l hβ, map_sum, ← hψ, hn, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, hz, smul_eq_mul, map_zsmul, zsmul_eq_mul, mul_comm]

theorem posSemidef_of_int {ι : Type} [Fintype ι] {N : Matrix ι ι ℝ} (hH : N.IsHermitian)
    (hp : ∀ x : ι → ℤ, 0 ≤ (fun i => (x i : ℝ)) ⬝ᵥ N *ᵥ (fun i => (x i : ℝ))) : N.PosSemidef := by
  have hq : ∀ x : ι → ℚ, 0 ≤ (fun i => (x i : ℝ)) ⬝ᵥ N *ᵥ (fun i => (x i : ℝ)) := by
    intro x
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) x
    choose y hy using hd
    have hd0 : ((d : ℤ) : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero d
    have hxy : (fun i => (y i : ℝ)) = ((d : ℤ) : ℝ) • (fun i => (x i : ℝ)) := by
      funext i
      have := congrArg (fun q : ℚ => (q : ℝ)) (hy i)
      simpa [Submonoid.smul_def] using this
    have h1 := hp y
    rw [hxy, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc] at h1
    exact nonneg_of_mul_nonneg_right h1 (mul_self_pos.2 hd0)
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨hH, fun x => ?_⟩
  have hd : DenseRange (Pi.map fun (_ : ι) => (Rat.cast : ℚ → ℝ)) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  refine hd.induction_on (p := fun x => 0 ≤ star x ⬝ᵥ N *ᵥ x) x ?_ (fun q => ?_)
  · exact isClosed_le continuous_const (by fun_prop)
  · exact hq q

theorem posDef_of_int {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ) (hs : ∀ i j, M i j = M j i)
    (hp : ∀ x : ι → ℤ, x ≠ 0 → 0 < x ⬝ᵥ M *ᵥ x) :
    M.det ≠ 0 ∧ (M.map (Int.cast : ℤ → ℝ)).PosDef := by
  have hd : M.det ≠ 0 := fun h => by
    obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    simpa [h0] using hp v hv
  have h1 : (M.map (Int.cast : ℤ → ℝ)).PosSemidef := by
    refine posSemidef_of_int (by ext i j; simp [hs i j]) fun x => ?_
    have : (fun i => (x i : ℝ)) ⬝ᵥ M.map (Int.cast : ℤ → ℝ) *ᵥ (fun i => (x i : ℝ)) =
        ((x ⬝ᵥ M *ᵥ x : ℤ) : ℝ) := by simp [dotProduct, mulVec]
    rw [this]
    by_cases hx : x = 0
    · simp [hx]
    · exact_mod_cast (hp x hx).le
  refine ⟨hd, h1.posDef_iff_det_ne_zero.2 ?_⟩
  rw [← Int.cast_det]
  exact_mod_cast hd

theorem sum_pos_of_tensor_pos : ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (ι : Type) [Fintype ι] (a c : ι → Y), (∀ f g : Y →ₗ[ℤ] ℤ, ∑ i, f (a i) * g (c i) = ∑ i, g (a i) * f (c i)) → (∀ f : Y →ₗ[ℤ] ℤ, f ≠ 0 → 0 < ∑ i, f (a i) * f (c i)) → ∀ γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ, (∀ x y, γ x y = γ y x) → (∀ x, 0 ≤ γ x x) → γ ≠ 0 → 0 < ∑ i, γ (a i) (c i) := by
  intro Y _ _ _ ι _ a c hs hp γ hγ h0 hne
  classical
  let b := Module.finBasis ℤ Y
  let M : Matrix _ _ ℤ := Matrix.of fun p q => ∑ i, b.coord p (a i) * b.coord q (c i)
  have hM := (posDef_of_int M (fun p q => hs _ _) fun x hx => by
    have := hp (∑ p, x p • b.coord p) fun h => hx (funext fun q => by
      simpa [Finsupp.single_apply] using LinearMap.congr_fun h (b q))
    convert this using 1
    simp only [dotProduct, mulVec, M, Matrix.of_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset ι))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset ι))]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
    ring).2
  let G : Matrix _ _ ℝ := Matrix.of fun p q => γ (b p) (b q)
  have hG : G.PosSemidef := posSemidef_of_int (by ext p q; simp [G, hγ (b p) (b q)]) fun x => by
    convert h0 (∑ p, x p • b p) using 1
    simp only [dotProduct, mulVec, G, Matrix.of_apply, map_sum, map_zsmul, LinearMap.sum_apply,
      LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hγ (b p) (b q)]; ring
  have htr : ∑ i, γ (a i) (c i) = (M.map (Int.cast : ℤ → ℝ) * G).trace := by
    simp only [← evalOn_tensorCoord b γ]
    change ∑ i, ∑ p : _ × _, ((b.repr (a i) p.1 * b.repr (c i) p.2 : ℤ) : ℝ) * γ (b p.1) (b p.2) = _
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, M, G, Matrix.of_apply,
      Int.cast_sum, Finset.sum_mul, Module.Basis.coord_apply]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hγ (b p) (b q)]
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.posSemidef.nonneg
  have hCd : IsUnit C.det := by
    refine Ne.isUnit fun h => hM.det_pos.ne' ?_
    rw [hC, det_mul, h, mul_zero]
  have h1 := hG.mul_mul_conjTranspose_same C
  have h2 : (C * G * Cᴴ).trace = ∑ i, γ (a i) (c i) := by
    rw [htr, hC, trace_mul_cycle, star_eq_conjTranspose]
  rw [← h2]
  refine lt_of_le_of_ne h1.trace_nonneg fun h => hne ?_
  have h3 := h1.trace_eq_zero_iff.1 h.symm
  have hu : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).2 hCd
  have h4 : G = 0 := by
    rwa [← star_eq_conjTranspose, hu.star.mul_left_eq_zero, hu.mul_right_eq_zero] at h3
  exact b.ext fun p => b.ext fun q => congrFun (congrFun h4 p) q

theorem eq_zero_of_trace_mul (E : Type) [Field E] [NumberField E] {u : 𝓞 E}
    (h : ∀ α : 𝓞 E, Algebra.trace ℤ (𝓞 E) (α * u) = 0) : u = 0 := by
  by_contra hu
  obtain ⟨r, hr, α, hα⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) u).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hu)
  have h1 := h α
  rw [mul_comm, ← hα, Algebra.trace_algebraMap, nsmul_eq_mul] at h1
  have hd : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
  exact mul_ne_zero (by exact_mod_cast hd.ne') hr h1

theorem exists_traceDual : ∀ (E : Type) [Field E] [NumberField E], ∃ (N : ℕ) (ι : Type) (_ : Fintype ι) (ω θ : ι → 𝓞 E), 0 < N ∧ ∑ s, θ s * ω s = (N : 𝓞 E) ∧ ∀ g : 𝓞 E →ₗ[ℤ] ℤ, ∀ α : 𝓞 E, Algebra.trace ℤ (𝓞 E) (α * ∑ s, g (ω s) • θ s) = N * g α := by
  intro E _ _
  classical
  let ω := RingOfIntegers.basis E
  let d := (integralBasis E).traceDual
  have : Algebra.IsAlgebraic ℤ E := (IsFractionRing.comap_isAlgebraic_iff (K := ℚ)).2 inferInstance
  obtain ⟨k, hk, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ (Finset.univ.image d)
  let θ : _ → 𝓞 E := fun s => k • (⟨k • d s, hint _ (by simp)⟩ : 𝓞 E)
  have hN : (((k * k).toNat : ℕ) : ℤ) = k * k := Int.toNat_of_nonneg (mul_self_nonneg k)
  have hθ : ∀ s t, Algebra.trace ℤ (𝓞 E) (ω t * θ s) = if t = s then k * k else 0 := by
    intro s t
    apply Int.cast_injective (α := ℚ)
    rw [Algebra.coe_trace_int]
    have : ((ω t * θ s : 𝓞 E) : E) = k • k • (d s * integralBasis E t) := by
      change (ω t : E) * (k • k • d s) = _
      rw [integralBasis_apply, zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul]
      ring
    rw [this, map_zsmul, map_zsmul, Module.Basis.trace_traceDual_mul]
    split_ifs <;> simp
  have h3 : ∀ (g : 𝓞 E →ₗ[ℤ] ℤ) (α : 𝓞 E),
      Algebra.trace ℤ (𝓞 E) (α * ∑ s, g (ω s) • θ s) = k * k * g α := by
    intro g α
    have : (Algebra.trace ℤ (𝓞 E)) ∘ₗ LinearMap.mulRight ℤ (∑ s, g (ω s) • θ s) = (k * k) • g :=
      ω.ext fun t => by
        simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, Finset.mul_sum, mul_smul_comm,
          map_sum, map_smul, hθ, LinearMap.smul_apply, smul_eq_mul]
        simp [mul_comm]
    exact LinearMap.congr_fun this α
  refine ⟨(k * k).toNat, _, inferInstance, ω, θ, ?_, ?_, fun g α => by rw [hN, h3]⟩
  · have := mul_self_pos.2 hk
    omega
  · rw [← sub_eq_zero]
    refine eq_zero_of_trace_mul E fun α => ?_
    have h4 : ∀ s, Algebra.trace ℤ (𝓞 E) (α * (θ s * ω s)) = k * k * ω.repr (α * ω s) s := by
      intro s
      have := h3 (ω.coord s) (α * ω s)
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, ite_smul,
        one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      rw [← this, mul_comm (θ s), mul_assoc]
    rw [mul_sub, map_sub, Finset.mul_sum, map_sum, mul_comm α (_ : 𝓞 E), ← nsmul_eq_mul, map_nsmul,
      nsmul_eq_mul, hN, Algebra.trace_eq_matrix_trace ω α]
    simp only [h4, Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, Finset.mul_sum, sub_self]

end GlobalTheory.PointStepCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumStarProjectionEigenspaceEqSelfOfEigenvaluesLi
section
namespace GlobalTheory

open Module

open Module in

theorem _root_.GlobalTheory.ev_starProjection_eigenspace_eq_residue :
    ∀ (Y : Type) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (t : ℕ) (m : Fin t → ℂ) (s : ℂ) (Om : Module.End ℂ Y) (ev : Y →ₗ[ℂ] V) (K : ℂ → (Y →ₗ[ℂ] V)) (q : ℂ → ℂ) (y : Y) (v : V) (l : Fin t), Function.Injective m → Om.IsSymmetric → (∀ (lam : ℂ) (x : Y), x ≠ 0 → Om x = lam • x → ∃ j, lam = m j + s) → (∀ (u : ℂ) (x : Y), K u ((u - s) • x + Om x) = (∏ j, (u + m j)) • ev x) → Continuous q → (∀ u, K u y = q u • v) → ev ((Module.End.eigenspace Om (m l + s)).starProjection y) = (q (-m l) / ∏ j ∈ Finset.univ.erase l, (m j - m l)) • v := by
  intro Y _ _ _ V _ _ t m s Om ev K q y v l hm hOm hspec hK hq hKy
  set P : Fin t → Y → Y := fun j x => (Module.End.eigenspace Om (m j + s)).starProjection x with hP
  set c : Fin t → ℂ → ℂ := fun j u => ∏ k ∈ Finset.univ.erase j, (u + m k) with hc
  have key : ∀ x : Y, ∀ u : ℂ, (∏ k, (u + m k)) • K u x = (∏ k, (u + m k)) • ∑ j, c j u • ev (P j x) := by
    intro x u
    have hx : x ∈ ⨆ μ, Module.End.eigenspace Om μ := by
      rw [Submodule.orthogonal_eq_bot_iff.mp hOm.orthogonalComplement_iSup_eigenspaces_eq_bot]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (fun μ => Module.End.eigenspace Om μ) (motive := fun x => (∏ k, (u + m k)) • K u x = (∏ k, (u + m k)) • ∑ j, c j u • ev (P j x)) hx ?_ ?_ ?_
    · intro μ x hxμ
      by_cases hx0 : x = 0
      · subst hx0; simp [hP]
      have hOmx : Om x = μ • x := Module.End.mem_eigenspace_iff.mp hxμ
      obtain ⟨i, rfl⟩ := hspec μ x hx0 hOmx
      have hPx : ∀ j, P j x = if j = i then x else 0 := by
        intro j
        split_ifs with hji
        · subst hji; exact Submodule.starProjection_eq_self_iff.mpr hxμ
        · have hne : m j + s ≠ m i + s := fun h => hji (hm (add_right_cancel h))
          have hortho := hOm.orthogonalFamily_eigenspaces.isOrtho hne
          exact (Submodule.starProjection_apply_eq_zero_iff _).mpr (hortho.symm hxμ)
      have hsum : ∑ j, c j u • ev (P j x) = c i u • ev x := by
        rw [Finset.sum_eq_single i (fun j _ hji => by rw [hPx, if_neg hji, map_zero, smul_zero]) (by simp), hPx, if_pos rfl]
      have hKx : (u + m i) • K u x = (∏ k, (u + m k)) • ev x := by
        rw [← hK u x, hOmx, ← map_smul]
        congr 1
        rw [← add_smul]; congr 1; ring
      have hprod : ∏ k, (u + m k) = c i u * (u + m i) := by
        simp only [hc]; exact (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
      rw [hsum, smul_comm (∏ k, (u + m k)) (c i u), ← hKx, hprod, mul_smul]
    · simp [hP]
    · intro x₁ x₂ h₁ h₂
      simp only [hP] at h₁ h₂ ⊢
      simp only [map_add, smul_add, Finset.sum_add_distrib, h₁, h₂]
  have hgen : ∀ u, ∏ k, (u + m k) ≠ 0 → q u • v = ∑ j, c j u • ev (P j y) := by
    intro u hu
    rw [← hKy]
    exact smul_right_injective V hu (key y u)
  have hdense : Dense {u : ℂ | ∏ k, (u + m k) ≠ 0} := by
    have hfin : {u : ℂ | ∏ k, (u + m k) = 0}.Countable := by
      apply Set.Finite.countable
      apply (Set.finite_range (fun k => -m k)).subset
      intro u hu
      simp only [Set.mem_setOf_eq, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and] at hu
      obtain ⟨k, hk⟩ := hu
      exact ⟨k, by linear_combination -hk⟩
    simpa [Set.compl_setOf] using hfin.dense_compl ℝ
  have hcont : Continuous fun u => ∑ j, c j u • ev (P j y) := by
    simp only [hc]; fun_prop
  have hf : Continuous fun u => q u • v := hq.smul continuous_const
  have hl := congrFun (Continuous.ext_on hdense hf hcont hgen) (-m l)
  rw [Finset.sum_eq_single l (fun j _ hjl => by
    simp only [hc]
    rw [Finset.prod_eq_zero (i := l) (Finset.mem_erase.mpr ⟨Ne.symm hjl, Finset.mem_univ l⟩) (by ring), zero_smul]) (by simp)] at hl
  have hcl : c l (-m l) = ∏ j ∈ Finset.univ.erase l, (m j - m l) :=
    Finset.prod_congr rfl (fun k _ => by ring)
  have hD : ∏ j ∈ Finset.univ.erase l, (m j - m l) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j hj => sub_ne_zero.mpr (hm.ne (Finset.ne_of_mem_erase hj)))
  rw [hcl] at hl
  change ev (P l y) = _
  rw [div_eq_inv_mul, mul_smul, hl, smul_smul, inv_mul_cancel₀ hD, one_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.VecPolyMemSpanValues
section
namespace GlobalTheory

theorem vecPoly_mem_span_values (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (Z : ℂ → V)
    (X : ℕ → V) (ν : Fin n → ℂ) (hν : Function.Injective ν)
    (hZ : ∀ s : ℂ, Z s = ∑ j ∈ Finset.range n, s ^ j • X j) :
    (∀ j, j < n → X j ∈ Submodule.span ℂ (Set.range fun i => Z (ν i))) ∧
      ∀ s : ℂ, Z s ∈ Submodule.span ℂ (Set.range fun i => Z (ν i)) := by
  classical
  set W := Submodule.span ℂ (Set.range fun i => Z (ν i)) with hW
  set M : Matrix (Fin n) (Fin n) ℂ := Matrix.vandermonde ν with hM
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hν)
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hunit
  have hZν : ∀ i, Z (ν i) = ∑ l : Fin n, M i l • X l := by
    intro i
    rw [hZ, ← Fin.sum_univ_eq_sum_range (fun j => ν i ^ j • X j) n]
    simp [hM, Matrix.vandermonde_apply]
  have hX : ∀ k : Fin n, X k ∈ W := by
    intro k
    have key : ∀ l, ∑ i, M⁻¹ k i * M i l = (1 : Matrix (Fin n) (Fin n) ℂ) k l := fun l => by
      rw [← hinv, Matrix.mul_apply]
    have hsum : ∑ i : Fin n, M⁻¹ k i • Z (ν i) = X k := by
      simp_rw [hZν, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, key, Matrix.one_apply, ite_smul, one_smul, zero_smul]
      simp
    rw [← hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨fun j hj => hX ⟨j, hj⟩, fun s => ?_⟩
  rw [hZ]
  exact Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (hX ⟨j, Finset.mem_range.mp hj⟩)

end GlobalTheory
end

