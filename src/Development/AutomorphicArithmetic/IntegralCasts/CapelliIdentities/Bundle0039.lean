import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InverseOmegaHolds
section
noncomputable def UpperTheory.Reformulated.B.Gwa1.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

noncomputable def UpperTheory.Reformulated.B.Gwa1.IsWq :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → WeierstrassCurve ℂ_[p] → PowerSeries ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) ↦
      have c : ℂ_[p] →+* PowerSeries ℂ_[p] := Algebra.algebraMap ℂ_[p] (PowerSeries ℂ_[p]);
      have X : PowerSeries ℂ_[p] := PowerSeries.X;
      wq =
        (1 : PowerSeries ℂ_[p]) + (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₁ * X * wq +
                (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₂ * X ^ (2 : ℕ) * wq +
              (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₃ * X ^ (3 : ℕ) * wq ^ (2 : ℕ) +
            (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₄ * X ^ (4 : ℕ) * wq ^ (2 : ℕ) +
          (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₆ * X ^ (6 : ℕ) * wq ^ (3 : ℕ)

noncomputable def UpperTheory.Reformulated.B.Gwa1.dX.{u_1} :
    {A : Type u_1} → [CommRing A] → PowerSeries A → PowerSeries A :=
    fun {A : Type u_1} [CommRing A] (f : PowerSeries A) ↦
      PowerSeries.mk fun (n : ℕ) ↦ ((↑n : A) + (1 : A)) * (PowerSeries.coeff (n + (1 : ℕ)) : PowerSeries A → A) f

noncomputable def UpperTheory.Reformulated.B.Gwa1.omegaW :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → WeierstrassCurve ℂ_[p] → PowerSeries ℂ_[p] → PowerSeries ℂ_[p] :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) ↦
      have c : ℂ_[p] →+* PowerSeries ℂ_[p] := Algebra.algebraMap ℂ_[p] (PowerSeries ℂ_[p]);
      have X : PowerSeries ℂ_[p] := PowerSeries.X;
      ((-2 : PowerSeries ℂ_[p]) * wq - X * UpperTheory.Reformulated.B.Gwa1.dX wq) *
        (wq *
            ((c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₁ * X + (c : ℂ_[p] → PowerSeries ℂ_[p]) W.a₃ * X ^ (3 : ℕ) * wq -
              (2 : PowerSeries ℂ_[p])))⁻¹

noncomputable def UpperTheory.Reformulated.B.Gwa1.flog :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → WeierstrassCurve ℂ_[p] → PowerSeries ℂ_[p] → PowerSeries ℂ_[p] :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) ↦
      PowerSeries.mk fun (n : ℕ) ↦
        if n = (0 : ℕ) then (0 : ℂ_[p])
        else (PowerSeries.coeff (n - (1 : ℕ)) : PowerSeries ℂ_[p] → ℂ_[p]) (UpperTheory.Reformulated.B.Gwa1.omegaW W wq) / (↑n : ℂ_[p])

noncomputable def UpperTheory.Reformulated.B.Gwa1.InvOmega :
    Prop :=
    ∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]),
      UpperTheory.Reformulated.B.Gwa1.IsIntP W.a₁ →
        UpperTheory.Reformulated.B.Gwa1.IsIntP W.a₂ →
          UpperTheory.Reformulated.B.Gwa1.IsIntP W.a₃ →
            UpperTheory.Reformulated.B.Gwa1.IsIntP W.a₄ →
              UpperTheory.Reformulated.B.Gwa1.IsIntP W.a₆ →
                UpperTheory.Reformulated.B.Gwa1.IsWq W wq →
                  ∃ (v : PowerSeries ℂ_[p]),
                    (∀ (n : ℕ), UpperTheory.Reformulated.B.Gwa1.IsIntP ((PowerSeries.coeff n : PowerSeries ℂ_[p] → ℂ_[p]) v)) ∧
                      v * UpperTheory.Reformulated.B.Gwa1.dX (UpperTheory.Reformulated.B.Gwa1.flog W wq) = (1 : PowerSeries ℂ_[p])

namespace UpperTheory.Reformulated.B.Gwa1

open PowerSeries

private def lowIn {R : Type*} [CommRing R] (O : Subring R) (n : ℕ) : Subring R⟦X⟧ where
  carrier := {f | ∀ k < n, coeff k f ∈ O}
  mul_mem' := by
    intro f g hf hg k hk
    rw [coeff_mul]
    refine O.sum_mem fun x hx => ?_
    have h := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    exact O.mul_mem (hf _ (by omega)) (hg _ (by omega))
  one_mem' := by
    intro k _
    rw [coeff_one]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  add_mem' := by
    intro f g hf hg k hk
    rw [map_add]
    exact O.add_mem (hf k hk) (hg k hk)
  zero_mem' := by
    intro k _
    rw [map_zero]
    exact O.zero_mem
  neg_mem' := by
    intro f hf k hk
    rw [map_neg]
    exact O.neg_mem (hf k hk)

private theorem C_mem {R : Type*} [CommRing R] {O : Subring R} (n : ℕ) {a : R} (ha : a ∈ O) :
    (C a : R⟦X⟧) ∈ lowIn O n := by
  intro k _
  rw [coeff_C]
  split_ifs
  · exact ha
  · exact O.zero_mem

private theorem X_mem {R : Type*} [CommRing R] (O : Subring R) (n : ℕ) :
    (X : R⟦X⟧) ∈ lowIn O n := by
  intro k _
  rw [coeff_X]
  split_ifs
  · exact O.one_mem
  · exact O.zero_mem

private theorem X_mul_mem {R : Type*} [CommRing R] {O : Subring R} {n : ℕ} {f : R⟦X⟧}
    (hf : f ∈ lowIn O n) : X * f ∈ lowIn O (n + 1) := by
  intro k hk
  cases k with
  | zero => rw [coeff_zero_X_mul]; exact O.zero_mem
  | succ k => rw [coeff_succ_X_mul]; exact hf k (by omega)

private theorem w_mem {R : Type*} [CommRing R] {O : Subring R} {a₁ a₂ a₃ a₄ a₆ : R}
    (h₁ : a₁ ∈ O) (h₂ : a₂ ∈ O) (h₃ : a₃ ∈ O) (h₄ : a₄ ∈ O) (h₆ : a₆ ∈ O) {w : R⟦X⟧}
    (hw : w = 1 + C a₁ * X * w + C a₂ * X ^ 2 * w + C a₃ * X ^ 3 * w ^ 2 + C a₄ * X ^ 4 * w ^ 2
      + C a₆ * X ^ 6 * w ^ 3) (n : ℕ) : w ∈ lowIn O n := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    have e : w = 1 + X * (C a₁ * w + C a₂ * X * w + C a₃ * X ^ 2 * w ^ 2 + C a₄ * X ^ 3 * w ^ 2
      + C a₆ * X ^ 5 * w ^ 3) := by linear_combination hw
    have hX := X_mem O n
    rw [e]
    exact add_mem (one_mem _) (X_mul_mem (add_mem (add_mem (add_mem (add_mem
      (mul_mem (C_mem n h₁) ih)
      (mul_mem (mul_mem (C_mem n h₂) hX) ih))
      (mul_mem (mul_mem (C_mem n h₃) (pow_mem hX _)) (pow_mem ih _)))
      (mul_mem (mul_mem (C_mem n h₄) (pow_mem hX _)) (pow_mem ih _)))
      (mul_mem (mul_mem (C_mem n h₆) (pow_mem hX _)) (pow_mem ih _))))

private theorem dX_eq {R : Type*} [CommRing R] (f : R⟦X⟧) : dX f = derivative R f := by
  ext n
  rw [coeff_derivative, dX, coeff_mk, mul_comm]

private theorem key {R : Type*} [CommRing R] {a₁ a₂ a₃ a₄ a₆ : R} {w : R⟦X⟧}
    (hw : w = 1 + C a₁ * X * w + C a₂ * X ^ 2 * w + C a₃ * X ^ 3 * w ^ 2 + C a₄ * X ^ 4 * w ^ 2
      + C a₆ * X ^ 6 * w ^ 3) :
    (1 - C a₁ * X - C a₂ * X ^ 2 - 2 * (C a₃ * X ^ 3 * w) - 2 * (C a₄ * X ^ 4 * w)
      - 3 * (C a₆ * X ^ 6 * w ^ 2)) * (-2 * w - X * dX w)
      = w * (C a₁ * X + C a₃ * X ^ 3 * w - 2) := by
  have h := congrArg (derivative R) hw
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, derivative_C, derivative_X,
    Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul] at h
  rw [dX_eq]
  push_cast at h
  linear_combination (-X) * h

private noncomputable def ball (p : ℕ) [Fact (Nat.Prime p)] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro x y hx hy
    change ‖x * y‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy
  one_mem' := by
    change ‖(1 : ℂ_[p])‖ ≤ 1
    rw [norm_one]
  add_mem' := by
    intro x y hx hy
    exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  zero_mem' := by
    change ‖(0 : ℂ_[p])‖ ≤ 1
    rw [norm_zero]
    exact zero_le_one
  neg_mem' := by
    intro x hx
    change ‖-x‖ ≤ 1
    rw [norm_neg]
    exact hx

private theorem dX_flog {p : ℕ} [Fact (Nat.Prime p)] (W : WeierstrassCurve ℂ_[p])
    (w : ℂ_[p]⟦X⟧) : dX (flog W w) = omegaW W w := by
  ext n
  have hn : ((n : ℂ_[p]) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  rw [dX, coeff_mk, flog, coeff_mk, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel,
    Nat.cast_add_one, mul_div_cancel₀ _ hn]

end UpperTheory.Reformulated.B.Gwa1

open PowerSeries in
theorem UpperTheory.Reformulated.B.Gwa1.inverse_omega_holds :
    UpperTheory.Reformulated.B.Gwa1.InvOmega := by
  intro p _ W w h₁ h₂ h₃ h₄ h₆ hw
  have hw' : w = 1 + C W.a₁ * X * w + C W.a₂ * X ^ 2 * w + C W.a₃ * X ^ 3 * w ^ 2
      + C W.a₄ * X ^ 4 * w ^ 2 + C W.a₆ * X ^ 6 * w ^ 3 := hw
  refine ⟨1 - C W.a₁ * X - C W.a₂ * X ^ 2 - 2 * (C W.a₃ * X ^ 3 * w) - 2 * (C W.a₄ * X ^ 4 * w)
      - 3 * (C W.a₆ * X ^ 6 * w ^ 2), fun n => ?_, ?_⟩
  · have hX := X_mem (ball p) (n + 1)
    have ih := w_mem (O := ball p) h₁ h₂ h₃ h₄ h₆ hw' (n + 1)
    have c₁ := C_mem (O := ball p) (n + 1) h₁
    have c₂ := C_mem (O := ball p) (n + 1) h₂
    have c₃ := C_mem (O := ball p) (n + 1) h₃
    have c₄ := C_mem (O := ball p) (n + 1) h₄
    have c₆ := C_mem (O := ball p) (n + 1) h₆
    exact (sub_mem (sub_mem (sub_mem (sub_mem (sub_mem (one_mem _) (mul_mem c₁ hX))
      (mul_mem c₂ (pow_mem hX _)))
      (mul_mem (ofNat_mem _ 2) (mul_mem (mul_mem c₃ (pow_mem hX _)) ih)))
      (mul_mem (ofNat_mem _ 2) (mul_mem (mul_mem c₄ (pow_mem hX _)) ih)))
      (mul_mem (ofNat_mem _ 3) (mul_mem (mul_mem c₆ (pow_mem hX _)) (pow_mem ih _))) :
        _ ∈ lowIn (ball p) (n + 1)) n (Nat.lt_succ_self n)
  · have h0 : constantCoeff w = 1 := by
      have h := congrArg constantCoeff hw'
      simpa using h
    have hu : constantCoeff (w * (C W.a₁ * X + C W.a₃ * X ^ 3 * w - 2)) ≠ 0 := by
      simp [h0, map_ofNat]
    have ho : omegaW W w = (-2 * w - X * dX w) * (w * (C W.a₁ * X + C W.a₃ * X ^ 3 * w - 2))⁻¹ :=
      rfl
    rw [dX_flog, ho, ← mul_assoc, key hw']
    exact PowerSeries.mul_inv_cancel _ hu
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleInvariant
section
noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariant.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariant.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.IrreducibleInvariant.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.IrreducibleInvariant.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariant.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.IrreducibleInvariant.IsIrrSub r ⊤

theorem UpperTheory.Reformulated.B.IrreducibleInvariant.exists_ne :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] (ρ : Γ →* GL (Fin (2 : ℕ)) k),
      UpperTheory.Reformulated.B.IrreducibleInvariant.IsIrr ρ →
        ∀ (g : GL (Fin (2 : ℕ)) k),
          ∃ (s : Γ),
            (↑(g * (ρ : Γ → GL (Fin (2 : ℕ)) k) s * g⁻¹) : Matrix (Fin (2 : ℕ)) (Fin (2 : ℕ)) k) (0 : Fin (2 : ℕ))
                (1 : Fin (2 : ℕ)) ≠
              (0 : k) := by
  intro Γ k _ _ ρ hirr g
  by_contra hcon
  push Not at hcon
  obtain ⟨-, -, hmin⟩ := hirr
  let L : Submodule k (Fin 2 → k) :=
    LinearMap.ker ((LinearMap.proj (0 : Fin 2) : (Fin 2 → k) →ₗ[k] k) ∘ₗ
      Matrix.mulVecLin (g : Matrix (Fin 2) (Fin 2) k))
  have hL : ∀ v, v ∈ L ↔ ((g : Matrix (Fin 2) (Fin 2) k).mulVec v) 0 = 0 := fun v => Iff.rfl
  have hg : ∀ w : Fin 2 → k, (g : Matrix (Fin 2) (Fin 2) k).mulVec
      (((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hinv : UpperTheory.Reformulated.B.IrreducibleInvariant.IsInv ρ L := by
    intro s v hv
    rw [hL] at hv ⊢
    have key : (g : Matrix (Fin 2) (Fin 2) k).mulVec
        (((ρ s : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec v) =
        ((g * ρ s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec
          ((g : Matrix (Fin 2) (Fin 2) k).mulVec v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
        inv_mul_cancel_right]
    rw [key]
    generalize (g : Matrix (Fin 2) (Fin 2) k).mulVec v = w at hv
    have h01 := hcon s
    generalize ((g * ρ s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = M at h01
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv, h01]
  rcases hmin L le_top hinv with h | h
  · have h1 : ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec (Pi.single 1 1) ∈ L := by
      rw [hL, hg]
      simp
    rw [h, Submodule.mem_bot] at h1
    have h2 := hg (Pi.single 1 1)
    rw [h1, Matrix.mulVec_zero] at h2
    have h3 := congrFun h2 1
    simp at h3
  · have h1 : ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).mulVec (Pi.single 0 1) ∈ L := by
      rw [h]
      exact Submodule.mem_top
    rw [hL, hg] at h1
    simp at h1
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleInvariantSubspaces
section
noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsIrrSub r ⊤

theorem UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.irr_conj :
    ∀ {k : Type} [inst : Field k] {Γ : Type} [inst_1 : Group Γ] {n : ℕ} (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k),
      (∀ (x : Γ), (r' : Γ → GL (Fin n) k) x = g * (r : Γ → GL (Fin n) k) x * g⁻¹) →
        UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsIrr r' → UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsIrr r := by
  intro k _ Γ _ n r r' g h hirr
  obtain ⟨hne, -, hmin⟩ := hirr
  refine ⟨hne, fun _ _ _ => Submodule.mem_top, fun W _ hW => ?_⟩
  have hgg : ∀ v : Fin n → k, (↑(g⁻¹) : Matrix (Fin n) (Fin n) k).mulVec
      ((↑g : Matrix (Fin n) (Fin n) k).mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hinv : UpperTheory.Reformulated.B.IrreducibleInvariantSubspaces.IsInv r'
      (W.comap (Matrix.mulVecLin (↑(g⁻¹) : Matrix (Fin n) (Fin n) k))) := by
    intro x v hv
    rw [Submodule.mem_comap, Matrix.mulVecLin_apply] at hv ⊢
    rw [h x, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgg]
    exact hW x _ hv
  rcases hmin _ le_top hinv with h0 | h1
  · left
    rw [Submodule.eq_bot_iff] at h0 ⊢
    intro v hv
    have h2 : (↑g : Matrix (Fin n) (Fin n) k).mulVec v = 0 := by
      apply h0
      rw [Submodule.mem_comap, Matrix.mulVecLin_apply, hgg]
      exact hv
    rw [← hgg v, h2, Matrix.mulVec_zero]
  · right
    rw [Submodule.eq_top_iff'] at h1 ⊢
    intro v
    have h2 := h1 ((↑g : Matrix (Fin n) (Fin n) k).mulVec v)
    rwa [Submodule.mem_comap, Matrix.mulVecLin_apply, hgg] at h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleOfSpanningMatrices
section
theorem UpperTheory.Reformulated.B.IrreducibleOfSpanningMatrices.irreducible_of_span_eq_top :
    ∀ {K G ι : Type} [inst : Field K] [inst_1 : Fintype ι]
    [DecidableEq ι] (f : G → Matrix ι ι K),
    Submodule.span K (Set.range f) = ⊤ →
      ∀ (N : Submodule K (ι → K)), (∀ (g : G), ∀ v ∈ N, (f g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro K G ι _ _ _ f hf N hN
  have key : ∀ A : Matrix ι ι K, ∀ v ∈ N, A.mulVec v ∈ N := by
    intro A v hv
    have hA : A ∈ Submodule.span K (Set.range f) := by rw [hf]; exact Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hN g v hv
    | zero => rw [Matrix.zero_mulVec]; exact N.zero_mem
    | add x y _ _ hx hy => rw [Matrix.add_mulVec]; exact N.add_mem hx hy
    | smul a x _ hx => rw [Matrix.smul_mulVec]; exact N.smul_mem a hx
  by_cases h : N = ⊥
  · exact Or.inl h
  · right
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    have hi' : v i ≠ 0 := hi
    rw [eq_top_iff]
    intro w _
    have h1 := key (Matrix.of fun a b => if b = i then w a * (v i)⁻¹ else 0) v hv
    have h2 : (Matrix.of fun a b => if b = i then w a * (v i)⁻¹ else 0).mulVec v = w := by
      funext a
      simp [Matrix.mulVec, dotProduct, hi']
    rwa [h2] at h1
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleProjectionExists
section
private lemma sepCore {R S N ι : Type} [Ring R] [AddCommGroup S] [Module R S] [IsSimpleModule R S]
    [AddCommGroup N] [Module R N] (f : ι → S →ₗ[R] N)
    (h : ⨆ i, LinearMap.range (f i) = ⊤) {x : N} (hx : x ≠ 0) :
    ∃ p : N →ₗ[R] S, p x ≠ 0 := by
  have hss : ∀ i, IsSemisimpleModule R (LinearMap.range (f i)) := fun i => .range (f i)
  have : IsSemisimpleModule R N := isSemisimpleModule_of_isSemisimpleModule_submodule' hss h
  have hiso : IsIsotypicOfType R N S := by
    apply IsIsotypicOfType.of_isotypicComponent_eq_top
    rw [eq_top_iff, ← h]
    refine iSup_le fun i => ?_
    rcases (f i).injective_or_eq_zero with hi | hi
    · exact le_sSup ⟨(LinearEquiv.ofInjective (f i) hi).symm⟩
    · rw [hi, LinearMap.range_zero]
      exact bot_le
  obtain ⟨κ, ⟨e⟩⟩ := hiso.linearEquiv_finsupp
  have hne : e x ≠ 0 := (LinearEquiv.map_ne_zero_iff e).mpr hx
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
  exact ⟨(Finsupp.lapply i) ∘ₗ e.toLinearMap, by simpa using hi⟩

theorem UpperTheory.irreducible_projection_exists :
    ∀ {H V M : Type} [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
        (σ : Representation ℂ H V) (ρ : Representation ℂ H M), σ.IsIrreducible →
        ∀ (Y : Submodule ℂ M),
          Y ≤ ⨆ (f : { f : V →ₗ[ℂ] M // (∀ (g : H) (v : V), f (σ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ Y }),
            LinearMap.range f.1 →
          ∀ {F : M}, F ∈ Y → F ≠ 0 →
            ∃ p : M →ₗ[ℂ] V, (∀ (g : H), ∀ y ∈ Y, p (ρ g y) = σ g (p y)) ∧ p F ≠ 0 := by
  intro H V M _ _ _ _ _ σ ρ hσ Y hY F hF hF0
  have hinv : ∀ (g : H) {y : M}, y ∈ Y → ρ g y ∈ Y := by
    intro g y hy
    refine Submodule.iSup_induction _ (motive := fun y => ρ g y ∈ Y) (hY hy) ?_ ?_ ?_
    · rintro ⟨f, hf, hr⟩ x ⟨v, rfl⟩
      rw [← hf g v]
      exact hr ⟨_, rfl⟩
    · simp
    · intro a b ha hb
      rw [map_add]
      exact Y.add_mem ha hb
  let Ys : Subrepresentation ρ := ⟨Y, hinv⟩
  let τ : Representation ℂ H Y := Ys.toRepresentation
  let φ : { f : V →ₗ[ℂ] M // (∀ (g : H) (v : V), f (σ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ Y } →
      Representation.IntertwiningMap σ τ := fun f =>
    (f.1.codRestrict Y (fun v => f.2.2 ⟨v, rfl⟩)).intertwiningMap_of_isIntertwiningMap σ τ
      (fun g v => Subtype.ext (f.2.1 g v))
  let ψ := fun i => Representation.IntertwiningMap.equivLinearMapAsModule σ τ (φ i)
  haveI : IsSimpleModule (MonoidAlgebra ℂ H) σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).mp hσ
  have hall : ∀ y ∈ (⨆ (f : { f : V →ₗ[ℂ] M // (∀ (g : H) (v : V), f (σ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ Y }),
      LinearMap.range f.1), ∃ hy : y ∈ Y,
      (show τ.asModule from (⟨y, hy⟩ : Y)) ∈ ⨆ i, LinearMap.range (ψ i) := by
    intro y hy
    refine Submodule.iSup_induction _ (motive := fun y => ∃ hy : y ∈ Y,
      (show τ.asModule from (⟨y, hy⟩ : Y)) ∈ ⨆ i, LinearMap.range (ψ i)) hy ?_ ?_ ?_
    · rintro f x ⟨v, rfl⟩
      exact ⟨f.2.2 ⟨v, rfl⟩, Submodule.mem_iSup_of_mem f ⟨v, rfl⟩⟩
    · exact ⟨Y.zero_mem, Submodule.zero_mem _⟩
    · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      exact ⟨Y.add_mem ha hb, Submodule.add_mem _ ha' hb'⟩
  have htop : ⨆ i, LinearMap.range (ψ i) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨_, hx⟩ := hall (x : Y).1 (hY (x : Y).2)
    exact hx
  obtain ⟨p, hp⟩ := sepCore ψ htop (x := (show τ.asModule from (⟨F, hF⟩ : Y)))
    (fun h => hF0 (congrArg Subtype.val (show (⟨F, hF⟩ : Y) = 0 from h)))
  let p' := (Representation.IntertwiningMap.equivLinearMapAsModule τ σ).symm p
  obtain ⟨q, hq⟩ := LinearMap.exists_extend p'.toLinearMap
  have hqy : ∀ (y : M) (hy : y ∈ Y), q y = p' ⟨y, hy⟩ := fun y hy =>
    congrArg (fun l => l (⟨y, hy⟩ : Y)) hq
  refine ⟨q, fun g y hy => ?_, ?_⟩
  · rw [hqy _ (hinv g hy), hqy _ hy]
    exact Representation.IntertwiningMap.isIntertwining τ σ p' g ⟨y, hy⟩
  · rw [hqy _ hF]
    exact hp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleSubrep
section
noncomputable def UpperTheory.Reformulated.B.IrreducibleSubrep.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.IrreducibleSubrep.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.IrreducibleSubrep.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.IrreducibleSubrep.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.IrreducibleSubrep.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.IrreducibleSubrep.IsIrrSub r ⊤

noncomputable def UpperTheory.Reformulated.B.IrreducibleSubrep.RepIso :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r r' : Γ →* GL (Fin n) k) ↦
      ∃ (g : GL (Fin n) k), ∀ (s : Γ), (r' : Γ → GL (Fin n) k) s = g * (r : Γ → GL (Fin n) k) s * g⁻¹

theorem UpperTheory.Reformulated.B.IrreducibleSubrep.irr_of_iso :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k},
      UpperTheory.Reformulated.B.IrreducibleSubrep.IsIrr r → UpperTheory.Reformulated.B.IrreducibleSubrep.RepIso r r' → UpperTheory.Reformulated.B.IrreducibleSubrep.IsIrr r' := by
  intro Γ k _ _ n r r' hr hiso
  obtain ⟨hne, -, hmin⟩ := hr
  obtain ⟨g, hg⟩ := hiso
  refine ⟨hne, fun _ _ _ => Submodule.mem_top, fun W' _ hW' => ?_⟩
  have hcomm : ∀ s : Γ, (g : Matrix (Fin n) (Fin n) k) * (r s : Matrix (Fin n) (Fin n) k)
      = (r' s : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k) := by
    intro s
    rw [← Units.val_mul, ← Units.val_mul, hg s, inv_mul_cancel_right]
  have hsec : ∀ v : Fin n → k, (g : Matrix (Fin n) (Fin n) k).mulVec
      (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hinv : UpperTheory.Reformulated.B.IrreducibleSubrep.IsInv r
      (W'.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k))) := by
    intro s v hv
    rw [Submodule.mem_comap, Matrix.mulVecLin_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec]
    exact hW' s _ hv
  rcases hmin _ le_top hinv with h | h
  · left
    rw [Submodule.eq_bot_iff] at h ⊢
    intro w hw
    have h0 := h (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec w) (by
      rw [Submodule.mem_comap, Matrix.mulVecLin_apply, hsec]; exact hw)
    rw [← hsec w, h0, Matrix.mulVec_zero]
  · right
    rw [Submodule.eq_top_iff'] at h ⊢
    intro w
    have h0 := h (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec w)
    rwa [Submodule.mem_comap, Matrix.mulVecLin_apply, hsec] at h0
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsIntegralNatCast
section
noncomputable def UpperTheory.Reformulated.B.IsIntegralNatCast.IsIntP :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → ℂ_[p] → Prop :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (x : ℂ_[p]) ↦ ‖x‖ ≤ (1 : ℝ)

theorem UpperTheory.Reformulated.B.IsIntegralNatCast.isPadicIntegral_natCast :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] (n : ℕ), UpperTheory.Reformulated.B.IsIntegralNatCast.IsIntP (↑n : ℂ_[p]) := by
  intro p _ n
  exact IsUltrametricDist.norm_natCast_le_one ℂ_[p] n
end

