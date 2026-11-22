import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AntidiagonalTranspose
section
noncomputable def UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat.{u_1} :
    (R : Type u_1) → [CommRing R] → (m : ℕ) → Matrix (Fin m) (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) (i j : Fin m) ↦ if j = i.rev then (1 : R) else (0 : R)

theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.aux2.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (m : ℕ),
      UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat R m * UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  intro R _ m
  ext i j
  simp only [Matrix.mul_apply, UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat, Matrix.one_apply]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

noncomputable def UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl.{u_1} :
    (R : Type u_1) → [inst : CommRing R] → (m : ℕ) → GL (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) ↦
      { val := UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat R m, inv := UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat R m, val_inv := UpperTheory.Reformulated.B.AntidiagonalTranspose.aux2 m,
        inv_val := UpperTheory.Reformulated.B.AntidiagonalTranspose.aux2 m : (Matrix (Fin m) (Fin m) R)ˣ }

theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.aux4.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.aux5.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

noncomputable def UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv.{u_1} :
    {n : Type} → [inst : Fintype n] → [inst_1 : DecidableEq n] → {R : Type u_1} → [inst_2 : CommRing R] → GL n R → GL n R :=
    fun {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) ↦
      { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose, val_inv := UpperTheory.Reformulated.B.AntidiagonalTranspose.aux4 g,
        inv_val := UpperTheory.Reformulated.B.AntidiagonalTranspose.aux5 g : (Matrix n n R)ˣ }

noncomputable def UpperTheory.Reformulated.B.AntidiagonalTranspose.theta.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R → GL (Fin m) R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) ↦
      UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m * UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv g * UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m

private theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat_transpose.{u_1} {R : Type u_1} [CommRing R] (m : ℕ) :
    (UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat R m).transpose = UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat R m := by
  ext i j
  simp only [Matrix.transpose_apply, UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat]
  have : (i = j.rev) ↔ (j = i.rev) := by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  simp [this]

private theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl_mul_self.{u_1} {R : Type u_1} [CommRing R] (m : ℕ) :
    UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m * UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m = 1 :=
  Units.ext (UpperTheory.Reformulated.B.AntidiagonalTranspose.aux2 m)

private theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl_inv.{u_1} {R : Type u_1} [CommRing R] (m : ℕ) :
    (UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m)⁻¹ = UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m :=
  inv_eq_of_mul_eq_one_left (UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl_mul_self m)

private theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv_mul.{u_1} {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1}
    [CommRing R] (g h : GL n R) :
    UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv (g * h) = UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv g * UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv h := by
  apply Units.ext
  change (((g * h)⁻¹ : GL n R) : Matrix n n R).transpose =
    (↑g⁻¹ : Matrix n n R).transpose * (↑h⁻¹ : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv_trInv.{u_1} {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1}
    [CommRing R] (g : GL n R) :
    UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv (UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv g) = g := by
  apply Units.ext
  change (↑(UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv g)⁻¹ : Matrix n n R).transpose = ↑g
  change ((↑g : Matrix n n R).transpose).transpose = ↑g
  exact Matrix.transpose_transpose _

private theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv_Jgl.{u_1} {R : Type u_1} [CommRing R] (m : ℕ) :
    UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv (UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m) = UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m := by
  apply Units.ext
  change (((UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m)⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R).transpose =
    UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat R m
  rw [UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl_inv]
  exact UpperTheory.Reformulated.B.AntidiagonalTranspose.Jmat_transpose m

theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.aux8.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g : GL (Fin m) R), UpperTheory.Reformulated.B.AntidiagonalTranspose.theta (UpperTheory.Reformulated.B.AntidiagonalTranspose.theta g) = g := by
  intro m R _ g
  have hJ := UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl_mul_self (R := R) m
  simp only [UpperTheory.Reformulated.B.AntidiagonalTranspose.theta, UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv_mul, UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv_trInv,
    UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv_Jgl]
  calc _ = (UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m * UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m) * g *
        (UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m * UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m) *
        (UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m * UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m) := by
        simp only [hJ, mul_one, one_mul]
        simp only [mul_assoc, hJ, mul_one]
        simp only [← mul_assoc, hJ, one_mul]
    _ = g := by simp [hJ]

theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.aux9.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g h : GL (Fin m) R),
      UpperTheory.Reformulated.B.AntidiagonalTranspose.theta (g * h) = UpperTheory.Reformulated.B.AntidiagonalTranspose.theta g * UpperTheory.Reformulated.B.AntidiagonalTranspose.theta h := by
  intro m R _ g h
  have hJ := UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl_mul_self (R := R) m
  simp only [UpperTheory.Reformulated.B.AntidiagonalTranspose.theta, UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv_mul]
  calc _ = UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m * UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv g * 1 * UpperTheory.Reformulated.B.AntidiagonalTranspose.trInv h *
        UpperTheory.Reformulated.B.AntidiagonalTranspose.Jgl R m := by simp only [mul_one, mul_assoc]
    _ = _ := by rw [← hJ]; simp only [mul_assoc]

noncomputable def UpperTheory.Reformulated.B.AntidiagonalTranspose.thetaAut.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := UpperTheory.Reformulated.B.AntidiagonalTranspose.theta, invFun := UpperTheory.Reformulated.B.AntidiagonalTranspose.theta, left_inv := UpperTheory.Reformulated.B.AntidiagonalTranspose.aux8,
        right_inv := UpperTheory.Reformulated.B.AntidiagonalTranspose.aux8, map_mul' := UpperTheory.Reformulated.B.AntidiagonalTranspose.aux9 : GL (Fin m) R ≃* GL (Fin m) R }

private theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.thetaAut_sq.{u_1} (m : ℕ) (R : Type u_1) [CommRing R] :
    UpperTheory.Reformulated.B.AntidiagonalTranspose.thetaAut m R * UpperTheory.Reformulated.B.AntidiagonalTranspose.thetaAut m R = 1 := by
  ext1 g
  exact UpperTheory.Reformulated.B.AntidiagonalTranspose.aux8 g

theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.aux11.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R],
      (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalTranspose.thetaAut m R) =
        (1 : MulAut (GL (Fin m) R)) := by
  intro m R _
  exact if_pos rfl

theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.aux12.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R] (s t : ℤˣ),
      (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalTranspose.thetaAut m R) =
        (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalTranspose.thetaAut m R) *
          if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalTranspose.thetaAut m R := by
  intro m R _ s t
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
  · simp
  · simp
  · simp
  · simp [UpperTheory.Reformulated.B.AntidiagonalTranspose.thetaAut_sq]

noncomputable def UpperTheory.Reformulated.B.AntidiagonalTranspose.sgnAct.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → ℤˣ →* MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.AntidiagonalTranspose.thetaAut m R,
        map_one' := UpperTheory.Reformulated.B.AntidiagonalTranspose.aux11 m R, map_mul' := UpperTheory.Reformulated.B.AntidiagonalTranspose.aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def UpperTheory.Reformulated.B.AntidiagonalTranspose.GG.{u_1} :
    ℕ → (R : Type u_1) → [CommRing R] → Type u_1 :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦ GL (Fin m) R ⋊[UpperTheory.Reformulated.B.AntidiagonalTranspose.sgnAct m R] ℤˣ

@[reducible] noncomputable def UpperTheory.Reformulated.B.AntidiagonalTranspose.ofGL.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R →* UpperTheory.Reformulated.B.AntidiagonalTranspose.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] ↦ SemidirectProduct.inl

noncomputable def UpperTheory.Reformulated.B.AntidiagonalTranspose.conjBy.{u_1, u_3} :
    {m : ℕ} →
      {R : Type u_1} →
        [inst : CommRing R] →
          {G : Type u_3} → [inst_1 : Group G] → GL (Fin m) R → (G →* UpperTheory.Reformulated.B.AntidiagonalTranspose.GG m R) → G →* UpperTheory.Reformulated.B.AntidiagonalTranspose.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G] (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.AntidiagonalTranspose.GG m R) ↦
      (MulEquiv.toMonoidHom
            ((MulAut.conj : UpperTheory.Reformulated.B.AntidiagonalTranspose.GG m R → MulAut (UpperTheory.Reformulated.B.AntidiagonalTranspose.GG m R))
              ((UpperTheory.Reformulated.B.AntidiagonalTranspose.ofGL : GL (Fin m) R → UpperTheory.Reformulated.B.AntidiagonalTranspose.GG m R) h))).comp
        r

theorem UpperTheory.Reformulated.B.AntidiagonalTranspose.conj_right :
    ∀ {G R : Type} [inst : Group G] [inst_1 : CommRing R] {m : ℕ} (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.AntidiagonalTranspose.GG m R)
      (g : G),
      ((UpperTheory.Reformulated.B.AntidiagonalTranspose.conjBy h r : G → UpperTheory.Reformulated.B.AntidiagonalTranspose.GG m R) g).right = ((r : G → UpperTheory.Reformulated.B.AntidiagonalTranspose.GG m R) g).right := by
  intro G R _ _ m h r g
  simp [UpperTheory.Reformulated.B.AntidiagonalTranspose.conjBy, MulAut.conj_apply]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BallRing
section
noncomputable def UpperTheory.Reformulated.B.ClosedUnitBallSubring.ballRing :
    (K : Type) → [inst : NormedField K] → [IsUltrametricDist K] → Subring K :=
  fun K _ _ =>
    { carrier := {x : K | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a * b‖ ≤ 1
        rw [norm_mul]
        exact mul_le_one₀ ha' (norm_nonneg b) hb'
      one_mem' := by
        show ‖(1 : K)‖ ≤ 1
        exact norm_one.le
      add_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a + b‖ ≤ 1
        exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha' hb')
      zero_mem' := by
        show ‖(0 : K)‖ ≤ 1
        rw [norm_zero]
        exact zero_le_one
      neg_mem' := fun {a} ha => by
        have ha' : ‖a‖ ≤ 1 := ha
        show ‖-a‖ ≤ 1
        rw [norm_neg]
        exact ha' }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BallSubgroup
section
noncomputable def UpperTheory.Reformulated.B.BallSubgroup.ball :
    (L : Type) → [inst : NontriviallyNormedField L] → [IsUltrametricDist L] → ValuationSubring L :=
  fun L _ _ =>
    { carrier := {x : L | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [norm_mul]
        exact mul_le_one₀ ha (norm_nonneg b) hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rwa [norm_neg]
      mem_or_inv_mem' := fun x => by
        simp only [Set.mem_setOf_eq]
        rcases le_total ‖x‖ 1 with h | h
        · exact Or.inl h
        · right
          rw [norm_inv]
          exact inv_le_one_of_one_le₀ h }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BlkB
section
noncomputable def UpperTheory.Reformulated.B.Yha8.blkA :
    {n : ℕ} → ℕ → Finset (Fin n) :=
    fun {n : ℕ} (j : ℕ) ↦ {i : Fin n | (↑i : ℕ) < j}

noncomputable def UpperTheory.Reformulated.B.Yha8.blkB :
    {n : ℕ} → ℕ → Finset (Fin n) :=
    fun {n : ℕ} (j : ℕ) ↦ (UpperTheory.Reformulated.B.Yha8.blkA j)ᶜ

theorem UpperTheory.Reformulated.B.Yha8.main :
    ∀ {n : ℕ} (j : ℕ) (Q S : Matrix (Fin n) (Fin n) ℂ),
      (∀ (a b : Fin n), Q a b ≠ (0 : ℂ) → b ∈ UpperTheory.Reformulated.B.Yha8.blkA j) →
        (∀ (a b : Fin n), S a b ≠ (0 : ℂ) → a ∈ UpperTheory.Reformulated.B.Yha8.blkB j) → Q * S = (0 : Matrix (Fin n) (Fin n) ℂ) := by
  intro n j Q S hQ hS
  ext a c
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hq : Q a b = 0
  · simp [hq]
  by_cases hs : S b c = 0
  · simp [hs]
  exfalso
  have h1 := hQ a b hq
  have h2 := hS b c hs
  unfold UpperTheory.Reformulated.B.Yha8.blkB at h2
  rw [Finset.mem_compl] at h2
  exact h2 h1
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BlockConjugation
section
noncomputable def UpperTheory.Reformulated.B.BlockConjugation.HasFlag :
    {H k : Type} → [inst : Group H] → [inst_1 : CommRing k] → {n : ℕ} → (H →* GL (Fin n) k) → (Fin n → H →* kˣ) → Prop :=
    fun {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k) (κ : Fin n → H →* kˣ) ↦
      ∃ (g : GL (Fin n) k),
        ∀ (s : H),
          (∀ (i j : Fin n), j < i → (↑(g * (r : H → GL (Fin n) k) s * g⁻¹) : Matrix (Fin n) (Fin n) k) i j = (0 : k)) ∧
            ∀ (i : Fin n),
              (↑(g * (r : H → GL (Fin n) k) s * g⁻¹) : Matrix (Fin n) (Fin n) k) i i = (↑((κ i : H → kˣ) s) : k)

private def UpperTheory.Reformulated.B.BlockConjugation.blk {k : Type} [CommRing k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  Matrix.of (Fin.cons (Fin.cons 1 0) (fun i => Fin.cons 0 (A i)))

private theorem UpperTheory.Reformulated.B.BlockConjugation.blk_mul {k : Type} [CommRing k] {n : ℕ} (A B : Matrix (Fin n) (Fin n) k) :
    UpperTheory.Reformulated.B.BlockConjugation.blk A * UpperTheory.Reformulated.B.BlockConjugation.blk B = UpperTheory.Reformulated.B.BlockConjugation.blk (A * B) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [UpperTheory.Reformulated.B.BlockConjugation.blk, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem UpperTheory.Reformulated.B.BlockConjugation.blk_one {k : Type} [CommRing k] {n : ℕ} :
    UpperTheory.Reformulated.B.BlockConjugation.blk (1 : Matrix (Fin n) (Fin n) k) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [UpperTheory.Reformulated.B.BlockConjugation.blk, Matrix.one_apply, (Fin.succ_ne_zero _).symm]

private theorem UpperTheory.Reformulated.B.BlockConjugation.exists_col {k : Type} [Field k] {n : ℕ} (v : Fin (n + 1) → k) (hv : v ≠ 0) :
    ∃ Q : GL (Fin (n + 1)) k, ∀ i, (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i 0 = v i := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hv
  have hd : (((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateCol a v).submatrix id (Equiv.swap 0 a)).det ≠ 0 := by
    rw [Matrix.det_permute', ← Matrix.cramer_apply, Matrix.cramer_one]
    refine mul_ne_zero ?_ (by simpa using ha)
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap 0 a)) with h | h <;> simp [h]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, fun i => ?_⟩
  change (((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateCol a v).submatrix id (Equiv.swap 0 a)) i 0 = v i
  simp

private theorem UpperTheory.Reformulated.B.BlockConjugation.conj_blk {k : Type} [CommRing k] {n : ℕ} (A B : Matrix (Fin n) (Fin n) k)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hM : ∀ i : Fin n, M i.succ 0 = 0) :
    (UpperTheory.Reformulated.B.BlockConjugation.blk A * M * UpperTheory.Reformulated.B.BlockConjugation.blk B) 0 0 = M 0 0 ∧
    (∀ i : Fin n, (UpperTheory.Reformulated.B.BlockConjugation.blk A * M * UpperTheory.Reformulated.B.BlockConjugation.blk B) i.succ 0 = 0) ∧
    (∀ i j : Fin n, (UpperTheory.Reformulated.B.BlockConjugation.blk A * M * UpperTheory.Reformulated.B.BlockConjugation.blk B) i.succ j.succ =
      (A * M.submatrix Fin.succ Fin.succ * B) i j) := by
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩ <;>
    simp [UpperTheory.Reformulated.B.BlockConjugation.blk, Matrix.mul_apply, Fin.sum_univ_succ, hM]

theorem UpperTheory.Reformulated.B.BlockConjugation.exists_common_eigenline :
    ∀ {H k : Type} [inst : Group H] [inst_1 : TopologicalSpace H] [inst_2 : Field k] [inst_3 : TopologicalSpace k]
      [IsTopologicalRing k] {n : ℕ} (r : H →* GL (Fin (n + (1 : ℕ))) k) (κ : Fin (n + (1 : ℕ)) → H →* kˣ)
      (v : Fin (n + (1 : ℕ)) → k),
      Continuous (⇑r : H → GL (Fin (n + (1 : ℕ))) k) →
        v ≠ (0 : Fin (n + (1 : ℕ)) → k) →
          (∀ (g : H),
              (↑((r : H → GL (Fin (n + (1 : ℕ))) k) g) : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k).mulVec v =
                (↑((κ (0 : Fin (n + (1 : ℕ))) : H → kˣ) g) : k) • v) →
            ∃ (p : GL (Fin (n + (1 : ℕ))) k) (r₁ : H →* GL (Fin (n + (1 : ℕ))) k) (r' : H →* GL (Fin n) k),
              (∀ (g : H), (r₁ : H → GL (Fin (n + (1 : ℕ))) k) g = p * (r : H → GL (Fin (n + (1 : ℕ))) k) g * p⁻¹) ∧
                Continuous (⇑r₁ : H → GL (Fin (n + (1 : ℕ))) k) ∧
                  Continuous (⇑r' : H → GL (Fin n) k) ∧
                    (∀ (g : H) (i : Fin n),
                        (↑((r₁ : H → GL (Fin (n + (1 : ℕ))) k) g) : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) i.succ
                            (0 : Fin (n + (1 : ℕ))) =
                          (0 : k)) ∧
                      (∀ (g : H),
                          (↑((r₁ : H → GL (Fin (n + (1 : ℕ))) k) g) : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k)
                              (0 : Fin (n + (1 : ℕ))) (0 : Fin (n + (1 : ℕ))) =
                            (↑((κ (0 : Fin (n + (1 : ℕ))) : H → kˣ) g) : k)) ∧
                        (∀ (g : H) (i j : Fin n),
                            (↑((r₁ : H → GL (Fin (n + (1 : ℕ))) k) g) : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k)
                                i.succ j.succ =
                              (↑((r' : H → GL (Fin n) k) g) : Matrix (Fin n) (Fin n) k) i j) ∧
                          ((UpperTheory.Reformulated.B.BlockConjugation.HasFlag r' fun (i : Fin n) ↦ κ i.succ) → UpperTheory.Reformulated.B.BlockConjugation.HasFlag r κ) := by
  intro H k _ _ _ _ _ n r κ v hr hv hev
  obtain ⟨Q, hQ⟩ := UpperTheory.Reformulated.B.BlockConjugation.exists_col v hv
  let r₁ : H →* GL (Fin (n + 1)) k := (MulAut.conj Q⁻¹).toMonoidHom.comp r
  have hr₁ : ∀ g, r₁ g = Q⁻¹ * r g * Q⁻¹⁻¹ := fun g => rfl
  have hc₁ : Continuous r₁ := by
    have : (⇑r₁) = fun g => Q⁻¹ * r g * Q⁻¹⁻¹ := funext hr₁
    rw [this]
    exact (continuous_const.mul hr).mul continuous_const
  have hQv : (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) k).mulVec (Pi.single 0 1) = v := by
    ext i
    simp [hQ]
  have hcol : ∀ g i, (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i 0 =
      ((κ 0 g : k) • (Pi.single 0 1 : Fin (n + 1) → k)) i := by
    intro g i
    have h1 : (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k).mulVec (Pi.single 0 1) =
        ((κ 0 g : k) • (Pi.single 0 1 : Fin (n + 1) → k)) := by
      rw [hr₁, inv_inv, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQv, hev,
        Matrix.mulVec_smul, ← hQv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [← h1]
    simp
  have h0 : ∀ g (i : Fin n), (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.succ 0 = 0 := by
    intro g i
    rw [hcol]
    simp
  have h00 : ∀ g, (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) 0 0 = (κ 0 g : k) := by
    intro g
    rw [hcol]
    simp
  let φ : H →* Matrix (Fin n) (Fin n) k :=
    { toFun := fun g => (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k).submatrix Fin.succ Fin.succ
      map_one' := by
        ext i j
        simp [Matrix.one_apply]
      map_mul' := fun a b => by
        ext i j
        rw [map_mul, Units.val_mul]
        simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_succ, h0, zero_mul, zero_add] }
  have hφ : ∀ g, φ g = (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k).submatrix Fin.succ Fin.succ := fun g => rfl
  refine ⟨Q⁻¹, r₁, φ.toHomUnits, hr₁, hc₁, ?_, h0, h00, fun g i j => rfl, ?_⟩
  · rw [Units.continuous_iff]
    refine ⟨(Units.continuous_val.comp hc₁).matrix_submatrix _ _, ?_⟩
    have : (fun g => (((φ.toHomUnits g)⁻¹ : (Matrix (Fin n) (Fin n) k)ˣ) : Matrix (Fin n) (Fin n) k)) =
        fun g => (((r₁ g)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k).submatrix
          Fin.succ Fin.succ := by
      funext g
      rw [← map_inv, ← map_inv]
      rfl
    rw [this]
    exact (Units.continuous_coe_inv.comp hc₁).matrix_submatrix _ _
  · rintro ⟨a, ha⟩
    let b : GL (Fin (n + 1)) k :=
      ⟨UpperTheory.Reformulated.B.BlockConjugation.blk (a : Matrix (Fin n) (Fin n) k),
        UpperTheory.Reformulated.B.BlockConjugation.blk ((a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k),
        by rw [UpperTheory.Reformulated.B.BlockConjugation.blk_mul, Units.mul_inv, UpperTheory.Reformulated.B.BlockConjugation.blk_one],
        by rw [UpperTheory.Reformulated.B.BlockConjugation.blk_mul, Units.inv_mul, UpperTheory.Reformulated.B.BlockConjugation.blk_one]⟩
    refine ⟨b * Q⁻¹, fun s => ?_⟩
    have e : ((b * Q⁻¹ * r s * (b * Q⁻¹)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
        UpperTheory.Reformulated.B.BlockConjugation.blk (a : Matrix (Fin n) (Fin n) k) * (r₁ s : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *
          UpperTheory.Reformulated.B.BlockConjugation.blk ((a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
      have : b * Q⁻¹ * r s * (b * Q⁻¹)⁻¹ = b * r₁ s * b⁻¹ := by
        rw [hr₁]
        group
      rw [this]
      rfl
    obtain ⟨c1, c2, c3⟩ := UpperTheory.Reformulated.B.BlockConjugation.conj_blk (a : Matrix (Fin n) (Fin n) k)
      ((a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) _ (h0 s)
    obtain ⟨d1, d2⟩ := ha s
    have e' : ((a * φ.toHomUnits s * a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        (a : Matrix (Fin n) (Fin n) k) *
          (r₁ s : Matrix (Fin (n + 1)) (Fin (n + 1)) k).submatrix Fin.succ Fin.succ *
          ((a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := rfl
    rw [e'] at d1 d2
    rw [e]
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · intro h
        exact absurd h (Fin.not_lt_zero _)
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro _
          exact c2 i
        · intro h
          rw [c3]
          exact d1 i j (Fin.succ_lt_succ_iff.mp h)
    · refine Fin.cases ?_ (fun i => ?_) i
      · rw [c1, h00]
      · rw [c3]
        exact d2 i
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BlockFourMatrices
section
noncomputable def UpperTheory.Reformulated.B.BlockFourMatrices.blk4 :
    {R : Type} →
      {n : ℕ} →
        Matrix (Fin n) (Fin n) R →
          Matrix (Fin n) (Fin n) R →
            Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R → Matrix (Fin (n + n)) (Fin (n + n)) R :=
    fun {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) ↦
      (Matrix.fromBlocks a b c d).submatrix (⇑finSumFinEquiv.symm : Fin (n + n) → Fin n ⊕ Fin n)
        (⇑finSumFinEquiv.symm : Fin (n + n) → Fin n ⊕ Fin n)

theorem UpperTheory.Reformulated.B.BlockFourMatrices.main :
    ∀ {R S : Type} {m : ℕ} (f : R → S) (a b c d : Matrix (Fin m) (Fin m) R),
      (UpperTheory.Reformulated.B.BlockFourMatrices.blk4 a b c d).map f = UpperTheory.Reformulated.B.BlockFourMatrices.blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  intro R S m f a b c d
  unfold UpperTheory.Reformulated.B.BlockFourMatrices.blk4
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BoxBounds
section
noncomputable def UpperTheory.Reformulated.B.BoxBounds.box :
    {K : Type} → [inst : Field K] → {i : ℕ} → K → Submodule (NumberField.RingOfIntegers K) (Fin i → K) :=
    fun {K : Type} [Field K] {i : ℕ} (c : K) ↦ Submodule.pi Set.univ fun (x : Fin i) ↦ NumberField.RingOfIntegers K ∙ c

theorem UpperTheory.Reformulated.B.BoxBounds.exists_box_le :
    ∀ {K : Type} [inst : Field K] [NumberField K] {i : ℕ} (L : Submodule (NumberField.RingOfIntegers K) (Fin i → K)),
      Submodule.span K (↑L : Set (Fin i → K)) = ⊤ →
        ∃ (e : NumberField.RingOfIntegers K),
          e ≠ (0 : NumberField.RingOfIntegers K) ∧
            UpperTheory.Reformulated.B.BoxBounds.box
                ((Algebra.algebraMap (NumberField.RingOfIntegers K) K : NumberField.RingOfIntegers K → K) e) ≤
              L := by
  intro K _ _ i L hL
  classical
  have h : ∀ j : Fin i, ∃ t : nonZeroDivisors (NumberField.RingOfIntegers K),
      (t : NumberField.RingOfIntegers K) • (Pi.single j (1 : K) : Fin i → K) ∈ L := by
    intro j
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
      (nonZeroDivisors (NumberField.RingOfIntegers K)) K (↑L : Set (Fin i → K))
      (Pi.single j (1 : K)) (hL ▸ Submodule.mem_top)
    rw [Submodule.span_eq] at ht
    exact ⟨t, ht⟩
  choose t ht using h
  refine ⟨∏ j, (t j : NumberField.RingOfIntegers K),
    Finset.prod_ne_zero_iff.mpr fun j _ => nonZeroDivisors.coe_ne_zero (t j), ?_⟩
  intro x hx
  rw [← Finset.univ_sum_single x]
  refine L.sum_mem fun j _ => ?_
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (Submodule.mem_pi.mp hx j (Set.mem_univ j))
  obtain ⟨u, hu⟩ : (t j : NumberField.RingOfIntegers K) ∣ ∏ k, (t k : NumberField.RingOfIntegers K) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  have hj : (Pi.single j (x j) : Fin i → K)
      = (a * u) • (t j : NumberField.RingOfIntegers K) • (Pi.single j (1 : K) : Fin i → K) := by
    rw [← ha, hu, smul_smul, ← Pi.single_smul, Algebra.algebraMap_eq_smul_one, smul_smul]
    congr 2
    ring
  rw [hj]
  exact L.smul_mem _ (ht j)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjOfSq
section
theorem UpperTheory.Reformulated.B.Qh56.conj_of_sq :
    ∀ {w : ℂ} {q : ℕ},
    (0 : ℕ) < q → w ^ (2 : ℕ) = (↑q : ℂ) → (starRingEnd ℂ : ℂ → ℂ) w = w := by
  intro w q _ h
  have hs : ((Real.sqrt q : ℝ) : ℂ) ^ 2 = (q : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg q), Complex.ofReal_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (h.trans hs.symm) with hw | hw
  · rw [hw, Complex.conj_ofReal]
  · rw [hw, map_neg, Complex.conj_ofReal]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsPF
section
noncomputable def UpperTheory.Reformulated.B.PolynomialFunction₂.IsPF :
    {A : Type} → [inst : Ring A] → [Algebra ℂ A] → (ℂ → A) → Prop :=
  fun {A} _ _ f => ∃ p : Polynomial A, ∀ Y : ℂ, f Y = Polynomial.eval (algebraMap ℂ A Y) p
end

