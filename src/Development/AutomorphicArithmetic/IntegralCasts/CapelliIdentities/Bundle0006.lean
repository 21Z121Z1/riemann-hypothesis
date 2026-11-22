import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CayleySignature
section
noncomputable def UpperTheory.Reformulated.B.CayleySignature.IsLatIn :
    {R W : Type} →
      [inst : CommRing R] → [inst_1 : AddCommGroup W] → [inst_2 : _root_.Module R W] → Submodule R W → Submodule R W → Prop :=
    fun {R W : Type} [CommRing R] [AddCommGroup W] [_root_.Module R W] (M V : Submodule R W) ↦
      M.FG ∧ M ≤ V ∧ ∀ x ∈ V, ∃ (c : R), c ≠ (0 : R) ∧ c • x ∈ M

theorem UpperTheory.Reformulated.B.CayleySignature.isLatIn_spanK :
    ∀ {O K V : Type} [inst : CommRing O] [IsDomain O] [inst_2 : Field K] [inst_3 : Algebra O K] [IsFractionRing O K]
      [inst_5 : AddCommGroup V] [inst_6 : _root_.Module K V] [inst_7 : _root_.Module O V] [inst_8 : IsScalarTower O K V]
      {N : Submodule O V}, N.FG → UpperTheory.Reformulated.B.CayleySignature.IsLatIn N (Submodule.restrictScalars O (Submodule.span K (↑N : Set V))) := by
  intro O K V _ _ _ _ _ _ _ _ _ N hN
  refine ⟨hN, fun x hx => Submodule.subset_span hx, fun x hx => ?_⟩
  rw [Submodule.restrictScalars_mem] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact N.smul_mem b hay
    · rw [mul_smul]
      exact N.smul_mem a hbz
  | smul k y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors O) k
    refine ⟨a * (q : O), mul_ne_zero ha (nonZeroDivisors.coe_ne_zero q), ?_⟩
    have h1 : (q : O) • (k • y) = p • y := by
      rw [← algebraMap_smul K (q : O), smul_smul, mul_comm, hpq, algebraMap_smul]
    rw [mul_smul, h1, smul_comm]
    exact N.smul_mem p hay
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CayleyTransformPreservesForm
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk20.Mat :
    ℕ → ℕ → Type :=
    fun (k r : ℕ) ↦ Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ

noncomputable def UpperTheory.Reformulated.B.Qk20.Hpk :
    (k r : ℕ) → Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ :=
    fun (k r : ℕ) (i j : Fin ((2 : ℕ) * r + k + (1 : ℕ))) ↦
      if (↑i : ℕ) < r ∧ (↑i : ℕ) + (↑j : ℕ) = (2 : ℕ) * r + k then (1 : ℂ)
      else
        if (↑j : ℕ) < r ∧ (↑i : ℕ) + (↑j : ℕ) = (2 : ℕ) * r + k then (1 : ℂ)
        else if r ≤ (↑i : ℕ) ∧ (↑i : ℕ) ≤ r + k ∧ i = j then if (↑i : ℕ) = r + k then (-1 : ℂ) else (1 : ℂ) else (0 : ℂ)

noncomputable def UpperTheory.Reformulated.B.Qk20.inLie :
    (k r : ℕ) → UpperTheory.Reformulated.B.Qk20.Mat k r → Prop :=
    fun (k r : ℕ) (X : UpperTheory.Reformulated.B.Qk20.Mat k r) ↦
      Matrix.conjTranspose X * UpperTheory.Reformulated.B.Qk20.Hpk k r + UpperTheory.Reformulated.B.Qk20.Hpk k r * X =
        (0 : Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ)

noncomputable def UpperTheory.Reformulated.B.Qk20.UH.{u_1} :
    {ι : Type u_1} → [Fintype ι] → [DecidableEq ι] → Matrix ι ι ℂ → Set (Matrix ι ι ℂ) :=
    fun {ι : Type u_1} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) ↦ {g : Matrix ι ι ℂ | g.conjTranspose * H * g = H}

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk20.GV :
    (k r : ℕ) → Set (UpperTheory.Reformulated.B.Qk20.Mat k r) :=
    fun (k r : ℕ) ↦ UpperTheory.Reformulated.B.Qk20.UH (UpperTheory.Reformulated.B.Qk20.Hpk k r)

noncomputable def UpperTheory.Reformulated.B.Qk20.kap :
    {k r : ℕ} → UpperTheory.Reformulated.B.Qk20.Mat k r → UpperTheory.Reformulated.B.Qk20.Mat k r :=
    fun {k r : ℕ} (Y : UpperTheory.Reformulated.B.Qk20.Mat k r) ↦
      ((1 : UpperTheory.Reformulated.B.Qk20.Mat k r) + Y) * ((1 : UpperTheory.Reformulated.B.Qk20.Mat k r) - Y)⁻¹

private theorem UpperTheory.Reformulated.B.Qk20.cayley_transform_preserves_form {n : Type} [Fintype n] [DecidableEq n]
    (H Y : Matrix n n ℂ) (h : Y.conjTranspose * H + H * Y = 0) (hu : IsUnit (1 - Y).det) :
    ((1 + Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 + Y) * (1 - Y)⁻¹) = H := by
  have key : (1 + Y).conjTranspose * H * (1 + Y) = (1 - Y).conjTranspose * H * (1 - Y) := by
    have h' : Y.conjTranspose * H = -(H * Y) := eq_neg_of_add_eq_zero_left h
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      add_mul, sub_mul, one_mul, h']
    noncomm_ring
  have hinv : (1 - Y) * (1 - Y)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  calc ((1 + Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 + Y) * (1 - Y)⁻¹)
      = ((1 - Y)⁻¹).conjTranspose * ((1 + Y).conjTranspose * H * (1 + Y)) * (1 - Y)⁻¹ := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = ((1 - Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 - Y) * (1 - Y)⁻¹) := by
        rw [key, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = H := by rw [hinv, Matrix.conjTranspose_one, one_mul, mul_one]

theorem UpperTheory.Reformulated.B.Qk20.kap_mem :
    ∀ {k r : ℕ} {Y : UpperTheory.Reformulated.B.Qk20.Mat k r},
      UpperTheory.Reformulated.B.Qk20.inLie k r Y →
        IsUnit (Matrix.det ((1 : UpperTheory.Reformulated.B.Qk20.Mat k r) - Y)) → UpperTheory.Reformulated.B.Qk20.kap Y ∈ UpperTheory.Reformulated.B.Qk20.GV k r := by
  intro k r Y h hu
  exact UpperTheory.Reformulated.B.Qk20.cayley_transform_preserves_form (UpperTheory.Reformulated.B.Qk20.Hpk k r) Y h hu
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ChainLength
section
theorem UpperTheory.Reformulated.B.JointEigenvalueBoundsFromAnyDatum.length_chain :
    ∀ {O X : Type} [inst : CommRing O] [inst_1 : AddCommGroup X]
    [inst_2 : _root_.Module O X] {A B C : Submodule O X},
    A ≤ B →
      B ≤ C →
        Module.length O (↥C ⧸ Submodule.comap C.subtype A) =
          Module.length O (↥B ⧸ Submodule.comap B.subtype A) + Module.length O (↥C ⧸ Submodule.comap C.subtype B) := by
  intro O X _ _ _ A B C hAB hBC
  let f : (↥B ⧸ Submodule.comap B.subtype A) →ₗ[O] (↥C ⧸ Submodule.comap C.subtype A) :=
    Submodule.mapQ _ _ (Submodule.inclusion hBC) (fun x hx => hx)
  let g : (↥C ⧸ Submodule.comap C.subtype A) →ₗ[O] (↥C ⧸ Submodule.comap C.subtype B) :=
    Submodule.mapQ _ _ LinearMap.id (fun x hx => hAB hx)
  refine Module.length_eq_add_of_exact f g ?_ ?_ ?_
  · rw [injective_iff_map_eq_zero]
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      intro h
      have h' : Submodule.Quotient.mk (p := Submodule.comap C.subtype A)
          (Submodule.inclusion hBC x) = 0 := h
      rw [Submodule.Quotient.mk_eq_zero] at h' ⊢
      exact h'
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H x => exact ⟨Submodule.Quotient.mk x, rfl⟩
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      constructor
      · intro h
        have h' : Submodule.Quotient.mk (p := Submodule.comap C.subtype B) x = 0 := h
        rw [Submodule.Quotient.mk_eq_zero] at h'
        exact ⟨Submodule.Quotient.mk ⟨x.1, h'⟩, rfl⟩
      · rintro ⟨z, hz⟩
        rw [← hz]
        induction z using Submodule.Quotient.induction_on with
        | H w =>
          have : Submodule.Quotient.mk (p := Submodule.comap C.subtype B)
              (Submodule.inclusion hBC w) = 0 :=
            (Submodule.Quotient.mk_eq_zero _).2 w.2
          exact this
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CharpolyCoeffValuation
section
private theorem UpperTheory.valuation_perm_term {K Γ ι : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K) (σ : Equiv.Perm ι) :
    v (Equiv.Perm.sign σ • ∏ i, M (σ i) i) = ∏ i, v (M (σ i) i) := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, map_prod]

private theorem UpperTheory.valuation_det_le_one_of_entries_le_one' {K Γ ι : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K)
    (h1 : ∀ i j, v (M i j) ≤ 1) : v M.det ≤ 1 := by
  rw [Matrix.det_apply]
  refine v.map_sum_le fun σ _ => ?_
  rw [UpperTheory.valuation_perm_term]
  exact Finset.prod_le_one' fun i _ => h1 _ _

private theorem UpperTheory.val_det_eq_one_iff {K Γ ι : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [Fintype ι] [DecidableEq ι] [LinearOrder ι] (M : Matrix ι ι K)
    (h1 : ∀ i j, v (M i j) ≤ 1) (h2 : ∀ i j, j < i → v (M i j) < 1) :
    v M.det = 1 ↔ ∀ i, v (M i i) = 1 := by
  have hlt : ∀ (σ : Equiv.Perm ι) (j : ι), v (M (σ j) j) < 1 →
      v (Equiv.Perm.sign σ • ∏ i, M (σ i) i) < 1 := by
    intro σ j hj
    rw [UpperTheory.valuation_perm_term, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (Finset.prod_le_one' fun i _ => h1 _ _)) hj
  have hσ : ∀ σ : Equiv.Perm ι, σ ≠ 1 → v (Equiv.Perm.sign σ • ∏ i, M (σ i) i) < 1 := by
    intro σ hσ
    have : ∃ j, j < σ j := by
      by_contra hcon
      push Not at hcon
      apply hσ
      ext i
      induction i using WellFoundedLT.induction with
      | _ i ih =>
        rcases (hcon i).lt_or_eq with h | h
        · exact σ.injective (ih _ h)
        · exact h
    obtain ⟨j, hj⟩ := this
    exact hlt σ j (h2 _ _ hj)
  constructor
  · intro h i
    by_contra hne
    have hi : v (M i i) < 1 := lt_of_le_of_ne (h1 _ _) hne
    refine absurd h (ne_of_lt ?_)
    rw [Matrix.det_apply]
    refine v.map_sum_lt one_ne_zero fun σ _ => ?_
    by_cases h' : σ = 1
    · exact hlt σ i (by simpa [h'] using hi)
    · exact hσ σ h'
  · intro h
    have h0 : v (Equiv.Perm.sign (1 : Equiv.Perm ι) • ∏ i, M ((1 : Equiv.Perm ι) i) i) = 1 := by
      rw [UpperTheory.valuation_perm_term]
      exact Finset.prod_eq_one fun i _ => h i
    rw [Matrix.det_apply, v.map_sum_eq_of_lt (Finset.mem_univ 1), h0]
    intro σ hσ'
    rw [h0]
    exact hσ σ (by simpa using hσ')

private theorem UpperTheory.prod_lt_of_strictMono {Γ ι : Type} [LinearOrderedCommGroupWithZero Γ]
    [LinearOrder ι] (f : ι → Γ) (hf : StrictMono f) (h0 : ∀ i, 0 < f i) (S T : Finset ι)
    (hc : S.card = T.card) (hne : S ≠ T) (hT : ∀ i j, i ∉ T → j ∈ T → i < j) :
    ∏ i ∈ S, f i < ∏ i ∈ T, f i := by
  have hc' : (S \ T).card = (T \ S).card := Finset.card_sdiff_comm hc
  have hS : (S \ T).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    exact hne (Finset.eq_of_subset_of_card_le hsub hc.ge)
  have hT' : (T \ S).Nonempty := by
    rw [← Finset.card_pos, ← hc', Finset.card_pos]
    exact hS
  obtain ⟨c, hcm, hcmax⟩ := Finset.exists_max_image (S \ T) id hS
  have key : ∏ i ∈ S \ T, f i < ∏ i ∈ T \ S, f i := by
    calc ∏ i ∈ S \ T, f i ≤ ∏ _i ∈ S \ T, f c :=
          Finset.prod_le_prod' fun i hi => hf.monotone (hcmax i hi)
      _ = ∏ _i ∈ T \ S, f c := by simp [hc']
      _ < _ := Finset.prod_lt_prod_of_nonempty (fun _ _ => h0 c)
          (fun i hi => hf (hT _ _ (Finset.mem_sdiff.1 hcm).2 (Finset.mem_sdiff.1 hi).1)) hT'
  rw [← Finset.prod_inter_mul_prod_diff S T, ← Finset.prod_inter_mul_prod_diff T S,
    Finset.inter_comm T S]
  exact mul_lt_mul_of_pos_left key (Finset.prod_pos fun i _ => h0 i)

theorem UpperTheory.charpoly_coeff_valuation :
    ∀ {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (n : ℕ)
        (M : Matrix (Fin n) (Fin n) K) (d : Fin n → K),
        (∀ i j, v (M i j) ≤ 1) → (∀ i j, j < i → v (M i j) < 1) → v M.det = 1 →
        StrictMono (fun i => v (d i)) → (∀ i, d i ≠ 0) →
        ∀ k ≤ n, v ((Matrix.diagonal d * M).charpoly.coeff k) =
          ∏ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), v (d i) := by
  intro K Γ _ _ v n M d h1 h2 hdet hmono hd k hk
  have hdiag := (UpperTheory.val_det_eq_one_iff v M h1 h2).1 hdet
  have hminor : ∀ S : Finset (Fin n),
      v ((Matrix.diagonal d * M).submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det
        = (∏ i ∈ S, v (d i)) *
          v (M.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det := by
    intro S
    have : (Matrix.diagonal d * M).submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)
        = Matrix.of fun i j : S => d i *
          (M.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)) i j := by
      ext i j
      simp
    rw [this, Matrix.det_mul_column, map_mul, map_prod, Finset.prod_coe_sort S fun i => v (d i)]
  set T := Finset.univ.filter (fun i : Fin n => k ≤ i.val) with hT
  have hcard : T.card = n - k := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i : Fin n => k ≤ i.val)
    have h' : (Finset.univ.filter fun i : Fin n => ¬ k ≤ i.val).card = k := by
      simp only [not_le]
      rw [Fin.card_filter_val_lt, min_eq_right hk]
    rw [h', Finset.card_univ, Fintype.card_fin, ← hT] at h
    omega
  have hTval : v ((Matrix.diagonal d * M).submatrix (Subtype.val : T → Fin n)
      (Subtype.val : T → Fin n)).det = ∏ i ∈ T, v (d i) := by
    rw [hminor, (UpperTheory.val_det_eq_one_iff v
      (M.submatrix (Subtype.val : T → Fin n) (Subtype.val : T → Fin n)) (fun i j => h1 _ _)
      (fun i j h => h2 _ _ h)).2 fun i => hdiag _, mul_one]
  have hc := Matrix.charpoly_coeff_eq_sum_minors (Matrix.diagonal d * M) (n - k) (by simp)
  rw [Fintype.card_fin, Nat.sub_sub_self hk] at hc
  have hmem : T ∈ Finset.powersetCard (n - k) (Finset.univ : Finset (Fin n)) := by
    simp [hcard]
  rw [hc, map_mul, map_pow, v.map_neg, map_one, one_pow, one_mul, v.map_sum_eq_of_lt hmem, hTval]
  intro S hS
  rw [hTval, hminor]
  simp only [Finset.mem_sdiff, Finset.mem_powersetCard, Finset.mem_singleton] at hS
  refine lt_of_le_of_lt
    (mul_le_of_le_one_right' (UpperTheory.valuation_det_le_one_of_entries_le_one' v _ fun i j => h1 _ _)) ?_
  refine UpperTheory.prod_lt_of_strictMono (fun i => v (d i)) hmono
    (fun i => zero_lt_iff.2 ((v.ne_zero_iff).2 (hd i))) S T (hS.1.2.trans hcard.symm) hS.2 ?_
  intro i j hi hj
  simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi hj
  exact Fin.lt_def.2 (lt_of_lt_of_le hi hj)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CharpolyPowersRatios
section
noncomputable def UpperTheory.Reformulated.B.CharpolyPowersRatios.FreeRatios :
    {κ ι : Type} → [inst : Field κ] → (ι → κˣ) → Prop :=
    fun {κ ι : Type} [Field κ] (α : ι → κˣ) ↦ ∀ (i j : ι), i ≠ j → ∀ (m : ℕ), (0 : ℕ) < m → α i ^ m ≠ α j ^ m

theorem UpperTheory.Reformulated.B.CharpolyPowersRatios.charpoly_pow :
    ∀ {K : Type} [inst : Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (a : Fin n → Kˣ),
      M.charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : K → Polynomial K) (↑(a i) : K)) →
        UpperTheory.Reformulated.B.CharpolyPowersRatios.FreeRatios a →
          ∀ (d : ℕ),
            (0 : ℕ) < d →
              (M ^ d).charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : K → Polynomial K) ((↑(a i) : K) ^ d)) := by
  intro K _ n M a hM hfree d _
  have hinj : Function.Injective (fun i => (a i : K)) := by
    intro i j hij
    by_contra hne
    exact hfree i j hne 1 one_pos (by simpa using Units.ext hij)
  have hev : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' M) (a i : K) := by
    intro i
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM,
      Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  choose v hv using fun i => (hev i).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' _ (fun i => (a i : K)) hinj v hv
  let b : Module.Basis (Fin n) K (Fin n → K) :=
    basisOfLinearIndependentOfCardEqFinrank' v hli (by simp)
  have hb : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank' v hli _
  have hpow : ∀ j, Matrix.toLin' (M ^ d) (v j) = ((a j : K) ^ d) • v j := by
    intro j
    rw [Matrix.toLin'_pow]
    exact (hv j).pow_apply d
  have hmat : LinearMap.toMatrix b b (Matrix.toLin' (M ^ d)) =
      Matrix.diagonal (fun i => (a i : K) ^ d) := by
    ext i j
    rw [LinearMap.toMatrix_apply, hb, hpow, map_smul, ← hb]
    simp only [Module.Basis.repr_self, Matrix.diagonal_apply, Finsupp.smul_single, Finsupp.single_apply, smul_eq_mul, mul_one]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [← Matrix.charpoly_toLin', ← LinearMap.charpoly_toMatrix _ b, hmat, Matrix.charpoly_diagonal]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CharpolySmul
section
theorem UpperTheory.Reformulated.B.Qh50.charpoly_smul_alt.{u_1, u_2} :
    ∀ {k : Type u_1} {ι : Type u_2} [inst : Field k] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι]
    (M : Matrix ι ι k) {c : k},
    c ≠ (0 : k) →
      (c • M).charpoly =
        (Polynomial.C : k → Polynomial k) (c ^ Fintype.card ι) *
          M.charpoly.comp ((Polynomial.C : k → Polynomial k) c⁻¹ * Polynomial.X) := by
  intro k ι _ _ _ M c hc
  have h1 : M.charpoly.comp (Polynomial.C c⁻¹ * Polynomial.X) =
      ((Polynomial.compRingHom (Polynomial.C c⁻¹ * Polynomial.X)).mapMatrix M.charmatrix).det := by
    rw [← RingHom.map_det]
    rfl
  have h2 : (Polynomial.C c : Polynomial k) * Polynomial.C c⁻¹ = 1 := by
    rw [← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1]
  rw [h1, Polynomial.C_pow, ← Matrix.det_smul, Matrix.charpoly]
  congr 1
  refine Matrix.ext fun i j => ?_
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.charmatrix_apply_eq, smul_eq_mul, Polynomial.coe_compRingHom_apply,
      Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, Polynomial.C_mul]
    rw [mul_sub, ← mul_assoc, h2, one_mul]
  · simp only [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.charmatrix_apply_ne _ _ _ hij, smul_eq_mul, Polynomial.coe_compRingHom_apply,
      Polynomial.neg_comp, Polynomial.C_comp, Polynomial.C_mul, mul_neg]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ChoiceFunction
section
theorem UpperTheory.Reformulated.B.InterpolationPointsOfFinrankBound.pick :
    ∀ {k D : Type} [inst : Field k] (P : Set D) {p0 : D},
    p0 ∈ P →
      ∀ (W : Submodule k (D → k)),
        (∀ (f : D → k), f ∈ W ↔ ∀ p ∈ P, f p = (0 : k)) →
          ∀ (n : ℕ) (Y : Submodule k (D → k)) [FiniteDimensional k ↥Y],
            Module.finrank k ↥Y ≤ n + Module.finrank k ↥(Y ⊓ W) →
              ∃ (u : Fin n → D), (∀ (a : Fin n), u a ∈ P) ∧ ∀ f ∈ Y, (∀ (a : Fin n), f (u a) = (0 : k)) → f ∈ W := by
  intro k D _ P p0 hp0 W hW n
  induction n with
  | zero =>
    intro Y _ h
    refine ⟨fun _ => p0, fun _ => hp0, fun f hf _ => ?_⟩
    have heq : Y ⊓ W = Y :=
      Submodule.eq_of_le_of_finrank_le inf_le_left (by simpa using h)
    rw [← heq] at hf
    exact hf.2
  | succ n ih =>
    intro Y _ h
    by_cases hYW : Y ≤ W
    · exact ⟨fun _ => p0, fun _ => hp0, fun f hf _ => hYW hf⟩
    · obtain ⟨g, hgY, hgW⟩ := SetLike.not_le_iff_exists.mp hYW
      rw [hW] at hgW
      simp only [not_forall] at hgW
      obtain ⟨p, hp, hgp⟩ := hgW
      let K : Submodule k (D → k) := LinearMap.ker (LinearMap.proj p : (D → k) →ₗ[k] k)
      have hK : ∀ f : D → k, f ∈ K ↔ f p = 0 := fun f => LinearMap.mem_ker
      have hWK : W ≤ K := fun f hf => (hK f).2 ((hW f).1 hf p hp)
      haveI : FiniteDimensional k ↥(Y ⊓ K) := Submodule.finiteDimensional_of_le inf_le_left
      have hlt : Y ⊓ K < Y := by
        refine lt_of_le_of_ne inf_le_left fun he => hgp ?_
        rw [← he] at hgY
        exact (hK g).1 hgY.2
      have hrank := Submodule.finrank_lt_finrank_of_lt hlt
      have hinf : (Y ⊓ K) ⊓ W = Y ⊓ W := by
        rw [inf_assoc, inf_eq_right.2 hWK]
      obtain ⟨u, hu, hu'⟩ := ih (Y ⊓ K) (by rw [hinf]; omega)
      refine ⟨Fin.cons p u, fun a => ?_, fun f hf hz => ?_⟩
      · refine Fin.cases ?_ (fun i => ?_) a
        · simpa using hp
        · simpa using hu i
      · refine hu' f ⟨hf, (hK f).2 ?_⟩ fun a => ?_
        · simpa using hz 0
        · simpa using hz a.succ
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ChoiceOfModulusAndDiscriminant
section
open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

noncomputable def UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.CmOK :
    ℕ → ℤ → ℤ → ℕ → Prop :=
    fun (a : ℕ) (b c : ℤ) (d : ℕ) ↦
      (4 : ℤ) * (↑a : ℤ) * c = b ^ (2 : ℕ) + (↑d : ℤ) ∧ Odd a ∧ d % (8 : ℕ) = (7 : ℕ) ∧ Nat.Prime d

noncomputable def UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta :
    ℤ → ℕ → ℂ :=
    fun (b : ℤ) (d : ℕ) ↦ ((↑b : ℂ) + Complex.I * (↑√(↑d : ℝ) : ℂ)) / (2 : ℂ)

@[reducible] noncomputable def UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.KF :
    ℤ → ℕ → IntermediateField ℚ ℂ :=
    fun (b : ℤ) (d : ℕ) ↦ ℚ⟮UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d⟯

private theorem UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_sq (b : ℤ) (d : ℕ) :
    UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d * UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d =
      (b : ℂ) * UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d - ((b : ℂ) ^ 2 + (d : ℂ)) / 4 := by
  have h : ((√(d : ℝ) : ℝ) : ℂ) * ((√(d : ℝ) : ℝ) : ℂ) = (d : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
    simp
  unfold UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta
  linear_combination (((√(d : ℝ) : ℝ) : ℂ) * ((√(d : ℝ) : ℝ) : ℂ) / 4) * Complex.I_mul_I - (1 / 4 : ℂ) * h

private theorem UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_integral (b : ℤ) (d : ℕ) :
    IsIntegral ℚ (UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (b : ℚ) * Polynomial.X
    + Polynomial.C (((b : ℚ) ^ 2 + (d : ℚ)) / 4), ?_, ?_⟩
  · monicity!
  · have h := UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_sq b d
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, eq_ratCast]
    push_cast
    linear_combination h

theorem UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.kap_repr :
    ∀ {a : ℕ} {b c : ℤ} {d : ℕ},
      UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.CmOK a b c d →
        ∀ {x : ℂ}, x ∈ UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.KF b d → ∃ (u : ℚ) (v : ℚ), x = (↑u : ℂ) + (↑v : ℂ) * UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d := by
  intro a b c d _ x hx
  have hx' : x ∈ Algebra.adjoin ℚ {UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.cmTheta b d} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_integral b d).isAlgebraic]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    exact ⟨0, 1, by simp [hy]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨u, v, rfl⟩ := hy
    obtain ⟨u', v', rfl⟩ := hz
    exact ⟨u + u', v + v', by push_cast; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨u, v, rfl⟩ := hy
    obtain ⟨u', v', rfl⟩ := hz
    refine ⟨u * u' - v * v' * (((b : ℚ) ^ 2 + (d : ℚ)) / 4), u * v' + v * u' + v * v' * b, ?_⟩
    push_cast
    linear_combination ((v : ℂ) * (v' : ℂ)) * UpperTheory.Reformulated.B.ChoiceOfModulusAndDiscriminant.theta_sq b d
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ClearDenominatorsLattice
section
theorem UpperTheory.Reformulated.B.ClearDenominatorsLattice.exists_integer_smul_mem_of_span_top :
    ∀ {K V : Type} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V]
    [inst_3 : _root_.Module K V] [inst_4 : _root_.Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (L : Submodule (NumberField.RingOfIntegers K) V),
    Submodule.span K (↑L : Set V) = ⊤ →
      ∀ (x : V), ∃ (r : NumberField.RingOfIntegers K), r ≠ (0 : NumberField.RingOfIntegers K) ∧ r • x ∈ L := by
  intro K V _ _ _ _ _ _ L hL x
  have hx : x ∈ Submodule.span K (↑L : Set V) := hL ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨r, hr, hry⟩ := hy
    obtain ⟨s, hs, hsz⟩ := hz
    refine ⟨r * s, mul_ne_zero hr hs, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact L.smul_mem _ hry
    · rw [mul_smul]
      exact L.smul_mem _ hsz
  | smul a y _ hy =>
    obtain ⟨r, hr, hry⟩ := hy
    obtain ⟨⟨n, d⟩, hnd⟩ :=
      IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) a
    refine ⟨r * d, mul_ne_zero hr (nonZeroDivisors.ne_zero d.2), ?_⟩
    have h1 : (d : NumberField.RingOfIntegers K) • (a • y) = n • y := by
      rw [← algebraMap_smul K (d : NumberField.RingOfIntegers K) (a • y), ← mul_smul, mul_comm,
        hnd, algebraMap_smul]
    rw [mul_smul, h1, ← mul_smul, mul_comm, mul_smul]
    exact L.smul_mem _ hry
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ContinuousHom
section
theorem UpperTheory.Reformulated.B.ContinuousHomomorphism.cont_hom :
    ∀ {Γ M : Type} [inst : Group Γ]
    [inst_1 : TopologicalSpace Γ] [ContinuousInv Γ] [inst_3 : Monoid M] [inst_4 : TopologicalSpace M] (f : Γ →* Mˣ),
    (Continuous fun (g : Γ) ↦ (↑((f : Γ → Mˣ) g) : M)) → Continuous (⇑f : Γ → Mˣ) := by
  intro Γ M _ _ _ _ _ f h
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  refine (h.comp continuous_inv).congr fun g => ?_
  simp only [Function.comp_apply, map_inv]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UpperTriangular
section
noncomputable def UpperTheory.Reformulated.B.UpperTriangular.UT :
    {L : Type} → [Field L] → {n : ℕ} → Matrix (Fin n) (Fin n) L → Prop :=
  fun {_} _ {n} A => (∀ i j : Fin n, j < i → A i j = 0) ∧ ∀ i : Fin n, A i i = 1
end

