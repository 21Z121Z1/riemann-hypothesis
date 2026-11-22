import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0002
import Mathlib.Data.Sym.Card
import Mathlib.Data.Sym.Sym2.Order

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrBdim
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private def borEquiv (K : Type) [Field K] (n : ℕ) (g : GL (Fin n) K) :
    bor g ≃ₗ[K] ({p : Fin n × Fin n // p.1 ≤ p.2} → K) where
  toFun X p := ((g : Matrix (Fin n) (Fin n) K) * X.1 * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) p.1.1 p.1.2
  map_add' X Y := by
    funext p
    simp only [Submodule.coe_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, Pi.add_apply]
  map_smul' c X := by
    funext p
    simp only [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Pi.smul_apply,
      RingHom.id_apply]
  invFun f := ⟨((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (Matrix.of fun i j => if h : i ≤ j then f ⟨(i, j), h⟩ else 0) * (g : Matrix (Fin n) (Fin n) K), by
    intro i j h
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one, Matrix.of_apply, dif_neg (not_le.mpr h)]⟩
  left_inv X := by
    apply Subtype.ext
    have e : (Matrix.of fun i j => if i ≤ j then ((g : Matrix (Fin n) (Fin n) K) * X.1 *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i j else 0) =
        (g : Matrix (Fin n) (Fin n) K) * X.1 * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      ext i j
      rw [Matrix.of_apply]
      split_ifs with h
      · rfl
      · exact (X.2 i j (not_le.mp h)).symm
    show ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (Matrix.of fun i j => if i ≤ j then ((g : Matrix (Fin n) (Fin n) K) * X.1 *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i j else 0) * (g : Matrix (Fin n) (Fin n) K) = X.1
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]
  right_inv f := by
    funext p
    show ((g : Matrix (Fin n) (Fin n) K) * (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (Matrix.of fun i j => if h : i ≤ j then f ⟨(i, j), h⟩ else 0) * (g : Matrix (Fin n) (Fin n) K)) *
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) p.1.1 p.1.2 = f p
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one, Matrix.of_apply, dif_pos p.2]

theorem UpperTheory.V.Fr.pr_bdim :
    ∀ (K : Type) [Field K] (n : ℕ) (g : GL (Fin n) K), 2 * Module.finrank K (bor g) = n * (n + 1) := by
  intro K _ n g
  rw [(borEquiv K n g).finrank_eq, Module.finrank_fintype_fun_eq_card,
    ← Fintype.card_congr (Sym2.sortEquiv (α := Fin n)), Sym2.card, Fintype.card_fin, Nat.choose_two_right,
    Nat.add_sub_cancel, Nat.mul_comm (n + 1) n]
  exact Nat.mul_div_cancel' (Nat.even_mul_succ_self n).two_dvd
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrBrig
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem upT_mul {K : Type} [CommRing K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : UpT A) (hB : UpT B) :
    UpT (A * B) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rcases lt_or_ge c i with hc | hc
  · rw [hA i c hc, zero_mul]
  · rw [hB c j (lt_of_lt_of_le h hc), mul_zero]

private theorem upT_of_comm {K : Type} [Field K] {n : ℕ} {T Z : Matrix (Fin n) (Fin n) K} (hT : UpT T)
    (hd : ∀ i j, i ≠ j → T i i ≠ T j j) (h : UpT (T * Z - Z * T)) : UpT Z := by
  have key : ∀ m : ℕ, ∀ i j : Fin n, n - i.val + j.val = m → j < i → Z i j = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i j hm hji
      have h0 := h i j hji
      have hji' : j.val < i.val := hji
      rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single i, Finset.sum_eq_single j] at h0
      · have h1 : (T i i - T j j) * Z i j = 0 := by linear_combination h0
        exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 (hd i j hji.ne'))
      · intro c _ hc
        rcases lt_or_gt_of_ne hc with hc | hc
        · have hc' : c.val < j.val := hc
          rw [ih (n - i.val + c.val) (by omega) i c rfl (hc.trans hji), zero_mul]
        · rw [hT c j hc, mul_zero]
      · simp
      · intro c _ hc
        rcases lt_or_gt_of_ne hc with hc | hc
        · rw [hT i c hc, zero_mul]
        · have hc' : i.val < c.val := hc
          have := c.isLt
          rw [ih (n - c.val + j.val) (by omega) c j rfl (hji.trans hc), mul_zero]
      · simp
  exact fun i j hij => key _ i j rfl hij

theorem UpperTheory.V.Fr.pr_brig :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}, ∀ (K : Type) [Field K] (ρ : NRep F n K) (B : Box F n K), B.Of ρ → ρ.Good → ∀ (v : F.V) (Y : Matrix (Fin n) (Fin n) K), (∀ s, B.ad (F.loc v s) Y - Y ∈ B.b v) → Y ∈ B.b v := by
  intro l _ k _ F n K _ ρ B hOf hG v Y hY
  obtain ⟨s, hs⟩ := hG.ψd v
  have hT := B.tri v s
  have hr : (B.r (F.loc v s)).right = 1 := (B.nu _).trans (F.loc0 v s).2
  have hres : (B.r (F.loc v s)).mat = ρ.r (F.loc0 v s) := hOf.res (F.loc0 v s)
  have h1 : UpT ((B.g v : Matrix (Fin n) (Fin n) K) * ((B.r (F.loc v s)).adFun Y - Y) *
      (((B.g v)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := hY s
  show UpT ((B.g v : Matrix (Fin n) (Fin n) K) * Y * (((B.g v)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
  refine upT_of_comm hT (fun i j hij => ?_) ?_
  · rw [hres, hOf.psi, hOf.psi]
    exact fun e => hs i j hij (Units.ext e)
  · convert upT_mul h1 hT using 1
    simp only [GG.adFun, hr, if_true, GG.mat, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
      Units.inv_mul_cancel_left]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrCfix
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem card_pairs (n : ℕ) :
    2 * Fintype.card {p : Fin n × Fin n // p.1 < p.2} + n = n * n := by
  have e : {p : Fin n × Fin n // p.1 < p.2} ≃ Σ j : Fin n, {i : Fin n // i < j} :=
    { toFun := fun p => ⟨p.1.2, p.1.1, p.2⟩
      invFun := fun q => ⟨(q.2.1, q.1), q.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  have hc : ∀ j : Fin n, Fintype.card {i : Fin n // i < j} = j := by
    intro j
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun i : Fin n => i < j) = Finset.Iio j := by
      ext i; simp
    rw [this, Fin.card_Iio]
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [hc]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n]
  have hs := Finset.sum_range_id_mul_two n
  cases n with
  | zero => simp
  | succ m =>
    simp only [Nat.add_sub_cancel] at hs
    nlinarith [hs]

private theorem finrank_skew {K : Type} [Field K] {n : ℕ} (h2 : (2 : K) ≠ 0)
    (W : Submodule K (Matrix (Fin n) (Fin n) K)) (S T : Matrix (Fin n) (Fin n) K)
    (hST : S * T = 1) (hTS : T * S = 1) (hW : ∀ X, X ∈ W ↔ (X * S)ᵀ = -(X * S)) :
    Module.finrank K W = Fintype.card {p : Fin n × Fin n // p.1 < p.2} := by
  classical
  let M : ({p : Fin n × Fin n // p.1 < p.2} → K) → Matrix (Fin n) (Fin n) K :=
    fun f => Matrix.of fun i j =>
      if h : i < j then f ⟨(i, j), h⟩ else if h' : j < i then -f ⟨(j, i), h'⟩ else 0
  have hskew : ∀ f, (M f)ᵀ = -(M f) := by
    intro f
    ext i j
    simp only [M, Matrix.transpose_apply, Matrix.neg_apply, Matrix.of_apply]
    split_ifs with h1 h2 h3 h4 <;> first | simp | (exfalso; omega)
  let e : W ≃ₗ[K] ({p : Fin n × Fin n // p.1 < p.2} → K) :=
    { toFun := fun X p => ((X : Matrix (Fin n) (Fin n) K) * S) p.1.1 p.1.2
      map_add' := by
        intro X Y
        funext p
        simp [Matrix.add_mul]
      map_smul' := by
        intro c X
        funext p
        simp [Matrix.smul_mul]
      invFun := fun f => ⟨M f * T, by
        rw [hW, Matrix.mul_assoc, hTS, Matrix.mul_one]
        exact hskew f⟩
      left_inv := by
        intro X
        apply Subtype.ext
        have hX : ((X : Matrix (Fin n) (Fin n) K) * S)ᵀ = -((X : Matrix (Fin n) (Fin n) K) * S) :=
          (hW X).1 X.2
        show M (fun p => ((X : Matrix (Fin n) (Fin n) K) * S) p.1.1 p.1.2) * T = X
        have hM : M (fun p => ((X : Matrix (Fin n) (Fin n) K) * S) p.1.1 p.1.2)
            = (X : Matrix (Fin n) (Fin n) K) * S := by
          ext i j
          have hij := congrFun (congrFun hX i) j
          have hji := congrFun (congrFun hX j) i
          simp only [Matrix.transpose_apply, Matrix.neg_apply] at hij hji
          simp only [M, Matrix.of_apply]
          split_ifs with h1 h3
          · rfl
          · rw [hij, neg_neg]
          · have he : i = j := le_antisymm (not_lt.mp h3) (not_lt.mp h1)
            subst he
            have h22 : 2 * ((X : Matrix (Fin n) (Fin n) K) * S) i i = 0 := by
              linear_combination hij
            exact ((mul_eq_zero.mp h22).resolve_left h2).symm
        rw [hM, Matrix.mul_assoc, hST, Matrix.mul_one]
      right_inv := by
        intro f
        funext p
        obtain ⟨⟨i, j⟩, h⟩ := p
        show (M f * T * S) i j = f ⟨(i, j), h⟩
        rw [Matrix.mul_assoc, hTS, Matrix.mul_one]
        simp [M, h] }
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card]

theorem UpperTheory.V.Fr.pr_cfix :
    ∀ (K : Type) [Field K] (n : ℕ) (x : GG n K), (2 : K) ≠ 0 → x * x = 1 → x.right = -1 → 2 * Module.finrank K (LinearMap.ker (GG.ad n K x - 1)) + n = n * n := by
  intro K _ n x h2 hx hr
  have hg : x.left * theta x.left = 1 := by
    have h := congrArg SemidirectProduct.left hx
    simpa [SemidirectProduct.mul_left, hr, sgnAct_neg_one] using h
  have hG : (x.left : Matrix (Fin n) (Fin n) K)
      = Jmat K n * (x.left : Matrix (Fin n) (Fin n) K)ᵀ * Jmat K n := by
    rw [← theta_inv_val, inv_eq_of_mul_eq_one_left hg]
  have hGJ : (x.left : Matrix (Fin n) (Fin n) K) * Jmat K n
      = Jmat K n * (x.left : Matrix (Fin n) (Fin n) K)ᵀ := by
    nth_rewrite 1 [hG]
    rw [Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.mul_one]
  have hST : ((x.left : Matrix (Fin n) (Fin n) K) * Jmat K n)
      * (Jmat K n * ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Jmat K n), Jmat_mul_Jmat, Matrix.one_mul,
      Units.mul_inv]
  have hTS : (Jmat K n * ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      * ((x.left : Matrix (Fin n) (Fin n) K) * Jmat K n) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      Units.inv_mul, Matrix.one_mul, Jmat_mul_Jmat]
  have hne : x.right ≠ 1 := by
    rw [hr]; decide
  have key : ∀ X : Matrix (Fin n) (Fin n) K, X ∈ LinearMap.ker (GG.ad n K x - 1) ↔
      (X * ((x.left : Matrix (Fin n) (Fin n) K) * Jmat K n))ᵀ
        = -(X * ((x.left : Matrix (Fin n) (Fin n) K) * Jmat K n)) := by
    intro X
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, GG.ad_apply]
    simp only [Module.End.one_apply, GG.adFun, GG.mat, if_neg hne, thetaLie]
    have hL : (x.left : Matrix (Fin n) (Fin n) K) * -(Jmat K n * Xᵀ * Jmat K n)
        * ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        * ((x.left : Matrix (Fin n) (Fin n) K) * Jmat K n)
        = -(X * ((x.left : Matrix (Fin n) (Fin n) K) * Jmat K n))ᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Jmat_transpose, ← hGJ]
      simp only [Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg]
      rw [← Matrix.mul_assoc ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
        Units.inv_mul, Matrix.one_mul, Jmat_mul_Jmat, Matrix.mul_one]
    constructor
    · intro h
      rw [h] at hL
      nth_rewrite 2 [hL]
      rw [neg_neg]
    · intro h
      rw [h, neg_neg] at hL
      have h' := congrArg (· * (Jmat K n * ((x.left⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) hL
      rw [Matrix.mul_assoc _ ((x.left : Matrix (Fin n) (Fin n) K) * Jmat K n), hST, Matrix.mul_one,
        Matrix.mul_assoc X, hST, Matrix.mul_one] at h'
      exact h'
  rw [finrank_skew h2 _ _ _ hST hTS key]
  exact card_pairs n
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrCount
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_count :
    ∀ {K G W V T : Type} [Field K] [Group G] [TopologicalSpace G] [AddCommGroup W] [Module K W] [Module.Finite K W] [AddCommGroup T] [Module K T] [Module.Finite K T] {Gv : V → Type} [∀ v, Group (Gv v)] (loc : ∀ v, Gv v →* G) (ρ : Representation K G W) (b : V → Submodule K W) (φ : T →ₗ[K] (G → W)), (∀ v Y, (∀ s, ρ (loc v s) Y - Y ∈ b v) → Y ∈ b v) → (∀ x ∈ Z1C loc ρ b, ∃ D X, ∀ s, φ D s = x.1 s + (ρ s X - X)) → Module.finrank K (H1C loc ρ b) ≤ Module.finrank K T ∧ ∀ (X₀ : W) (D₀ : T), X₀ ≠ 0 → (∀ s, φ D₀ s = ρ s X₀ - X₀) → Module.finrank K (H1C loc ρ b) + 1 ≤ Module.finrank K T + Module.finrank K (coneH0 ρ b) := by
  intro K G W V T _ _ _ _ _ _ _ _ _ Gv _ loc ρ b φ hA hB
  let cob : W →ₗ[K] (G → W) := LinearMap.pi (fun s => ρ s - LinearMap.id)
  have hcob : ∀ X s, cob X s = ρ s X - X := fun X s => rfl
  let C := LinearMap.range cob
  let f : T →ₗ[K] (G → W) ⧸ C := C.mkQ ∘ₗ φ
  let Ψ : Z1C loc ρ b →ₗ[K] (G → W) ⧸ C :=
    C.mkQ ∘ₗ (LinearMap.fst K (G → W) (V → W)) ∘ₗ (Z1C loc ρ b).subtype
  have hle : Submodule.comap (Z1C loc ρ b).subtype (continuousCoboundaries1 ρ b) ≤ LinearMap.ker Ψ := by
    rintro ⟨x, hx⟩ hxB
    rw [Submodule.mem_comap] at hxB
    obtain ⟨X, hX, -⟩ := hxB
    rw [LinearMap.mem_ker]
    show C.mkQ x.1 = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨X, funext fun s => ((hX s).trans (hcob X s).symm).symm⟩
  have hker : LinearMap.ker Ψ ≤ Submodule.comap (Z1C loc ρ b).subtype (continuousCoboundaries1 ρ b) := by
    rintro ⟨x, hx⟩ hk
    rw [LinearMap.mem_ker] at hk
    change C.mkQ x.1 = 0 at hk
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hk
    obtain ⟨X, hX⟩ := hk
    obtain ⟨-, -, hloc⟩ := hx
    rw [Submodule.mem_comap]
    refine ⟨X, fun s => (congrFun hX s).symm, fun v => ?_⟩
    have hmem : X - x.2 v ∈ b v := by
      refine hA v _ (fun s => ?_)
      have h1 := hloc v s
      convert h1 using 1
      rw [← hX, hcob, map_sub]
      abel
    have h2 := (b v).neg_mem hmem
    rwa [neg_sub] at h2
  let L := (Submodule.comap (Z1C loc ρ b).subtype (continuousCoboundaries1 ρ b)).liftQ Ψ hle
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker
  have hrange : ∀ y, L y ∈ LinearMap.range f := by
    intro y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨D, X, hD⟩ := hB z.1 z.2
    refine ⟨D, ?_⟩
    show C.mkQ (φ D) = C.mkQ z.1.1
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    refine ⟨X, funext fun s => ?_⟩
    show cob X s = φ D s - z.1.1 s
    rw [hcob, hD]
    abel
  let L' : H1C loc ρ b →ₗ[K] LinearMap.range f := L.codRestrict _ hrange
  have hinj' : Function.Injective L' := fun a c h => hinj (congrArg Subtype.val h)
  have h1 : Module.finrank K (H1C loc ρ b) ≤ Module.finrank K (LinearMap.range f) :=
    LinearMap.finrank_le_finrank_of_injective hinj'
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h3 := LinearMap.finrank_range_le f
  refine ⟨h1.trans h3, ?_⟩
  intro X₀ D₀ hX₀ hD₀
  by_cases hinv : ∀ s, ρ s X₀ = X₀
  · have hH0 : X₀ ∈ coneH0 ρ b := by
      show (∀ g, ρ g X₀ = X₀) ∧ ∀ v, X₀ ∈ b v
      exact ⟨hinv, fun v => hA v X₀ (fun s => by rw [hinv, sub_self]; exact (b v).zero_mem)⟩
    have h4 : Module.finrank K (coneH0 ρ b) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      intro h
      rw [h] at hH0
      exact hX₀ ((Submodule.mem_bot K).1 hH0)
    omega
  · push_neg at hinv
    obtain ⟨s, hs⟩ := hinv
    have hD0 : D₀ ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker]
      show C.mkQ (φ D₀) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨X₀, funext fun t => (hcob X₀ t).trans (hD₀ t).symm⟩
    have hne : D₀ ≠ 0 := by
      rintro rfl
      apply hs
      have h5 := hD₀ s
      rw [map_zero, Pi.zero_apply] at h5
      exact (sub_eq_zero.1 h5.symm)
    have h4 : Module.finrank K (LinearMap.ker f) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero]
      intro h
      rw [h] at hD0
      exact hne ((Submodule.mem_bot K).1 hD0)
    omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrDual
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem tri_zero {K G ι : Type} [Field K] [Fintype ι] [LinearOrder ι] (M : G → Matrix ι ι K) (ω : G → K)
    (Φ : Matrix ι ι K) (hM : ∀ g i j, j < i → M g i j = 0)
    (h : ∀ g i j, ∑ p, M g i p * Φ p j = ω g * ∑ q, Φ i q * M g q j)
    (key : ∀ i j, (∀ g, M g i i * Φ i j = ω g * (Φ i j * M g j j)) → Φ i j = 0) : ∀ i j, Φ i j = 0 := by
  intro i
  induction i using WellFoundedGT.induction with
  | _ i ih =>
  intro j
  induction j using WellFoundedLT.induction with
  | _ j ih' =>
  refine key i j fun g => ?_
  have := h g i j
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j] at this
  · exact this
  · intro q _ hq
    rcases lt_or_gt_of_ne hq with h1 | h1
    · rw [ih' q h1, zero_mul]
    · rw [hM g q j h1, mul_zero]
  · simp
  · intro p _ hp
    rcases lt_or_gt_of_ne hp with h1 | h1
    · rw [hM g i p h1, zero_mul]
    · rw [ih p h1 j, mul_zero]
  · simp

private theorem om_map {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (F : Frame l k) {K : Type} [Field K]
    [CharP K l] (φ : k →+* K) (g : F.Γ) : φ (F.om k g : k) = (F.om K g : K) := by
  have : φ.comp (ZMod.castHom (dvd_refl l) k) = ZMod.castHom (dvd_refl l) K := Subsingleton.elim _ _
  exact RingHom.congr_fun this _

private theorem w_cases {n : ℕ} (hn : n = 2 ∨ n = 3) (i j : Fin n) :
    w n j - w n i = 0 ∨ (w n j - w n i = 1 ∨ w n j - w n i = -1) ∨
      ((w n j - w n i = 2 ∨ w n j - w n i = -2) ∧ j = i.rev) := by
  rcases hn with rfl | rfl
  · revert i j; decide
  · revert i j; decide

private theorem thetaLie_single {K : Type} [Field K] {n : ℕ} (i : Fin n) :
    thetaLie (Matrix.single i i.rev (1 : K)) = -Matrix.single i i.rev (1 : K) := by
  unfold thetaLie
  congr 1
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single b.rev, Matrix.mul_apply, Finset.sum_eq_single a.rev]
  · simp only [Jmat, Matrix.transpose_apply, Matrix.single_apply, Fin.rev_rev, if_true, one_mul, mul_one,
      Fin.rev_inj]
    congr 1
    refine propext ⟨?_, ?_⟩
    · rintro ⟨rfl, rfl⟩; simp
    · rintro ⟨rfl, rfl⟩; simp
  · intro p _ hp
    simp [Jmat, hp]
  · simp
  · intro p _ hp
    have : b ≠ p.rev := fun h => hp (by simp [h])
    simp [Jmat, this]
  · simp

theorem UpperTheory.V.Fr.pr_dual :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (K : Type) [Field K] [CharP K l] (φ : k →+* K) (ρ : NRep F n K) (B : Box F n K), B.Of ρ → ρ.IsBar φ → ((∀ g, UpT (ρ.r g)) ∨ ∀ g, UpT (ρ.r g)ᵀ) → ∀ f : Matrix (Fin n) (Fin n) K →ₗ[K] K, (∀ g X, f (B.ad g X) = F.om K g * f X) → f = 0 := by
  intro l _ k _ _ F C₀ n ok hn K _ _ φ ρ B hB hbar htri f hf
  set Φ : Matrix (Fin n) (Fin n) K := fun i j => f (Matrix.single i j 1) with hΦ
  have hsum : ∀ X : Matrix (Fin n) (Fin n) K, f X = ∑ i, ∑ j, X i j * Φ i j := fun X => by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hΦ, ← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have h0 : ∀ (g : F.G0) X, f (ρ.r g * X) = F.om K g * f (X * ρ.r g) := fun g X => by
    rw [← hf]
    congr 1
    have hr : (B.r g).right = 1 := (B.nu g).trans g.2
    show _ = (B.r g).adFun _
    rw [GG.adFun, if_pos hr, ← hB.res g, GG.mat]
    simp [Matrix.mul_assoc]
  have h1 : ∀ (g : F.G0) i j, ∑ p, ρ.r g p i * Φ p j = F.om K g * ∑ q, Φ i q * ρ.r g j q := fun g i j => by
    have := h0 g (Matrix.single i j 1)
    rw [hsum, hsum] at this
    rw [Finset.sum_eq_single i (s := Finset.univ) (f := fun a => ∑ b, (Matrix.single i j (1 : K) * ρ.r g) a b * Φ a b)]
      at this
    · convert this using 2 with p
      · rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb
          rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hb, zero_mul]
        · simp
      · simp [mul_comm]
    · intro a _ ha
      exact Finset.sum_eq_zero fun b _ => by rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ ha, zero_mul]
    · simp
  have hc : ∀ i, -Φ i i.rev = F.om K F.c * Φ i i.rev := fun i => by
    rw [hΦ]
    dsimp only
    rw [← hf, ← map_neg, ← thetaLie_single]
    congr 1
    have hr : (B.r F.c).right ≠ 1 := by rw [B.nu, ok.del_c]; decide
    have hl : (B.r F.c).left = 1 := Units.ext hB.atc
    show _ = (B.r F.c).adFun _
    rw [GG.adFun, if_neg hr, GG.mat, hl]
    simp
  have key : ∀ i j, (∀ g : F.G0, ρ.r g i i * Φ i j = F.om K g * (Φ i j * ρ.r g j j)) → Φ i j = 0 := by
    intro i j h
    by_contra hne
    have h2 : ∀ g : F.G0, F.om k g * F.Ψ g ^ (w n j - w n i) = 1 := fun g => by
      have e := h g
      rw [hbar.1, hbar.1, ← om_map F φ, mul_comm (Φ i j), ← mul_assoc, ← map_mul] at e
      have e2 := φ.injective (mul_right_cancel₀ hne e)
      rw [← Units.val_mul, Units.val_inj] at e2
      rw [_root_.zpow_sub, ← mul_assoc, ← e2, mul_inv_cancel]
    rcases w_cases hn i j with h3 | h3 | ⟨h3, rfl⟩
    · obtain ⟨g, hg⟩ := ok.f2a
      exact hg (by simpa [h3] using h2 g)
    · obtain ⟨g, hg⟩ := ok.f2b _ h3
      exact hg (h2 g)
    · obtain ⟨g, hg⟩ := ok.f2c _ h3
      apply hg
      rcases Int.units_eq_one_or (F.del g) with hd | hd
      · rw [h2 ⟨g, hd⟩, one_mul]
        simp [Frame.delK, hd]
      · have hm : g * F.c ∈ F.del.ker := by rw [MonoidHom.mem_ker, map_mul, hd, ok.del_c]; rfl
        have e := h2 ⟨_, hm⟩
        have ec : F.om k F.c = -1 := by
          apply Units.ext
          apply φ.injective
          rw [om_map]
          have := hc i
          rw [← neg_one_mul] at this
          rw [← mul_right_cancel₀ hne this]
          simp
        have ed : F.delK k g = -1 := by
          apply Units.ext
          simp [Frame.delK, hd]
        simp only [map_mul, ec, ok.Ψ_c, mul_one] at e
        rw [ed, mul_right_comm, e]
  have hz : ∀ i j, Φ i j = 0 := by
    rcases htri with ht | ht
    · exact tri_zero (ι := (Fin n)ᵒᵈ) (fun g : F.G0 => (ρ.r g)ᵀ) (fun g => F.om K g) Φ
        (fun g i j hij => ht g j i hij) h1 key
    · exact tri_zero (fun g : F.G0 => (ρ.r g)ᵀ) (fun g => F.om K g) Φ ht h1 key
  ext1 X
  simp [hsum, hz]
end

