import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProjectionCompact
section
noncomputable def UpperTheory.Reformulated.B.ProjectionCompact.piK :
    {T κ : Type} →
      [inst : Fintype T] →
        [inst_1 : DecidableEq T] →
          [inst_2 : Fintype κ] → [inst_3 : DecidableEq κ] → (T → Matrix κ κ ℂ) →* Matrix (T → κ) (T → κ) ℂ :=
  fun {T κ} _ _ _ _ =>
    { toFun := fun M => Matrix.of fun f g => ∏ t, M t (f t) (g t)
      map_one' := by
        ext f g
        simp only [Matrix.of_apply, Pi.one_apply, Matrix.one_apply]
        by_cases h : f = g
        · subst h
          simp
        · obtain ⟨t, ht⟩ := Function.ne_iff.mp h
          rw [if_neg h]
          exact Finset.prod_eq_zero (Finset.mem_univ t) (if_neg ht)
      map_mul' := fun M N => by
        ext f g
        simp only [Matrix.of_apply, Pi.mul_apply, Matrix.mul_apply]
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
        exact Finset.sum_congr rfl fun h _ => Finset.prod_mul_distrib }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProjectiveLineOf
section
noncomputable def UpperTheory.Reformulated.B.ProjectiveLineOf.P1 :
    Prop :=
    ∀ (k : Type) [inst : NontriviallyNormedField k] [LocallyCompactSpace k] [CharZero k] (n : ℕ) (γ : GL (Fin n) k),
      (↑γ : Matrix (Fin n) (Fin n) k).charpoly.Separable →
        ∀ (D : Set (GL (Fin n) k)),
          IsCompact D →
            ∃ (C : Set (GL (Fin n) k)),
              IsCompact C ∧ ∀ (x : GL (Fin n) k), x⁻¹ * γ * x ∈ D → ∃ (t : GL (Fin n) k), t * γ = γ * t ∧ ∃ y ∈ C, x = t * y

section

open Polynomial Matrix

private theorem charpoly_dvd_of_aeval {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (hA : A.charpoly.Separable) (p : k[X]) (hp : aeval A p = 0) : A.charpoly ∣ p := by
  by_cases hp0 : p = 0
  · simp [hp0]
  let K := AlgebraicClosure k
  let f := algebraMap k K
  rw [← Polynomial.map_dvd_map' f]
  have hsep : (A.charpoly.map f).Separable := hA.map
  refine (IsAlgClosed.splits _).dvd_of_roots_le_roots hsep.ne_zero ?_
  rw [Multiset.le_iff_subset (nodup_roots hsep)]
  intro r hr
  have hr' : (A.map f).charpoly.IsRoot r := by
    rw [Matrix.charpoly_map]; exact isRoot_of_mem_roots hr
  rw [← Matrix.mem_spectrum_iff_isRoot_charpoly] at hr'
  have h1 := spectrum.subset_polynomial_aeval (A.map f) (p.map f) ⟨r, hr', rfl⟩
  have h2 : aeval (A.map f) (p.map f) = 0 := by
    have h3 : aeval ((Algebra.ofId k K).mapMatrix A) p = 0 := by
      rw [aeval_algHom_apply, hp, map_zero]
    rw [aeval_map_algebraMap]
    exact h3
  rw [mem_roots (Polynomial.map_ne_zero hp0)]
  by_contra hne
  rw [h2, spectrum.mem_iff, sub_zero] at h1
  exact h1 ((IsUnit.mk0 _ hne).map _)

private def krylov {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k) (v : Fin n → k) :
    Matrix (Fin n) (Fin n) k :=
  Matrix.of fun i j => ((A ^ (j : ℕ)) *ᵥ v) i

private theorem krylov_mulVec {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (v : Fin n → k) (p : k[X]) (hp : p.degree < n) :
    krylov A v *ᵥ (fun j => p.coeff j) = aeval A p *ᵥ v := by
  have h : aeval A p = ∑ j : Fin n, p.coeff j • A ^ (j : ℕ) := by
    conv_lhs => rw [← p.sum_C_mul_X_pow_eq, ← Polynomial.sum_fin _ (by simp) hp]
    simp [Algebra.smul_def]
  rw [h, Matrix.sum_mulVec]
  ext i
  simp [krylov, Matrix.mulVec, dotProduct, Finset.sum_apply, Finset.mul_sum, mul_comm, mul_left_comm,
    mul_assoc]

private theorem exists_krylov_det_ne_zero {k : Type} [Field k] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) (hA : A.charpoly.Separable) :
    ∃ v, (krylov A v).det ≠ 0 := by
  obtain ⟨x, hx⟩ := Module.exists_ker_toSpanSingleton_eq_annihilator k[X]
    (Module.AEval' (Matrix.toLin' A))
  obtain ⟨v, rfl⟩ := (Module.AEval'.of _).surjective x
  refine ⟨v, fun hdet => ?_⟩
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let p : k[X] := (degreeLTEquiv k n).symm c
  have hpdeg : p.degree < n := mem_degreeLT.mp ((degreeLTEquiv k n).symm c).2
  have hpc : (fun j : Fin n => p.coeff j) = c := (degreeLTEquiv k n).apply_symm_apply c
  have hlin : aeval (Matrix.toLin' A) p = Matrix.toLin' (aeval A p) :=
    aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)) A p
  have h1 : aeval A p *ᵥ v = 0 := by rw [← krylov_mulVec A v p hpdeg, hpc, hc]
  have h2 : p ∈ Module.annihilator k[X] (Module.AEval' (Matrix.toLin' A)) := by
    rw [← hx, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply,
      ← Module.AEval.of_aeval_smul, Module.End.smul_def, hlin, Matrix.toLin'_apply, h1, map_zero]
  rw [Module.AEval.annihilator_eq_ker_aeval, RingHom.mem_ker, hlin, map_eq_zero_iff _ Matrix.toLin'.injective] at h2
  have h3 := charpoly_dvd_of_aeval A hA p h2
  have h4 : p = 0 := by
    refine eq_zero_of_dvd_of_degree_lt h3 ?_
    simpa [Matrix.charpoly_degree_eq_dim] using hpdeg
  apply hc0
  rw [← hpc, h4]
  rfl

private theorem mul_krylov {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (v : Fin n → k) :
    A * krylov A v = krylov A v *
      Matrix.of fun i j : Fin n => (X ^ ((j : ℕ) + 1) %ₘ A.charpoly).coeff i := by
  ext i j
  have hdeg : (X ^ ((j : ℕ) + 1) %ₘ A.charpoly).degree < n := by
    simpa [Matrix.charpoly_degree_eq_dim] using
      degree_modByMonic_lt (X ^ ((j : ℕ) + 1)) A.charpoly_monic
  have h := congrFun (krylov_mulVec A v _ hdeg) i
  rw [← Matrix.pow_eq_aeval_mod_charpoly, pow_succ' A, ← Matrix.mulVec_mulVec] at h
  exact h.symm

private theorem continuous_krylov {k : Type} [NontriviallyNormedField k] {n : ℕ} (v : Fin n → k) :
    Continuous fun δ : GL (Fin n) k => krylov (δ : Matrix (Fin n) (Fin n) k) v := by
  refine continuous_matrix fun i j => ?_
  exact (continuous_apply i).comp ((Units.continuous_val.pow _).matrix_mulVec continuous_const)

private theorem exists_compact_krylov {k : Type} [NontriviallyNormedField k] {n : ℕ}
    (v : Fin n → k) (S : Set (GL (Fin n) k)) (hS : IsCompact S)
    (h : ∀ δ ∈ S, (krylov (δ : Matrix (Fin n) (Fin n) k) v).det ≠ 0) :
    ∃ C : Set (GL (Fin n) k), IsCompact C ∧
      ∀ δ ∈ S, ∃ u ∈ C, (u : Matrix (Fin n) (Fin n) k) = krylov (δ : Matrix (Fin n) (Fin n) k) v := by
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let Φ : S → GL (Fin n) k := fun δ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (h δ.1 δ.2)
  have hval : ∀ δ : S, (Φ δ : Matrix (Fin n) (Fin n) k) =
      krylov (δ.1 : Matrix (Fin n) (Fin n) k) v := fun δ => rfl
  have hc : Continuous fun δ : S => krylov (δ.1 : Matrix (Fin n) (Fin n) k) v :=
    (continuous_krylov v).comp continuous_subtype_val
  have hΦ : Continuous Φ := by
    rw [Units.continuous_iff]
    refine ⟨hc, ?_⟩
    simp_rw [Matrix.coe_units_inv, hval, Matrix.inv_def, Ring.inverse_eq_inv']
    exact (hc.matrix_det.inv₀ fun δ => h δ.1 δ.2).smul hc.matrix_adjugate
  exact ⟨Set.range Φ, isCompact_range hΦ, fun δ hδ => ⟨Φ ⟨δ, hδ⟩, ⟨_, rfl⟩, rfl⟩⟩

private theorem isClosed_charpoly_eq {k : Type} [NontriviallyNormedField k] [CharZero k] {n : ℕ}
    (χ : k[X]) :
    IsClosed {δ : GL (Fin n) k | (δ : Matrix (Fin n) (Fin n) k).charpoly = χ} := by
  have h : {δ : GL (Fin n) k | (δ : Matrix (Fin n) (Fin n) k).charpoly = χ} =
      ⋂ r : k, {δ : GL (Fin n) k |
        (Matrix.scalar (Fin n) r - (δ : Matrix (Fin n) (Fin n) k)).det = χ.eval r} := by
    ext δ
    simp only [Set.mem_setOf_eq, Set.mem_iInter, ← Matrix.eval_charpoly]
    exact ⟨fun h r => by rw [h], Polynomial.funext⟩
  rw [h]
  exact isClosed_iInter fun r =>
    isClosed_eq (continuous_const.sub Units.continuous_val).matrix_det continuous_const

end

theorem UpperTheory.Reformulated.B.ProjectiveLineOf.p1_holds :
    UpperTheory.Reformulated.B.ProjectiveLineOf.P1 := by
  intro k _ _ _ n γ hγ D hD
  classical
  set χ := (γ : Matrix (Fin n) (Fin n) k).charpoly with hχ
  have hD' := hD.inter_right (isClosed_charpoly_eq (n := n) χ)
  let U : (Fin n → k) → Set (GL (Fin n) k) := fun v =>
    {δ | (krylov (δ : Matrix (Fin n) (Fin n) k) v).det ≠ 0}
  have hU : ∀ v, IsOpen (U v) := fun v =>
    isOpen_ne_fun (continuous_krylov v).matrix_det continuous_const
  obtain ⟨s, hs⟩ := hD'.elim_finite_subcover U hU (by
    rintro δ ⟨-, hδ⟩
    exact Set.mem_iUnion.mpr (exists_krylov_det_ne_zero _ (by rw [hδ]; exact hγ)))
  obtain ⟨S, hSc, hSU, hS⟩ := hD'.finite_compact_cover s U (fun v _ => hU v) hs
  choose C hCc hC using fun v => exists_compact_krylov v (S v) (hSc v) (hSU v)
  obtain ⟨v₀, hv₀⟩ := exists_krylov_det_ne_zero _ hγ
  let u₀ : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hv₀
  have hu₀ : (u₀ : Matrix (Fin n) (Fin n) k) = krylov (γ : Matrix (Fin n) (Fin n) k) v₀ := rfl
  refine ⟨⋃ v ∈ s, (fun u => u₀ * u⁻¹) '' C v,
    s.isCompact_biUnion fun v _ => (hCc v).image (by fun_prop), fun x hx => ?_⟩
  have hch : ((x⁻¹ * γ * x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly = χ := by
    rw [Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, mul_inv_cancel_left]
  have hmem : x⁻¹ * γ * x ∈ ⋃ v ∈ s, S v := hS ▸ ⟨hx, hch⟩
  obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hmem
  obtain ⟨u, huC, hu⟩ := hC v _ hxv
  have h1 := mul_krylov ((x⁻¹ * γ * x : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) v
  have h2 := mul_krylov (γ : Matrix (Fin n) (Fin n) k) v₀
  rw [← hu, hch] at h1
  rw [← hu₀, ← hχ] at h2
  have h3 : u⁻¹ * (x⁻¹ * γ * x) * u = u₀⁻¹ * γ * u₀ := by
    apply Units.ext
    rw [mul_assoc, mul_assoc u₀⁻¹, Units.val_mul, Units.val_mul, h1, Units.val_mul,
      Units.val_mul, h2, Units.inv_mul_cancel_left, Units.inv_mul_cancel_left]
  refine ⟨x * u * u₀⁻¹, ?_, u₀ * u⁻¹, Set.mem_iUnion₂.mpr ⟨v, hv, u, huC, rfl⟩, by group⟩
  calc x * u * u₀⁻¹ * γ = x * u * (u₀⁻¹ * γ * u₀) * u₀⁻¹ := by group
    _ = γ * (x * u * u₀⁻¹) := by rw [← h3]; group
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PseudoDivision
section
universe u

theorem UpperTheory.pseudo_division :
    ∀ (R : Type u) [CommRing R] (g p : Polynomial R), g ≠ 0 → ∃ (k : ℕ) (q r : Polynomial R), Polynomial.C (g.leadingCoeff ^ k) * p = g * q + r ∧ r.degree < g.degree := by
  intro R _ g p hg
  induction p using (Polynomial.degree_lt_wf (R := R)).induction with
  | _ p ih =>
    by_cases h : p.degree < g.degree
    · exact ⟨0, 0, p, by simp, h⟩
    · have hle : g.degree ≤ p.degree := not_lt.mp h
      have hp : p ≠ 0 := by
        rintro rfl
        rw [Polynomial.degree_zero, le_bot_iff, Polynomial.degree_eq_bot] at hle
        exact hg hle
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Polynomial.natDegree_le_natDegree hle)
      have hlt : (Polynomial.C g.leadingCoeff * p
          - g * Polynomial.monomial d p.leadingCoeff).degree < p.degree := by
        rw [Polynomial.degree_eq_natDegree hp, Polynomial.degree_lt_iff_coeff_zero]
        intro m hm
        obtain ⟨j, rfl⟩ : ∃ j, m = j + d := ⟨m - d, by omega⟩
        rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_mul_monomial]
        rcases Nat.eq_or_lt_of_le hm with he | hl
        · have hj : j = g.natDegree := by omega
          rw [← he, hj]
          exact sub_self _
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hl,
            Polynomial.coeff_eq_zero_of_natDegree_lt (show g.natDegree < j by omega)]
          simp
      obtain ⟨k, q, r, he, hr⟩ := ih _ hlt
      refine ⟨k + 1, q + Polynomial.C (g.leadingCoeff ^ k) * Polynomial.monomial d p.leadingCoeff,
        r, ?_, hr⟩
      rw [pow_succ, Polynomial.C_mul]
      linear_combination he
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PzIffPos
section
noncomputable def UpperTheory.Reformulated.B.Qh60.Pz :
    {R : Type} → [inst : Ring R] → [Algebra ℝ R] → R → Prop :=
    fun {R : Type} [Ring R] [Algebra ℝ R] (t : R) ↦
      ∃ (s : Finset ℝ),
        (∀ l ∈ s, (0 : ℝ) < l) ∧
          (Polynomial.aeval t : Polynomial ℝ → R) (∏ l ∈ s, (Polynomial.X - (Polynomial.C : ℝ → Polynomial ℝ) l)) = (0 : R)

private theorem UpperTheory.Reformulated.B.Qh60.aux {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (T : Module.End ℝ W) (hT : LinearMap.IsSymmetric T) :
    UpperTheory.Reformulated.B.Qh60.Pz T ↔ ∀ x : W, x ≠ 0 → 0 < inner ℝ (T x) x := by
  classical
  have hn : Module.finrank ℝ W = Module.finrank ℝ W := rfl
  set b := hT.eigenvectorBasis hn with hb
  set μ := hT.eigenvalues hn with hμ
  have hev : ∀ i, Module.End.HasEigenvector T (μ i) (b i) := fun i => by
    simpa using hT.hasEigenvector_eigenvectorBasis hn i
  have happ : ∀ i, T (b i) = μ i • b i := fun i => (hev i).apply_eq_smul
  have hne : ∀ i, b i ≠ 0 := fun i => (hev i).2
  have haev : ∀ (s : Finset ℝ) i,
      (Polynomial.aeval T (∏ l ∈ s, (Polynomial.X - Polynomial.C l))) (b i)
        = (∏ l ∈ s, (μ i - l)) • b i := fun s i => by
    rw [Module.End.aeval_apply_of_hasEigenvector (hev i)]
    simp [Polynomial.eval_prod]
  constructor
  · rintro ⟨s, hs, h0⟩ x hx
    have hpos : ∀ i, 0 < μ i := fun i => by
      have h1 := haev s i
      rw [h0, LinearMap.zero_apply, eq_comm, smul_eq_zero] at h1
      obtain ⟨l, hl, h2⟩ := Finset.prod_eq_zero_iff.1 (h1.resolve_right (hne i))
      rw [sub_eq_zero.1 h2]
      exact hs l hl
    have hsum : inner ℝ (T x) x = ∑ i, μ i * (inner ℝ (b i) x) ^ 2 := by
      rw [← b.sum_inner_mul_inner (T x) x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hT x (b i), happ i, real_inner_smul_right, real_inner_comm (b i) x]
      ring
    have hex : ∃ i, inner ℝ (b i) x ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hx
      rw [← b.sum_repr' x]
      simp [hc]
    obtain ⟨i, hi⟩ := hex
    rw [hsum]
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hpos j).le (sq_nonneg _))
      ⟨i, Finset.mem_univ i, mul_pos (hpos i) (by positivity)⟩
  · intro h
    refine ⟨Finset.univ.image μ, ?_, ?_⟩
    · intro l hl
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hl
      have h1 := h (b i) (hne i)
      rw [happ i, real_inner_smul_left] at h1
      exact (pos_iff_pos_of_mul_pos h1).2 (real_inner_self_pos.2 (hne i))
    · refine b.toBasis.ext fun i => ?_
      rw [OrthonormalBasis.coe_toBasis, haev, LinearMap.zero_apply,
        Finset.prod_eq_zero (Finset.mem_image_of_mem μ (Finset.mem_univ i)) (sub_self _), zero_smul]

theorem UpperTheory.Reformulated.B.Qh60.Pz_iff_pos :
    ∀ {W : Type} [inst : AddCommGroup W] [inst_1 : _root_.Module ℝ W] [FiniteDimensional ℝ W] (Q : W →ₗ[ℝ] W →ₗ[ℝ] ℝ),
      (∀ (x y : W), ((Q : W → W →ₗ[ℝ] ℝ) x : W → ℝ) y = ((Q : W → W →ₗ[ℝ] ℝ) y : W → ℝ) x) →
        (∀ (x : W), x ≠ (0 : W) → (0 : ℝ) < ((Q : W → W →ₗ[ℝ] ℝ) x : W → ℝ) x) →
          ∀ (T : Module.End ℝ W),
            (∀ (x y : W),
                ((Q : W → W →ₗ[ℝ] ℝ) ((T : W → W) x) : W → ℝ) y = ((Q : W → W →ₗ[ℝ] ℝ) x : W → ℝ) ((T : W → W) y)) →
              (UpperTheory.Reformulated.B.Qh60.Pz T ↔ ∀ (x : W), x ≠ (0 : W) → (0 : ℝ) < ((Q : W → W →ₗ[ℝ] ℝ) ((T : W → W) x) : W → ℝ) x) := by
  intro W _ _ _ Q hsymm hpos T hT
  let c : InnerProductSpace.Core ℝ W :=
    { inner := fun x y => Q x y
      conj_inner_symm := fun x y => by simpa using hsymm y x
      re_inner_nonneg := fun x => by
        by_cases hx : x = 0
        · simp [hx]
        · simpa using (hpos x hx).le
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun x hx => by
        by_contra h
        exact (hpos x h).ne' hx }
  letI : NormedAddCommGroup W := @InnerProductSpace.Core.toNormedAddCommGroup ℝ W _ _ _ c
  letI : InnerProductSpace ℝ W := InnerProductSpace.ofCore c.toCore
  exact UpperTheory.Reformulated.B.Qh60.aux T (fun x y => hT x y)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.QuotientBasisFiniteModule
section
theorem UpperTheory.Reformulated.B.FiniteModuleImageInFiniteExtension.qb_fdmod :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {M : Type}
    [inst_1 : AddCommGroup M] [inst_2 : _root_.Module ℤ_[l] M] [Module.Finite ℤ_[l] M] (f : M →ₗ[ℤ_[l]] PadicAlgCl l),
    ∃ (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
      FiniteDimensional ℚ_[l] ↥K ∧ ∀ (x : M), (f : M → PadicAlgCl l) x ∈ K := by
  intro l _ M _ _ hM f
  obtain ⟨S, hS⟩ := hM.fg_top
  have hfin : (f '' (S : Set M)).Finite := S.finite_toSet.image _
  haveI : Finite (f '' (S : Set M)) := hfin.to_subtype
  refine ⟨IntermediateField.adjoin ℚ_[l] (f '' (S : Set M)), ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin
      (fun x _ => Algebra.IsIntegral.isIntegral x)
  · intro x
    have hx : x ∈ Submodule.span ℤ_[l] (S : Set M) := by
      rw [hS]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha =>
      rw [map_smul, ← IsScalarTower.algebraMap_smul ℚ_[l] c (f a)]
      exact IntermediateField.smul_mem _ ha
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RadFinAdjoinStable
section
noncomputable def UpperTheory.Reformulated.B.Qj9.Stable :
    {M : Type} → [inst : AddCommGroup M] → [inst_1 : _root_.Module ℂ M] → Set (Module.End ℂ M) → Submodule ℂ M → Prop :=
    fun {M : Type} [AddCommGroup M] [_root_.Module ℂ M] (Op : Set (Module.End ℂ M)) (P : Submodule ℂ M) ↦
      ∀ g ∈ Op, ∀ x ∈ P, (g : M → M) x ∈ P

theorem UpperTheory.Reformulated.B.Qj9.radFin_adjoin_stable :
    ∀ {M : Type} [inst : AddCommGroup M] [inst_1 : _root_.Module ℂ M] (Op : Set (Module.End ℂ M)) (P : Submodule ℂ M),
      UpperTheory.Reformulated.B.Qj9.Stable Op P → ∀ e ∈ Algebra.adjoin ℂ Op, ∀ x ∈ P, (e : M → M) x ∈ P := by
  intro M _ _ Op P h e he
  induction he using Algebra.adjoin_induction with
  | mem g hg => exact h g hg
  | algebraMap r =>
    intro x hx
    rw [Module.algebraMap_end_apply]
    exact P.smul_mem r hx
  | add a b _ _ ha hb =>
    intro x hx
    rw [LinearMap.add_apply]
    exact P.add_mem (ha x hx) (hb x hx)
  | mul a b _ _ ha hb =>
    intro x hx
    rw [Module.End.mul_apply]
    exact ha _ (hb x hx)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RayPrimeSpan
section
theorem UpperTheory.Reformulated.B.Qi16.rayPrime_span :
    ∀
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (p : ℕ),
    Nat.Prime p →
      (↑p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal → v.asIdeal = Ideal.span {(↑p : NumberField.RingOfIntegers ℚ)} := by
  intro v p hp hmem
  have hprime : Prime (p : NumberField.RingOfIntegers ℚ) := by
    rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv]
    rw [map_natCast]
    exact Nat.prime_iff_prime_int.mp hp
  have hP : (Ideal.span {(p : NumberField.RingOfIntegers ℚ)}).IsPrime :=
    (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  have hne : Ideal.span {(p : NumberField.RingOfIntegers ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hprime.ne_zero
  have hmax : (Ideal.span {(p : NumberField.RingOfIntegers ℚ)}).IsMaximal :=
    hP.isMaximal hne
  exact (hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hmem)).symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RealCharacter
section
theorem UpperTheory.Reformulated.B.UnitaryCharacterOfReals.char_real :
    ∀ (f : ℝ → ℂ),
    Continuous f →
      (∀ (s t : ℝ), f (s + t) = f s * f t) →
        (∀ (s : ℝ), ‖f s‖ = (1 : ℝ)) → ∃ (b : ℝ), ∀ (s : ℝ), f s = Complex.exp ((↑(b * s) : ℂ) * Complex.I) := by
  intro f hf hadd hn
  let F : C(ℝ, Circle) :=
    ⟨fun s => ⟨f s, mem_sphere_zero_iff_norm.2 (hn s)⟩, hf.subtype_mk _⟩
  have hF : ∀ s, (F s : ℂ) = f s := fun _ => rfl
  have hFadd : ∀ s t, F (s + t) = F s * F t := fun s t => by
    apply Circle.ext
    rw [Circle.coe_mul, hF, hF, hF, hadd]
  have hF0 : F 0 = 1 := by
    have h := hFadd 0 0
    rw [add_zero] at h
    exact left_eq_mul.1 h
  have cov := Circle.isCoveringMap_exp
  obtain ⟨g, ⟨hg0, hg⟩, -⟩ :=
    cov.existsUnique_continuousMap_lifts F 0 0 (by rw [hF0]; exact Circle.exp_zero)
  have hg' : ∀ s, Circle.exp (g s) = F s := fun s => congrFun hg s
  have gadd : ∀ s t, g (s + t) = g s + g t := fun s t => by
    have h := cov.eq_of_comp_eq (g₁ := fun s : ℝ => g (s + t)) (g₂ := fun s : ℝ => g s + g t)
      (by fun_prop) (by fun_prop)
      (by
        funext s
        show Circle.exp (g (s + t)) = Circle.exp (g s + g t)
        rw [Circle.exp_add, hg', hg', hg', hFadd]) 0 (by simp [hg0])
    exact congrFun h s
  let G : ℝ →+ ℝ := AddMonoidHom.mk' g gadd
  refine ⟨g 1, fun s => ?_⟩
  have hs : g s = g 1 * s := by
    have h := map_real_smul G g.continuous s 1
    simp only [smul_eq_mul, mul_one] at h
    rw [mul_comm]
    exact h
  rw [← hs, ← hF, ← hg', Circle.coe_exp]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RealDiff
section
open MeasureTheory in
private theorem UpperTheory.Reformulated.B.Qh3.one_side {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (ν : Measure Ω) (X : Ω → ι → ℝ) (f : Ω → ℝ) (hX : Measurable X) (hf : Integrable f ν)
    (G : (ι → ℝ) → ℂ) (hG : Measurable G) :
    ∫ x, G x ∂Measure.map X (ν.withDensity fun ω ↦ ENNReal.ofReal (f ω)) =
      ∫ ω, G (X ω) * ((max (f ω) 0 : ℝ) : ℂ) ∂ν := by
  rw [integral_map hX.aemeasurable hG.aestronglyMeasurable]
  have h : AEMeasurable (fun ω ↦ (f ω).toNNReal) ν := hf.aemeasurable.real_toNNReal
  have h2 := integral_withDensity_eq_integral_smul₀ h (fun ω ↦ G (X ω))
  refine Eq.trans h2 ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal', Complex.real_smul, mul_comm]

open MeasureTheory in
private theorem UpperTheory.Reformulated.B.Qh3.int_mul {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (ν : Measure Ω) (X : Ω → ι → ℝ) (f : Ω → ℝ) (hX : Measurable X) (hf : Integrable f ν)
    (G : (ι → ℝ) → ℂ) (hG : Measurable G) (hb : ∀ x, ‖G x‖ ≤ (1 : ℝ)) :
    Integrable (fun ω ↦ G (X ω) * ((max (f ω) 0 : ℝ) : ℂ)) ν := by
  have h1 : Integrable (fun ω ↦ ((max (f ω) 0 : ℝ) : ℂ)) ν := hf.pos_part.ofReal
  exact h1.bdd_mul (c := 1) (hG.comp hX).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω ↦ hb _)

theorem UpperTheory.Reformulated.B.Qh3.real_diff :
    ∀ {Ω ι : Type} [inst : MeasurableSpace Ω] [Fintype ι]
    (ν : MeasureTheory.Measure Ω) (X : Ω → ι → ℝ) (f : Ω → ℝ),
    Measurable X →
      MeasureTheory.Integrable f ν →
        ∀ (G : (ι → ℝ) → ℂ),
          Measurable G →
            (∀ (x : ι → ℝ), ‖G x‖ ≤ (1 : ℝ)) →
              ∫ (x : ι → ℝ), G x ∂MeasureTheory.Measure.map X (ν.withDensity fun (ω : Ω) ↦ ENNReal.ofReal (f ω)) -
                  ∫ (x : ι → ℝ), G x ∂MeasureTheory.Measure.map X (ν.withDensity fun (ω : Ω) ↦ ENNReal.ofReal (-f ω)) =
                ∫ (ω : Ω), G (X ω) * (↑(f ω) : ℂ) ∂ν := by
  intro Ω ι _ _ ν X f hX hf G hG hb
  have hn : MeasureTheory.Integrable (fun ω ↦ -f ω) ν := hf.neg
  rw [UpperTheory.Reformulated.B.Qh3.one_side ν X f hX hf G hG,
    UpperTheory.Reformulated.B.Qh3.one_side ν X (fun ω ↦ -f ω) hX hn G hG,
    ← MeasureTheory.integral_sub (UpperTheory.Reformulated.B.Qh3.int_mul ν X f hX hf G hG hb)
      (UpperTheory.Reformulated.B.Qh3.int_mul ν X (fun ω ↦ -f ω) hX hn G hG hb)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
  have h : max (f ω) 0 - max (-f ω) 0 = f ω := max_zero_sub_max_neg_zero_eq_self (f ω)
  simp only
  rw [← mul_sub, ← Complex.ofReal_sub, h]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ResAlgClosed
section
theorem UpperTheory.Reformulated.B.Qk69.res_algClosed :
    ∀ {Ω : Type} [inst : Field Ω] [IsAlgClosed Ω]
    (A : ValuationSubring Ω), IsAlgClosed (IsLocalRing.ResidueField ↥A) := by
  intro Ω _ _ A
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hsurj : Function.Surjective (IsLocalRing.residue A) := IsLocalRing.residue_surjective
  have hl : p ∈ Polynomial.lifts (IsLocalRing.residue A) :=
    (Polynomial.mem_lifts _).2 (Polynomial.map_surjective _ hsurj p)
  obtain ⟨q, hq, hdeg, hm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hp
  have hd : q.degree ≠ 0 := by
    rw [hdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  have hinj : Function.Injective (algebraMap A Ω) := Subtype.val_injective
  have hd' : (q.map (algebraMap A Ω)).degree ≠ 0 := by
    rwa [hm.degree_map]
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd'
  have hx' : Polynomial.eval₂ (algebraMap A Ω) x q = 0 := by
    rw [← Polynomial.eval_map]
    exact hx
  have hint : IsIntegral A x := ⟨q, hm, hx'⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hy : q.eval y = 0 := by
    apply hinj
    rw [Polynomial.eval₂_at_apply] at hx'
    rw [hx', map_zero]
  refine ⟨IsLocalRing.residue A y, ?_⟩
  rw [← hq, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]
end

