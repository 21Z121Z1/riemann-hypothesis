import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedFrameOfIsotropicColumns
section
namespace GlobalTheory

open Matrix

theorem exists_adapted_frame_of_isotropic_columns :
    ∀ (E : Type) [Field E] (r : ℕ) (Y : Submodule E ((Fin r → E) × (Fin r → E))),
      Module.finrank E Y = r →
      ∀ (C : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E),
        Submodule.span E (Set.range fun j => ((fun a => C.1 a j), (fun a => C.2 a j))) = Y →
        ∀ (s : ℕ) (I : Matrix (Fin r) (Fin s) E), LinearIndependent E I.transpose →
          (∀ j, ((fun a => I a j), (0 : Fin r → E)) ∈ Y) →
          ∃ (t : ℕ) (J : Matrix (Fin r) (Fin s) E) (K : Matrix (Fin r) (Fin t) E)
            (L : Matrix (Fin s) (Fin r) E) (M : Matrix (Fin t) (Fin r) E),
            C.1 * J = I ∧ C.2 * J = 0 ∧ L * J = 1 ∧ L * K = 0 ∧ M * J = 0 ∧ M * K = 1 ∧
              J * L + K * M = 1 := by
  intro E _ r Y _ C hspan s I hI hmem

  have hc : ∀ j, ∃ c : Fin r → E,
      ∑ k, c k • ((fun a => C.1 a k), (fun a => C.2 a k)) = ((fun a => I a j), (0 : Fin r → E)) := by
    intro j
    have := hmem j
    rw [← hspan] at this
    exact (Submodule.mem_span_range_iff_exists_fun E).mp this
  choose c hc using hc
  let J : Matrix (Fin r) (Fin s) E := Matrix.of fun k j => c j k
  have h1 : C.1 * J = I := by
    ext a j
    have := congrFun (congrArg Prod.fst (hc j)) a
    simp only [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, J, Matrix.of_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have h2 : C.2 * J = 0 := by
    ext a j
    have := congrFun (congrArg Prod.snd (hc j)) a
    simp only [Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at this
    simp only [Matrix.mul_apply, J, Matrix.of_apply, Matrix.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

  have hIinj : Function.Injective I.mulVec := Matrix.mulVec_injective_iff.mpr hI
  have hJinj : Function.Injective J.mulVec := by
    intro x y hxy
    apply hIinj
    rw [← h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy]
  let jL : (Fin s → E) →ₗ[E] (Fin r → E) := Matrix.toLin' J
  have hker : LinearMap.ker jL = ⊥ := LinearMap.ker_eq_bot.mpr (by
    intro x y hxy; exact hJinj (by simpa [jL, Matrix.toLin'_apply] using hxy))
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective jL hker
  let Wk := LinearMap.ker g
  let b := Module.finBasis E Wk
  let kL : (Fin (Module.finrank E Wk) → E) →ₗ[E] (Fin r → E) :=
    Wk.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hgP : ∀ x, g (x - jL (g x)) = 0 := by
    intro x
    rw [map_sub]
    have := LinearMap.congr_fun hg (g x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [this, sub_self]
  let ψ : (Fin r → E) →ₗ[E] Wk :=
    LinearMap.codRestrict Wk (LinearMap.id - jL ∘ₗ g) (fun x => by
      simpa [Wk, LinearMap.mem_ker] using hgP x)
  let mL : (Fin r → E) →ₗ[E] (Fin (Module.finrank E Wk) → E) := b.equivFun.toLinearMap ∘ₗ ψ
  have hJ : J = LinearMap.toMatrix' jL := by simp [jL]
  refine ⟨Module.finrank E Wk, J, LinearMap.toMatrix' kL, LinearMap.toMatrix' g,
    LinearMap.toMatrix' mL, h1, h2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hJ, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp]
    have : g ∘ₗ kL = 0 := by
      refine LinearMap.ext fun y => ?_
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, kL]
      exact (b.equivFun.symm y).2
    rw [this, map_zero]
  · rw [hJ, ← LinearMap.toMatrix'_comp]
    have : mL ∘ₗ jL = 0 := by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, mL]
      have : ψ (jL x) = 0 := by
        apply Subtype.ext
        simp only [ψ, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
          LinearMap.comp_apply, ZeroMemClass.coe_zero]
        have := LinearMap.congr_fun hg x
        simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
        rw [this, sub_self]
      rw [this, map_zero]
    rw [this, map_zero]
  · rw [← LinearMap.toMatrix'_comp]
    have : mL ∘ₗ kL = LinearMap.id := by
      refine LinearMap.ext fun y => ?_
      simp only [LinearMap.comp_apply, LinearMap.id_apply, mL]
      have : ψ (kL y) = b.equivFun.symm y := by
        apply Subtype.ext
        have hk : g (kL y) = 0 := (b.equivFun.symm y).2
        simp only [ψ, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
          LinearMap.comp_apply, hk, map_zero, sub_zero]
        rfl
      rw [this]
      exact b.equivFun.apply_symm_apply y
    rw [this, LinearMap.toMatrix'_id]
  · rw [hJ, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp, ← map_add,
      ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, mL, kL]
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.coe_subtype, ψ,
      LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicCoordinatesOfBasisModP
section
namespace GlobalTheory.AdicCoord

theorem eq_zero_of_forall_pow_dvd {R : Type} [CommRing R] (x : R)
    [IsHausdorff (Ideal.span {x}) R] (y : R) (h : ∀ N : ℕ, x ^ N ∣ y) : y = 0 := by
  refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {x}) R) y fun N => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact h N

theorem exists_sum_series {R : Type} [CommRing R] (x : R)
    [IsPrecomplete (Ideal.span {x}) R] (a : ℕ → R) :
    ∃ L : R, ∀ N : ℕ, x ^ N ∣ (∑ k ∈ Finset.range N, x ^ k * a k) - L := by
  have key : ∀ (N : ℕ) (u v : R), u ≡ v [SMOD ((Ideal.span {x}) ^ N • ⊤ : Submodule R R)] ↔
      x ^ N ∣ u - v := by
    intro N u v
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {x}) R)
    (f := fun N => ∑ k ∈ Finset.range N, x ^ k * a k) (by
      intro m n hmn
      rw [key, ← dvd_neg, neg_sub, ← Finset.sum_Ico_eq_sub _ hmn]
      refine Finset.dvd_sum fun k hk => ?_
      exact Dvd.dvd.mul_right (pow_dvd_pow x (Finset.mem_Ico.1 hk).1) _)
  exact ⟨L, fun N => (key N _ _).1 (hL N)⟩

theorem exists_coord : ∀ (p : ℕ) (O EE W RW : Type) [CommRing O] [CommRing EE] [CommRing W] [CommRing RW] [Algebra O EE] [Algebra O RW] (ι : EE →ₐ[O] RW) (c : W →+* RW) (d : ℕ) (o : Fin d → O), (∀ r : RW, ∃! w : Fin d → W, r = ∑ j, o j • c (w j)) → IsAdicComplete (Ideal.span {(p : EE)}) EE → IsAdicComplete (Ideal.span {(p : W)}) W → (∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e - ∑ j, o j • e' j ∈ Ideal.span {(p : EE)}) → ∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e = ∑ j, o j • e' j := by
  intro p O EE W RW _ _ _ _ _ _ ι c d o huniq hE hW hstep e
  choose g hg1 hg2 using hstep
  choose w hw using hg1
  simp only [Ideal.mem_span_singleton] at hg2
  choose h hh using hg2

  have hsep : ∀ r : RW, (∀ N : ℕ, (p : RW) ^ N ∣ r) → r = 0 := by
    intro r hr
    obtain ⟨u, hu, huu⟩ := huniq r
    have hu0 : ∀ j, u j = 0 := by
      intro j
      refine eq_zero_of_forall_pow_dvd (p : W) _ fun N => ?_
      obtain ⟨r', hr'⟩ := hr N
      obtain ⟨u', hu', -⟩ := huniq r'
      have : (fun j => (p : W) ^ N * u' j) = u := by
        apply huu
        rw [hr', hu', Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp
      exact ⟨u' j, by rw [← this]⟩
    rw [hu]
    simp [hu0]
  choose F hF using fun j => exists_sum_series (p : EE) (fun k => g (h^[k] e) j)
  choose V hV using fun j => exists_sum_series (p : W) (fun k => w (h^[k] e) j)
  refine ⟨F, fun j => ⟨V j, ?_⟩, ?_⟩
  · rw [← sub_eq_zero]
    refine hsep _ fun N => ?_
    have h1 := map_dvd ι (hF j N)
    have h2 := map_dvd c (hV j N)
    simp only [map_pow, map_natCast, map_sub, map_sum, map_mul, hw] at h1 h2
    have := dvd_sub h1 h2
    convert this using 1
    ring
  · have hiter : ∀ N : ℕ, e = ∑ j, o j • (∑ k ∈ Finset.range N, (p : EE) ^ k * g (h^[k] e) j)
        + (p : EE) ^ N * h^[N] e := by
      intro N
      induction N with
      | zero => simp
      | succ n ih =>
        have h3 := hh (h^[n] e)
        rw [sub_eq_iff_eq_add] at h3
        rw [Function.iterate_succ_apply']
        simp only [Finset.sum_range_succ, smul_add, Finset.sum_add_distrib]
        have h4 : ∑ j, o j • ((p : EE) ^ n * g (h^[n] e) j)
            = (p : EE) ^ n * ∑ j, o j • g (h^[n] e) j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => (mul_smul_comm _ _ _).symm
        rw [h4]
        linear_combination ih + (p : EE) ^ n * h3
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_pow_dvd (p : EE) _ fun N => ?_
    have h5 : e - ∑ j, o j • F j =
        ∑ j, o j • ((∑ k ∈ Finset.range N, (p : EE) ^ k * g (h^[k] e) j) - F j)
        + (p : EE) ^ N * h^[N] e := by
      simp only [smul_sub, Finset.sum_sub_distrib]
      linear_combination hiter N
    rw [h5]
    refine dvd_add (Finset.dvd_sum fun j _ => ?_) (dvd_mul_right _ _)
    rw [Algebra.smul_def]
    exact Dvd.dvd.mul_left (hF j N) _

end GlobalTheory.AdicCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgHomTraceEqSumMultTrace
section
namespace GlobalTheory

open Matrix

noncomputable def blockDiagMultAlgHom (k : Type) [Field k] (N : ℕ) (n m : Fin N → ℕ) :
    (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₐ[k]
      Matrix (Σ j : (Σ i, Fin (m i)), Fin (n j.1)) (Σ j : (Σ i, Fin (m i)), Fin (n j.1)) k where
  toFun x := blockDiagonal' (fun j : (Σ i, Fin (m i)) => x j.1)
  map_one' := by
    show blockDiagonal' (fun j : (Σ i, Fin (m i)) => (1 : Matrix (Fin (n j.1)) (Fin (n j.1)) k)) = 1
    exact blockDiagonal'_one
  map_mul' x y := by
    simp only [Pi.mul_apply]
    exact blockDiagonal'_mul _ _
  map_zero' := by
    show blockDiagonal' (fun j : (Σ i, Fin (m i)) => (0 : Matrix (Fin (n j.1)) (Fin (n j.1)) k)) = 0
    exact blockDiagonal'_zero
  map_add' x y := by
    simp only [Pi.add_apply]
    exact (blockDiagonal'_add _ _)
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    simp only [Pi.smul_apply, Pi.one_apply]
    rw [show (fun j : (Σ i, Fin (m i)) => r • (1 : Matrix (Fin (n j.1)) (Fin (n j.1)) k))
        = r • (fun j => 1) from rfl, blockDiagonal'_smul]
    congr 1
    exact blockDiagonal'_one

theorem blockDiagMultAlgHom_trace (k : Type) [Field k] (N : ℕ) (n m : Fin N → ℕ)
    (x : Π i, Matrix (Fin (n i)) (Fin (n i)) k) :
    (blockDiagMultAlgHom k N n m x).trace = ∑ i, (m i : k) * (x i).trace := by
  show (blockDiagonal' (fun j : (Σ i, Fin (m i)) => x j.1)).trace = _
  rw [trace_blockDiagonal', Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ∑ _y : Fin (m i), (x i).trace = _
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem exists_algHom_trace_eq_sum_mult_trace : ∀ (k : Type) [Field k] (N : ℕ) (n m : Fin N → ℕ) (d : ℕ),
    ∑ i, m i * n i = d → ∃ ρ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₐ[k] Matrix (Fin d) (Fin d) k,
      ∀ x, (ρ x).trace = ∑ i, (m i : k) * (x i).trace := by
  intro k _ N n m d hd
  have hcard : Fintype.card (Σ j : (Σ i, Fin (m i)), Fin (n j.1)) = d := by
    rw [Fintype.card_sigma, Fintype.sum_sigma, ← hd]
    simp [mul_comm]
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨(reindexAlgEquiv k k e).toAlgHom.comp (blockDiagMultAlgHom k N n m), fun x => ?_⟩
  rw [← blockDiagMultAlgHom_trace]
  show (reindex e e (blockDiagMultAlgHom k N n m x)).trace = _
  simp only [reindex_apply, trace, diag, submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => blockDiagMultAlgHom k N n m x i i)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlternatingFormLeftCorankLeOne
section
namespace GlobalTheory.AltCorank

open Module

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

def Good (S₁ S₂ : Submodule K V) : Prop :=
  ∃ ω : V →ₗ[K] V →ₗ[K] K, (∀ v, ω v v = 0) ∧ ∀ x : Fin 2 → V, (∀ a, x a ∈ S₁) →
    (∀ a, ∀ y ∈ S₂, ω (x a) y = 0) → ¬ LinearIndependent K x

theorem good_step (S₁ S₂ T₁ T₂ : Submodule K V) (u v : V) (φ ψ : V →ₗ[K] K)
    (hφu : φ u = 1) (hφv : φ v = 0) (hψu : ψ u = 0) (hψv : ψ v = 1) (hv : v ∈ S₂)
    (hu : u ∈ S₂ ∨ ∀ x ∈ S₁, ψ x = 0)
    (h₁ : ∀ x ∈ S₁, φ x = 0 → ψ x = 0 → x ∈ T₁)
    (h₂ : ∀ y ∈ T₂, y ∈ S₂ ∧ φ y = 0 ∧ ψ y = 0) (h : Good T₁ T₂) : Good S₁ S₂ := by
  obtain ⟨ω, hω, hk⟩ := h
  let π : V →ₗ[K] V := LinearMap.id - φ.smulRight u - ψ.smulRight v
  have hπ : ∀ x, π x = x - φ x • u - ψ x • v := fun x => rfl
  let Ω : V →ₗ[K] V →ₗ[K] K :=
    ω.compl₁₂ π π + (LinearMap.mul K K).compl₁₂ φ ψ - (LinearMap.mul K K).compl₁₂ ψ φ
  have hΩ : ∀ x y, Ω x y = ω (π x) (π y) + φ x * ψ y - ψ x * φ y := fun x y => rfl
  have hπu : π u = 0 := by simp [hπ, hφu, hψu]
  have hπv : π v = 0 := by simp [hπ, hφv, hψv]
  refine ⟨Ω, fun x => by rw [hΩ, hω]; ring, fun x hx hz => ?_⟩
  have e1 : ∀ a, φ (x a) = 0 := fun a => by
    have := hz a v hv
    rw [hΩ, hπv, hφv, hψv] at this
    simpa using this
  have e2 : ∀ a, ψ (x a) = 0 := fun a => by
    rcases hu with hu | hu
    · have := hz a u hu
      rw [hΩ, hπu, hφu, hψu] at this
      simpa using this
    · exact hu _ (hx a)
  refine hk x (fun a => h₁ _ (hx a) (e1 a) (e2 a)) fun a y hy => ?_
  obtain ⟨hy, f1, f2⟩ := h₂ y hy
  have := hz a y hy
  rw [hΩ, hπ, hπ, e1, e2, f1, f2] at this
  simpa using this

theorem finrank_inf_ker [Module.Finite K V] (S : Submodule K V) (φ : V →ₗ[K] K) (u : V)
    (hu : u ∈ S) (hφ : φ u = 1) :
    finrank K (S ⊓ LinearMap.ker φ : Submodule K V) + 1 = finrank K S := by
  have hne : (φ.domRestrict S : Module.Dual K S) ≠ 0 := by
    intro h
    have := LinearMap.congr_fun h ⟨u, hu⟩
    simp [hφ] at this
  rw [← Module.Dual.finrank_ker_add_one_of_ne_zero hne, LinearMap.ker_domRestrict,
    ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]

theorem exists_dual (S : Submodule K V) (u : V) (hu : u ∉ S) :
    ∃ φ : V →ₗ[K] K, φ u = 1 ∧ ∀ x ∈ S, φ x = 0 := by
  obtain ⟨f, hf, hS⟩ := S.exists_dual_map_eq_bot_of_notMem hu inferInstance
  refine ⟨(f u)⁻¹ • f, by simp [hf], fun x hx => ?_⟩
  have : f x ∈ S.map f := ⟨x, hx, rfl⟩
  rw [hS] at this
  simp [(Submodule.mem_bot K).1 this]

theorem good_of_finrank_eq [Module.Finite K V] (n : ℕ) :
    ∀ S₁ S₂ : Submodule K V, finrank K S₁ = n → finrank K S₂ = n → Good S₁ S₂ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S₁ S₂ h₁ h₂
  by_cases hE : S₁ = S₂
  · subst hE
    by_cases hx : ∃ x : Fin 2 → V, (∀ a, x a ∈ S₁) ∧ LinearIndependent K x
    · obtain ⟨x, hx, hli⟩ := hx
      have n0 : x 0 ∉ Submodule.span K {x 1} := by
        have := hli.notMem_span_image (s := {1}) (x := 0) (by simp)
        simpa using this
      have n1 : x 1 ∉ Submodule.span K {x 0} := by
        have := hli.notMem_span_image (s := {0}) (x := 1) (by simp)
        simpa using this
      obtain ⟨φ, a1, a2⟩ := exists_dual _ _ n0
      obtain ⟨ψ, b1, b2⟩ := exists_dual _ _ n1
      have a3 := a2 _ (Submodule.mem_span_singleton_self _)
      have b3 := b2 _ (Submodule.mem_span_singleton_self _)
      have hlt : finrank K (S₁ ⊓ LinearMap.ker φ ⊓ LinearMap.ker ψ : Submodule K V) < n := by
        have := finrank_inf_ker S₁ φ _ (hx 0) a1
        have := Submodule.finrank_mono
          (inf_le_left : S₁ ⊓ LinearMap.ker φ ⊓ LinearMap.ker ψ ≤ S₁ ⊓ LinearMap.ker φ)
        omega
      refine good_step S₁ S₁ _ _ (x 0) (x 1) φ ψ a1 a3 b3 b1 (hx 1) (Or.inl (hx 0)) ?_ ?_
        (ih _ hlt _ _ rfl rfl)
      · intro y h1 h2 h3
        exact ⟨⟨h1, h2⟩, h3⟩
      · rintro y ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, h3⟩
    · exact ⟨0, fun _ => rfl, fun x h1 _ h2 => hx ⟨x, h1, h2⟩⟩
  · have l1 : ¬ S₁ ≤ S₂ := fun h => hE (Submodule.eq_of_le_of_finrank_eq h (h₁.trans h₂.symm))
    have l2 : ¬ S₂ ≤ S₁ := fun h =>
      hE (Submodule.eq_of_le_of_finrank_eq h (h₂.trans h₁.symm)).symm
    obtain ⟨u, hu1, hu2⟩ := SetLike.not_le_iff_exists.1 l1
    obtain ⟨v, hv2, hv1⟩ := SetLike.not_le_iff_exists.1 l2
    obtain ⟨φ, a1, a2⟩ := exists_dual _ _ hu2
    obtain ⟨ψ, b1, b2⟩ := exists_dual _ _ hv1
    have c1 := finrank_inf_ker S₁ φ u hu1 a1
    have c2 := finrank_inf_ker S₂ ψ v hv2 b1
    refine good_step S₁ S₂ (S₁ ⊓ LinearMap.ker φ) (S₂ ⊓ LinearMap.ker ψ) u v φ ψ a1 (a2 _ hv2)
      (b2 _ hu1) b1 hv2 (Or.inr b2) ?_ ?_ (ih (n - 1) (by omega) _ _ (by omega) (by omega))
    · intro y h1 h2 _
      exact ⟨h1, h2⟩
    · rintro y ⟨h1, h2⟩
      exact ⟨h1, a2 _ h1, h2⟩

theorem exists_alt_corank_le_one :
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
      (S₁ S₂ : Submodule K V), Module.finrank K S₁ = Module.finrank K S₂ →
      ∃ ω : V →ₗ[K] V →ₗ[K] K, (∀ v, ω v v = 0) ∧ ∀ x : Fin 2 → V, (∀ a, x a ∈ S₁) →
        (∀ a, ∀ y ∈ S₂, ω (x a) y = 0) → ¬ LinearIndependent K x :=
  fun _ _ _ _ _ _ S₁ S₂ h => good_of_finrank_eq _ S₁ S₂ h rfl

end GlobalTheory.AltCorank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAnalyticSubOneDivOneSubUnitMulExp
section
open Filter Topology

namespace GlobalTheory

theorem one_sub_unit_mul_exp_ne_zero (L : ℝ) (hL : 0 < L) (χ : ℂ) (hχ : ‖χ‖ = 1) (t : ℝ)
    (ht : t ≠ 0) : 1 - χ * Complex.exp (-((L : ℂ) * (t : ℂ))) ≠ 0 := by
  intro h
  have h1 : χ * Complex.exp (-((L : ℂ) * (t : ℂ))) = 1 := (sub_eq_zero.mp h).symm
  have h2 := congrArg norm h1
  rw [norm_mul, hχ, one_mul, Complex.norm_exp, norm_one] at h2
  have h3 : (-((L : ℂ) * (t : ℂ))).re = 0 := by
    have := Real.exp_eq_one_iff _ |>.mp h2
    exact this
  simp at h3
  rcases h3 with h3 | h3
  · exact hL.ne' h3
  · exact ht h3

theorem exists_analytic_sub_one_div_one_sub_unit_mul_exp :
    ∀ (L : ℝ), 0 < L → ∀ χ : ℂ, ‖χ‖ = 1 → ∃ h : ℂ → ℂ, (∀ x : ℝ, 0 < x → AnalyticAt ℂ h (x : ℂ)) ∧ (∀ x : ℝ, 1 < x → h (x : ℂ) = ((x : ℂ) - 1) / (1 - χ * Complex.exp (-((L : ℂ) * ((x : ℂ) - 1))))) ∧ (χ ≠ 1 → h 1 = 0) := by
  intro L hL χ hχ
  by_cases h1 : χ = 1
  · subst h1
    set f : ℂ → ℂ := fun w => 1 - Complex.exp (-((L : ℂ) * w)) with hf
    have hfd : Differentiable ℂ f := by
      rw [hf]; fun_prop
    have hkd : Differentiable ℂ (dslope f 0) := by
      rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
      exact hfd.differentiableOn
    have hk : ∀ w : ℂ, w ≠ 0 → dslope f 0 w = f w / w := by
      intro w hw
      rw [dslope_of_ne _ hw, slope_def_field]
      simp [hf]
    have hk0 : dslope f 0 0 = L := by
      rw [dslope_same]
      have : HasDerivAt f (0 - Complex.exp (-((L : ℂ) * 0)) * (-((L : ℂ) * 1))) 0 :=
        (hasDerivAt_const _ _).sub (((hasDerivAt_id (0 : ℂ)).const_mul (L : ℂ)).neg.cexp)
      rw [this.deriv]; simp
    refine ⟨fun s => (dslope f 0 (s - 1))⁻¹, ?_, ?_, fun h => absurd rfl h⟩
    · intro x _
      have hd : Differentiable ℂ (fun s : ℂ => dslope f 0 (s - 1)) :=
        hkd.comp (differentiable_id.sub_const 1)
      refine (hd.analyticAt _).inv ?_
      by_cases hx : x = 1
      · subst hx
        show dslope f 0 (((1 : ℝ) : ℂ) - 1) ≠ 0
        rw [Complex.ofReal_one, sub_self, hk0]
        exact_mod_cast hL.ne'
      · have hx' : x - 1 ≠ 0 := sub_ne_zero.mpr hx
        have hx'' : (x : ℂ) - 1 ≠ 0 := by exact_mod_cast hx'
        show dslope f 0 ((x : ℂ) - 1) ≠ 0
        rw [hk _ hx'']
        refine div_ne_zero ?_ hx''
        have := one_sub_unit_mul_exp_ne_zero L hL 1 hχ (x - 1) hx'
        simpa [hf] using this
    · intro x hx
      have hx' : x - 1 ≠ 0 := sub_ne_zero.mpr hx.ne'
      have hx'' : (x : ℂ) - 1 ≠ 0 := by exact_mod_cast hx'
      show (dslope f 0 ((x : ℂ) - 1))⁻¹ = _
      rw [hk _ hx'', inv_div, one_mul]
  · refine ⟨fun s => (s - 1) / (1 - χ * Complex.exp (-((L : ℂ) * (s - 1)))), ?_, fun _ _ => rfl,
      fun _ => by simp⟩
    intro x _
    have hd : Differentiable ℂ (fun s : ℂ => 1 - χ * Complex.exp (-((L : ℂ) * (s - 1)))) := by
      fun_prop
    have hn : Differentiable ℂ (fun s : ℂ => s - 1) := by fun_prop
    refine (hn.analyticAt _).div (hd.analyticAt _) ?_
    by_cases hx : x = 1
    · subst hx
      simpa [sub_eq_zero] using fun h => h1 (Eq.symm h)
    · have := one_sub_unit_mul_exp_ne_zero L hL χ hχ (x - 1) (sub_ne_zero.mpr hx)
      simpa using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCommonDenominatorAevalOfFg
section
open Polynomial

namespace GlobalTheory

theorem exists_denominator_aeval_elem (O E A : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] (g : A)
    (h : ∀ x : A, ∃ p : E[X], aeval g p = x) (x : A) :
    ∃ c : O, c ≠ 0 ∧ ∃ p : O[X], aeval g p = c • x := by
  obtain ⟨q, rfl⟩ := h x
  obtain ⟨b, hb, hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors O) q
  refine ⟨b, nonZeroDivisors.ne_zero hb, IsLocalization.integerNormalization (nonZeroDivisors O) q, ?_⟩
  rw [← aeval_map_algebraMap E, hq, ← algebraMap_smul E b q, map_smul, algebraMap_smul]

theorem exists_common_denominator_aeval_of_fg (O E A : Type) [CommRing O] [IsDomain O] [Field E]
    [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A]
    [IsScalarTower O E A] (g : A) (h : ∀ x : A, ∃ p : E[X], aeval g p = x)
    (S : Submodule O A) (hS : S.FG) :
    ∃ c : O, c ≠ 0 ∧ ∀ x ∈ S, ∃ p : O[X], aeval g p = c • x := by
  classical
  obtain ⟨s, rfl⟩ := hS
  have key : ∃ c : O, c ≠ 0 ∧ ∀ x ∈ s, ∃ p : O[X], aeval g p = c • x := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | insert a s _ ih =>
      obtain ⟨c, hc, hs⟩ := ih
      obtain ⟨d, hd, p, hp⟩ := exists_denominator_aeval_elem O E A g h a
      refine ⟨c * d, mul_ne_zero hc hd, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ⟨c • p, by rw [map_smul, hp, mul_smul]⟩
      · obtain ⟨q, hq⟩ := hs x hx
        exact ⟨d • q, by rw [map_smul, hq, mul_comm, mul_smul]⟩
  obtain ⟨c, hc, hs⟩ := key
  refine ⟨c, hc, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨p, hp⟩ := hx
    obtain ⟨q, hq⟩ := hy
    exact ⟨p + q, by rw [map_add, hp, hq, smul_add]⟩
  | smul a x _ hx =>
    obtain ⟨p, hp⟩ := hx
    exact ⟨a • p, by rw [map_smul, hp, smul_comm]⟩

end GlobalTheory
end

