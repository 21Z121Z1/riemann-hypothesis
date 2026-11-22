import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchurIrreducible
section
noncomputable def UpperTheory.Reformulated.B.SchurIrreducible.Irr :
    {G : Type} → [inst : Group G] → {N : ℕ} → (G →* GL (Fin N) ℂ) → Prop :=
    fun {G : Type} [Group G] {N : ℕ} (ρ : G →* GL (Fin N) ℂ) ↦
      ∀ (S : Submodule ℂ (Fin N → ℂ)),
        (∀ (g : G), ∀ v ∈ S, (↑((ρ : G → GL (Fin N) ℂ) g) : Matrix (Fin N) (Fin N) ℂ).mulVec v ∈ S) → S = ⊥ ∨ S = ⊤

noncomputable def UpperTheory.Reformulated.B.SchurIrreducible.SchurStep :
    Prop :=
    ∀ (G : Type) [inst : Group G] (M : ℕ) (σ : G →* GL (Fin M) ℂ),
      UpperTheory.Reformulated.B.SchurIrreducible.Irr σ →
        ∀ (C : Matrix (Fin M) (Fin M) ℂ),
          (∀ (g : G),
              (↑((σ : G → GL (Fin M) ℂ) g) : Matrix (Fin M) (Fin M) ℂ) * C =
                C * (↑((σ : G → GL (Fin M) ℂ) g) : Matrix (Fin M) (Fin M) ℂ)) →
            ∃ (c : ℂ), C = c • (1 : Matrix (Fin M) (Fin M) ℂ)

theorem UpperTheory.Reformulated.B.SchurIrreducible.schurStep :
    UpperTheory.Reformulated.B.SchurIrreducible.SchurStep := by
  intro G _ M σ hσ C hC
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · exact ⟨0, Subsingleton.elim _ _⟩
  haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' C)
  refine ⟨c, ?_⟩
  have hS := hσ (Module.End.eigenspace (Matrix.toLin' C) c) (by
    intro g v hv
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, ← hC g, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul])
  rcases hS with h | h
  · exact absurd h hc
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    have hv : v ∈ Module.End.eigenspace (Matrix.toLin' C) c := by
      rw [h]; exact Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [hv]
    simp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchurScalar
section
noncomputable def UpperTheory.Reformulated.B.Qi17.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.Qi17.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.Qi17.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.Qi17.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.Qi17.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.Qi17.IsIrrSub r ⊤

theorem UpperTheory.Reformulated.B.Qi17.schur_scalar :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] [IsAlgClosed k] {n : ℕ} (r : Γ →* GL (Fin n) k),
      UpperTheory.Reformulated.B.Qi17.IsIrr r →
        ∀ (g : GL (Fin n) k),
          (∀ (s : Γ), (r : Γ → GL (Fin n) k) s * g = g * (r : Γ → GL (Fin n) k) s) →
            ∃ (c : kˣ), (↑g : Matrix (Fin n) (Fin n) k) = (↑c : k) • (1 : Matrix (Fin n) (Fin n) k) := by
  intro Γ k _ _ _ n r hr g hg
  obtain ⟨hne, -, hmin⟩ := hr
  haveI : Nontrivial (Fin n → k) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hne (Subsingleton.elim _ _)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k))
  have hinv : UpperTheory.Reformulated.B.Qi17.IsInv r
      (Module.End.eigenspace (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) c) := by
    intro s v hv
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
    have h : (g : Matrix (Fin n) (Fin n) k) * (r s : Matrix (Fin n) (Fin n) k)
        = (r s : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k) := by
      rw [← Units.val_mul, ← Units.val_mul, hg s]
    rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  have htop := (hmin _ le_top hinv).resolve_left hc
  have hgc : (g : Matrix (Fin n) (Fin n) k) = c • (1 : Matrix (Fin n) (Fin n) k) := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ Module.End.eigenspace (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) c := by
      rw [htop]; exact Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [hv, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hgc
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → k)
    apply hv
    have h1 : (1 : Matrix (Fin n) (Fin n) k) = 0 := by
      rw [← g.mul_inv, hgc, zero_mul]
    rw [← Matrix.one_mulVec v, h1, Matrix.zero_mulVec]
  exact ⟨Units.mk0 c hc0, hgc⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchurTwistHolds
section
noncomputable def UpperTheory.Reformulated.B.H13.IsInv :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      ∀ (g : Γ), ∀ v ∈ W, (↑((ρ : Γ → GL (Fin a) k) g) : Matrix (Fin a) (Fin a) k).mulVec v ∈ W

noncomputable def UpperTheory.Reformulated.B.H13.IsIrrSub :
    {Γ : Type} →
      [inst : Group Γ] → {k : Type} → [inst_1 : Field k] → {a : ℕ} → (Γ →* GL (Fin a) k) → Submodule k (Fin a → k) → Prop :=
    fun {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) ↦
      W ≠ ⊥ ∧ UpperTheory.Reformulated.B.H13.IsInv ρ W ∧ ∀ W' ≤ W, UpperTheory.Reformulated.B.H13.IsInv ρ W' → W' = ⊥ ∨ W' = W

noncomputable def UpperTheory.Reformulated.B.H13.IsIrr :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) ↦ UpperTheory.Reformulated.B.H13.IsIrrSub r ⊤

noncomputable def UpperTheory.Reformulated.B.H13.RepIso :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → (Γ →* GL (Fin n) k) → Prop :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r r' : Γ →* GL (Fin n) k) ↦
      ∃ (g : GL (Fin n) k), ∀ (s : Γ), (r' : Γ → GL (Fin n) k) s = g * (r : Γ → GL (Fin n) k) s * g⁻¹

theorem UpperTheory.Reformulated.B.H13.aux5 :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ),
      (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) (1 : Γ)) *
          (r : Γ → GL (Fin n) k) (1 : Γ) =
        (1 : GL (Fin n) k) := by
  intro Γ k _ _ n r χ
  simp

theorem UpperTheory.Reformulated.B.H13.aux6 :
    ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (s t : Γ),
      (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) (s * t)) *
          (r : Γ → GL (Fin n) k) (s * t) =
        (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) s) * (r : Γ → GL (Fin n) k) s *
          ((Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) t) * (r : Γ → GL (Fin n) k) t) := by
  intro Γ k _ _ n r χ s t
  have hc : ∀ (c : kˣ) (A : GL (Fin n) k),
      A * Matrix.GeneralLinearGroup.scalar (Fin n) c = Matrix.GeneralLinearGroup.scalar (Fin n) c * A := by
    intro c A
    apply Units.ext
    simp only [Units.val_mul]
    exact (Matrix.scalar_commute (c : k) (fun x => Commute.all _ _) (A : Matrix (Fin n) (Fin n) k)).eq.symm
  rw [map_mul, map_mul, map_mul]
  simp only [mul_assoc]
  rw [← mul_assoc (r s), hc, mul_assoc]

noncomputable def UpperTheory.Reformulated.B.H13.tw :
    {Γ k : Type} → [inst : Group Γ] → [inst_1 : Field k] → {n : ℕ} → (Γ →* GL (Fin n) k) → (Γ →* kˣ) → Γ →* GL (Fin n) k :=
    fun {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) ↦
      {
        toFun := fun (s : Γ) ↦
          (Matrix.GeneralLinearGroup.scalar (Fin n) : kˣ → GL (Fin n) k) ((χ : Γ → kˣ) s) * (r : Γ → GL (Fin n) k) s,
        map_one' := UpperTheory.Reformulated.B.H13.aux5 r χ, map_mul' := UpperTheory.Reformulated.B.H13.aux6 r χ : Γ →* GL (Fin n) k }

noncomputable def UpperTheory.Reformulated.B.H13.SchurTw :
    Prop :=
    ∀ (Γ Γ' k : Type) [inst : Group Γ] [inst_1 : Group Γ'] [inst_2 : Field k] [IsAlgClosed k] (n : ℕ)
      (r : Γ →* GL (Fin n) k) (φ : Γ' →* Γ) (δ : Γ →* kˣ),
      UpperTheory.Reformulated.B.H13.IsIrr (r.comp φ) →
        δ.comp φ = (1 : Γ' →* kˣ) → UpperTheory.Reformulated.B.H13.RepIso r (UpperTheory.Reformulated.B.H13.tw r δ) → δ = (1 : Γ →* kˣ)

theorem UpperTheory.Reformulated.B.H13.schur_twist_holds :
    UpperTheory.Reformulated.B.H13.SchurTw := by
  intro Γ Γ' k _ _ _ _ n r φ δ hirr hδ hiso
  obtain ⟨hne, -, hmin⟩ := hirr
  obtain ⟨g, hg⟩ := hiso
  have hg' : ∀ s : Γ, Matrix.GeneralLinearGroup.scalar (Fin n) (δ s) * r s * g = g * r s := by
    intro s
    have h : Matrix.GeneralLinearGroup.scalar (Fin n) (δ s) * r s = g * r s * g⁻¹ := hg s
    rw [h, inv_mul_cancel_right]
  have hcomm : ∀ t : Γ', r (φ t) * g = g * r (φ t) := by
    intro t
    have h1 : δ (φ t) = 1 := DFunLike.congr_fun hδ t
    have h := hg' (φ t)
    rwa [h1, map_one, one_mul] at h
  haveI : Nontrivial (Fin n → k) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hne (Subsingleton.elim _ _)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k))
  have hmem : ∀ v : Fin n → k,
      v ∈ Module.End.eigenspace (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) c ↔
        (g : Matrix (Fin n) (Fin n) k).mulVec v = c • v := by
    intro v
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  have htop : Module.End.eigenspace (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)) c = ⊤ := by
    refine (hmin _ le_top ?_).resolve_left hc
    intro t v hv
    rw [hmem] at hv ⊢
    have h : (r (φ t) : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k)
        = (g : Matrix (Fin n) (Fin n) k) * (r (φ t) : Matrix (Fin n) (Fin n) k) := by
      rw [← Units.val_mul, ← Units.val_mul, hcomm]
    change (g : Matrix (Fin n) (Fin n) k).mulVec ((r (φ t) : Matrix (Fin n) (Fin n) k).mulVec v)
      = c • (r (φ t) : Matrix (Fin n) (Fin n) k).mulVec v
    rw [Matrix.mulVec_mulVec, ← h, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  have hgv : ∀ v : Fin n → k, (g : Matrix (Fin n) (Fin n) k).mulVec v = c • v := by
    intro v
    rw [← hmem, htop]
    exact Submodule.mem_top
  have hcent : ∀ A : GL (Fin n) k, g * A = A * g := by
    intro A
    apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Units.val_mul, Units.val_mul, Matrix.toLin'_apply, Matrix.toLin'_apply,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgv, hgv, Matrix.mulVec_smul]
  have hn : Nonempty (Fin n) := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact not_subsingleton (Fin n → k) inferInstance
  obtain ⟨i⟩ := hn
  refine MonoidHom.ext fun s => ?_
  have h := hg' s
  rw [hcent, mul_left_inj, mul_eq_right] at h
  have h2 := congrArg (fun A : GL (Fin n) k => (A : Matrix (Fin n) (Fin n) k) i i) h
  apply Units.ext
  simpa using h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzFunctionGeneration
section
open scoped RestrictedProduct
open Filter Set

private lemma UpperTheory.factorizable_generation {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)]
    [∀ i, T2Space (R i)] {A : ∀ i, Set (R i)} (ho : ∀ i, IsOpen (A i))
    (hc : ∀ i, IsCompact (A i)) {κ : Type*} [Finite κ] (v : ι) (φ : (κ → R v) → ℂ)
    (h1 : IsLocallyConstant φ) (h2 : HasCompactSupport φ) (g : (κ → Πʳ i, [R i, A i]) → ℂ)
    (hg : ∀ x, g x = φ (fun i => x i v) *
      Set.indicator {z : κ → Πʳ i, [R i, A i] | ∀ i u, u ≠ v → z i u ∈ A u} 1 x) :
    IsLocallyConstant g ∧ HasCompactSupport g := by
  classical
  set S : Set (κ → Πʳ i, [R i, A i]) := {z | ∀ i u, u ≠ v → z i u ∈ A u} with hS
  have hSo : IsOpen S := by
    rw [hS, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i =>
      (RestrictedProduct.isOpen_forall_imp_mem ho (p := fun u => u ≠ v)).preimage
        (f := fun z : κ → Πʳ i, [R i, A i] => z i) (continuous_apply i)
  have hSc : IsClosed S := by
    simp only [hS, Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun u => isClosed_iInter fun _ =>
      (hc u).isClosed.preimage
        ((RestrictedProduct.continuous_eval u).comp (continuous_apply i))
  have hev : Continuous fun (x : κ → Πʳ i, [R i, A i]) (i : κ) => x i v :=
    continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)
  have hK : ∀ K : Set (R v), IsCompact K →
      IsCompact {y : Πʳ i, [R i, A i] | y v ∈ K ∧ ∀ u, u ≠ v → y u ∈ A u} := by
    intro K hK
    have hle : (cofinite : Filter ι) ≤ 𝓟 ({v}ᶜ : Set ι) := by simp
    have hQ : IsCompact (Set.univ.pi (Function.update A v K)) :=
      isCompact_univ_pi fun u => by
        by_cases h : u = v
        · subst h; simpa using hK
        · simpa [h] using hc u
    have hP := (RestrictedProduct.isEmbedding_coe_of_principal (R := R) (A := A)
      (S := ({v}ᶜ : Set ι))).isCompact_preimage_iff (K := Set.univ.pi (Function.update A v K))
      (by
        rw [RestrictedProduct.range_coe_principal]
        intro x hx u hu
        have h : u ≠ v := hu
        simpa [h] using hx u trivial) |>.mpr hQ
    convert hP.image (RestrictedProduct.continuous_inclusion hle) using 1
    ext y
    constructor
    · rintro ⟨hy1, hy2⟩
      refine ⟨⟨y.1, hy2⟩, fun u _ => ?_, rfl⟩
      by_cases h : u = v
      · subst h; rw [Function.update_self]; exact hy1
      · rw [Function.update_of_ne h]; exact hy2 u h
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, fun u hu => z.2 hu⟩
      have := hz v trivial
      rw [Function.update_self] at this
      exact this
  constructor
  · have hI : IsLocallyConstant (S.indicator (1 : (κ → Πʳ i, [R i, A i]) → ℂ)) :=
      (LocallyConstant.indicator (1 : LocallyConstant (κ → Πʳ i, [R i, A i]) ℂ)
        (U := S) ⟨hSc, hSo⟩).isLocallyConstant
    rw [funext hg]
    exact (h1.comp_continuous hev).mul hI
  · refine HasCompactSupport.intro (isCompact_univ_pi fun i : κ =>
      hK _ (h2.isCompact.image (continuous_apply i))) fun x hx => ?_
    rw [hg]
    by_cases hxS : x ∈ S
    · by_contra hne
      refine hx fun i _ => ⟨⟨fun j => x j v, ?_, rfl⟩, hxS i⟩
      exact subset_tsupport _ (left_ne_zero_of_mul hne)
    · rw [Set.indicator_of_notMem hxS, mul_zero]

private lemma UpperTheory.valuation_subring_compact {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    [Valued K Γ] [(Valued.v : Valuation K Γ).RankOne] [LocallyCompactSpace K] :
    IsCompact ((Valued.v : Valuation K Γ).valuationSubring : Set K) := by
  letI := Valued.toNontriviallyNormedField K Γ
  haveI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  exact isCompact_iff_compactSpace.mpr
    (Valued.integer.properSpace_iff_compactSpace_integer.mp this)

theorem UpperTheory.schwartz_function_generation :
    ∀ (F : Type) [Field F] [NumberField F],
        (∀ u : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), LocallyCompactSpace (u.adicCompletion F)) →
        ∀ (κ : Type) [Fintype κ] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
          (φ : (κ → v.adicCompletion F) → ℂ), IsLocallyConstant φ → HasCompactSupport φ →
          ∀ g : (κ → IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) → ℂ,
            (∀ x, g x = φ (fun i => x i v) *
              Set.indicator {z : κ → IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F |
                ∀ i u, u ≠ v → z i u ∈ u.adicCompletionIntegers F} 1 x) →
            IsLocallyConstant g ∧ HasCompactSupport g := by
  intro F _ _ hlc κ _ v φ h1 h2 g hg
  exact UpperTheory.factorizable_generation
    (R := fun u : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) =>
      u.adicCompletion F)
    (A := fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F)))
    (fun _ => Valued.isOpen_valuationSubring _)
    (fun u => haveI := hlc u; UpperTheory.valuation_subring_compact) v φ h1 h2 g hg
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SectionLift
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Yt7.Sp :
    (R : Type) → [CommRing R] → AlgebraicGeometry.Scheme :=
    fun (R : Type) [CommRing R] ↦ AlgebraicGeometry.Spec (CommRingCat.of R)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Yt7.spMap :
    {R R' : Type} →
      [inst : CommRing R] → [inst_1 : CommRing R'] → (R →+* R') → (UpperTheory.Reformulated.B.Yt7.Sp R' ⟶ UpperTheory.Reformulated.B.Yt7.Sp R) :=
    fun {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') ↦ AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)

open CategoryTheory AlgebraicGeometry in
private theorem UpperTheory.Reformulated.B.Yt7.ring_lift {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [IsIntegrallyClosed R] {A : Type} [CommRing A] (φ : R →+* A) (hφ : φ.Finite)
    (ψ : A →+* K) (h : ψ.comp φ = algebraMap R K) :
    ∃ σ : A →+* R, σ.comp φ = RingHom.id R ∧ (algebraMap R K).comp σ = ψ := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hmem : ∀ a : A, ψ a ∈ (algebraMap R K).range := by
    intro a
    have hi : (algebraMap R K).IsIntegralElem (ψ a) := by
      rw [← h]
      exact (hφ.to_isIntegral a).map ψ
    exact IsIntegrallyClosed.isIntegral_iff.mp hi
  let e : R ≃+* (algebraMap R K).range :=
    RingEquiv.ofBijective (algebraMap R K).rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), (algebraMap R K).rangeRestrict_surjective⟩
  have key : ∀ a : A, algebraMap R K (e.symm ⟨ψ a, hmem a⟩) = ψ a := fun a =>
    congrArg Subtype.val (e.apply_symm_apply ⟨ψ a, hmem a⟩)
  refine ⟨e.symm.toRingHom.comp (ψ.codRestrict _ hmem), ?_, ?_⟩
  · ext r
    apply hinj
    exact (key (φ r)).trans (RingHom.congr_fun h r)
  · ext a
    exact key a

open CategoryTheory AlgebraicGeometry in
private theorem UpperTheory.Reformulated.B.Yt7.section_lift {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [IsIntegrallyClosed R] {P : Scheme} (g : P ⟶ Spec (CommRingCat.of R)) [IsFinite g]
    (s : Spec (CommRingCat.of K) ⟶ P)
    (h : s ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃ t : Spec (CommRingCat.of R) ⟶ P,
      t ≫ g = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ t = s := by
  have : IsAffine P := isAffine_of_isAffineHom g
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (P.isoSpec.inv ≫ g)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (s ≫ P.isoSpec.hom)
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  have hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap R K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, ← h]
    simp
  obtain ⟨σ, h1, h2⟩ := UpperTheory.Reformulated.B.Yt7.ring_lift (K := K) φ.hom hfin ψ.hom
    (congrArg CommRingCat.Hom.hom hc)
  have h1' : φ ≫ CommRingCat.ofHom σ = 𝟙 _ := CommRingCat.hom_ext h1
  have h2' : CommRingCat.ofHom σ ≫ CommRingCat.ofHom (algebraMap R K) = ψ := CommRingCat.hom_ext h2
  refine ⟨Spec.map (CommRingCat.ofHom σ) ≫ P.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp, h1', Spec.map_id]
  · rw [← Category.assoc, ← Spec.map_comp, h2', hψ]
    simp

theorem UpperTheory.Reformulated.B.Yt7.lift_finite :
    ∀ {R K : Type} [inst : CommRing R] [IsDomain R] [inst_2 : Field K] [inst_3 : Algebra R K] [IsFractionRing R K]
      [IsIntegrallyClosed R] {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) [AlgebraicGeometry.IsFinite f]
      (y : UpperTheory.Reformulated.B.Yt7.Sp R ⟶ S) (w : UpperTheory.Reformulated.B.Yt7.Sp K ⟶ X),
      CategoryTheory.CategoryStruct.comp w f =
          CategoryTheory.CategoryStruct.comp (UpperTheory.Reformulated.B.Yt7.spMap (Algebra.algebraMap R K)) y →
        ∃ (v : UpperTheory.Reformulated.B.Yt7.Sp R ⟶ X),
          CategoryTheory.CategoryStruct.comp v f = y ∧
            CategoryTheory.CategoryStruct.comp (UpperTheory.Reformulated.B.Yt7.spMap (Algebra.algebraMap R K)) v = w := by
  intro R K _ _ _ _ _ _ X S f _ y w h
  obtain ⟨t, ht1, ht2⟩ := UpperTheory.Reformulated.B.Yt7.section_lift (K := K) (CategoryTheory.Limits.pullback.snd f y)
    (CategoryTheory.Limits.pullback.lift w _ h) (CategoryTheory.Limits.pullback.lift_snd _ _ _)
  refine ⟨CategoryTheory.CategoryStruct.comp t (CategoryTheory.Limits.pullback.fst f y), ?_, ?_⟩
  · rw [CategoryTheory.Category.assoc, CategoryTheory.Limits.pullback.condition,
      ← CategoryTheory.Category.assoc, ht1, CategoryTheory.Category.id_comp]
  · rw [← CategoryTheory.Category.assoc, ht2, CategoryTheory.Limits.pullback.lift_fst]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SemilinearLatticeMem
section
theorem UpperTheory.semilinear_lattice_mem :
    ∀ (R K C V W : Type) [CommRing R] [Field K] [Field C] [Algebra R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] [AddCommGroup W] [Module C W] (e : K →+* C) (U : Submodule K V) (Φ : U →ₛₗ[e] W) (A : Set C) (L : AddSubgroup W) (G : Set V), (∀ a ∈ A, ∀ y ∈ L, a • y ∈ L) → (∀ r : R, e (algebraMap R K r) ∈ A) → (∀ g ∈ G, ∃ h : g ∈ U, Φ ⟨g, h⟩ ∈ L) → ∀ (s : R), algebraMap R K s ≠ 0 → e (algebraMap R K s)⁻¹ ∈ A → ∀ v : U, s • (v : V) ∈ Submodule.span R G → Φ v ∈ L := by
  intro R K C V W _ _ _ _ _ _ _ _ _ _ e U Φ A L G hA hR hG s hs hsA v hv
  have key : ∀ x ∈ Submodule.span R G, ∃ h : x ∈ U, Φ ⟨x, h⟩ ∈ L := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hG x hx
    | zero =>
      refine ⟨U.zero_mem, ?_⟩
      have h0 : (⟨0, U.zero_mem⟩ : U) = 0 := rfl
      rw [h0, map_zero]
      exact L.zero_mem
    | add x y _ _ hx hy =>
      obtain ⟨hxU, hx⟩ := hx
      obtain ⟨hyU, hy⟩ := hy
      refine ⟨U.add_mem hxU hyU, ?_⟩
      have h0 : (⟨x + y, U.add_mem hxU hyU⟩ : U) = ⟨x, hxU⟩ + ⟨y, hyU⟩ := rfl
      rw [h0, map_add]
      exact L.add_mem hx hy
    | smul r x _ hx =>
      obtain ⟨hxU, hx⟩ := hx
      have hm : r • x ∈ U := by
        rw [← algebraMap_smul K r x]
        exact U.smul_mem _ hxU
      refine ⟨hm, ?_⟩
      have h0 : (⟨r • x, hm⟩ : U) = algebraMap R K r • (⟨x, hxU⟩ : U) :=
        Subtype.ext (algebraMap_smul K r x).symm
      rw [h0, LinearMap.map_smulₛₗ]
      exact hA _ (hR r) _ hx
  obtain ⟨hU, hL⟩ := key _ hv
  have h1 : v = (algebraMap R K s)⁻¹ • (⟨s • (v : V), hU⟩ : U) := by
    apply Subtype.ext
    change (v : V) = (algebraMap R K s)⁻¹ • (s • (v : V))
    rw [← algebraMap_smul K s (v : V), inv_smul_smul₀ hs]
  rw [h1, LinearMap.map_smulₛₗ]
  exact hA _ hsA _ hL
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SeqEx
section
theorem UpperTheory.Reformulated.B.Qj7.seq_ex :
    ∀ (S : ℕ → Type),
    (∀ (n : ℕ), Finite (S n)) →
      (∀ (n : ℕ), Nonempty (S n)) →
        ∀ (t : (n : ℕ) → S (n + (1 : ℕ)) → S n), ∃ (u : (n : ℕ) → S n), ∀ (n : ℕ), t n (u (n + (1 : ℕ))) = u n := by
  intro S hfin hne t
  classical
  letI : ∀ n, TopologicalSpace (S n) := fun _ => ⊥
  haveI : ∀ n, DiscreteTopology (S n) := fun _ => ⟨rfl⟩
  let C : ℕ → Set ((n : ℕ) → S n) := fun k => {u | ∀ n < k, t n (u (n + 1)) = u n}
  have hclosed : ∀ k, IsClosed (C k) := by
    intro k
    have hC : C k = ⋂ n, ⋂ (_ : n < k), {u : (n : ℕ) → S n | t n (u (n + 1)) = u n} := by
      ext u
      simp [C]
    rw [hC]
    refine isClosed_iInter fun n => isClosed_iInter fun _ => ?_
    exact isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply (n + 1)))
      (continuous_apply n)
  have hstep : ∀ (k : ℕ) (x : S k), ∃ u ∈ C k, u k = x := by
    intro k
    induction k with
    | zero =>
      intro x
      refine ⟨Function.update (fun n => Classical.choice (hne n)) 0 x, ?_, by simp⟩
      intro n hn
      exact absurd hn (Nat.not_lt_zero n)
    | succ k ih =>
      intro x
      obtain ⟨u, hu, hk⟩ := ih (t k x)
      refine ⟨Function.update u (k + 1) x, ?_, by simp⟩
      intro n hn
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h | h
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hu n h
      · subst h
        rw [Function.update_self, Function.update_of_ne (by omega), hk]
  have hnon : ∀ k, (C k).Nonempty := by
    intro k
    obtain ⟨u, hu, _⟩ := hstep k (Classical.choice (hne k))
    exact ⟨u, hu⟩
  have hmono : ∀ k, C (k + 1) ⊆ C k := fun k u hu n hn => hu n (Nat.lt_succ_of_lt hn)
  obtain ⟨u, hu⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hmono hnon
    (hclosed 0).isCompact hclosed
  exact ⟨u, fun n => Set.mem_iInter.mp hu (n + 1) n (Nat.lt_succ_self n)⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StarEqOfSq
section
theorem UpperTheory.Reformulated.B.Ra8.star_eq_of_sq :
    ∀ {z : ℂ} {r : ℝ},
    (0 : ℝ) ≤ r → z * z = (↑r : ℂ) → Star.star z = z := by
  intro z r hr h
  have hre : z.re * z.re - z.im * z.im = r := by
    simpa using congrArg Complex.re h
  have him : z.re * z.im + z.im * z.re = 0 := by
    simpa using congrArg Complex.im h
  have h0 : z.im = 0 := by
    by_contra hne
    have h1 : z.re * z.im = 0 := by linarith [mul_comm z.re z.im]
    have h2 : z.re = 0 := (mul_eq_zero.mp h1).resolve_right hne
    have h3 : 0 < z.im * z.im := mul_self_pos.mpr hne
    rw [h2] at hre
    linarith
  exact Complex.conj_eq_iff_im.mpr h0
end

