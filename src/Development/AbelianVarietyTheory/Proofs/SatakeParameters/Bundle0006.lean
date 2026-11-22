import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsComplOrthogonalOfNoCommonIrreducibleTypes
section
open Module

namespace GlobalTheory.IsotypicOrth

variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}
  {σ : K →* K}

lemma pair_left (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    (k : K) (x y : V) : B (ρ k x) y = B x (ρ (σ k⁻¹) y) := by
  rw [← hB k x (ρ (σ k⁻¹) y), map_inv, Representation.self_inv_apply]

lemma left_ker_zero (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    {S₁ S : Subrepresentation ρ} (h₁ : IsAtom S₁)
    (hn : ∃ x ∈ S₁.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0) :
    ∀ x ∈ S₁.toSubmodule, (∀ y ∈ S.toSubmodule, B x y = 0) → x = 0 := by
  let T : Subrepresentation ρ :=
    ⟨S₁.toSubmodule ⊓ ⨅ y ∈ S.toSubmodule, LinearMap.ker (B.flip y), by
      intro k x hx
      simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
        LinearMap.flip_apply] at hx ⊢
      refine ⟨S₁.apply_mem_toSubmodule k hx.1, fun y hy => ?_⟩
      rw [pair_left B hB]
      exact hx.2 _ (S.apply_mem_toSubmodule _ hy)⟩
  have hle : T ≤ S₁ := fun x hx => (Submodule.mem_inf.mp hx).1
  have hmem : ∀ x ∈ S₁.toSubmodule, (∀ y ∈ S.toSubmodule, B x y = 0) → x ∈ T.toSubmodule := by
    intro x hx h0
    simp only [T, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]
    exact ⟨hx, h0⟩
  rcases h₁.le_iff.mp hle with h | h
  · intro x hx h0
    have hT : T.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h
    have := hmem x hx h0
    rw [hT] at this
    exact (Submodule.mem_bot ℂ).mp this
  · exfalso
    obtain ⟨x, hx, y, hy, hne⟩ := hn
    have hT : T.toSubmodule = S₁.toSubmodule := congrArg Subrepresentation.toSubmodule h
    rw [← hT] at hx
    simp only [T, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.flip_apply] at hx
    exact hne (hx.2 y hy)

lemma right_ker_zero (hσ : Function.Surjective σ) (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    {S₁ S : Subrepresentation ρ} (h : IsAtom S)
    (hn : ∃ x ∈ S₁.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0) :
    ∀ y ∈ S.toSubmodule, (∀ x ∈ S₁.toSubmodule, B x y = 0) → y = 0 := by
  let T : Subrepresentation ρ :=
    ⟨S.toSubmodule ⊓ ⨅ x ∈ S₁.toSubmodule, LinearMap.ker (B x), by
      intro k' y hy
      obtain ⟨k, rfl⟩ := hσ k'
      simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢
      refine ⟨S.apply_mem_toSubmodule _ hy.1, fun x hx => ?_⟩
      have e := hB k (ρ k⁻¹ x) y
      rw [Representation.self_inv_apply] at e
      rw [e]
      exact hy.2 _ (S₁.apply_mem_toSubmodule _ hx)⟩
  have hle : T ≤ S := fun x hx => (Submodule.mem_inf.mp hx).1
  have hmem : ∀ y ∈ S.toSubmodule, (∀ x ∈ S₁.toSubmodule, B x y = 0) → y ∈ T.toSubmodule := by
    intro y hy h0
    simp only [T, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
    exact ⟨hy, h0⟩
  rcases h.le_iff.mp hle with h' | h'
  · intro y hy h0
    have hT : T.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h'
    have := hmem y hy h0
    rw [hT] at this
    exact (Submodule.mem_bot ℂ).mp this
  · exfalso
    obtain ⟨x, hx, y, hy, hne⟩ := hn
    have hT : T.toSubmodule = S.toSubmodule := congrArg Subrepresentation.toSubmodule h'
    rw [← hT] at hy
    simp only [T, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hy
    exact hne (hy.2 x hx)

lemma restr_injective (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    {S₁ S : Subrepresentation ρ} (h₁ : IsAtom S₁)
    (hn : ∃ x ∈ S₁.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0) :
    Function.Injective (B.domRestrict₁₂ S₁.toSubmodule S.toSubmodule) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  apply Subtype.ext
  refine left_ker_zero B hB h₁ hn a a.2 fun y hy => ?_
  have := LinearMap.congr_fun ha ⟨y, hy⟩
  simpa [LinearMap.domRestrict₁₂_apply] using this

lemma restr_flip_injective (hσ : Function.Surjective σ) (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    {S₁ S : Subrepresentation ρ} (h : IsAtom S)
    (hn : ∃ x ∈ S₁.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0) :
    Function.Injective (B.domRestrict₁₂ S₁.toSubmodule S.toSubmodule).flip := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  apply Subtype.ext
  refine right_ker_zero hσ B hB h hn a a.2 fun x hx => ?_
  have := LinearMap.congr_fun ha ⟨x, hx⟩
  simpa [LinearMap.domRestrict₁₂_apply] using this

theorem nonempty_equiv_of_pair (hσ : Function.Surjective σ)
    (hfin : ∀ S : Subrepresentation ρ, IsAtom S → FiniteDimensional ℂ S.toSubmodule)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (hB : ∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ)
    {S₁ S₂ S : Subrepresentation ρ} (h₁ : IsAtom S₁) (h₂ : IsAtom S₂) (h : IsAtom S)
    (hn₁ : ∃ x ∈ S₁.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0)
    (hn₂ : ∃ x ∈ S₂.toSubmodule, ∃ y ∈ S.toSubmodule, B x y ≠ 0) :
    Nonempty (S₁.toRepresentation.Equiv S₂.toRepresentation) := by
  haveI := hfin S₁ h₁
  haveI := hfin S₂ h₂
  haveI := hfin S h
  set f₁ := B.domRestrict₁₂ S₁.toSubmodule S.toSubmodule with hf₁def
  set f₂ := B.domRestrict₁₂ S₂.toSubmodule S.toSubmodule with hf₂def
  have i₁ : Function.Injective f₁ := restr_injective B hB h₁ hn₁
  have i₂ : Function.Injective f₂ := restr_injective B hB h₂ hn₂
  have j₁ : Function.Injective f₁.flip := restr_flip_injective hσ B hB h hn₁
  have j₂ : Function.Injective f₂.flip := restr_flip_injective hσ B hB h hn₂
  have d₁ : finrank ℂ S₁.toSubmodule = finrank ℂ (Dual ℂ S.toSubmodule) := by
    rw [Subspace.dual_finrank_eq]
    refine le_antisymm ?_ ?_
    · exact (LinearMap.finrank_le_finrank_of_injective i₁).trans_eq Subspace.dual_finrank_eq
    · exact (LinearMap.finrank_le_finrank_of_injective j₁).trans_eq Subspace.dual_finrank_eq
  have d₂ : finrank ℂ S₂.toSubmodule = finrank ℂ (Dual ℂ S.toSubmodule) := by
    rw [Subspace.dual_finrank_eq]
    refine le_antisymm ?_ ?_
    · exact (LinearMap.finrank_le_finrank_of_injective i₂).trans_eq Subspace.dual_finrank_eq
    · exact (LinearMap.finrank_le_finrank_of_injective j₂).trans_eq Subspace.dual_finrank_eq
  let e₁ := LinearEquiv.ofBijective f₁ ⟨i₁, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank d₁).mp i₁⟩
  let e₂ := LinearEquiv.ofBijective f₂ ⟨i₂, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank d₂).mp i₂⟩
  let e := e₁.trans e₂.symm
  have hfe : ∀ x, f₂ (e x) = f₁ x := by
    intro x
    have h1 : ∀ z, e₁ z = f₁ z := fun z => LinearEquiv.ofBijective_apply _ _
    have h2 : ∀ z, e₂ z = f₂ z := fun z => LinearEquiv.ofBijective_apply _ _
    rw [← h1, ← h2]
    simp [e]
  have hcomm : ∀ (x : S₁.toSubmodule) (y : S.toSubmodule), B (e x : V) y = B x y := by
    intro x y
    have := LinearMap.congr_fun (hfe x) y
    simpa [f₁, f₂, LinearMap.domRestrict₁₂_apply] using this
  refine ⟨Representation.Equiv.mk e fun k => ?_⟩
  apply LinearMap.ext
  intro x
  apply i₂
  apply LinearMap.ext
  intro y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hf₂def, LinearMap.domRestrict₁₂_apply]
  rw [hcomm]
  change B (ρ k x) y = B (ρ k (e x)) y
  rw [pair_left B hB, pair_left B hB]
  exact (hcomm x ⟨_, S.apply_mem_toSubmodule _ y.2⟩).symm

lemma exists_atom_pair
    (hsum : ∀ X : Subrepresentation ρ,
      X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule)
    (B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ) (Y : Subrepresentation ρ) (ψ : V)
    (h : ∃ y ∈ Y.toSubmodule, B y ψ ≠ 0) :
    ∃ S₁ : Subrepresentation ρ, IsAtom S₁ ∧ S₁ ≤ Y ∧ ∃ x ∈ S₁.toSubmodule, B x ψ ≠ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨y, hy, hne⟩ := h
  apply hne
  have hle : Y.toSubmodule ≤ LinearMap.ker (B.flip ψ) := by
    rw [hsum Y]
    exact iSup₂_le fun S hS x hx => by simpa using hc S hS.1 hS.2 x hx
  simpa using hle hy

end GlobalTheory.IsotypicOrth

namespace GlobalTheory.IsotypicOrth

theorem orth_isCompl : ∀ (K V : Type) [Group K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V) (σ : K →* K), Function.Surjective σ → (∀ S : Subrepresentation ρ, IsAtom S → FiniteDimensional ℂ S.toSubmodule) → (∀ X : Subrepresentation ρ, X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule) → ∀ B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ) → ∀ X Y : Subrepresentation ρ, IsCompl X.toSubmodule Y.toSubmodule → (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → IsAtom S₂ → S₁ ≤ Y → S₂ ≤ X → IsEmpty (S₁.toRepresentation.Equiv S₂.toRepresentation)) → IsCompl (⨅ y ∈ Y.toSubmodule, LinearMap.ker (B y)) (⨅ x ∈ X.toSubmodule, LinearMap.ker (B x)) := by
  intro K V _ _ _ ρ σ hσ hfin hsum B _hl hr hB X Y hXY hiso
  constructor
  · rw [Submodule.disjoint_def]
    intro ψ h1 h2
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h1 h2
    apply hr
    intro φ
    have : φ ∈ X.toSubmodule ⊔ Y.toSubmodule := by rw [hXY.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp this
    rw [map_add, LinearMap.add_apply, h1 b hb, h2 a ha, add_zero]
  · rw [codisjoint_iff, eq_top_iff]
    have htop := hsum ⊤
    change (⊤ : Submodule ℂ V) = _ at htop
    rw [htop]
    refine iSup₂_le fun S hS => ?_
    by_cases hY : S.toSubmodule ≤ ⨅ y ∈ Y.toSubmodule, LinearMap.ker (B y)
    · exact le_sup_of_le_left hY
    by_cases hX : S.toSubmodule ≤ ⨅ x ∈ X.toSubmodule, LinearMap.ker (B x)
    · exact le_sup_of_le_right hX
    exfalso
    obtain ⟨ψ₁, hψ₁, hψ₁'⟩ := SetLike.not_le_iff_exists.mp hY
    obtain ⟨ψ₂, hψ₂, hψ₂'⟩ := SetLike.not_le_iff_exists.mp hX
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, not_forall] at hψ₁' hψ₂'
    obtain ⟨y, hy, hy'⟩ := hψ₁'
    obtain ⟨x, hx, hx'⟩ := hψ₂'
    obtain ⟨S₁, a₁, l₁, x₁, hx₁, n₁⟩ := exists_atom_pair hsum B Y ψ₁ ⟨y, hy, hy'⟩
    obtain ⟨S₂, a₂, l₂, x₂, hx₂, n₂⟩ := exists_atom_pair hsum B X ψ₂ ⟨x, hx, hx'⟩
    have e := nonempty_equiv_of_pair hσ hfin B hB a₁ a₂ hS.1 ⟨x₁, hx₁, ψ₁, hψ₁, n₁⟩
      ⟨x₂, hx₂, ψ₂, hψ₂, n₂⟩
    exact (hiso S₁ S₂ a₁ a₂ l₁ l₂).false e.some

end GlobalTheory.IsotypicOrth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsReducedQuotientOfArtinianOfMaximalLe
section
namespace GlobalTheory

open scoped BigOperators

theorem quotient_maximal_le_sq {A : Type} [CommRing A] (I : Ideal A)
    (h : ∀ m : Ideal A, m.IsMaximal → I ≤ m → m ≤ I ⊔ m ^ 2)
    (M : Ideal (A ⧸ I)) (hM : M.IsMaximal) : M ≤ M ^ 2 := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  set m := M.comap (Ideal.Quotient.mk I) with hm
  have hmax : m.IsMaximal := Ideal.comap_isMaximal_of_surjective _ hsurj
  have hIm : I ≤ m := by
    intro x hx
    simp [hm, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have key := Ideal.map_mono (f := Ideal.Quotient.mk I) (h m hmax hIm)
  rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_quotient_self, bot_sup_eq,
    hm, Ideal.map_comap_of_surjective _ hsurj] at key
  exact key

theorem pow_eq_self_of_le_sq {R : Type} [CommRing R] (M : Ideal R) (h : M ≤ M ^ 2) :
    ∀ k : ℕ, M ^ (k + 1) = M := by
  have h2 : M * M = M := by
    rw [← sq]; exact le_antisymm (Ideal.pow_le_self two_ne_zero) h
  intro k
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, h2]

theorem isReduced_quotient_of_artinian_of_maximal_le (A : Type) [CommRing A] (I : Ideal A)
    (hart : IsArtinianRing (A ⧸ I))
    (h : ∀ m : Ideal A, m.IsMaximal → I ≤ m → m ≤ I ⊔ m ^ 2) : IsReduced (A ⧸ I) := by
  classical
  set R := A ⧸ I
  haveI : Finite (MaximalSpectrum R) := inferInstance
  haveI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  set J : Ideal R := ∏ M : MaximalSpectrum R, M.asIdeal with hJ
  have hJinf : J = ⨅ M ∈ (Finset.univ : Finset (MaximalSpectrum R)), M.asIdeal := by
    rw [hJ]
    apply Ideal.prod_eq_iInf_of_pairwise_isCoprime
    intro a _ b _ hab
    exact Ideal.isCoprime_of_isMaximal (fun e => hab (MaximalSpectrum.ext e))
  have hpow : ∀ k : ℕ, J ^ (k + 1) = J := by
    intro k
    rw [hJ, ← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun M _ => ?_)
    exact pow_eq_self_of_le_sq _ (quotient_maximal_le_sq I h M.asIdeal M.isMaximal) k
  have hJjac : J ≤ Ideal.jacobson ⊥ := by
    rw [hJinf]
    intro x hx
    rw [Ideal.mem_jacobson_bot]
    intro y
    by_contra hu
    obtain ⟨M, hMmax, hM⟩ := Ideal.exists_le_maximal (Ideal.span {x * y + 1})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    have hxM : x ∈ M := by
      have := (Submodule.mem_iInf _).mp hx ⟨M, hMmax⟩
      simpa using this
    have h1 : x * y + 1 ∈ M := hM (Ideal.subset_span rfl)
    have : (1 : R) ∈ M := by
      have := M.sub_mem h1 (M.mul_mem_right y hxM)
      simpa using this
    exact hMmax.ne_top ((Ideal.eq_top_iff_one _).mpr this)
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  have hJbot : J = ⊥ := by
    rw [← hpow n]
    refine le_bot_iff.mp ?_
    calc J ^ (n + 1) ≤ (Ideal.jacobson ⊥) ^ (n + 1) := Ideal.pow_right_mono hJjac _
      _ ≤ (Ideal.jacobson ⊥) ^ n := Ideal.pow_le_pow_right (Nat.le_succ n)
      _ = ⊥ := hn
  refine ⟨fun x hx => ?_⟩
  have hxJ : x ∈ J := by
    rw [hJinf]
    refine (Submodule.mem_iInf _).mpr (fun M => (Submodule.mem_iInf _).mpr (fun _ => ?_))
    exact (hx.map (Ideal.Quotient.mk M.asIdeal)).eq_zero |> Ideal.Quotient.eq_zero_iff_mem.mp
  rw [hJbot] at hxJ
  exact (Submodule.mem_bot R).mp hxJ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthLeOfForallFgSubmoduleLengthLe
section
open Pointwise

namespace GlobalTheory

theorem length_le_of_forall_fg_length_le (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (b : ℕ∞)
    (h : ∀ N : Submodule O M, N.FG → Module.length O N ≤ b) : Module.length O M ≤ b := by
  rw [Module.length_eq_height]
  refine Order.height_le_iff'.2 fun p _ => ?_
  have hx : ∀ i : Fin p.length, ∃ x ∈ p i.succ, x ∉ p i.castSucc :=
    fun i => SetLike.exists_of_lt (p.step i)
  choose x hx1 hx2 using hx
  set N : Submodule O M := Submodule.span O (Set.range x) with hN
  have hNfg : N.FG := Submodule.fg_span (Set.finite_range x)
  have hxN : ∀ i, x i ∈ N := fun i => Submodule.subset_span ⟨i, rfl⟩
  let q : LTSeries (Submodule O N) :=
    { length := p.length
      toFun := fun i => (p i).comap N.subtype
      step := fun i => by
        refine lt_of_le_of_ne (Submodule.comap_mono (p.step i).le) ?_
        intro heq
        have h1 : (⟨x i, hxN i⟩ : N) ∈ (p i.succ).comap N.subtype := hx1 i
        rw [← heq] at h1
        exact hx2 i h1 }
  have h2 : (q.length : ℕ∞) ≤ Order.height (⊤ : Submodule O N) :=
    Order.length_le_height le_top
  calc (p.length : ℕ∞) = q.length := rfl
    _ ≤ Order.height (⊤ : Submodule O N) := h2
    _ = Module.length O N := (Module.length_eq_height (R := O) (M := N)).symm
    _ ≤ b := h N hNfg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientScalarMul
section
open Pointwise

namespace GlobalTheory

theorem length_quot_smul_range_finite_free : ∀ (O M : Type) [CommRing O] [Nontrivial O] [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M] (a : O), Module.length O (M ⧸ LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))) = (Module.finrank O M : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  intro O M _ _ _ _ _ _ a
  classical
  set d := Module.finrank O M
  let e : M ≃ₗ[O] (Fin d → O) := (Module.finBasis O M).equivFun
  have hmap : (LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))).map (e : M →ₗ[O] (Fin d → O))
      = Submodule.pi Set.univ (fun _ : Fin d => (Ideal.span {a} : Submodule O O)) := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, true_implies,
      LinearMap.smul_apply, LinearMap.id_apply]
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩ i
      rw [LinearEquiv.coe_coe, map_smul, Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)
    · intro h
      choose c hc using fun i => Ideal.mem_span_singleton'.1 (h i)
      refine ⟨a • e.symm c, ⟨e.symm c, rfl⟩, ?_⟩
      rw [LinearEquiv.coe_coe, map_smul, LinearEquiv.apply_symm_apply]
      funext i
      simp [← hc i, mul_comm]
  let f := (Submodule.Quotient.equiv _ _ e hmap).trans
    (Submodule.quotientPi (fun _ : Fin d => (Ideal.span {a} : Submodule O O)))
  rw [f.length_eq, Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSmulSupLeIntermediate
section
open Pointwise

namespace GlobalTheory

theorem length_quotient_tower_of_le {R : Type} [CommRing R] {X : Type} [AddCommGroup X] [Module R X]
    (Y W : Submodule R X) (hYW : Y ≤ W) :
    Module.length R (X ⧸ Y) =
      Module.length R (W ⧸ Y.comap W.subtype) + Module.length R (X ⧸ W) := by
  have hf : Function.Injective ((Y.comap W.subtype).mapQ Y W.subtype le_rfl) := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ]
    simp
  refine Module.length_eq_add_of_exact ((Y.comap W.subtype).mapQ Y W.subtype le_rfl)
    (Submodule.factor hYW) hf (Submodule.factor_surjective hYW) ?_
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H x =>
    constructor
    · intro h
      have hx : x ∈ W := by
        simpa [Submodule.Quotient.mk_eq_zero] using h
      exact ⟨Submodule.Quotient.mk ⟨x, hx⟩, rfl⟩
    · rintro ⟨w, hw⟩
      rw [← hw]
      induction w using Submodule.Quotient.induction_on with
      | H z => simp [Submodule.Quotient.mk_eq_zero]

theorem length_quotient_smul_sup_le : ∀ (O A : Type) [CommRing O] [AddCommGroup A] [Module O A]
    (Z B B' : Submodule O A) (a : O), B ≤ B' →
    Module.length O (↥Z ⧸ (Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B).comap Z.subtype) ≤
      Module.length O ((↥Z ⧸ B'.comap Z.subtype) ⧸ LinearMap.range (a • (LinearMap.id :
        (↥Z ⧸ B'.comap Z.subtype) →ₗ[O] (↥Z ⧸ B'.comap Z.subtype)))) +
      Module.length O (↥(Z ⊓ B') ⧸ B.comap (Z ⊓ B').subtype) := by
  intro O A _ _ _ Z B B' a hBB'
  set N : Submodule O Z := (Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B).comap Z.subtype with hN
  set C : Submodule O Z := B'.comap Z.subtype with hC
  set K : Submodule O Z := N ⊔ C with hK
  rw [length_quotient_tower_of_le N K le_sup_left, add_comm]
  refine add_le_add ?_ ?_
  ·
    let f : (↥Z ⧸ C) →ₗ[O] (↥Z ⧸ K) := Submodule.factor (le_sup_right : C ≤ K)
    have hf : LinearMap.range (a • (LinearMap.id : (↥Z ⧸ C) →ₗ[O] (↥Z ⧸ C))) ≤ LinearMap.ker f := by
      rintro y ⟨q, rfl⟩
      induction q using Submodule.Quotient.induction_on with
      | H z =>
        rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, map_smul]
        change a • (Submodule.Quotient.mk z : ↥Z ⧸ K) = 0
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        refine Submodule.mem_sup_left ?_
        show ((a • z : Z) : A) ∈ Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B
        exact Submodule.mem_sup_left ⟨z, z.2, by simp⟩
    refine Module.length_le_of_surjective (Submodule.liftQ _ f hf) ?_
    intro w
    induction w using Submodule.Quotient.induction_on with
    | H z =>
      exact ⟨Submodule.Quotient.mk (Submodule.Quotient.mk z), rfl⟩
  ·
    let ι : ↥(Z ⊓ B') →ₗ[O] K :=
      LinearMap.codRestrict K (LinearMap.codRestrict Z (Z ⊓ B').subtype (fun x => x.2.1))
        (fun x => Submodule.mem_sup_right (show _ ∈ C from x.2.2))
    let φ : ↥(Z ⊓ B') →ₗ[O] (↥K ⧸ N.comap K.subtype) := (N.comap K.subtype).mkQ ∘ₗ ι
    have hφ : B.comap (Z ⊓ B').subtype ≤ LinearMap.ker φ := by
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      show ((x : A)) ∈ Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B
      exact Submodule.mem_sup_right hx
    refine Module.length_le_of_surjective (Submodule.liftQ _ φ hφ) ?_
    intro w
    induction w using Submodule.Quotient.induction_on with
    | H k =>
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp k.2
      refine ⟨Submodule.Quotient.mk ⟨(z : A), z.2, hz⟩, ?_⟩
      rw [Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.eq]
      have : ((ι ⟨(z : A), z.2, hz⟩ - k : K) : Z) = -y := by
        ext
        simp only [ι, ← hyz, Submodule.coe_sub, Submodule.coe_neg, Submodule.coe_add]
        change (z : A) - ((y : A) + (z : A)) = -(y : A)
        abel
      show ((ι ⟨(z : A), z.2, hz⟩ - k : K) : Z) ∈ N
      rw [this]
      exact N.neg_mem hy

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSpanPowLeMulLength
section
open Pointwise

namespace GlobalTheory

theorem length_quotient_span_pow_le (O : Type) [CommRing O] (p : O) (n : ℕ) :
    Module.length O (O ⧸ Ideal.span {p ^ n}) ≤ (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) := by
  induction n with
  | zero =>
    rw [pow_zero, Ideal.span_singleton_one]
    haveI : Subsingleton (O ⧸ (⊤ : Ideal O)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    rw [Module.length_eq_zero]
    exact bot_le
  | succ n ih =>
    set S : Submodule O O := Ideal.span {p ^ (n + 1)} with hS
    set T : Submodule O O := Ideal.span {p ^ n} with hT
    have hST : S ≤ T := Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow p n.le_succ)
    let v : O ⧸ S := S.mkQ (p ^ n)
    have hker : (Ideal.span {p} : Submodule O O) ≤ LinearMap.ker (LinearMap.toSpanSingleton O (O ⧸ S) v) := by
      intro x hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      simp only [v, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul]
      rw [Submodule.Quotient.mk_eq_zero, hS, Ideal.mem_span_singleton']
      exact ⟨c, by ring⟩
    let ψ : (O ⧸ (Ideal.span {p} : Submodule O O)) →ₗ[O] O ⧸ S :=
      (Ideal.span {p} : Submodule O O).liftQ (LinearMap.toSpanSingleton O (O ⧸ S) v) hker
    let N : Submodule O (O ⧸ S) := LinearMap.range ψ
    have hN : N = T.map S.mkQ := by
      simp only [N, ψ, Submodule.range_liftQ, hT, Ideal.span, Submodule.map_span, Set.image_singleton]
      rw [← LinearMap.span_singleton_eq_range]
    have h1 := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N)
    have hle : Module.length O N ≤ Module.length O (O ⧸ Ideal.span {p}) :=
      Module.length_le_of_surjective ψ.rangeRestrict ψ.surjective_rangeRestrict
    have heq : Module.length O ((O ⧸ S) ⧸ N) = Module.length O (O ⧸ Ideal.span {p ^ n}) := by
      rw [hN]
      exact (Submodule.quotientQuotientEquivQuotient S T hST).length_eq
    change Module.length O (O ⧸ S) ≤ _
    rw [h1, heq]
    calc Module.length O N + Module.length O (O ⧸ Ideal.span {p ^ n})
        ≤ Module.length O (O ⧸ Ideal.span {p}) + (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) :=
          add_le_add hle ih
      _ = ((n + 1 : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) := by
          push_cast; ring

theorem main : ∀ (O : Type) [CommRing O] (p : O) (n : ℕ),
    Module.length O (O ⧸ Ideal.span {p ^ n}) ≤ (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) :=
  fun O _ p n => length_quotient_span_pow_le O p n

end GlobalTheory
end

