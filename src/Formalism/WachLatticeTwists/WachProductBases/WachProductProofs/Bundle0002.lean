import Formalism.WachLatticeTwists.WachProductBases.Statement
import Formalism.CoboundaryTransfers.GammaStableTransfers.Bundle0001
import Formalism.CoboundaryTransfers.GammaStableTransfers.Bundle0002
import Formalism.WachLatticeTwists.WachProductBases.WachProductProofs.Bundle0001

-- bundled from Formalism.WachLatticeTwists.WachProductBases.WachProductProofs.AffineLineLocalAcyclicityOfStrictHenselianPoints
section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N1

open Formalism.CoboundaryTransfers Finset

theorem kernel_intersection_holds : ComapLeOfSaturated := by
  intro A _ D₀ D₁ _ _ _ _ f N₀ N₁ l hrat hsat x hx
  obtain ⟨k, hk⟩ := hrat x hx
  induction k with
  | zero => simpa using hk
  | succ k ih =>
    apply ih
    apply hsat
    rwa [smul_smul, ← pow_succ']

theorem cokernel_killed_holds : CokernelKilledByPower := by
  intro A _ D₁ D₂ _ _ _ _ f N₁ N₂ π l a hsurj hfN hl hdens hsat hfg
  classical
  have hsat' : ∀ (b : ℕ) (d : D₂), (∃ k : ℕ, π ^ k • (l ^ b • d) ∈ N₂) → ∃ k : ℕ, π ^ k • d ∈ N₂ := by
    intro b
    induction b with
    | zero => intro d h; simpa using h
    | succ b ih =>
      intro d ⟨k, hk⟩
      apply ih
      apply hsat
      exact ⟨k, by rwa [smul_smul l, ← pow_succ']⟩
  have hpt : ∀ n ∈ N₂, ∃ c : ℕ, ∃ n₁ ∈ N₁, f n₁ = π ^ c • n := by
    intro n hn
    obtain ⟨d, rfl⟩ := hsurj n
    obtain ⟨k, n₁, hn₁, d', hd⟩ := hdens d
    have h1 : l ^ a • f d' = π ^ k • f d - f n₁ := by
      rw [← map_smul, ← map_smul, hd, map_add]
      abel
    obtain ⟨j, hj⟩ := hsat' a (f d') ⟨0, by
      rw [pow_zero, one_smul, h1]
      exact N₂.sub_mem (N₂.smul_mem _ hn) (hfN _ hn₁)⟩
    obtain ⟨n₁', hn₁', hf'⟩ := hl _ hj
    refine ⟨j + k, π ^ j • n₁ + n₁', N₁.add_mem (N₁.smul_mem _ hn₁) hn₁', ?_⟩
    rw [map_add, map_smul, hf', pow_add, mul_smul, smul_comm (l ^ a), h1, smul_sub]
    abel
  have huni : ∀ s : Finset D₂, (∀ x ∈ s, x ∈ N₂) →
      ∃ c : ℕ, ∀ x ∈ s, ∃ n₁ ∈ N₁, f n₁ = π ^ c • x := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; exact ⟨0, by simp⟩
    | insert x s hx ih =>
      intro h
      obtain ⟨c, hc⟩ := ih (fun y hy => h y (Finset.mem_insert_of_mem hy))
      obtain ⟨c', n', hn', hf'⟩ := hpt x (h x (Finset.mem_insert_self _ _))
      refine ⟨c + c', ?_⟩
      intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact ⟨π ^ c • n', N₁.smul_mem _ hn', by rw [map_smul, hf', pow_add, mul_smul]⟩
      · obtain ⟨n, hn, hf⟩ := hc y hy
        exact ⟨π ^ c' • n, N₁.smul_mem _ hn, by rw [map_smul, hf, pow_add, mul_comm, mul_smul]⟩
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨c, hc⟩ := huni s (fun x hx => hs ▸ Submodule.subset_span hx)
  refine ⟨c, fun n hn => ?_⟩
  have hle : Submodule.span A (s : Set D₂) ≤
      (N₁.map f).comap (π ^ c • (LinearMap.id : D₂ →ₗ[A] D₂)) := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨n₁, h1, h2⟩ := hc x hx
    exact ⟨n₁, h1, by simpa using h2⟩
  obtain ⟨n₁, h1, h2⟩ := hle (hs ▸ hn)
  exact ⟨n₁, h1, by simpa using h2⟩

theorem affineLine_localAcyclicity_of_strictHenselian_points : C3 := by
  intro O A _ _ _ B M D _ _ _ _ W y hQ x hx
  exact gammaStableOfGammaQUnit_holds O A B y D W.N W.γ hQ W.Q_bij W.γ_smul W.γ_N x hx

section Aeval

variable {O : Type} [CommRing O] {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M']
  [Module O M']

theorem aeval_intertwine_on (T : Submodule O M) (f : M →ₗ[O] M') (g : M →ₗ[O] M)
    (g' : M' →ₗ[O] M') (hT : ∀ d ∈ T, g d ∈ T) (h : ∀ d ∈ T, f (g d) = g' (f d))
    (q : Polynomial O) (d : M) (hd : d ∈ T) :
    f (Polynomial.aeval g q d) = Polynomial.aeval g' q (f d) := by
  have hpow : ∀ (n : ℕ) (d : M), d ∈ T → f ((g ^ n) d) = (g' ^ n) (f d) := by
    intro n
    induction n with
    | zero => intro d _; simp
    | succ n ih =>
      intro d hd
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih _ (hT d hd), h d hd]
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, hpow n d hd]

theorem aeval_mem (T : Submodule O M) (g : M →ₗ[O] M) (h : ∀ d ∈ T, g d ∈ T)
    (q : Polynomial O) (d : M) (hd : d ∈ T) : Polynomial.aeval g q d ∈ T := by
  have hpow : ∀ (n : ℕ) (d : M), d ∈ T → (g ^ n) d ∈ T := by
    intro n
    induction n with
    | zero => intro d hd; simpa using hd
    | succ n ih =>
      intro d hd
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (h d hd)
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply]
    exact T.add_mem hp hq
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact T.smul_mem _ (hpow n d hd)

end Aeval

theorem consequence_two_global : GlobalWachProductConsequence := by
  intro O A _ _ _ D _ _ _ _ N γ Q y p ρ P _ _ loc γl Ll Ly hloc hP5 hγ hLy hp d hd
  let NQ : Submodule O D :=
    { carrier := {d | ∃ k : ℕ, Q ^ k • d ∈ N}
      add_mem' := by
        rintro a b ⟨k, hk⟩ ⟨k', hk'⟩
        refine ⟨k + k', ?_⟩
        rw [smul_add]
        refine N.add_mem ?_ ?_
        · rw [pow_add, mul_comm, mul_smul]; exact N.smul_mem _ hk
        · rw [pow_add, mul_smul]; exact N.smul_mem _ hk'
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨k, hk⟩
        exact ⟨k, by rw [smul_comm]; exact N.smul_of_tower_mem c hk⟩ }
  have h1 : Polynomial.aeval γ p d ∈ NQ := aeval_mem NQ γ (fun d hd => hγ d hd) p d ⟨y, hd⟩
  refine hP5 _ h1 fun x => ?_
  rw [aeval_intertwine_on NQ (loc x) γ (γl x) (fun d hd => hγ d hd) (fun d hd => hloc x d hd) p d
    ⟨y, hd⟩]
  exact hp x _ (hLy d hd x)

end Formalism.RepresentationBoundsCohomology.N1
end
end

-- bundled from Formalism.WachLatticeTwists.WachProductBases.WachProductProofs.ToWachModuleHolds
section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N1

open Formalism.CoboundaryTransfers Finset

theorem to_wach_module_holds : ToWach := by
  intro O A _ _ _ S ι _ pr D _ _ _ _ W M h M₀ h₀ hrad hP2 hP5 hM hh
  classical
  cases nonempty_fintype ι
  have hGQ : S.base.GammaQ := (base_wach_holds O A S).2.2 hrad
  let N' : Submodule A (ι → D) := Submodule.pi Set.univ W.N
  let Φ : (ι → D) →ₗ[O] (ι → D) := LinearMap.pi (fun i => (W.φ i).comp (LinearMap.proj (pr i)))
  let Γ : (ι → D) →ₗ[O] (ι → D) := LinearMap.pi (fun i => (W.γ i).comp (LinearMap.proj i))
  have hΦ : ∀ x i, Φ x i = W.φ i (x (pr i)) := fun _ _ => rfl
  have hΓ : ∀ x i, Γ x i = W.γ i (x i) := fun _ _ => rfl
  have hmem : ∀ x : ι → D, x ∈ N' ↔ ∀ i, x i ∈ W.N i := by
    intro x
    simp [N', Submodule.mem_pi]
  have hΓs : ∀ (a : A) (x : ι → D), Γ (a • x) = S.base.γ a • Γ x := by
    intro a x
    funext i
    rw [hΓ, Pi.smul_apply, W.γ_smul, Pi.smul_apply, hΓ]
    rfl
  have hQbij : Function.Bijective (fun x : ι → D => S.base.Q • x) := by
    constructor
    · intro x y hxy
      funext i
      exact W.Q_bij.1 (congrFun hxy i)
    · intro y
      choose x hx using fun i => W.Q_bij.2 (y i)
      exact ⟨x, funext hx⟩
  have hΓN : ∀ x ∈ N', ∃ x' ∈ N', Γ x - x = S.base.X • x' := by
    intro x hx
    choose x' hx' hx'' using fun i => hP2 i (x i) ((hmem x).1 hx i)
    exact ⟨x', (hmem x').2 hx', funext fun i => hx'' i⟩
  let W' : WachMod S.base M₀ (ι → D) :=
    { N := N'
      φ := Φ
      γ := Γ
      φ_smul := by
        intro a x
        funext i
        rw [hΦ, Pi.smul_apply, W.φ_smul, Pi.smul_apply, hΦ]
        rfl
      γ_smul := hΓs
      comm := by
        intro x
        funext i
        rw [hΦ, hΓ, hΓ, hΦ, W.comm]
      X_inj := by
        intro x hx
        funext i
        apply W.X_bij.1
        have h0 : S.X • x i = 0 := congrFun hx i
        simpa using h0
      Q_bij := hQbij
      φ_N := by
        intro x hx
        rw [hmem]
        intro i
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hM i)
        rw [Pi.smul_apply, hΦ, hk, pow_add, mul_comm, mul_smul]
        exact (W.N i).smul_mem _ (hP5.1 i _ ((hmem x).1 hx (pr i)))
      γ_N := hΓN
      γ_QN := gammaStableOfGammaQUnit_holds O A S.base M₀ (ι → D) N' Γ hGQ hQbij hΓs hΓN }
  refine ⟨W', rfl, hΦ, hΓ, ?_⟩
  intro y hy
  set T := Submodule.span A (W'.φ '' (W'.N : Set (ι → D))) with hT
  have hsingle : ∀ i, (Submodule.span A (W.φ i '' (W.N (pr i) : Set D))).map
      (LinearMap.single A (fun _ => D) i) ≤ T := by
    intro i
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    refine ⟨Pi.single (pr i) n, ?_, ?_⟩
    · show Pi.single (pr i) n ∈ N'
      rw [hmem]
      intro j
      by_cases hj : j = pr i
      · subst hj; simpa using hn
      · rw [Pi.single_eq_of_ne hj]; exact (W.N j).zero_mem
    · funext j
      show W.φ j ((Pi.single (pr i) n : ι → D) (pr j)) = (Pi.single i (W.φ i n) : ι → D) j
      by_cases hj : j = i
      · subst hj; simp
      · have : pr j ≠ pr i := fun h => hj (pr.injective h)
        rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne this, map_zero]
  have hsum : S.base.Q ^ h₀ • y = ∑ i, Pi.single i (S.Q ^ h₀ • y i) := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp; rfl
    · intro i _ hij
      rw [Pi.single_eq_of_ne (Ne.symm hij)]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [hsum]
  refine T.sum_mem fun i _ => hsingle i ⟨_, ?_, rfl⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hh i)
  rw [hk, pow_add, mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ (hP5.2 i _ ((hmem y).1 hy i))

end Formalism.RepresentationBoundsCohomology.N1
end
end

