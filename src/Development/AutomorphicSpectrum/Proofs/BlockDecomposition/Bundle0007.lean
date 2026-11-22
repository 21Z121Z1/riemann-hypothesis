import Mathlib

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBoundOfIsBigO
section
open UpperHalfPlane hiding I
open Complex Filter Asymptotics CongruenceSubgroup ModularFormClass
open scoped Real MatrixGroups Modular

namespace GlobalTheory.CompanionTheory.CuspDecay

theorem exists_bound_of_isBigO {a : ℕ → ℂ} {e : ℝ}
    (h : a =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ e) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ e := by
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hC
  refine ⟨|C| + ∑ m ∈ Finset.range n₀, ‖a m‖ / (m : ℝ) ^ e, fun n hn ↦ ?_⟩
  have hpos : 0 < (n : ℝ) ^ e := Real.rpow_pos_of_pos (by exact_mod_cast hn) e
  have hS : ∀ m ∈ Finset.range n₀, 0 ≤ ‖a m‖ / (m : ℝ) ^ e := fun m _ ↦
    div_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg m) e)
  have hS0 := Finset.sum_nonneg hS
  rcases lt_or_ge n n₀ with h1 | h1
  · have h2 := Finset.single_le_sum hS (Finset.mem_range.mpr h1)
    have h3 : ‖a n‖ = ‖a n‖ / (n : ℝ) ^ e * (n : ℝ) ^ e := by field_simp
    rw [h3]
    exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C]) hpos.le
  · have h2 := hn₀ n h1
    rw [Real.norm_of_nonneg hpos.le] at h2
    refine h2.trans (mul_le_mul_of_nonneg_right ?_ hpos.le)
    linarith [le_abs_self C]

theorem exists_exp_bound {f : ℍ → ℂ} {e C : ℝ}
    (hO : f =O[atImInfty] fun τ ↦ Real.exp (-2 * π * τ.im))
    (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ e) :
    ∃ D : ℝ, ∀ τ : ℍ, 1 ≤ τ.im → ‖f τ‖ ≤ D * Real.exp (-τ.im) := by
  obtain ⟨D, hD⟩ := hO.bound
  rw [atImInfty, eventually_comap, eventually_atTop] at hD
  obtain ⟨A₀, hA⟩ := hD
  set A := max A₀ 1 with hAdef
  have hA1 : 1 ≤ A := le_max_right _ _
  refine ⟨|D| + |C| * A ^ |e| * Real.exp A, fun τ hτ ↦ ?_⟩
  have hy : 0 < τ.im := τ.im_pos
  have hE : 0 < Real.exp (-τ.im) := Real.exp_pos _
  have hAe : 0 ≤ |C| * A ^ |e| * Real.exp A := by positivity
  rcases le_total A τ.im with h1 | h1
  · have h2 := hA τ.im ((le_max_left _ _).trans h1) τ rfl
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at h2
    have h3 : Real.exp (-2 * π * τ.im) ≤ Real.exp (-τ.im) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_gt_three]
    calc ‖f τ‖ ≤ D * Real.exp (-2 * π * τ.im) := h2
      _ ≤ |D| * Real.exp (-2 * π * τ.im) :=
        mul_le_mul_of_nonneg_right (le_abs_self D) (Real.exp_pos _).le
      _ ≤ |D| * Real.exp (-τ.im) := mul_le_mul_of_nonneg_left h3 (abs_nonneg D)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hE.le
  · have h2 : (τ.im ^ e)⁻¹ ≤ A ^ |e| := by
      rw [← Real.rpow_neg hy.le]
      calc τ.im ^ (-e) ≤ τ.im ^ |e| := Real.rpow_le_rpow_of_exponent_le hτ (neg_le_abs e)
        _ ≤ A ^ |e| := Real.rpow_le_rpow hy.le h1 (abs_nonneg e)
    have h3 : 1 ≤ Real.exp A * Real.exp (-τ.im) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    have hAp : 0 ≤ A ^ |e| := by positivity
    calc ‖f τ‖ ≤ C / τ.im ^ e := hC τ
      _ = C * (τ.im ^ e)⁻¹ := div_eq_mul_inv _ _
      _ ≤ |C| * (τ.im ^ e)⁻¹ :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (inv_nonneg.mpr (by positivity))
      _ ≤ |C| * A ^ |e| := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
      _ ≤ |C| * A ^ |e| * (Real.exp A * Real.exp (-τ.im)) :=
        le_mul_of_one_le_right (by positivity) h3
      _ = |C| * A ^ |e| * Real.exp A * Real.exp (-τ.im) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [abs_nonneg D]) hE.le

theorem coeff_and_decay {N : ℕ} [NeZero N] {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [CuspFormClass F (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k] (f : F) (a : ℕ → ℂ)
    (ha : ∀ τ : ℍ, HasSum (fun n : ℕ ↦ a n * cexp (2 * π * I * n * τ)) (f τ)) :
    a 0 = 0 ∧ (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ C * (n : ℝ) ^ ((k : ℝ) / 2)) ∧
      ∃ D : ℝ, ∀ τ : ℍ, 1 ≤ τ.im → ‖f τ‖ ≤ D * Real.exp (-τ.im) := by
  have hΓ : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp
  have hcoef : ∀ m, a m = (qExpansion 1 f).coeff m := by
    refine ModularFormClass.qExpansion_coeff_unique (Γ := (Gamma1 N : Subgroup (GL (Fin 2) ℝ)))
      (k := k) one_pos hΓ fun τ ↦ ?_
    convert ha τ using 3 with n
    rw [smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hcoef]
    exact CuspFormClass.qExpansion_coeff_zero (Γ := (Gamma1 N : Subgroup (GL (Fin 2) ℝ)))
      (k := k) f one_pos hΓ
  · have h := CuspFormClass.qExpansion_isBigO (Γ := (Gamma1 N : Subgroup (GL (Fin 2) ℝ)))
      (k := k) f
    have hw : (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictWidthInfty = 1 := by simp
    rw [hw] at h
    have ha' : a = fun n ↦ (qExpansion 1 f).coeff n := funext hcoef
    rw [← ha'] at h
    exact exists_bound_of_isBigO h
  · obtain ⟨C, hC⟩ := CuspFormClass.exists_bound (Γ := (Gamma1 N : Subgroup (GL (Fin 2) ℝ)))
      (k := k) f
    have hO := CuspFormClass.exp_decay_atImInfty (Γ := (Gamma1 N : Subgroup (GL (Fin 2) ℝ)))
      (k := k) (h := 1) f one_pos hΓ
    simp only [Nat.cast_one, div_one] at hO
    exact exists_exp_bound (by simpa using hO) hC

end GlobalTheory.CompanionTheory.CuspDecay
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChainsOfRange
section
namespace GlobalTheory.CompanionTheory.JordanChain

open Module Submodule

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

def chainVec (f : V →ₗ[K] V) {ι : Type} (e : ι → ℕ) (v : ι → V) : (Σ a, Fin (e a)) → V :=
  fun p => (f ^ (p.2 : ℕ)) (v p.1)

theorem pow_coe_of_restrict {W : Submodule K V} (f : V →ₗ[K] V) (g : W →ₗ[K] W)
    (hg : ∀ x, (g x : V) = f x) (k : ℕ) (x : W) : (((g ^ k) x : W) : V) = (f ^ k) x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hg]

theorem exists_chains_of_range [FiniteDimensional K V] (f : V →ₗ[K] V)
    (g : LinearMap.range f →ₗ[K] LinearMap.range f) (hg : ∀ x, (g x : V) = f x)
    {ι' : Type} [Fintype ι'] (e' : ι' → ℕ) (he' : ∀ b, 0 < e' b) (w : ι' → LinearMap.range f)
    (h0 : ∀ b, (g ^ e' b) (w b) = 0) (hli : LinearIndependent K (chainVec g e' w))
    (hsp : span K (Set.range (chainVec g e' w)) = ⊤) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (v : ι → V), (∀ a, 0 < e a) ∧
      (∀ a, (f ^ e a) (v a) = 0) ∧ LinearIndependent K (chainVec f e v) ∧
      span K (Set.range (chainVec f e v)) = ⊤ := by
  classical
  have hu : ∀ b, ∃ u, f u = (w b : V) := fun b => (w b).2
  choose u hu using hu
  have hstep : ∀ (b : ι') (j : ℕ), (f ^ (j + 1)) (u b) = (f ^ j) (w b : V) := by
    intro b j
    rw [pow_succ, Module.End.mul_apply, hu]
  set N := LinearMap.ker f with hN
  let t : ι' → V := fun b => (f ^ e' b) (u b)
  have htN : ∀ b, t b ∈ N := by
    intro b
    have h1 : f (t b) = (f ^ (e' b + 1)) (u b) := by
      simp only [t]
      rw [pow_succ', Module.End.mul_apply]
    rw [hN, LinearMap.mem_ker, h1, hstep, ← pow_coe_of_restrict f g hg, h0]
    rfl
  have hLV : LinearIndependent K (fun p => ((chainVec g e' w p : LinearMap.range f) : V)) :=
    hli.map' (LinearMap.range f).subtype (Submodule.ker_subtype _)
  let idx : ι' → Σ b, Fin (e' b) := fun b => ⟨b, ⟨e' b - 1, by have := he' b; omega⟩⟩
  have hidx : Function.Injective idx := fun a b h => congrArg Sigma.fst h
  have ht : LinearIndependent K t := by
    have h2 := hLV.comp idx hidx
    convert h2 using 1
    funext b
    simp only [t, Function.comp, idx, chainVec]
    rw [pow_coe_of_restrict f g hg, ← hstep]
    congr 2
    have := he' b
    omega
  let tN : ι' → N := fun b => ⟨t b, htN b⟩
  have htNli : LinearIndependent K tN := LinearIndependent.of_comp N.subtype ht
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (span K (Set.range tN))
  let bC := Module.finBasis K C
  let z : Fin (finrank K C) → V := fun c => ((bC c : C) : N)
  have hz : ∀ c, f (z c) = 0 := fun c => ((bC c : C) : N).2
  let e : ι' ⊕ Fin (finrank K C) → ℕ := Sum.elim (fun b => e' b + 1) (fun _ => 1)
  let v : ι' ⊕ Fin (finrank K C) → V := Sum.elim u z
  let T := span K (Set.range (chainVec f e v))
  have hTu : ∀ (b : ι') (j : ℕ), j ≤ e' b → (f ^ j) (u b) ∈ T := by
    intro b j hj
    exact subset_span ⟨⟨Sum.inl b, ⟨j, Nat.lt_succ_of_le hj⟩⟩, rfl⟩
  have hTz : ∀ c, z c ∈ T := by
    intro c
    exact subset_span ⟨⟨Sum.inr c, ⟨0, Nat.one_pos⟩⟩, by simp [chainVec, v]⟩
  have hkerS : map N.subtype (span K (Set.range tN)) ≤ T := by
    refine (Submodule.map_span_le _ _ _).2 ?_
    rintro _ ⟨b, rfl⟩
    exact hTu b _ le_rfl
  have hkerC : map (N.subtype ∘ₗ C.subtype) ⊤ ≤ T := by
    rw [← bC.span_eq]
    refine (Submodule.map_span_le _ _ _).2 ?_
    rintro _ ⟨c, rfl⟩
    exact hTz c
  have hker : N ≤ T := by
    intro x hx
    have hx' : (⟨x, hx⟩ : N) ∈ span K (Set.range tN) ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨s, hs, c, hc, hsc⟩ := Submodule.mem_sup.1 hx'
    have hxe : x = (s : V) + (c : V) := by
      have := congrArg Subtype.val hsc
      simpa using this.symm
    rw [hxe]
    exact T.add_mem (hkerS ⟨s, hs, rfl⟩) (hkerC ⟨⟨c, hc⟩, trivial, rfl⟩)
  have hrange : ∀ y : LinearMap.range f, ∃ x ∈ T, f x = y := by
    have h3 : map (LinearMap.range f).subtype (span K (Set.range (chainVec g e' w))) ≤ map f T := by
      refine (Submodule.map_span_le _ _ _).2 ?_
      rintro _ ⟨⟨b, j⟩, rfl⟩
      refine ⟨(f ^ (j : ℕ)) (u b), hTu b _ j.2.le, ?_⟩
      simp only [chainVec, Submodule.subtype_apply]
      rw [pow_coe_of_restrict f g hg, ← hstep, pow_succ']
      rfl
    intro y
    have hy : (y : V) ∈ map (LinearMap.range f).subtype (span K (Set.range (chainVec g e' w))) := by
      rw [hsp]
      exact ⟨y, trivial, rfl⟩
    obtain ⟨x, hx, hxy⟩ := h3 hy
    exact ⟨x, hx, hxy⟩
  have hTtop : T = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨x', hx', hxx⟩ := hrange ⟨f x, x, rfl⟩
    have hk : x - x' ∈ N := by
      rw [hN, LinearMap.mem_ker, map_sub, hxx]
      simp
    have := T.add_mem (hker hk) hx'
    simpa using this
  have hcard₁ : finrank K (LinearMap.range f) = ∑ b, e' b := by
    have h4 := finrank_span_eq_card hli
    rw [hsp, finrank_top] at h4
    rw [h4, Fintype.card_sigma]
    simp
  have hcard₂ : finrank K N = Fintype.card ι' + finrank K C := by
    have h5 := Submodule.finrank_add_eq_of_isCompl hC
    rw [finrank_span_eq_card htNli] at h5
    exact h5.symm
  have hcard : Fintype.card (Σ a, Fin (e a)) = finrank K V := by
    have h6 := LinearMap.finrank_range_add_finrank_ker f
    rw [Fintype.card_sigma, ← h6, hcard₁, ← hN, hcard₂]
    simp [e, Fintype.sum_sum_type, Finset.sum_add_distrib]
    omega
  refine ⟨ι' ⊕ Fin (finrank K C), inferInstance, e, v, ?_, ?_, ?_, hTtop⟩
  · rintro (b | c)
    · exact Nat.succ_pos _
    · exact Nat.one_pos
  · rintro (b | c)
    · change (f ^ (e' b + 1)) (u b) = 0
      rw [hstep, ← pow_coe_of_restrict f g hg, h0]
      rfl
    · change (f ^ 1) (z c) = 0
      simpa using hz c
  · exact linearIndependent_of_top_le_span_of_card_eq_finrank hTtop.ge hcard

theorem exists_chains : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] V), finrank K V = n → IsNilpotent f →
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (v : ι → V), (∀ a, 0 < e a) ∧
      (∀ a, (f ^ e a) (v a) = 0) ∧ LinearIndependent K (chainVec f e v) ∧
      span K (Set.range (chainVec f e v)) = ⊤ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ f hn hf
    by_cases hV : Subsingleton V
    · refine ⟨Empty, inferInstance, fun _ => 0, fun _ => 0, fun a => a.elim, fun a => a.elim,
        ?_, Subsingleton.elim _ _⟩
      exact linearIndependent_empty_type
    · have hnt : Nontrivial V := not_subsingleton_iff_nontrivial.1 hV
      obtain ⟨m, hm⟩ := hf
      have hlt : finrank K (LinearMap.range f) < n := by
        rw [← hn]
        refine Submodule.finrank_lt ?_
        intro htop
        have hsurj : Function.Surjective f := LinearMap.range_eq_top.1 htop
        have hs : Function.Surjective (f ^ m) := by
          rw [Module.End.coe_pow]
          exact hsurj.iterate m
        rw [hm] at hs
        obtain ⟨x, hx⟩ := exists_ne (0 : V)
        obtain ⟨y, hy⟩ := hs x
        exact hx (by simpa using hy.symm)
      let g : LinearMap.range f →ₗ[K] LinearMap.range f :=
        f.restrict (fun x _ => LinearMap.mem_range_self f x)
      have hg : ∀ x, (g x : V) = f x := fun x => rfl
      have hgn : IsNilpotent g := by
        refine ⟨m, LinearMap.ext fun x => Subtype.ext ?_⟩
        rw [pow_coe_of_restrict f g hg, hm]
        rfl
      obtain ⟨ι', _, e', w, he', h0, hli, hsp⟩ := ih _ hlt (LinearMap.range f) g rfl hgn
      exact exists_chains_of_range f g hg e' he' w h0 hli hsp

theorem exists_chain_basis {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : V →ₗ[K] V) (hf : IsNilpotent f) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (v : ι → V), (∀ a, 0 < e a) ∧
      (∀ a, (f ^ e a) (v a) = 0) ∧
      LinearIndependent K (fun p : Σ a, Fin (e a) => (f ^ (p.2 : ℕ)) (v p.1)) ∧
      span K (Set.range (fun p : Σ a, Fin (e a) => (f ^ (p.2 : ℕ)) (v p.1))) = ⊤ :=
  exists_chains _ V f rfl hf

end GlobalTheory.CompanionTheory.JordanChain
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactOpenSubgroupMem
section
open Matrix ValuativeRel

namespace GlobalTheory.CompanionTheory.LatticePoint

theorem isOpen_valBall {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (γ : ValueGroupWithZero k) (hγ : γ ≠ 0) :
    IsOpen {x : k | valuation k x ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  change valuation k x ≤ γ at hx
  rw [IsValuativeTopology.mem_nhds_iff']
  refine ⟨Units.mk0 γ hγ, fun y hy => ?_⟩
  change valuation k (y - x) < ((Units.mk0 γ hγ : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) at hy
  rw [Units.val_mk0] at hy
  show valuation k y ≤ γ
  calc valuation k y = valuation k ((y - x) + x) := by rw [sub_add_cancel]
    _ ≤ max (valuation k (y - x)) (valuation k x) := Valuation.map_add _ _ _
    _ ≤ γ := max_le hy.le hx

theorem exists_compact_open_addSubgroup_mem :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (n : ℕ) (x : Fin n → k),
      ∃ A : AddSubgroup (Fin n → k), IsCompact (A : Set (Fin n → k)) ∧
        IsOpen (A : Set (Fin n → k)) ∧ x ∈ A := by
  intro k _ _ _ _ n x
  let γ : ValueGroupWithZero k := Finset.univ.sup (fun i => valuation k (x i)) ⊔ 1
  have hγ : γ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one le_sup_right)
  let S : AddSubgroup k :=
    { carrier := {y | valuation k y ≤ γ}
      add_mem' := fun {a b} ha hb => by
        change valuation k a ≤ γ at ha
        change valuation k b ≤ γ at hb
        show valuation k (a + b) ≤ γ
        exact (Valuation.map_add _ _ _).trans (max_le ha hb)
      zero_mem' := by
        show valuation k 0 ≤ γ
        simp
      neg_mem' := fun {a} ha => by
        change valuation k a ≤ γ at ha
        show valuation k (-a) ≤ γ
        rwa [Valuation.map_neg] }
  have hS : (S : Set k) = {y | valuation k y ≤ γ} := rfl
  refine ⟨AddSubgroup.pi Set.univ (fun _ => S), ?_, ?_, ?_⟩
  · rw [AddSubgroup.coe_pi, hS]
    exact isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k γ
  · rw [AddSubgroup.coe_pi, hS]
    exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_valBall γ hγ
  · rw [AddSubgroup.mem_pi]
    intro i _
    show valuation k (x i) ≤ γ
    exact le_sup_of_le_left (Finset.le_sup (f := fun i => valuation k (x i)) (Finset.mem_univ i))

end GlobalTheory.CompanionTheory.LatticePoint
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCongruenceSubset
section
open ValuativeRel Filter Topology Matrix

namespace GlobalTheory.CompanionTheory.CongruenceBasis

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_pow_succ_lt {a γ : ValueGroupWithZero k} (ha0 : a ≠ 0) (ha : a < 1) (hγ : γ ≠ 0) :
    ∃ m : ℕ, a ^ (m + 1) < γ := by
  haveI : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.1 inferInstance
  have h1 : 1 < a⁻¹ := (one_lt_inv₀ (zero_lt_iff.2 ha0)).2 ha
  obtain ⟨n, hn⟩ := MulArchimedean.arch γ⁻¹ h1
  refine ⟨n, ?_⟩
  have h2 : a ^ n ≤ γ := by
    rw [inv_pow] at hn
    exact (inv_le_inv₀ (zero_lt_iff.2 hγ) (zero_lt_iff.2 (pow_ne_zero n ha0))).1 hn
  exact lt_of_lt_of_le (pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.2 ha0) ha n.lt_succ_self) h2

theorem inv_mem_of_mem {N : ℕ} {t : ValueGroupWithZero k} (ht : t < 1) (g : GL (Fin N) k)
    (hg : ∀ i j, valuation k ((g : Matrix (Fin N) (Fin N) k) i j -
      (1 : Matrix (Fin N) (Fin N) k) i j) ≤ t) (i j : Fin N) :
    valuation k (((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j -
      (1 : Matrix (Fin N) (Fin N) k) i j) ≤ t := by
  set A : Matrix (Fin N) (Fin N) k := (g : Matrix (Fin N) (Fin N) k) - 1 with hA
  set B : Matrix (Fin N) (Fin N) k := ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) - 1 with hB
  have hAle : ∀ i j, valuation k (A i j) ≤ t := fun i j => by simpa [hA] using hg i j
  have hrel : B = -A - A * B := by
    have hgh : (g : Matrix (Fin N) (Fin N) k) * ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hg' : (g : Matrix (Fin N) (Fin N) k) = A + 1 := by simp [hA]
    have hh' : ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) = B + 1 := by simp [hB]
    rw [hg', hh'] at hgh
    have : (A + 1) * (B + 1) = A * B + A + B + 1 := by noncomm_ring
    rw [this] at hgh
    have h3 : A * B + A + B = 0 := by simpa using hgh
    rw [eq_sub_iff_add_eq, eq_neg_iff_add_eq_zero, ← h3]
    abel
  show valuation k (B i j) ≤ t
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨⟨i₀, j₀⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin N × Fin N))
    (fun p => valuation k (B p.1 p.2)) ⟨(i, j), Finset.mem_univ _⟩
  set M := valuation k (B i₀ j₀) with hM
  have hMt : t < M := lt_of_lt_of_le hcon (hmax (i, j) (Finset.mem_univ _))
  have hM0 : 0 < M := lt_of_le_of_lt zero_le' hMt
  have hprod : valuation k ((A * B) i₀ j₀) ≤ t * M := by
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_le _ fun l _ => ?_
    rw [map_mul]
    exact mul_le_mul' (hAle _ _) (hmax (l, j₀) (Finset.mem_univ _))
  have htM : t * M < M := by
    simpa using mul_lt_mul_of_pos_right ht hM0
  have hent : B i₀ j₀ = -A i₀ j₀ - (A * B) i₀ j₀ := by
    conv_lhs => rw [hrel]
    simp
  have : M < M := by
    calc M = valuation k (-A i₀ j₀ - (A * B) i₀ j₀) := by rw [hM, ← hent]
      _ ≤ max (valuation k (-A i₀ j₀)) (valuation k ((A * B) i₀ j₀)) := Valuation.map_sub _ _ _
      _ < M := by
        refine max_lt ?_ (lt_of_le_of_lt hprod htM)
        rw [Valuation.map_neg]
        exact lt_of_le_of_lt (hAle _ _) hMt
  exact lt_irrefl _ this

theorem exists_congruence_subset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : k), ϖ ≠ 0 →
    ValuativeRel.valuation k (ϖ) < 1 →
    (∀ x : k, ValuativeRel.valuation k (x) < 1 →
      ValuativeRel.valuation k (x) ≤ ValuativeRel.valuation k (ϖ)) →
    ∀ U : Set (GL (Fin N) k), U ∈ nhds (1 : GL (Fin N) k) →
    ∃ m : ℕ, 1 ≤ m ∧ {g : GL (Fin N) k | ∀ i j,
      ValuativeRel.valuation k ((g : Matrix (Fin N) (Fin N) k) i j -
        (1 : Matrix (Fin N) (Fin N) k) i j) ≤ ValuativeRel.valuation k (ϖ ^ m)} ⊆ U := by
  intro k _ _ _ _ N ϖ hϖ0 hϖ1 _ U hU
  set a := valuation k ϖ with ha
  have ha0 : a ≠ 0 := (Valuation.ne_zero_iff _).2 hϖ0
  let K : ℕ → Set (GL (Fin N) k) := fun m => {g | ∀ i j,
    valuation k ((g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ a ^ (m + 1)}
  have hanti : Antitone K := fun m n hmn g hg i j =>
    (hg i j).trans (pow_le_pow_of_le_one zero_le' hϖ1.le (by omega))
  have hbasis : (⨅ m, 𝓟 (K m)).HasBasis (fun _ => True) K :=
    hasBasis_iInf_principal hanti.directed_ge
  have hent : ∀ (i j : Fin N) (c : GL (Fin N) k → k), (∀ m, ∀ g ∈ K m, valuation k (c g - (1 : Matrix (Fin N) (Fin N) k) i j) ≤ a ^ (m + 1)) →
      Tendsto c (⨅ m, 𝓟 (K m)) (𝓝 ((1 : Matrix (Fin N) (Fin N) k) i j)) := by
    intro i j c hc
    rw [(IsValuativeTopology.hasBasis_nhds' _).tendsto_right_iff]
    intro γ hγ
    obtain ⟨m, hm⟩ := exists_pow_succ_lt ha0 hϖ1 hγ
    exact hbasis.eventually_iff.2 ⟨m, trivial, fun g hg => lt_of_le_of_lt (hc m g hg) hm⟩
  have hlim : Tendsto (id : GL (Fin N) k → GL (Fin N) k) (⨅ m, 𝓟 (K m)) (𝓝 1) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    refine Tendsto.prodMk_nhds ?_ ?_
    · refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      exact hent i j _ fun m g hg => hg i j
    · refine (MulOpposite.continuous_op.tendsto _).comp ?_
      refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      exact hent i j (fun g => ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) fun m g hg =>
        inv_mem_of_mem (pow_lt_one₀ zero_le' hϖ1 (by omega)) g hg i j
  obtain ⟨m, -, hm⟩ := hbasis.mem_iff.1 (hlim hU)
  refine ⟨m + 1, by omega, fun g hg => hm fun i j => ?_⟩
  simpa [ha, map_pow] using hg i j

end GlobalTheory.CompanionTheory.CongruenceBasis
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConjMulEq
section
namespace GlobalTheory.CompanionTheory.FFNorm

theorem exists_conj_mul_eq : ∀ (κ : Type) [Field κ] [Finite κ] (τ : κ →+* κ), (∀ x, τ (τ x) = x) →
    (∃ x, τ x ≠ x) → ∀ c : κ, τ c = c → ∃ s : κ, τ s * s = c := by
  intro κ _ _ τ hinv hne c hc
  classical
  let F : Subfield κ := RingHom.eqLocusField τ (RingHom.id κ)
  have hF : ∀ y : F, τ (y : κ) = y := fun y => y.2
  let σ : κ ≃ₐ[F] κ := AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom τ τ
      (RingHom.ext hinv) (RingHom.ext hinv)) (fun y => hF y)
  have hσ : ∀ x, σ x = τ x := fun x => rfl
  have hσ1 : σ ≠ 1 := by
    obtain ⟨x, hx⟩ := hne
    intro h
    exact hx (by rw [← hσ, h]; rfl)
  have hall : ∀ ρ : κ ≃ₐ[F] κ, ρ = 1 ∨ ρ = σ := by
    have hfix : IntermediateField.fixedField (Subgroup.zpowers σ) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : σ x = x := hx ⟨σ, Subgroup.mem_zpowers σ⟩
      exact IntermediateField.mem_bot.2 ⟨⟨x, this⟩, rfl⟩
    have htop : Subgroup.zpowers σ = ⊤ := by
      rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers σ), hfix]
      exact IntermediateField.fixingSubgroup_bot
    intro ρ
    have hρ : ρ ∈ Subgroup.zpowers σ := htop ▸ Subgroup.mem_top ρ
    have hsq : σ ^ 2 = 1 := by
      ext x
      simp [pow_two, hσ, hinv]
    obtain ⟨n, rfl⟩ := hρ
    rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
    · left; simp [zpow_mul, hsq]
    · right; simp [zpow_add, zpow_mul, hsq]
  have huniv : (Finset.univ : Finset (κ ≃ₐ[F] κ)) = {1, σ} := by
    ext ρ
    simpa using hall ρ
  obtain ⟨a, ha⟩ := FiniteField.norm_surjective F κ (⟨c, hc⟩ : F)
  refine ⟨a, ?_⟩
  have h := Algebra.norm_eq_prod_automorphisms F a
  rw [huniv, Finset.prod_pair hσ1.symm, ha] at h
  have h2 : algebraMap F κ (⟨c, hc⟩ : F) = c := rfl
  rw [h2] at h
  simpa [hσ, mul_comm] using h.symm

end GlobalTheory.CompanionTheory.FFNorm
end

