import Formalism.GaloisIrreducibility.Statement

-- bundled from Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.PermSubSumInv
section
namespace Formalism.GaloisIrreducibility

namespace SubsetSumInvariance

open Equiv Equiv.Perm Finset

variable {α : Type} [Fintype α] [DecidableEq α]

def orbs (σ : Perm α) : Finset (Finset α) :=
  (σ.cycleFactorsFinset.image support) ∪ ((univ \ σ.support).image fun y => {y})

lemma fixed_of_not_mem {σ : Perm α} {y : α} (h : y ∉ σ.support) : σ y = y := Perm.notMem_support.1 h

lemma orbs_stable {σ : Perm α} {O : Finset α} (hO : O ∈ orbs σ) : ∀ x ∈ O, σ x ∈ O := by
  intro x hx
  rcases Finset.mem_union.1 hO with h | h
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h
    rw [← (Perm.mem_cycleFactorsFinset_iff.1 hc).2 x hx]
    exact Perm.apply_mem_support.2 hx
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 h
    rw [Finset.mem_singleton] at hx ⊢
    subst hx
    exact fixed_of_not_mem (Finset.mem_sdiff.1 hy).2

lemma pow_stable {σ : Perm α} {A : Finset α} (hA : ∀ x ∈ A, σ x ∈ A) :
    ∀ m : ℕ, ∀ z ∈ A, (σ ^ m) z ∈ A := by
  intro m
  induction m with
  | zero => intro z hz; simpa using hz
  | succ m ih =>
    intro z hz
    rw [pow_succ', Perm.mul_apply]
    exact hA _ (ih z hz)

lemma orbs_sub {σ : Perm α} {A : Finset α} (hA : ∀ x ∈ A, σ x ∈ A) {O : Finset α}
    (hO : O ∈ orbs σ) {x : α} (hxO : x ∈ O) (hxA : x ∈ A) : O ⊆ A := by
  intro y hy
  rcases Finset.mem_union.1 hO with h | h
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h
    have hcx : c = σ.cycleOf x := Perm.cycle_is_cycleOf hxO hc
    rw [hcx, Perm.mem_support_cycleOf_iff] at hy
    obtain ⟨i, hi⟩ := hy.1.exists_nat_pow_eq
    rw [← hi]
    exact pow_stable hA i x hxA
  · obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 h
    rw [Finset.mem_singleton] at hy hxO
    rw [hy, ← hxO]
    exact hxA

lemma orbs_eq {σ : Perm α} {O O' : Finset α} (hO : O ∈ orbs σ) (hO' : O' ∈ orbs σ) {x : α}
    (h1 : x ∈ O) (h2 : x ∈ O') : O = O' := by
  have key : ∀ {O O' : Finset α}, O ∈ orbs σ → O' ∈ orbs σ → x ∈ O → x ∈ O' → O ⊆ O' := by
    intro O O' hO hO' h1 h2
    exact orbs_sub (fun y hy => orbs_stable hO' y hy) hO h1 h2
  exact Finset.Subset.antisymm (key hO hO' h1 h2) (key hO' hO h2 h1)

lemma orbs_pd (σ : Perm α) : (orbs σ : Set (Finset α)).PairwiseDisjoint id := by
  intro O hO O' hO' hne
  rw [Function.onFun, id, id, Finset.disjoint_left]
  intro x h1 h2
  exact hne (orbs_eq hO hO' h1 h2)

lemma orbs_parts (σ : Perm α) : (orbs σ).val.map Finset.card = σ.partition.parts := by
  have hdisj : Disjoint (σ.cycleFactorsFinset.image support) ((univ \ σ.support).image fun y => {y}) := by
    rw [Finset.disjoint_left]
    intro O h1 h2
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨y, -, hy⟩ := Finset.mem_image.1 h2
    have h2le := (Perm.mem_cycleFactorsFinset_iff.1 hc).1.two_le_card_support
    rw [← hy, Finset.card_singleton] at h2le
    omega
  have hinj1 : Set.InjOn support (σ.cycleFactorsFinset : Set (Perm α)) := by
    intro c hc c' hc' h
    obtain ⟨a, ha⟩ := (Perm.mem_cycleFactorsFinset_iff.1 hc).1.nonempty_support
    rw [Perm.cycle_is_cycleOf ha hc, Perm.cycle_is_cycleOf (h ▸ ha) hc']
  have hinj2 : Set.InjOn (fun y : α => ({y} : Finset α)) ((univ \ σ.support : Finset α) : Set α) := by
    intro y _ z _ h
    exact Finset.singleton_injective h
  rw [orbs, ← Finset.disjUnion_eq_union _ _ hdisj, Finset.disjUnion_val, Multiset.map_add,
    Finset.image_val_of_injOn hinj1, Finset.image_val_of_injOn hinj2, Multiset.map_map, Multiset.map_map,
    Perm.parts_partition, Perm.cycleType_def]
  congr 1
  have : (Finset.card ∘ fun y : α => ({y} : Finset α)) = fun _ => 1 := by
    funext y
    simp
  rw [this, Multiset.map_const', Finset.card_val, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ]

end SubsetSumInvariance

namespace SubsetSumInvariance

lemma exists_le_map {β γ : Type*} (f : β → γ) (m : Multiset β) :
    ∀ s : Multiset γ, s ≤ m.map f → ∃ t ≤ m, t.map f = s := by
  classical
  induction m using Multiset.induction_on with
  | empty =>
    intro s hs
    refine ⟨0, le_rfl, ?_⟩
    simp only [Multiset.map_zero, nonpos_iff_eq_zero] at hs ⊢
    exact hs.symm
  | cons b m ih =>
    intro s hs
    rw [Multiset.map_cons] at hs
    by_cases hb : f b ∈ s
    · have hle : s.erase (f b) ≤ m.map f := by
        have := Multiset.erase_le_erase (f b) hs
        rwa [Multiset.erase_cons_head] at this
      obtain ⟨t, ht, htf⟩ := ih _ hle
      refine ⟨b ::ₘ t, Multiset.cons_le_cons b ht, ?_⟩
      rw [Multiset.map_cons, htf, Multiset.cons_erase hb]
    · obtain ⟨t, ht, htf⟩ := ih s ((Multiset.le_cons_of_notMem hb).1 hs)
      exact ⟨t, ht.trans (Multiset.le_cons_self _ _), htf⟩

end SubsetSumInvariance

open SubsetSumInvariance in
theorem exists_invariant_of_isSubSum {α : Type} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (a : ℕ)
    (h : IsSubSum σ.partition.parts a) : ∃ A : Finset α, (∀ x ∈ A, σ x ∈ A) ∧ A.card = a := by
  obtain ⟨s, hs, hsum⟩ := h
  rw [← orbs_parts] at hs
  obtain ⟨t, ht, htf⟩ := exists_le_map Finset.card _ s hs
  let T : Finset (Finset α) := ⟨t, Multiset.nodup_of_le ht (orbs σ).nodup⟩
  have hT : T ⊆ orbs σ := fun O hO => Multiset.subset_of_le ht hO
  refine ⟨T.biUnion id, ?_, ?_⟩
  · intro x hx
    obtain ⟨O, hO, hxO⟩ := Finset.mem_biUnion.1 hx
    exact Finset.mem_biUnion.2 ⟨O, hO, orbs_stable (hT hO) x hxO⟩
  · rw [Finset.card_biUnion (fun O hO O' hO' hne => orbs_pd σ (hT hO) (hT hO') hne),
      Finset.sum_eq_multiset_sum]
    change (t.map fun O => (id O).card).sum = a
    simpa [htf] using hsum

theorem permutation_subset_sum_invariant : PermSubSumInv := by
  intro α _ _ σ a h
  obtain ⟨A, hA, hcard⟩ := exists_invariant_of_isSubSum σ a h
  exact ⟨A, hA, hcard⟩

end Formalism.GaloisIrreducibility
end

-- bundled from Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.PrimitiveOfPCycle
section
namespace Formalism.GaloisIrreducibility

open scoped Pointwise

theorem poc_powSmul_injective {M Y : Type*} [Group M] [MulAction M Y] (s : M) (p : ℕ) (hp : p.Prime)
    (hs : s ^ p = 1) (y : Y) (hy : s • y ≠ y) :
    ∀ i < p, ∀ j < p, s ^ i • y = s ^ j • y → i = j := by
  have key : ∀ d : ℕ, 0 < d → d < p → s ^ d • y ≠ y := by
    intro d hd0 hdp hd
    have hnd : ¬ p ∣ d := fun h => absurd (Nat.le_of_dvd hd0 h) (by omega)
    have hcop : Nat.Coprime d p := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
    have h1 : s ^ d ∈ MulAction.stabilizer M y := MulAction.mem_stabilizer_iff.mpr hd
    have h2 : s ^ p ∈ MulAction.stabilizer M y := by rw [hs]; exact one_mem _
    have hb := Nat.gcd_eq_gcd_ab d p
    rw [hcop.gcd_eq_one] at hb
    have e : s = (s ^ d) ^ (Nat.gcdA d p) * (s ^ p) ^ (Nat.gcdB d p) := by
      rw [← zpow_natCast s d, ← zpow_natCast s p, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hb,
        Nat.cast_one, zpow_one]
    have h3 : s ∈ MulAction.stabilizer M y := by
      rw [e]; exact mul_mem (zpow_mem h1 _) (zpow_mem h2 _)
    exact hy (MulAction.mem_stabilizer_iff.mp h3)
  have step : ∀ i j : ℕ, i < j → j < p → s ^ i • y = s ^ j • y → False := by
    intro i j hij hjp h
    apply key (j - i) (by omega) (by omega)
    have h' : s ^ i • (s ^ (j - i) • y) = s ^ i • y := by
      rw [smul_smul, ← pow_add, show i + (j - i) = j by omega]
      exact h.symm
    exact (smul_left_cancel_iff _).mp h'
  intro i hi j hj hij
  rcases lt_trichotomy i j with h | h | h
  · exact (step i j h hj hij).elim
  · exact h
  · exact (step j i h hi hij.symm).elim

theorem primitive_of_p_cycle : PrimitiveOfPCycle := by
  unfold PrimitiveOfPCycle
  intro α _ _ G σ p hp hσG hcyc hsupp hcard htr
  refine @MulAction.IsPreprimitive.mk _ _ _ htr ?_
  intro B hB
  by_contra hcon
  unfold MulAction.IsTrivialBlock at hcon
  rw [not_or] at hcon
  obtain ⟨hns, hnt⟩ := hcon
  obtain ⟨b, hb, c, hc, hbc⟩ : ∃ b ∈ B, ∃ c ∈ B, b ≠ c := by
    by_contra h
    push_neg at h
    exact hns (fun u hu v hv => h u hu v hv)
  obtain ⟨z, hz⟩ : ∃ z, z ∉ B := by
    by_contra h
    push_neg at h
    exact hnt (Set.eq_univ_of_forall h)
  have hσp : σ ^ p = 1 := by
    rw [← hsupp, ← hcyc.orderOf]; exact pow_orderOf_eq_one σ
  obtain ⟨x, hxs⟩ : σ.support.Nonempty := Finset.card_pos.mp (by rw [hsupp]; exact hp.pos)
  obtain ⟨s, hsσ⟩ : ∃ s : G, (s : Equiv.Perm α) = σ := ⟨⟨σ, hσG⟩, rfl⟩
  have hs : s ^ p = 1 := Subtype.ext (by simp [hsσ, hσp])
  have hx : s • x ≠ x := by
    rw [Subgroup.smul_def, hsσ, Equiv.Perm.smul_def]; exact Equiv.Perm.mem_support.mp hxs
  obtain ⟨g, hgb⟩ := MulAction.exists_smul_eq G b x
  set t : G := g⁻¹ * s * g with ht
  have htp : t ^ p = 1 := by
    have e : ∀ i : ℕ, t ^ i = g⁻¹ * s ^ i * g := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [pow_succ, ih, ht, pow_succ]; group
    rw [e, hs]; group
  have htb : t • b ≠ b := by
    intro h
    apply hx
    have h2 : g • (t • b) = g • b := by rw [h]
    rw [ht, mul_smul, mul_smul, smul_inv_smul, hgb] at h2
    exact h2
  have blk : ∀ g₁ g₂ : G, g₁ • B ≠ g₂ • B → Disjoint (g₁ • B) (g₂ • B) := by
    intro g₁ g₂ hne
    rcases hB.smul_eq_or_disjoint (g₂⁻¹ * g₁) with h | h
    · exfalso; apply hne
      rw [mul_smul] at h
      calc g₁ • B = g₂ • (g₂⁻¹ • g₁ • B) := (smul_inv_smul g₂ _).symm
        _ = g₂ • B := by rw [h]
    · rw [Set.disjoint_left]
      intro a ha1 ha2
      rw [Set.mem_smul_set_iff_inv_smul_mem] at ha1 ha2
      have h3 : g₂⁻¹ • a ∈ (g₂⁻¹ * g₁) • B := by
        rw [Set.mem_smul_set_iff_inv_smul_mem, mul_inv_rev, inv_inv, mul_smul, smul_inv_smul]
        exact ha1
      exact Set.disjoint_left.mp h h3 ha2
  rcases hB.smul_eq_or_disjoint t with hE | hD
  · have hpow : ∀ i : ℕ, t ^ i • b ∈ B := by
      intro i
      induction i with
      | zero => simpa using hb
      | succ i ih =>
        rw [pow_succ', mul_smul, ← hE]
        exact Set.smul_mem_smul_set ih
    obtain ⟨h, hhb⟩ := MulAction.exists_smul_eq G b z
    have hne : h • B ≠ B := by
      intro e; apply hz; rw [← e, ← hhb]; exact Set.smul_mem_smul_set hb
    have hdis : Disjoint (h • B) B := by
      have h4 := blk h 1 (by rwa [one_smul])
      rwa [one_smul] at h4
    let f : Fin p ⊕ Fin p → α :=
      Sum.elim (fun i => t ^ (i : ℕ) • b) (fun i => h • (t ^ (i : ℕ) • b))
    have hf : Function.Injective f := by
      rintro (i | i) (j | j) hij
      · simp only [f, Sum.elim_inl] at hij
        exact congrArg Sum.inl (Fin.ext (poc_powSmul_injective t p hp htp b htb i i.2 j j.2 hij))
      · simp only [f, Sum.elim_inl, Sum.elim_inr] at hij
        exact (Set.disjoint_left.mp hdis (Set.smul_mem_smul_set (hpow j))
          (by rw [← hij]; exact hpow i)).elim
      · simp only [f, Sum.elim_inl, Sum.elim_inr] at hij
        exact (Set.disjoint_left.mp hdis (Set.smul_mem_smul_set (hpow i))
          (by rw [hij]; exact hpow j)).elim
      · simp only [f, Sum.elim_inr] at hij
        exact congrArg Sum.inr (Fin.ext (poc_powSmul_injective t p hp htp b htb i i.2 j j.2
          ((smul_left_cancel_iff h).mp hij)))
    have hcd := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_sum, Fintype.card_fin] at hcd
    omega
  · have htB : t • B ≠ B := by
      intro e; rw [e] at hD
      exact Set.disjoint_left.mp hD hb hb
    have hinj := poc_powSmul_injective t p hp htp B htB
    have key : ∀ i j : Fin p, ∀ u v : α, u ∈ B → v ∈ B → t ^ (i : ℕ) • u = t ^ (j : ℕ) • v → i = j := by
      intro i j u v hu hv e
      by_contra hij
      have hne : t ^ (i : ℕ) • B ≠ t ^ (j : ℕ) • B := fun h => hij (Fin.ext (hinj i i.2 j j.2 h))
      exact Set.disjoint_left.mp (blk _ _ hne) (Set.smul_mem_smul_set hu)
        (by rw [e]; exact Set.smul_mem_smul_set hv)
    let f : Fin p ⊕ Fin p → α := Sum.elim (fun i => t ^ (i : ℕ) • b) (fun i => t ^ (i : ℕ) • c)
    have hf : Function.Injective f := by
      rintro (i | i) (j | j) hij
      · simp only [f, Sum.elim_inl] at hij
        have := key i j b b hb hb hij; subst this; rfl
      · simp only [f, Sum.elim_inl, Sum.elim_inr] at hij
        have := key i j b c hb hc hij; subst this
        exact absurd ((smul_left_cancel_iff _).mp hij) hbc
      · simp only [f, Sum.elim_inl, Sum.elim_inr] at hij
        have := key i j c b hc hb hij; subst this
        exact absurd ((smul_left_cancel_iff _).mp hij).symm hbc
      · simp only [f, Sum.elim_inr] at hij
        have := key i j c c hc hc hij; subst this; rfl
    have hcd := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_sum, Fintype.card_fin] at hcd
    omega

end Formalism.GaloisIrreducibility
end

-- bundled from Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.RestrictRoots
section
namespace Formalism.GaloisIrreducibility

open Module Polynomial

section SlopeTestRemainingChoices
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

lemma rr_charpoly_compl (φ : Module.End K V) (P Q : Submodule K V) (hPQ : IsCompl P Q)
    (hP : ∀ x ∈ P, φ x ∈ P) (hQ : ∀ x ∈ Q, φ x ∈ Q) :
    φ.charpoly = (φ.restrict hP).charpoly * (φ.restrict hQ).charpoly := by
  have hconj : (Submodule.prodEquivOfIsCompl P Q hPQ).symm.conj φ = (φ.restrict hP).prodMap (φ.restrict hQ) := by
    apply LinearMap.ext
    rintro ⟨p, q⟩
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_symm, Submodule.coe_prodEquivOfIsCompl', LinearMap.prodMap_apply]
    rw [map_add φ, ← LinearMap.restrict_coe_apply φ hP p, ← LinearMap.restrict_coe_apply φ hQ q,
      map_add, Submodule.prodEquivOfIsCompl_symm_apply_left,
      Submodule.prodEquivOfIsCompl_symm_apply_right]
    simp
  rw [← LinearEquiv.charpoly_conj (Submodule.prodEquivOfIsCompl P Q hPQ).symm φ, hconj, LinearMap.charpoly_prodMap]

lemma rr_roots_of_nilp (B : Module.End K V) (c : K) (h : IsNilpotent (B - c • 1)) :
    B.charpoly.roots = Multiset.replicate (finrank K V) c := by
  have h1 := (LinearMap.isNilpotent_iff_charpoly _).mp h
  rw [LinearMap.charpoly_sub_smul] at h1
  have h2 : B.charpoly = (Polynomial.X - Polynomial.C c) ^ finrank K V := by
    have h3 := congrArg (fun p => p.comp (Polynomial.X - Polynomial.C c)) h1
    simp only [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp,
      sub_add_cancel, Polynomial.comp_X, Polynomial.pow_comp] at h3
    exact h3
  rw [h2, Polynomial.roots_pow, Polynomial.roots_X_sub_C, Multiset.nsmul_singleton]

end SlopeTestRemainingChoices

lemma rr_nilp_pow {R : Type} [Ring R] {K : Type} [Field K] [Algebra K R] (a : R) (c : K)
    (h : IsNilpotent (a - algebraMap K R c)) (q : ℕ) :
    IsNilpotent (a ^ q - algebraMap K R (c ^ q)) := by
  have hc : Commute a (algebraMap K R c) := (Algebra.commutes c a).symm
  rw [map_pow, ← hc.geom_sum₂_mul]
  refine Commute.isNilpotent_mul_left ?_ h
  refine Commute.sum_left _ _ _ fun i _ => ?_
  exact (((Commute.refl a).sub_right hc).pow_left i).mul_left
    ((hc.symm.sub_right (Commute.refl _)).pow_left _)

private lemma coe_restrict_pow_apply' {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (A : Module.End K V) (S : Submodule K V) (hS : ∀ x ∈ S, A x ∈ S) (k : ℕ) (x : S) :
    (((A.restrict hS) ^ k) x : V) = (A ^ k) x := by
  induction k with
  | zero => simp
  | succ k ihk =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply,
      LinearMap.restrict_coe_apply, ihk]

lemma rr_roots_pow {K : Type} [Field K] [IsAlgClosed K] (q : ℕ) : ∀ (n : ℕ) (V : Type)
    [AddCommGroup V] [Module K V] [FiniteDimensional K V],
    finrank K V = n → ∀ (A : Module.End K V),
      (A ^ q).charpoly.roots = A.charpoly.roots.map (· ^ q) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn A
  have hinv : ∀ (S : Submodule K V) (hS : ∀ x ∈ S, A x ∈ S) (hSq : ∀ x ∈ S, (A ^ q) x ∈ S),
      (A ^ q).restrict hSq = (A.restrict hS) ^ q := by
    intro S hS hSq
    ext x
    rw [LinearMap.restrict_coe_apply, coe_restrict_pow_apply']
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  ·
    have hsub : Subsingleton V := Module.finrank_zero_iff.mp (hn.trans hn0)
    have hnil : ∀ B : Module.End K V, B.charpoly = 1 := by
      intro B
      have hB : IsNilpotent B := ⟨1, LinearMap.ext fun x => Subsingleton.elim _ _⟩
      rw [(LinearMap.isNilpotent_iff_charpoly B).mp hB, hn, hn0, pow_zero]
    simp [hnil]
  · haveI : Nontrivial V := Module.finrank_pos_iff.mp (hn ▸ hnpos)
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue A
    obtain ⟨f, hf⟩ : ∃ f : Module.End K V, f = A - μ • 1 := ⟨_, rfl⟩
    obtain ⟨N0, hN0⟩ :=
      Filter.eventually_atTop.mp (LinearMap.eventually_isCompl_ker_pow_range_pow f)
    have hPQ := hN0 (N0 + 1) (Nat.le_succ _)

    have hcomm : ∀ g : Module.End K V, Commute g f →
        (∀ x ∈ LinearMap.ker (f ^ (N0 + 1)), g x ∈ LinearMap.ker (f ^ (N0 + 1))) ∧ (∀ x ∈ LinearMap.range (f ^ (N0 + 1)), g x ∈ LinearMap.range (f ^ (N0 + 1))) := by
      intro g hg
      have hgN := (hg.pow_right (N0 + 1)).eq
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rw [LinearMap.mem_ker] at hx ⊢
        rw [← Module.End.mul_apply, ← hgN, Module.End.mul_apply, hx, map_zero]
      · obtain ⟨y, rfl⟩ := hx
        exact ⟨g y, by rw [← Module.End.mul_apply, ← hgN, Module.End.mul_apply]⟩
    have hAf : Commute A f := by
      rw [hf]
      exact (Commute.refl A).sub_right ((Commute.one_right A).smul_right μ)
    obtain ⟨hP, hQ⟩ := hcomm A hAf
    obtain ⟨hPq, hQq⟩ := hcomm (A ^ q) (hAf.pow_left q)
    by_cases hQb : LinearMap.range (f ^ (N0 + 1)) = ⊥
    ·
      have hPt : LinearMap.ker (f ^ (N0 + 1)) = ⊤ := by
        have h := hPQ.sup_eq_top
        rwa [hQb, sup_bot_eq] at h
      have hnil : IsNilpotent f := ⟨N0 + 1, LinearMap.ker_eq_top.mp hPt⟩
      rw [hf] at hnil
      have hnilq : IsNilpotent (A ^ q - (μ ^ q) • 1) := by
        have h := rr_nilp_pow A μ (by rw [Algebra.algebraMap_eq_smul_one]; exact hnil) q
        rwa [Algebra.algebraMap_eq_smul_one] at h
      rw [rr_roots_of_nilp A μ hnil, rr_roots_of_nilp (A ^ q) (μ ^ q) hnilq, Multiset.map_replicate]
    ·
      have hPb : LinearMap.ker (f ^ (N0 + 1)) ≠ ⊥ := by
        intro hPb
        obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
        apply hv.2
        have hfv : f v = 0 := by
          rw [hf, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
            hv.apply_eq_smul, sub_self]
        have hvP : v ∈ LinearMap.ker (f ^ (N0 + 1)) := by
          rw [LinearMap.mem_ker, pow_succ, Module.End.mul_apply, hfv, map_zero]
        rw [hPb] at hvP
        exact (Submodule.mem_bot K).mp hvP
      have hdim := Submodule.finrank_add_eq_of_isCompl hPQ
      have hP0 : finrank K (LinearMap.ker (f ^ (N0 + 1))) ≠ 0 := fun h => hPb (Submodule.finrank_eq_zero.mp h)
      have hQ0 : finrank K (LinearMap.range (f ^ (N0 + 1))) ≠ 0 := fun h => hQb (Submodule.finrank_eq_zero.mp h)
      have ihP := ih _ (by omega) (LinearMap.ker (f ^ (N0 + 1))) rfl (A.restrict hP)
      have ihQ := ih _ (by omega) (LinearMap.range (f ^ (N0 + 1))) rfl (A.restrict hQ)
      have hne : ∀ (S : Submodule K V) (B : Module.End K S), B.charpoly ≠ 0 :=
        fun S B => (LinearMap.charpoly_monic B).ne_zero
      rw [rr_charpoly_compl (A ^ q) _ _ hPQ hPq hQq, rr_charpoly_compl A _ _ hPQ hP hQ,
        Polynomial.roots_mul (mul_ne_zero (hne _ _) (hne _ _)),
        Polynomial.roots_mul (mul_ne_zero (hne _ _) (hne _ _)),
        hinv _ hP hPq, hinv _ hQ hQq, ihP, ihQ, Multiset.map_add]

private lemma charpoly_restrict_dvd_charpoly {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (τ : Module.End K V) (W : Submodule K V) (hτ : ∀ v ∈ W, τ v ∈ W) :
    (τ.restrict hτ).charpoly ∣ τ.charpoly := by
  classical
  obtain ⟨Q, hWQ⟩ := Submodule.exists_isCompl W
  obtain ⟨e, he⟩ : ∃ e : (W × Q) ≃ₗ[K] V, e = Submodule.prodEquivOfIsCompl W Q hWQ := ⟨_, rfl⟩
  have he1 : ∀ x : W, e.symm (x : V) = (x, 0) := fun x => by
    rw [he]; exact Submodule.prodEquivOfIsCompl_symm_apply_left W Q hWQ x
  have he2 : ∀ x : W, e (x, 0) = (x : V) := fun x => by
    rw [← he1 x, LinearEquiv.apply_symm_apply]
  have bW := Module.finBasis K W
  have bQ := Module.finBasis K Q
  have key : ∀ j, (e.symm.conj τ) ((bW.prod bQ) (Sum.inl j)) = ((τ.restrict hτ) (bW j), 0) := by
    intro j
    have hb : (bW.prod bQ) (Sum.inl j) = (bW j, 0) := by simp [Module.Basis.prod_apply]
    rw [hb, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, LinearEquiv.symm_symm, he2, ← LinearMap.restrict_coe_apply τ hτ, he1]
  have h21 : (LinearMap.toMatrix (bW.prod bQ) (bW.prod bQ) (e.symm.conj τ)).toBlocks₂₁ = 0 := by
    ext i j
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply, LinearMap.toMatrix_apply, key,
      Module.Basis.prod_repr_inr, map_zero, Finsupp.coe_zero, Pi.zero_apply]
  have h11 : (LinearMap.toMatrix (bW.prod bQ) (bW.prod bQ) (e.symm.conj τ)).toBlocks₁₁ =
      LinearMap.toMatrix bW bW (τ.restrict hτ) := by
    ext i j
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, LinearMap.toMatrix_apply, key,
      Module.Basis.prod_repr_inl]
  rw [← LinearEquiv.charpoly_conj e.symm τ, ← LinearMap.charpoly_toMatrix (e.symm.conj τ) (bW.prod bQ),
    ← LinearMap.charpoly_toMatrix (τ.restrict hτ) bW,
    ← Matrix.fromBlocks_toBlocks (LinearMap.toMatrix (bW.prod bQ) (bW.prod bQ) (e.symm.conj τ)),
    h21, h11, Matrix.charpoly_fromBlocks_zero₂₁]
  exact dvd_mul_right _ _

theorem restrict_roots_to_subfield : RestrictRoots := by
  unfold RestrictRoots
  intro K V _ _ _ _ _ τ F q hF W hτ hFW
  have hFW' : ∀ v ∈ W, (F : V →ₗ[K] V) v ∈ W := hFW
  have hinj : Function.Injective ((F : V →ₗ[K] V).restrict hFW') := by
    intro x y hxy
    apply Subtype.ext
    apply F.injective
    have h := congrArg Subtype.val hxy
    simpa only [LinearMap.restrict_coe_apply, LinearEquiv.coe_coe] using h
  have hbij : Function.Bijective ((F : V →ₗ[K] V).restrict hFW') :=
    ⟨hinj, LinearMap.surjective_of_injective hinj⟩
  obtain ⟨eW, heW⟩ : ∃ eW : W ≃ₗ[K] W, ∀ x, eW x = ((F : V →ₗ[K] V).restrict hFW') x :=
    ⟨LinearEquiv.ofBijective _ hbij, fun x => rfl⟩
  have hconj : eW.conj (τ.restrict hτ) = (τ.restrict hτ) ^ q := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := eW.surjective x
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    simp only [heW, LinearMap.restrict_coe_apply, coe_restrict_pow_apply', LinearEquiv.coe_coe]
    exact hF y
  constructor
  · exact Polynomial.roots.le_of_dvd (LinearMap.charpoly_monic τ).ne_zero
      (charpoly_restrict_dvd_charpoly τ W hτ)
  · have h1 := rr_roots_pow q (finrank K W) W rfl (τ.restrict hτ)
    rw [← hconj, LinearEquiv.charpoly_conj] at h1
    exact h1.symm

end Formalism.GaloisIrreducibility
end

