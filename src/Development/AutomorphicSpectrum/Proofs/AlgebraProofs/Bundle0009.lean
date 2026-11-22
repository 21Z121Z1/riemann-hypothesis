import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEqNsmulOfForallDvdOfBijective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SaturatedLatticeQuotientCount
section
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem mem_of_forall_exists_sub_eq_nsmul (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    (W : Submodule ℤ Λ) (hW : ∀ (k : ℤ) x, k ≠ 0 → k • x ∈ W → x ∈ W) (x : Λ)
    (h : ∀ N : ℕ, 0 < N → ∃ w ∈ W, ∃ b : Λ, x - w = N • b) : x ∈ W := by
  have htf : Module.IsTorsionFree ℤ (Λ ⧸ W) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m hrm => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective W m
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hrm
      exact (Submodule.Quotient.mk_eq_zero W).mpr (hW r y hr hrm)
  have hfree : Module.Free ℤ (Λ ⧸ W) := Module.free_iff_isTorsionFree.mpr htf
  let bs := Module.Free.chooseBasis ℤ (Λ ⧸ W)
  rw [← Submodule.Quotient.mk_eq_zero W]
  refine bs.repr.injective ?_
  rw [map_zero]
  ext i
  rw [Finsupp.zero_apply]
  obtain ⟨w, hw, b, hb⟩ := h ((bs.repr (Submodule.Quotient.mk x) i).natAbs + 1) (by omega)
  generalize hn : (bs.repr (Submodule.Quotient.mk x) i).natAbs = n at hb
  have hq : (Submodule.Quotient.mk x : Λ ⧸ W) = (n + 1) • Submodule.Quotient.mk b := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← hb]
    simpa using hw
  have hc : bs.repr (Submodule.Quotient.mk x) i =
      ((n + 1 : ℕ) : ℤ) * bs.repr (Submodule.Quotient.mk b) i := by
    rw [hq, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  have habs := congrArg Int.natAbs hc
  rw [Int.natAbs_mul, Int.natAbs_natCast, hn] at habs
  rcases Nat.eq_zero_or_pos (bs.repr (Submodule.Quotient.mk b) i).natAbs with ht | ht
  · rw [ht, mul_zero] at habs
    rw [habs] at hn
    exact Int.natAbs_eq_zero.mp hn
  · nlinarith

theorem mem_of_forall_card_mul_eq_pow :
    ∀ (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
      (B : LinearMap.BilinForm ℤ Λ), Function.Bijective B → (∀ x, B x x = 0) →
      ∀ W : Submodule ℤ Λ, (∀ (k : ℤ) x, k ≠ 0 → k • x ∈ W → x ∈ W) →
      (∀ N : ℕ, 0 < N →
        ∃ T : Set (W ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : W →ₗ[ℤ] W))),
          Nat.card (W ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : W →ₗ[ℤ] W))) * Nat.card T
            = N ^ Module.finrank ℤ Λ ∧
          ∀ x y : W, Submodule.Quotient.mk x ∈ T → (N : ℤ) ∣ B x y) →
      ∀ x, (∀ y ∈ W, B x y = 0) → x ∈ W := by
  intro Λ _ _ _ B hB halt W hW hT x hx
  apply mem_of_forall_exists_sub_eq_nsmul Λ W hW x
  intro N hN
  obtain ⟨T, hcard, hTpair⟩ := hT N hN
  let R : Λ → (W ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : W →ₗ[ℤ] W))) → Prop :=
    fun a p => ∃ w : W, Submodule.Quotient.mk w = p ∧ ∃ b : Λ, a - w = N • b
  have h1 : ∀ a b p, R a p → R (a + N • b) p := by
    rintro a b p ⟨w, hw, b0, hb0⟩
    refine ⟨w, hw, b0 + b, ?_⟩
    rw [smul_add, ← hb0]
    abel
  have h2 : ∀ a p p', R a p → R a p' → p = p' := by
    rintro a p p' ⟨w, rfl, b, hb⟩ ⟨w', rfl, b', hb'⟩
    have hdiff : ((w : Λ) - w') = (N : ℤ) • (b' - b) := by
      rw [natCast_zsmul, smul_sub, ← hb, ← hb']
      abel
    have hmem : b' - b ∈ W :=
      hW (N : ℤ) (b' - b) (by exact_mod_cast hN.ne') (by rw [← hdiff]; exact W.sub_mem w.2 w'.2)
    rw [Submodule.Quotient.eq]
    refine ⟨⟨b' - b, hmem⟩, ?_⟩
    apply Subtype.ext
    exact hdiff.symm
  have h3 : ∀ p, ∃ a, R a p := by
    intro p
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ p
    exact ⟨w, w, rfl, 0, by simp⟩
  have h4 : ∀ a p a' p', R a p → p ∈ T → R a' p' → (N : ℤ) ∣ B a a' := by
    rintro a p a' p' ⟨w, rfl, b, hb⟩ hp ⟨w', -, b', hb'⟩
    have ha : a = w + N • b := by rw [← hb]; abel
    have ha' : a' = w' + N • b' := by rw [← hb']; abel
    have hww := hTpair w w' hp
    have hexp : B (↑w + N • b) (↑w' + N • b') = B w w' + N * (B w b' + B b w' + N * B b b') := by
      simp only [map_add, LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      ring
    rw [ha, ha', hexp]
    exact dvd_add hww (dvd_mul_right _ _)
  have h5 : ∀ a' p', R a' p' → (N : ℤ) ∣ B x a' := by
    rintro a' p' ⟨w', -, b', hb'⟩
    have ha' : a' = w' + N • b' := by rw [← hb']; abel
    rw [ha', map_add, map_nsmul, hx w' w'.2, zero_add]
    exact ⟨B x b', nsmul_eq_mul _ _⟩
  obtain ⟨p, w, -, b, hwb⟩ :=
    GlobalTheory.exists_rel_of_forall_dvd_of_card_mul Λ B hB N hN _ T R h1 h2 h3 hcard h4 x h5
  exact ⟨w, w.2, b, hwb⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SmulMemSpanOver
section
namespace GlobalTheory.CompanionTheory.Ar.Num.SpanExact

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω]
  {E E₂ : Type*} [AddCommGroup E] [Module Ω E] [AddCommGroup E₂] [Module Ω E₂]

theorem smul_mem_spanOver (R : Subalgebra o Ω) (S : Set E) {a : Ω} (ha : a ∈ R) {v : E}
    (hv : v ∈ spanOver R S) : a • v ∈ spanOver R S := by
  unfold spanOver at hv ⊢
  induction hv using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, e, he, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a * b, R.mul_mem ha hb, e, he, by rw [mul_smul]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem map_spanOver (R : Subalgebra o Ω) (S : Set E) (q : E →ₗ[Ω] E₂) :
    (spanOver R S).map q.toAddMonoidHom = spanOver R (q '' S) := by
  unfold spanOver
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨v, ⟨a, ha, e, he, rfl⟩, rfl⟩
    exact ⟨a, ha, q e, ⟨e, he, rfl⟩, by simp⟩
  · rintro ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨a • e, ⟨a, ha, e, he, rfl⟩, by simp⟩

theorem local_step (R R₁ : Subalgebra o Ω) (hR : R ≤ R₁) (q : E →ₗ[Ω] E₂) (L : AddSubgroup E)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {r : ℕ} (f : Ω) (hf : f ∈ R) (b : Fin r → E₂)
    (hb : LinearIndependent Ω b) (hsp : Submodule.span Ω (Set.range b) = ⊤)
    (hloc : ∀ e, (∃ n : ℕ, f ^ n • e ∈ L.map q.toAddMonoidHom) ↔
        ∃ a : Fin r → Ω, (∀ j, ∃ n : ℕ, f ^ n * a j ∈ R) ∧ e = ∑ j, a j • b j)
    {v : E} (hv : v ∈ spanOver R₁ (L : Set E)) (hq : q v = 0) :
    ∃ m : ℕ, f ^ m • v ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0} := by
  classical
  have h1 : ∀ j, ∃ n : ℕ, ∃ s ∈ L, q s = f ^ n • b j := by
    intro j
    obtain ⟨n, s, hs, hs'⟩ := (hloc (b j)).2 ⟨Pi.single j 1, fun k => ⟨0, by
      by_cases h : k = j
      · subst h; simpa using R.one_mem
      · simpa [h] using R.zero_mem⟩, by simp [Pi.single_apply]⟩
    exact ⟨n, s, hs, hs'⟩
  choose n s hs hqs using h1
  set N := ∑ j, n j with hN
  have hle : ∀ j, n j ≤ N := fun j =>
    Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  let t : Fin r → E := fun j => f ^ (N - n j) • s j
  have ht : ∀ j, t j ∈ L := fun j => hL _ (R.pow_mem hf _) _ (hs j)
  have hqt : ∀ j, q (t j) = f ^ N • b j := fun j => by
    simp only [t, map_smul, hqs, smul_smul, ← pow_add, Nat.sub_add_cancel (hle j)]
  let B : Module.Basis (Fin r) Ω E₂ := Module.Basis.mk hb hsp.ge
  let σ : E₂ →ₗ[Ω] E := B.constr Ω t
  have hσ : ∀ j, σ (b j) = t j := fun j => by
    have : b j = B j := by simp [B]
    rw [this]; simp [σ]
  set S := spanOver R₁ {e | e ∈ L ∧ q e = 0} with hS
  have hup : ∀ (w : E) (m k : ℕ), f ^ m • w ∈ S → f ^ (k + m) • w ∈ S := fun w m k h => by
    rw [pow_add, mul_smul]
    exact smul_mem_spanOver R₁ _ (R₁.pow_mem (hR hf) _) h
  have key : ∃ m : ℕ, f ^ m • (f ^ N • v - σ (q v)) ∈ S := by
    clear hq
    unfold spanOver at hv
    induction hv using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, e, he, rfl⟩ := hx
      obtain ⟨c, hc, hce⟩ := (hloc (q e)).1 ⟨0, e, he, by simp⟩
      choose p hp using hc
      set M := ∑ j, p j with hM
      have hle' : ∀ j, p j ≤ M := fun j =>
        Finset.single_le_sum (f := p) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have hp' : ∀ j, f ^ M * c j ∈ R := fun j => by
        rw [← Nat.sub_add_cancel (hle' j), pow_add, mul_assoc]
        exact R.mul_mem (R.pow_mem hf _) (hp j)
      refine ⟨M, AddSubgroup.subset_closure ⟨a, ha, f ^ M • (f ^ N • e - σ (q e)), ⟨?_, ?_⟩, ?_⟩⟩
      · rw [smul_sub]
        refine sub_mem (hL _ (R.pow_mem hf _) _ (hL _ (R.pow_mem hf _) _ he)) ?_
        rw [hce, map_sum, Finset.smul_sum]
        refine sum_mem fun j _ => ?_
        rw [map_smul, smul_smul, hσ]
        exact hL _ (hp' j) _ (ht j)
      · rw [map_smul, map_sub, map_smul, hce, map_sum, map_sum, Finset.smul_sum]
        simp only [map_smul, hσ, hqt]
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_zero, smul_zero]
        intro j _
        rw [smul_comm, sub_self]
      · simp only [map_smul]
        module
    | zero => exact ⟨0, by simpa using S.zero_mem⟩
    | add x y _ _ hx hy =>
      obtain ⟨m, hm⟩ := hx
      obtain ⟨k, hk⟩ := hy
      refine ⟨k + m, ?_⟩
      have h2 := hup _ _ m hk
      rw [add_comm] at h2
      convert add_mem (hup _ _ k hm) h2 using 1
      simp only [map_add]
      module
    | neg x _ hx =>
      obtain ⟨m, hm⟩ := hx
      refine ⟨m, ?_⟩
      convert neg_mem hm using 1
      simp only [map_neg]
      module
  obtain ⟨m, hm⟩ := key
  refine ⟨m + N, ?_⟩
  simpa [hq, smul_smul, pow_add] using hm

theorem mem_spanOver_ker (R R₁ : Subalgebra o Ω) (hR : R ≤ R₁) (q : E →ₗ[Ω] E₂) (L : AddSubgroup E)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {r : ℕ} (hF : LocFree R r (L.map q.toAddMonoidHom))
    {v : E} (hv : v ∈ spanOver R₁ (L : Set E)) (hq : q v = 0) :
    v ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0} := by
  obtain ⟨-, k, f, c, hf, hc, hsum, hl⟩ := hF
  let J : Ideal R :=
    { carrier := {a | (a : Ω) • v ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0}}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, Subalgebra.coe_add, add_smul] at ha hb ⊢
        exact add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun a b hb => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, MulMemClass.coe_mul, mul_smul] at hb ⊢
        exact smul_mem_spanOver R₁ _ (hR a.2) hb }
  have h1 : (1 : R) ∈ J.radical := by
    have : (1 : R) = ∑ l, (⟨c l, hc l⟩ : R) * ⟨f l, hf l⟩ := by
      apply Subtype.ext
      simp [hsum]
    rw [this]
    refine sum_mem fun l _ => Ideal.mul_mem_left _ _ ?_
    obtain ⟨b, hb, hsp, hloc⟩ := hl l
    obtain ⟨m, hm⟩ := local_step R R₁ hR q L hL (f l) (hf l) b hb hsp hloc hv hq
    exact ⟨m, hm⟩
  obtain ⟨m, hm⟩ := h1
  have : ((1 ^ m : R) : Ω) • v ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0} := hm
  simpa using this

theorem span_comap_exact : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R R₁ : Subalgebra o Ω), R ≤ R₁ → ∀ {E E₁ E₂ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] [AddCommGroup E₂] [Module Ω E₂] (i : E₁ →ₗ[Ω] E) (q : E →ₗ[Ω] E₂), Function.Injective i → LinearMap.range i = LinearMap.ker q → ∀ (L : AddSubgroup E) (r₂ : ℕ), (∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) → LocFree R r₂ (L.map q.toAddMonoidHom) → (spanOver R₁ (L : Set E)).comap i.toAddMonoidHom = spanOver R₁ (L.comap i.toAddMonoidHom : Set E₁) ∧ (spanOver R₁ (L : Set E)).map q.toAddMonoidHom = spanOver R₁ (L.map q.toAddMonoidHom : Set E₂) := by
  intro o Ω _ _ _ R R₁ hR E E₁ E₂ _ _ _ _ _ _ i q hi hex L r₂ hL hF
  refine ⟨?_, ?_⟩
  · have himg : i '' (L.comap i.toAddMonoidHom : Set E₁) = {e | e ∈ L ∧ q e = 0} := by
      ext e
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx, by rw [← LinearMap.mem_ker, ← hex]; exact ⟨x, rfl⟩⟩
      · rintro ⟨he, hq⟩
        rw [← LinearMap.mem_ker, ← hex] at hq
        obtain ⟨x, rfl⟩ := hq
        exact ⟨x, he, rfl⟩
    have hmap := map_spanOver R₁ (L.comap i.toAddMonoidHom : Set E₁) i
    rw [himg] at hmap
    ext x
    constructor
    · intro hx
      have hq : q (i x) = 0 := by rw [← LinearMap.mem_ker, ← hex]; exact ⟨x, rfl⟩
      have := mem_spanOver_ker R R₁ hR q L hL hF (v := i x) hx hq
      rw [← hmap] at this
      obtain ⟨y, hy, hxy⟩ := this
      obtain rfl : y = x := hi hxy
      exact hy
    · intro hx
      have h1 : i x ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0} := by
        rw [← hmap]; exact ⟨x, hx, rfl⟩
      have h2 : spanOver R₁ {e | e ∈ L ∧ q e = 0} ≤ spanOver R₁ (L : Set E) :=
        AddSubgroup.closure_mono fun w ⟨a, ha, e, he, hw⟩ => ⟨a, ha, e, he.1, hw⟩
      exact h2 h1
  · rw [map_spanOver, AddSubgroup.coe_map]
    rfl

end GlobalTheory.CompanionTheory.Ar.Num.SpanExact
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SumMemLoc
section
namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeExt

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω]

section One

variable {E : Type*} [AddCommGroup E] [Module Ω E]

def loc (R : Subalgebra o Ω) (f : Ω) (hf : f ∈ R) (L : AddSubgroup E)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) : AddSubgroup E where
  carrier := {e | ∃ n : ℕ, f ^ n • e ∈ L}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [pow_add, mul_comm, mul_smul]; exact hL _ (R.pow_mem hf _) _ hn
    · rw [pow_add, mul_smul]; exact hL _ (R.pow_mem hf _) _ hm
  neg_mem' := by
    rintro x ⟨n, hn⟩
    exact ⟨n, by rw [smul_neg]; exact L.neg_mem hn⟩

theorem mem_loc {R : Subalgebra o Ω} {f : Ω} {hf : f ∈ R} {L : AddSubgroup E}
    {hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L} {e : E} :
    e ∈ loc R f hf L hL ↔ ∃ n : ℕ, f ^ n • e ∈ L := Iff.rfl

theorem sum_mem_loc {R : Subalgebra o Ω} {f : Ω} (hf : f ∈ R) {L : AddSubgroup E}
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {r : ℕ} (a : Fin r → Ω) (b : Fin r → E)
    (ha : ∀ q, ∃ n : ℕ, f ^ n * a q ∈ R) (hb : ∀ q, ∃ n : ℕ, f ^ n • b q ∈ L) :
    ∃ n : ℕ, f ^ n • (∑ q, a q • b q) ∈ L := by
  rw [← mem_loc (hf := hf) (hL := hL)]
  refine AddSubgroup.sum_mem _ fun q _ => ?_
  obtain ⟨n, hn⟩ := ha q
  obtain ⟨m, hm⟩ := hb q
  refine ⟨n + m, ?_⟩
  have h := hL _ hn _ hm
  rw [smul_smul] at h
  rw [smul_smul]
  convert h using 2
  ring

def FreeOn (R : Subalgebra o Ω) (f : Ω) (L : AddSubgroup E) {r : ℕ} (b : Fin r → E) : Prop :=
  LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
    ∀ e, (∃ n : ℕ, f ^ n • e ∈ L) ↔
      ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q

theorem FreeOn.basis_mem {R : Subalgebra o Ω} {f : Ω} {L : AddSubgroup E} {r : ℕ} {b : Fin r → E}
    (h : FreeOn R f L b) (q : Fin r) : ∃ n : ℕ, f ^ n • b q ∈ L := by
  classical
  refine (h.2.2 _).2 ⟨Pi.single q 1, fun p => ⟨0, ?_⟩, ?_⟩
  · by_cases hp : p = q
    · subst hp; simp
    · simp [Pi.single_eq_of_ne hp]
  · simp [Pi.single_apply, ite_smul]

theorem exists_coord {r : ℕ} {b : Fin r → E} (h : Submodule.span Ω (Set.range b) = ⊤) (e : E) :
    ∃ a : Fin r → Ω, e = ∑ q, a q • b q := by
  have he : e ∈ Submodule.span Ω (Set.range b) := h ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 he
  exact ⟨a, ha.symm⟩

theorem FreeOn.mul {R : Subalgebra o Ω} {f g : Ω} (hf : f ∈ R) (hg : g ∈ R) {L : AddSubgroup E}
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {r : ℕ} {b : Fin r → E}
    (h : FreeOn R f L b) : FreeOn R (f * g) L b := by
  refine ⟨h.1, h.2.1, fun e => ⟨?_, ?_⟩⟩
  · rintro ⟨n, hn⟩
    by_cases hg0 : g = 0
    · obtain ⟨a, ha⟩ := exists_coord h.2.1 e
      exact ⟨a, fun q => ⟨1, by simp [hg0]⟩, ha⟩
    · rw [mul_pow, mul_smul] at hn
      obtain ⟨a, ha, he⟩ := (h.2.2 _).1 ⟨n, hn⟩
      refine ⟨fun q => (g ^ n)⁻¹ * a q, fun q => ?_, ?_⟩
      · obtain ⟨m, hm⟩ := ha q
        refine ⟨n + m, ?_⟩
        have h1 := R.mul_mem (R.mul_mem (R.pow_mem hf n) (R.pow_mem hg m)) hm
        convert h1 using 1
        have : g ^ n ≠ 0 := pow_ne_zero _ hg0
        field_simp
        ring
      · simp only [mul_smul]
        rw [← Finset.smul_sum, ← he, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hg0), one_smul]
  · rintro ⟨a, ha, rfl⟩
    refine sum_mem_loc (R.mul_mem hf hg) hL a b ha fun q => ?_
    obtain ⟨n, hn⟩ := h.basis_mem q
    refine ⟨n, ?_⟩
    rw [mul_pow, mul_comm, mul_smul]
    exact hL _ (R.pow_mem hg _) _ hn

end One

variable {E E₁ E₂ : Type*} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁]
  [AddCommGroup E₂] [Module Ω E₂]

theorem freeOn_ext {R : Subalgebra o Ω} {f : Ω} (hf : f ∈ R) (i : E₁ →ₗ[Ω] E) (q : E →ₗ[Ω] E₂)
    (hi : Function.Injective i) (hq : Function.Surjective q)
    (hiq : LinearMap.range i = LinearMap.ker q) {L : AddSubgroup E}
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {r₁ r₂ : ℕ} {b₁ : Fin r₁ → E₁} {b₂ : Fin r₂ → E₂}
    (h₁ : FreeOn R f (L.comap i.toAddMonoidHom) b₁) (h₂ : FreeOn R f (L.map q.toAddMonoidHom) b₂) :
    ∃ b : Fin (r₁ + r₂) → E, FreeOn R f L b := by
  have hlift : ∀ p, ∃ t : E, q t = b₂ p ∧ ∃ n : ℕ, f ^ n • t ∈ L := by
    intro p
    by_cases hf0 : f = 0
    · obtain ⟨t, ht⟩ := hq (b₂ p)
      exact ⟨t, ht, 1, by simp [hf0]⟩
    · obtain ⟨n, s, hs, hs'⟩ := h₂.basis_mem p
      have hs'' : q s = f ^ n • b₂ p := hs'
      refine ⟨(f ^ n)⁻¹ • s, ?_, n, ?_⟩
      · rw [map_smul, hs'', smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hf0), one_smul]
      · rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hf0), one_smul]; exact hs
  choose t ht htL using hlift
  have hqi : ∀ x, q (i x) = 0 := fun x => by
    have : i x ∈ LinearMap.ker q := hiq ▸ LinearMap.mem_range_self i x
    exact this
  have hsum : ∀ (a₁ : Fin r₁ → Ω) (a₂ : Fin r₂ → Ω),
      ∑ p, Fin.append a₁ a₂ p • Fin.append (fun p => i (b₁ p)) t p
        = i (∑ p, a₁ p • b₁ p) + ∑ p, a₂ p • t p := by
    intro a₁ a₂
    rw [Fin.sum_univ_add]
    simp [map_sum]
  have hker : ∀ (e : E) (a₂ : Fin r₂ → Ω), q e = ∑ p, a₂ p • b₂ p →
      ∃ x, i x = e - ∑ p, a₂ p • t p := by
    intro e a₂ he
    have : e - ∑ p, a₂ p • t p ∈ LinearMap.range i := by
      rw [hiq, LinearMap.mem_ker, map_sub, he]
      simp [map_sum, ht]
    exact this
  refine ⟨Fin.append (fun p => i (b₁ p)) t, ?_, ?_, fun e => ⟨?_, ?_⟩⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_add] at hg
    simp only [Fin.append_left, Fin.append_right] at hg
    have h2 : ∑ p, g (Fin.natAdd r₁ p) • b₂ p = 0 := by
      have := congrArg q hg
      simpa [map_sum, hqi, ht] using this
    have h2' := Fintype.linearIndependent_iff.1 h₂.1 _ h2
    have h1 : ∑ p, g (Fin.castAdd r₂ p) • b₁ p = 0 := by
      apply hi
      simpa [map_sum, h2'] using hg
    have h1' := Fintype.linearIndependent_iff.1 h₁.1 _ h1
    intro p
    refine Fin.addCases (fun p => h1' p) (fun p => h2' p) p
  · rw [eq_top_iff]
    intro e _
    obtain ⟨a₂, ha₂⟩ := exists_coord h₂.2.1 (q e)
    obtain ⟨x, hx⟩ := hker e a₂ ha₂
    obtain ⟨a₁, ha₁⟩ := exists_coord h₁.2.1 x
    refine (Submodule.mem_span_range_iff_exists_fun Ω).2 ⟨Fin.append a₁ a₂, ?_⟩
    rw [hsum, ← ha₁, hx, sub_add_cancel]
  · rintro ⟨n, hn⟩
    obtain ⟨a₂, ha₂R, ha₂⟩ := (h₂.2.2 (q e)).1 ⟨n, f ^ n • e, hn, by simp⟩
    obtain ⟨x, hx⟩ := hker e a₂ ha₂
    have hxL : i x ∈ loc R f hf L hL := by
      rw [hx]
      exact AddSubgroup.sub_mem _ ⟨n, hn⟩ (sum_mem_loc hf hL a₂ t ha₂R htL)
    obtain ⟨m, hm⟩ := hxL
    obtain ⟨a₁, ha₁R, ha₁⟩ := (h₁.2.2 x).1 ⟨m, by
      rw [AddSubgroup.mem_comap]; simpa using hm⟩
    refine ⟨Fin.append a₁ a₂, fun p => ?_, ?_⟩
    · refine Fin.addCases (fun p => ?_) (fun p => ?_) p
      · simpa using ha₁R p
      · simpa using ha₂R p
    · rw [hsum, ← ha₁, hx, sub_add_cancel]
  · rintro ⟨a, ha, rfl⟩
    refine sum_mem_loc hf hL a _ ha fun p => ?_
    refine Fin.addCases (fun p => ?_) (fun p => ?_) p
    · obtain ⟨n, hn⟩ := h₁.basis_mem p
      rw [AddSubgroup.mem_comap] at hn
      exact ⟨n, by simpa using hn⟩
    · simpa using htL p

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E E₁ E₂ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] [AddCommGroup E₂] [Module Ω E₂] (i : E₁ →ₗ[Ω] E) (q : E →ₗ[Ω] E₂), Function.Injective i → Function.Surjective q → LinearMap.range i = LinearMap.ker q → ∀ (L : AddSubgroup E) (r₁ r₂ : ℕ), (∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) → LocFree R r₁ (L.comap i.toAddMonoidHom) → LocFree R r₂ (L.map q.toAddMonoidHom) → LocFree R (r₁ + r₂) L := by
  intro o Ω _ _ _ R E E₁ E₂ _ _ _ _ _ _ i q hi hq hiq L r₁ r₂ hL
  rintro ⟨hL₁, k₁, f₁, c₁, hf₁, hc₁, hs₁, hb₁⟩ ⟨hL₂, k₂, f₂, c₂, hf₂, hc₂, hs₂, hb₂⟩
  refine ⟨hL, k₁ * k₂,
    fun l => f₁ (finProdFinEquiv.symm l).1 * f₂ (finProdFinEquiv.symm l).2,
    fun l => c₁ (finProdFinEquiv.symm l).1 * c₂ (finProdFinEquiv.symm l).2,
    fun l => R.mul_mem (hf₁ _) (hf₂ _), fun l => R.mul_mem (hc₁ _) (hc₂ _), ?_, fun l => ?_⟩
  · rw [Equiv.sum_comp finProdFinEquiv.symm
      (fun p : Fin k₁ × Fin k₂ => c₁ p.1 * c₂ p.2 * (f₁ p.1 * f₂ p.2)), Fintype.sum_prod_type,
      ← mul_one (1 : Ω)]
    conv_rhs => rw [← hs₁]; enter [2]; rw [hs₁, ← hs₂]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  · obtain ⟨b₁, h₁⟩ := hb₁ (finProdFinEquiv.symm l).1
    obtain ⟨b₂, h₂⟩ := hb₂ (finProdFinEquiv.symm l).2
    have h₁' := FreeOn.mul (hf₁ _) (hf₂ (finProdFinEquiv.symm l).2) hL₁ h₁
    have h₂' := FreeOn.mul (hf₂ _) (hf₁ (finProdFinEquiv.symm l).1) hL₂ h₂
    rw [mul_comm] at h₂'
    exact freeOn_ext (R.mul_mem (hf₁ _) (hf₂ _)) i q hi hq hiq hL h₁' h₂'

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeExt
end

