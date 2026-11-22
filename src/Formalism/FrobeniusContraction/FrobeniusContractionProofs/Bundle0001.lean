import Formalism.FrobeniusContraction.Bundle0001

-- bundled from Formalism.FrobeniusContraction.FrobeniusContractionProofs.CocycleComponentRelation
section
namespace Formalism.WachCohomologyFacts.PExt

open Formalism.WachCohomologyFacts

variable {O A AA : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
  [Algebra A AA] [IsScalarTower O A AA]
variable {V : Type} [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V]
  [Module O V] [IsScalarTower O AA V]

def extMap (f : V →ₗ[O] V) (g : AA →ₐ[O] AA) (w : V) : V × AA →ₗ[O] V × AA where
  toFun p := (f p.1 + g p.2 • w, g p.2)
  map_add' p p' := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul, Prod.mk_add_mk, Prod.mk.injEq,
      and_true]
    abel
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply, Prod.smul_mk, smul_add,
      smul_assoc]

@[simp] lemma extMap_apply (f : V →ₗ[O] V) (g : AA →ₐ[O] AA) (w : V) (p : V × AA) :
    extMap f g w p = (f p.1 + g p.2 • w, g p.2) := rfl

lemma span_inl {s : Set V} (hs : Submodule.span AA s = ⊤) (v : V) :
    ((v, (0 : AA)) : V × AA) ∈ Submodule.span AA ((fun w => ((w, (0 : AA)) : V × AA)) '' s) := by
  have e : (fun w => ((w, (0 : AA)) : V × AA)) '' s = (LinearMap.inl AA V AA) '' s := rfl
  rw [e, Submodule.span_image, hs]
  exact ⟨v, Submodule.mem_top, rfl⟩

section

variable {B : Base O A} {E : Amb B AA} {n : ℕ} (W : WachDatum E n V)

def NN (i : ZMod n) : Submodule A (V × AA) := (W.N i).prod (1 : Submodule A AA)

lemma mem_NN (i : ZMod n) (p : V × AA) :
    p ∈ NN W i ↔ p.1 ∈ W.N i ∧ ∃ a0 : A, algebraMap A AA a0 = p.2 := by
  rw [NN, Submodule.mem_prod, Submodule.mem_one]

variable {W}

lemma ext_γN {z : ZMod n → V} (hz : ∀ j, ∃ m ∈ W.N j, z j = B.X • m) (i : ZMod n) (p : V × AA) :
    p ∈ NN W i ↔ extMap (W.γ i) E.γ (z i) p ∈ NN W i := by
  obtain ⟨v, a⟩ := p
  obtain ⟨m, hm, hzm⟩ := hz i
  have key : ∀ a0 : A, (algebraMap A AA a0) • z i ∈ W.N i := fun a0 => by
    rw [algebraMap_smul, hzm]; exact (W.N i).smul_mem _ ((W.N i).smul_mem _ hm)
  simp only [mem_NN, extMap_apply]
  constructor
  · rintro ⟨hv, a0, rfl⟩
    refine ⟨?_, B.γ a0, (E.γ_ext a0).symm⟩
    rw [E.γ_ext]; exact (W.N i).add_mem ((W.γ_N i v).1 hv) (key _)
  · rintro ⟨hv, b, hb⟩
    obtain ⟨a0, rfl⟩ := B.γ_bij.2 b
    have ha : a = algebraMap A AA a0 := E.γ_bij.1 (by rw [E.γ_ext, hb])
    subst ha
    refine ⟨?_, a0, rfl⟩
    rw [E.γ_ext] at hv
    have := (W.N i).sub_mem hv (key (B.γ a0))
    rw [add_sub_cancel_right] at this
    exact (W.γ_N i v).2 this

lemma ext_γsub {z : ZMod n → V} (hz : ∀ j, ∃ m ∈ W.N j, z j = B.X • m) (i : ZMod n) :
    ∀ p ∈ NN W i, ∃ p' ∈ NN W i, extMap (W.γ i) E.γ (z i) p - p = B.X • p' := by
  rintro ⟨v, a⟩ hp
  obtain ⟨hv, a0, rfl⟩ := (mem_NN W i _).1 hp
  obtain ⟨m, hm, hzm⟩ := hz i
  obtain ⟨x', hx', hx⟩ := W.γ_sub i v hv
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (B.γ_modX a0)
  refine ⟨(x' + B.γ a0 • m, algebraMap A AA d),
    (mem_NN W i _).2 ⟨(W.N i).add_mem hx' ((W.N i).smul_mem _ hm), d, rfl⟩, ?_⟩
  simp only [extMap_apply, E.γ_ext, Prod.mk_sub_mk, Prod.smul_mk]
  refine Prod.ext ?_ ?_
  · simp only
    rw [add_sub_right_comm, hx, hzm, algebraMap_smul, smul_add, smul_smul, smul_smul, mul_comm]
  · simp only
    rw [← map_sub, ← hd, Algebra.smul_def, ← map_mul, mul_comm]

lemma ext_φspan (y : ZMod n → V) (i : ZMod n) :
    Submodule.span AA (Set.range (extMap (W.φ i) E.φ (y (i + 1)))) = ⊤ := by
  set S := Submodule.span AA (Set.range (extMap (W.φ i) E.φ (y (i + 1))))
  have hsub : (fun w => ((w, (0 : AA)) : V × AA)) '' Set.range (W.φ i) ⊆
      Set.range (extMap (W.φ i) E.φ (y (i + 1))) := by
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨(w, 0), by simp⟩
  have h1 : ∀ v : V, ((v, 0) : V × AA) ∈ S := fun v =>
    Submodule.span_mono hsub (span_inl (W.φ_span i) v)
  have h2 : ((y (i + 1), 1) : V × AA) ∈ S := Submodule.subset_span ⟨(0, 1), by simp⟩
  rw [eq_top_iff]
  rintro ⟨v, a⟩ -
  have := add_mem (h1 (v - a • y (i + 1))) (S.smul_mem a h2)
  simpa using this

lemma ext_φN {y : ZMod n → V} {k0 : ℕ} (hk0 : ∀ j, B.q ^ k0 • y j ∈ W.N j) (i : ZMod n) :
    ∀ p ∈ NN W i, ∃ k : ℕ, B.q ^ k • extMap (W.φ i) E.φ (y (i + 1)) p ∈ NN W (i + 1) := by
  rintro ⟨v, a⟩ hp
  obtain ⟨hv, a0, rfl⟩ := (mem_NN W i _).1 hp
  obtain ⟨k1, hk1⟩ := W.φ_N i v hv
  refine ⟨k1 + k0, (mem_NN W _ _).2 ⟨?_, B.q ^ (k1 + k0) * B.φ a0, ?_⟩⟩
  · simp only [extMap_apply, E.φ_ext, algebraMap_smul, smul_add, Prod.smul_fst]
    refine add_mem ?_ ?_
    · rw [pow_add, mul_comm, mul_smul]; exact (W.N _).smul_mem _ hk1
    · rw [smul_comm, pow_add, mul_smul]
      exact (W.N _).smul_mem _ ((W.N _).smul_mem _ (hk0 _))
  · simp [extMap_apply, E.φ_ext, Algebra.smul_def]

lemma ext_Nφ {y : ZMod n → V} {k0 : ℕ} (hk0 : ∀ j, B.q ^ k0 • y j ∈ W.N j) (i : ZMod n) :
    ∀ p ∈ NN W (i + 1), ∃ k : ℕ, B.q ^ k • p ∈
      Submodule.span A (extMap (W.φ i) E.φ (y (i + 1)) '' (NN W i : Set (V × AA))) := by
  rintro ⟨v, a⟩ hp
  obtain ⟨hv, a0, rfl⟩ := (mem_NN W _ _).1 hp
  set S := Submodule.span A (extMap (W.φ i) E.φ (y (i + 1)) '' (NN W i : Set (V × AA)))
  have hw : B.q ^ k0 • (v - a0 • y (i + 1)) ∈ W.N (i + 1) := by
    rw [smul_sub, smul_comm]
    exact sub_mem ((W.N _).smul_mem _ hv) ((W.N _).smul_mem _ (hk0 _))
  obtain ⟨k2, hk2⟩ := W.N_φ i _ hw
  have hsub : (fun w => ((w, (0 : AA)) : V × AA)) '' (W.φ i '' (W.N i : Set V)) ⊆
      extMap (W.φ i) E.φ (y (i + 1)) '' (NN W i : Set (V × AA)) := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨(w, 0), (mem_NN W i _).2 ⟨hw, 0, map_zero _⟩, by simp⟩
  have h1 : ((B.q ^ k2 • B.q ^ k0 • (v - a0 • y (i + 1)), (0 : AA)) : V × AA) ∈ S := by
    have e : (fun w => ((w, (0 : AA)) : V × AA)) '' (W.φ i '' (W.N i : Set V)) =
        (LinearMap.inl A V AA) '' (W.φ i '' (W.N i : Set V)) := rfl
    have : ((B.q ^ k2 • B.q ^ k0 • (v - a0 • y (i + 1)), (0 : AA)) : V × AA) ∈
        Submodule.span A ((fun w => ((w, (0 : AA)) : V × AA)) '' (W.φ i '' (W.N i : Set V))) := by
      rw [e, Submodule.span_image]
      exact ⟨_, hk2, rfl⟩
    exact Submodule.span_mono hsub this
  have h2 : ((y (i + 1), 1) : V × AA) ∈ S :=
    Submodule.subset_span ⟨(0, 1), (mem_NN W i _).2 ⟨zero_mem _, 1, map_one _⟩, by simp⟩
  refine ⟨k2 + k0, ?_⟩
  have := add_mem h1 (S.smul_mem (B.q ^ (k2 + k0) * a0) h2)
  convert this using 1
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_mk]
    rw [smul_sub, smul_sub, smul_smul, smul_smul, smul_smul, ← pow_add]
    abel
  · simp [Algebra.smul_def]

end

end Formalism.WachCohomologyFacts.PExt
end

-- bundled from Formalism.FrobeniusContraction.FrobeniusContractionProofs.ContractBij
section
namespace Formalism.WachCohomologyFacts.PContractBij

variable {R P : Type} [CommRing R] [AddCommGroup P] [Module R P] (I : Ideal R)

theorem pow_smul_top_anti {m n : ℕ} (h : m ≤ n) :
    (I ^ n • ⊤ : Submodule R P) ≤ (I ^ m • ⊤ : Submodule R P) :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right h)

variable {I}

theorem iterate_mem (f : P →+ P)
    (hf : ∀ k : ℕ, ∀ x ∈ (I ^ k • ⊤ : Submodule R P), f x ∈ (I ^ (k + 1) • ⊤ : Submodule R P))
    (y : P) : ∀ r : ℕ, f^[r] y ∈ (I ^ r • ⊤ : Submodule R P)
  | 0 => by simp
  | r + 1 => by
    rw [Function.iterate_succ_apply']
    exact hf r _ (iterate_mem f hf y r)

theorem fixed_mem (f : P →+ P)
    (hf : ∀ k : ℕ, ∀ x ∈ (I ^ k • ⊤ : Submodule R P), f x ∈ (I ^ (k + 1) • ⊤ : Submodule R P))
    (d : P) (hd : f d = d) : ∀ k : ℕ, d ∈ (I ^ k • ⊤ : Submodule R P)
  | 0 => by simp
  | k + 1 => by
    rw [← hd]
    exact hf k _ (fixed_mem f hf d hd k)

theorem telescope (f : P →+ P) (y : P) (n : ℕ) :
    f (-∑ r ∈ Finset.range n, f^[r] y) - (-∑ r ∈ Finset.range n, f^[r] y) = y - f^[n] y := by
  have key := Finset.sum_range_sub (fun r => f^[r] y) n
  rw [Finset.sum_sub_distrib] at key
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq] at key
  rw [map_neg, map_sum, neg_sub_neg]
  exact (neg_sub _ _).symm.trans (by rw [key, neg_sub])

end Formalism.WachCohomologyFacts.PContractBij

open Formalism.WachCohomologyFacts.PContractBij in
theorem subIdBijectiveOfContracting_holds : Formalism.WachCohomologyFacts.ContractBij := by
  intro R P _ _ _ I _ f hf
  have haus : ∀ z : P, (∀ n : ℕ, z ∈ (I ^ n • ⊤ : Submodule R P)) → z = 0 := by
    intro z hz
    exact IsHausdorff.haus (I := I) inferInstance z
      (fun n => SModEq.sub_mem.mpr (by rw [sub_zero]; exact hz n))
  constructor
  · intro a b hab
    simp only at hab
    have hfix : f (a - b) = a - b := by
      rw [map_sub]
      exact sub_eq_sub_iff_sub_eq_sub.mp hab
    exact sub_eq_zero.mp (haus _ (Formalism.WachCohomologyFacts.PContractBij.fixed_mem f hf _ hfix))
  · intro y
    let xs : ℕ → P := fun n => -∑ r ∈ Finset.range n, f^[r] y
    have hc : ∀ {m n : ℕ}, m ≤ n → xs m ≡ xs n [SMOD (I ^ m • ⊤ : Submodule R P)] := by
      intro m n hmn
      apply SModEq.sub_mem.mpr
      have hsplit : xs m - xs n = ∑ r ∈ Finset.Ico m n, f^[r] y := by
        simp only [xs]
        rw [neg_sub_neg, ← Finset.sum_range_add_sum_Ico _ hmn, add_sub_cancel_left]
      rw [hsplit]
      refine Submodule.sum_mem _ (fun r hr => ?_)
      exact Formalism.WachCohomologyFacts.PContractBij.pow_smul_top_anti I (Finset.mem_Ico.mp hr).1 (Formalism.WachCohomologyFacts.PContractBij.iterate_mem f hf y r)
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (inferInstance : IsPrecomplete I P) hc
    refine ⟨L, ?_⟩
    simp only
    rw [← sub_eq_zero]
    apply haus
    intro n
    have he : L - xs n ∈ (I ^ n • ⊤ : Submodule R P) := by
      rw [← neg_sub]
      exact neg_mem (SModEq.sub_mem.mp (hL n))
    have h1 : f (xs n) - xs n = y - f^[n] y := Formalism.WachCohomologyFacts.PContractBij.telescope f y n
    have h2 : f (xs n) = y - f^[n] y + xs n := by rw [← h1, sub_add_cancel]
    have hz : f L - L - y = f (L - xs n) - (L - xs n) - f^[n] y := by
      rw [map_sub, h2]
      abel
    rw [hz]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ he) (Formalism.WachCohomologyFacts.PContractBij.iterate_mem f hf y n)
    exact Formalism.WachCohomologyFacts.PContractBij.pow_smul_top_anti I (Nat.le_succ n) (hf n _ he)
end

-- bundled from Formalism.FrobeniusContraction.FrobeniusContractionProofs.FiniteCocyclesLeCocycles
section
noncomputable section

namespace Formalism.WachCohomologyFacts.PCoh

open Formalism.WachCohomologyFacts

section One

variable {O A AA : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
  [Algebra A AA] [IsScalarTower O A AA] {B : Base O A} {E : Amb B AA} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V] [Module O V]
  [IsScalarTower O AA V] (W : WachDatum E n V)

theorem Φ_apply (x : ZMod n → V) (j : ZMod n) : W.Φ x j = W.φ (j - 1) (x (j - 1)) := rfl

theorem Γ_apply (x : ZMod n → V) (j : ZMod n) : W.Γ x j = W.γ j (x j) := rfl

theorem ΓΦ_comm (x : ZMod n → V) : W.Γ (W.Φ x) = W.Φ (W.Γ x) := by
  funext j
  rw [Γ_apply, Φ_apply, Φ_apply, Γ_apply, W.comm (j - 1) (x (j - 1)), sub_add_cancel]

end One

section Two

variable {O A AA : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
  [Algebra A AA] [IsScalarTower O A AA] {B : Base O A} {E : Amb B AA} {n : ℕ}
  {V₁ : Type} [AddCommGroup V₁] [Module AA V₁] [Module A V₁] [IsScalarTower A AA V₁]
  [Module O V₁] [IsScalarTower O AA V₁]
  {V₂ : Type} [AddCommGroup V₂] [Module AA V₂] [Module A V₂] [IsScalarTower A AA V₂]
  [Module O V₂] [IsScalarTower O AA V₂]
  {W₁ : WachDatum E n V₁} {W₂ : WachDatum E n V₂} (h : Hom W₁ W₂)

theorem fD_apply (x : ZMod n → V₁) (j : ZMod n) : h.fD x j = h.f (x j) := rfl

theorem fD_Φ (x : ZMod n → V₁) : h.fD (W₁.Φ x) = W₂.Φ (h.fD x) := by
  funext j
  simp only [fD_apply, Φ_apply, h.φ_comm]

theorem fD_Γ (x : ZMod n → V₁) : h.fD (W₁.Γ x) = W₂.Γ (h.fD x) := by
  funext j
  simp only [fD_apply, Γ_apply, h.γ_comm]

end Two

end Formalism.WachCohomologyFacts.PCoh
end
end

-- bundled from Formalism.FrobeniusContraction.FrobeniusContractionProofs.FrobIterQModPrimeHolds
section
noncomputable section

namespace Formalism.WachCohomologyFacts.PPs

open Formalism.WachCohomologyFacts

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]

lemma p_eq_pow (B : Base O A) (s : ℕ) : B.p s = (B.φ ^ s) B.q := by
  unfold Base.p
  induction s with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', AlgHom.mul_apply, Function.iterate_succ_apply', ih]

lemma p_eq (B : Base O A) (s : ℕ) : B.p s = (B.φ ^ s) B.X + (B.ℓ : A) := by
  rw [p_eq_pow, Base.q, map_add, map_natCast]

end Formalism.WachCohomologyFacts.PPs

namespace Formalism.WachCohomologyFacts

open Formalism.WachCohomologyFacts.PPs

end Formalism.WachCohomologyFacts
end
end

-- bundled from Formalism.FrobeniusContraction.FrobeniusContractionProofs.LemmaS
section
namespace Formalism.WachCohomologyFacts.PLemmaS

open Formalism.WachCohomologyFacts.Top

def lift (ℓ : ℕ) (a : ℤ) (x : ZMod ℓ) : ℤ := ((x - (a : ZMod ℓ)).val : ℤ) + a

end Formalism.WachCohomologyFacts.PLemmaS
end

