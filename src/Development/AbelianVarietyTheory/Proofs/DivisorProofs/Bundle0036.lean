import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfRankEq
section
namespace GlobalTheory.SemisimpleCount

variable {Rg : Type} [Ring Rg] [Algebra ℂ Rg]

def killed (I : Set Rg) (M : Type) [AddCommGroup M] [Module ℂ M] [Module Rg M]
    [IsScalarTower ℂ Rg M] : Submodule ℂ M where
  carrier := {m | ∀ x ∈ I, x • m = 0}
  add_mem' := fun ha hb x hx => by rw [smul_add, ha x hx, hb x hx, add_zero]
  zero_mem' := fun x _ => smul_zero x
  smul_mem' := fun c m hm x hx => by rw [smul_comm, hm x hx, smul_zero]

section
variable (I : Set Rg) {M N : Type} [AddCommGroup M] [Module ℂ M] [Module Rg M]
    [IsScalarTower ℂ Rg M] [AddCommGroup N] [Module ℂ N] [Module Rg N] [IsScalarTower ℂ Rg N]

theorem mem_killed {m : M} : m ∈ killed I M ↔ ∀ x ∈ I, x • m = 0 := Iff.rfl

theorem map_mem_killed {A B : Type} [AddCommGroup A] [Module Rg A] [AddCommGroup B] [Module Rg B]
    (f : A →ₗ[Rg] B) {a : A} (ha : ∀ x ∈ I, x • a = 0) : ∀ x ∈ I, x • f a = 0 := by
  intro x hx
  rw [← map_smul, ha x hx, map_zero]

theorem rank_killed_le (f : M →ₗ[Rg] N) (hf : Function.Injective f) :
    Module.rank ℂ (killed I M) ≤ Module.rank ℂ (killed I N) := by
  refine LinearMap.rank_le_of_injective
    ((f.restrictScalars ℂ).restrict (p := killed I M) (q := killed I N)
      (fun m hm => map_mem_killed I f hm)) ?_
  intro a b hab
  exact Subtype.ext (hf (congrArg Subtype.val hab))

theorem rank_killed_congr (e : M ≃ₗ[Rg] N) :
    Module.rank ℂ (killed I M) = Module.rank ℂ (killed I N) :=
  le_antisymm (rank_killed_le I e.toLinearMap e.injective)
    (rank_killed_le I e.symm.toLinearMap e.symm.injective)

theorem rank_killed_prod :
    Module.rank ℂ (killed I (M × N)) =
      Module.rank ℂ (killed I M) + Module.rank ℂ (killed I N) := by
  have h : killed I (M × N) = (killed I M).prod (killed I N) := by
    ext ⟨a, b⟩
    simp only [mem_killed, Submodule.mem_prod, Prod.smul_mk, Prod.mk_eq_zero]
    exact ⟨fun h => ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩,
      fun h x hx => ⟨h.1 x hx, h.2 x hx⟩⟩
  rw [h, ← rank_prod']
  refine LinearEquiv.rank_eq
    { toFun := fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
      invFun := fun p => ⟨(p.1.1, p.2.1), p.1.2, p.2.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem rank_killed_compl {U V : Submodule Rg M} (h : IsCompl U V) :
    Module.rank ℂ (killed I M) = Module.rank ℂ (killed I U) + Module.rank ℂ (killed I V) := by
  rw [← rank_killed_congr I (Submodule.prodEquivOfIsCompl U V h), rank_killed_prod]

variable {S : Type} [AddCommGroup S] [Module Rg S]

theorem rank_hom_le (f : M →ₗ[Rg] N) (hf : Function.Injective f) :
    Module.rank ℂ (S →ₗ[Rg] M) ≤ Module.rank ℂ (S →ₗ[Rg] N) := by
  refine LinearMap.rank_le_of_injective
    { toFun := fun g => f.comp g
      map_add' := fun a b => by ext; simp
      map_smul' := fun c a => by
        ext s
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply]
        exact (f.restrictScalars ℂ).map_smul c (a s) } ?_
  intro a b hab
  ext s
  exact hf (LinearMap.congr_fun hab s)

theorem rank_hom_congr (e : M ≃ₗ[Rg] N) :
    Module.rank ℂ (S →ₗ[Rg] M) = Module.rank ℂ (S →ₗ[Rg] N) :=
  le_antisymm (rank_hom_le e.toLinearMap e.injective)
    (rank_hom_le e.symm.toLinearMap e.symm.injective)

theorem rank_hom_compl {U V : Submodule Rg M} (h : IsCompl U V) :
    Module.rank ℂ (S →ₗ[Rg] M) = Module.rank ℂ (S →ₗ[Rg] U) + Module.rank ℂ (S →ₗ[Rg] V) := by
  rw [← rank_hom_congr (Submodule.prodEquivOfIsCompl U V h), ← rank_prod']
  exact (LinearMap.prodEquiv ℂ).rank_eq.symm

theorem rank_hom_congr_left {S' : Type} [AddCommGroup S'] [Module Rg S'] (e : S ≃ₗ[Rg] S') :
    Module.rank ℂ (S →ₗ[Rg] M) = Module.rank ℂ (S' →ₗ[Rg] M) :=
  LinearEquiv.rank_eq
    { toFun := fun g => g.comp e.symm.toLinearMap
      invFun := fun g => g.comp e.toLinearMap
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun g => by ext; simp
      right_inv := fun g => by ext; simp }

theorem injective_of_ne_zero {A : Type} [AddCommGroup A] [Module Rg A] [IsSimpleModule Rg S]
    {f : S →ₗ[Rg] A} (hf : f ≠ 0) : Function.Injective f :=
  (LinearMap.injective_or_eq_zero f).resolve_right hf

theorem rank_hom_le_killed [IsSimpleModule Rg S] {s : S} (hs : s ≠ 0) (hI : ∀ x ∈ I, x • s = 0) :
    Module.rank ℂ (S →ₗ[Rg] M) ≤ Module.rank ℂ (killed I M) := by
  refine LinearMap.rank_le_of_injective
    { toFun := fun g => ⟨g s, map_mem_killed I g hI⟩
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl } ?_
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h
  have h0 : a s = 0 := congrArg Subtype.val ha
  exact hs (injective_of_ne_zero h (h0.trans (map_zero a).symm))

theorem exists_ne_zero_of_rank_eq {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B]
    [Module ℂ B] (h : Module.rank ℂ A = Module.rank ℂ B) {a : A} (ha : a ≠ 0) :
    ∃ b : B, b ≠ 0 := by
  by_contra hb
  push_neg at hb
  exact ha (rank_zero_iff_forall_zero.1 (h.trans (rank_zero_iff_forall_zero.2 hb)) a)

theorem exists_simple {A : Type} [AddCommGroup A] [Module Rg A] [IsSemisimpleModule Rg A]
    {a : A} (ha : a ≠ 0) (hI : ∀ x ∈ I, x • a = 0) :
    ∃ U : Submodule Rg A, IsSimpleModule Rg U ∧ ∃ u : U, u ≠ 0 ∧ ∀ x ∈ I, x • u = 0 := by
  have hj : a ∉ Module.jacobson Rg A := by
    rw [IsSemisimpleModule.jacobson_eq_bot]
    simpa using ha
  simp only [Module.jacobson, Submodule.mem_sInf, not_forall] at hj
  obtain ⟨P, hP, haP⟩ := hj
  obtain ⟨U, hU⟩ := exists_isCompl P
  have e := Submodule.quotientEquivOfIsCompl P U hU
  haveI : IsSimpleModule Rg (A ⧸ P) := isSimpleModule_iff_isCoatom.2 hP
  refine ⟨U, IsSimpleModule.congr e.symm, e (P.mkQ a), ?_, ?_⟩
  · simpa using haP
  · exact map_mem_killed I (e.toLinearMap.comp P.mkQ) hI

end

theorem rank_killed_eq (I : Set Rg) (n : ℕ) :
    ∀ (M N : Type) [AddCommGroup M] [Module ℂ M] [Module Rg M]
    [IsScalarTower ℂ Rg M] [AddCommGroup N] [Module ℂ N] [Module Rg N] [IsScalarTower ℂ Rg N]
    [IsSemisimpleModule Rg M] [IsSemisimpleModule Rg N],
    Module.rank ℂ (killed I M) = n →
    (∀ (S : Type) [AddCommGroup S] [Module Rg S] [IsSimpleModule Rg S] (s : S), s ≠ 0 →
      (∀ x ∈ I, x • s = 0) → Module.rank ℂ (S →ₗ[Rg] M) = Module.rank ℂ (S →ₗ[Rg] N)) →
    Module.rank ℂ (killed I N) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M N _ _ _ _ _ _ _ _ _ _ hn H
  have sub_ne : ∀ {A : Type} [AddCommGroup A] [Module Rg A] (U : Submodule Rg A) (u : U),
      u ≠ 0 → U.subtype ≠ 0 := by
    intro A _ _ U u hu h
    exact hu (Subtype.ext (LinearMap.congr_fun h u))
  by_cases h0 : ∀ m : killed I M, m = 0
  · rw [← hn, rank_zero_iff_forall_zero.2 h0, rank_zero_iff_forall_zero]
    intro a
    by_contra ha
    obtain ⟨U, hU, u, hu, hI⟩ := exists_simple I (a := a.1) (fun h => ha (Subtype.ext h)) a.2
    obtain ⟨f, hf⟩ := exists_ne_zero_of_rank_eq (H U u hu hI).symm (sub_ne U u hu)
    have h1 : f u = 0 := congrArg Subtype.val (h0 ⟨f u, map_mem_killed I f hI⟩)
    exact hu (injective_of_ne_zero hf (h1.trans (map_zero f).symm))
  · push_neg at h0
    obtain ⟨a, ha⟩ := h0
    obtain ⟨U, hU, u, hu, hI⟩ := exists_simple I (a := a.1) (fun h => ha (Subtype.ext h)) a.2
    obtain ⟨f, hf⟩ := exists_ne_zero_of_rank_eq (H U u hu hI) (sub_ne U u hu)
    have e : U ≃ₗ[Rg] LinearMap.range f := LinearEquiv.ofInjective f (injective_of_ne_zero hf)
    obtain ⟨M', hM'⟩ := exists_isCompl U
    obtain ⟨N', hN'⟩ := exists_isCompl (LinearMap.range f)
    have hM := rank_killed_compl I hM'
    rw [hn] at hM
    have hUf : Module.rank ℂ (killed I U) < Cardinal.aleph0 :=
      lt_of_le_of_lt (hM ▸ le_self_add) (Cardinal.natCast_lt_aleph0 (n := n))
    have hMf : Module.rank ℂ (killed I M') < Cardinal.aleph0 :=
      lt_of_le_of_lt (hM ▸ le_add_self) (Cardinal.natCast_lt_aleph0 (n := n))
    obtain ⟨k, hk⟩ := Cardinal.lt_aleph0.1 hUf
    obtain ⟨l, hl⟩ := Cardinal.lt_aleph0.1 hMf
    have hk0 : k ≠ 0 := by
      rintro rfl
      have := rank_zero_iff_forall_zero.1 (hk.trans Nat.cast_zero) ⟨u, hI⟩
      exact hu (congrArg Subtype.val this)
    have hkl : n = k + l := by
      rw [hk, hl] at hM
      exact_mod_cast hM
    have hN := ih l (by omega) M' N' hl (by
      intro S _ _ _ s hs hsI
      have h := H S s hs hsI
      rw [rank_hom_compl hM', rank_hom_compl hN', ← rank_hom_congr e] at h
      have hfin : Module.rank ℂ (S →ₗ[Rg] U) < Cardinal.aleph0 :=
        lt_of_le_of_lt (rank_hom_le_killed I hs hsI) hUf
      exact Cardinal.eq_of_add_eq_add_left h hfin)
    rw [rank_killed_compl I hN', ← rank_killed_congr I e, hk, hN, hkl, Nat.cast_add]

theorem finrank_killed_eq : ∀ (Rg : Type) [Ring Rg] [Algebra ℂ Rg] (M N : Type) [AddCommGroup M] [Module ℂ M] [Module Rg M] [IsScalarTower ℂ Rg M] [SMulCommClass Rg ℂ M] [AddCommGroup N] [Module ℂ N] [Module Rg N] [IsScalarTower ℂ Rg N] [SMulCommClass Rg ℂ N] (I : Set Rg) (FM : Submodule ℂ M) (FN : Submodule ℂ N), IsSemisimpleModule Rg M → IsSemisimpleModule Rg N → (∀ m, m ∈ FM ↔ ∀ x ∈ I, x • m = 0) → (∀ n, n ∈ FN ↔ ∀ x ∈ I, x • n = 0) → FiniteDimensional ℂ FM → FiniteDimensional ℂ FN → (∀ U : Submodule Rg M, IsSimpleModule Rg U → (∃ u ∈ U, u ≠ 0 ∧ u ∈ FM) → Module.rank ℂ (U →ₗ[Rg] M) = Module.rank ℂ (U →ₗ[Rg] N)) → (∀ U : Submodule Rg N, IsSimpleModule Rg U → (∃ u ∈ U, u ≠ 0 ∧ u ∈ FN) → Module.rank ℂ (U →ₗ[Rg] M) = Module.rank ℂ (U →ₗ[Rg] N)) → Module.finrank ℂ FM = Module.finrank ℂ FN := by
  intro Rg _ _ M N _ _ _ _ _ _ _ _ _ _ I FM FN hM hN hFM hFN fM fN HM HN
  obtain rfl : FM = killed I M := Submodule.ext hFM
  obtain rfl : FN = killed I N := Submodule.ext hFN
  have key := rank_killed_eq I (Module.finrank ℂ (killed I M)) M N
    (Module.finrank_eq_rank ℂ _).symm (by
      intro S _ _ _ s hs hI
      by_cases h1 : ∃ f : S →ₗ[Rg] M, f ≠ 0
      · obtain ⟨f, hf⟩ := h1
        have hi := injective_of_ne_zero hf
        have e : S ≃ₗ[Rg] LinearMap.range f := LinearEquiv.ofInjective f hi
        rw [rank_hom_congr_left e, rank_hom_congr_left e]
        exact HM _ (IsSimpleModule.congr e.symm) ⟨f s, ⟨s, rfl⟩,
          fun h => hs (hi (h.trans (map_zero f).symm)), map_mem_killed I f hI⟩
      by_cases h2 : ∃ f : S →ₗ[Rg] N, f ≠ 0
      · obtain ⟨f, hf⟩ := h2
        have hi := injective_of_ne_zero hf
        have e : S ≃ₗ[Rg] LinearMap.range f := LinearEquiv.ofInjective f hi
        rw [rank_hom_congr_left e, rank_hom_congr_left e]
        exact HN _ (IsSimpleModule.congr e.symm) ⟨f s, ⟨s, rfl⟩,
          fun h => hs (hi (h.trans (map_zero f).symm)), map_mem_killed I f hI⟩
      push_neg at h1 h2
      rw [rank_zero_iff_forall_zero.2 h1, rank_zero_iff_forall_zero.2 h2])
  exact (Module.finrank_eq_of_rank_eq key).symm

end GlobalTheory.SemisimpleCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroMinorOfRank
section
open Matrix

namespace GlobalTheory

theorem exists_rows_linearIndependent_of_le_rank {K m n : Type} [Field K] [Fintype m] [Fintype n]
    (ρ : ℕ) (M : Matrix m n K) (h : ρ ≤ M.rank) :
    ∃ S : Fin ρ → m, LinearIndependent K (M.submatrix S id).row := by
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K M.row
  haveI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hκ : Fintype.card κ = M.rank := by
    rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_row]
  have hle : Fintype.card (Fin ρ) ≤ Fintype.card κ := by rw [hκ, Fintype.card_fin]; exact h
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hle
  exact ⟨a ∘ f, hli.comp f f.injective⟩

theorem exists_submatrix_det_ne_zero_of_le_rank :
    ∀ (k : Type) [Field k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
      (ρ : ℕ) (Y : Matrix A D k), ρ ≤ Y.rank → ∃ S : Fin ρ → A, ∃ τ : Fin ρ → D,
        (Y.submatrix S τ).det ≠ 0 := by
  intro k _ A D _ _ _ _ ρ Y h
  obtain ⟨S, hS⟩ := exists_rows_linearIndependent_of_le_rank ρ Y h
  have hZ : (Y.submatrix S id).rank = ρ := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hS, Fintype.card_fin]
  have hZt : ρ ≤ (Y.submatrix S id)ᵀ.rank := by rw [Matrix.rank_transpose, hZ]
  obtain ⟨τ, hτ⟩ := exists_rows_linearIndependent_of_le_rank ρ (Y.submatrix S id)ᵀ hZt
  refine ⟨S, τ, ?_⟩
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hτ)
  have e : (Y.submatrix S id)ᵀ.submatrix τ id = (Y.submatrix S τ)ᵀ := by ext i j; rfl
  rw [e, Matrix.det_transpose] at hu
  exact hu.ne_zero

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNotMemSmulEqZeroOfSubmodule
section
open TensorProduct Polynomial

namespace GlobalTheory.NakAug

theorem eval_notMem_of_monic {A : Type*} [CommRing A] (P : Ideal A) [P.IsPrime] (p : A[X])
    (hmon : p.Monic) (hc : ∀ k, p.coeff k ∈ P ^ (p.natDegree - k)) (t : A) (ht : t ∉ P) :
    p.eval t ∉ P := by
  intro hmem
  rw [eval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree, one_mul] at hmem
  have hs : ∑ i ∈ Finset.range p.natDegree, p.coeff i * t ^ i ∈ P := by
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ ?_
    have hi' : i < p.natDegree := Finset.mem_range.mp hi
    exact Ideal.pow_le_self (by omega) (hc i)
  have : t ^ p.natDegree ∈ P := by
    have := P.sub_mem hmem hs
    simpa using this
  exact ht (Ideal.IsPrime.mem_of_pow_mem inferInstance _ this)

theorem exists_notMem_smul_eq_zero {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Finite A M] (P : Ideal A) [P.IsPrime] (t : A) (ht : t ∉ P)
    (h : ∀ m : M, t • m ∈ P • (⊤ : Submodule A M)) :
    ∃ g : A, g ∉ P ∧ ∀ m : M, g • m = 0 := by
  obtain ⟨p, hmon, -, hc, h0⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero A
      (algebraMap A (Module.End A M) t) P (by
        rintro _ ⟨m, rfl⟩
        simpa [Module.algebraMap_end_apply] using h m)
  refine ⟨p.eval t, eval_notMem_of_monic P p hmon hc t ht, fun m => ?_⟩
  rw [aeval_algebraMap_apply_eq_algebraMap_eval] at h0
  have := congrArg (fun φ : Module.End A M => φ m) h0
  simpa [Module.algebraMap_end_apply] using this

theorem exists_notMem_smul_eq_zero_of_submodule {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (P : Ideal A) [P.IsPrime] (N : Submodule A M) (hN : N.FG) (t : A) (ht : t ∉ P)
    (h : ∀ m ∈ N, t • m ∈ P • N) :
    ∃ g : A, g ∉ P ∧ ∀ m ∈ N, g • m = 0 := by
  haveI : Module.Finite A N := Module.Finite.iff_fg.mpr hN
  obtain ⟨g, hg, h0⟩ := exists_notMem_smul_eq_zero (M := N) P t ht (fun m => by
    have hm := h m m.2
    have hmap : P • N = (P • (⊤ : Submodule A N)).map N.subtype := by
      rw [Submodule.map_smul'', Submodule.map_subtype_top]
    rw [hmap] at hm
    obtain ⟨z, hz, hzm⟩ := hm
    have : z = t • m := Subtype.ext (by simpa using hzm)
    exact this ▸ hz)
  exact ⟨g, hg, fun m hm => by simpa using congrArg Subtype.val (h0 ⟨m, hm⟩)⟩

theorem exists_uniform_notMem {A M M' : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup M'] [Module A M'] [Module.Finite A M] (P : Ideal A) [hP : P.IsPrime]
    (S : Submodule A M') (D : M →ₗ[A] M') (h : ∀ b, ∃ f : A, f ∉ P ∧ f • D b ∈ S) :
    ∃ f : A, f ∉ P ∧ ∀ b, f • D b ∈ S := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule A M).FG)
  have key : ∀ t : Finset M, ∃ f : A, f ∉ P ∧ ∀ b ∈ t, f • D b ∈ S := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨1, fun h1 => hP.ne_top ((Ideal.eq_top_iff_one _).mpr h1), by simp⟩
    | insert a t ha ih =>
      obtain ⟨F, hF, hFt⟩ := ih
      obtain ⟨fa, hfa, hfaa⟩ := h a
      refine ⟨fa * F, fun hm => (hP.mem_or_mem hm).elim hfa hF, fun b hb => ?_⟩
      rcases Finset.mem_insert.mp hb with rfl | hb
      · rw [mul_comm, mul_smul]; exact S.smul_mem _ hfaa
      · rw [mul_smul]; exact S.smul_mem _ (hFt b hb)
  obtain ⟨f, hf, hfs⟩ := key s
  refine ⟨f, hf, fun b => ?_⟩
  have hle : Submodule.span A (s : Set M) ≤ S.comap (f • D) := by
    rw [Submodule.span_le]
    intro b hb
    exact hfs b hb
  have hb : b ∈ Submodule.span A (s : Set M) := hs ▸ Submodule.mem_top
  simpa using hle hb

theorem augmentation_agrees_after_inverting
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A] [Module.Finite A B]
    (P : Ideal A) [hP : P.IsPrime] (ε : B →ₐ[A] A) (α : B →ₐ[A] B) (d : ℕ) (hd : (d : A) ∉ P)
    (h2 : ∀ x ∈ RingHom.ker ε, α x - (d : B) * x ∈ (RingHom.ker ε) ^ 2)
    (h3 : ∀ b, ∃ f : A, f ∉ P ∧ f • (α b - algebraMap A B (ε b)) ∈ P.map (algebraMap A B)) :
    ∃ g : A, g ∉ P ∧ ∀ b, g • (α b - algebraMap A B (ε b)) = 0 := by
  classical
  set J : Ideal B := RingHom.ker ε with hJdef
  set Q : Ideal B := P.map (algebraMap A B) with hQdef
  haveI : IsNoetherian A B := isNoetherian_of_isNoetherianRing_of_finite A B

  let D : B →ₗ[A] B := α.toLinearMap - (Algebra.linearMap A B).comp ε.toLinearMap
  have hDapp : ∀ b, D b = α b - algebraMap A B (ε b) := fun b => rfl
  obtain ⟨f, hf, hfD⟩ := exists_uniform_notMem P (Q.restrictScalars A) D
    (fun b => by simpa only [hDapp, Submodule.restrictScalars_mem] using h3 b)
  have hmemJ : ∀ x, x ∈ J ↔ ε x = 0 := fun x => RingHom.mem_ker
  have hφ : ∀ b, b - algebraMap A B (ε b) ∈ J := fun b => by
    rw [hmemJ, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have hαφ : ∀ b, α (b - algebraMap A B (ε b)) = α b - algebraMap A B (ε b) := fun b => by
    rw [map_sub, AlgHom.commutes]
  have hαJ : ∀ x ∈ J, α x ∈ J := fun x hx => by
    have h := h2 x hx
    have e : α x = (α x - (d : B) * x) + (d : B) * x := by ring
    rw [e]
    exact J.add_mem (Ideal.pow_le_self two_ne_zero h) (J.mul_mem_left _ hx)

  have hfαQ : ∀ x ∈ J, algebraMap A B f * α x ∈ Q := fun x hx => by
    have h := hfD x
    rw [hDapp, (hmemJ x).mp hx, map_zero, sub_zero, Algebra.smul_def] at h
    exact h

  have hL1 : ∀ y ∈ Q, y ∈ J → y ∈ P • J.restrictScalars A := fun y hyQ hyJ => by
    let φ : B →ₗ[A] B := LinearMap.id - (Algebra.linearMap A B).comp ε.toLinearMap
    have hy : y ∈ P • (⊤ : Submodule A B) := by
      rw [Ideal.smul_top_eq_map]; exact hyQ
    have h1 : φ y ∈ (P • (⊤ : Submodule A B)).map φ := Submodule.mem_map_of_mem hy
    rw [Submodule.map_smul''] at h1
    have hle : (⊤ : Submodule A B).map φ ≤ J.restrictScalars A := by
      rintro _ ⟨b, -, rfl⟩
      exact hφ b
    have hφy : φ y = y := by
      show y - algebraMap A B (ε y) = y
      rw [(hmemJ y).mp hyJ, map_zero, sub_zero]
    rw [hφy] at h1
    exact Submodule.smul_mono le_rfl hle h1

  have hs : ∃ s : A, s ∉ P ∧ ∀ x ∈ J, algebraMap A B s * x ∈ J ^ 2 := by
    let L : B →ₗ[A] B ⧸ J ^ 2 := (Ideal.Quotient.mkₐ A (J ^ 2)).toLinearMap
    have hL : ∀ x, L x = Ideal.Quotient.mk (J ^ 2) x := fun x => rfl
    let N : Submodule A (B ⧸ J ^ 2) := (J.map (Ideal.Quotient.mk (J ^ 2))).restrictScalars A
    have hNfg : N.FG := IsNoetherian.noetherian N
    obtain ⟨s, hs, hs0⟩ := exists_notMem_smul_eq_zero_of_submodule P N hNfg (f * d)
      (fun hm => (hP.mem_or_mem hm).elim hf hd) (fun m hm => by
        obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hm
        have e1 : (f * (d : A)) • Ideal.Quotient.mk (J ^ 2) x
            = L (algebraMap A B f * α x) := by
          rw [← hL, ← map_smul, hL, hL, Ideal.Quotient.eq, Algebra.smul_def, map_mul, map_natCast]
          have : algebraMap A B f * (d : B) * x - algebraMap A B f * α x
              = - (algebraMap A B f * (α x - (d : B) * x)) := by ring
          rw [this]
          exact (J ^ 2).neg_mem ((J ^ 2).mul_mem_left _ (h2 x hx))
        rw [e1]
        have hy := hL1 _ (hfαQ x hx) (J.mul_mem_left _ (hαJ x hx))
        have h1 : L (algebraMap A B f * α x) ∈ (P • J.restrictScalars A).map L :=
          Submodule.mem_map_of_mem hy
        rw [Submodule.map_smul''] at h1
        refine Submodule.smul_mono le_rfl ?_ h1
        rintro _ ⟨z, hz, rfl⟩
        exact Ideal.mem_map_of_mem _ hz)
    refine ⟨s, hs, fun x hx => ?_⟩
    have h0 := hs0 _ (Ideal.mem_map_of_mem (Ideal.Quotient.mk (J ^ 2)) hx)
    rw [← hL, ← map_smul, hL, Ideal.Quotient.eq_zero_iff_mem, Algebra.smul_def] at h0
    exact h0
  obtain ⟨s, hsP, hsJ⟩ := hs

  set K : Ideal B := J.map α with hKdef
  have hKfg : (K.restrictScalars A).FG := IsNoetherian.noetherian _
  have hJ2 : ∀ y ∈ J ^ 2, algebraMap A B f * α y ∈ Q * K := by
    intro y hy
    rw [pow_two] at hy
    refine Submodule.mul_induction_on hy (fun y1 hy1 y2 hy2 => ?_) (fun a b ha hb => ?_)
    · rw [map_mul, ← mul_assoc]
      exact Ideal.mul_mem_mul (hfαQ y1 hy1) (Ideal.mem_map_of_mem α hy2)
    · rw [map_add, mul_add]; exact Ideal.add_mem _ ha hb
  have hKt : ∀ m ∈ K.restrictScalars A, (s * f) • m ∈ P • K.restrictScalars A := by
    intro m hm
    rw [← Ideal.smul_restrictScalars, Submodule.restrictScalars_mem, Ideal.smul_eq_mul,
      Algebra.smul_def]
    rw [Submodule.restrictScalars_mem] at hm
    refine Submodule.span_induction (p := fun m _ => algebraMap A B (s * f) * m ∈ Q * K)
      ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨x, hx, rfl⟩
      have e : algebraMap A B (s * f) * α x = algebraMap A B f * α (algebraMap A B s * x) := by
        rw [map_mul, map_mul, AlgHom.commutes]; ring
      rw [e]; exact hJ2 _ (hsJ x hx)
    · simp
    · intro x y _ _ hx hy; rw [mul_add]; exact Ideal.add_mem _ hx hy
    · intro b x _ hx; rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ b hx
  obtain ⟨g, hg, hg0⟩ := exists_notMem_smul_eq_zero_of_submodule P (K.restrictScalars A) hKfg
    (s * f) (fun hm => (hP.mem_or_mem hm).elim hsP hf) hKt
  refine ⟨g, hg, fun b => ?_⟩
  rw [← hαφ]
  exact hg0 _ (Ideal.mem_map_of_mem α (hφ b))

end GlobalTheory.NakAug
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyAnnihilatesCommutingLinearCombination
section
noncomputable section

open Polynomial

namespace GlobalTheory.CommutingPoly

theorem exists_poly_annihilates_linear_combination : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Type} [Fintype ι] (A : ι → Module.End ℂ M),
    (∀ i j, Commute (A i) (A j)) → ∀ (c : ι → ℂ) (P : ι → Polynomial ℂ), (∀ i, P i ≠ 0) →
      ∃ p : Polynomial ℂ, p ≠ 0 ∧ ∀ v : M, (∀ i, Polynomial.aeval (A i) (P i) v = 0) →
        Polynomial.aeval (∑ i, c i • A i) p v = 0 := by
  intro M _ _ ι _ A hc c P hP
  classical
  letI : CommRing (Algebra.adjoin ℂ (Set.range A)) := Algebra.adjoinCommRingOfComm ℂ
    (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hc i j)
  let S := Algebra.adjoin ℂ (Set.range A)
  let I : Ideal S :=
    { carrier := {a | ∀ v : M, (∀ i, Polynomial.aeval (A i) (P i) v = 0) → (a : Module.End ℂ M) v = 0}
      add_mem' := by
        intro a b ha hb v hv
        simp only [Set.mem_setOf_eq] at ha hb
        simp [ha v hv, hb v hv]
      zero_mem' := by intro v _; simp
      smul_mem' := by
        intro a b hb v hv
        show ((a * b : S) : Module.End ℂ M) v = 0
        rw [Subalgebra.coe_mul, Module.End.mul_apply, hb v hv, map_zero] }
  have hI : ∀ a : S, a ∈ I ↔ ∀ v : M, (∀ i, Polynomial.aeval (A i) (P i) v = 0) → (a : Module.End ℂ M) v = 0 :=
    fun a => Iff.rfl
  let t : ι → S := fun i => ⟨A i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  let q : S →ₐ[ℂ] S ⧸ I := Ideal.Quotient.mkₐ ℂ I
  have hint : ∀ i, IsIntegral ℂ (q (t i)) := by
    intro i
    refine IsAlgebraic.isIntegral ⟨P i, hP i, ?_⟩
    rw [aeval_algHom_apply]
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    rw [hI]
    intro v hv
    rw [aeval_subalgebra_coe]
    exact hv i
  have hs : IsIntegral ℂ (q (∑ i, c i • t i)) := by
    rw [map_sum]
    exact IsIntegral.sum _ (fun i _ => by rw [map_smul]; exact (hint i).smul _)
  obtain ⟨p, hpm, hp⟩ := hs
  refine ⟨p, hpm.ne_zero, fun v hv => ?_⟩
  have hq : q (aeval (∑ i, c i • t i) p) = 0 := by
    rw [← aeval_algHom_apply, aeval_def]
    exact hp
  have hmem : aeval (∑ i, c i • t i) p ∈ I := (Ideal.Quotient.eq_zero_iff_mem).mp hq
  have h := (hI _).mp hmem v hv
  rw [aeval_subalgebra_coe] at h
  have hsum : ((∑ i, c i • t i : S) : Module.End ℂ M) = ∑ i, c i • A i := by
    rw [show ((∑ i, c i • t i : S) : Module.End ℂ M) = S.val (∑ i, c i • t i) from rfl, map_sum]
    simp [t]
  rw [hsum] at h
  exact h

end GlobalTheory.CommutingPoly
end
end

