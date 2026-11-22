import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLiftNumberFieldModule
section
open NumberField

namespace GlobalTheory

theorem nsmul_surjective_torsion_lift (M : Type) [AddCommGroup M] (N e : ℕ) (hN : 1 ≤ N)
    (h : ∀ j : ℕ, Nat.card {x : M // (N ^ j) • x = 0} = (N ^ j) ^ e)
    (j : ℕ) (y : M) (hy : (N ^ j) • y = 0) :
    ∃ z : M, (N ^ (j + 1)) • z = 0 ∧ N • z = y := by
  let A : ℕ → AddSubgroup M := fun k => (DistribMulAction.toAddMonoidHom M (N ^ k)).ker
  have hA : ∀ k x, x ∈ A k ↔ (N ^ k) • x = 0 := fun k x => by
    simp [A, AddMonoidHom.mem_ker]
  have hcard : ∀ k, Nat.card (A k) = (N ^ k) ^ e := fun k => by
    rw [← h k]; exact Nat.card_congr (Equiv.subtypeEquivRight (hA k))
  have hpos : ∀ k, 0 < (N ^ k) ^ e := fun k => by positivity
  have hfin : ∀ k, Finite (A k) := fun k =>
    Nat.finite_of_card_ne_zero (by rw [hcard k]; exact (hpos k).ne')
  let ψ : A (j + 1) →+ M := (DistribMulAction.toAddMonoidHom M N).comp (A (j + 1)).subtype
  have hψ : ∀ z : A (j + 1), ψ z = N • (z : M) := fun z => rfl
  have hN1 : ∀ x : M, x ∈ A 1 ↔ N • x = 0 := fun x => by rw [hA 1 x, pow_one]
  have hker : Nat.card ψ.ker = Nat.card (A 1) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun z => ⟨(z.1 : M), (hN1 _).2 (by rw [← hψ]; exact AddMonoidHom.mem_ker.1 z.2)⟩
        invFun := fun z => ⟨⟨(z : M), (hA (j+1) _).2 (by
            rw [pow_succ, mul_smul, (hN1 _).1 z.2, smul_zero])⟩,
            AddMonoidHom.mem_ker.2 (by rw [hψ]; exact (hN1 _).1 z.2)⟩
        left_inv := fun z => rfl
        right_inv := fun z => rfl }
  have hle : ψ.range ≤ A j := by
    rintro _ ⟨z, rfl⟩
    rw [hA, hψ, ← mul_smul, ← pow_succ]
    exact (hA (j+1) _).1 z.2
  have hmul := AddSubgroup.card_mul_index ψ.ker
  rw [AddSubgroup.index_ker] at hmul
  have hrange : Nat.card (Set.range ψ) = Nat.card (A j) := by
    have e1 : (N ^ (j + 1)) ^ e = (N ^ 1) ^ e * (N ^ j) ^ e := by
      rw [← mul_pow, ← pow_add, add_comm]
    rw [hker, hcard, hcard, e1] at hmul
    rw [hcard]
    exact Nat.eq_of_mul_eq_mul_left (hpos 1) hmul
  have heq : ψ.range = A j := by
    refine AddSubgroup.eq_of_le_of_card_ge hle ?_
    rw [← hrange]
    exact le_of_eq (Nat.card_congr (Equiv.setCongr (AddMonoidHom.coe_range ψ)).symm)
  have hyr : y ∈ ψ.range := by rw [heq]; exact (hA j y).2 hy
  obtain ⟨z, hz⟩ := hyr
  exact ⟨z, (hA (j+1) _).1 z.2, hz⟩

theorem nsmul_surj_of_card_torsion :
    ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N →
    (∀ j : ℕ, Nat.card {x : M // (N ^ j) • x = 0} = (N ^ j) ^ (2 * Module.finrank ℚ F)) →
    ∀ j : ℕ, ∀ y : M, (N ^ j) • y = 0 → ∃ z : M, (N ^ (j + 1)) • z = 0 ∧ N • z = y := by
  intro F _ _ M _ _ N hN h j y hy
  exact nsmul_surjective_torsion_lift M N _ hN h j y hy

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTwoGeneratorsGlobal
section
open NumberField

namespace GlobalTheory

theorem torsion_gens_glue_of_local (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M]
    [Module (𝓞 F) M] (N : ℕ) (hN : 1 ≤ N) (hfin : Finite {x : M // N • x = 0})
    (H : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
      ∃ u v : M, N • u = 0 ∧ N • v = 0 ∧ ∀ x : M, N • x = 0 → ∃ a b : 𝓞 F,
        x - a • u - b • v ∈ 𝔭 • Submodule.torsionBy (𝓞 F) M (N : 𝓞 F)) :
    ∃ p : Fin 2 → M, (∀ i, N • p i = 0) ∧ ∀ y : M, N • y = 0 → ∃ a b : 𝓞 F, y = a • p 0 + b • p 1 := by
  classical
  set T := Submodule.torsionBy (𝓞 F) M (N : 𝓞 F) with hTdef
  have hT : ∀ x, x ∈ T ↔ N • x = 0 := fun x => by
    rw [hTdef, Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul]
  set J : Ideal (𝓞 F) := Ideal.span {(N : 𝓞 F)} with hJdef
  have hJ : J ≠ ⊥ := by
    rw [hJdef, Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]; omega
  haveI : Finite (𝓞 F ⧸ J) := Ideal.finiteQuotientOfFreeOfNeBot J hJ
  have hPfin : {𝔭 : Ideal (𝓞 F) | 𝔭.IsMaximal ∧ J ≤ 𝔭}.Finite := by
    have key : ∀ 𝔭 𝔮 : Ideal (𝓞 F), J ≤ 𝔮 →
        (Ideal.Quotient.mk J) '' (𝔭 : Set (𝓞 F)) = (Ideal.Quotient.mk J) '' (𝔮 : Set (𝓞 F)) →
        𝔭 ≤ 𝔮 := by
      intro 𝔭 𝔮 hq he x hx
      have hmem : Ideal.Quotient.mk J x ∈ (Ideal.Quotient.mk J) '' (𝔮 : Set (𝓞 F)) :=
        he ▸ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := hmem
      have hyx : y - x ∈ J := Ideal.Quotient.eq.mp hxy
      have := 𝔮.sub_mem hy (hq hyx)
      simpa using this
    refine Set.Finite.of_finite_image (f := fun 𝔭 : Ideal (𝓞 F) =>
      (Ideal.Quotient.mk J) '' (𝔭 : Set (𝓞 F))) (Set.toFinite _) ?_
    intro 𝔭 h𝔭 𝔮 h𝔮 he
    exact le_antisymm (key _ _ h𝔮.2 he) (key _ _ h𝔭.2 he.symm)
  set P := hPfin.toFinset with hPdef
  have hP : ∀ 𝔭, 𝔭 ∈ P ↔ 𝔭.IsMaximal ∧ J ≤ 𝔭 := fun 𝔭 => Set.Finite.mem_toFinset _
  have hmax : ∀ j : P, j.1.IsMaximal := fun j => ((hP j.1).1 j.2).1
  have H' : ∀ i : P, ∃ uv : M × M, N • uv.1 = 0 ∧ N • uv.2 = 0 ∧ ∀ x : M, N • x = 0 →
      ∃ a b : 𝓞 F, x - a • uv.1 - b • uv.2 ∈ i.1 • T := by
    intro i
    have hi := (hP i.1).1 i.2
    obtain ⟨u, v, hu, hv, hx⟩ :=
      H i.1 hi.1 ((Ideal.span_singleton_le_iff_mem _).mp hi.2)
    exact ⟨(u, v), hu, hv, hx⟩
  choose uv huv1 huv2 hgen using H'
  have hc : ∀ i : P, ∃ c : 𝓞 F, c - 1 ∈ i.1 ∧ ∀ j : P, j ≠ i → c ∈ j.1 := by
    intro i
    have htop : i.1 ⊔ ∏ j ∈ Finset.univ.erase i, j.1 = ⊤ := by
      apply Ideal.sup_prod_eq_top
      intro j hj
      exact (hmax i).coprime_of_ne (hmax j)
        (fun h => (Finset.ne_of_mem_erase hj) (Subtype.ext h.symm))
    have h1 : (1 : 𝓞 F) ∈ i.1 ⊔ ∏ j ∈ Finset.univ.erase i, j.1 := htop ▸ Submodule.mem_top
    obtain ⟨a, ha, k, hk, hak⟩ := Submodule.mem_sup.mp h1
    refine ⟨k, ?_, fun j hj => ?_⟩
    · have hk1 : k - 1 = -a := by rw [← hak]; ring
      rw [hk1]; exact i.1.neg_mem ha
    · exact (Ideal.prod_le_inf.trans
        (Finset.inf_le (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩))) hk
  choose c hc1 hc2 using hc
  have hcd : ∀ i j : P, c j - (if j = i then 1 else 0) ∈ i.1 := by
    intro i j
    by_cases h : j = i
    · subst h; simpa using hc1 j
    · simpa [h] using hc2 j i (fun e => h e.symm)
  have gl : ∀ (i : P) (w : P → M), (∀ j, w j ∈ T) → ∑ j, c j • w j - w i ∈ i.1 • T := by
    intro i w hw
    have hsum : ∑ j, c j • w j - w i = ∑ j, (c j - if j = i then 1 else 0) • w j := by
      simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hcd i j) (hw j)
  have huT : ∀ j, (uv j).1 ∈ T := fun j => (hT _).2 (huv1 j)
  have hvT : ∀ j, (uv j).2 ∈ T := fun j => (hT _).2 (huv2 j)
  set p : Fin 2 → M := ![∑ j, c j • (uv j).1, ∑ j, c j • (uv j).2] with hpdef
  have hp0 : p 0 = ∑ j, c j • (uv j).1 := rfl
  have hp1 : p 1 = ∑ j, c j • (uv j).2 := rfl
  have hpT : ∀ i, p i ∈ T := by
    intro i
    fin_cases i
    · exact Submodule.sum_mem _ fun j _ => T.smul_mem _ (huT j)
    · exact Submodule.sum_mem _ fun j _ => T.smul_mem _ (hvT j)
  set S := Submodule.span (𝓞 F) (Set.range p) with hSdef
  have hloc : ∀ i : P, ∀ x ∈ T, ∃ a b : 𝓞 F, x - a • p 0 - b • p 1 ∈ i.1 • T := by
    intro i x hx
    obtain ⟨a, b, hab⟩ := hgen i x ((hT x).1 hx)
    refine ⟨a, b, ?_⟩
    have he : x - a • p 0 - b • p 1 = (x - a • (uv i).1 - b • (uv i).2)
        - a • (p 0 - (uv i).1) - b • (p 1 - (uv i).2) := by
      simp only [smul_sub]; abel
    rw [he]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ hab (Submodule.smul_mem _ _ ?_))
      (Submodule.smul_mem _ _ ?_)
    · exact gl i (fun j => (uv j).1) huT
    · exact gl i (fun j => (uv j).2) hvT
  have hTfg : T.FG := by
    have hTset : (T : Set M) = {x : M | N • x = 0} := Set.ext hT
    have hfs : (T : Set M).Finite := by
      rw [hTset]; exact Set.finite_coe_iff.mp hfin
    exact Submodule.fg_def.mpr ⟨T, hfs, Submodule.span_eq T⟩
  set N' := T.map S.mkQ with hN'def
  have hN'fg : N'.FG := hTfg.map _
  have hprime : ∀ i : P, N' ≤ i.1 • N' := by
    rintro i _ ⟨x, hx, rfl⟩
    obtain ⟨a, b, hab⟩ := hloc i x hx
    have hq : S.mkQ x = S.mkQ (x - a • p 0 - b • p 1) := by
      simp only [Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      have : x - (x - a • p 0 - b • p 1) = a • p 0 + b • p 1 := by abel
      rw [this]
      exact S.add_mem (S.smul_mem _ (Submodule.subset_span ⟨0, rfl⟩))
        (S.smul_mem _ (Submodule.subset_span ⟨1, rfl⟩))
    rw [hq, hN'def, ← Submodule.map_smul'']
    exact Submodule.mem_map_of_mem hab
  have hprod : ∀ s : Finset P, N' ≤ (∏ i ∈ s, i.1) • N' := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Submodule.mul_smul]
      exact (hprime i).trans (Submodule.smul_mono le_rfl ih)
  have hjac : (∏ i : P, i.1) ≤ J.jacobson := by
    unfold Ideal.jacobson
    refine le_sInf ?_
    rintro m ⟨hJm, hm⟩
    have hmP : m ∈ P := (hP m).2 ⟨hm, hJm⟩
    exact Ideal.prod_le_inf.trans (Finset.inf_le (f := fun i : P => i.1) (Finset.mem_univ ⟨m, hmP⟩))
  have hJN' : J • N' = ⊥ := by
    rw [eq_bot_iff]
    refine Submodule.smul_le.mpr ?_
    rintro r hr _ ⟨x, hx, rfl⟩
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have hx0 : (N : 𝓞 F) • x = 0 := (Submodule.mem_torsionBy_iff _ _).mp hx
    rw [mul_smul, ← LinearMap.map_smul, hx0, map_zero, smul_zero]
    exact Submodule.zero_mem _
  have hN'bot : N' = ⊥ := by
    rw [Submodule.eq_smul_of_le_smul_of_le_jacobson hN'fg (hprod Finset.univ) hjac, hJN']
  have hTS : T ≤ S := by
    intro x hx
    have hmem : S.mkQ x ∈ N' := Submodule.mem_map_of_mem hx
    rw [hN'bot, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmem
    exact hmem
  refine ⟨p, fun i => (hT _).1 (hpT i), fun y hy => ?_⟩
  have hyS : y ∈ S := hTS ((hT y).2 hy)
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hyS
  refine ⟨f 0, f 1, ?_⟩
  rw [← hf, Fin.sum_univ_two]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTwoGeneratorsModPrime
section
open NumberField

namespace GlobalTheory

open scoped Pointwise

theorem torsionBy_two_generators_mod_prime :
  ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N → Finite {x : M // N • x = 0} →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
    Nat.card {x : M // ∀ a ∈ 𝔭, a • x = 0} ≤ Ideal.absNorm 𝔭 ^ 2 →
    ∃ u v : M, N • u = 0 ∧ N • v = 0 ∧ ∀ x : M, N • x = 0 → ∃ a b : 𝓞 F,
      x - a • u - b • v ∈ 𝔭 • Submodule.torsionBy (𝓞 F) M (N : 𝓞 F) := by
  intro F _ _ M _ _ N hN hfin 𝔭 h𝔭 hN𝔭 hcard
  set T := Submodule.torsionBy (𝓞 F) M (N : 𝓞 F) with hT
  have memT : ∀ x : M, x ∈ T ↔ N • x = 0 := by
    intro x; rw [Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul]
  haveI : Finite T := by
    refine Finite.of_injective (fun y : T => (⟨y.1, (memT y.1).1 y.2⟩ : {x : M // N • x = 0})) ?_
    intro y z h
    have h' := congrArg (fun w : {x : M // N • x = 0} => w.1) h
    exact Subtype.ext h'
  have hNR : (N : 𝓞 F) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hspan0 : Ideal.span {(N : 𝓞 F)} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hNR
  have h𝔭0 : 𝔭 ≠ ⊥ := fun h => hNR (by simpa [h] using hN𝔭)
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq
    ((Ideal.span_singleton_le_iff_mem _).2 hN𝔭) hspan0
  let φ : T →ₗ[𝓞 F] T := a • LinearMap.id
  have hNT : ∀ y : T, (N : 𝓞 F) • y = 0 := fun y => Subtype.ext ((Submodule.mem_torsionBy_iff _ _).1 y.2)
  have hsmul : 𝔭 • (⊤ : Submodule (𝓞 F) T) = LinearMap.range φ := by
    rw [← ha, Submodule.sup_smul, Submodule.ideal_span_singleton_smul,
      Submodule.ideal_span_singleton_smul]
    ext y
    simp only [Submodule.mem_sup, Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top,
      true_and, LinearMap.mem_range]
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, _, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, by simp [φ, hNT]⟩
    · rintro ⟨w, rfl⟩
      exact ⟨0, ⟨0, by simp⟩, _, ⟨w, rfl⟩, by simp [φ]⟩

  let P := {x : M // ∀ b ∈ 𝔭, b • x = 0}
  haveI : Finite P := by
    refine Finite.of_injective (fun y : P => (⟨y.1, by
      rw [← Nat.cast_smul_eq_nsmul (𝓞 F)]; exact y.2 _ hN𝔭⟩ : {x : M // N • x = 0})) ?_
    intro y z h
    have h' := congrArg (fun w : {x : M // N • x = 0} => w.1) h
    exact Subtype.ext h'
  have hker : Nat.card (LinearMap.ker φ) ≤ Nat.card P := by
    refine Nat.card_le_card_of_injective (fun y : LinearMap.ker φ => (⟨y.1.1, by
      intro b hb
      rw [← ha] at hb
      obtain ⟨b1, hb1, b2, hb2, rfl⟩ := Submodule.mem_sup.1 hb
      obtain ⟨c1, rfl⟩ := Ideal.mem_span_singleton'.1 hb1
      obtain ⟨c2, rfl⟩ := Ideal.mem_span_singleton'.1 hb2
      have e1 : (N : 𝓞 F) • y.1.1 = 0 := congrArg Subtype.val (hNT y.1)
      have e2 : a • y.1.1 = 0 := by
        have := y.2
        rw [LinearMap.mem_ker] at this
        exact congrArg Subtype.val this
      rw [add_smul, mul_smul, mul_smul, e1, e2, smul_zero, smul_zero, add_zero]⟩ : P)) ?_
    intro y z h
    have h' := congrArg (fun w : P => w.1) h
    exact Subtype.ext (Subtype.ext h')
  have hQ : Nat.card (T ⧸ 𝔭 • (⊤ : Submodule (𝓞 F) T)) = Nat.card (LinearMap.ker φ) := by
    rw [hsmul]
    have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range φ)
    have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker φ)
    have h3 : Nat.card (T ⧸ LinearMap.ker φ) = Nat.card (LinearMap.range φ) :=
      Nat.card_congr φ.quotKerEquivRange.toEquiv
    have h4 : 0 < Nat.card (LinearMap.range φ) := Nat.card_pos
    rw [h3] at h2
    rw [h1, mul_comm (Nat.card (LinearMap.range φ))] at h2
    exact Nat.eq_of_mul_eq_mul_right h4 h2

  haveI : Finite (𝓞 F ⧸ 𝔭) := Ideal.finiteQuotientOfFreeOfNeBot 𝔭 h𝔭0
  letI : Field (𝓞 F ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  haveI : Finite (T ⧸ 𝔭 • (⊤ : Submodule (𝓞 F) T)) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  haveI : Module.Finite (𝓞 F ⧸ 𝔭) (T ⧸ 𝔭 • (⊤ : Submodule (𝓞 F) T)) := Module.Finite.of_finite
  have hk : 1 < Nat.card (𝓞 F ⧸ 𝔭) := Finite.one_lt_card
  have hnorm : Ideal.absNorm 𝔭 = Nat.card (𝓞 F ⧸ 𝔭) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hdim : Module.finrank (𝓞 F ⧸ 𝔭) (T ⧸ 𝔭 • (⊤ : Submodule (𝓞 F) T)) ≤ 2 := by
    have h5 := Module.natCard_eq_pow_finrank (K := 𝓞 F ⧸ 𝔭) (V := T ⧸ 𝔭 • (⊤ : Submodule (𝓞 F) T))
    have h6 : Nat.card (T ⧸ 𝔭 • (⊤ : Submodule (𝓞 F) T)) ≤ Nat.card (𝓞 F ⧸ 𝔭) ^ 2 := by
      rw [hQ, ← hnorm]; exact hker.trans hcard
    rw [h5] at h6
    exact (Nat.pow_le_pow_iff_right hk).1 h6

  set Q := T ⧸ 𝔭 • (⊤ : Submodule (𝓞 F) T) with hQdef
  set r := Module.finrank (𝓞 F ⧸ 𝔭) Q with hr
  let bs := Module.finBasis (𝓞 F ⧸ 𝔭) Q
  let u' : Q := if h : 0 < r then bs ⟨0, h⟩ else 0
  let v' : Q := if h : 1 < r then bs ⟨1, h⟩ else 0
  have hspan : ∀ q : Q, ∃ c d : 𝓞 F ⧸ 𝔭, c • u' + d • v' = q := by
    intro q
    have hle : Set.range bs ⊆ ({u', v'} : Set Q) := by
      rintro _ ⟨i, rfl⟩
      have hi : i.val = 0 ∨ i.val = 1 := by have := i.2; omega
      rcases hi with hi | hi
      · left
        have h0 : 0 < r := by have := i.2; omega
        simp only [u', dif_pos h0]
        congr 1; exact Fin.ext hi
      · right
        have h1 : 1 < r := by have := i.2; omega
        simp only [v', dif_pos h1]
        simp only [Set.mem_singleton_iff]
        congr 1; exact Fin.ext hi
    have hq : q ∈ Submodule.span (𝓞 F ⧸ 𝔭) (Set.range bs) := by
      rw [bs.span_eq]; exact Submodule.mem_top
    have hq2 := Submodule.span_mono hle hq
    exact Submodule.mem_span_pair.1 hq2
  obtain ⟨u0, hu0⟩ := Submodule.Quotient.mk_surjective _ u'
  obtain ⟨v0, hv0⟩ := Submodule.Quotient.mk_surjective _ v'
  refine ⟨u0.1, v0.1, (memT _).1 u0.2, (memT _).1 v0.2, ?_⟩
  intro x hx
  let y : T := ⟨x, (memT x).2 hx⟩
  obtain ⟨c, d, hcd⟩ := hspan (Submodule.Quotient.mk y)
  obtain ⟨c0, rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨d0, rfl⟩ := Ideal.Quotient.mk_surjective d
  refine ⟨c0, d0, ?_⟩
  rw [← hu0, ← hv0, Module.Quotient.mk_smul_mk, Module.Quotient.mk_smul_mk,
    ← Submodule.Quotient.mk_add, eq_comm, Submodule.Quotient.eq] at hcd
  have hmap := Submodule.mem_map_of_mem (f := T.subtype) hcd
  rw [Submodule.map_smul'', Submodule.map_subtype_top] at hmap
  convert hmap using 1
  simp [y, sub_sub]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeAevalLeOfDegLeOne
section
set_option autoImplicit false

open NumberField MvPolynomial

noncomputable section

namespace GlobalTheory.SZShift

theorem totalDegree_aeval_le_of_deg_le_one {σ τ F E : Type} [CommRing F] [CommRing E] [Algebra F E]
    (g : σ → MvPolynomial τ E) (hg : ∀ i, (g i).totalDegree ≤ 1) (P : MvPolynomial σ F) :
    (aeval g P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun d hd => ?_)
  rw [aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.algebraMap_apply, totalDegree_C, zero_add, Finsupp.prod]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hd)
  rw [Finsupp.sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hg i))

def shiftSubst {F E : Type} [CommRing F] [CommRing E] [Algebra F E] {D N n : ℕ}
    (w : Matrix (Fin N) (Fin n) F) (y : Fin D → Fin n → E) (p : Fin D × Fin N) :
    MvPolynomial (Fin D × Fin n) E :=
  ∑ k, C (algebraMap F E (w p.2 k)) * (X (p.1, k) + C (y p.1 k))

end GlobalTheory.SZShift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceEqSumMultMulRe
section
namespace GlobalTheory.TraceRealEmbeddingSum

open NumberField

theorem re_embedding_mk {F : Type} [Field F] (φ : F →+* ℂ) (x : F) :
    ((InfinitePlace.mk φ).embedding x).re = (φ x).re := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h <;>
    simp [h, ComplexEmbedding.conjugate_coe_eq]

theorem trace_eq_sum_mult_mul_re {F : Type} [Field F] [NumberField F] (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) =
      ∑ w : InfinitePlace F, (w.mult : ℝ) * (w.embedding x).re := by
  classical

  have htr : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ∑ σ : F →ₐ[ℚ] ℂ, σ x := by
    rw [← trace_eq_sum_embeddings ℂ (K := ℚ) (L := F), eq_ratCast]
  have hre : ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ φ : F →+* ℂ, (φ x).re := by
    have h := congrArg Complex.re htr
    rw [Complex.ratCast_re, Complex.re_sum] at h
    rw [h, ← (RingHom.equivRatAlgHom F ℂ).sum_comp]
    rfl

  rw [hre, ← Finset.univ.sum_fiberwise (fun φ : F →+* ℂ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hfib : ∀ φ ∈ Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w),
      (φ x).re = (w.embedding x).re := by
    intro φ hφ
    rw [(Finset.mem_filter.mp hφ).2.symm, re_embedding_mk]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    nsmul_eq_mul]

end GlobalTheory.TraceRealEmbeddingSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMonicOverMvPolynomial
section
open MvPolynomial

namespace GlobalTheory

theorem trace_monic_over_mvPolynomial {K : Type} [Field K] (F : Subfield K) [FiniteDimensional F K]
    {ι : Type} (z : ι → K) (hz : ∀ i, z i ∈ F) (v : K)
    (hv : IsIntegral (Subring.closure (Set.range z)) v) :
    ∃ f : Polynomial (MvPolynomial ι ℤ), f.Monic ∧
      f.eval₂ (aeval z).toRingHom (Algebra.trace F K v : K) = 0 := by
  set φ : MvPolynomial ι ℤ →+* K := (aeval z).toRingHom with hφdef
  set S : Subring K := Subring.closure (Set.range z) with hSdef
  have hφF : ∀ p, φ p ∈ F := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simpa [hφdef] using F.intCast_mem a
    | add p q hp hq => simpa [map_add] using F.add_mem hp hq
    | mul_X p i hp => simpa [map_mul, hφdef] using F.mul_mem hp (hz i)
  have hφS : ∀ p, φ p ∈ S := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simpa [hφdef] using S.intCast_mem a
    | add p q hp hq => simpa [map_add] using S.add_mem hp hq
    | mul_X p i hp =>
        simpa [map_mul, hφdef] using S.mul_mem hp (Subring.subset_closure ⟨i, rfl⟩)
  let ψ : MvPolynomial ι ℤ →+* F := φ.codRestrict F hφF
  let θ : MvPolynomial ι ℤ →+* S := φ.codRestrict S hφS
  letI : Algebra (MvPolynomial ι ℤ) K := φ.toAlgebra
  letI : Algebra (MvPolynomial ι ℤ) F := ψ.toAlgebra
  letI : Algebra (MvPolynomial ι ℤ) S := θ.toAlgebra
  haveI : IsScalarTower (MvPolynomial ι ℤ) F K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower (MvPolynomial ι ℤ) S K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hθsurj : Function.Surjective θ := by
    rintro ⟨s, hs⟩
    have hle : S ≤ φ.range := by
      rw [hSdef, Subring.closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨X i, by simp [hφdef]⟩
    obtain ⟨p, hp⟩ := hle hs
    exact ⟨p, Subtype.ext hp⟩
  haveI : Algebra.IsIntegral (MvPolynomial ι ℤ) S :=
    Algebra.IsIntegral.of_surjective (Algebra.ofId _ _) hθsurj
  have hvP : IsIntegral (MvPolynomial ι ℤ) v := isIntegral_trans v hv
  have hT : IsIntegral (MvPolynomial ι ℤ) (Algebra.trace F K v) := Algebra.isIntegral_trace hvP
  obtain ⟨f, hfm, hf⟩ := hT
  refine ⟨f, hfm, ?_⟩
  have h := congrArg F.subtype hf
  rw [Polynomial.hom_eval₂, map_zero] at h
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformScalar
section
namespace GlobalTheory.UniformScalarBound

theorem uniform_scalar {R V : Type} [CommRing R] [IsDomain R] [AddCommGroup V] [Module R V]
    (A B : Submodule R V) (hA : A.FG) (h : ∀ x ∈ A, ∃ s : R, s ≠ 0 ∧ s • x ∈ B) :
    ∃ s : R, s ≠ 0 ∧ ∀ x ∈ A, s • x ∈ B := by
  classical
  obtain ⟨S, rfl⟩ := hA
  choose! f hf0 hfB using fun x (hx : x ∈ S) => h x (Submodule.subset_span hx)
  refine ⟨∏ g ∈ S, f g, Finset.prod_ne_zero_iff.mpr (fun g hg => hf0 g hg), ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rw [← Finset.mul_prod_erase S f hy, mul_comm, mul_smul]
    exact B.smul_mem _ (hfB y hy)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact B.add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact B.smul_mem a hx

theorem main : ∀ {R V : Type} [inst : CommRing R] [IsDomain R] [inst_2 : AddCommGroup V]
    [inst_3 : Module R V] (A B : Submodule R V), Submodule.FG A →
    (∀ x ∈ A, ∃ (s : R), s ≠ (0 : R) ∧ s • x ∈ B) →
    ∃ (s : R), s ≠ (0 : R) ∧ ∀ x ∈ A, s • x ∈ B :=
  fun A B hA h => uniform_scalar A B hA h

end GlobalTheory.UniformScalarBound
end

