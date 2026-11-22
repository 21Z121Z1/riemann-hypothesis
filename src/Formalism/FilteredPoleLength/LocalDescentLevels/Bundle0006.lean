import Formalism.FilteredPoleLength.ReducedBasisBounds.GradedFreeLengthFiltered
import Formalism.FilteredPoleLength.LocalDescentLevels.Bundle0004
import Formalism.FilteredPoleLength.ReducedBasisBounds.LocalStepLevelsExt
import Formalism.FilteredPoleLength.LocalDescentLevels.Bundle0005
import Formalism.FilteredPoleLength.LocalDescentLevels.LengthBaseChange

-- bundled from Formalism.FilteredPoleLength.LocalDescentLevels.LeadingTermLength
section
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

theorem leadingTermLength : LeadingTermLength := by
  intro O A A0 _ _ _ _ _ n F ι _ _ deg δ t σ u h0 hn hF hker hsurj hdeg hu hli
  classical
  have hanti : Antitone F := antitone_nat_of_succ_le hF
  have hkill : ∀ k (x : A) (h : x ∈ F k), x ∈ F (k + 1) → σ k ⟨x, h⟩ = 0 := by
    intro k x h hx
    have : (⟨x, h⟩ : ↥(F k)) ∈ LinearMap.ker (σ k) := by
      rw [hker k]; exact hx
    exact this
  have hkill' : ∀ k (x : A) (h : x ∈ F k), σ k ⟨x, h⟩ = 0 → x ∈ F (k + 1) := by
    intro k x h hx
    have : (⟨x, h⟩ : ↥(F k)) ∈ LinearMap.ker (σ k) := hx
    rw [hker k] at this
    exact this

  have hmem0 : ∀ (α : ι) (j : ℕ) (a : Fin δ → O), (deg α < j → a = 0) →
      ∑ i, a i • u α i ∈ F j := by
    intro α j a ha
    rcases lt_or_ge (deg α) j with h | h
    · rw [ha h]; simp
    · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hanti h (hu α i).1)
  have hval0 : ∀ (α : ι) (j : ℕ) (a : Fin δ → O) (h : ∑ i, a i • u α i ∈ F j),
      (deg α < j → a = 0) → ∀ β : {β : ι // deg β = j},
        σ j ⟨∑ i, a i • u α i, h⟩ β = if β.1 = α then ∑ i, a i • t i else 0 := by
    intro α j a h ha β
    rcases lt_trichotomy (deg α) j with hlt | heq | hgt
    · have hz : (⟨∑ i, a i • u α i, h⟩ : ↥(F j)) = 0 := by
        apply Subtype.ext
        simp [ha hlt]
      rw [hz, ha hlt]; simp
    · subst heq
      have hz : (⟨∑ i, a i • u α i, h⟩ : ↥(F (deg α))) =
          ∑ i, a i • (⟨u α i, (hu α i).1⟩ : ↥(F (deg α))) := by
        apply Subtype.ext
        simp
      rw [hz, map_sum, Finset.sum_apply]
      have : ∀ i, (σ (deg α)) (a i • (⟨u α i, (hu α i).1⟩ : ↥(F (deg α)))) β =
          if β.1 = α then a i • t i else 0 := by
        intro i
        rw [map_smul, (hu α i).2, Pi.smul_apply, Pi.single_apply]
        by_cases hb : β.1 = α
        · have : β = ⟨α, rfl⟩ := Subtype.ext hb
          simp [this]
        · have : β ≠ ⟨α, rfl⟩ := fun h' => hb (congrArg Subtype.val h')
          simp [this, hb]
      simp_rw [this]
      by_cases hb : β.1 = α <;> simp [hb]
    · have hx : ∑ i, a i • u α i ∈ F (j + 1) :=
        Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hanti hgt (hu α i).1)
      rw [hkill j _ h hx]
      have hb : β.1 ≠ α := by
        intro hb
        have := β.2
        rw [hb] at this
        omega
      simp [hb]

  have hmem1 : ∀ (j : ℕ) (c : ι → Fin δ → O), (∀ α, deg α < j → c α = 0) →
      ∑ α, ∑ i, c α i • u α i ∈ F j := fun j c hc =>
    Submodule.sum_mem _ fun α _ => hmem0 α j (c α) (hc α)
  have hval1 : ∀ (j : ℕ) (c : ι → Fin δ → O) (h : ∑ α, ∑ i, c α i • u α i ∈ F j),
      (∀ α, deg α < j → c α = 0) → ∀ β : {β : ι // deg β = j},
        σ j ⟨∑ α, ∑ i, c α i • u α i, h⟩ β = ∑ i, c β.1 i • t i := by
    intro j c h hc β
    have hz : (⟨∑ α, ∑ i, c α i • u α i, h⟩ : ↥(F j)) =
        ∑ α, (⟨∑ i, c α i • u α i, hmem0 α j (c α) (hc α)⟩ : ↥(F j)) := by
      apply Subtype.ext
      simp
    rw [hz, map_sum, Finset.sum_apply]
    simp_rw [hval0 _ j _ _ (hc _) β]
    simp

  have hstrict : ∀ (k : ℕ) (c : ι → Fin δ → O), ∑ α, ∑ i, c α i • u α i ∈ F k →
      ∀ j, j ≤ k → ∀ α, deg α < j → c α = 0 := by
    intro k c hb j
    induction j with
    | zero => intro _ α h; omega
    | succ j ih =>
      intro hj α hα
      have ih' := ih (by omega)
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hα) with h | h
      · exact ih' α h
      · have hbj := hmem1 j c ih'
        have h1 := hval1 j c hbj ih' ⟨α, h⟩
        rw [hkill j _ hbj (hanti hj hb)] at h1
        funext i
        exact Fintype.linearIndependent_iff.mp hli (c α) h1.symm i
  set N : Submodule O A := Submodule.span O (Set.range fun p : ι × Fin δ => u p.1 p.2) with hN
  have hNmem : ∀ x : A, x ∈ N ↔ ∃ c : ι → Fin δ → O, ∑ α, ∑ i, c α i • u α i = x := by
    intro x
    rw [hN, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨fun α i => c (α, i), by rw [Fintype.sum_prod_type]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨fun p => c p.1 p.2, by rw [Fintype.sum_prod_type]⟩
  set T : Submodule O A0 := Submodule.span O (Set.range t) with hT

  have hgr : ∀ k, (F (k + 1) ⊔ (N ⊓ F k)).comap (F k).subtype =
      (Submodule.pi Set.univ fun _ : {α : ι // deg α = k} => T).comap (σ k) := by
    intro k
    ext ⟨x, hx⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_pi, Set.mem_univ,
      forall_true_left]
    constructor
    · intro h β
      obtain ⟨a, ha, b, ⟨hbN, hbF⟩, rfl⟩ := Submodule.mem_sup.mp h
      obtain ⟨c, rfl⟩ := (hNmem b).mp hbN
      have hc := hstrict k c hbF k le_rfl
      have hz : (⟨a + ∑ α, ∑ i, c α i • u α i, hx⟩ : ↥(F k)) =
          ⟨a, hF k ha⟩ + ⟨∑ α, ∑ i, c α i • u α i, hbF⟩ := rfl
      rw [hz, map_add, hkill k a _ ha, zero_add, hval1 k c hbF hc β]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · intro h
      have hch : ∀ β : {α : ι // deg α = k}, ∃ a : Fin δ → O, ∑ i, a i • t i = σ k ⟨x, hx⟩ β :=
        fun β => (Submodule.mem_span_range_iff_exists_fun O).mp (h β)
      choose a ha using hch
      let c : ι → Fin δ → O := fun α => if hα : deg α = k then a ⟨α, hα⟩ else 0
      have hc : ∀ α, deg α < k → c α = 0 := by
        intro α hα
        simp only [c]
        rw [dif_neg (by omega)]
      have hyF := hmem1 k c hc
      have hyN : ∑ α, ∑ i, c α i • u α i ∈ N := (hNmem _).mpr ⟨c, rfl⟩
      have hσ : σ k ⟨x, hx⟩ = σ k ⟨∑ α, ∑ i, c α i • u α i, hyF⟩ := by
        funext β
        rw [hval1 k c hyF hc β, ← ha β]
        simp only [c]
        rw [dif_pos β.2]
      have hd : x - ∑ α, ∑ i, c α i • u α i ∈ F (k + 1) := by
        refine hkill' k _ ((F k).sub_mem hx hyF) ?_
        have hz : (⟨x - ∑ α, ∑ i, c α i • u α i, (F k).sub_mem hx hyF⟩ : ↥(F k)) =
            ⟨x, hx⟩ - ⟨∑ α, ∑ i, c α i • u α i, hyF⟩ := rfl
        rw [hz, map_sub, hσ, sub_self]
      refine Submodule.mem_sup.mpr ⟨_, hd, _, ⟨hyN, hyF⟩, by abel⟩
  have hlen : ∀ k, Module.length O (↥(F k) ⧸ (F (k + 1) ⊔ (N ⊓ F k)).comap (F k).subtype) =
      (Fintype.card {α : ι // deg α = k} : ℕ∞) * Module.length O (A0 ⧸ T) := by
    intro k
    set P : Submodule O ({α : ι // deg α = k} → A0) :=
      Submodule.pi Set.univ fun _ : {α : ι // deg α = k} => T with hP
    have hk : LinearMap.ker (P.mkQ ∘ₗ σ k) = (F (k + 1) ⊔ (N ⊓ F k)).comap (F k).subtype := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ, hgr k]
    have hs : Function.Surjective (P.mkQ ∘ₗ σ k) :=
      (Submodule.mkQ_surjective P).comp (hsurj k)
    have e1 := (Submodule.quotEquivOfEq _ _ hk).symm.trans
      ((P.mkQ ∘ₗ σ k).quotKerEquivOfSurjective hs)
    have e2 := Submodule.quotientPi (fun _ : {α : ι // deg α = k} => T)
    rw [e1.length_eq, e2.length_eq, Module.length_pi_of_fintype]
    simp
  rw [filteredLength O A n F h0 hn hF N]
  simp_rw [hlen]
  rw [← Finset.sum_mul]
  congr 1
  rw [← Nat.cast_sum]
  congr 1
  have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset ι)) (t := Finset.range n)
    (f := deg) (fun α _ => by simpa using hdeg α)
  rw [Finset.card_univ] at this
  rw [this]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.card_subtype]

end Formalism.LatticeBaseChangeAlt
end
end

-- bundled from Formalism.FilteredPoleLength.LocalDescentLevels.LevelsLengthSum
section
namespace Formalism.LatticeBaseChangeAlt

open Module

theorem levelsLengthSum : LevelsLengthSum := by
  intro O' _ _ ι _ Rr A _ _ _ _ _ _ _ _ x mm n F r R h0 hn hmono hinj hlen hsum
  rw [Module.length_pi_of_fintype]
  refine Finset.sum_congr rfl fun z _ => ?_
  have h := filteredPoleLength O' (Rr z) (A z) (x z) (mm z) (n z) (F z) (r z) (h0 z) (hn z)
    (hmono z) (hinj z) (hlen z)
  rw [h, hsum z]

end Formalism.LatticeBaseChangeAlt
end

-- bundled from Formalism.FilteredPoleLength.LocalDescentLevels.LocalStepExtOf
section
open Module

namespace Formalism.LatticeBaseChangeAlt

open BQuot in
theorem localStepExt_of (hQ : QuotientLengthExt) : LocalStepExt := by
  intro O K K₁ V W _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ϖ hϖ M Θ N₁ Z Zm N' e be n th c AA AA' N₁'
    ρ a a' X NK hMl hΘl hNΘ hthM hthΘ hker hspan hcM ha ha' hdet hXN hN₁ hZ hZm hρ hkρ himg hN₁'
    hAA hf1 hf2 hf3 V'
  have hp0 : algebraMap O K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hϖ.ne_zero
  have hp1 : algebraMap O K₁ ϖ ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply O K K₁]
    exact (map_ne_zero_iff _ (algebraMap K K₁).injective).2 hp0
  have hsm : ∀ v : V, (algebraMap O K ϖ) ^ e • v = ϖ ^ e • v := by
    intro v
    rw [← map_pow, algebraMap_smul]
  have hIdx := Formalism.IncomingBounds.index_last_reduction_holds O K V ϖ hϖ (e : ℤ) M Θ hMl hΘl V'
  have hbridge : M.map ((((algebraMap O K ϖ) ^ (e : ℤ)) • LinearMap.id : V →ₗ[K] V).restrictScalars O)
      = X := by
    ext x
    simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, LinearMap.smul_apply,
      LinearMap.id_coe, id_eq, zpow_natCast, X, LinearMap.smul_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, (hsm y).symm⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, hsm y⟩
  rw [hbridge] at hIdx
  let Tj : Submodule O V := Submodule.span O (Set.range fun j => (algebraMap O K ϖ) ^ e • th j)
  have hTΘ : Tj ≤ Θ := Submodule.span_le.2 (by
    rintro _ ⟨j, rfl⟩
    show (algebraMap O K ϖ) ^ e • th j ∈ Θ
    rw [hsm]
    exact Θ.smul_mem _ (hthΘ j))
  have hthX : ∀ j, (algebraMap O K ϖ) ^ e • th j ∈ X := by
    intro j
    rw [hsm]
    exact ⟨th j, hthM j, rfl⟩
  have hcX : ∀ x ∈ X, ∀ i, ∃ y ∈ integralClosure O K₁,
      c x i = (algebraMap O K₁ ϖ) ^ ((e : ℤ) - (be : ℤ)) * y := by
    rintro _ ⟨y, hy, rfl⟩ i
    obtain ⟨u, hu, hcu⟩ := hcM y hy i
    refine ⟨u, hu, ?_⟩
    show c (ϖ ^ e • y) i = _
    rw [← hsm, map_smul, Pi.smul_apply, hcu, Algebra.smul_def, map_pow,
      ← IsScalarTower.algebraMap_apply, ← mul_assoc, sub_eq_add_neg, zpow_add₀ hp1, zpow_natCast]
  obtain ⟨m, hm, hmle⟩ := hQ O K K₁ V ϖ hϖ n c _ hker th hspan X e be hcX hthX a a' ha ha' hdet
  have r1 := reduction X Θ (N₁ ⊔ Z) Tj NK hNΘ hTΘ
  have r2 := levels N' ((X ⊓ NK) ⊔ (N₁ ⊔ Z)) N₁ Z Zm AA AA' N₁' ρ
    (sup_le hXN (sup_le hN₁ (hZ.trans hZm))) hρ hkρ himg
  have r3 : ql X ((X ⊓ NK) ⊔ Tj) = m := hm
  set L1 := Module.length O (↥AA' ⧸ AA.comap AA'.subtype)
  set L2 := Module.length O (↥AA ⧸ N₁'.comap AA.subtype)
  set L3 := Module.length O (↥Zm ⧸ Z.comap Zm.subtype)
  set L := Formalism.LatticeIndexTer.qlen O V (X ⊔ Θ) Θ with hL
  have hLA' : L ≤ L1 + L2 + L3 + ((m : ℕ) : ℕ∞) := by
    rw [← r3]; exact r1.trans (add_le_add r2 le_rfl)
  have hsum : L1 + L2 + L3 + ((m : ℕ) : ℕ∞) =
      ((L1.toNat + L2.toNat + L3.toNat + m : ℕ) : ℕ∞) := by
    rw [← ENat.natCast_toNat hf1, ← ENat.natCast_toNat hf2, ← ENat.natCast_toNat hf3]
    simp only [ENat.toNat_natCast]
    push_cast; rfl
  rw [hsum] at hLA'
  have hLt : L.toNat ≤ L1.toNat + L2.toNat + L3.toNat + m := by
    have hLne : L ≠ ⊤ := ne_top_of_le_ne_top (by simp) hLA'
    rw [← ENat.natCast_toNat hLne] at hLA'
    exact_mod_cast hLA'
  have h5 : ((L.toNat : ℕ) : ℤ) ≤ (L1.toNat : ℤ) + (L2.toNat : ℤ) + (L3.toNat : ℤ) + (m : ℤ) := by
    exact_mod_cast hLt
  have hd : (0 : ℤ) ≤ (finrank K K₁ : ℤ) := Int.natCast_nonneg _
  have h6 := mul_le_mul_of_nonneg_left (hIdx.trans (add_le_add le_rfl h5)) hd
  linarith

theorem localStepExt : LocalStepExt := localStepExt_of quotientLengthExt

end Formalism.LatticeBaseChangeAlt
end

