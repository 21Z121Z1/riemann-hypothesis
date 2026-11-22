import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0034
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0024
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0021
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsNearOfSmul
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.UniformizerValuationHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0033
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0028
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FamilyGramHolds
section
open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

theorem family_gram_holds : FamGram := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  have := h𝔭.isPrime
  obtain ⟨hbU, -, hbo, hbn, ha0⟩ := hba
  obtain ⟨hwW, hwo, hwn, hτ, ⟨s₀, hu⟩, hcong, hunit⟩ := hg
  have hwn1 : ∀ j, h (w j) (w j) = algebraMap F K (c j) := fun j => (hwn j).1
  have hbw : ∀ i j, h (b i) (w j) = 0 := fun i j =>
    LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (hwW j) (b i)) (hbU i))
  have hwb : ∀ i j, h (w j) (b i) = 0 := fun i j => by
    rw [← hs.eq (b i) (w j), hbw]; simp
  have hcP : ∀ i, vF 𝔭 (a i) ≠ 0 → InP 𝔭 (vF 𝔭 (a i)) (algebraMap F K (c (τ i))) := by
    intro i hi
    have h1 : InP 𝔭 (vF 𝔭 (a i)) (algebraMap F K ((a i : F) + c (τ i))) :=
      (hcong i hi).mono (by omega)
    have h2 : InP 𝔭 (vF 𝔭 (a i)) (algebraMap F K ((a i : 𝓞 F) : F)) := inP_vF h𝔭 (ha0 i)
    have e : algebraMap F K (c (τ i)) =
        algebraMap F K ((a i : F) + c (τ i)) + -algebraMap F K ((a i : 𝓞 F) : F) := by
      rw [map_add]; ring
    rw [e]; exact h1.add h2.neg
  have hcS : ∀ j, algebraMap F K (c j) ∈ SP K 𝔭 := by
    intro j
    by_cases hj : ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j
    · obtain ⟨i, hi, rfl⟩ := hj
      exact (hcP i hi).mem_SP
    · push Not at hj
      exact (hunit j fun i hi => hj i hi).1
  have haS : ∀ i, algebraMap F K ((a i : 𝓞 F) : F) ∈ SP K 𝔭 := fun i => by
    rw [← jι_eq']; exact jK_mem_SP _
  have key_ii : ∀ i, h (b i + w (τ i)) (b i + w (τ i)) = algebraMap F K ((a i : F) + c (τ i)) := by
    intro i
    simp only [map_add, LinearMap.add_apply, hbw, hwb, hbn, hwn1]
    ring
  have key_ik : ∀ i k, i ≠ k → vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 →
      h (b i + w (τ i)) (b k + w (τ k)) = 0 := by
    intro i k hik hi hk
    have hτik : τ i ≠ τ k := fun e => hik (hτ i k hi hk e)
    simp only [map_add, LinearMap.add_apply, hbw, hwb, hbo i k hik, hwo _ _ hτik]
    ring
  suffices H : ∀ x y, h (glueFam K 𝔭 b a π w τ x) (glueFam K 𝔭 b a π w τ y) ∈ SP K 𝔭 by
    intro x y; rw [← mem_SP_iff_locF]; exact H x y
  rintro (i | j) (k | l)
  · simp only [glueFam, Sum.elim_inl]
    by_cases hik : i = k
    · subst hik
      by_cases hi : vF 𝔭 (a i) = 0
      · rw [if_pos hi, hbn]; exact haS i
      · rw [if_neg hi, form_smul_smul, key_ii i, star_inv_pow hF, ← pow_add, ← two_mul]
        exact mem_SP_of_inP hu (hcong i hi)
    · by_cases hi : vF 𝔭 (a i) = 0 <;> by_cases hk : vF 𝔭 (a k) = 0
      · rw [if_pos hi, if_pos hk, hbo i k hik]; exact (SP K 𝔭).zero_mem
      · rw [if_pos hi, if_neg hk, form_smul_right, map_add, hbo i k hik, hbw, add_zero, mul_zero]
        exact (SP K 𝔭).zero_mem
      · rw [if_neg hi, if_pos hk, form_smul_left, map_add, LinearMap.add_apply, hbo i k hik, hwb,
          add_zero, mul_zero]
        exact (SP K 𝔭).zero_mem
      · rw [if_neg hi, if_neg hk, form_smul_smul, key_ik i k hik hi hk, mul_zero]
        exact (SP K 𝔭).zero_mem
  · simp only [glueFam, Sum.elim_inl, Sum.elim_inr]
    by_cases hi : vF 𝔭 (a i) = 0
    · rw [if_pos hi, hbw]; exact (SP K 𝔭).zero_mem
    · rw [if_neg hi, form_smul_left, map_add, LinearMap.add_apply, hbw, zero_add, star_inv_pow hF]
      by_cases hj : τ i = l
      · subst hj; rw [hwn1]; exact mem_SP_of_inP hu (hcP i hi)
      · rw [hwo _ _ hj, mul_zero]; exact (SP K 𝔭).zero_mem
  · simp only [glueFam, Sum.elim_inl, Sum.elim_inr]
    by_cases hk : vF 𝔭 (a k) = 0
    · rw [if_pos hk, hwb]; exact (SP K 𝔭).zero_mem
    · rw [if_neg hk, form_smul_right, map_add, hwb, zero_add]
      by_cases hj : τ k = j
      · subst hj; rw [hwn1]; exact mem_SP_of_inP hu (hcP k hk)
      · rw [hwo _ _ (Ne.symm hj), mul_zero]; exact (SP K 𝔭).zero_mem
  · simp only [glueFam, Sum.elim_inr]
    by_cases hjl : j = l
    · subst hjl; rw [hwn1]; exact hcS j
    · rw [hwo _ _ hjl]; exact (SP K 𝔭).zero_mem

end Formalism.L2.SG.Pf.GluingBases
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanIsometryHolds
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

theorem jordanIsom_of (hE : ExactVec) (hR : Rebase) (hL : LocSpan) (hU : UnifVal)
    (hJ : JordSpan) : Formalism.L2.SG.Pf.Cnt.JordanIsom := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hd L L' hLl hLl' 𝔭 h𝔭 b a b' a' hb hb' hv
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  obtain ⟨π, hπ, hval⟩ := hU K F hK hF P hP
  have hda := LocF.aniso_of_totPosDef hd
  obtain ⟨-, hbL, hbo, hbn, hba⟩ := hb
  obtain ⟨-, hbL', hbo', hbn', hba'⟩ := hb'
  have hsp := hJ K F V L hLl _ h𝔭 _ b hbL
  have hsp' := hJ K F V L' hLl' _ h𝔭 _ b' hbL'
  have hS := isHermSemilocal_locRing hK hP
  obtain ⟨g, hg, -, hgm⟩ := core_of_split hs hda
    (splitAt_of (hE K F V hK hF h hs hd P hP π hπ) (hR K V (locRing P) π h hS hπ hs hda))
    _ (Fin _) le_rfl b b' (fun i => vF _ (a i)) 1 hbo hbo'
    (fun i => by rw [hbn i]; exact hval _ (hba i))
    (fun i => by rw [hbn' i, hv i]; exact hval _ (hba' i)) (one_mem _)
    (fun v => by
      rw [hsp, hsp']
      exact ⟨fun _ => Submodule.mem_top, fun _ => Submodule.mem_top⟩)
  refine ⟨g, hg, gmap_eq_of_iff fun v => ?_⟩
  rw [← hbL, ← hbL', locF_eq_loc hK hF hP, locF_eq_loc hK hF hP, hL K F V hK hF P hP,
    hL K F V hK hF P hP]
  exact hgm v

end Formalism.L2.SG.Pf.G3

namespace Formalism.L2.SG.Pf.Cnt

theorem jordan_isometry_holds : JordanIsom :=
  Formalism.L2.SG.Pf.G3.jordanIsom_of Formalism.L2.SG.Pf.TemperedBoundGL3.exact_vector_holds Formalism.L2.SG.Pf.TemperedBoundGL3.rebasing_holds
    Formalism.L2.SG.Pf.G3.local_span_holds Formalism.L2.SG.Pf.TemperedBoundGL3.uniformizer_valuation_holds Formalism.L2.SG.Pf.G3.jordan_span_holds

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LastRescaleOf
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

def LastUnit : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h U M 𝔭 b a →
    cJof 𝔭 a < finrank K (orthK h U) →
    ∀ (π : 𝓞 F) (w : Fin (finrank K (orthK h U)) → V) (c : Fin (finrank K (orthK h U)) → F)
      (τ : Fin (finrank K U) → Fin (finrank K (orthK h U))), IsGlueDataPre h U 𝔭 a π w c τ →
      ∀ j : Fin (finrank K (orthK h U)), (j : ℕ) + 1 = finrank K (orthK h U) →
      ∃ l : K, l ≠ 0 ∧ InP 𝔭 0 (algebraMap F K (c j) * (l * star l)) ∧
        InP 𝔭 0 (algebraMap F K (c j) * (l * star l))⁻¹

theorem lastRescale_of (hL : LastUnit) : LastRescale := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc π w c τ hg
  have hm : 0 < finrank K (orthK h U) := lt_of_le_of_lt (Nat.zero_le _) hc
  set j₀ : Fin (finrank K (orthK h U)) := ⟨finrank K (orthK h U) - 1, by omega⟩ with hj₀
  obtain ⟨l, hl0, hl1, hl2⟩ :=
    hL K F V hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc π w c τ hg j₀ (by simp [j₀]; omega)
  obtain ⟨hwW, hwo, hwn, hτ, hu, hcong, hτl, hunit⟩ := hg
  obtain ⟨μ, hμ⟩ := (hF (l * star l)).1 (by rw [star_mul', star_star, mul_comm])
  have hμ0 : μ ≠ 0 := by
    intro e; rw [e, map_zero] at hμ
    exact mul_ne_zero hl0 (star_ne_zero.2 hl0) hμ.symm
  let w' := Function.update w j₀ (l • w j₀)
  let c' := Function.update c j₀ (μ * c j₀)
  have hw'₀ : w' j₀ = l • w j₀ := Function.update_self _ _ _
  have hw'n : ∀ j, j ≠ j₀ → w' j = w j := fun j hj => Function.update_of_ne hj _ _
  have hc'₀ : c' j₀ = μ * c j₀ := Function.update_self _ _ _
  have hc'n : ∀ j, j ≠ j₀ → c' j = c j := fun j hj => Function.update_of_ne hj _ _
  have hτ₀ : ∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ j₀ := by
    intro i hi e
    have := hτl i hi
    rw [e] at this
    simp [j₀] at this
    omega
  refine ⟨w', c', ⟨?_, ?_, ?_, hτ, hu, ?_, ?_⟩⟩
  · intro j
    by_cases hj : j = j₀
    · rw [hj, hw'₀]; exact Submodule.smul_mem _ _ (hwW j₀)
    · rw [hw'n j hj]; exact hwW j
  · intro j k hjk
    by_cases hj : j = j₀
    · have hk : k ≠ j₀ := fun e => hjk (hj.trans e.symm)
      rw [hj, hw'₀, hw'n k hk, form_smul_left, hwo _ _ (hj ▸ hjk), mul_zero]
    · by_cases hk : k = j₀
      · rw [hk, hw'₀, hw'n j hj, form_smul_right, hwo _ _ (hk ▸ hjk), mul_zero]
      · rw [hw'n j hj, hw'n k hk]; exact hwo j k hjk
  · intro j
    by_cases hj : j = j₀
    · rw [hj, hw'₀, hc'₀, form_smul_smul, (hwn j₀).1, map_mul, hμ]
      refine ⟨by ring, mul_ne_zero hμ0 (hwn j₀).2⟩
    · rw [hw'n j hj, hc'n j hj]; exact hwn j
  · intro i hi
    rw [hc'n _ (hτ₀ i hi)]; exact hcong i hi
  · intro j hnp
    by_cases hj : j = j₀
    · rw [hj, hc'₀]
      refine ⟨?_, ?_⟩
      · rw [map_mul, hμ, mul_comm]; exact hl1
      · rw [map_inv₀, map_mul, hμ, mul_comm]; exact hl2
    · rw [hc'n j hj]
      refine hunit j ?_ hnp
      have h1 := j.isLt
      have h2 : (j : ℕ) ≠ finrank K (orthK h U) - 1 := fun e => hj (Fin.ext e)
      omega

end Formalism.L2.SG.Pf.GluingBases
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LinearIndependentOrth
section
open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem locF_subset_span {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) V) :
    (locF 𝔭 L : Set V) ⊆ Submodule.span K (L : Set V) := by
  intro x hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp L x).1 hx
  have ht0 : algebraMap F K (t : F) ≠ 0 := by
    rw [← jι_eq']; exact jι_ne_zero (ne_zero_of_notMem ht)
  have h1 : algebraMap F K (t : F) • x ∈ Submodule.span K (L : Set V) := by
    rw [← jι_eq', algebraMap_smul]; exact Submodule.subset_span htx
  exact (Submodule.smul_mem_iff _ ht0).1 h1

theorem le_span_of_locF {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {U : Submodule K V}
    {M : Submodule (𝓞 K) V} (hM : IsLatIn U M) {n : ℕ} {b : Fin n → V}
    (hb : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 M) :
    U ≤ Submodule.span K (Set.range b) := by
  rw [← hM.2, Submodule.span_le]
  intro x hx
  have h1 : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) := by
    rw [hb]; exact LocF.le_locF 𝔭 M hx
  have h2 := locF_subset_span hp _ h1
  rwa [Submodule.span_span_of_tower] at h2

theorem linearIndependent_orth {m : ℕ} (h : V →ₗ⋆[K] V →ₗ[K] K) (w : Fin m → V)
    (hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0) (hwn : ∀ j, h (w j) (w j) ≠ 0) :
    LinearIndependent K w := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have h1 := congrArg (h (w k)) hg
  rw [map_sum, map_zero] at h1
  simp only [map_smul, smul_eq_mul] at h1
  rw [Finset.sum_eq_single k (fun j _ hj => by rw [hwo k j (Ne.symm hj), mul_zero])
    (by simp)] at h1
  exact (mul_eq_zero.1 h1).resolve_right (hwn k)

theorem family_top_holds : FamTop := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  have hp := h𝔭.isPrime
  obtain ⟨hbU, hbL, hbo, hbn, ha0⟩ := hba
  obtain ⟨hwW, hwo, hwn, hτ, ⟨s₀, hu⟩, hcong, hunit⟩ := hg
  have hw : ∀ j, w j ∈ Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) :=
    fun j => Submodule.subset_span ⟨Sum.inr j, rfl⟩
  have hb : ∀ i, b i ∈ Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) := by
    intro i
    have hg' : glueFam K 𝔭 b a π w τ (Sum.inl i) ∈
        Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) := Submodule.subset_span ⟨Sum.inl i, rfl⟩
    simp only [glueFam, Sum.elim_inl] at hg'
    by_cases hi : vF 𝔭 (a i) = 0
    · rwa [if_pos hi] at hg'
    · rw [if_neg hi] at hg'
      have h0 : (algebraMap F K (π : F))⁻¹ ^ vF 𝔭 (a i) ≠ 0 := by
        apply pow_ne_zero; apply inv_ne_zero; rw [← jι_eq']; exact jι_ne_zero hu.ne_zero
      have h1 := (Submodule.smul_mem_iff _ h0).1 hg'
      have h2 := Submodule.sub_mem _ h1 (hw (τ i))
      rwa [add_sub_cancel_right] at h2
  have hU : U ≤ Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) :=
    le_trans (le_span_of_locF hp hM hbL) (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb i))
  have hli : LinearIndependent K w := linearIndependent_orth h w hwo fun j => by
    rw [(hwn j).1]; exact (map_ne_zero _).2 (hwn j).2
  have hle : Submodule.span K (Set.range w) ≤ orthK h U :=
    Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hwW j)
  have hfr : finrank K (Submodule.span K (Set.range w)) = finrank K (orthK h U) := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hW : orthK h U ≤ Submodule.span K (Set.range (glueFam K 𝔭 b a π w τ)) :=
    le_trans (Submodule.eq_of_le_of_finrank_eq hle hfr).ge
      (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hw j))
  rw [eq_top_iff, ← hUc.sup_eq_top]
  exact sup_le hU hW

end Formalism.L2.SG.Pf.GluingBases
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocalFormIntegralOnLattice
section
open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section S1

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (L : LocSp D M) (p : PlF D)

theorem local_form_add_right (x y y' : L.V p) : (L.H p).h x (y + y') = (L.H p).h x y + (L.H p).h x y' := by
  rw [(L.H p).h_herm (y + y') x, (L.H p).h_add_left, map_add, ← (L.H p).h_herm y x,
    ← (L.H p).h_herm y' x]

theorem local_form_smul_right (x y : L.V p) (a : (D.s.atP p).Ep) :
    (L.H p).h x (a • y) = (M p).L.cj a * (L.H p).h x y := by
  rw [(L.H p).h_herm (a • y) x, (L.H p).h_smul_left, map_mul, ← (L.H p).h_herm y x]

theorem local_form_zero_left (y : L.V p) : (L.H p).h 0 y = 0 := by
  have h := (L.H p).h_smul_left 0 0 y
  rwa [zero_smul, zero_mul] at h

theorem local_form_zero_right (x : L.V p) : (L.H p).h x 0 = 0 := by
  rw [(L.H p).h_herm 0 x, local_form_zero_left, map_zero]

theorem base_change_smul_integral {δ : ∀ p : PlF D, (D.s.atP p).Fp} (hA : Agree δ M p) (o : 𝓞 D.host.E) (x : (VS D).V) :
    ∃ c ∈ (M p).L.O, L.bc p (o • x) = c • L.bc p x := by
  refine ⟨(D.s.atP p).ιE (o : D.host.E), ?_, ?_⟩
  · rw [hA.2.2.2.1]
    exact PI.CntNotIntW.iE_mem_O D p o
  · rw [← L.bc_smul p (o : D.host.E) x]
    congr 1
    first
    | exact (algebraMap_smul D.host.E o x).symm
    | rfl

theorem local_form_integral_on_lattice (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hcjO : ∀ a ∈ (M p).L.O, (M p).L.cj a ∈ (M p).L.O)
    (hint : ∀ a ∈ Λ, ∀ b ∈ Λ, (L.H p).h (L.bc p a) (L.bc p b) ∈ (M p).L.O)
    {x y : L.V p} (hx : x ∈ lattice₂ L p Λ) (hy : y ∈ lattice₂ L p Λ) : (L.H p).h x y ∈ (M p).L.O := by
  unfold lattice₂ at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx0 =>
    obtain ⟨a, ha, rfl⟩ := hx0
    induction hy using Submodule.span_induction with
    | mem y hy0 =>
      obtain ⟨b, hb, rfl⟩ := hy0
      exact hint a ha b hb
    | zero => rw [local_form_zero_right]; exact (M p).L.O.zero_mem
    | add y y' _ _ h1 h2 => rw [local_form_add_right]; exact add_mem h1 h2
    | smul c y _ h1 =>
      rw [show c • y = (c : (D.s.atP p).Ep) • y from rfl, local_form_smul_right]
      exact mul_mem (hcjO _ c.2) h1
  | zero => rw [local_form_zero_left]; exact (M p).L.O.zero_mem
  | add x x' _ _ h1 h2 => rw [(L.H p).h_add_left]; exact add_mem h1 h2
  | smul c x _ h1 =>
    rw [show c • x = (c : (D.s.atP p).Ep) • x from rfl, (L.H p).h_smul_left]
    exact mul_mem c.2 h1

end S1

set_option maxHeartbeats 1000000 in
theorem local_self_dual_holds : LocSelfDual := by
  intro D δ M hA L p
  have hAp := hA p
  obtain ⟨-, -, hcj, hO, -⟩ := hAp
  have hLat := (VS D).standardTuple_isLattice
  have hU := (VS D).baseLattice_isUnimodular

  have hform : ∀ a b : (VS D).V, (L.H p).h (L.bc p a) (L.bc p b) = (D.s.atP p).ιE ((VS D).hT b a) := by
    intro a b; rw [L.bc_form p]; rfl
  have hcjO : ∀ a ∈ (M p).L.O, (M p).L.cj a ∈ (M p).L.O := by
    intro a ha; rw [hcj, hO] at *; exact LocFacts.lf_cj_mem p a ha

  have hint : ∀ a ∈ (VS D).L0, ∀ b ∈ (VS D).L0, (L.H p).h (L.bc p a) (L.bc p b) ∈ (M p).L.O := by
    intro a ha b hb
    rw [hform]
    have ha' : a ∈ Formalism.E.hdual (VS D).hT (VS D).L0 := by
      have : Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 = (VS D).L0 := hU
      rw [← this] at ha; exact ha
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 ((LocFacts.lf_mem_hdual).1 ha' b hb)
    rw [← ho, hO]
    exact PI.CntNotIntW.iE_mem_O D p o
  refine ⟨?_, ?_, fun x => ⟨fun hx y hy => ?_, fun h => ?_⟩⟩
  ·
    obtain ⟨s, hs⟩ := hLat.fg
    have : lattice₂ L p (VS D).L0 = Submodule.span (M p).L.O (L.bc p '' (s : Set (VS D).V)) := by
      apply le_antisymm
      · rw [lattice₂, Submodule.span_le, ← hs]
        rintro _ ⟨x, hx, rfl⟩
        induction hx using Submodule.span_induction with
        | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
        | zero => simp
        | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
        | smul o y _ hy =>
          obtain ⟨c, hc, he⟩ := base_change_smul_integral L p (hA p) o y
          rw [he]
          exact Submodule.smul_mem _ (⟨c, hc⟩ : (M p).L.O) hy
      · rw [← hs]; exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
    rw [this]
    exact Submodule.fg_span (s.finite_toSet.image _)
  ·
    rw [eq_top_iff, ← L.bc_span p, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span D.host.E ((VS D).L0 : Set (VS D).V) := by rw [hLat.span_eq_top]; trivial
    induction hv using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (Submodule.subset_span ⟨y, hy, rfl⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul a y _ hy => rw [L.bc_smul p]; exact Submodule.smul_mem _ _ hy
  ·
    exact local_form_integral_on_lattice L p _ hcjO hint hx hy
  ·
    obtain ⟨n, g, f, hgf⟩ := Formalism.HermitianLatticesTheory.finitely_generated_projective_coords (K := D.host.E) (VS D).L0 hLat.fg
      (IsFractionRing.injective (𝓞 D.host.E) D.host.E)
    choose μ hμL0 hμ using fun i => LocFacts.lf_riesz_lat hLat hU (f i)
    have hV : ∀ v : (VS D).V, v = ∑ i, (VS D).hT (μ i) v • ((g i : (VS D).L0) : (VS D).V) := by
      let L2 : (VS D).V →ₗ[D.host.E] (VS D).V := ∑ i, ((VS D).hT (μ i)).smulRight ((g i : (VS D).L0) : (VS D).V)
      have hL2 : ∀ v, L2 v = ∑ i, (VS D).hT (μ i) v • ((g i : (VS D).L0) : (VS D).V) := by
        intro v; simp [L2]
      have heq : LinearMap.id = L2 := by
        apply LinearMap.ext_on hLat.span_eq_top
        intro y hy
        have e1 := congrArg (fun z : (VS D).L0 => (z : (VS D).V)) (hgf ⟨y, hy⟩)
        rw [LinearMap.id_apply, hL2]
        refine e1.trans ?_
        rw [Submodule.coe_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Submodule.coe_smul, ← algebraMap_smul D.host.E, hμ i ⟨y, hy⟩]
      intro v
      rw [← hL2, ← heq, LinearMap.id_apply]
    have hVp : ∀ w : L.V p, w = ∑ i, (L.H p).h w (L.bc p (μ i)) • L.bc p ((g i : (VS D).L0) : (VS D).V) := by
      intro w
      have hw : w ∈ Submodule.span (D.s.atP p).Ep (Set.range (L.bc p)) := by rw [L.bc_span p]; trivial
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨v, rfl⟩ := hw
        have e : ∀ i, (L.H p).h (L.bc p v) (L.bc p (μ i)) = (D.s.atP p).ιE ((VS D).hT (μ i) v) := fun i => hform _ _
        simp only [e, ← L.bc_smul p]
        rw [← map_sum, ← hV v]
      | zero => simp [local_form_zero_left]
      | add w w' _ _ h1 h2 =>
        simp only [(L.H p).h_add_left, add_smul, Finset.sum_add_distrib]
        rw [← h1, ← h2]
      | smul a w _ h1 =>
        simp only [(L.H p).h_smul_left, mul_smul]
        rw [← Finset.smul_sum, ← h1]
    have hmem : (∑ i, (L.H p).h x (L.bc p (μ i)) • L.bc p ((g i : (VS D).L0) : (VS D).V)) ∈ lattice₂ L p (VS D).L0 := by
      refine Submodule.sum_mem _ fun i _ => ?_
      have hc : (L.H p).h x (L.bc p (μ i)) ∈ (M p).L.O := h _ (Submodule.subset_span ⟨μ i, hμL0 i, rfl⟩)
      have hg : L.bc p ((g i : (VS D).L0) : (VS D).V) ∈ lattice₂ L p (VS D).L0 := Submodule.subset_span ⟨_, (g i).2, rfl⟩
      exact Submodule.smul_mem _ (⟨_, hc⟩ : (M p).L.O) hg
    have hxe := hVp x
    rw [← hxe] at hmem
    exact hmem

end Formalism.L2.SG.Pf.Cnt
end
end

