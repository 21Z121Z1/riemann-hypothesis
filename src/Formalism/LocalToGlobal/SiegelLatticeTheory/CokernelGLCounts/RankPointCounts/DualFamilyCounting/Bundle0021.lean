import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0017
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0015
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0018
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0027
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXECPfC

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FibSEqSingleton
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

private lemma mem_locF_lemma (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ locF 𝔭 L ↔ ∃ s ∈ Submonoid.closure
      {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}, s • x ∈ L := Iff.rfl

private lemma locF_inf_restrictScalars (X : Submodule K V) (Λ : Submodule (𝓞 K) V) {𝔭 : Ideal (𝓞 F)}
    (hp : 𝔭.IsPrime) :
    locF 𝔭 (Λ ⊓ X.restrictScalars (𝓞 K)) = locF 𝔭 Λ ⊓ X.restrictScalars (𝓞 K) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 _ x).mp hx
    refine Submodule.mem_inf.mpr ⟨(mem_locF_lemma 𝔭 _ x).mpr ⟨s, hs, hsx.1⟩, ?_⟩
    rw [← Formalism.L2.SG.Pf.G7.locF_subspace X hp]
    exact (mem_locF_lemma 𝔭 _ x).mpr ⟨s, hs, hsx.2⟩
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 _ x).mp hx1
    exact (mem_locF_lemma 𝔭 _ x).mpr
      ⟨s, hs, Submodule.mem_inf.mpr ⟨hsx, (X.restrictScalars (𝓞 K)).smul_mem s hx2⟩⟩

theorem locF_mem_fibS (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}
    {M T Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) (hu : Formalism.HermitianLatticesTheory.IsUnimodular h Λ)
    (hM : Λ ⊓ U.restrictScalars (𝓞 K) = M) (hT : Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = T)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : locF 𝔭 Λ ∈ fibS h U 𝔭 M T := by
  have hu' : Formalism.HermitianLatticesTheory.dual h Λ = Λ := hu
  simp only [fibS, Set.mem_setOf_eq]
  refine ⟨⟨Λ, hΛ, rfl⟩, ?_, ?_, ?_⟩
  · rw [← Formalism.L2.SG.Pf.G7.locF_dual hF h hΛ.fg h𝔭.isPrime, hu']
  · rw [← hM, locF_inf_restrictScalars U Λ h𝔭.isPrime]
  · rw [← hT, locF_inf_restrictScalars (orthK h U) Λ h𝔭.isPrime]

theorem fibS_eq_singleton (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}
    (hUc : IsCompl U (orthK h U)) {M T Λ₀ : Submodule (𝓞 K) V} (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) (hΛ₀ : Submodule.IsLattice K Λ₀) (hu : Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (he : locF 𝔭 (M ⊔ T) = locF 𝔭 Λ₀) :
    fibS h U 𝔭 M T = {locF 𝔭 (M ⊔ T)} := by
  have hu' : Formalism.HermitianLatticesTheory.dual h Λ₀ = Λ₀ := hu
  have hN : dualF h 𝔭 (locF 𝔭 (M ⊔ T)) = locF 𝔭 (M ⊔ T) := by
    rw [he, ← Formalism.L2.SG.Pf.G7.locF_dual hF h hΛ₀.fg h𝔭.isPrime, hu']
  have hMU : ∀ x ∈ M, x ∈ U := fun x hx => hM.2 ▸ Submodule.subset_span hx
  have hTW : ∀ x ∈ T, x ∈ orthK h U := fun x hx => hT.2 ▸ Submodule.subset_span hx
  have hcapU : locF 𝔭 (M ⊔ T) ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M :=
    locF_sup_inf hUc hMU hTW h𝔭.isPrime
  have hcapW : locF 𝔭 (M ⊔ T) ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T := by
    rw [sup_comm]; exact locF_sup_inf hUc.symm hTW hMU h𝔭.isPrime
  ext Λ
  simp only [fibS, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨Λ₁, hΛ₁, rfl⟩, hd, hcU, hcW⟩
    have hle : locF 𝔭 (M ⊔ T) ≤ locF 𝔭 Λ₁ := by
      intro x hx
      obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 _ x).mp hx
      obtain ⟨m, hm, t, ht, hmt⟩ := Submodule.mem_sup.mp hsx
      have hm' : m ∈ locF 𝔭 Λ₁ := by
        have hm1 : m ∈ locF 𝔭 M :=
          (mem_locF_lemma 𝔭 _ m).mpr ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩
        rw [← hcU] at hm1
        exact (Submodule.mem_inf.mp hm1).1
      have ht' : t ∈ locF 𝔭 Λ₁ := by
        have ht1 : t ∈ locF 𝔭 T :=
          (mem_locF_lemma 𝔭 _ t).mpr ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩
        rw [← hcW] at ht1
        exact (Submodule.mem_inf.mp ht1).1
      have hsx' : s • x ∈ locF 𝔭 Λ₁ := by rw [← hmt]; exact add_mem hm' ht'
      obtain ⟨s', hs', h'⟩ := (mem_locF_lemma 𝔭 _ _).mp hsx'
      exact (mem_locF_lemma 𝔭 _ x).mpr
        ⟨s' * s, Submonoid.mul_mem _ hs' hs, by rw [mul_smul]; exact h'⟩
    refine le_antisymm ?_ hle
    calc locF 𝔭 Λ₁ = dualF h 𝔭 (locF 𝔭 Λ₁) := hd.symm
      _ ≤ dualF h 𝔭 (locF 𝔭 (M ⊔ T)) := dualF_anti h 𝔭 hle
      _ = locF 𝔭 (M ⊔ T) := hN
  · rintro rfl
    exact ⟨⟨Λ₀, hΛ₀, he.symm⟩, hN, hcapU, hcapW⟩

theorem card_glue (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {U : Submodule K V} (hUc : IsCompl U (orthK h U)) {M : Submodule (𝓞 K) V} (hM : IsLatIn U M)
    {Λ₀ : Submodule (𝓞 K) V} (hΛ₀ : Λ₀ ∈ GlueSet h U M) {T : Submodule (𝓞 K) V}
    (hT : IsLatIn (orthK h U) T) :
    Nat.card {Λ : Submodule (𝓞 K) V // Λ ∈ GlueSet h U M ∧ Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = T} =
      ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, fibP h U 𝔭.1 M T := by
  classical
  have hN := isLattice_sup hUc hM hT
  obtain ⟨s, hs⟩ := exists_locF_eq (F := F) hN hΛ₀.1
  have hsing : ∀ 𝔭 ∉ s, fibS h U 𝔭.1 M T = {locF 𝔭.1 (M ⊔ T)} := fun 𝔭 h𝔭 =>
    fibS_eq_singleton hF hUc hM hT hΛ₀.1 hΛ₀.2.1 𝔭.2 (hs 𝔭 h𝔭)
  have hone : ∀ 𝔭 ∉ s, fibP h U 𝔭.1 M T = 1 := by
    intro 𝔭 h𝔭
    rw [fibP_eq, hsing 𝔭 h𝔭]
    simp
  rw [tprod_eq_prod hone, ← Finset.prod_coe_sort s]
  simp only [fibP_eq]
  rw [← Nat.card_pi]
  refine Nat.card_congr (Equiv.ofBijective
    (fun Λ 𝔭 => ⟨locF 𝔭.1.1 Λ.1, locF_mem_fibS hF Λ.2.1.1 Λ.2.1.2.1 Λ.2.1.2.2 Λ.2.2 𝔭.1.2⟩) ⟨?_, ?_⟩)
  · rintro ⟨Λ₁, h1⟩ ⟨Λ₂, h2⟩ he
    apply Subtype.ext
    show Λ₁ = Λ₂
    refine G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_
    by_cases hps : (⟨𝔭, h𝔭⟩ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) ∈ s
    · exact congrArg Subtype.val (congrFun he ⟨_, hps⟩)
    · have a1 := locF_mem_fibS hF h1.1.1 h1.1.2.1 h1.1.2.2 h1.2 h𝔭
      have a2 := locF_mem_fibS hF h2.1.1 h2.1.2.1 h2.1.2.2 h2.2 h𝔭
      rw [hsing _ hps, Set.mem_singleton_iff] at a1 a2
      exact a1.trans a2.symm
  · intro τ
    obtain ⟨Λ, ⟨hΛ, hin, hout⟩, -⟩ := exists_unique_patch hK hF hN s
      (fun 𝔭 => if hp : 𝔭 ∈ s then (τ ⟨𝔭, hp⟩).1 else ⊥) (by
        intro 𝔭 hp
        simp only [dif_pos hp]
        obtain ⟨⟨A, hA, e⟩, -, -, -⟩ := (τ ⟨𝔭, hp⟩).2
        exact ⟨by rw [← e, LocF.locF_idem], A, hA, e⟩)
    have hfib : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, locF 𝔭.1 Λ ∈ fibS h U 𝔭.1 M T := by
      intro 𝔭
      by_cases hp : 𝔭 ∈ s
      · rw [hin 𝔭 hp, dif_pos hp]
        exact (τ ⟨𝔭, hp⟩).2
      · rw [hout 𝔭 hp, hsing 𝔭 hp]
        exact Set.mem_singleton _
    have hmem : Λ ∈ GlueSet h U M ∧ Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = T := by
      refine ⟨⟨hΛ, ?_, ?_⟩, ?_⟩
      · show Formalism.HermitianLatticesTheory.dual h Λ = Λ
        refine G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_
        rw [G7.locF_dual hF h hΛ.fg h𝔭.isPrime]
        exact (hfib ⟨𝔭, h𝔭⟩).2.1
      · refine G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_
        rw [LIOrb.locF_inf_locF h𝔭, G7.locF_subspace U h𝔭.isPrime]
        exact (hfib ⟨𝔭, h𝔭⟩).2.2.1
      · refine G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_
        rw [LIOrb.locF_inf_locF h𝔭, G7.locF_subspace (orthK h U) h𝔭.isPrime]
        exact (hfib ⟨𝔭, h𝔭⟩).2.2.2
    refine ⟨⟨Λ, hmem⟩, ?_⟩
    funext 𝔭
    apply Subtype.ext
    show locF 𝔭.1.1 Λ = (τ 𝔭).1
    rw [hin 𝔭.1 𝔭.2, dif_pos 𝔭.2]

end Formalism.L2.SG.Pf.G8
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IncOInjective
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

section Transport

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def resF (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V) : W →ₗ⋆[K] W →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => h x y)
    (fun x x' y => by simp) (fun c x y => by simp) (fun x y y' => by simp) (fun c x y => by simp)

@[simp] theorem resF_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V) (x y : W) :
    resF h W x y = h x y := rfl

abbrev incO (W : Submodule K V) : W →ₗ[𝓞 K] V := W.subtype.restrictScalars (𝓞 K)

abbrev latW (W : Submodule K V) (T : Submodule (𝓞 K) V) : Submodule (𝓞 K) W := T.comap (incO W)

theorem map_latW {W : Submodule K V} {T : Submodule (𝓞 K) V} (hT : IsLatIn W T) :
    (latW W T).map (incO W) = T := by
  rw [Submodule.map_comap_eq, inf_eq_right]
  intro x hx
  exact ⟨⟨x, hT.2 ▸ Submodule.subset_span hx⟩, rfl⟩

theorem incO_injective (W : Submodule K V) : Function.Injective (incO W) := Subtype.val_injective

theorem isLattice_latW {W : Submodule K V} {T : Submodule (𝓞 K) V} (hT : IsLatIn W T) :
    Submodule.IsLattice K (latW W T) := by
  refine ⟨Submodule.fg_of_fg_map_injective _ (incO_injective W) (by rw [map_latW hT]; exact hT.1), ?_⟩
  apply Submodule.map_injective_of_injective (f := W.subtype) Subtype.val_injective
  have himg : (Subtype.val '' ((latW W T : Submodule (𝓞 K) W) : Set W)) = (T : Set V) := by
    have e := congrArg (fun S : Submodule (𝓞 K) V => (S : Set V)) (map_latW hT)
    simpa [Submodule.map_coe] using e
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, Submodule.coe_subtype, himg, hT.2]

private lemma mem_of_algebraMap_smul_mem (W : Submodule K V) {t : 𝓞 F} (ht : t ≠ 0) {x : V}
    (h : algebraMap (𝓞 F) (𝓞 K) t • x ∈ W) : x ∈ W := by
  have hs : algebraMap (𝓞 F) (𝓞 K) t ≠ 0 := fun h0 =>
    ht (NumberField.RingOfIntegers.algebraMap.injective F K (h0.trans (map_zero _).symm))
  have hsK : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
    rw [← NumberField.RingOfIntegers.coe_eq_algebraMap]
    exact_mod_cast hs
  rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) x] at h
  have h2 := W.smul_mem (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ hsK, one_smul] at h2

private lemma map_incO_locF (W : Submodule K V) (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime]
    (A : Submodule (𝓞 K) W) : (locF 𝔭 A).map (incO W) = locF 𝔭 (A.map (incO W)) := by
  ext x
  simp only [Submodule.mem_map, Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF]
  constructor
  · rintro ⟨y, ⟨t, ht, hy⟩, rfl⟩
    exact ⟨t, ht, _, hy, by simp⟩
  · rintro ⟨t, ht, z, hz, hzx⟩
    have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ 𝔭.zero_mem)
    have hxW : x ∈ W := by
      apply mem_of_algebraMap_smul_mem W ht0
      rw [← hzx]
      exact z.2
    refine ⟨⟨x, hxW⟩, ⟨t, ht, ?_⟩, rfl⟩
    convert hz using 1
    exact Subtype.ext hzx.symm

theorem locF_latW {W : Submodule K V} {T : Submodule (𝓞 K) V} (hT : IsLatIn W T) (𝔭 : Ideal (𝓞 F))
    [𝔭.IsPrime] : (locF 𝔭 (latW W T)).map (incO W) = locF 𝔭 T := by
  rw [map_incO_locF, map_latW hT]

theorem isJordanIn_res {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {T : Submodule (𝓞 K) V}
    (hT : IsLatIn W T) {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {b : Fin (finrank K W) → V} {a : Fin (finrank K W) → 𝓞 F}
    (hb : IsJordanIn h W T 𝔭 b a) :
    IsJordanIn (resF h W) ⊤ (latW W T) 𝔭
      (fun i => ⟨b (finCongr (finrank_top K W) i), hb.1 _⟩) (fun i => a (finCongr (finrank_top K W) i)) := by
  obtain ⟨hbW, hloc, horth, hdiag, hne⟩ := hb
  refine ⟨fun i => Submodule.mem_top, ?_, ?_, ?_, fun i => hne _⟩
  · apply Submodule.map_injective_of_injective (incO_injective W)
    have himg : ⇑(incO W) '' Set.range (fun i : Fin (finrank K (⊤ : Submodule K W)) =>
        (⟨b (finCongr (finrank_top K W) i), hbW _⟩ : W)) = Set.range b := by
      ext v
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨_, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨_, ⟨(finCongr (finrank_top K W)).symm i, rfl⟩, by simp⟩
    rw [map_incO_locF, locF_latW hT, Submodule.map_span, himg, hloc]
  · intro i j hij
    simp only [resF_apply]
    exact horth _ _ ((finCongr (finrank_top K W)).injective.ne hij)
  · intro i
    simp only [resF_apply]
    exact hdiag _

end Transport

end Formalism.L2.SG.Pf.G8
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanSpanHolds
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

theorem local_span_holds : LocSpan := by
  intro K F V _ _ _ _ _ _ _ _ _ _ hK hF P hP n b v
  have hPp := hP.isPrime
  constructor
  · intro hv
    obtain ⟨s, hs, hsv⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hv
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hsv
    have hs0 := algebraMap_ne_zero_of_mem_hcompl hPp hs
    refine ⟨fun i => algebraMap (𝓞 K) K (c i) / algebraMap (𝓞 K) K s,
      fun i => div_mem_locRing hPp (c i) hs, ?_⟩
    have e : v = (algebraMap (𝓞 K) K s)⁻¹ • (algebraMap (𝓞 K) K s • v) := by
      rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [e, algebraMap_smul, ← hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K (c i) (b i), smul_smul]
    simp only [div_eq_inv_mul]
  · rintro ⟨d, hd, rfl⟩
    refine Submodule.sum_mem _ fun i _ => smul_mem_loc hPp (hd i) ?_
    exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem jordan_span_holds : JordSpan := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ L hL 𝔭 h𝔭 n b hb
  rw [eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
  intro x hx
  have hx' : x ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) := by
    rw [hb]
    exact LocF.le_locF 𝔭 L hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ x).mp hx'
  have ht0 : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
    intro h0
    apply ht
    have h1 : algebraMap (𝓞 F) (𝓞 K) t = 0 :=
      FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero])
    have h2 : t = 0 := FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K) (by rw [h1, map_zero])
    rw [h2]
    exact 𝔭.zero_mem
  have hmem := Submodule.span_le_restrictScalars (𝓞 K) K (Set.range b) htx
  have e : x = (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ •
      (algebraMap (𝓞 F) (𝓞 K) t • x) := by
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) x, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ hmem

end Formalism.L2.SG.Pf.G3
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemSpanIffSpanS
section
open Module

noncomputable section

namespace Formalism.L2.SG.Pf.G3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

section

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem spanS_smul_mem {ι : Type} [Fintype ι] {b : ι → V} {a : K} (ha : a ∈ S) {v : V}
    (hv : v ∈ spanS S b) : a • v ∈ spanS S b := by
  obtain ⟨c, hc, rfl⟩ := hv
  refine Exists.intro (fun i => a * c i) ⟨fun i => S.mul_mem ha (hc i), ?_⟩
  simp only [Finset.smul_sum, smul_smul]

theorem form_sum_orth {ι : Type} [Fintype ι] {b : ι → V} (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (c : ι → K) (i : ι) : h (b i) (∑ j, c j • b j) = c i * h (b i) (b i) := by
  simp only [map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single i (fun j _ hji => by rw [ho i j (Ne.symm hji), mul_zero])
    (fun hi => absurd (Finset.mem_univ i) hi)]

theorem mem_spanS_iff_sub {ι : Type} [Fintype ι] [DecidableEq ι] {b : ι → V}
    (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) {i₀ : ι} (h0 : h (b i₀) (b i₀) ≠ 0) (T : Subring K)
    (v : V) : (v ∈ spanS T b ∧ h (b i₀) v = 0) ↔
      v ∈ spanS T (fun j : {i // i ≠ i₀} => b j) := by
  constructor
  · rintro ⟨⟨c, hc, rfl⟩, hv⟩
    have hci : c i₀ = 0 := by
      rw [form_sum_orth ho c i₀] at hv
      exact (mul_eq_zero.mp hv).resolve_right h0
    refine Exists.intro (fun j => c j) ⟨fun j => hc j, ?_⟩
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀, hci, zero_smul, zero_add]
  · rintro ⟨d, hd, rfl⟩
    refine ⟨Exists.intro (fun i => if hi : i = i₀ then 0 else d ⟨i, hi⟩) ⟨fun i => ?_, ?_⟩, ?_⟩
    · dsimp only
      split_ifs
      exacts [T.zero_mem, hd _]
    · rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀]
      dsimp only
      rw [dif_pos rfl, zero_smul, zero_add]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [dif_neg j.2]
    · rw [map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_smul, ho i₀ j (Ne.symm j.2), smul_zero]

theorem mem_span_iff_spanS {ι : Type} [Fintype ι] (b : ι → V) (v : V) :
    v ∈ Submodule.span K (Set.range b) ↔ v ∈ spanS (⊤ : Subring K) b := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    exact Exists.intro c ⟨fun _ => Subring.mem_top _, rfl⟩
  · rintro ⟨c, _, rfl⟩
    exact ⟨c, rfl⟩

theorem mem_cutW_span_iff {ι : Type} [Fintype ι] [DecidableEq ι] {b : ι → V}
    (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) {i₀ : ι} (h0 : h (b i₀) (b i₀) ≠ 0) (v : V) :
    v ∈ cutW h (Submodule.span K (Set.range b)) (b i₀) ↔
      v ∈ Submodule.span K (Set.range (fun j : {i // i ≠ i₀} => b j)) := by
  simp only [cutW, Submodule.mem_inf, LinearMap.mem_ker]
  rw [mem_span_iff_spanS, mem_span_iff_spanS]
  exact mem_spanS_iff_sub ho h0 ⊤ v

theorem mem_cutM_spanS_iff {ι : Type} [Fintype ι] [DecidableEq ι] {b : ι → V}
    (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0) {i₀ : ι} (h0 : h (b i₀) (b i₀) ≠ 0) (v : V) :
    v ∈ cutM h (spanS S b) (b i₀) ↔ v ∈ spanS S (fun j : {i // i ≠ i₀} => b j) := by
  simp only [cutM, AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup, LinearMap.mem_ker]
  exact mem_spanS_iff_sub ho h0 S v

theorem coef_mem {ι : Type} [Fintype ι] {b : ι → V} (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    {i₀ : ι} (h0 : h (b i₀) (b i₀) ≠ 0) {m : V} (hm : m ∈ spanS S b) :
    h (b i₀) m * (h (b i₀) (b i₀))⁻¹ ∈ S := by
  obtain ⟨c, hc, rfl⟩ := hm
  rw [form_sum_orth ho c i₀, mul_inv_cancel_right₀ h0]
  exact hc i₀

theorem mem_iff_of_cut' {M N : AddSubgroup V} (hMs : ∀ a ∈ S, ∀ m ∈ M, a • m ∈ M)
    (hNs : ∀ a ∈ S, ∀ m ∈ N, a • m ∈ N) {x X : V} (hx : x ∈ M) (hX : X ∈ N)
    (hMx : ∀ m ∈ M, h x m * (h x x)⁻¹ ∈ S) (hNX : ∀ m ∈ N, h X m * (h X X)⁻¹ ∈ S)
    {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (hgx : g x = X) (hxx : h x x ≠ 0)
    (hcut : ∀ v, v ∈ cutM h M x ↔ g v ∈ cutM h N X) : ∀ v, v ∈ M ↔ g v ∈ N := by
  have hcut' : ∀ v, (v ∈ M ∧ h x v = 0) ↔ (g v ∈ N ∧ h X (g v) = 0) := by
    intro v
    have := hcut v
    simp only [cutM, AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup, LinearMap.mem_ker] at this
    exact this
  have hiso : ∀ u w, h (g u) (g w) = h u w := hg
  have hXX : h X X ≠ 0 := by
    rw [← hgx, hiso x x]
    exact hxx
  intro v
  constructor
  · intro hv
    have hαS : h x v * (h x x)⁻¹ ∈ S := hMx v hv
    have h1 : v - (h x v * (h x x)⁻¹) • x ∈ M := M.sub_mem hv (hMs _ hαS x hx)
    have h2 : h x (v - (h x v * (h x x)⁻¹) • x) = 0 := by
      rw [map_sub, map_smul, smul_eq_mul, inv_mul_cancel_right₀ hxx, sub_self]
    obtain ⟨h3, -⟩ := (hcut' _).mp ⟨h1, h2⟩
    rw [map_sub, map_smul, hgx] at h3
    have := N.add_mem h3 (hNs _ hαS X hX)
    rwa [sub_add_cancel] at this
  · intro hv
    have hβS : h X (g v) * (h X X)⁻¹ ∈ S := hNX _ hv
    have h1 : g (v - (h X (g v) * (h X X)⁻¹) • x) ∈ N := by
      rw [map_sub, map_smul, hgx]
      exact N.sub_mem hv (hNs _ hβS X hX)
    have h2 : h X (g (v - (h X (g v) * (h X X)⁻¹) • x)) = 0 := by
      rw [map_sub, map_smul, hgx, map_sub, map_smul, smul_eq_mul, inv_mul_cancel_right₀ hXX,
        sub_self]
    obtain ⟨h3, -⟩ := (hcut' _).mpr ⟨h1, h2⟩
    have := M.add_mem h3 (hMs _ hβS x hx)
    rwa [sub_add_cancel] at this

end

end Formalism.L2.SG.Pf.G3
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXECPf
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.EC

open Formalism.QuantumDeterminants WlocSk.NB

theorem expChart_of (hS : ShearStep) (hC : ConstStep) : ExpChart := by
  intro k r
  obtain ⟨σ, hσ, hσe⟩ := hS k r
  obtain ⟨Λ, hΛm, hΛ, hvol⟩ := hC k r
  have hE := Formalism.MainNotions.BridgeCSB.continuous_expLie (k := k) (r := r) (Nset k r)
  let Φ : (CI k r → ℂ) × (Fin r → ℝ) → Mt k r := fun t => phi0 t.1 t.2
  have hφ : Continuous Φ := continuous_nilpotent_chart
  unfold Formalism.MainNotions.S.haarLie
  rw [one_smul, hvol, Measure.map_smul, Measure.map_map hE.measurable hΛm, ← hσ.map_eq]
  congr 1
  have e : ((fun x : Formalism.MainNotions.S.lieE (Nset k r) => fun i j =>
      NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) i j) ∘ Λ : (J k r → ℝ) → Mt k r) = Φ ∘ σ := by
    funext y
    simp only [Function.comp, Φ]
    rw [hσe y, hΛ y, Formalism.MainNotions.BridgeCSB.unrealify_RL]
  rw [e]
  exact (Measure.map_map hφ.measurable hσ.measurable).symm

end Formalism.L2.SG.Pf.NcReal.JX.EC

namespace Formalism.L2.SG.Pf.NcReal.JX

theorem exponential_chart_haar : ExpChart := EC.expChart_of EC.shear_change_holds EC.constant_change_holds

end Formalism.L2.SG.Pf.NcReal.JX
end
end

