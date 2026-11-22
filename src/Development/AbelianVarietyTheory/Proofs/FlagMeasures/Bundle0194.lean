import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0170
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0060
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0167
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryOpNormBoundedByTwoFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeNonzeroVectorPairNormalForms
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMap
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnimodularTraceOnMiddleSpaceLift
section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

noncomputable section

open Formalism.HermitianLatticeCounting.P

namespace GlobalTheory.DegCnt.WnLat

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)

def pr : V →ₗ[K] V := LinearMap.id - NFGeom.proj N

theorem pr_add (x : V) : pr N x + NFGeom.proj N x = x := by simp [pr]

theorem Wn_perp_Ist {y : V} (hy : y ∈ N.Wn) : ∀ u ∈ N.Ist, H.B y u = 0 :=
  (mem_perp_iff H _ _).1 ((NFGeom.mem_perp_sup _ _ _).1 hy).2

theorem Wn_perp_II {y : V} (hy : y ∈ N.Wn) {x : V} (hx : x ∈ II N.F N.F') : H.B y x = 0 :=
  (mem_perp_iff H _ _).1 ((NFGeom.mem_perp_sup _ _ _).1 hy).1 x (Submodule.mem_sup_left hx.1)

theorem pr_of_Wn {y : V} (hy : y ∈ N.Wn) : pr N y = y := by
  simp [pr, NFGeom.proj_zero N (Wn_perp_Ist N hy)]

theorem pr_II {x : V} (hx : x ∈ II N.F N.F') : pr N x = 0 := by
  simp [pr, NFGeom.proj_II N hx]

theorem pr_mem_Wn {x : V} (hx : x ∈ uPerp N.F N.F') : pr N x ∈ N.Wn :=
  (NFGeom.mem_perp_sup _ _ _).2
    ⟨Submodule.sub_mem _ hx (NFGeom.II_le_uPerp N (NFGeom.proj_mem N x)), NFGeom.sub_proj_perp N x⟩

theorem Wn_le_uPerp : N.Wn ≤ uPerp N.F N.F' := by
  rw [NFGeom.uPerp_eq N]; exact le_sup_left

theorem orthogonal_perp_z {w : V} (hw : w ∈ N.Wt) : H.B w N.F.z = 0 :=
  (mem_perp_iff H _ _).1 ((NFGeom.mem_perp_sup _ _ _).1 hw).1 _ (lastVector_mem_jointSpan_left N.F N.F')

theorem zz : H.B N.F.z N.F.z = -N.F.T := N.F.zz

theorem nondeg_Wn [FiniteDimensional K V] (x : V) (hx : x ∈ N.Wn) (h : ∀ y ∈ N.Wn, H.B x y = 0) :
    x = 0 := by
  have hx' := hx
  rw [NFGeom.Wn_eq N, Submodule.mem_sup] at hx'
  obtain ⟨w, hw, u, hu, rfl⟩ := hx'
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hu
  have hz := h _ (NFGeom.z_mem_Wn N)
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, orthogonal_perp_z N hw,
    zz] at hz
  have ht : t = 0 := by
    have := N.F.hT
    simp at hz
    exact hz.resolve_right this
  subst ht
  simp only [zero_smul, add_zero] at h ⊢
  by_contra h0
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hwW : w ∈ N.Wn := by rw [NFGeom.Wn_eq N]; exact Submodule.mem_sup_left hw
  have := NFGeom.Wt_pos N σ hw h0
  rw [h w hwW] at this
  simp at this

theorem z_ne : N.F.z ≠ 0 := fun h => N.F.hT (by
  have := zz N
  rw [h] at this
  simpa using this.symm)

theorem hermFramePair_middleSpace_inf_span_z_eq_bot : N.Wt ⊓ Submodule.span K {N.F.z} = ⊥ :=
  eq_bot_iff.2 fun x hx => (Submodule.mem_bot K).2 <| by
    obtain ⟨hw, hz⟩ := hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have h := orthogonal_perp_z N hw
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, zz] at h
    have := N.F.hT
    rcases mul_eq_zero.1 h with h1 | h1
    · simp [h1]
    · exact absurd (neg_eq_zero.1 h1) this

theorem finrank_Wn [FiniteDimensional K V] : Module.finrank K N.Wn + 2 * r = Module.finrank K V := by
  have h1 := NFGeom.finrank_Wt N
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq N.Wt (Submodule.span K {N.F.z})
  rw [hermFramePair_middleSpace_inf_span_z_eq_bot, finrank_bot, finrank_span_singleton (z_ne N), ← NFGeom.Wn_eq N] at h2
  omega

def hW [FiniteDimensional K V] : HermSpace K N.Wn where
  B := H.B.domRestrict₁₂ N.Wn N.Wn
  herm x y := H.herm x y
  nondeg x hx := Submodule.coe_eq_zero.1 (nondeg_Wn N x x.2 fun y hy => hx ⟨y, hy⟩)

theorem hW_B [FiniteDimensional K V] (x y : N.Wn) : (hW N).B x y = H.B x y := rfl

end GlobalTheory.DegCnt.WnLat

namespace GlobalTheory.DegCnt.WnLat

open Formalism.HermitianLatticeCounting.P

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)

theorem unimod (L : Submodule (𝓞 K) V) (hL : IsUnimodMod H L (uPerp N.F N.F') (II N.F N.F')) :
    GlobalTheory.HermLat.IsUnimod (hW N) (L.comap (N.Wn.subtype.restrictScalars (𝓞 K))) := by
  obtain ⟨⟨⟨N0, hN0, hLeq⟩, hspanL⟩, hdL⟩ := hL
  set M := L.comap (N.Wn.subtype.restrictScalars (𝓞 K)) with hM
  have hIL : ∀ x ∈ II N.F N.F', x ∈ L := fun x hx => by
    rw [hLeq]; exact Submodule.mem_sup_right hx
  have hprL : ∀ x ∈ L, pr N x ∈ L := fun x hx => by
    have : pr N x = x - NFGeom.proj N x := by simp [pr]
    rw [this]; exact L.sub_mem hx (hIL _ (NFGeom.proj_mem N x))
  have hprW : ∀ x ∈ L, pr N x ∈ N.Wn := fun x hx => by
    refine pr_mem_Wn N ?_
    rw [← hspanL]; exact Submodule.subset_span hx
  have hS : L ⊓ rs (𝓞 K) N.Wn = N0.map ((pr N).restrictScalars (𝓞 K)) := by
    apply le_antisymm
    · rintro x ⟨hxL, hxW⟩
      have hxL' := hxL
      rw [hLeq] at hxL'
      obtain ⟨n, hn, i, hi, rfl⟩ := Submodule.mem_sup.1 hxL'
      refine ⟨n, hn, ?_⟩
      show pr N n = n + i
      have h1 : pr N (n + i) = n + i := pr_of_Wn N hxW
      rwa [map_add, pr_II N hi, add_zero] at h1
    · rintro _ ⟨n, hn, rfl⟩
      have hnL : n ∈ L := by rw [hLeq]; exact Submodule.mem_sup_left hn
      exact ⟨hprL n hnL, hprW n hnL⟩
  have hmap : M.map (N.Wn.subtype.restrictScalars (𝓞 K)) = L ⊓ rs (𝓞 K) N.Wn := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨hy, y.2⟩
    · rintro ⟨hxL, hxW⟩; exact ⟨⟨x, hxW⟩, hxL, rfl⟩
  have hfg : M.FG := by
    refine Submodule.fg_of_fg_map_injective (N.Wn.subtype.restrictScalars (𝓞 K)) Subtype.val_injective ?_
    rw [hmap, hS]; exact hN0.map _
  have hspan : Submodule.span K (M : Set N.Wn) = ⊤ := by
    apply Submodule.map_injective_of_injective (f := N.Wn.subtype) Subtype.val_injective
    rw [Submodule.map_span, Submodule.map_subtype_top]
    apply le_antisymm
    · rw [Submodule.span_le]; rintro _ ⟨y, _, rfl⟩; exact y.2
    · intro w hw
      have h1 : w ∈ Submodule.span K (L : Set V) := by rw [hspanL]; exact Wn_le_uPerp N hw
      have h2 : pr N w ∈ (Submodule.span K (L : Set V)).map (pr N) := Submodule.mem_map_of_mem h1
      rw [Submodule.map_span, pr_of_Wn N hw] at h2
      refine Submodule.span_mono ?_ h2
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨pr N x, hprW x hx⟩, hprL x hx, rfl⟩
  have hdual : dual (hW N) M = M := by
    ext y
    rw [mem_dual_iff, hspan]
    simp only [Submodule.mem_top, true_and]
    constructor
    · intro h
      show (y : V) ∈ L
      rw [← hdL, mem_dual_iff, hspanL]
      refine ⟨Wn_le_uPerp N y.2, fun x hx => ?_⟩
      have h1 := h ⟨pr N x, hprW x hx⟩ (hprL x hx)
      rw [hW_B] at h1
      rw [← pr_add N x, map_add, Wn_perp_II N y.2 (NFGeom.proj_mem N x), add_zero]
      exact h1
    · intro hy x hx
      rw [hW_B]
      have : (y : V) ∈ dual H L := by rw [hdL]; exact hy
      exact ((mem_dual_iff H L y).1 this).2 x hx
  exact ⟨⟨⟨M, hfg, by simp [rs]⟩, hspan⟩, hdual⟩

end GlobalTheory.DegCnt.WnLat

namespace GlobalTheory.DegCnt

theorem NF.wnUnimod : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r) (L : Submodule (𝓞 K) V), IsUnimodMod H L (uPerp N.F N.F') (II N.F N.F') → ∃ HW : HermSpace K N.Wn, (∀ x y : N.Wn, HW.B x y = H.B x y) ∧ Module.finrank K N.Wn + 2 * r = Module.finrank K V ∧ GlobalTheory.HermLat.IsUnimod HW (L.comap (N.Wn.subtype.restrictScalars (𝓞 K))) := by
  intro K V _ _ _ _ _ _ _ _ H _ r N L hL
  exact ⟨WnLat.hW N, WnLat.hW_B N, WnLat.finrank_Wn N, WnLat.unimod N L hL⟩

end GlobalTheory.DegCnt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueMulMemBoxTriangularLayers
section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCov

theorem existsUnique_mul_mem_box_of_layers : ∀ (M I A B D : Type) [Monoid M] [Fintype I] [AddCommGroup A] [AddCommGroup B] [AddCommGroup D] (ht : I → ℕ) (C : (I → A) × B × D → M) (Γ : Set M) (Λ₁ F₁ : I → Set A) (Λ₂ F₂ : Set B) (Λ₃ F₃ : Set D), Function.Injective C → C 0 = 1 → (∀ p q, ∃ w, C p * C q = C w ∧ (∀ i, (∀ l, ht l < ht i → p.1 l = 0) → w.1 i = p.1 i + q.1 i) ∧ (p.1 = 0 → w.2.1 = p.2.1 + q.2.1) ∧ (p.1 = 0 → p.2.1 = 0 → w.2.2 = p.2.2 + q.2.2)) → Γ ⊆ Set.range C → (1 : M) ∈ Γ → (∀ a ∈ Γ, ∀ b ∈ Γ, a * b ∈ Γ) → (∀ a ∈ Γ, ∃ b ∈ Γ, b * a = 1) → (∀ p, C p ∈ Γ → ∀ i, p.1 i ∈ Λ₁ i) → (∀ p, C p ∈ Γ → p.1 = 0 → p.2.1 ∈ Λ₂) → (∀ p, C p ∈ Γ → p.1 = 0 → p.2.1 = 0 → p.2.2 ∈ Λ₃) → (∀ i, ∀ a ∈ Λ₁ i, ∃ p, C p ∈ Γ ∧ p.1 = Pi.single i a) → (∀ b ∈ Λ₂, ∃ p, C p ∈ Γ ∧ p.1 = 0 ∧ p.2.1 = b) → (∀ d ∈ Λ₃, C (0, 0, d) ∈ Γ) → (∀ i a, ∃! b, b ∈ Λ₁ i ∧ b + a ∈ F₁ i) → (∀ a, ∃! b, b ∈ Λ₂ ∧ b + a ∈ F₂) → (∀ a, ∃! b, b ∈ Λ₃ ∧ b + a ∈ F₃) → ∀ q, ∃! m, m ∈ Γ ∧ m * C q ∈ C '' (Set.pi Set.univ F₁ ×ˢ F₂ ×ˢ F₃) := by
  intro M I A B D _ _ _ _ _ ht C Γ Λ₁ F₁ Λ₂ F₂ Λ₃ F₃ hC hC0 hmul hΓC h1 hmulΓ hinv h1Λ h2Λ h3Λ
    h1s h2s h3s hF₁ hF₂ hF₃ q
  classical

  have h0Γ : C 0 ∈ Γ := hC0 ▸ h1
  have z1 : ∀ i, (0 : A) ∈ Λ₁ i := fun i => h1Λ 0 h0Γ i
  have z2 : (0 : B) ∈ Λ₂ := h2Λ 0 h0Γ rfl
  have z3 : (0 : D) ∈ Λ₃ := h3Λ 0 h0Γ rfl rfl

  have layer1 : ∀ s : Finset I, ∀ q, ∃ m ∈ Γ, ∃ w, m * C q = C w ∧ ∀ i ∈ s, w.1 i ∈ F₁ i := by
    intro s
    induction s using Finset.induction_on_max_value ht with
    | empty => exact fun q => ⟨1, h1, q, one_mul _, by simp⟩
    | insert a s has hmax ih =>
      intro q
      obtain ⟨m, hm, w, hmw, hw⟩ := ih q
      obtain ⟨b, ⟨hbΛ, hbF⟩, -⟩ := hF₁ a (w.1 a)
      obtain ⟨p, hpΓ, hp1⟩ := h1s a b hbΛ
      obtain ⟨w', hw'eq, hw'1, -, -⟩ := hmul p w
      refine ⟨C p * m, hmulΓ _ hpΓ _ hm, w', by rw [mul_assoc, hmw, hw'eq], ?_⟩
      have key : ∀ i, ht i ≤ ht a → w'.1 i = p.1 i + w.1 i := fun i hi =>
        hw'1 i (fun l hl => by
          rw [hp1]; exact Pi.single_eq_of_ne (ne_of_apply_ne ht (by omega)) _)
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [key i le_rfl, hp1, Pi.single_eq_same]; exact hbF
      · have hia : i ≠ a := fun h => has (h ▸ hi)
        rw [key i (hmax i hi), hp1, Pi.single_eq_of_ne hia, zero_add]; exact hw i hi

  have hex : ∃ m ∈ Γ, ∃ u, m * C q = C u ∧ u ∈ Set.pi Set.univ F₁ ×ˢ F₂ ×ˢ F₃ := by
    obtain ⟨m, hm, w, hmw, hw⟩ := layer1 Finset.univ q
    obtain ⟨b, ⟨hbΛ, hbF⟩, -⟩ := hF₂ w.2.1
    obtain ⟨p, hpΓ, hp1, hp2⟩ := h2s b hbΛ
    obtain ⟨w', hw'eq, hw'1, hw'2, -⟩ := hmul p w
    obtain ⟨d, ⟨hdΛ, hdF⟩, -⟩ := hF₃ w'.2.2
    obtain ⟨w'', hw''eq, hw''1, hw''2, hw''3⟩ := hmul (0, 0, d) w'
    refine ⟨C (0, 0, d) * (C p * m), hmulΓ _ (h3s d hdΛ) _ (hmulΓ _ hpΓ _ hm), w'',
      by rw [mul_assoc, mul_assoc, hmw, hw'eq, hw''eq], ?_⟩
    have e1 : ∀ i, w'.1 i = w.1 i := fun i => by
      rw [hw'1 i (fun l _ => by rw [hp1]; rfl), hp1]; exact zero_add _
    have e1' : ∀ i, w''.1 i = w'.1 i := fun i => by
      rw [hw''1 i (fun l _ => rfl)]; exact zero_add _
    have e2 : w''.2.1 = w'.2.1 := by rw [hw''2 rfl]; exact zero_add _
    refine Set.mk_mem_prod ?_ (Set.mk_mem_prod ?_ ?_)
    · exact Set.mem_univ_pi.2 fun i => by
        rw [e1', e1]; exact hw i (Finset.mem_univ i)
    · rw [e2, hw'2 hp1, hp2]; exact hbF
    · rw [hw''3 rfl rfl]; exact hdF

  have rigid : ∀ g ∈ Γ, ∀ u u', u ∈ Set.pi Set.univ F₁ ×ˢ F₂ ×ˢ F₃ →
      u' ∈ Set.pi Set.univ F₁ ×ˢ F₂ ×ˢ F₃ → g * C u = C u' → g = 1 := by
    intro g hg u u' hu hu' hgu
    obtain ⟨p, rfl⟩ := hΓC hg
    obtain ⟨w, hweq, hw1, hw2, hw3⟩ := hmul p u
    have hwu : w = u' := hC (hweq.symm.trans hgu)
    rw [hwu] at hw1 hw2 hw3
    simp only [Set.mem_prod, Set.mem_univ_pi] at hu hu'

    have key : ∀ n, ∀ i, ht i = n → p.1 i = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro i hi
        have e := hw1 i (fun l hl => ih (ht l) (hi ▸ hl) l rfl)
        exact (hF₁ i (u.1 i)).unique ⟨h1Λ p hg i, e ▸ hu'.1 i⟩ ⟨z1 i, (zero_add (u.1 i)).symm ▸ hu.1 i⟩
    have hp1 : p.1 = 0 := funext fun i => key _ i rfl
    have hp2 : p.2.1 = 0 :=
      (hF₂ u.2.1).unique ⟨h2Λ p hg hp1, hw2 hp1 ▸ hu'.2.1⟩ ⟨z2, (zero_add u.2.1).symm ▸ hu.2.1⟩
    have hp3 : p.2.2 = 0 :=
      (hF₃ u.2.2).unique ⟨h3Λ p hg hp1 hp2, hw3 hp1 hp2 ▸ hu'.2.2⟩
        ⟨z3, (zero_add u.2.2).symm ▸ hu.2.2⟩
    have hp : p = 0 := Prod.ext hp1 (Prod.ext hp2 hp3)
    rw [hp, hC0]

  obtain ⟨m, hmΓ, u, hmu, hu⟩ := hex
  refine ⟨m, ⟨hmΓ, u, hu, hmu.symm⟩, ?_⟩
  rintro m' ⟨hm'Γ, u', hu', hm'u⟩
  obtain ⟨n, hnΓ, hnm⟩ := hinv m hmΓ
  have hg : m' * n = 1 := by
    refine rigid (m' * n) (hmulΓ _ hm'Γ _ hnΓ) u u' hu hu' ?_
    rw [← hmu, hm'u, ← mul_assoc, mul_assoc m', hnm, mul_one]
  calc m' = m' * (n * m) := by rw [hnm, mul_one]
    _ = m' * n * m := (mul_assoc _ _ _).symm
    _ = m := by rw [hg, one_mul]

end GlobalTheory.DegVol.RefCov
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealPlaces

variable (D : D7)

theorem embS_injective : Function.Injective (embS D) := by
  intro τ τ' h
  exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem mem_cm_iff (φ : D.host.E →+* ℂ) :
    φ ∈ D.host.cmType ↔ ∃ τ, embS D τ = φ := by
  constructor
  · intro h
    obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 φ
    have hg := ((factEmb D.R D.host).2 g).1 h
    refine ⟨D.eTau.symm ⟨g, hg⟩, ?_⟩
    unfold embS
    rw [Equiv.apply_symm_apply]
  · rintro ⟨τ, rfl⟩
    exact ((factEmb D.R D.host).2 _).2 (D.eTau τ).2

theorem range_iff (φ : D.host.E →+* ℂ) :
    (∃ τ, embS D τ = φ) ↔ ¬ ∃ τ, embS D τ = ComplexEmbedding.conjugate φ := by
  rw [← mem_cm_iff, ← mem_cm_iff]
  exact D.host.der.cmType.1 φ

theorem ne_conj (τ τ' : D.what₂.Tau) : embS D τ' ≠ ComplexEmbedding.conjugate (embS D τ) :=
  fun h => (range_iff D _).1 ⟨τ, rfl⟩ ⟨τ', h⟩

theorem sum_bijective : Function.Bijective
    (Sum.elim (embS D) (fun τ => ComplexEmbedding.conjugate (embS D τ))) := by
  constructor
  · rintro (τ | τ) (τ' | τ') h
    · exact congrArg _ (embS_injective D h)
    · exact absurd h (ne_conj D _ _)
    · exact absurd h.symm (ne_conj D _ _)
    · exact congrArg _ (embS_injective D (star_injective h))
  · intro φ
    by_cases h : ∃ τ, embS D τ = φ
    · obtain ⟨τ, hτ⟩ := h
      exact ⟨Sum.inl τ, hτ⟩
    · obtain ⟨τ, hτ⟩ := not_not.1 (fun h' => h ((range_iff D φ).2 h'))
      refine ⟨Sum.inr τ, ?_⟩
      show star (embS D τ) = φ
      rw [hτ]
      exact star_star φ

theorem existsUnique_place (w : InfinitePlace D.host.E) :
    ∃! τ, InfinitePlace.mk (embS D τ) = w := by
  have hex : ∃ τ, InfinitePlace.mk (embS D τ) = w := by
    obtain ⟨τ | τ, h⟩ := (sum_bijective D).2 w.embedding
    · exact ⟨τ, by rw [show embS D τ = w.embedding from h, InfinitePlace.mk_embedding]⟩
    · refine ⟨τ, ?_⟩
      rw [← InfinitePlace.mk_conjugate_eq,
        show ComplexEmbedding.conjugate (embS D τ) = w.embedding from h, InfinitePlace.mk_embedding]
  obtain ⟨τ, hτ⟩ := hex
  refine ⟨τ, hτ, fun τ' h' => ?_⟩
  rcases InfinitePlace.mk_eq_iff.1 (h'.trans hτ.symm) with h | h
  · exact embS_injective D h
  · exact absurd h.symm (ne_conj D _ _)

theorem prod_norm (a : D.host.E) :
    ∏ τ, ‖embS D τ a‖ ^ 2 = |((Algebra.norm ℚ a : ℚ) : ℝ)| := by
  have hb : Function.Bijective (fun τ => InfinitePlace.mk (embS D τ)) :=
    (Function.bijective_iff_existsUnique _).2 (existsUnique_place D)
  have h := InfinitePlace.prod_eq_abs_norm a
  rw [Rat.cast_abs] at h
  rw [← h, ← hb.prod_comp]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hc : (InfinitePlace.mk (embS D τ)).IsComplex := by
    rw [InfinitePlace.isComplex_mk_iff]
    exact fun hr => ne_conj D τ τ (ComplexEmbedding.isReal_iff.1 hr).symm
  rw [hc.mult_eq_two, InfinitePlace.apply]

theorem placeProd_eq (X : (D.host.E →+* ℂ) → ℝ) (h0 : ∀ φ, 0 ≤ X φ)
    (hc : ∀ φ, X (ComplexEmbedding.conjugate φ) = X φ) : placeProd X = ∏ τ, X (embS D τ) := by
  unfold placeProd
  rw [← (sum_bijective D).prod_comp, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, hc]
  exact Real.sqrt_mul_self (Finset.prod_nonneg fun τ _ => h0 _)

theorem finrank_E : finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField, Ranks.f, Ranks.n]
  ring

theorem finrank_F : finrank ℚ D.host.F = D.R.f := by
  have h := finrank_mul_finrank ℚ D.host.F D.host.E
  rw [finrank_E, D.sp.cm.deg2] at h
  omega

theorem one_le_rdE : 1 ≤ D.host.rdE := by
  unfold Host.rdE
  refine Real.one_le_rpow ?_ (by positivity)
  have := Int.one_le_abs (discr_ne_zero D.host.E)
  exact_mod_cast this

theorem absNorm_ddS :
    ((FractionalIdeal.absNorm (ddS D) : ℚ) : ℝ) = D.host.rdE ^ (2 * D.R.f) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.cm_discr_sq D.host.F D.host.E D.sp.cm
  have hpos : finrank ℚ D.host.E ≠ 0 := Module.finrank_pos.ne'
  unfold ddS Host.rdE
  rw [FractionalIdeal.coeIdeal_absNorm, h2, ← finrank_E, one_div,
    Real.rpow_inv_natCast_pow (abs_nonneg _) hpos]
  have h3 : |(discr D.host.E : ℝ)| = (discr D.host.F : ℝ) ^ 2 := by exact_mod_cast h1
  rw [h3]
  push_cast
  rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]

end GlobalTheory.RealPlaces

theorem GlobalTheory.real_places_facts : ∀ D : D7, Fintype.card D.what₂.Tau = D.R.f ∧ finrank ℚ D.host.E = 2 * D.R.f ∧ finrank ℚ D.host.F = D.R.f ∧ D.R.m = 2 * D.R.rS + 2 ∧ 1 ≤ D.host.rdE ∧ (∀ τ (a : D.host.E), embS D τ (star a) = starRingEnd ℂ (embS D τ a)) ∧ (∀ a : D.host.E, ∏ τ, ‖embS D τ a‖ ^ 2 = |((Algebra.norm ℚ a : ℚ) : ℝ)|) ∧ (∀ X : (D.host.E →+* ℂ) → ℝ, (∀ φ, 0 ≤ X φ) → (∀ φ, X (NumberField.ComplexEmbedding.conjugate φ) = X φ) → placeProd X = ∏ τ, X (embS D τ)) ∧ ((FractionalIdeal.absNorm (ddS D) : ℚ) : ℝ) = D.host.rdE ^ (2 * D.R.f) ∧ (∀ w : InfinitePlace D.host.E, ∃! τ, InfinitePlace.mk (embS D τ) = w) := by
  intro D
  refine ⟨D.what₂.card_Tau, GlobalTheory.RealPlaces.finrank_E D, GlobalTheory.RealPlaces.finrank_F D, D.R.rS_two.symm,
    GlobalTheory.RealPlaces.one_le_rdE D, fun τ a => D.sp.cm.cmUnram.2.1 _ a, GlobalTheory.RealPlaces.prod_norm D,
    GlobalTheory.RealPlaces.placeProd_eq D, GlobalTheory.RealPlaces.absNorm_ddS D,
    GlobalTheory.RealPlaces.existsUnique_place D⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarSubgroupBiInvariant
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.UnipUnimod

section General

open scoped Pointwise NNReal ENNReal

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem unimod_of_contract (N : Subgroup G) (hN : IsClosed (N : Set G)) {ν : Measure G}
    (h : IsHaarSub (N : Set G) ν) (a : ℝ → G) (h1 : ∀ s, ∀ m ∈ N, a s * m * (a s)⁻¹ ∈ N)
    (h2 : ∀ s, ∀ m ∈ N, (a s)⁻¹ * m * a s ∈ N)
    (h3 : ∀ m ∈ N, Filter.Tendsto (fun s => a s * m * (a s)⁻¹) Filter.atBot (nhds 1)) :
    (∀ m ∈ N, ν.map (fun x => x * m) = ν) ∧ ν.map (fun x => x⁻¹) = ν := by
  first
  | exact @_root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted
  | exact _root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted
  | (apply _root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted <;> assumption)
  | (intros; apply _root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ModularAutomorphism.unimodular_of_contracted ..)

end General

theorem unimodular_NW : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → (∀ m ∈ NW ε W, ν.map (fun x => x * m) = ν) ∧ ν.map (fun x => x⁻¹) = ν := by
  intro n ε W ν hW hν
  obtain ⟨a, Hm, -, ha, -, h1, h3, -⟩ := GlobalTheory.T.isotropic_splitTorus_iwasawa_unitaryGroup n ε W hW
  have hinv : ∀ s, a (-s) = (a s)⁻¹ := fun s => by
    refine eq_inv_of_mul_eq_one_left (Subtype.ext (Units.ext ?_))
    change umat (a (-s)) * umat (a s) = 1
    rw [ha, ha, Complex.ofReal_neg, neg_smul,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl ((s : ℂ) • Hm)).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  refine unimod_of_contract (nwSub ε W) (isClosed_NW ε W) hν a (fun s m hm => (h1 s m hm).1)
    (fun s m hm => ?_) h3
  have := (h1 (-s) m hm).1
  rwa [hinv, inv_inv] at this

end GlobalTheory.UnipUnimod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnimodularBesselModelUnitaryGroupStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnimodular_besselModelUnitaryGroup : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → IsUnimod (GG k r) μ := by
  first | exact @GlobalTheory.SgInf.isUnimod_GG | exact GlobalTheory.SgInf.isUnimod_GG | (intros; apply GlobalTheory.SgInf.isUnimod_GG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryOpNormBoundedByTwoFramesStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometry_opNorm_bounded_by_two_frames : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (C : Set (Mat k r)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsCompact C → (∀ γ ∈ C, γ ∈ GG k r ∧ Gf k r z z' γ ≠ 0) → ∃ C0 : ℝ, ∀ γ ∈ C, ∀ s ∈ GG k r, ∀ B : ℝ, 1 ≤ B → (∀ i, eucl (s *ᵥ gramVec k r z z' γ i) ≤ B) → opn s ≤ C0 * B ^ 2 := by
  first | exact @GlobalTheory.SgInf.isom_frame_bound | exact GlobalTheory.SgInf.isom_frame_bound | (intros; apply GlobalTheory.SgInf.isom_frame_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KTypeExtendsHolomorphicComplexifiedKStatement
section
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kType_extends_holomorphic_complexifiedK : TauExists := by
  first | exact @GlobalTheory.Dec.TauExt.tauExists | exact GlobalTheory.Dec.TauExt.tauExists | (intros; apply GlobalTheory.Dec.TauExt.tauExists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeNonzeroVectorPairNormalFormsStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_nonzero_vector_pair_normal_forms : ∀ (E : Type) [Field E] [NumberField E] (k : ℕ), ∀ Lf : Ideal (𝓞 E) → Submodule (𝓞 E) (Fin k → E) → Submodule (𝓞 E) (Fin (k + 1) → E), (∀ 𝔞 Λ' y, y ∈ Lf 𝔞 Λ' ↔ (∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Fin.tail y ∈ Λ') → (∀ 𝔞 Λ', 𝔞 ≠ ⊥ → Submodule.IsLattice E Λ' → Submodule.IsLattice E (Lf 𝔞 Λ') ∧ Pi.single 0 1 ∈ Lf 𝔞 Λ') ∧ (∀ Λ : Submodule (𝓞 E) (Fin (k + 1) → E), Submodule.IsLattice E Λ → ∀ x ∈ Λ, x ≠ 0 → ∃ (γ : GL (Fin (k + 1)) E) (𝔞 : Ideal (𝓞 E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), 𝔞 ≠ ⊥ ∧ Submodule.IsLattice E Λ' ∧ (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ x = Pi.single 0 1 ∧ ∀ y, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ y ∈ Lf 𝔞 Λ' ↔ y ∈ Λ) ∧ ∀ 𝔞 𝔟 Λ₁ Λ₂, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → Submodule.IsLattice E Λ₁ → Submodule.IsLattice E Λ₂ → ∀ γ : GL (Fin (k + 1)) E, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ Pi.single 0 1 = Pi.single 0 1 → ((∀ y, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) *ᵥ y ∈ Lf 𝔟 Λ₂ ↔ y ∈ Lf 𝔞 Λ₁) ↔ 𝔞 = 𝔟 ∧ (∀ y, (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E).submatrix Fin.succ Fin.succ *ᵥ y ∈ Λ₂ ↔ y ∈ Λ₁) ∧ ∀ y ∈ Λ₁, ∀ t ∈ 𝔞, (t : E) * ((fun b => (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) E) 0 b.succ) ⬝ᵥ y) ∈ (algebraMap (𝓞 E) E).range) := by
  first | exact @GlobalTheory.LatVecPair.classes | exact GlobalTheory.LatVecPair.classes | (intros; apply GlobalTheory.LatVecPair.classes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMapStatement
section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lebesgueCommonStabilizer_eq_radical_levi_map : ∀ (k r j : ℕ) (β : Fin r → ℕ), Monotone β → (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) → lebR0 k r j β = (volume : Measure ((UTin β → ℂ) × PTop k r j)).map (fun q => Matrix.of.symm (pTop k r j q.2 * uEmb k r (upperIn β q.1))) ∧ Set.range (rEl k r j β) = Set.range (fun q : (UTin β → ℂ) × PTop k r j => pTop k r j q.2 * uEmb k r (upperIn β q.1)) ∧ Function.Injective (fun q : (UTin β → ℂ) × PTop k r j => pTop k r j q.2 * uEmb k r (upperIn β q.1)) ∧ (j = 0 → lebR0 k r j β = lebN k r) := by
  first | exact @GlobalTheory.DegVol.Swap.range_eq_and_injective_parabolic_unipotent_product | exact GlobalTheory.DegVol.Swap.range_eq_and_injective_parabolic_unipotent_product | (intros; apply GlobalTheory.DegVol.Swap.range_eq_and_injective_parabolic_unipotent_product <;> assumption)
end

