import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0017
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NondegenerateOnOrthCompl
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0018
import Formalism.HermitianLattices.HermitianLatticesProofs.TraceReal

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscriminantNormShapes
section
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.discriminantNormShapes

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5

def skSet (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [Fact (IsFixF K F)] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    Set (Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :=
  {X | Xᴴ * diagQ K 𝔭 k a * X = diagQ K 𝔭 k a}

def udPre (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [Fact (IsFixF K F)] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) : Type :=
  {Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) //
    (∃ P, P * diagQ K 𝔭 k a = diagQ K 𝔭 k a * Y) ∧
    ∃ W, Yᴴ * diagQ K 𝔭 k a * Y - diagQ K 𝔭 k a = diagQ K 𝔭 k a * W * diagQ K 𝔭 k a}

def udSetoid (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [Fact (IsFixF K F)] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    Setoid (udPre K 𝔭 k a) where
  r Y Y' := ∃ Z : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k), Y.1 - Y'.1 = Z * diagQ K 𝔭 k a
  iseqv := {
    refl := fun Y => ⟨0, by simp⟩
    symm := fun ⟨Z, hZ⟩ => ⟨-Z, by rw [Matrix.neg_mul, ← hZ, neg_sub]⟩
    trans := fun ⟨Z, hZ⟩ ⟨Z', hZ'⟩ => ⟨Z + Z', by rw [Matrix.add_mul, ← hZ, ← hZ', sub_add_sub_cancel]⟩ }

def udQ (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [Fact (IsFixF K F)] {m : ℕ} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) : Type :=
  Quotient (udSetoid K 𝔭 k a)

def UDModel : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h →
    ∀ L : Submodule (𝓞 K) V, Submodule.IsLattice K L → Formalism.HermitianLatticesTheory.IsIntegralLat h L →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h ⊤ L 𝔭 b a →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k → discAut h ⊤ L 𝔭 = Nat.card (udQ K 𝔭 k a)

def OrbitCount : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
    ∀ k : ℕ, 2 * vJof 𝔭 a + 1 ≤ k →
      Nat.card (skSet K 𝔭 k a) = Nat.card (udQ K 𝔭 k a) * Nat.card (kerSet K 𝔭 k a)

section

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem linearIndependent_of_jordan {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    {𝔭 : Ideal (𝓞 F)} {b : Fin (finrank K (⊤ : Submodule K V)) → V}
    {a : Fin (finrank K (⊤ : Submodule K V)) → 𝓞 F} (hb : IsJordanIn h ⊤ L 𝔭 b a) :
    LinearIndependent K b := by
  obtain ⟨-, -, horth, hdiag, hne⟩ := hb
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h1 : h (b i) (∑ j ∈ s, g j • b j) = 0 := by rw [hg, map_zero]
  rw [map_sum, Finset.sum_eq_single i] at h1
  · rw [map_smul, smul_eq_mul, hdiag] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd (by simpa using h2) (hne i)
  · intro j _ hji
    rw [map_smul, horth i j (Ne.symm hji), smul_zero]
  · intro hi'
    exact absurd hi hi'

variable [Fact (IsFixF K F)]

theorem akCount_eq_skSet {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {b : Fin (finrank K (⊤ : Submodule K V)) → V}
    {a : Fin (finrank K (⊤ : Submodule K V)) → 𝓞 F} (hb : IsJordanIn h ⊤ L 𝔭 b a) (k : ℕ) :
    akCount h L 𝔭 k = Nat.card (skSet K 𝔭 k a) := by
  have hli := linearIndependent_of_jordan hb
  have hcard : Fintype.card (Fin (finrank K (⊤ : Submodule K V))) = finrank K V := by
    simp [finrank_top]
  have hB : ⇑(Basis.mk hli (le_of_eq (hli.span_eq_top_of_card_eq_finrank' hcard).symm)) = b :=
    Basis.coe_mk _ _
  have hH : ∀ i j, algebraMap (𝓞 K) K
      ((Matrix.diagonal fun i => algebraMap (𝓞 F) (𝓞 K) (a i)) i j) =
      h (Basis.mk hli (le_of_eq (hli.span_eq_top_of_card_eq_finrank' hcard).symm) i)
        (Basis.mk hli (le_of_eq (hli.span_eq_top_of_card_eq_finrank' hcard).symm) j) := by
    intro i j
    rw [hB]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, hb.2.2.2.1 i]
      rfl
    · rw [Matrix.diagonal_apply_ne _ hij, map_zero]
      exact (hb.2.2.1 i j hij).symm
  rw [integralBasisSpans.akCount_eq h h𝔭 _ (by
    have h2 := hb.2.1
    rw [← hB] at h2
    exact h2) hH k]
  have hd : (Matrix.diagonal fun i => algebraMap (𝓞 F) (𝓞 K) (a i)).map
      (Ideal.Quotient.mk (extP K 𝔭 ^ k)) = diagQ K 𝔭 k a := by
    rw [diagQ, Matrix.diagonal_map (map_zero _)]
  rw [hd]
  rfl

end

theorem discOnto_of (hU : UDModel) (hO : OrbitCount) : DiscOnto := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ _ hK h hsymm hpos L hL hint 𝔭 h𝔭 b a hb k hk
  have ha : ∀ i, a i ≠ 0 := by
    obtain ⟨-, -, -, -, h5⟩ := hb
    exact h5
  rw [akCount_eq_skSet h𝔭 hb k, hO K F hK 𝔭 h𝔭 _ a ha k hk,
    hU K F V hK h hsymm hpos L hL hint 𝔭 h𝔭 b a hb k hk]

end Formalism.L2.SG.Pf.discriminantNormShapes
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExtensionIdentityOfMemCompl
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalComplementGenusMass

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G9

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def formOn (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) : ↥X →ₗ⋆[K] ↥X →ₗ[K] K :=
  (h.comp X.subtype).compl₂ X.subtype

@[simp] theorem formOn_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (x y : ↥X) :
    formOn h X x y = h x y := rfl

theorem formOn_isSymm {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (X : Submodule K V) :
    (formOn h X).IsSymm :=
  ⟨fun x y => hs.eq (x : V) (y : V)⟩

def incl (X : Submodule K V) : ↥X →ₗ[𝓞 K] V := X.subtype.restrictScalars (𝓞 K)

theorem incl_apply (X : Submodule K V) (x : ↥X) : incl X x = x := rfl

theorem incl_injective (X : Submodule K V) : Function.Injective (incl X) := Subtype.val_injective

def push (X : Submodule K V) (L : Submodule (𝓞 K) ↥X) : Submodule (𝓞 K) V := L.map (incl X)

def pull (X : Submodule K V) (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) ↥X := L.comap (incl X)

theorem mem_push {X : Submodule K V} {L : Submodule (𝓞 K) ↥X} {v : V} :
    v ∈ push X L ↔ ∃ x ∈ L, (x : V) = v := Submodule.mem_map

theorem coe_mem_push {X : Submodule K V} {L : Submodule (𝓞 K) ↥X} {x : ↥X} :
    (x : V) ∈ push X L ↔ x ∈ L := by
  rw [mem_push]
  constructor
  · rintro ⟨y, hy, e⟩
    rwa [← Subtype.ext e]
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem push_le (X : Submodule K V) (L : Submodule (𝓞 K) ↥X) : ∀ v ∈ push X L, v ∈ X := by
  rintro v ⟨x, -, rfl⟩
  exact x.2

theorem pull_push (X : Submodule K V) (L : Submodule (𝓞 K) ↥X) : pull X (push X L) = L :=
  Submodule.comap_map_eq_of_injective (incl_injective X) L

theorem push_pull {X : Submodule K V} {L : Submodule (𝓞 K) V} (hL : ∀ v ∈ L, v ∈ X) :
    push X (pull X L) = L := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hv
    exact ⟨⟨v, hL v hv⟩, hv, rfl⟩

theorem push_injective (X : Submodule K V) : Function.Injective (push X) :=
  Submodule.map_injective_of_injective (incl_injective X)

theorem algebraMap_ne_zero {𝔭 : Ideal (𝓞 F)} (_hp : 𝔭.IsPrime) {t : 𝓞 F} (ht : t ∉ 𝔭) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
  have ht0 : t ≠ 0 := fun e => ht (e ▸ 𝔭.zero_mem)
  have e : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := rfl
  rw [e]
  exact (map_ne_zero (algebraMap F K)).mpr (by exact_mod_cast ht0)

theorem mem_of_smul_mem {X : Submodule K V} {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {t : 𝓞 F}
    (ht : t ∉ 𝔭) {v : V} (hv : algebraMap (𝓞 F) (𝓞 K) t • v ∈ X) : v ∈ X := by
  have hne := algebraMap_ne_zero (K := K) hp ht
  have e : v = (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ •
      (algebraMap (𝓞 F) (𝓞 K) t • v) := by
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) v, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [e]
  exact X.smul_mem _ hv

theorem push_locF (X : Submodule K V) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    push X (locF 𝔭 L) = locF 𝔭 (push X L) := by
  ext v
  rw [LocF.mem_locF_iff hp]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht, hx⟩ := (LocF.mem_locF_iff hp L x).1 hx
    exact ⟨t, ht, ⟨_, hx, (incl X).map_smul _ _⟩⟩
  · rintro ⟨t, ht, hy⟩
    have hv : v ∈ X := mem_of_smul_mem (K := K) hp ht (push_le X L _ hy)
    refine ⟨⟨v, hv⟩, (LocF.mem_locF_iff hp L _).2 ⟨t, ht, ?_⟩, rfl⟩
    rw [← coe_mem_push (X := X)]
    exact hy

theorem push_span (X : Submodule K V) (s : Set ↥X) :
    push X (Submodule.span (𝓞 K) s) = Submodule.span (𝓞 K) (((↑) : ↥X → V) '' s) :=
  Submodule.map_span (incl X) s

theorem isLatIn_push_iff_isLattice {X : Submodule K V} (L : Submodule (𝓞 K) ↥X) :
    IsLatIn X (push X L) ↔ Submodule.IsLattice K L := by
  have hspan : Submodule.span K ((push X L : Submodule (𝓞 K) V) : Set V) =
      (Submodule.span K (L : Set ↥X)).map X.subtype := by
    rw [Submodule.map_span]
    congr 1
  constructor
  · rintro ⟨hfg, hsp⟩
    refine ⟨Submodule.fg_of_fg_map_injective _ (incl_injective X) hfg, ?_⟩
    apply Submodule.map_injective_of_injective X.injective_subtype
    rw [← hspan, hsp, Submodule.map_subtype_top]
  · rintro ⟨hfg, hsp⟩
    refine ⟨hfg.map _, ?_⟩
    rw [hspan, hsp, Submodule.map_subtype_top]

theorem isIntegralLat_push {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} (L : Submodule (𝓞 K) ↥X) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h (push X L) ↔ Formalism.HermitianLatticesTheory.IsIntegralLat (formOn h X) L := by
  constructor
  · intro H x hx y hy
    exact H _ (coe_mem_push.mpr hx) _ (coe_mem_push.mpr hy)
  · rintro H _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact H x hx y hy

theorem isJordanIn_top {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} {L : Submodule (𝓞 K) ↥X}
    {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {b : Fin (finrank K X) → V} {a : Fin (finrank K X) → 𝓞 F}
    (H : IsJordanIn h X (push X L) 𝔭 b a) :
    IsJordanIn (formOn h X) ⊤ L 𝔭 (fun i => ⟨b (Fin.cast (finrank_top K ↥X) i), H.1 _⟩)
      (fun i => a (Fin.cast (finrank_top K ↥X) i)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  refine ⟨fun _ => Submodule.mem_top, ?_, fun i j hij => h3 _ _ fun e => hij (Fin.cast_injective _ e),
    fun i => h4 _, fun i => h5 _⟩
  apply push_injective X
  rw [push_locF X hp, push_locF X hp, push_span]
  refine Eq.trans ?_ h2
  congr 2
  ext v
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨i, rfl⟩
    refine ⟨_, ⟨Fin.cast (finrank_top K ↥X).symm i, rfl⟩, ?_⟩
    rfl

section Ext

variable [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}

def extId (hc : IsCompl U (orthK h U)) (g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)) : V ≃ₗ[K] V :=
  (Submodule.prodEquivOfIsCompl U (orthK h U) hc).symm.trans
    (((LinearEquiv.refl K ↥U).prodCongr g).trans (Submodule.prodEquivOfIsCompl U (orthK h U) hc))

theorem extId_add (hc : IsCompl U (orthK h U)) (g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)) {u w : V}
    (hu : u ∈ U) (hw : w ∈ orthK h U) : extId hc g (u + w) = u + (g ⟨w, hw⟩ : V) := by
  have e1 : (Submodule.prodEquivOfIsCompl U (orthK h U) hc).symm (u + w) = (⟨u, hu⟩, ⟨w, hw⟩) := by
    rw [LinearEquiv.symm_apply_eq, Submodule.coe_prodEquivOfIsCompl']
  simp only [extId, LinearEquiv.trans_apply, e1, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, Submodule.coe_prodEquivOfIsCompl']

theorem exists_add (hc : IsCompl U (orthK h U)) (v : V) :
    ∃ u ∈ U, ∃ w ∈ orthK h U, u + w = v := by
  have hv : v ∈ U ⊔ orthK h U := by rw [hc.sup_eq_top]; exact Submodule.mem_top
  exact Submodule.mem_sup.mp hv

theorem extId_of_mem_U (hc : IsCompl U (orthK h U)) (g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)) {u : V}
    (hu : u ∈ U) : extId hc g u = u := by
  have := extId_add hc g hu (orthK h U).zero_mem
  rw [add_zero] at this
  rw [this]
  simp

theorem extension_identity_of_mem_compl (hc : IsCompl U (orthK h U)) (g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U))
    (w : ↥(orthK h U)) : extId hc g w = g w := by
  have := extId_add hc g U.zero_mem w.2
  rw [zero_add] at this
  rw [this, zero_add]

theorem extId_mem (hs : h.IsSymm) (hc : IsCompl U (orthK h U)) {g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)}
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom (formOn h (orthK h U))) : extId hc g ∈ isomFix h U := by
  refine ⟨fun v v' => ?_, fun u hu => extId_of_mem_U hc g hu⟩
  obtain ⟨u, hu, w, hw, rfl⟩ := exists_add hc v
  obtain ⟨u', hu', w', hw', rfl⟩ := exists_add hc v'
  rw [extId_add hc g hu hw, extId_add hc g hu' hw']
  have hg' : h (g ⟨w, hw⟩ : V) (g ⟨w', hw'⟩ : V) = h w w' := hg _ _
  have o1 : ∀ {x y : V}, x ∈ U → y ∈ orthK h U → h x y = 0 := fun hx hy => mem_orthK.mp hy _ hx
  have o2 : ∀ {x y : V}, x ∈ U → y ∈ orthK h U → h y x = 0 := fun {x y} hx hy => by
    rw [← hs.eq x y, o1 hx hy, map_zero]
  simp only [map_add, LinearMap.add_apply]
  rw [hg', o1 hu (g ⟨w', hw'⟩).2, o2 hu' (g ⟨w, hw⟩).2, o1 hu hw', o2 hu' hw]

theorem map_orthK {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) :
    (orthK h U).map (g : V →ₗ[K] V) = orthK h U := by
  ext x
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact apply_mem_orthK hg hy
  · intro hx
    exact ⟨g.symm x, apply_mem_orthK ((isomFix h U).inv_mem hg) hx, g.apply_symm_apply x⟩

def restr {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U) :=
  g.ofSubmodules (orthK h U) (orthK h U) (map_orthK hg)

theorem restr_apply {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) (w : ↥(orthK h U)) :
    (restr hg w : V) = g w :=
  LinearEquiv.ofSubmodules_apply _ _ _

theorem restr_mem {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) :
    restr hg ∈ Formalism.HermitianLatticesTheory.isom (formOn h (orthK h U)) := fun x y => by
  simp only [formOn_apply, restr_apply]
  exact hg.1 x y

theorem extId_restr (hc : IsCompl U (orthK h U)) {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) :
    extId hc (restr hg) = g := by
  apply LinearEquiv.ext
  intro v
  obtain ⟨u, hu, w, hw, rfl⟩ := exists_add hc v
  rw [extId_add hc _ hu hw, restr_apply, map_add, hg.2 u hu]

theorem restr_extId (hs : h.IsSymm) (hc : IsCompl U (orthK h U))
    {g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)} (hg : g ∈ Formalism.HermitianLatticesTheory.isom (formOn h (orthK h U))) :
    restr (extId_mem hs hc hg) = g := by
  apply LinearEquiv.ext
  intro w
  apply Subtype.ext
  exact (restr_apply _ w).trans (extension_identity_of_mem_compl hc g w)

theorem gmap_push {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) (L : Submodule (𝓞 K) ↥(orthK h U)) :
    Formalism.HermitianLatticesTheory.gmap g (push (orthK h U) L) = push (orthK h U) (Formalism.HermitianLatticesTheory.gmap (restr hg) L) := by
  unfold Formalism.HermitianLatticesTheory.gmap push
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1

theorem gmap_extId_push (hs : h.IsSymm) (hc : IsCompl U (orthK h U))
    {g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)} (hg : g ∈ Formalism.HermitianLatticesTheory.isom (formOn h (orthK h U)))
    (L : Submodule (𝓞 K) ↥(orthK h U)) :
    Formalism.HermitianLatticesTheory.gmap (extId hc g) (push (orthK h U) L) = push (orthK h U) (Formalism.HermitianLatticesTheory.gmap g L) := by
  rw [gmap_push (extId_mem hs hc hg), restr_extId hs hc hg]

end Ext

end Formalism.L2.SG.Pf.OrthogonalComplementGenusMass
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueExistsOfLocal
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G7

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem zmult_of_span (M : Submodule (𝓞 K) V) (x : V) (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hnx m
    · rw [mul_smul]; exact zsmul_mem hmy n
  | smul a x _ hx =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨k, hk, α, hα⟩ := Formalism.HermitianLatticesTheory.traceReal_den a
    refine ⟨k * n, mul_ne_zero hk hn, ?_⟩
    have e1 : (k * n) • (a • x) = α • (n • x) := by
      rw [← Int.cast_smul_eq_zsmul K (k * n), ← algebraMap_smul K α (n • x),
        ← Int.cast_smul_eq_zsmul K n, smul_smul, smul_smul]
      congr 1
      rw [show algebraMap (NumberField.RingOfIntegers K) K α = (α : K) from rfl, ← hα]
      push_cast
      ring
    rw [e1]
    exact M.smul_mem α hnx

def zdiv (B : Submodule (𝓞 K) V) (n : ℤ) : Submodule (𝓞 K) V where
  carrier := {x | n • x ∈ B}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    show n • (a + b) ∈ B
    rw [smul_add]
    exact B.add_mem ha hb
  smul_mem' := by
    intro c x hx
    show n • (c • x) ∈ B
    rw [smul_comm]
    exact B.smul_mem c hx

theorem exists_zsmul_of_fg {A B : Submodule (𝓞 K) V} (hA : A.FG)
    (hAB : ∀ y ∈ A, ∃ n : ℤ, n ≠ 0 ∧ n • y ∈ B) : ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ A, n • x ∈ B := by
  classical
  obtain ⟨S, rfl⟩ := hA
  choose! m hm hmy using fun y (hy : y ∈ S) => hAB y (Submodule.subset_span hy)
  refine ⟨∏ y ∈ S, m y, Finset.prod_ne_zero_iff.2 hm, fun x hx => ?_⟩
  show x ∈ zdiv B (∏ y ∈ S, m y)
  refine (Submodule.span_le.2 ?_) hx
  intro y hy
  show (∏ y ∈ S, m y) • y ∈ B
  rw [← Finset.prod_erase_mul S m hy, mul_smul]
  exact zsmul_mem (hmy y hy) _

theorem locF_le_of_zsmul {A B : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (n : ℤ)
    (hn : (n : 𝓞 F) ∉ 𝔭) (hAB : ∀ x ∈ A, n • x ∈ B) : locF 𝔭 A ≤ locF 𝔭 B := by
  intro x hx
  obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff hp A x).1 hx
  refine (LocF.mem_locF_iff hp B x).2 ⟨(n : 𝓞 F) * t, fun hm => (hp.mem_or_mem hm).elim hn ht, ?_⟩
  rw [map_mul, map_intCast, mul_smul, Int.cast_smul_eq_zsmul]
  exact hAB _ htx

theorem badFinite : BadFinite := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF Λ₀ hΛ₀ U M hM
  classical
  set N : Submodule (𝓞 K) V := Λ₀ ⊓ U.restrictScalars (𝓞 K) with hN
  have hMU : ∀ y ∈ M, y ∈ U := fun y hy => by
    rw [← hM.2]; exact Submodule.subset_span hy
  obtain ⟨n₁, hn₁, h₁⟩ : ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ M, n • x ∈ N := by
    refine exists_zsmul_of_fg hM.1 fun y hy => ?_
    obtain ⟨m, hm, hmy⟩ := Formalism.HermitianLatticesTheory.traceReal_mult Λ₀ hΛ₀ y
    exact ⟨m, hm, Submodule.mem_inf.2 ⟨hmy, zsmul_mem (hMU y hy) m⟩⟩
  have hNfg : N.FG := Submodule.FG.of_le hΛ₀.fg inf_le_left
  obtain ⟨n₂, hn₂, h₂⟩ : ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ N, n • x ∈ M := by
    refine exists_zsmul_of_fg hNfg fun y hy => zmult_of_span M y ?_
    rw [hM.2]
    exact (Submodule.mem_inf.1 hy).2
  set a : 𝓞 F := ((n₁ * n₂ : ℤ) : 𝓞 F) with ha
  have ha0 : a ≠ 0 := by
    rw [ha, Int.cast_ne_zero]
    exact mul_ne_zero hn₁ hn₂
  have hD : Ideal.span {a} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hfin : {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} | a ∈ 𝔭.1}.Finite := by
    refine ((Ideal.finite_factors hD).image (fun v =>
      (⟨v.asIdeal, v.isMaximal⟩ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}))).subset ?_
    intro 𝔭 h𝔭
    have hne : 𝔭.1 ≠ ⊥ := fun e => ha0 (by
      have : a ∈ 𝔭.1 := h𝔭
      rwa [e, Ideal.mem_bot] at this)
    refine ⟨⟨𝔭.1, 𝔭.2.isPrime, hne⟩, ?_, rfl⟩
    show 𝔭.1 ∣ Ideal.span {a}
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
    exact h𝔭
  refine ⟨hfin.toFinset, fun 𝔭 h𝔭 => ?_⟩
  have haP : a ∉ 𝔭.1 := fun h => h𝔭 (hfin.mem_toFinset.2 h)
  have e : a = (n₁ : 𝓞 F) * (n₂ : 𝓞 F) := by rw [ha]; push_cast; ring
  have h1P : (n₁ : 𝓞 F) ∉ 𝔭.1 := fun h => haP (e ▸ Ideal.mul_mem_right _ _ h)
  have h2P : (n₂ : 𝓞 F) ∉ 𝔭.1 := fun h => haP (e ▸ Ideal.mul_mem_left _ _ h)
  exact le_antisymm (locF_le_of_zsmul 𝔭.2.isPrime n₂ h2P h₂)
    (locF_le_of_zsmul 𝔭.2.isPrime n₁ h1P h₁)

theorem glueExists_of_local (hloc : GlueLocal) : GlueExists :=
  glueExists_of_of hloc badFinite

end Formalism.L2.SG.Pf.G7
end
end

