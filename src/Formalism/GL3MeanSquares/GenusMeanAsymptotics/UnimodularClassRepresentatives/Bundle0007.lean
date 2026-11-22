import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassSt
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsPrimitiveNorm
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0006

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CovolumeIntegerLatticeEq
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem nrComplexPlaces_eq_fDeg (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    InfinitePlace.nrComplexPlaces K = Formalism.HermitianLatticesTheory.fDeg K := by
  have h0 : InfinitePlace.nrRealPlaces K = 0 := by
    classical
    unfold InfinitePlace.nrRealPlaces
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mpr (hK.1.isComplex w.1) w.2⟩
  unfold Formalism.HermitianLatticesTheory.fDeg
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, h0, zero_add]

theorem finrank_eq_two_fDeg (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    finrank ℚ K = 2 * Formalism.HermitianLatticesTheory.fDeg K := by
  rw [← nrComplexPlaces_eq_fDeg hK]
  have h0 : InfinitePlace.nrRealPlaces K = 0 := by
    classical
    unfold InfinitePlace.nrRealPlaces
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mpr (hK.1.isComplex w.1) w.2⟩
  have := InfinitePlace.card_add_two_mul_card_eq_rank K
  omega

theorem vInv_pos (K : Type) [Field K] [NumberField K] : 0 < Formalism.HermitianLatticesTheory.vInv K := by
  unfold Formalism.HermitianLatticesTheory.vInv
  have hd : (0 : ℝ) < |(discr K : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero K)
  exact div_pos (Real.rpow_pos_of_pos hd _) two_pos

theorem covolume_integerLattice_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) :
    (2⁻¹ : ℝ) ^ InfinitePlace.nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| =
      Formalism.HermitianLatticesTheory.vInv K ^ Formalism.HermitianLatticesTheory.fDeg K := by
  rw [nrComplexPlaces_eq_fDeg hK]
  unfold Formalism.HermitianLatticesTheory.vInv
  have hpos : 0 < Formalism.HermitianLatticesTheory.fDeg K := Fintype.card_pos
  have hf : (Formalism.HermitianLatticesTheory.fDeg K : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [div_pow, ← Real.rpow_natCast (|(discr K : ℝ)| ^ ((1 : ℝ) / (2 * Formalism.HermitianLatticesTheory.fDeg K))),
    ← Real.rpow_mul (abs_nonneg _), Real.sqrt_eq_rpow]
  have e : (1 : ℝ) / (2 * Formalism.HermitianLatticesTheory.fDeg K) * (Formalism.HermitianLatticesTheory.fDeg K : ℝ) = 1 / 2 := by
    field_simp
  rw [e, inv_pow]
  ring

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomScale
section
noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.U0

open WA

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

def cutW (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V) (X : V) : Submodule K V :=
  W ⊓ LinearMap.ker (h X)

def cutM (h : V →ₗ⋆[K] V →ₗ[K] K) (M : AddSubgroup V) (X : V) : AddSubgroup V :=
  M ⊓ (LinearMap.ker (h X)).toAddSubgroup

variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}

theorem mem_cutW {X v : V} : v ∈ cutW h W X ↔ v ∈ W ∧ h X v = 0 := by
  simp [cutW]

theorem mem_cutM {X v : V} : v ∈ cutM h M X ↔ v ∈ M ∧ h X v = 0 := by
  simp [cutM]

theorem symm_zero (hs : h.IsSymm) {x y : V} (hxy : h x y = 0) : h y x = 0 := by
  have e := hs.eq x y
  rw [hxy, map_zero] at e
  exact e.symm

theorem proj_mem (hM : IsLatIn S h W M) {X : V} (hX : X ∈ M) (hu : IsUnitIn S (h X X)) {m : V}
    (hm : m ∈ M) : m - (h X m * (h X X)⁻¹) • X ∈ cutM h M X := by
  have hc : h X m * (h X X)⁻¹ ∈ S := S.mul_mem (hM.int X hX m hm) hu.2.2
  rw [mem_cutM]
  refine ⟨M.sub_mem hm (hM.smul_mem _ hc _ hX), ?_⟩
  rw [map_sub, map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hu.1, mul_one, sub_self]

theorem IsLatIn.cut (hM : IsLatIn S h W M) (X : V) : IsLatIn S h (cutW h W X) (cutM h M X) where
  le := fun m hm => mem_cutW.mpr ⟨hM.le m (mem_cutM.mp hm).1, (mem_cutM.mp hm).2⟩
  smul_mem := fun a ha m hm => mem_cutM.mpr ⟨hM.smul_mem a ha m (mem_cutM.mp hm).1, by
    rw [map_smul, (mem_cutM.mp hm).2, smul_zero]⟩
  int := fun x hx y hy => hM.int x (mem_cutM.mp hx).1 y (mem_cutM.mp hy).1
  span := fun x hx => by
    obtain ⟨t, ht0, ht⟩ := hM.span x (mem_cutW.mp hx).1
    exact ⟨t, ht0, mem_cutM.mpr ⟨ht, by rw [map_smul, (mem_cutW.mp hx).2, smul_zero]⟩⟩

theorem int_of_cut (hM : IsLatIn S h W M) {X : V} (hX : X ∈ M)
    (hu : IsUnitIn S (h X X)) {x : V} (hXx : h X x = 0) (hx : ∀ m ∈ cutM h M X, h m x ∈ S) :
    ∀ m ∈ M, h m x ∈ S := by
  intro m hm
  have hp := hx _ (proj_mem hM hX hu hm)
  rw [LinearMap.map_sub₂, LinearMap.map_smulₛₗ₂, hXx, smul_zero, sub_zero] at hp
  exact hp

theorem IsSD.cut (hM : IsSD S h W M) {X : V} (hX : X ∈ M) (hu : IsUnitIn S (h X X)) :
    IsSD S h (cutW h W X) (cutM h M X) := by
  refine ⟨hM.toIsLatIn.cut X, fun x hx hxS => ?_⟩
  obtain ⟨hxW, hx0⟩ := mem_cutW.1 hx
  exact mem_cutM.2 ⟨hM.dual x hxW (int_of_cut hM.toIsLatIn hX hu hx0 hxS), hx0⟩

theorem IsASD.cut (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm) {z : V}
    (hM : IsASD S π h W M z) {X : V} (hX : X ∈ M) (hu : IsUnitIn S (h X X)) :
    IsASD S π h (cutW h W X) (cutM h M X) (z - (h X z * (h X X)⁻¹) • X) := by
  have hL := hM.toIsLatIn
  have hXz' := (mem_cutM.1 (proj_mem hL hX hu hM.z_mem)).2
  have hsh : ∀ v, h X v = 0 → h (z - (h X z * (h X X)⁻¹) • X) v = h z v := by
    intro v hv
    rw [LinearMap.map_sub₂, LinearMap.map_smulₛₗ₂, hv, smul_zero, sub_zero]
  refine ⟨hL.cut X, proj_mem hL hX hu hM.z_mem, ?_, fun m hm => ?_, fun x hx hzx hxS => ?_⟩
  · obtain ⟨hN0, -, hNi⟩ := hu
    obtain ⟨hu0, hu1, hui⟩ := hM.z_norm
    have hπ0 := hπ.ne
    obtain ⟨s, hsS, hzX⟩ : ∃ s ∈ S, h z X = s * π :=
      ⟨_, hM.z_rad X hX, by rw [inv_mul_cancel_right₀ hπ0]⟩
    have hXz : h X z = star s * π := by
      rw [← hs.eq z X, hzX, map_mul, starRingEnd_apply, starRingEnd_apply, hπ.fix]
    have hNN : starRingEnd K (h X X) = h X X := hs.eq X X
    have e1 : h (z - (h X z * (h X X)⁻¹) • X) X = 0 := symm_zero hs hXz'
    have key : h (z - (h X z * (h X X)⁻¹) • X) (z - (h X z * (h X X)⁻¹) • X)
        = h z z - s * π * (h X X)⁻¹ * (star s * π) := by
      rw [LinearMap.map_sub, LinearMap.map_smul, e1, smul_zero, sub_zero, LinearMap.map_sub₂,
        LinearMap.map_smulₛₗ₂, smul_eq_mul, map_mul, map_inv₀, hNN, hs.eq X z, hzX, hXz]
    have hzz0 : h z z ≠ 0 := fun e => hu0 (by rw [e, zero_mul])
    have hmul : ∀ a b : K, IsUnitIn S a → IsUnitIn S b → IsUnitIn S (a * b) := fun a b ha hb =>
      ⟨mul_ne_zero ha.1 hb.1, S.mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact S.mul_mem ha.2.2 hb.2.2⟩
    have e2 : (h z z - s * π * (h X X)⁻¹ * (star s * π)) * π⁻¹
        = (h z z * π⁻¹) * (1 + π * (-(s * star s * (h X X)⁻¹) * (h z z * π⁻¹)⁻¹)) := by
      field_simp
      ring
    rw [key, e2]
    exact hmul _ _ ⟨hu0, hu1, hui⟩ (hπ.rad _ (S.mul_mem (S.neg_mem
      (S.mul_mem (S.mul_mem hsS (hS.star_mem s hsS)) hNi)) hui))
  · rw [mem_cutM] at hm
    show h _ m * π⁻¹ ∈ S
    rw [hsh m hm.2]
    exact hM.z_rad m hm.1
  · obtain ⟨hxW, hx0⟩ := mem_cutW.1 hx
    rw [hsh x hx0] at hzx
    exact mem_cutM.2 ⟨hM.dual x hxW hzx (int_of_cut hL hX hu hx0 hxS), hx0⟩

theorem exists_isom_move (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) {x y : V}
    (hxy : h x x = h y y) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ x = y ∧ (∀ v, h x v = 0 → h y v = 0 → τ v = v) ∧
      ∀ W : Submodule K V, x ∈ W → y ∈ W → ∀ v, v ∈ W ↔ τ v ∈ W := by
  by_cases hxy' : x = y
  · subst hxy'
    exact ⟨1, one_mem _, rfl, fun v _ _ => rfl, fun W _ _ v => Iff.rfl⟩
  generalize hu_def : x - y = u
  have hD : h u u = h u x + starRingEnd K (h u x) := by
    rw [hs.eq u x, ← hu_def]
    simp only [map_sub, LinearMap.sub_apply]
    rw [hxy]
    ring
  have hu0 : u ≠ 0 := by rw [← hu_def]; exact sub_ne_zero.2 hxy'
  have hD0 : h u x ≠ 0 := by
    intro e
    apply hu0
    apply hd
    rw [hD, e, map_zero, add_zero]
  have hD0' : starRingEnd K (h u x) ≠ 0 := by rwa [map_ne_zero]
  let f : V →ₗ[K] V := LinearMap.id - (LinearMap.toSpanSingleton K V u) ∘ₗ ((h u x)⁻¹ • h u)
  let f' : V →ₗ[K] V :=
    LinearMap.id - (LinearMap.toSpanSingleton K V u) ∘ₗ ((starRingEnd K (h u x))⁻¹ • h u)
  have hf : ∀ v, f v = v - ((h u x)⁻¹ * h u v) • u := fun v => by simp [f]
  have hf' : ∀ v, f' v = v - ((starRingEnd K (h u x))⁻¹ * h u v) • u := fun v => by simp [f']
  have c1 : f ∘ₗ f' = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.id_apply, hf, hf', map_sub, map_smul, smul_eq_mul, sub_sub,
      ← add_smul, sub_eq_self]
    apply smul_eq_zero_of_left
    rw [hD]
    field_simp
    ring
  have c2 : f' ∘ₗ f = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.id_apply, hf, hf', map_sub, map_smul, smul_eq_mul, sub_sub,
      ← add_smul, sub_eq_self]
    apply smul_eq_zero_of_left
    rw [hD]
    field_simp
    ring
  refine ⟨LinearEquiv.ofLinear f f' c1 c2, fun a b => ?_, ?_, fun v hxv hyv => ?_, fun W hxW hyW v => ?_⟩
  · change h (f a) (f b) = h a b
    rw [hf a, hf b]
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.map_smulₛₗ₂, LinearMap.smul_apply,
      smul_eq_mul, map_mul, map_inv₀]
    rw [← hs.eq u a, hD]
    field_simp
    ring
  · change f x = y
    rw [hf, inv_mul_cancel₀ hD0, one_smul, ← hu_def, sub_sub_cancel]
  · change f v = v
    have huv : h u v = 0 := by rw [← hu_def, LinearMap.map_sub₂, hxv, hyv, sub_zero]
    rw [hf, huv, mul_zero, zero_smul, sub_zero]
  · have huW : u ∈ W := by rw [← hu_def]; exact W.sub_mem hxW hyW
    change v ∈ W ↔ f v ∈ W
    rw [hf]
    exact (Submodule.sub_mem_iff_left W (W.smul_mem _ huW)).symm

theorem exists_isom_scale (hs : h.IsSymm) {z : V} (hz : h z z ≠ 0) {b : K} (hb : star b * b = 1) :
    ∃ ψ ∈ Formalism.HermitianLatticesTheory.isom h, ψ z = b • z ∧ ∀ v, h z v = 0 → ψ v = v := by
  have hN : starRingEnd K (h z z) = h z z := hs.eq z z
  have hNi : h z z * (h z z)⁻¹ = 1 := mul_inv_cancel₀ hz
  have hz0 : ∀ (v : V) (c : K), c = 0 → v + c • z = v := fun v c hc => by
    rw [hc, zero_smul, add_zero]
  let f : V →ₗ[K] V :=
    LinearMap.id + (LinearMap.toSpanSingleton K V z) ∘ₗ (((b - 1) * (h z z)⁻¹) • h z)
  let f' : V →ₗ[K] V :=
    LinearMap.id + (LinearMap.toSpanSingleton K V z) ∘ₗ (((star b - 1) * (h z z)⁻¹) • h z)
  have hf : ∀ v, f v = v + ((b - 1) * (h z z)⁻¹ * h z v) • z := fun v => by simp [f]
  have hf' : ∀ v, f' v = v + ((star b - 1) * (h z z)⁻¹ * h z v) • z := fun v => by simp [f']
  have c1 : f ∘ₗ f' = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.id_apply, hf, hf', map_add, map_smul, smul_eq_mul, add_assoc,
      ← add_smul]
    apply hz0
    linear_combination ((h z z)⁻¹ * h z v) * hb +
      ((h z z)⁻¹ * h z v * (b - 1) * (star b - 1)) * hNi
  have c2 : f' ∘ₗ f = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.id_apply, hf, hf', map_add, map_smul, smul_eq_mul, add_assoc,
      ← add_smul]
    apply hz0
    linear_combination ((h z z)⁻¹ * h z v) * hb +
      ((h z z)⁻¹ * h z v * (b - 1) * (star b - 1)) * hNi
  refine ⟨LinearEquiv.ofLinear f f' c1 c2, fun a c => ?_, ?_, fun v hv => ?_⟩
  · change h (f a) (f c) = h a c
    rw [hf a, hf c]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.map_smulₛₗ₂, LinearMap.smul_apply,
      smul_eq_mul, map_mul, map_inv₀, map_sub, map_one, hN]
    rw [← hs.eq z a]
    simp only [starRingEnd_apply]
    linear_combination ((h z z)⁻¹ * star (h z a) * h z c) * hb +
      ((h z z)⁻¹ * star (h z a) * h z c * (b - 1) * (star b - 1)) * hNi
  · change f z = b • z
    rw [hf, mul_assoc, inv_mul_cancel₀ hz, mul_one, sub_smul, one_smul]
    abel
  · change f v = v
    rw [hf, hv, mul_zero, zero_smul, add_zero]

theorem exists_prep (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) {W₁ W₂ : Submodule K V}
    {φ : V ≃ₗ[K] V} (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom h) (hW : ∀ v, v ∈ W₁ ↔ φ v ∈ W₂) {x X : V}
    (hx : x ∈ W₁) (hX : X ∈ W₂) (hxX : h x x = h X X) :
    ∃ φ' ∈ Formalism.HermitianLatticesTheory.isom h, φ' x = X ∧ (∀ v, v ∈ cutW h W₁ x ↔ φ' v ∈ cutW h W₂ X) ∧
      ∀ v, (∀ w ∈ W₁, h w v = 0) → φ' v = φ v := by
  have hφh : ∀ a b, h (φ a) (φ b) = h a b := fun a b => hφ a b
  have hx' : φ x ∈ W₂ := (hW x).1 hx
  obtain ⟨τ, hτ, hτx, hτfix, hτW⟩ := exists_isom_move hs hd (x := φ x) (y := X) (by rw [hφh, hxX])
  have hτh : ∀ a b, h (τ a) (τ b) = h a b := fun a b => hτ a b
  refine ⟨τ * φ, mul_mem hτ hφ, hτx, fun v => ?_, fun v hv => ?_⟩
  · change v ∈ cutW h W₁ x ↔ τ (φ v) ∈ cutW h W₂ X
    rw [mem_cutW, mem_cutW, ← hτW W₂ hx' hX (φ v), ← hW v, ← hτx, hτh, hφh]
  · change τ (φ v) = φ v
    apply hτfix
    · rw [hφh]; exact hv x hx
    · have hX' : φ.symm X ∈ W₁ := (hW _).2 (by rwa [LinearEquiv.apply_symm_apply])
      rw [← LinearEquiv.apply_symm_apply φ X, hφh]
      exact hv _ hX'

theorem mem_iff_of_cut {W₁ W₂ : Submodule K V} {N : AddSubgroup V} (hM : IsLatIn S h W₁ M)
    (hN : IsLatIn S h W₂ N) {x X : V} (hx : x ∈ M) (hX : X ∈ N) (hu : IsUnitIn S (h x x))
    {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (hgx : g x = X)
    (hcut : ∀ v, v ∈ cutM h M x ↔ g v ∈ cutM h N X) : ∀ v, v ∈ M ↔ g v ∈ N := by
  have hgh : ∀ a b, h (g a) (g b) = h a b := fun a b => hg a b
  have hu' : IsUnitIn S (h X X) := by rw [← hgx, hgh]; exact hu
  intro v
  constructor
  · intro hv
    have hp := (hcut _).1 (proj_mem hM hx hu hv)
    have hc : h x v * (h x x)⁻¹ ∈ S := S.mul_mem (hM.int x hx v hv) hu.2.2
    have hgN := (mem_cutM.1 hp).1
    rw [map_sub, map_smul, hgx] at hgN
    have e := N.add_mem hgN (hN.smul_mem _ hc X hX)
    rwa [sub_add_cancel] at e
  · intro hv
    have hp := proj_mem hN hX hu' hv
    have hc : h X (g v) * (h X X)⁻¹ ∈ S := S.mul_mem (hN.int X hX _ hv) hu'.2.2
    have e : g v - (h X (g v) * (h X X)⁻¹) • X = g (v - (h x v * (h x x)⁻¹) • x) := by
      rw [map_sub, map_smul, ← hgx, hgh, hgh]
    rw [e] at hp
    have hm := (mem_cutM.1 ((hcut _).2 hp)).1
    have hc' : h x v * (h x x)⁻¹ ∈ S := by rwa [← hgx, hgh, hgh] at hc
    have e2 := M.add_mem hm (hM.smul_mem _ hc' x hx)
    rwa [sub_add_cancel] at e2

end Formalism.HermitianLattices.Ext.L3.U0
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSqAbsNormOfInert
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

section NoF

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem conjO_coe (x : 𝓞 K) : ((conjO K x : 𝓞 K) : K) = star (x : K) := rfl

theorem conjO_conjO (x : 𝓞 K) : conjO K (conjO K x) = x := by
  apply RingOfIntegers.ext
  rw [conjO_coe, conjO_coe, star_star]

theorem conjIdeal_eq_comap (P : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P.comap (conjO K) := by
  unfold Formalism.HermitianLatticesTheory.conjIdeal
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro r ⟨s, hs, hrs⟩
    have hr : conjO K r = s := by
      apply RingOfIntegers.ext
      rw [conjO_coe]
      have h2 : (r : K) = star (s : K) := hrs
      rw [h2, star_star]
    show conjO K r ∈ P
    rw [hr]
    exact hs
  · intro x hx
    apply Ideal.subset_span
    refine ⟨conjO K x, hx, ?_⟩
    show (x : K) = star ((conjO K x : 𝓞 K) : K)
    rw [conjO_coe, star_star]

theorem exists_sub_conjO_notMem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    ∃ θ : 𝓞 K, θ - conjO K θ ∉ P := by
  obtain ⟨θ, t, ht, hθ⟩ := hK.2.2 P hP
  refine ⟨θ, ?_⟩
  have hθt : conjO K θ = t := by
    apply RingOfIntegers.ext
    rw [conjO_coe]
    exact ht.symm
  rwa [hθt]

omit [StarRing K] in
theorem absNorm_eq_card (I : Ideal (𝓞 K)) : Ideal.absNorm I = Nat.card (𝓞 K ⧸ I) := by
  first
  | rfl
  | (rw [Ideal.absNorm_apply]; rfl)
  | (rw [Ideal.absNorm_apply, Submodule.cardQuot_apply])

theorem conjIdeal_isMaximal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P).IsMaximal := by
  rw [conjIdeal_eq_comap]
  haveI := hP
  exact Ideal.comap_isMaximal_of_surjective (conjO K) (fun y => ⟨conjO K y, conjO_conjO y⟩)

theorem conjIdeal_conjIdeal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (P : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := K) (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) = P := by
  ext x
  simp only [conjIdeal_eq_comap, Ideal.mem_comap, conjO_conjO]

theorem conjIdeal_eq_map (P : Ideal (𝓞 K)) : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P.map (conjO K) := by
  rw [conjIdeal_eq_comap]
  apply le_antisymm
  · intro x hx
    have h := Ideal.mem_map_of_mem (conjO K) (show conjO K x ∈ P from hx)
    rwa [conjO_conjO] at h
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    simpa only [Ideal.mem_comap, conjO_conjO] using hx

theorem absNorm_conjIdeal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (P : Ideal (𝓞 K)) :
    Ideal.absNorm (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) = Ideal.absNorm P := by
  rw [absNorm_eq_card, absNorm_eq_card]
  let e : 𝓞 K ≃+* 𝓞 K :=
    { conjO K with
      invFun := conjO K
      left_inv := fun x => conjO_conjO x
      right_inv := fun x => conjO_conjO x }
  have h : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P.map (e : 𝓞 K →+* 𝓞 K) := by
    rw [conjIdeal_eq_map]
    rfl
  exact (Nat.card_congr (Ideal.quotientEquiv P _ e h).toEquiv).symm

theorem exists_sq_absNorm_of_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) :
    ∃ q : ℕ, Ideal.absNorm P = q ^ 2 := by
  rw [conjIdeal_eq_comap] at hc
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
  rw [absNorm_eq_card]
  exact SplitPrimeIdeals.exists_sq_card_quot conjO_conjO hP hc hθ

end NoF

section WithF

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem conjO_eq_iff_mem_range (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (x : 𝓞 K) :
    conjO K x = x ↔ x ∈ Set.range (algebraMap (𝓞 F) (𝓞 K)) := by
  constructor
  · intro hx
    have hfix : star (x : K) = x := by rw [← conjO_coe, hx]
    obtain ⟨a, ha⟩ := (hF _).1 hfix
    have hint : IsIntegral ℤ (algebraMap F K a) := by
      rw [ha]
      first
      | exact RingOfIntegers.isIntegral_coe x
      | exact x.2
    have ha' : IsIntegral ℤ a := (isIntegral_algebraMap_iff (algebraMap F K).injective).1 hint
    refine ⟨⟨a, ha'⟩, ?_⟩
    apply RingOfIntegers.ext
    show algebraMap F K a = (x : K)
    exact ha
  · rintro ⟨y, rfl⟩
    apply RingOfIntegers.ext
    rw [conjO_coe]
    have hy : ((algebraMap (𝓞 F) (𝓞 K) y : 𝓞 K) : K) = algebraMap F K (y : F) := rfl
    rw [hy]
    exact (hF _).2 ⟨_, rfl⟩

theorem comap_eq_comap_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {P Q : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hQ : Q.IsMaximal) :
    P.comap (algebraMap (𝓞 F) (𝓞 K)) = Q.comap (algebraMap (𝓞 F) (𝓞 K)) ↔ Q = P ∨ Q = Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
  rw [conjIdeal_eq_comap]
  exact SplitPrimeIdeals.comap_eq_comap_iff conjO_conjO (conjO_eq_iff_mem_range hF) hP hQ

theorem exists_maximal_over (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 := by
  haveI := h𝔭
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 K)) := by
    first
    | exact NoZeroSMulDivisors.algebraMap_injective _ _
    | exact FaithfulSMul.algebraMap_injective _ _
    | (intro a b hab
       apply RingOfIntegers.ext
       apply (algebraMap F K).injective
       exact congrArg (fun z : 𝓞 K => (z : K)) hab)
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 K)) ≤ 𝔭 := by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]
    exact bot_le
  exact Ideal.exists_ideal_over_maximal_of_isIntegral 𝔭 hker

theorem absNorm_comap_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) :
    Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) ^ 2 = Ideal.absNorm P := by
  rw [conjIdeal_eq_comap] at hc
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
  rw [absNorm_eq_card, absNorm_eq_card]
  exact SplitPrimeIdeals.card_quot_inert conjO_conjO (conjO_eq_iff_mem_range hF) hP hc hθ

theorem absNorm_comap_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) :
    Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) = Ideal.absNorm P := by
  rw [conjIdeal_eq_comap] at hc
  rw [absNorm_eq_card, absNorm_eq_card]
  exact SplitPrimeIdeals.card_quot_split conjO_conjO (conjO_eq_iff_mem_range hF) hP hc

theorem etaF_comap (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    etaF K F (P.comap (algebraMap (𝓞 F) (𝓞 K))) = if Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P then -1 else 1 := by
  rw [conjIdeal_eq_comap]
  unfold etaF
  by_cases hc : P.comap (conjO K) = P
  · obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
    rw [SplitPrimeIdeals.map_comap_of_inert conjO_conjO (conjO_eq_iff_mem_range hF) hP hc hθ, if_pos hP.isPrime,
      if_pos hc]
  · rw [if_neg (SplitPrimeIdeals.not_isPrime_map_of_split conjO_conjO (conjO_eq_iff_mem_range hF) hP hc),
      if_neg hc]

end WithF

end Formalism.HermitianLattices.Ext.L3
end
end

