import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0031
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0035
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0011
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0017
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InLZeroIff
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0034
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0025
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0013
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0023

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormLeOfMemBoxSet
section
open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.A5

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem boxSet_finite (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) :
    (boxSet K F T).Finite := by
  refine Set.Finite.of_finite_image (f := fun n : 𝓞 F => algebraMap F K (n : F)) ?_
    (fun a _ b _ hab => RingOfIntegers.ext ((algebraMap F K).injective hab))
  refine (NumberField.Embeddings.finite_of_norm_le K ℂ T).subset ?_
  rintro _ ⟨n, hn, rfl⟩
  refine ⟨map_isIntegral_int (algebraMap F K) (RingOfIntegers.isIntegral_coe n), fun φ => ?_⟩
  have hst : star (algebraMap F K (n : F)) = algebraMap F K (n : F) := (hF _).mpr ⟨_, rfl⟩
  have hc := hK.2.1 φ (algebraMap F K (n : F))
  rw [hst] at hc
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp hc.symm
  have h1 := hn φ
  simp only at h1 ⊢
  rw [hr] at h1 ⊢
  rw [Complex.ofReal_re] at h1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1.1]
  exact h1.2

theorem ne_zero_of_mem_boxSet {T : ℝ} {n : 𝓞 F} (hn : n ∈ boxSet K F T) : n ≠ 0 := by
  rintro rfl
  obtain ⟨φ⟩ := (inferInstance : Nonempty (K →+* ℂ))
  have := (hn φ).1
  simp at this

theorem absNorm_le_of_mem_boxSet (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {T : ℝ} {n : 𝓞 F}
    (hn : n ∈ boxSet K F T) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) ≤ T ^ Formalism.HermitianLatticesTheory.fDeg K := by
  by_contra hlt
  have := box_inter_eq_empty hK hF (b := Ideal.span {n}) (not_le.mp hlt)
  have hmem : n ∈ {n' : 𝓞 F | n' ∈ boxSet K F T ∧ n' ∈ Ideal.span {n}} :=
    ⟨hn, Ideal.mem_span_singleton_self n⟩
  rw [this] at hmem
  exact hmem

def eFac (K : Type) {F : Type} [Field K] [Field F] [NumberField F] [Algebra F K] (m : ℕ)
    (𝔭 : Ideal (𝓞 F)) : ℝ :=
  1 - etaF K F 𝔭 ^ m * (Ideal.absNorm 𝔭 : ℝ) ^ (-(m : ℤ))

theorem eFac_pos {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {m : ℕ} (hm : 1 ≤ m) : 0 < eFac K m 𝔭 := by
  have hq : (1 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by exact_mod_cast two_le_absNorm h𝔭
  have h1 := IdealNormInequalities.zpow_neg_lt_one hq hm
  have h0 : 0 ≤ (Ideal.absNorm 𝔭 : ℝ) ^ (-(m : ℤ)) := zpow_nonneg (by linarith) _
  have hη : |etaF K F 𝔭 ^ m| = 1 := by
    rw [abs_pow]
    unfold etaF
    split_ifs <;> simp
  have h2 : etaF K F 𝔭 ^ m * (Ideal.absNorm 𝔭 : ℝ) ^ (-(m : ℤ)) ≤
      (Ideal.absNorm 𝔭 : ℝ) ^ (-(m : ℤ)) := by
    calc _ ≤ |etaF K F 𝔭 ^ m| * (Ideal.absNorm 𝔭 : ℝ) ^ (-(m : ℤ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ = _ := by rw [hη, one_mul]
  unfold eFac
  linarith

theorem alphaN_eq_stage (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) :
    ∃ k : ℕ, alphaN h L 𝔭 n =
      (nkCount h L 𝔭 k n : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) := by
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    have := two_le_absNorm h𝔭
    exact_mod_cast (by omega : 0 < Ideal.absNorm 𝔭)
  set k0 := 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2
  refine ⟨k0, ?_⟩
  refine Tendsto.limUnder_eq (tendsto_atTop_of_eventually_const (i₀ := k0) fun k hk => ?_)
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [← ih, nkCount_succ hK hF hs hd hL hLi h𝔭 hn hk]
    generalize 2 * finrank K V - 1 = r
    rw [add_mul, one_mul, pow_add]
    push_cast
    field_simp

theorem alphaN_bound (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ C : ℝ, ∀ n : 𝓞 F, n ≠ 0 → 0 ≤ alphaN h L 𝔭 n ∧ alphaN h L 𝔭 n ≤ C := by
  have hq : (0 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
    have := two_le_absNorm h𝔭
    exact_mod_cast (by omega : 0 < Ideal.absNorm 𝔭)
  obtain ⟨C, hC⟩ := nkCount_le hK hF hs hd hL hLi hm h𝔭
  refine ⟨C, fun n hn => ?_⟩
  obtain ⟨k, hk⟩ := alphaN_eq_stage hK hF hs hd hL hLi h𝔭 hn
  rw [hk]
  exact ⟨by positivity, (div_le_iff₀ (by positivity)).mpr (hC k n)⟩

end Formalism.HermitianLattices.Ext.L3.A5
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LaurentAdjoinEqOfImageEq
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WCB

section Alg

variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]

def skewY (h : V →ₗ⋆[K] V →ₗ[K] K) (u w : V) (θ : K) : V →ₗ[K] V :=
  (θ • h u - h w).smulRight u + (h u).smulRight w

theorem skewY_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (u w : V) (θ : K) (z : V) :
    skewY h u w θ z = (θ * h u z - h w z) • u + h u z • w := by
  simp [skewY]

theorem skewY_skew {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (u w : V) {θ : K} (hθ : star θ = -θ)
    (a b : V) : h (skewY h u w θ a) b + h a (skewY h u w θ b) = 0 := by
  have e1 : star (h u a) = h a u := hs.eq u a
  have e2 : star (h w a) = h a w := hs.eq w a
  rw [skewY_apply, skewY_apply]
  simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, star_sub, star_mul', e1, e2, hθ]
  ring

theorem laurent_adjoin_eq_of_image_eq {h : V →ₗ⋆[K] V →ₗ[K] K} (han : ∀ x, h x x = 0 → x = 0) {Y : V →ₗ[K] V}
    (hY : ∀ a b, h (Y a) b + h a (Y b) = 0) {l m : K} (hm : star m = l) (hl : l + m = 1) {z : V}
    (hz : z = m • Y z) : z = 0 := by
  apply han
  have h1 : h z z = m * h z (Y z) := by
    have := congrArg (h z) hz
    rwa [map_smul, smul_eq_mul] at this
  have h2 : h z z = l * h (Y z) z := by
    have := congrArg (fun t => h t z) hz
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, hm] at this
    exact this
  have h3 := hY z z
  have h4 : h z (Y z) = 0 := by linear_combination (-(h z (Y z))) * hl - h1 + h2 + l * h3
  rw [h1, h4, mul_zero]

theorem exists_cayley [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K}
    (han : ∀ x, h x x = 0 → x = 0) {Y : V →ₗ[K] V} (hY : ∀ a b, h (Y a) b + h a (Y b) = 0) {l : K}
    (hl : l + star l = 1) :
    ∃ g : V ≃ₗ[K] V, g ∈ Formalism.HermitianLatticesTheory.isom h ∧ (∀ z, g (z - star l • Y z) = z + l • Y z) ∧
      (∀ z, ∃ z', z' - star l • Y z' = z) ∧ (∀ z, ∃ z', z' + l • Y z' = z) := by
  let S : V →ₗ[K] V := LinearMap.id - star l • Y
  let T : V →ₗ[K] V := LinearMap.id + l • Y
  have hS : Function.Injective S := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hz' : z - star l • Y z = 0 := hz
    exact laurent_adjoin_eq_of_image_eq han hY (star_star l) hl (sub_eq_zero.1 hz')
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hz' : z + l • Y z = 0 := hz
    have hY' : ∀ a b, h ((-Y) a) b + h a ((-Y) b) = 0 := by
      intro a b
      simp only [LinearMap.neg_apply, map_neg]
      linear_combination (-1 : K) * hY a b
    refine laurent_adjoin_eq_of_image_eq (l := star l) (m := l) han hY' rfl (by rw [add_comm]; exact hl) ?_
    rw [LinearMap.neg_apply, smul_neg]
    exact eq_neg_of_add_eq_zero_left hz'
  let eS := LinearEquiv.ofInjectiveEndo S hS
  let eT := LinearEquiv.ofInjectiveEndo T hT
  have heS : ∀ z, eS z = z - star l • Y z := fun z => rfl
  have heT : ∀ z, eT z = z + l • Y z := fun z => rfl
  refine ⟨eS.symm.trans eT, ?_, ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨a, rfl⟩ := eS.surjective x
    obtain ⟨b, rfl⟩ := eS.surjective y
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [heS, heS, heT, heT]
    simp only [map_add, map_sub, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
    linear_combination (l + star l) * hY a b
  · intro z
    rw [← heS, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, heT]
  · intro z
    exact ⟨eS.symm z, by rw [← heS, LinearEquiv.apply_symm_apply]⟩
  · intro z
    exact ⟨eT.symm z, by rw [← heT, LinearEquiv.apply_symm_apply]⟩

end Alg

section Int

open WCA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}

theorem skewY_mem (hp : 𝔭.IsPrime) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {J : ℕ} {u w z : V} {θ : K} (hu : InL 𝔭 A 0 u)
    (hw : InL 𝔭 A J w) (hθ : InI 𝔭 J θ) (hz : InL 𝔭 A 0 z) : InL 𝔭 A J (skewY h u w θ z) := by
  rw [skewY_apply]
  refine InL.add hp ?_ ?_
  · refine (InL.smul hp (i := J) ?_ hu).mono (by omega)
    exact InI.sub hp ((hθ.mul hp (hu.form hp hF hA hz)).mono (by omega))
      ((hw.form hp hF hA hz).mono (by omega))
  · exact (InL.smul hp (hu.form hp hF hA hz) hw).mono (by omega)

theorem mem_of_resolvent (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {u w z z' : V} {θ c : K} (hu : InL 𝔭 A 0 u)
    (hw : InL 𝔭 A 1 w) (hθ : InI 𝔭 1 θ) (hc : InI 𝔭 0 c) (hz : InL 𝔭 A 0 z)
    (e : z' - c • skewY h u w θ z' = z) : InL 𝔭 A 0 z' := by
  have hp := h𝔭.isPrime
  obtain ⟨b, hb⟩ : ∃ b : K, b = h u z' := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : K, a = θ * b - h w z' := ⟨_, rfl⟩
  have e' : z' = z + (c * a) • u + (c * b) • w := by
    rw [skewY_apply, ← hb, ← ha] at e
    rw [← e, smul_add, smul_smul, smul_smul]
    abel
  have eb : b = h u z + c * a * h u u + c * b * h u w := by
    conv_lhs => rw [hb, e']
    rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have ew : h w z' = h w z + c * a * h w u + c * b * h w w := by
    conv_lhs => rw [e']
    rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have Iν : InI 𝔭 0 (h u u) := hu.form hp hF hA hu
  have Ip : InI 𝔭 1 (h u w) := (hu.form hp hF hA hw).mono (by omega)
  have Ir : InI 𝔭 1 (h w u) := (hw.form hp hF hA hu).mono (by omega)
  have Is : InI 𝔭 1 (h w w) := (hw.form hp hF hA hw).mono (by omega)
  have Iβ : InI 𝔭 0 (h u z) := hu.form hp hF hA hz
  have Iγ : InI 𝔭 0 (h w z) := (hw.form hp hF hA hz).mono (by omega)
  have m01 : ∀ {x y : K}, InI 𝔭 0 x → InI 𝔭 1 y → InI 𝔭 1 (x * y) := fun hx hy =>
    (hx.mul hp hy).mono (by omega)
  have m00 : ∀ {x y : K}, InI 𝔭 0 x → InI 𝔭 0 y → InI 𝔭 0 (x * y) := fun hx hy => hx.mul hp hy
  have Icr : InI 𝔭 1 (c * h w u) := m01 hc Ir
  have Iκ : InI 𝔭 1 (θ - c * h w w) := hθ.sub hp (m01 hc Is)
  obtain ⟨hE1, IE1⟩ := InI.unit h𝔭 hF Icr
  have Iε : InI 𝔭 1 (c * h w u - c * h u w - c * h u w * (c * h w u)
      - c * h u u * (θ - c * h w w)) :=
    ((Icr.sub hp (m01 hc Ip)).sub hp (m01 (m00 hc (Ip.mono (by omega))) Icr)).sub hp
      (m01 (m00 hc Iν) Iκ)
  obtain ⟨hD, ID⟩ := InI.unit h𝔭 hF Iε
  have ea : a * (1 + c * h w u) = b * (θ - c * h w w) - h w z := by
    linear_combination ha - ew
  have ebD : b * (1 + (c * h w u - c * h u w - c * h u w * (c * h w u)
      - c * h u u * (θ - c * h w w))) = h u z * (1 + c * h w u) - c * h u u * h w z := by
    linear_combination (1 + c * h w u) * eb + c * h u u * ea
  have Ib : InI 𝔭 0 b := by
    rw [(eq_mul_inv_iff_mul_eq₀ hD).2 ebD]
    exact m00 ((m00 Iβ ((InI.one hp).add hp (Icr.mono (by omega)))).sub hp (m00 (m00 hc Iν) Iγ)) ID
  have Ia : InI 𝔭 0 a := by
    rw [(eq_mul_inv_iff_mul_eq₀ hE1).2 ea]
    exact m00 ((m00 Ib (Iκ.mono (by omega))).sub hp Iγ) IE1
  rw [e']
  have h1 : InL 𝔭 A 0 ((c * a) • u) := (InL.smul hp (m00 hc Ia) hu).mono (by omega)
  have h2 : InL 𝔭 A 0 ((c * b) • w) := (InL.smul hp (m00 hc Ib) hw).mono (by omega)
  exact (hz.add hp h1).add hp h2

end Int

end Formalism.HermitianLattices.Ext.L3.WCB
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocFEqLocFAdjoinCut
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinC

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

private theorem VecSplit_adjoin_le_locF_of_le_locF (S : VecSplit h h') {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsPrime)
    {T T' : Submodule (𝓞 K) V'} (hT : T ≤ locF 𝔭 T') :
    S.adjoin T ≤ locF 𝔭 (S.adjoin T') := by
  refine sup_le ?_ ?_
  · rw [Submodule.span_singleton_le_iff_mem]
    exact LocF.le_locF 𝔭 _ (S.x₀_mem_adjoin T')
  · rw [Submodule.map_le_iff_le_comap]
    intro a ha
    obtain ⟨t, ht, hta⟩ := (LocF.mem_locF_iff h𝔭 T' a).mp (hT ha)
    rw [Submodule.mem_comap, LocF.mem_locF_iff h𝔭]
    refine ⟨t, ht, ?_⟩
    rw [← map_smul]
    exact Submodule.mem_sup_right (Submodule.mem_map_of_mem hta)

theorem locF_adjoin_congr (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (S : VecSplit h h')
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {T T' : Submodule (𝓞 K) V'} (e : locF 𝔭 T = locF 𝔭 T') :
    locF 𝔭 (S.adjoin T) = locF 𝔭 (S.adjoin T') := by
  have key : ∀ {A B : Submodule (𝓞 K) V'}, locF 𝔭 A = locF 𝔭 B →
      locF 𝔭 (S.adjoin A) ≤ locF 𝔭 (S.adjoin B) := by
    intro A B hAB
    have hle := VecSplit_adjoin_le_locF_of_le_locF S h𝔭.isPrime ((LocF.le_locF 𝔭 A).trans hAB.le)
    calc locF 𝔭 (S.adjoin A) ≤ locF 𝔭 (locF 𝔭 (S.adjoin B)) := LocF.locF_mono 𝔭 hle
      _ = locF 𝔭 (S.adjoin B) := LocF.locF_idem 𝔭 _
  exact le_antisymm (key e) (key e.symm)

theorem vd_eq_of_basis (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) {L : Submodule (𝓞 K) V}
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {m : ℕ} (hm : finrank K V = m) (b : Basis (Fin m) K V)
    (hb : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L) {g₀ : 𝓞 K}
    (hg : algebraMap (𝓞 K) K g₀ = (Matrix.of fun i j => h (b i) (b j)).det) :
    vd h L 𝔭 = sSup {e : ℕ | g₀ ∈ extP K 𝔭 ^ e} := by
  subst hm
  rw [← localizedQuotients.vd_locF hF h L h𝔭, ← hb, localizedQuotients.vd_locF hF h _ h𝔭, vd, BallB.discrIdeal_span b hg]
  simp only [Ideal.span_singleton_le_iff_mem]

theorem span_range_cons (S : VecSplit h h') {n : ℕ} (x : Fin n → V') :
    Submodule.span (𝓞 K) (Set.range (Fin.cons S.x₀ (fun i => S.ι (x i)) : Fin (n + 1) → V)) =
      S.adjoin (Submodule.span (𝓞 K) (Set.range x)) := by
  rw [Fin.range_cons, Submodule.span_insert, VecSplit.adjoin, Submodule.map_span, ← Set.range_comp]
  rfl

theorem vd_cut (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : vd h' (S.cut L) 𝔭 = vd h L 𝔭 := by
  have hcL : Submodule.IsLattice K (S.cut L) := by
    rw [← S.isLattice_adjoin_iff, S.adjoin_cut h1 hLi hx]
    exact hL
  obtain ⟨b', hb'L, hb'⟩ := LocalSpans.exists_basis_locF hcL h𝔭
  have hint : ∀ i j, h' (b' i) (b' j) ∈ (1 : Submodule (𝓞 K) K) := fun i j =>
    UnimodularLocalization.isIntegralLat_cut S hLi _ (hb'L i) _ (hb'L j)
  choose H hH using fun i j => Submodule.mem_one.mp (hint i j)
  have hg₀ : algebraMap (𝓞 K) K (Matrix.of H).det =
      (Matrix.of fun i j => h' (b' i) (b' j)).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [hH]
  let c : Fin (finrank K V' + 1) → V := Fin.cons S.x₀ (fun i => S.ι (b' i))
  have hli : LinearIndependent K c := by
    refine linearIndependent_finCons.mpr ⟨?_, ?_⟩
    · exact b'.linearIndependent.map' S.ι (LinearMap.ker_eq_bot.mpr S.inj)
    · intro hmem
      have hle : Submodule.span K (Set.range fun i => S.ι (b' i)) ≤ LinearMap.range S.ι :=
        Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact ⟨b' i, rfl⟩)
      obtain ⟨a, ha⟩ := hle hmem
      exact S.x₀_not_mem_range a ha
  have hcard : Fintype.card (Fin (finrank K V' + 1)) = finrank K V := by
    rw [Fintype.card_fin]
    exact S.finrank_add_one
  let bb := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hbb : ⇑bb = c := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hgram : (Matrix.of fun i j => h (bb i) (bb j)).det =
      (Matrix.of fun i j => h' (b' i) (b' j)).det := by
    rw [hbb, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp [c, S.orth, h1, Fin.succAbove_zero]
    congr 1
    ext i j
    simp [S.isom]
  have hspan : locF 𝔭 (Submodule.span (𝓞 K) (Set.range bb)) = locF 𝔭 L := by
    rw [hbb, span_range_cons S b', locF_adjoin_congr hK hF S h𝔭 hb', S.adjoin_cut h1 hLi hx]
  rw [vd_eq_of_basis hF h h𝔭 S.finrank_add_one.symm bb hspan (hg₀.trans hgram.symm),
    vd_eq_of_basis hF h' h𝔭 rfl b' hb' hg₀]

theorem locF_eq_locF_adjoin_cut (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (S : VecSplit h h')
    (h1 : h S.x₀ S.x₀ = 1) {B : Submodule (𝓞 K) V} (hBi : Formalism.HermitianLatticesTheory.IsIntegralLat h B)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hx : S.x₀ ∈ locF 𝔭 B) :
    locF 𝔭 B = locF 𝔭 (S.adjoin (S.cut B)) := by
  obtain ⟨P, hP, rfl⟩ := LocalizedFibreSets.exists_max_over (K := K) h𝔭
  simp only [locF_eq_loc hK hF hP] at hx ⊢
  refine UnimodularLocalization.loc_eq_loc_adjoin_cut S hP.isPrime hBi hx ?_
  rw [h1, inv_one]
  exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩⟩

theorem vd_cut_of_mem_locF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {B : Submodule (𝓞 K) V}
    (hB : Submodule.IsLattice K B) (hBi : Formalism.HermitianLatticesTheory.IsIntegralLat h B)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hx : S.x₀ ∈ locF 𝔭 B) :
    vd h' (S.cut B) 𝔭 = vd h B 𝔭 := by
  have e5 := locF_eq_locF_adjoin_cut hK hF S h1 hBi h𝔭 hx
  have hcB : Submodule.IsLattice K (S.cut B) := StabilizerLattices.isLattice_cut S hB
  have hcBi := UnimodularLocalization.isIntegralLat_cut S hBi
  calc vd h' (S.cut B) 𝔭 = vd h (S.adjoin (S.cut B)) 𝔭 := by
        rw [← vd_cut hK hF hs hd S h1 ((S.isLattice_adjoin_iff _).mpr hcB)
          ((S.isIntegralLat_adjoin_iff hs h1 _).mpr hcBi) (S.x₀_mem_adjoin _) h𝔭, S.cut_adjoin]
    _ = vd h B 𝔭 := by rw [← localizedQuotients.vd_locF hF h _ h𝔭, ← e5, localizedQuotients.vd_locF hF h _ h𝔭]

theorem exists_isom_cut (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hxg : S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) :
    ∃ g' ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g' (locF 𝔭 (S.cut L)) = S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) ∧
      Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') (locF 𝔭 L) = Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) := by
  have hML : Submodule.IsLattice K (Formalism.HermitianLatticesTheory.gmap g L) := LocalizedFibreSets.isLattice_gmap g hL
  have hMi : Formalism.HermitianLatticesTheory.IsIntegralLat h (Formalism.HermitianLatticesTheory.gmap g L) := UnimodularLocalization.isIntegralLat_gmap hg hLi
  have hxM : S.x₀ ∈ locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g L) := by rwa [← LocalizedFibreSets.gmap_locF]
  have hxL : S.x₀ ∈ locF 𝔭 L := LocF.le_locF 𝔭 L hx
  have hvA : vd h' (S.cut L) 𝔭 = vd h L 𝔭 := vd_cut hK hF hs hd S h1 hL hLi hx h𝔭
  have hvB : vd h' (S.cut (Formalism.HermitianLatticesTheory.gmap g L)) 𝔭 = vd h L 𝔭 := by
    rw [vd_cut_of_mem_locF hK hF hs hd S h1 hML hMi h𝔭 hxM, UnimodularLocalization.vd_gmap hg]
  have hA := StabilizerLattices.isLattice_cut S hL
  have hB := StabilizerLattices.isLattice_cut S hML
  have hAi := UnimodularLocalization.isIntegralLat_cut S hLi
  have hBi := UnimodularLocalization.isIntegralLat_cut S hMi
  have hs' : h'.IsSymm := S.isSymm hs
  have hd' : IsTotPosDef h' := S.isTotPosDef hd
  obtain ⟨g', hg', hg'e⟩ : ∃ g' ∈ Formalism.HermitianLatticesTheory.isom h',
      Formalism.HermitianLatticesTheory.gmap g' (locF 𝔭 (S.cut L)) = locF 𝔭 (S.cut (Formalism.HermitianLatticesTheory.gmap g L)) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv with h0 | h0
    · exact exists_isom_locF_of_vd_zero hK hF hs' hd' hA hB hAi hBi h𝔭 (hvA.trans h0)
        (hvB.trans h0)
    · exact exists_isom_locF_of_vd_one hK hF hs' hd' hA hB hAi hBi h𝔭 (hvA.trans h0)
        (hvB.trans h0)
  refine ⟨g', hg', ?_, ?_⟩
  · rw [hg'e, LocalizedFibreSets.gmap_locF, LocalizedFibreSets.cut_locF]
  · rw [LocalizedFibreSets.gmap_locF g 𝔭 L, locF_eq_locF_adjoin_cut hK hF S h1 hLi h𝔭 hxL, LocalizedFibreSets.gmap_locF,
      SplitBAux.gmap_extOf S g' rfl, locF_eq_locF_adjoin_cut hK hF S h1 hMi h𝔭 hxM]
    exact locF_adjoin_congr hK hF S h𝔭 (by rw [← LocalizedFibreSets.gmap_locF]; exact hg'e)

theorem fibLoc_cut (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) : fibLoc S L 𝔭 (locF 𝔭 (S.cut L)) = 1 := by
  have hxL : S.x₀ ∈ locF 𝔭 L := LocF.le_locF 𝔭 L hx
  rw [fibLoc, Nat.card_eq_one_iff_exists]
  refine ⟨⟨locF 𝔭 L, LocF.locF_idem 𝔭 L, ⟨1, one_mem _, autSub_gmap_one _⟩, hxL,
    by rw [LocalizedFibreSets.cut_locF, LocF.locF_idem]⟩, ?_⟩
  rintro ⟨Λ, -, ⟨g, hg, rfl⟩, hΛx, hΛc⟩
  apply Subtype.ext
  show Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = locF 𝔭 L
  have hMi := UnimodularLocalization.isIntegralLat_gmap hg hLi
  rw [LocalizedFibreSets.gmap_locF] at hΛx hΛc ⊢
  rw [locF_eq_locF_adjoin_cut hK hF S h1 hMi h𝔭 hΛx,
    locF_eq_locF_adjoin_cut hK hF S h1 hLi h𝔭 hxL]
  apply locF_adjoin_congr hK hF S h𝔭
  rw [← LocalizedFibreSets.cut_locF, hΛc, LocF.locF_idem]

theorem isLocReps_cut (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) : IsLocReps S L 𝔭 {locF 𝔭 (S.cut L)} := by
  have hcLi := UnimodularLocalization.isIntegralLat_cut S hLi
  refine ⟨?_, ?_⟩
  · intro T hT
    rw [Finset.mem_singleton] at hT
    subst hT
    refine ⟨LocF.locF_idem 𝔭 _, GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF hcLi, ?_⟩
    rw [fibLoc_cut hK hF hs hd S h1 hL hLi hx h𝔭 hv]
    exact one_ne_zero
  · intro T hT _ hf
    refine ⟨locF 𝔭 (S.cut L), ⟨Finset.mem_singleton_self _, ?_⟩, ?_⟩
    · obtain ⟨g, hg, hgx, hgT⟩ := UnimodularLocalization.exists_of_fibLoc_ne_zero S hf
      rw [← LocalizedFibreSets.gmap_locF] at hgx
      obtain ⟨g', hg', he, -⟩ := exists_isom_cut hK hF hs hd S h1 hL hLi hx h𝔭 hv hg hgx
      refine ⟨g', hg', ?_⟩
      rw [he, LocalizedFibreSets.gmap_locF, LocalizedFibreSets.cut_locF, hgT, hT]
    · rintro T₀ ⟨hT₀, -⟩
      exact Finset.mem_singleton.mp hT₀

theorem exists_aut_map (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) {y : V} (hy : y ∈ locF 𝔭 L) (hyy : h y y = 1) :
    ∃ g ∈ autSub h (locF 𝔭 L), g S.x₀ = y := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hyy
  obtain ⟨g₁, hg₁, hg₁y⟩ := exists_isom_map_of_eq hK hs hd hy0 (hyy.trans h1.symm)
  have hxg : S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap g₁ (locF 𝔭 L) := by
    rw [← hg₁y]
    exact Submodule.mem_map_of_mem hy
  obtain ⟨g', hg', -, he⟩ := exists_isom_cut hK hF hs hd S h1 hL hLi hx h𝔭 hv hg₁ hxg
  refine ⟨g₁⁻¹ * SplitBAux.extOf S g', ⟨mul_mem (inv_mem hg₁) (SplitBAux.extOf_mem_isom hs S hg'), ?_⟩, ?_⟩
  · rw [autSub_gmap_mul, he, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]
  · show g₁⁻¹ (SplitBAux.extOf S g' S.x₀) = y
    rw [SplitBAux.extOf_x₀, ← hg₁y]
    exact g₁.symm_apply_apply y

end Formalism.HermitianLattices.Ext.L3.PinC
end
end

