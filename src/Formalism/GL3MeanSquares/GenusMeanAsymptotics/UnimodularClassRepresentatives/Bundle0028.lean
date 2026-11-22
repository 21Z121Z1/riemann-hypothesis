import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0027
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0025
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardUnitaryFin
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0012
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0007
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0024
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0015

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AdjoinIntegralOfNonempty
section
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem locF_mem_fibSet (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (S : VecSplit h h')
    {L Λ : Submodule (𝓞 K) V} {Λ' : Submodule (𝓞 K) V'} (hΛ : Λ ∈ fibG S L Λ') {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : locF 𝔭 Λ ∈ fibSet S L 𝔭 Λ' := by
  obtain ⟨⟨-, hgen⟩, hx, hc⟩ := hΛ
  haveI := h𝔭
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 K)) := by
    first
    | exact FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)
    | exact NoZeroSMulDivisors.algebraMap_injective (𝓞 F) (𝓞 K)
    | (intro a b hab
       apply RingOfIntegers.ext
       apply (algebraMap F K).injective
       have := congrArg (fun z : 𝓞 K => (z : K)) hab
       simpa using this)
  obtain ⟨P, hP, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral 𝔭
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  refine ⟨locF_idem 𝔭 Λ, ?_, le_locF 𝔭 Λ hx, ?_⟩
  · obtain ⟨g, hg, e⟩ := hgen P hP
    refine ⟨g, hg, ?_⟩
    rw [← hPc, locF_eq_loc hK hF hP, locF_eq_loc hK hF hP]
    exact e
  · rw [cut_locF, hc]

theorem adjoin_le_of_mem_fibSet (S : VecSplit h h') {L Λ : Submodule (𝓞 K) V}
    {Λ' : Submodule (𝓞 K) V'} {𝔭 : Ideal (𝓞 F)} (hΛ : Λ ∈ fibSet S L 𝔭 Λ') : S.adjoin Λ' ≤ Λ := by
  obtain ⟨-, -, hx, hc⟩ := hΛ
  refine sup_le ?_ ?_
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hx
  · rw [Submodule.map_le_iff_le_comap]
    exact (LocF.le_locF 𝔭 Λ').trans hc.symm.le

private theorem star_algebraMap_of_fixed_field_eq (hF : IsFixF K F) (t : 𝓞 F) :
    star (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t)) =
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) := by
  rw [hF]
  refine ⟨(t : F), ?_⟩
  rw [← IsScalarTower.algebraMap_apply]
  first
  | rw [IsScalarTower.algebraMap_apply (𝓞 F) F K]; rfl
  | simp

theorem adjoin_integral_of_nonempty (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V} (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {Λ' : Submodule (𝓞 K) V'}
    (H : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (fibSet S L 𝔭.1 Λ').Nonempty) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h (S.adjoin Λ') := by
  intro x hx y hy
  rw [← LocF.iInf_locF (F := F) (1 : Submodule (𝓞 K) K), Submodule.mem_iInf]
  intro 𝔭
  obtain ⟨Λ, hΛ⟩ := H 𝔭
  have hle := adjoin_le_of_mem_fibSet S hΛ
  obtain ⟨-, ⟨g, hg, hgΛ⟩, -, -⟩ := hΛ
  have hp : 𝔭.1.IsPrime := 𝔭.2.isPrime
  rw [← hgΛ] at hle
  obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.1 (hle hx)
  obtain ⟨y', hy', rfl⟩ := Submodule.mem_map.1 (hle hy)
  rw [LocF.mem_locF_iff hp] at hx' hy'
  rw [LocF.mem_locF_iff hp]
  obtain ⟨t, ht, htx⟩ := hx'
  obtain ⟨s, hs, hsy⟩ := hy'
  refine ⟨t * s, fun hts => (hp.mem_or_mem hts).elim ht hs, ?_⟩
  have key := hLi _ htx _ hsy
  have e1 : h (g x') (g y') = h x' y' := hg x' y'
  simp only [LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  rw [e1]
  rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) x',
    ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) s) y'] at key
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, LinearMap.map_smul, starRingEnd_apply,
    star_algebraMap_of_fixed_field_eq hF] at key
  convert key using 1
  rw [Algebra.smul_def, map_mul, map_mul, smul_eq_mul, smul_eq_mul]
  simp only [RingHom.id_apply]
  ring

private theorem isLattice_gmap_of_isLattice (g : V ≃ₗ[K] V) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) : Submodule.IsLattice K (Formalism.HermitianLatticesTheory.gmap g L) := by
  obtain ⟨hfg, hspan⟩ := hL
  refine ⟨hfg.map _, ?_⟩
  show Submodule.span K ((L.map ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) : Set V)) = ⊤
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hspan,
    Submodule.map_top, LinearEquiv.range]

private theorem comap_algebraMap_isMaximal_of_isMaximal (P : Ideal (𝓞 K)) (hP : P.IsMaximal) :
    (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal := by
  haveI := hP
  first
  | exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  | exact inferInstance
  | exact Ideal.IsMaximal.under (𝓞 F) P

theorem card_fibG_eq_card_pi (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (S : VecSplit h h')
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) {Λ' : Submodule (𝓞 K) V'}
    (hΛ' : Submodule.IsLattice K Λ') (s : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (hs1 : ∀ 𝔭 ∉ s, fibSet S L 𝔭.1 Λ' = {locF 𝔭.1 (S.adjoin Λ')}) :
    Nat.card (fibG S L Λ') = Nat.card (∀ 𝔭 : s, fibSet S L 𝔭.1.1 Λ') := by
  classical
  have hN : Submodule.IsLattice K (S.adjoin Λ') := (VecSplit.isLattice_adjoin_iff' (S := S) Λ').2 hΛ'
  have hsing : ∀ 𝔭 ∉ s, locF 𝔭.1 (S.adjoin Λ') ∈ fibSet S L 𝔭.1 Λ' := fun 𝔭 h𝔭 => by
    rw [hs1 𝔭 h𝔭]; rfl
  let Φ : fibG S L Λ' → ∀ 𝔭 : s, fibSet S L 𝔭.1.1 Λ' := fun Λ 𝔭 =>
    ⟨locF 𝔭.1.1 Λ.1, locF_mem_fibSet hK hF S Λ.2 𝔭.1.2⟩
  have hloc : ∀ (Λ : fibG S L Λ') (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}), 𝔭 ∉ s →
      locF 𝔭.1 Λ.1 = locF 𝔭.1 (S.adjoin Λ') := by
    intro Λ 𝔭 h𝔭
    have := locF_mem_fibSet hK hF S Λ.2 𝔭.2
    rw [hs1 𝔭 h𝔭] at this
    exact this
  have hinj : Function.Injective Φ := by
    intro Λ₁ Λ₂ e
    apply Subtype.ext
    rw [← LocF.iInf_locF (F := F) Λ₁.1, ← LocF.iInf_locF (F := F) Λ₂.1]
    refine iInf_congr fun 𝔭 => ?_
    by_cases h𝔭 : 𝔭 ∈ s
    · exact congrArg (fun φ => (φ ⟨𝔭, h𝔭⟩).1) e
    · rw [hloc Λ₁ 𝔭 h𝔭, hloc Λ₂ 𝔭 h𝔭]
  have hsurj : Function.Surjective Φ := by
    intro f
    have hg : ∀ 𝔭 : s, ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭.1.1 L) = (f 𝔭).1 := by
      intro 𝔭
      obtain ⟨-, hex, -, -⟩ := (f 𝔭).2
      exact hex
    choose g hgi hgf using hg
    let B : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → Submodule (𝓞 K) V := fun 𝔭 =>
      if h𝔭 : 𝔭 ∈ s then Formalism.HermitianLatticesTheory.gmap (g ⟨𝔭, h𝔭⟩) L else S.adjoin Λ'
    have hBlat : ∀ 𝔭, Submodule.IsLattice K (B 𝔭) := by
      intro 𝔭
      by_cases h𝔭 : 𝔭 ∈ s
      · simp only [B, dif_pos h𝔭]
        exact isLattice_gmap_of_isLattice _ hL
      · simp only [B, dif_neg h𝔭]
        exact hN
    have hBs : ∀ 𝔭 ∉ s, B 𝔭 = S.adjoin Λ' := fun 𝔭 h𝔭 => by simp only [B, dif_neg h𝔭]
    obtain ⟨hMlat, hMloc⟩ := LocF.patch hN s B hBlat hBs
    have hBf : ∀ 𝔭 (h𝔭 : 𝔭 ∈ s), locF 𝔭.1 (B 𝔭) = (f ⟨𝔭, h𝔭⟩).1 := by
      intro 𝔭 h𝔭
      simp only [B, dif_pos h𝔭]
      rw [← gmap_locF]
      exact hgf ⟨𝔭, h𝔭⟩
    have hBmem : ∀ 𝔭, locF 𝔭.1 (B 𝔭) ∈ fibSet S L 𝔭.1 Λ' := by
      intro 𝔭
      by_cases h𝔭 : 𝔭 ∈ s
      · rw [hBf 𝔭 h𝔭]; exact (f ⟨𝔭, h𝔭⟩).2
      · rw [hBs 𝔭 h𝔭]; exact hsing 𝔭 h𝔭
    have hMmem : (⨅ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, locF 𝔭.1 (B 𝔭)) ∈ fibG S L Λ' := by
      refine ⟨⟨hMlat, ?_⟩, ?_, ?_⟩
      · intro P hP
        have h𝔭 : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal := comap_algebraMap_isMaximal_of_isMaximal P hP
        obtain ⟨-, ⟨g', hg', e'⟩, -, -⟩ := hBmem ⟨_, h𝔭⟩
        refine ⟨g', hg', ?_⟩
        rw [← locF_eq_loc hK hF hP, ← locF_eq_loc hK hF hP]
        rw [hMloc ⟨_, h𝔭⟩]
        exact e'
      · rw [Submodule.mem_iInf]
        intro 𝔭
        obtain ⟨-, -, hx, -⟩ := hBmem 𝔭
        exact hx
      · show Submodule.comap _ _ = Λ'
        rw [Submodule.comap_iInf]
        conv_rhs => rw [← LocF.iInf_locF (F := F) Λ']
        refine iInf_congr fun 𝔭 => ?_
        obtain ⟨-, -, -, hc⟩ := hBmem 𝔭
        exact hc
    refine ⟨⟨_, hMmem⟩, ?_⟩
    funext 𝔭
    apply Subtype.ext
    show locF 𝔭.1.1 (⨅ 𝔮 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, locF 𝔮.1 (B 𝔮)) = (f 𝔭).1
    rw [hMloc 𝔭.1]
    exact hBf 𝔭.1 𝔭.2
  exact Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)

end Formalism.HermitianLattices.Ext.L3.LocalizedFibreSets
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LamGEqOneOfOrtho
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem alphaL_of_vd_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) : alphaL h L 𝔭 = alphaStd K 𝔭 (finrank K V) := by
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, u, -, hb, hH, hu, hunit⟩ := OrthogonalBases.exists_orth_basis hK hF hs hd hL hLi h𝔭 hv
  exact IsotropicCounts.alphaL_eq_of_bridge hK h𝔭 u hu hunit fun k => integralBasisSpans.akCount_eq h h𝔭 b hb hH k

theorem alphaStd_pos (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (m : ℕ) : 0 < alphaStd K 𝔭 m := by
  have h1 : Ideal.absNorm 𝔭 ≠ 1 := fun h => h𝔭.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have h0 : Ideal.absNorm 𝔭 ≠ 0 := fun h =>
    (Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F))
      (Ideal.absNorm_eq_zero_iff.mp h)
  have hN : (1 : ℝ) < Ideal.absNorm 𝔭 := by
    have : 1 < Ideal.absNorm 𝔭 := by omega
    exact_mod_cast this
  unfold alphaStd
  apply Finset.prod_pos
  intro j hj
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hpow : (Ideal.absNorm 𝔭 : ℝ) ^ (-(j : ℤ)) < 1 := zpow_lt_one_of_neg₀ hN (by omega)
  have hpos : 0 < (Ideal.absNorm 𝔭 : ℝ) ^ (-(j : ℤ)) := zpow_pos (by linarith) _
  have hη : etaF K F 𝔭 = 1 ∨ etaF K F 𝔭 = -1 := by
    unfold etaF
    split_ifs <;> simp
  rcases hη with h | h <;> rw [h]
  · rw [one_pow, one_mul]
    linarith
  · rcases neg_one_pow_eq_or ℝ j with h' | h' <;> rw [h'] <;> linarith

theorem localMassFactor_of_valuation_eq_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) : lamP h L 𝔭 = 1 := by
  unfold lamP
  rw [hv, mul_zero, pow_zero, mul_one, alphaL_of_vd_zero hK hF hs hd hL hLi h𝔭 hv]
  exact div_self (alphaStd_pos hK hF h𝔭 _).ne'

theorem lamG_eq_one_of_ortho (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {I : Submodule (𝓞 K) V} {n : ℕ}
    (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n) : lamG F h I = 1 := by
  unfold lamG
  have hd := isTotPosDef_of_ortho hK hs hI
  have hL := isLattice_of_ortho hI
  have hLi := isIntegralLat_of_ortho hI
  have : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, lamP h I 𝔭.1 = 1 := by
    intro 𝔭
    obtain ⟨P, hP, hP𝔭⟩ := exists_maximal_over hK hF 𝔭.2
    apply localMassFactor_of_valuation_eq_zero hK hF hs hd hL hLi 𝔭.2
    rw [← hP𝔭]
    exact (isUnimodularAt_iff_vd hK hF hs hd hL hLi hP).mp (isUnimodularAt_of_ortho hK hs hI P hP)
  simp only [this, tprod_one]

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NeBotOfIsMaximal
section
open NumberField Module Filter Topology
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem vF_lt_of_notMem {𝔭 : Ideal (𝓞 F)} {n : 𝓞 F} {e : ℕ} (h : n ∉ 𝔭 ^ e) : vF 𝔭 n < e := by
  unfold vF
  have hne : ({e' : ℕ | n ∈ 𝔭 ^ e'} : Set ℕ).Nonempty := ⟨0, by simp⟩
  have hlt : ∀ k ∈ ({e' : ℕ | n ∈ 𝔭 ^ e'} : Set ℕ), k < e := by
    intro k hk
    by_contra hke
    push_neg at hke
    exact h (Ideal.pow_le_pow_right hke hk)
  have hbdd : BddAbove ({e' : ℕ | n ∈ 𝔭 ^ e'} : Set ℕ) := ⟨e, fun k hk => (hlt k hk).le⟩
  exact hlt _ (Nat.sSup_mem hne hbdd)

theorem ne_bot_of_isMaximal {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 𝔭 ≠ ⊥ := by
  haveI := h𝔭
  exact Ideal.IsMaximal.ne_bot_of_isIntegral_int 𝔭

theorem one_lt_absNorm {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : (1 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := by
  have h1 : Ideal.absNorm 𝔭 ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact h𝔭.ne_top
  have h0 : Ideal.absNorm 𝔭 ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact ne_bot_of_isMaximal h𝔭
  have h2 : 1 < Ideal.absNorm 𝔭 := by omega
  exact_mod_cast h2

end Formalism.HermitianLattices.Ext.L3.BoxSum
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoBallCount
section
open NumberField Module Filter Topology

set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem tendsto_ballCount (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) :
    Tendsto (fun j : ℕ => (ballCount h L ((j : ℝ) ^ 2) : ℝ) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V))
      atTop (𝓝 ((Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ Formalism.HermitianLatticesTheory.fDeg K /
        (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) * normD h L))) := by
  classical
  haveI : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mpr (hK.1.isComplex w.1) w.2⟩
  obtain ⟨b, hbL, ho⟩ := BallB.exists_orth_basis_mem hK hs hd hL
  have hBL : Submodule.span (𝓞 K) (Set.range b) ≤ L :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbL i)
  obtain ⟨N, hN, hNx⟩ := LocF.exists_zsmul_le hL (BallB.isLattice_span b)
  have hlat1 : BallD.lat b (Submodule.span (𝓞 K) (Set.range b)) =
      Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V)))) := BallD.lat_span b
  have hle : Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V)))) ≤ BallD.lat b L := by
    rw [← hlat1]
    intro y hy
    rw [BallD.mem_lat] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hBL hx, rfl⟩
  have hNy : ∀ y ∈ BallD.lat b L,
      N • y ∈ Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V)))) := by
    intro y hy
    rw [← hlat1]
    rw [BallD.mem_lat] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨N • x, hNx x hx, map_zsmul (BallD.emb b) N x⟩
  have hA : ∀ (w : {w : InfinitePlace K // w.IsComplex}) i, 0 < (w.1.embedding (h (b i) (b i))).re :=
    fun w i => hd (b i) (b.ne_zero i) w.1.embedding
  obtain ⟨hidx, hT⟩ := BallA.tendsto_card_of_le (μ := MeasureTheory.volume)
    (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))) (BallD.lat b L) hle hN hNy
    (BallD.isBounded_ballSet hA) BallD.measurableSet_ballSet (BallD.convex_ballSet hA)
  have hfr : finrank ℝ (Fin (finrank K V) → NumberField.mixedEmbedding.mixedSpace K) = 2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      NumberField.mixedEmbedding.finrank, finrank_eq_two_fDeg hK]
    ring
  have hcov : ZLattice.covolume (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))) MeasureTheory.volume =
      Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) := by
    rw [BallC.covolume_piBasis, covolume_integerLattice_eq hK, Fintype.card_fin, ← pow_mul]
  have hidx' : (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))).toAddSubgroup.relIndex
      (BallD.lat b L).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup := by
    rw [← hlat1]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ (BallD.emb_injective b)
  have hI0 : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
    rw [← hidx']; exact hidx
  have hnorm := BallB.normD_mul_relIndex hK hLi b hbL hI0
  have hgdet := BallB.prod_place_gdet hK hs hd b ho
  have hvol := BallD.volume_ballSet hA
  have hP : 0 < ∏ w : {w : InfinitePlace K // w.IsComplex}, ∏ i, (w.1.embedding (h (b i) (b i))).re :=
    Finset.prod_pos fun w _ => Finset.prod_pos fun i _ => hA w i
  have hIr : ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ≠ 0 := by
    exact_mod_cast hI0
  have hND : normD h L ≠ 0 := by
    intro h0
    rw [h0, zero_mul, hgdet] at hnorm
    linarith
  have hV : Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) ≠ 0 := pow_ne_zero _ (vInv_pos K).ne'
  have hlim : MeasureTheory.volume.real (BallD.ballSet h b) *
      ((Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))).toAddSubgroup.relIndex
        (BallD.lat b L).toAddSubgroup : ℝ) /
      ZLattice.covolume (Submodule.span ℤ (Set.range (BallC.piBasis K (Fin (finrank K V))))) MeasureTheory.volume =
      (Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ Formalism.HermitianLatticesTheory.fDeg K /
        (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) * normD h L) := by
    rw [hvol, hcov, hidx', ← hgdet, ← hnorm, nrComplexPlaces_eq_fDeg hK]
    field_simp
  rw [← hlim]
  refine Tendsto.congr' ?_ hT
  filter_upwards [eventually_gt_atTop 0] with j hj
  rw [BallD.card_eq hK ho L hj, hfr]

end Formalism.HermitianLattices.Ext.L3
end
end

