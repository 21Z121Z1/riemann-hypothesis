import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MulEqZeroIff
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0031
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardLiftMatrix

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DiscrIdealSmulLeIff
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

omit [FiniteDimensional K V] in
theorem isIntegralLat_smul {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (c : 𝓞 F) :
    Formalism.HermitianLatticesTheory.IsIntegralLat (algebraMap F K (c : F) • h) L := by
  intro x hx y hy
  have h1 : algebraMap F K (c : F) ∈ (1 : Submodule (𝓞 K) K) :=
    Submodule.mem_one.2 ⟨algebraMap (𝓞 F) (𝓞 K) c, rfl⟩
  have h2 := Submodule.mul_mem_mul h1 (hLi x hx y hy)
  rw [one_mul] at h2
  exact h2

theorem akCount_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) {k : ℕ} (hk : vF 𝔭 c ≤ k) :
    akCount (algebraMap F K (c : F) • h) L 𝔭 k =
      Ideal.absNorm 𝔭 ^ (2 * vF 𝔭 c * finrank K V ^ 2) * akCount h L 𝔭 (k - vF 𝔭 c) := by
  have : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, -⟩ := localValuationFiltration.exists_local_data hF hs hd hL hLi h𝔭
  have hH' : ∀ i j, algebraMap (𝓞 K) K ((algebraMap (𝓞 F) (𝓞 K) c • H) i j) =
      (algebraMap F K (c : F) • h) (b i) (b j) := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, hH, MeanB.algebraMap_comp]
    rfl
  rw [integralBasisSpans.akCount_eq _ h𝔭 b hb hH', integralBasisSpans.akCount_eq h h𝔭 b hb hH, PinAA.akM_smul hK h𝔭 hc hk,
    Fintype.card_fin]

theorem nkCount_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) (n : 𝓞 F) {k : ℕ} (hk : vF 𝔭 c ≤ k) :
    nkCount (algebraMap F K (c : F) • h) L 𝔭 k (c * n) =
      Ideal.absNorm 𝔭 ^ (2 * vF 𝔭 c * finrank K V) * nkCount h L 𝔭 (k - vF 𝔭 c) n := by
  have : Fact (IsFixF K F) := ⟨hF⟩
  obtain ⟨b, H, D, hb, hH, -⟩ := localValuationFiltration.exists_local_data hF hs hd hL hLi h𝔭
  have hH' : ∀ i j, algebraMap (𝓞 K) K ((algebraMap (𝓞 F) (𝓞 K) c • H) i j) =
      (algebraMap F K (c : F) • h) (b i) (b j) := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, hH, MeanB.algebraMap_comp]
    rfl
  rw [integralBasisSpans.nkCount_eq _ h𝔭 b hb hH', integralBasisSpans.nkCount_eq h h𝔭 b hb hH, PinAA.nkM_smul hK h𝔭 hc n hk,
    Fintype.card_fin]

omit [NumberField K] [StarRing K] [Algebra F K] in
theorem pow_notMem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} {j : ℕ} (hc : c ∉ 𝔭 ^ (j + 1))
    (m : ℕ) : c ^ m ∉ 𝔭 ^ (m * j + 1) := by
  induction m with
  | zero =>
    rw [pow_zero, zero_mul, zero_add, pow_one]
    exact fun e => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 e)
  | succ m ih =>
    rw [show (m + 1) * j + 1 = m * j + j + 1 by ring, pow_succ c]
    exact idealPowerSpanBounds.mul_notMem h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) ih hc

theorem gram_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (c : 𝓞 F) (x : Fin (finrank K V) → V) :
    (Matrix.of fun i j => (algebraMap F K (c : F) • h) (x i) (x j)).det =
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (c ^ finrank K V)) *
        (Matrix.of fun i j => h (x i) (x j)).det := by
  have e : (Matrix.of fun i j => (algebraMap F K (c : F) • h) (x i) (x j)) =
      algebraMap F K (c : F) • Matrix.of fun i j => h (x i) (x j) := by
    ext i j
    rfl
  rw [e, Matrix.det_smul, Fintype.card_fin]
  congr 1
  simp only [map_pow]
  rfl

theorem discrIdeal_smul_le_iff {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0)
    (e : ℕ) :
    discrIdeal (algebraMap F K (c : F) • h) L ≤ extP K 𝔭 ^ (finrank K V * vF 𝔭 c + e) ↔
      discrIdeal h L ≤ extP K 𝔭 ^ e := by
  constructor
  · intro hle
    unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, ez⟩
    apply idealPowerSpanBounds.mem_of_mul_mem h𝔭 (pow_notMem h𝔭 (localValuationFiltration.notMem_pow_vF h𝔭 hc) (finrank K V))
    apply hle
    exact Ideal.subset_span ⟨x, hx, by rw [gram_smul, map_mul, ez]⟩
  · intro hle
    unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, ez⟩
    obtain ⟨g, -, hdet⟩ := LocF.exists_gram hLi x hx
    have hz : z = algebraMap (𝓞 F) (𝓞 K) (c ^ finrank K V) * g.det := by
      apply RingOfIntegers.coe_injective
      show algebraMap (𝓞 K) K z = algebraMap (𝓞 K) K _
      rw [ez, gram_smul, map_mul, hdet]
    have h1 : g.det ∈ extP K 𝔭 ^ e := hle (Ideal.subset_span ⟨x, hx, hdet⟩)
    have h2 : algebraMap (𝓞 F) (𝓞 K) (c ^ finrank K V) ∈ extP K 𝔭 ^ (finrank K V * vF 𝔭 c) := by
      apply localizedQuotients.ι_mem_pow
      rw [mul_comm, pow_mul]
      exact Ideal.pow_mem_pow (localValuationFiltration.mem_pow_vF h𝔭 hc) _
    show z ∈ _
    rw [hz, pow_add]
    exact Ideal.mul_mem_mul h2 h1

theorem vd_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) :
    vd (algebraMap F K (c : F) • h) L 𝔭 = vd h L 𝔭 + finrank K V * vF 𝔭 c := by
  have hD := LocF.discrIdeal_ne_bot (LocF.aniso_of_totPosDef hd) hL hLi
  have hE : extP K 𝔭 ≠ ⊤ := by
    intro e
    apply h𝔭.ne_top
    rw [Ideal.eq_top_iff_one, ← pow_one 𝔭, ← idealPowerSpanBounds.mem_pow_iff (K := K), pow_one, e]
    trivial
  have hb : BddAbove {e : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ e} := by
    by_contra hnb
    rw [not_bddAbove_iff] at hnb
    apply hD
    rw [eq_bot_iff, ← Ideal.iInf_pow_eq_bot_of_isDomain (extP K 𝔭) hE]
    refine le_iInf fun k => ?_
    obtain ⟨e, he, hke⟩ := hnb k
    exact he.trans (Ideal.pow_le_pow_right hke.le)
  have hmem : vd h L 𝔭 ∈ {e : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ e} :=
    Nat.sSup_mem ⟨0, by simp⟩ hb
  have hg : IsGreatest {e : ℕ | discrIdeal (algebraMap F K (c : F) • h) L ≤ extP K 𝔭 ^ e}
      (vd h L 𝔭 + finrank K V * vF 𝔭 c) := by
    constructor
    · rw [add_comm]
      exact (discrIdeal_smul_le_iff hLi h𝔭 hc _).2 hmem
    · intro e' he'
      by_cases hlt : e' ≤ finrank K V * vF 𝔭 c
      · omega
      · obtain ⟨e, rfl⟩ : ∃ e, e' = finrank K V * vF 𝔭 c + e := ⟨e' - finrank K V * vF 𝔭 c, by omega⟩
        have h1 : e ≤ vd h L 𝔭 := le_csSup hb ((discrIdeal_smul_le_iff hLi h𝔭 hc e).1 he')
        omega
  exact hg.csSup_eq

end Formalism.HermitianLattices.Ext.L3.PinA
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsIntegralLatOfForall
section
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.GoodGenusOrbits

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

open UnimodularLocalization GoodPrimeTerms SplitBAux

theorem gmap_inj (g : V ≃ₗ[K] V) {A B : Submodule (𝓞 K) V} :
    Formalism.HermitianLatticesTheory.gmap g A = Formalism.HermitianLatticesTheory.gmap g B ↔ A = B :=
  (gmap_injective g).eq_iff

theorem fibLoc_gmap (hs : h.IsSymm) (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    {g' : V' ≃ₗ[K] V'} (hg' : g' ∈ Formalism.HermitianLatticesTheory.isom h') (T : Submodule (𝓞 K) V') :
    fibLoc S L 𝔭 (Formalism.HermitianLatticesTheory.gmap g' T) = fibLoc S L 𝔭 T := by
  have hG : extOf S g' ∈ Formalism.HermitianLatticesTheory.isom h := extOf_mem_isom hs S hg'
  let e : Submodule (𝓞 K) V ≃ Submodule (𝓞 K) V :=
    { toFun := Formalism.HermitianLatticesTheory.gmap (extOf S g')
      invFun := Formalism.HermitianLatticesTheory.gmap (extOf S g').symm
      left_inv := fun Λ => Formalism.HermitianLatticesTheory.isomAct_gmap_symm _ Λ
      right_inv := fun Λ => Formalism.HermitianLatticesTheory.isomAct_gmap_symm (extOf S g').symm Λ }
  unfold fibLoc
  refine (Nat.card_congr (Equiv.subtypeEquiv e ?_)).symm
  intro Λ
  change _ ↔ (locF 𝔭 (Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ) = Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ ∧
    (∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ) ∧
    S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ ∧
    S.cut (Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ) = locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g' T))
  rw [← LocalizedFibreSets.gmap_locF, gmap_inj, StabilizerLattices.cut_gmap_extOf, ← LocalizedFibreSets.gmap_locF, gmap_inj,
    Formalism.HermitianLatticesTheory.isomAct_mem_gmap, symm_fix (extOf_x₀ S g')]
  refine and_congr_right fun _ => and_congr_left fun _ => ?_
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨extOf S g' * g, Subgroup.mul_mem _ hG hg, autSub_gmap_mul _ _ _⟩
  · rintro ⟨g, hg, e1⟩
    refine ⟨(extOf S g')⁻¹ * g, Subgroup.mul_mem _ (Subgroup.inv_mem _ hG) hg, ?_⟩
    rw [autSub_gmap_mul, e1, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]

theorem fibLoc_eq_of_rel (hs : h.IsSymm) (S : VecSplit h h') (L : Submodule (𝓞 K) V)
    {𝔭 : Ideal (𝓞 F)} {M M₁ : Submodule (𝓞 K) V'}
    (H : ∃ g ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 M) = locF 𝔭 M₁) :
    fibLoc S L 𝔭 M₁ = fibLoc S L 𝔭 M := by
  obtain ⟨g, hg, e⟩ := H
  rw [← fibLoc_locF S L 𝔭 M₁, ← e, fibLoc_gmap hs S L 𝔭 hg, fibLoc_locF]

theorem sameGenus_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (A B : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.SameGenus h A B ↔ ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭.1 A) = locF 𝔭.1 B := by
  constructor
  · rintro H ⟨𝔭, h𝔭⟩
    obtain ⟨P, hP, rfl⟩ := LocalizedFibreSets.exists_max_over (K := K) h𝔭
    rw [locF_eq_loc hK hF hP, locF_eq_loc hK hF hP]
    exact H P hP
  · intro H P hP
    have hm : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
    have := H ⟨_, hm⟩
    rwa [locF_eq_loc hK hF hP, locF_eq_loc hK hF hP] at this

theorem isIntegralLat_of_forall {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] {h₀ : W →ₗ⋆[K] W →ₗ[K] K} {M : Submodule (𝓞 K) W}
    (H : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, IsIntegralAt 𝔭.1 h₀ (locF 𝔭.1 M)) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h₀ M := by
  intro x hx y hy
  rw [← LocF.iInf_locF (F := F) (1 : Submodule (𝓞 K) K), Submodule.mem_iInf]
  exact fun 𝔭 => H 𝔭 x (LocF.le_locF _ _ hx) y (LocF.le_locF _ _ hy)

theorem isIntegralAt_gmap {𝔭 : Ideal (𝓞 F)} {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    {T : Submodule (𝓞 K) V} (hT : IsIntegralAt 𝔭 h T) : IsIntegralAt 𝔭 h (Formalism.HermitianLatticesTheory.gmap g T) := by
  intro x hx y hy
  rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap] at hx hy
  rw [← isom_apply (symm_mem_isom hg)]
  exact hT _ hx _ hy

theorem tprod_natCast_ne_zero {ι : Type*} (f : ι → ℕ) (hf : ∀ i, f i ≠ 0) :
    (∏' i, (f i : ℝ)) ≠ 0 := by
  by_cases hm : Multipliable fun i => (f i : ℝ)
  · have h1 : (1 : ℝ) ≤ ∏' i, (f i : ℝ) := by
      refine ge_of_tendsto hm.hasProd (Filter.Eventually.of_forall fun s => ?_)
      have : (1 : ℝ) ≤ ((∏ i ∈ s, f i : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hf i)
      simpa using this
    linarith
  · rw [tprod_eq_one_of_not_multipliable hm]
    exact one_ne_zero

def Good (F : Type) [Field F] [NumberField F] [Algebra F K] (S : VecSplit h h')
    (L : Submodule (𝓞 K) V) (M : Submodule (𝓞 K) V') : Prop :=
  Submodule.IsLattice K M ∧ ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, fibLoc S L 𝔭.1 M ≠ 0

theorem Good.integral (hF : IsFixF K F) {S : VecSplit h h'} {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {M : Submodule (𝓞 K) V'} (hM : Good F S L M) : Formalism.HermitianLatticesTheory.IsIntegralLat h' M := by
  apply isIntegralLat_of_forall (F := F)
  intro 𝔭
  obtain ⟨C, -, hCi, e⟩ := exists_lattice_of_fibLoc_ne_zero S hL hLi (hM.2 𝔭)
  rw [← e]
  exact isIntegralAt_locF 𝔭.2.isPrime hF hCi

theorem Good.nonempty (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) {S : VecSplit h h'} {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {M : Submodule (𝓞 K) V'} (hM : Good F S L M) : (fibG S L M).Nonempty := by
  have h1 := card_fibG_eq_prod (F := F) hK hF hs hd S hL hLi hM.1
  have h2 := tprod_natCast_ne_zero _ hM.2
  rw [← h1] at h2
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  apply h2
  rw [hne]
  simp

theorem Good.of_genus (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    {S : VecSplit h h'} {L : Submodule (𝓞 K) V} {M M₁ : Submodule (𝓞 K) V'}
    (hM : Good F S L M) (h1 : M₁ ∈ Formalism.HermitianLatticesTheory.genus h' M) : Good F S L M₁ :=
  ⟨h1.1, fun 𝔭 => by
    rw [fibLoc_eq_of_rel hs S L ((sameGenus_iff hK hF M M₁).mp h1.2 𝔭)]
    exact hM.2 𝔭⟩

theorem exists_patch (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {A : Submodule (𝓞 K) V'} (hA : Submodule.IsLattice K A)
    (Z : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (τ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → Submodule (𝓞 K) V')
    (hτ : ∀ 𝔭 ∈ Z, locF 𝔭.1 (τ 𝔭) = τ 𝔭 ∧ fibLoc S L 𝔭.1 (τ 𝔭) ≠ 0)
    (hZ : ∀ 𝔭 ∉ Z, fibLoc S L 𝔭.1 A ≠ 0) :
    ∃ M, Good F S L M ∧ (∀ 𝔭 ∈ Z, locF 𝔭.1 M = τ 𝔭) ∧ ∀ 𝔭 ∉ Z, locF 𝔭.1 M = locF 𝔭.1 A := by
  obtain ⟨M, ⟨hMl, h1, h2⟩, -⟩ := exists_unique_patch hK hF hA Z τ (fun 𝔭 h𝔭 => by
    obtain ⟨C, hC, -, e⟩ := exists_lattice_of_fibLoc_ne_zero S hL hLi (hτ 𝔭 h𝔭).2
    exact ⟨(hτ 𝔭 h𝔭).1, C, hC, by rw [e, (hτ 𝔭 h𝔭).1]⟩)
  refine ⟨M, ⟨hMl, fun 𝔭 => ?_⟩, h1, h2⟩
  by_cases h𝔭 : 𝔭 ∈ Z
  · rw [fibLoc_congr S L (T' := τ 𝔭) (by rw [h1 𝔭 h𝔭, (hτ 𝔭 h𝔭).1])]
    exact (hτ 𝔭 h𝔭).2
  · rw [fibLoc_congr S L (h2 𝔭 h𝔭)]
    exact hZ 𝔭 h𝔭

open scoped Formalism.HermitianLattices.Ext.L3.StabilizerLattices in
theorem exists_locReps (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {M₀ : Submodule (𝓞 K) V'} (hM₀ : Good F S L M₀) (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    ∃ s, IsLocReps S L 𝔭.1 s := by
  classical
  obtain ⟨s', hs'⟩ := exists_fibReps hK hs hd S hL hLi
  let A : Set (Submodule (𝓞 K) V') :=
    {T | locF 𝔭.1 T = T ∧ IsIntegralAt 𝔭.1 h' T ∧ fibLoc S L 𝔭.1 T ≠ 0}
  have hA : ∀ g : Formalism.HermitianLatticesTheory.isom h', ∀ T ∈ A, g • T ∈ A := by
    rintro g T ⟨h1, h2, h3⟩
    refine ⟨?_, isIntegralAt_gmap g.2 h2, ?_⟩
    · change locF 𝔭.1 (Formalism.HermitianLatticesTheory.gmap g.1 T) = Formalism.HermitianLatticesTheory.gmap g.1 T
      rw [← LocalizedFibreSets.gmap_locF, h1]
    · change fibLoc S L 𝔭.1 (Formalism.HermitianLatticesTheory.gmap g.1 T) ≠ 0
      rwa [fibLoc_gmap hs S L 𝔭.1 g.2]
  obtain ⟨s, hs1, hs2⟩ := OrbSum.exists_reps_of_cover (G := Formalism.HermitianLatticesTheory.isom h') A hA
    {T | T ∈ A ∧ T ∈ s'.image (locF 𝔭.1)}
    ((s'.image (locF 𝔭.1)).finite_toSet.subset fun T hT => hT.2) (fun c hc => hc.1) (by
      intro T hT
      obtain ⟨M, hM, h1, -⟩ := exists_patch hK hF S hL hLi hM₀.1 {𝔭} (fun _ => T)
        (fun 𝔮 h𝔮 => by
          rw [Finset.mem_singleton] at h𝔮
          subst h𝔮
          exact ⟨hT.1, hT.2.2⟩) (fun 𝔮 _ => hM₀.2 𝔮)
      obtain ⟨Λ₀, ⟨hΛ₀, g, hg, e⟩, -⟩ := hs'.2 M (hM.nonempty hK hF hs hd hL hLi)
      have e2 : (⟨g, hg⟩ : Formalism.HermitianLatticesTheory.isom h') • locF 𝔭.1 Λ₀ = T := by
        change Formalism.HermitianLatticesTheory.gmap g (locF 𝔭.1 Λ₀) = T
        rw [LocalizedFibreSets.gmap_locF, e, h1 𝔭 (Finset.mem_singleton_self _)]
      refine ⟨locF 𝔭.1 Λ₀, ⟨?_, Finset.mem_image_of_mem _ hΛ₀⟩, ⟨g, hg⟩, e2⟩
      have := hA (⟨g, hg⟩ : Formalism.HermitianLatticesTheory.isom h')⁻¹ T hT
      rwa [← e2, inv_smul_smul] at this)
  refine ⟨s, hs1, fun T h1 h2 h3 => ?_⟩
  obtain ⟨T₀, ⟨hT₀, g, hg⟩, hu⟩ := hs2 T ⟨h1, h2, h3⟩
  exact ⟨T₀, ⟨hT₀, g.1, g.2, hg⟩, fun T₁ ⟨h4, g₁, hg₁, e₁⟩ => hu T₁ ⟨h4, ⟨g₁, hg₁⟩, e₁⟩⟩

theorem isClassReps_filter (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {s' : Finset (Submodule (𝓞 K) V')} (hs' : IsFibReps S L s')
    {M : Submodule (𝓞 K) V'} (hM : Good F S L M)
    [DecidablePred fun Λ' : Submodule (𝓞 K) V' => Formalism.HermitianLatticesTheory.SameGenus h' M Λ'] :
    Formalism.ThetaLiftIndependence.IsClassReps h' M (s'.filter fun Λ' => Formalism.HermitianLatticesTheory.SameGenus h' M Λ') := by
  obtain ⟨he, hi, -⟩ :=
    Formalism.HermitianLatticesTheory.genusBasic (𝓞 K) K V' h' (S.isSymm hs) Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range
  constructor
  · intro Λ' hΛ'
    rw [Finset.mem_filter] at hΛ'
    obtain ⟨Λ, hΛ, -, rfl⟩ := hs'.1 Λ' hΛ'.1
    exact ⟨StabilizerLattices.isLattice_cut S hΛ.1, hΛ'.2⟩
  · intro M₁ hM₁
    obtain ⟨Λ₀, ⟨hΛ₀, g, hg, e⟩, hu⟩ :=
      hs'.2 M₁ ((hM.of_genus hK hF hs hM₁).nonempty hK hF hs hd hL hLi)
    refine ⟨Λ₀, ⟨Finset.mem_filter.mpr ⟨hΛ₀, ?_⟩, g, hg, e⟩, ?_⟩
    · have h1 := hi Λ₀ g hg
      rw [e] at h1
      exact he.trans hM₁.2 (he.symm h1)
    · rintro Λ₁ ⟨h1, h2⟩
      exact hu Λ₁ ⟨(Finset.mem_filter.mp h1).1, h2⟩

end Formalism.HermitianLattices.Ext.L3.GoodGenusOrbits
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SmulGenMemIff
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.EndomorphismScalars

open Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

abbrev Qk (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) : Type :=
  ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)

variable {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {e : V}

private theorem exists_mul_sub_one_mem_pow_of_not_mem_maximal (h𝔭 : 𝔭.IsMaximal) {t : 𝓞 F} (ht : t ∉ 𝔭) (k : ℕ) :
    ∃ s : 𝓞 F, s * t - 1 ∈ 𝔭 ^ k := by
  obtain ⟨y, i, hi, hyi⟩ := h𝔭.exists_inv ht
  refine ⟨y * ∑ l ∈ Finset.range k, i ^ l, ?_⟩
  have h1 : y * t = 1 - i := by rw [← hyi]; ring
  have h2 : y * (∑ l ∈ Finset.range k, i ^ l) * t - 1 = -(i ^ k) := by
    rw [mul_right_comm, h1, mul_neg_geom_sum]; ring
  rw [h2]
  exact (Submodule.neg_mem_iff _).mpr (Ideal.pow_mem_pow hi k)

private theorem algebraMap_mem_extP_pow_of_mem_pow {k : ℕ} {a : 𝓞 F} (ha : a ∈ 𝔭 ^ k) :
    algebraMap (𝓞 F) (𝓞 K) a ∈ extP K 𝔭 ^ k := by
  rw [extP, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ha

theorem mk_eq_smul (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) (x : ↥L) :
    ∃ a : 𝓞 K, (Submodule.Quotient.mk x : Qk L 𝔭 k) = a • Submodule.Quotient.mk ⟨e, he.1⟩ := by
  obtain ⟨t, ht, a, hta⟩ := he.2.2 x x.2
  obtain ⟨s, hs⟩ := exists_mul_sub_one_mem_pow_of_not_mem_maximal h𝔭 ht k
  refine ⟨algebraMap (𝓞 F) (𝓞 K) s * a, ?_⟩
  have hmem : (algebraMap (𝓞 F) (𝓞 K) (s * t - 1)) • x ∈
      ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) :=
    Submodule.smul_mem_smul (algebraMap_mem_extP_pow_of_mem_pow hs) Submodule.mem_top
  have hL : (algebraMap (𝓞 F) (𝓞 K) t) • x = a • (⟨e, he.1⟩ : ↥L) :=
    Subtype.ext (by rw [Submodule.coe_smul, Submodule.coe_smul]; exact hta)
  have hx : x = (algebraMap (𝓞 F) (𝓞 K) s * a) • (⟨e, he.1⟩ : ↥L) -
      (algebraMap (𝓞 F) (𝓞 K) (s * t - 1)) • x := by
    rw [map_sub, map_mul, map_one, sub_smul, one_smul, mul_smul, mul_smul, hL]
    abel
  conv_lhs => rw [hx]
  rw [Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero _).mpr hmem, sub_zero,
    Submodule.Quotient.mk_smul]

theorem smul_top_spec (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) {w : ↥L}
    (hw : w ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ c ∈ extP K 𝔭 ^ k, algebraMap (𝓞 F) (𝓞 K) t • (w : V) = c • e := by
  refine Submodule.smul_induction_on
    (p := fun w : ↥L => ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ c ∈ extP K 𝔭 ^ k,
      algebraMap (𝓞 F) (𝓞 K) t • (w : V) = c • e) hw ?_ ?_
  · intro r hr n _
    obtain ⟨t, ht, a, hta⟩ := he.2.2 n n.2
    refine ⟨t, ht, r * a, Ideal.mul_mem_right _ _ hr, ?_⟩
    rw [Submodule.coe_smul, smul_comm, hta, smul_smul]
  · rintro x y ⟨t1, ht1, c1, hc1, h1⟩ ⟨t2, ht2, c2, hc2, h2⟩
    refine ⟨t1 * t2, fun h => (h𝔭.isPrime.mem_or_mem h).elim ht1 ht2,
      algebraMap (𝓞 F) (𝓞 K) t2 * c1 + algebraMap (𝓞 F) (𝓞 K) t1 * c2,
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ hc1) (Ideal.mul_mem_left _ _ hc2), ?_⟩
    have e1 : algebraMap (𝓞 F) (𝓞 K) (t1 * t2) • (x : V) = algebraMap (𝓞 F) (𝓞 K) t2 • (c1 • e) := by
      rw [map_mul, mul_comm (algebraMap (𝓞 F) (𝓞 K) t1), mul_smul, h1]
    have e2 : algebraMap (𝓞 F) (𝓞 K) (t1 * t2) • (y : V) = algebraMap (𝓞 F) (𝓞 K) t1 • (c2 • e) := by
      rw [map_mul, mul_smul, h2]
    rw [Submodule.coe_add, smul_add, e1, e2, add_smul, mul_smul, mul_smul]

theorem smul_gen_mem_iff (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) (b : 𝓞 K) :
    b • (⟨e, he.1⟩ : ↥L) ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) ↔ b ∈ extP K 𝔭 ^ k := by
  constructor
  · intro hb
    obtain ⟨t, ht, c, hc, htc⟩ := smul_top_spec h𝔭 he k hb
    have h1 : (algebraMap (𝓞 F) (𝓞 K) t * b) • e = c • e := by
      rw [Submodule.coe_smul] at htc
      rw [mul_smul]
      exact htc
    have h2 : algebraMap (𝓞 F) (𝓞 K) t * b = c := by
      rw [← algebraMap_smul K _ e, ← algebraMap_smul K c e] at h1
      exact IsFractionRing.injective (𝓞 K) K (smul_left_injective K he.2.1 h1)
    obtain ⟨s, hs⟩ := exists_mul_sub_one_mem_pow_of_not_mem_maximal h𝔭 ht k
    have hb' : b = algebraMap (𝓞 F) (𝓞 K) s * c -
        algebraMap (𝓞 F) (𝓞 K) (s * t - 1) * b := by
      rw [← h2, map_sub, map_mul, map_one]; ring
    rw [hb']
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hc) (Ideal.mul_mem_right _ _ (algebraMap_mem_extP_pow_of_mem_pow hs))
  · intro hb
    exact Submodule.smul_mem_smul hb Submodule.mem_top

theorem end_surj (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ)
    (X : Module.End (𝓞 K) (Qk L 𝔭 k)) :
    ∃ b : 𝓞 K, algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b = X := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (X (Submodule.Quotient.mk ⟨e, he.1⟩))
  obtain ⟨a, ha⟩ := mk_eq_smul h𝔭 he k y
  refine ⟨a, LinearMap.ext fun z => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨ax, hax⟩ := mk_eq_smul h𝔭 he k x
  rw [Module.algebraMap_end_apply, hax, map_smul, ← hy, ha, smul_comm]

theorem end_eq_zero_iff (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) (b : 𝓞 K) :
    algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b = 0 ↔ b ∈ extP K 𝔭 ^ k := by
  constructor
  · intro h0
    have := LinearMap.congr_fun h0 (Submodule.Quotient.mk ⟨e, he.1⟩)
    rw [Module.algebraMap_end_apply, LinearMap.zero_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at this
    exact (smul_gen_mem_iff h𝔭 he k b).mp this
  · intro hb
    refine LinearMap.ext fun z => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [Module.algebraMap_end_apply, LinearMap.zero_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hb Submodule.mem_top

def endHom (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) :
    (𝓞 K ⧸ extP K 𝔭 ^ k) →+* Module.End (𝓞 K) (Qk L 𝔭 k) :=
  Ideal.Quotient.lift _ (algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)))
    fun b hb => (end_eq_zero_iff h𝔭 he k b).2 hb

theorem endHom_mk (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) (b : 𝓞 K) :
    endHom h𝔭 he k (Ideal.Quotient.mk _ b) =
      algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b := Ideal.Quotient.lift_mk _ _ _

theorem endHom_bijective (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) (k : ℕ) :
    Function.Bijective (endHom h𝔭 he k) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [endHom_mk, end_eq_zero_iff h𝔭 he k] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
  · intro X
    obtain ⟨b, hb⟩ := end_surj h𝔭 he k X
    exact ⟨Ideal.Quotient.mk _ b, by rw [endHom_mk, hb]⟩

end Formalism.HermitianLattices.Ext.L3.EndomorphismScalars
end
end

