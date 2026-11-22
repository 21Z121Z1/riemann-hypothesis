import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0037
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0035
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoSingSSum
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0028
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0025
import Lemmata.GeneralBFactLeftRest.Imports

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CoeMemOfMemSmulTop
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

theorem relIndex_eq_card_image {G α : Type*} [Group G] (H S : Subgroup G) (f : G → α)
    (hf : ∀ a ∈ S, ∀ b ∈ S, f a = f b ↔ a⁻¹ * b ∈ H) :
    H.relIndex S = Nat.card {c : α // ∃ a ∈ S, f a = c} := by
  classical
  show Nat.card (S ⧸ H.subgroupOf S) = _
  apply Nat.card_congr
  refine Equiv.ofBijective (fun q => Quotient.liftOn' q
    (fun a : S => (⟨f a, a, a.2, rfl⟩ : {c : α // ∃ a ∈ S, f a = c})) ?_) ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    show f a = f b
    have hab' : a⁻¹ * b ∈ H.subgroupOf S := QuotientGroup.leftRel_apply.mp hab
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hab'
    exact (hf a a.2 b b.2).mpr hab'
  · intro q₁ q₂ e
    induction q₁ using QuotientGroup.induction_on with
    | H a =>
    induction q₂ using QuotientGroup.induction_on with
    | H b =>
    have e' : f a = f b := congrArg Subtype.val e
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (hf a a.2 b b.2).mp e'
  · rintro ⟨c, a, ha, rfl⟩
    exact ⟨QuotientGroup.mk ⟨a, ha⟩, rfl⟩

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem gmap_eq_iff (a b : V ≃ₗ[K] V) (B : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap a B = Formalism.HermitianLatticesTheory.gmap b B ↔ a⁻¹ * b ∈ glSub B := by
  rw [mem_glSub]
  constructor
  · intro e
    rw [autSub_gmap_mul, ← e, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]
  · intro e
    rw [show b = a * (a⁻¹ * b) from (mul_inv_cancel_left a b).symm, autSub_gmap_mul a, e]

theorem autSub_le_sSub (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    autSub h A ≤ sSub h A 𝔭 k := fun X hX => ⟨hX.2, fun x _ y _ => by
  rw [hX.1 x y, sub_self]
  exact Submodule.zero_mem _⟩

theorem coe_mem_of_mem_smul_top (I : Ideal (𝓞 K)) (A : Submodule (𝓞 K) V) {u : ↥A}
    (hu : u ∈ (I • ⊤ : Submodule (𝓞 K) ↥A)) : (u : V) ∈ I • A := by
  have h2 := Submodule.mem_map_of_mem (f := A.subtype) hu
  rwa [Submodule.map_smul'', Submodule.map_subtype_top] at h2

theorem exists_autSub_mul_nSub (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ k) {X : V ≃ₗ[K] V}
    (hX : X ∈ sSub h (locF 𝔭 A₀) 𝔭 k) :
    ∃ g ∈ autSub h (locF 𝔭 A₀), g⁻¹ * X ∈ nSub (locF 𝔭 A₀) 𝔭 (k - eA h (locF 𝔭 A₀) 𝔭) := by
  obtain ⟨hXg, hXh⟩ := hX
  set A := locF 𝔭 A₀ with hA
  let f : ↥A →ₗ[𝓞 K] ↥A :=
    (((X : V →ₗ[K] V).restrictScalars (𝓞 K)).domRestrict A).codRestrict A
      (fun x => apply_mem hXg x.2)
  have hf : ∀ x : ↥A, ((f x : ↥A) : V) = X x := fun x => rfl
  let Xb : Module.End (𝓞 K) (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A)) :=
    Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top _ f)
  have key : ∀ x x' : ↥A, Submodule.Quotient.mk x' = Xb (Submodule.Quotient.mk x) →
      (x' : V) - X x ∈ extP K 𝔭 ^ k • A := by
    intro x x' hx
    have h1 : x' - f x ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A) := by
      rw [← Submodule.Quotient.eq]
      exact hx
    exact coe_mem_of_mem_smul_top _ _ h1
  have h0 : ∀ {z : V}, z ∈ A → z ∈ extP K 𝔭 ^ 0 • A := fun hz => by rwa [pow_zero_smul]
  obtain ⟨g, hg, hgX⟩ := exists_isom_lift hK hF hs hd hA₀ hA₀i h𝔭 hk Xb (by
    intro x y x' y' hx hy
    rw [congrP_algebraMap_iff_sub_mem h𝔭]
    have hu := key x x' hx
    have hv := key y y' hy
    have e1 : h (x' : V) (y' : V) - h (x : V) (y : V) =
        (h (X x) (X y) - h (x : V) (y : V)) + h ((x' : V) - X x) (y' : V)
          + h (X x) ((y' : V) - X y) := by
      simp only [map_sub, LinearMap.sub_apply]
      ring
    rw [e1]
    refine add_mem (add_mem (hXh x x.2 y y.2) ?_) ?_
    · simpa using form_mem_pK hF hA₀i h𝔭 hu (h0 y'.2)
    · simpa using form_mem_pK hF hA₀i h𝔭 (h0 (apply_mem hXg x.2)) hv)
  refine ⟨g, hg, mul_mem (inv_mem hg.2) hXg, fun x hx => ?_⟩
  have h1 := hgX ⟨x, hx⟩ (f ⟨x, hx⟩) rfl
  have h2 := apply_mem_smul (inv_mem (show g ∈ glSub A from hg.2)) _ ((Submodule.neg_mem _ h1))
  have e : ∀ z : V, g⁻¹ (g z) = z := fun z => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  simpa [e, hf] using h2

theorem relIndex_inf_glSub (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {B₀ : Submodule (𝓞 K) V}
    (hB₀ : Submodule.IsLattice K B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, (sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀)).relIndex (sSub h (locF 𝔭 A₀) 𝔭 k) =
      orbCount h (locF 𝔭 A₀) (locF 𝔭 B₀) := by
  obtain ⟨k₁, hk₁⟩ := nSub_le_glSub hA₀ hB₀ h𝔭
  refine ⟨eA h (locF 𝔭 A₀) 𝔭 + 1 + k₁, fun k hk => ?_⟩
  rw [Subgroup.inf_relIndex_left,
    relIndex_eq_card_image _ _ (fun X => Formalism.HermitianLatticesTheory.gmap X (locF 𝔭 B₀))
      (fun a _ b _ => gmap_eq_iff a b _)]
  unfold orbCount
  refine Nat.card_congr (Equiv.subtypeEquivRight fun C => ⟨?_, ?_⟩)
  · rintro ⟨X, hX, rfl⟩
    obtain ⟨g, hg, hY⟩ := exists_autSub_mul_nSub hK hF hs hd hA₀ hA₀i h𝔭 (by omega) hX
    exact ⟨g, hg.1, hg.2, (gmap_eq_iff g X _).2 (hk₁ _ (by omega) hY)⟩
  · rintro ⟨g, hg, hgA, rfl⟩
    exact ⟨g, autSub_le_sSub h _ 𝔭 k ⟨hg, hgA⟩, rfl⟩

end Formalism.HermitianLattices.Ext.L3.D2
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FactorIdentity
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.Step

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V V' : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

theorem alphaStd_succ (𝔭 : Ideal (𝓞 F)) {m : ℕ} (hm : 1 ≤ m) :
    alphaStd K 𝔭 m = alphaStd K 𝔭 (m - 1) * A5.eFac K m 𝔭 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  unfold alphaStd A5.eFac
  rw [Finset.prod_Icc_succ_top (by omega)]
  simp

theorem factor_identity (q aS e aL aN : ℝ) (m a b : ℕ) (hm : 1 ≤ m) (hq : q ≠ 0) (he : e ≠ 0)
    (hL : aL ≠ 0) :
    q ^ ((m - 1) * (a + b)) * aS * aN / aL =
      (q ^ a) ^ (m - 1) * (aS * e * q ^ (m * b) / aL) * (q ^ b)⁻¹ * (aN / e) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  field_simp
  ring

theorem tprod_localPsi_eq (hLI : LIStat) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L)
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 1 ≤ finrank K V) {n : 𝓞 F} (hn0 : n ≠ 0)
    (hn : h S.x₀ S.x₀ = algebraMap F K (n : F)) :
    ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, psiP S L 𝔭.1 =
      (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * lamG F h L * (normD h L)⁻¹ *
        singS F h L n := by
  classical
  set U : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} :=
    (finite_vd_ne_zero (F := F) hK hF hs hd hL hLi).toFinset ∪ (A5.finite_primes_of_mem hn0).toFinset
    with hU
  have hU1 : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 𝔭 ∉ U → vd h L 𝔭.1 = 0 := by
    intro 𝔭 h𝔭
    rw [hU, Finset.mem_union, not_or, Set.Finite.mem_toFinset] at h𝔭
    exact not_not.mp h𝔭.1
  have hU2 : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 𝔭 ∉ U → n ∉ 𝔭.1 := by
    intro 𝔭 h𝔭
    rw [hU, Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at h𝔭
    exact h𝔭.2
  have hU3 : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 𝔭 ∉ U → vF 𝔭.1 n = 0 := by
    intro 𝔭 h𝔭
    by_contra hne
    have := (A5.mem_pow_iff_le_vF 𝔭.2 hn0 1).mpr (Nat.one_le_iff_ne_zero.mpr hne)
    rw [pow_one] at this
    exact hU2 𝔭 h𝔭 this
  have hpt : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, psiP S L 𝔭.1 =
      ((Ideal.absNorm 𝔭.1 : ℝ) ^ vF 𝔭.1 n) ^ (finrank K V - 1) * lamP h L 𝔭.1 *
        ((Ideal.absNorm 𝔭.1 : ℝ) ^ vd h L 𝔭.1)⁻¹ *
        (alphaN h L 𝔭.1 n / (1 - etaF K F 𝔭.1 ^ finrank K V *
          (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ)))) := by
    intro 𝔭
    rw [hLI K F hK hF V V' h h' S L 𝔭.1 n hs hd 𝔭.2 hn0 hn hL hLi]
    unfold lamP
    rw [alphaStd_succ 𝔭.1 hm]
    have hq : (Ideal.absNorm 𝔭.1 : ℝ) ≠ 0 := by
      have := A5.two_le_absNorm 𝔭.2
      positivity
    exact factor_identity _ _ _ _ _ _ _ _ hm hq (A5.eFac_pos 𝔭.2 hm).ne'
      (alphaL_pos hK hF hs hd hL hLi 𝔭.2).ne'
  have e1 : (Ideal.absNorm (Ideal.span {n}) : ℝ) =
      ∏ 𝔭 ∈ U, (Ideal.absNorm 𝔭.1 : ℝ) ^ vF 𝔭.1 n := by
    rw [absNorm_span_eq_prod n hn0]
    exact tprod_eq_prod fun 𝔭 h𝔭 => by rw [hU3 𝔭 h𝔭, pow_zero]
  have e2 : lamG F h L = ∏ 𝔭 ∈ U, lamP h L 𝔭.1 := by
    unfold lamG
    exact tprod_eq_prod fun 𝔭 h𝔭 => localMassFactor_of_valuation_eq_zero hK hF hs hd hL hLi 𝔭.2 (hU1 𝔭 h𝔭)
  have e3 : normD h L = ∏ 𝔭 ∈ U, (Ideal.absNorm 𝔭.1 : ℝ) ^ vd h L 𝔭.1 := by
    rw [normD_eq_prod hK hF hs hd hL hLi]
    exact tprod_eq_prod fun 𝔭 h𝔭 => by rw [hU1 𝔭 h𝔭, pow_zero]
  have h4 : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, 𝔭 ∉ U →
      alphaN h L 𝔭.1 n / (1 - etaF K F 𝔭.1 ^ finrank K V *
          (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ))) = 1 := by
    intro 𝔭 h𝔭
    rw [alphaN_of_vd_zero_unit hK hF hs hd hL hLi 𝔭.2 (hU1 𝔭 h𝔭) hm (hU2 𝔭 h𝔭)]
    exact div_self (A5.eFac_pos 𝔭.2 hm).ne'
  have e4 : singS F h L n = ∏ 𝔭 ∈ U, alphaN h L 𝔭.1 n / (1 - etaF K F 𝔭.1 ^ finrank K V *
          (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ))) := by
    unfold singS
    exact tprod_eq_prod h4
  have e0 : ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, psiP S L 𝔭.1 = ∏ 𝔭 ∈ U, psiP S L 𝔭.1 := by
    refine tprod_eq_prod fun 𝔭 h𝔭 => ?_
    rw [hpt 𝔭, hU3 𝔭 h𝔭, hU1 𝔭 h𝔭, h4 𝔭 h𝔭, localMassFactor_of_valuation_eq_zero hK hF hs hd hL hLi 𝔭.2 (hU1 𝔭 h𝔭)]
    simp
  rw [e0, e1, e2, e3, e4, ← Finset.prod_pow, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun 𝔭 _ => hpt 𝔭

theorem repMass_eq (hH : HermRepUnram) (hLI : LIStat) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (hm : 2 ≤ finrank K V) {c : ℝ} (hc : MassConst K F (finrank K V - 1) c) {T : ℝ} {n : 𝓞 F}
    (hn : n ∈ boxSet K F T) :
    repMass h L (algebraMap F K (n : F)) = c * lamG F h L * (normD h L)⁻¹ *
      ((Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * singS F h L n) := by
  have hn0 : n ≠ 0 := A5.ne_zero_of_mem_boxSet hn
  obtain ⟨x₀, hx₀⟩ := exists_vec_of_hermRep hH hK hs hd hm (algebraMap F K (n : F))
    ((hF _).mpr ⟨_, rfl⟩) (fun φ => (hn φ).1)
  have hne : h x₀ x₀ ≠ 0 := by
    rw [hx₀]
    intro e
    apply hn0
    apply RingOfIntegers.ext
    exact (algebraMap F K).injective (by rw [e]; simp)
  have h1 := repMass_eq_prod_psi (F := F) hK hF hs hd (vecSplitPerp h hne) hL hLi hc
  have h2 := tprod_localPsi_eq hLI hK hF hs hd (vecSplitPerp h hne) hL hLi (by omega) hn0 hx₀
  rw [h2] at h1
  have h3 : h (vecSplitPerp h hne).x₀ (vecSplitPerp h hne).x₀ = algebraMap F K (n : F) := hx₀
  rw [h3] at h1
  rw [h1]
  ring

end Formalism.HermitianLattices.Ext.L3.Step
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemLocFOfSmulMem
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

namespace RedC

theorem index_eq_card {G T : Type*} [Group G] (N : Subgroup G) (f : G → T) (hs : Function.Surjective f)
    (hf : ∀ a b, f a = f b ↔ a⁻¹ * b ∈ N) : N.index = Nat.card T := by
  first | exact Bl.general_b_fact_left_rest.goal1 .. | (apply Bl.general_b_fact_left_rest.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_rest.goal1 <;> assumption)

def redEnd (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (X : V ≃ₗ[K] V) (hX : X ∈ glSub A) :
    Module.End (𝓞 K) (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A)) :=
  Submodule.mapQ _ _ (((X : V →ₗ[K] V).restrictScalars (𝓞 K)).restrict fun _ hx => apply_mem hX hx)
    (fun x hx => by
      rw [Submodule.mem_comap, Submodule.mem_smul_top_iff]
      rw [Submodule.mem_smul_top_iff] at hx
      exact apply_mem_smul hX _ hx)

theorem redEnd_mk (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (X : V ≃ₗ[K] V) (hX : X ∈ glSub A)
    (x : ↥A) : redEnd A 𝔭 k X hX (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨X x, apply_mem hX x.2⟩ := rfl

theorem mk_eq_redEnd_iff {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {k : ℕ} {X : V ≃ₗ[K] V}
    (hX : X ∈ glSub A) (x x' : ↥A) :
    Submodule.Quotient.mk x' = redEnd A 𝔭 k X hX (Submodule.Quotient.mk x) ↔
      (x' : V) - X x ∈ extP K 𝔭 ^ k • A := by
  rw [redEnd_mk, Submodule.Quotient.eq, Submodule.mem_smul_top_iff]
  rfl

theorem redEnd_eq_iff {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {k : ℕ} {a b : V ≃ₗ[K] V}
    (ha : a ∈ glSub A) (hb : b ∈ glSub A) :
    redEnd A 𝔭 k a ha = redEnd A 𝔭 k b hb ↔ a⁻¹ * b ∈ nSub A 𝔭 k := by
  have e : ∀ z : V, a⁻¹ (a z) = z := fun z => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]
    rfl
  have e' : ∀ z : V, a (a⁻¹ z) = z := fun z => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl
  constructor
  · intro hab
    refine ⟨mul_mem (inv_mem ha) hb, fun x hx => ?_⟩
    have h1 : Submodule.Quotient.mk (⟨b x, apply_mem hb hx⟩ : ↥A) =
        redEnd A 𝔭 k a ha (Submodule.Quotient.mk ⟨x, hx⟩) := by
      rw [hab, redEnd_mk]
    have h2 := apply_mem_smul (inv_mem ha) _ ((mk_eq_redEnd_iff ha _ _).1 h1)
    simpa [e] using h2
  · rintro ⟨-, hab⟩
    refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with | _ x => ?_
    symm
    rw [redEnd_mk, mk_eq_redEnd_iff]
    have h2 := apply_mem_smul ha _ (hab x x.2)
    simpa [e'] using h2

theorem redEnd_cond (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {A₀ : Submodule (𝓞 K) V}
    (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {X : V ≃ₗ[K] V}
    (hX : X ∈ sSub h (locF 𝔭 A₀) 𝔭 k) (x y x' y' : ↥(locF 𝔭 A₀))
    (hx : Submodule.Quotient.mk x' = redEnd (locF 𝔭 A₀) 𝔭 k X hX.1 (Submodule.Quotient.mk x))
    (hy : Submodule.Quotient.mk y' = redEnd (locF 𝔭 A₀) 𝔭 k X hX.1 (Submodule.Quotient.mk y)) :
    CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V)) := by
  rw [congrP_algebraMap_iff_sub_mem h𝔭]
  rw [mk_eq_redEnd_iff] at hx hy
  have z : ∀ w ∈ locF 𝔭 A₀, w ∈ extP K 𝔭 ^ 0 • locF 𝔭 A₀ := fun w hw => by rwa [pow_zero_smul]
  have h1 := hX.2 x x.2 y y.2
  have h2 := form_mem_pK hF hA₀i h𝔭 hx (z _ y'.2)
  have h3 := form_mem_pK hF hA₀i h𝔭 (z _ (apply_mem hX.1 x.2)) hy
  rw [add_zero] at h2
  rw [zero_add] at h3
  have h4 := add_mem (add_mem h1 h2) h3
  have e : h (x' : V) (y' : V) - h (x : V) (y : V) =
      h (X x) (X y) - h (x : V) (y : V) + h ((x' : V) - X x) (y' : V) + h (X x) ((y' : V) - X y) := by
    simp only [map_sub, LinearMap.sub_apply]
    abel
  rw [e]
  exact h4

theorem mem_smul_of_smul_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (A : Submodule (𝓞 K) V) (k : ℕ)
    {t : 𝓞 F} (ht : t ∉ 𝔭) {v : V} (hv : v ∈ A)
    (h : algebraMap (𝓞 F) (𝓞 K) t • v ∈ extP K 𝔭 ^ k • A) : v ∈ extP K 𝔭 ^ k • A := by
  obtain ⟨u, hu⟩ := MeanA.exists_mul_sub_one_mem_pow h𝔭 ht k
  have : v = algebraMap (𝓞 F) (𝓞 K) u • (algebraMap (𝓞 F) (𝓞 K) t • v) -
      algebraMap (𝓞 F) (𝓞 K) (u * t - 1) • v := by
    rw [map_sub, map_mul, map_one, sub_smul, mul_smul, one_smul]; abel
  rw [this]
  exact sub_mem (Submodule.smul_mem _ _ h) (Submodule.smul_mem_smul (localizedQuotients.ι_mem_pow hu) hv)

theorem mem_locF_of_smul_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (A₀ : Submodule (𝓞 K) V)
    {t : 𝓞 F} (ht : t ∉ 𝔭) {v : V} (h : algebraMap (𝓞 F) (𝓞 K) t • v ∈ locF 𝔭 A₀) : v ∈ locF 𝔭 A₀ := by
  have := h𝔭.isPrime
  obtain ⟨s, hs, h1⟩ := (LocalSpans.mem_locF 𝔭 A₀ _).1 h
  refine (LocalSpans.mem_locF 𝔭 A₀ _).2 ⟨s * t, fun h => (h𝔭.isPrime.mem_or_mem h).elim hs ht, ?_⟩
  rwa [map_mul, mul_smul]

theorem exists_lift {A₀ : Submodule (𝓞 K) V} (hA₀ : Submodule.IsLattice K A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ)
    (Y : Module.End (𝓞 K) (↥(locF 𝔭 A₀) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 A₀)))) :
    ∃ D : V →ₗ[K] V, ∀ x : ↥(locF 𝔭 A₀), ∃ hD : D x ∈ locF 𝔭 A₀,
      Submodule.Quotient.mk (⟨D x, hD⟩ : ↥(locF 𝔭 A₀)) = Y (Submodule.Quotient.mk x) := by
  have := h𝔭.isPrime
  obtain ⟨b, -, hb⟩ := LocalSpans.exists_basis_locF hA₀ h𝔭
  have hsp : Submodule.span (𝓞 K) (Set.range b) ≤ locF 𝔭 A₀ := hb ▸ localizedQuotients.le_locF 𝔭 _
  have hbA : ∀ i, b i ∈ locF 𝔭 A₀ := fun i => hsp (Submodule.subset_span ⟨i, rfl⟩)
  choose c hc using fun i => Submodule.Quotient.mk_surjective _ (Y (Submodule.Quotient.mk ⟨b i, hbA i⟩))
  let D : V →ₗ[K] V := b.constr K fun i => (c i : V)
  have hDb : ∀ i, D (b i) = c i := fun i => b.constr_basis K _ i
  have key : ∀ y ∈ Submodule.span (𝓞 K) (Set.range b), ∃ (hy : y ∈ locF 𝔭 A₀) (hD : D y ∈ locF 𝔭 A₀),
      Submodule.Quotient.mk (⟨D y, hD⟩ : ↥(locF 𝔭 A₀)) = Y (Submodule.Quotient.mk ⟨y, hy⟩) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      refine ⟨hbA i, by rw [hDb]; exact (c i).2, ?_⟩
      rw [← hc i]
      congr 1
      exact Subtype.ext (hDb i)
    | zero =>
      refine ⟨zero_mem _, by rw [map_zero]; exact zero_mem _, ?_⟩
      have e1 : (⟨D 0, by rw [map_zero]; exact zero_mem _⟩ : ↥(locF 𝔭 A₀)) = 0 := Subtype.ext (map_zero D)
      have e2 : (⟨0, zero_mem _⟩ : ↥(locF 𝔭 A₀)) = 0 := rfl
      rw [e1, e2, Submodule.Quotient.mk_zero, map_zero]
    | add y z _ _ h1 h2 =>
      obtain ⟨hy, hDy, e1⟩ := h1
      obtain ⟨hz, hDz, e2⟩ := h2
      refine ⟨add_mem hy hz, by rw [map_add]; exact add_mem hDy hDz, ?_⟩
      have e3 : (⟨D (y + z), by rw [map_add]; exact add_mem hDy hDz⟩ : ↥(locF 𝔭 A₀)) =
          ⟨D y, hDy⟩ + ⟨D z, hDz⟩ := Subtype.ext (map_add D y z)
      have e4 : (⟨y + z, add_mem hy hz⟩ : ↥(locF 𝔭 A₀)) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
      rw [e3, e4, Submodule.Quotient.mk_add, Submodule.Quotient.mk_add, map_add, e1, e2]
    | smul a y _ h1 =>
      obtain ⟨hy, hDy, e1⟩ := h1
      have hs : D (a • y) = a • D y := LinearMap.map_smul_of_tower D a y
      refine ⟨Submodule.smul_mem _ a hy, by rw [hs]; exact Submodule.smul_mem _ a hDy, ?_⟩
      have e3 : (⟨D (a • y), by rw [hs]; exact Submodule.smul_mem _ a hDy⟩ : ↥(locF 𝔭 A₀)) =
          a • ⟨D y, hDy⟩ := Subtype.ext hs
      have e4 : (⟨a • y, Submodule.smul_mem _ a hy⟩ : ↥(locF 𝔭 A₀)) = a • ⟨y, hy⟩ := rfl
      rw [e3, e4, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul, map_smul, e1]
  refine ⟨D, fun x => ?_⟩
  have hx : (x : V) ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) := by rw [hb]; exact x.2
  obtain ⟨t, ht, hxt⟩ := (LocalSpans.mem_locF 𝔭 _ _).1 hx
  obtain ⟨hy, hDy, e1⟩ := key _ hxt
  have hs : D (algebraMap (𝓞 F) (𝓞 K) t • (x : V)) = algebraMap (𝓞 F) (𝓞 K) t • D x :=
    LinearMap.map_smul_of_tower D _ _
  have hDx : D x ∈ locF 𝔭 A₀ := mem_locF_of_smul_mem h𝔭 A₀ ht (hs ▸ hDy)
  refine ⟨hDx, ?_⟩
  obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (Y (Submodule.Quotient.mk x))
  rw [← hw, Submodule.Quotient.eq, Submodule.mem_smul_top_iff]
  have e4 : (⟨algebraMap (𝓞 F) (𝓞 K) t • (x : V), hy⟩ : ↥(locF 𝔭 A₀)) = algebraMap (𝓞 F) (𝓞 K) t • x := rfl
  rw [e4, Submodule.Quotient.mk_smul, Y.map_smul, ← hw, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
    Submodule.mem_smul_top_iff] at e1
  refine mem_smul_of_smul_mem h𝔭 _ k ht (sub_mem hDx w.2) ?_
  have e5 : algebraMap (𝓞 F) (𝓞 K) t • (D x - (w : V)) =
      D (algebraMap (𝓞 F) (𝓞 K) t • (x : V)) - algebraMap (𝓞 F) (𝓞 K) t • (w : V) := by
    rw [hs, smul_sub]
  show algebraMap (𝓞 F) (𝓞 K) t • (D x - (w : V)) ∈ _
  rw [e5]
  exact e1

theorem exists_redEnd_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : eA h (locF 𝔭 A₀) 𝔭 + 1 ≤ k)
    (Y : Module.End (𝓞 K) (↥(locF 𝔭 A₀) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 A₀))))
    (hY : ∀ x y x' y' : ↥(locF 𝔭 A₀), Submodule.Quotient.mk x' = Y (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = Y (Submodule.Quotient.mk y) →
      CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V))) :
    ∃ (X : V ≃ₗ[K] V) (hX : X ∈ sSub h (locF 𝔭 A₀) 𝔭 k), redEnd (locF 𝔭 A₀) 𝔭 k X hX.1 = Y := by
  obtain ⟨g, hg, hgY⟩ := exists_isom_lift hK hF hs hd hA₀ hA₀i h𝔭 hk Y hY
  have hgA : g ∈ glSub (locF 𝔭 A₀) := hg.2
  obtain ⟨D, hD⟩ := exists_lift hA₀ h𝔭 k Y
  have hle : extP K 𝔭 ^ (k - eA h (locF 𝔭 A₀) 𝔭) • locF 𝔭 A₀ ≤ extP K 𝔭 • locF 𝔭 A₀ :=
    Submodule.smul_mono_left (Ideal.pow_le_self (by omega))
  let E : V →ₗ[K] V := (g⁻¹ : V ≃ₗ[K] V).toLinearMap ∘ₗ D - LinearMap.id
  have hE : E ∈ endL (locF 𝔭 A₀) (extP K 𝔭 • locF 𝔭 A₀) := by
    intro x hx
    obtain ⟨hDx, h1⟩ := hD ⟨x, hx⟩
    have h2 := apply_mem_smul (inv_mem hgA) _ (hle (hgY ⟨x, hx⟩ ⟨D x, hDx⟩ h1))
    have h3 := neg_mem h2
    have e3 : E x = -(g⁻¹ (g x - D x)) := by
      simp [E]
    rw [e3]
    exact h3
  obtain ⟨Z, hZ, hZA⟩ := exists_equiv_of_mem_endL hA₀ h𝔭 hE
  have hXD : ∀ x, (g * Z) x = D x := fun x => by
    rw [LinearEquiv.mul_apply, hZ]
    simp [E]
  have hXA : g * Z ∈ glSub (locF 𝔭 A₀) := mul_mem hgA hZA
  have hmk : ∀ x : ↥(locF 𝔭 A₀), Submodule.Quotient.mk (⟨(g * Z) x, apply_mem hXA x.2⟩ : ↥(locF 𝔭 A₀)) =
      Y (Submodule.Quotient.mk x) := fun x => by
    obtain ⟨hDx, h1⟩ := hD x
    rw [← h1]
    congr 1
    exact Subtype.ext (hXD x)
  refine ⟨g * Z, ⟨hXA, fun x hx y hy => ?_⟩, ?_⟩
  · exact (congrP_algebraMap_iff_sub_mem h𝔭).1 (hY ⟨x, hx⟩ ⟨y, hy⟩ _ _ (hmk ⟨x, hx⟩) (hmk ⟨y, hy⟩))
  · refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with | _ x => ?_
    rw [redEnd_mk]
    exact hmk x

end RedC

theorem alphaL_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, alphaL h (locF 𝔭 A₀) 𝔭 =
      (akCount h (locF 𝔭 A₀) 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V ^ 2) := by
  refine ⟨2 * vd h A₀ 𝔭 + 1, fun k hk => ?_⟩
  have h1 : alphaL h (locF 𝔭 A₀) 𝔭 = alphaL h A₀ 𝔭 := by
    unfold alphaL
    simp_rw [akCount_locF hF h A₀ 𝔭 h𝔭]
  rw [h1, akCount_locF hF h A₀ 𝔭 h𝔭]
  exact firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hA₀ hA₀i h𝔭 hk

theorem akCount_eq_relIndex (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, akCount h (locF 𝔭 A₀) 𝔭 k =
      (nSub (locF 𝔭 A₀) 𝔭 k).relIndex (sSub h (locF 𝔭 A₀) 𝔭 k) := by
  refine ⟨eA h (locF 𝔭 A₀) 𝔭 + 1, fun k hk => ?_⟩
  symm
  unfold akCount Subgroup.relIndex
  refine RedC.index_eq_card _
    (fun X : ↥(sSub h (locF 𝔭 A₀) 𝔭 k) => ⟨RedC.redEnd (locF 𝔭 A₀) 𝔭 k X.1 X.2.1,
      RedC.redEnd_cond hF hA₀i h𝔭 X.2⟩) ?_ ?_
  · rintro ⟨Y, hY⟩
    obtain ⟨X, hX, e⟩ := RedC.exists_redEnd_eq hK hF hs hd hA₀ hA₀i h𝔭 hk Y hY
    exact ⟨⟨X, hX⟩, Subtype.ext e⟩
  · intro a b
    rw [Subtype.mk.injEq, RedC.redEnd_eq_iff, Subgroup.mem_subgroupOf]
    rfl

end Formalism.HermitianLattices.Ext.L3.D2
end
end

