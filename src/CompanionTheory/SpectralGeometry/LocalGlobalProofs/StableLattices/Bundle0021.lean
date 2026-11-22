import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0008
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0015
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0014
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0002
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0017
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import Formalism.RealPlaceAnalysis.Bundle0004
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousHermScal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0032
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.KsetSubset
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0020

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecompositionGL
section
open CompanionTheory.Rg.Fl Matrix
namespace GlobalTheory.CompanionTheory.CartGL

theorem stCartanGL : StCartanGL := by
  unfold CompanionTheory.Rg.Fl.StCartanGL CompanionTheory.Rg.Fl.HasCartan
  intro L _ _ _ n U hU
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_uniformizer_nonarchimedean L
  have hp1 : ‖(p : L)‖ < 1 := by
    unfold GlobalTheory.CompanionTheory.CartGL.IsUnif at hp
    exact hp.1
  obtain ⟨ε, hε, hεU⟩ := GlobalTheory.T.congruence_subgroups_neighborhood_basis L n (U : Set (GL (Fin n) L)) hU U.one_mem
  obtain ⟨r, hr0, hr1, hrε⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ r ≤ ε :=
    ⟨min ε (1 / 2), lt_min hε (by norm_num), lt_of_le_of_lt (min_le_right _ _) (by norm_num), min_le_left _ _⟩
  have h0 : 0 ≤ r := hr0.le
  have h1 : r ≤ 1 := hr1.le
  refine ⟨GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1, fun x hx => hεU r h0 h1 hrε hx,
    GlobalTheory.T.congruence_subgroup_is_open L n r h0 h1 hr0, GlobalTheory.T.congruence_subgroup_is_compact L n r h0 h1, ?_⟩
  obtain ⟨d, c, hc, hcK⟩ := GlobalTheory.T.compact_subgroup_finite_open_cosets (GL (Fin n) L) (GlobalTheory.CompanionTheory.CartGL.congK L n 1 zero_le_one le_rfl)
    (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1) (GlobalTheory.T.congruence_subgroup_is_compact L n 1 zero_le_one le_rfl) (GlobalTheory.T.congruence_subgroup_is_open L n r h0 h1 hr0)
  refine ⟨d, n + 2, ?_⟩
  unfold CompanionTheory.Rg.Fl.IsCartan
  refine ⟨c, GlobalTheory.CompanionTheory.CartGL.tGen p, ?_, ?_, ?_, ?_⟩
  · intro i k
    constructor
    · intro hk
      exact GlobalTheory.T.congruence_subgroup_normal_in_maximal_compact L n r h0 h1 (c i) k (hc i) hk
    · intro hk
      have h2 := GlobalTheory.T.congruence_subgroup_normal_in_maximal_compact L n r h0 h1 (c i)⁻¹ _ (Subgroup.inv_mem _ (hc i)) hk
      have e : (c i)⁻¹ * (c i * k * (c i)⁻¹) * (c i)⁻¹⁻¹ = k := by group
      rwa [e] at h2
  · intro i j
    show GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n i) * GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n j) =
      GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n j) * GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n i)
    rw [← GlobalTheory.CompanionTheory.CartGL.dPow_add, ← GlobalTheory.CompanionTheory.CartGL.dPow_add, add_comm]
  · intro g
    obtain ⟨a, ha, k₁, hk₁, k₂, hk₂, rfl⟩ := GlobalTheory.T.cartan_decomposition_gl_nonarchimedean L n p hp g
    obtain ⟨i, κ₁, hκ₁, rfl⟩ := hcK k₁ hk₁
    obtain ⟨j, κ₂, hκ₂, rfl⟩ := hcK k₂ hk₂
    refine ⟨i, j, GlobalTheory.CompanionTheory.CartGL.dPow p a, GlobalTheory.T.antitone_powers_in_dominant_monoid L n p a ha, κ₁, hκ₁, (c j)⁻¹ * κ₂ * c j, ?_, ?_⟩
    · have h2 := GlobalTheory.T.congruence_subgroup_normal_in_maximal_compact L n r h0 h1 (c j)⁻¹ κ₂ (Subgroup.inv_mem _ (hc j)) hκ₂
      rwa [inv_inv] at h2
    · group
  · intro s hs s' hs' k hk
    obtain ⟨a₁, ha₁, rfl⟩ := GlobalTheory.T.dominant_monoid_elements_are_antitone_powers L n p s hs
    obtain ⟨a₂, ha₂, rfl⟩ := GlobalTheory.T.dominant_monoid_elements_are_antitone_powers L n p s' hs'
    have hkA : ∀ i j, ‖((k : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := fun i j =>
      (GlobalTheory.CompanionTheory.CartGL.mem_congK.mp hk i j).1
    obtain ⟨Um, Wm, hUl, hWu, hUr, hWr, hUW⟩ := GlobalTheory.T.near_identity_upper_lower_factorization L n r h0 hr1 (k : Matrix (Fin n) (Fin n) L) hkA
    obtain ⟨kU, -, hkUv⟩ := GlobalTheory.T.matrix_near_identity_in_congruence_subgroup L n r h0 h1 hr1 Um hUr
    obtain ⟨kW, -, hkWv⟩ := GlobalTheory.T.matrix_near_identity_in_congruence_subgroup L n r h0 h1 hr1 Wm hWr
    have hk_eq : k = kU * kW := Units.ext (by rw [Units.val_mul, hkUv, hkWv, hUW])
    have hA : GlobalTheory.CompanionTheory.CartGL.dPow p a₁ * kU * (GlobalTheory.CompanionTheory.CartGL.dPow p a₁)⁻¹ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 := by
      have hb := GlobalTheory.T.dominant_conjugation_preserves_upper_congruence L n p hp1 a₁ ha₁ r kU (fun i j hij => by rw [hkUv]; exact hUl i j hij)
        (fun i j => by rw [hkUv]; exact hUr i j)
      obtain ⟨k', hk', hk'v⟩ := GlobalTheory.T.matrix_near_identity_in_congruence_subgroup L n r h0 h1 hr1 _ hb
      rw [← Units.ext hk'v]
      exact hk'
    have hB : (GlobalTheory.CompanionTheory.CartGL.dPow p a₂)⁻¹ * kW * GlobalTheory.CompanionTheory.CartGL.dPow p a₂ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 := by
      have hb := GlobalTheory.T.dominant_conjugation_preserves_lower_congruence L n p hp1 a₂ ha₂ r kW (fun i j hij => by rw [hkWv]; exact hWu i j hij)
        (fun i j => by rw [hkWv]; exact hWr i j)
      obtain ⟨k', hk', hk'v⟩ := GlobalTheory.T.matrix_near_identity_in_congruence_subgroup L n r h0 h1 hr1 _ hb
      rw [← Units.ext hk'v]
      exact hk'
    refine ⟨_, hA, _, hB, ?_⟩
    rw [hk_eq]
    group

end GlobalTheory.CompanionTheory.CartGL
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CompactFiniteAdelesAwayPBoundedDenominators
section
open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.KModExists

open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open PI.UpqRep (IsKFin IsKTypeOf IsKStableOn)
open CompanionTheory.D.DSIC

theorem kHighest_iff {n : ℕ} (ε : Fin n → Bool) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ι : V →ₗ[ℂ] W) (hι : Function.Injective ι) (E' : Fin n → Fin n → Module.End ℂ V)
    (E : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b v, ι (E' a b v) = E a b (ι v)) (μ : Fin n → ℝ) (v : V) :
    KHighest ε E' μ v ↔ KHighest ε E μ (ι v) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a => ?_, fun a b hab he => ?_⟩
    · rw [← h, h1 a, map_smul]
    · rw [← h, h2 a b hab he, map_zero]
  · rintro ⟨h1, h2⟩
    refine ⟨fun a => hι ?_, fun a b hab he => hι ?_⟩
    · rw [h, h1 a, map_smul]
    · rw [h, h2 a b hab he, map_zero]

theorem glRel_of_inj {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ι : V →ₗ[ℂ] W) (hι : Function.Injective ι) (E' : Fin n → Fin n → Module.End ℂ V)
    (E : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b v, ι (E' a b v) = E a b (ι v)) (hE : GlRel E) :
    GlRel E' := by
  intro a b c d
  ext v
  apply hι
  have := LinearMap.congr_fun (hE a b c d) (ι v)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, h]
  rw [this]
  split_ifs <;> simp [h]

theorem kModExists (h1 : SmMod) (h2 : KFinSm) (h3 : KFinStab) (h4 : StabLink) (h5 : HWofType) (h6 : TypeOfHW) :
    CompanionTheory.D.LK.KModExists := by
  intro n ε H _ _ _ σ hσ hirr
  obtain ⟨S, E, hS⟩ := h1 n ε H σ hσ
  obtain ⟨V₀, hV, hst⟩ := h3 n ε H σ S E hσ hS
  have hsm : ∀ v, IsKFin ε σ v → v ∈ S := fun v hv => (hS.mem v).2 (h2 n ε H σ hσ hirr v hv)
  set D : Submodule ℂ H := V₀.map S.subtype with hD
  have hmem : ∀ v, v ∈ D ↔ IsKFin ε σ v := by
    intro v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hV x).1 hx
    · intro hv
      exact ⟨⟨v, hsm v hv⟩, (hV _).2 hv, rfl⟩
  have hDS : D ≤ S := fun v hv => hsm v ((hmem v).1 hv)
  let ι : D →ₗ[ℂ] S := Submodule.inclusion hDS
  have hι : Function.Injective ι := Submodule.inclusion_injective hDS
  have hin : ∀ a b (v : D), (S.subtype ∘ₗ E a b ∘ₗ ι) v ∈ D := fun a b v =>
    ⟨E a b (ι v), hst a b _ ((hV _).2 ((hmem _).1 v.2)), rfl⟩
  let E' : Fin n → Fin n → Module.End ℂ D := fun a b => LinearMap.codRestrict D (S.subtype ∘ₗ E a b ∘ₗ ι) (hin a b)
  have hE' : ∀ a b v, ι (E' a b v) = E a b (ι v) := fun a b v => Subtype.ext rfl
  have hT : ∀ T : Submodule ℂ H, FiniteDimensional ℂ T → IsKStableOn ε σ T → T ≤ D :=
    fun T hf hs v hv => (hmem v).2 ⟨T, hf, hv, hs⟩
  refine ⟨D, E', hmem, fun X hX v => hS.real X hX (ι v), glRel_of_inj ι hι E' E hE' hS.gl,
    fun a b x y => hS.unit a b (ι x) (ι y), ?_, ?_, ?_⟩
  · intro x
    obtain ⟨T, hf, hx, hs⟩ := (hmem _).1 x.2
    have hTD := hT T hf hs
    have hTS : T ≤ S := hTD.trans hDS
    have f1 : FiniteDimensional ℂ (T.comap S.subtype) :=
      (Submodule.comapSubtypeEquivOfLe hTS).symm.finiteDimensional
    have f2 : FiniteDimensional ℂ (T.comap D.subtype) :=
      (Submodule.comapSubtypeEquivOfLe hTD).symm.finiteDimensional
    have hk : KStab ε E (T.comap S.subtype) := by
      rw [h4 n ε H σ S E hσ hS _ f1, Submodule.map_comap_subtype, inf_eq_right.2 hTS]
      exact hs
    exact ⟨T.comap D.subtype, f2, fun a b hab v hv => hk a b hab (ι v) hv, hx⟩
  · intro μ T hty
    have hTD := hT T hty.1 hty.2.1
    obtain ⟨v, hv0, hvT, hv⟩ := h5 n ε H σ S E hσ hS μ T hty (hTD.trans hDS)
    refine ⟨⟨v, hTD hvT⟩, fun h => hv0 (Subtype.ext (congrArg (fun z : D => (z : H)) h)), hvT, ?_⟩
    exact (kHighest_iff ε ι hι E' E hE' μ _).2 hv
  · intro μ x hx0 hx
    exact h6 n ε H σ S E hσ hS μ (ι x) (fun h => hx0 (hι (h.trans (map_zero ι).symm))) ((hmem _).1 x.2)
      ((kHighest_iff ε ι hι E' E hE' μ _).1 hx)

end GlobalTheory.CompanionTheory.KModExists
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsAdFam
section
open Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LKInvLift

open Formalism.REAL (GlRel)
open CompanionTheory.D.DSIC (KStab)
open CompanionTheory.D.LK

variable {n : ℕ}

def AdFam {ι : Type} [Fintype ι] (w : ι → FreeAlgebra ℂ (Fin n × Fin n)) (M : Fin n → Fin n → Matrix ι ι ℂ) : Prop :=
  (∀ c d i j, star (M c d j i) = M d c i j) ∧
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E →
    ∀ c d i, E c d * ev E (w i) - ev E (w i) * E c d = ∑ j, M c d j i • ev E (w j)

theorem exists_adFam (a : FreeAlgebra ℂ (Fin n × Fin n)) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → FreeAlgebra ℂ (Fin n × Fin n)) (M : Fin n → Fin n → Matrix ι ι ℂ)
      (t : ι → ℂ), AdFam w M ∧ a = ∑ i, t i • w i := by
  classical
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    refine ⟨Unit, inferInstance, fun _ => 1, fun _ _ => 0, fun _ => r, ⟨?_, ?_⟩, ?_⟩
    · intro c d i j; simp
    · intro V _ _ E _ c d i; simp
    · simp [Algebra.algebraMap_eq_smul_one]
  | grade1 x =>
    refine ⟨Fin n × Fin n, inferInstance, fun p => FreeAlgebra.ι ℂ p,
      fun c d => Matrix.of fun j i => (if d = i.1 ∧ j = (c, i.2) then 1 else 0) - (if i.2 = c ∧ j = (i.1, d) then 1 else 0),
      Pi.single x 1, ⟨?_, ?_⟩, ?_⟩
    · rintro c d ⟨i1, i2⟩ ⟨j1, j2⟩
      simp only [Matrix.of_apply, star_sub, Prod.mk.injEq, apply_ite star, star_one, star_zero]
      congr 1
      · apply if_congr _ rfl rfl
        constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h2.symm, h1.symm, h3.symm⟩
      · apply if_congr _ rfl rfl
        constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h3, h2.symm, h1⟩
    · rintro V _ _ E hE c d ⟨a, b⟩
      have h := hE c d a b
      simp only [ev, FreeAlgebra.lift_ι_apply, Matrix.of_apply, sub_smul, Finset.sum_sub_distrib]
      rw [h]
      congr 1
      · by_cases h1 : d = a <;> simp [h1]
      · by_cases h1 : b = c <;> simp [h1]
    · simp [Pi.single_apply]
  | mul a b ha hb =>
    obtain ⟨ι, _, w, M, t, ⟨h1, h2⟩, rfl⟩ := ha
    obtain ⟨ι', _, w', M', t', ⟨h1', h2'⟩, rfl⟩ := hb
    refine ⟨ι × ι', inferInstance, fun p => w p.1 * w' p.2,
      fun c d => Matrix.of fun j i => (if j.2 = i.2 then M c d j.1 i.1 else 0) + (if j.1 = i.1 then M' c d j.2 i.2 else 0),
      fun p => t p.1 * t' p.2, ⟨?_, ?_⟩, ?_⟩
    · rintro c d ⟨i1, i2⟩ ⟨j1, j2⟩
      simp only [Matrix.of_apply, star_add, apply_ite star, star_zero, h1, h1', eq_comm]
    · rintro V _ _ E hE c d ⟨i, i'⟩
      have e1 := h2 V E hE c d i
      have e2 := h2' V E hE c d i'
      have : E c d * ev E (w i * w' i') - ev E (w i * w' i') * E c d =
          (E c d * ev E (w i) - ev E (w i) * E c d) * ev E (w' i') +
            ev E (w i) * (E c d * ev E (w' i') - ev E (w' i') * E c d) := by
        rw [map_mul]; noncomm_ring
      simp only []
      rw [this, e1, e2]
      simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib, Fintype.sum_prod_type, ite_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
        mul_smul_comm]
      congr 1
      rw [Finset.sum_comm]
      simp
    · rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
      simp only [smul_mul_smul_comm]
  | add a b ha hb =>
    obtain ⟨ι, _, w, M, t, ⟨h1, h2⟩, rfl⟩ := ha
    obtain ⟨ι', _, w', M', t', ⟨h1', h2'⟩, rfl⟩ := hb
    refine ⟨ι ⊕ ι', inferInstance, Sum.elim w w', fun c d => Matrix.fromBlocks (M c d) 0 0 (M' c d),
      Sum.elim t t', ⟨?_, ?_⟩, ?_⟩
    · rintro c d (i | i) (j | j) <;> simp [← h1 d c, ← h1' d c]
    · rintro V _ _ E hE c d (i | i)
      · simp [Fintype.sum_sum_type, h2 V E hE]
      · simp [Fintype.sum_sum_type, h2' V E hE]
    · simp [Fintype.sum_sum_type]

theorem AdFam.comm {ι : Type} [Fintype ι] {w : ι → FreeAlgebra ℂ (Fin n × Fin n)}
    {M : Fin n → Fin n → Matrix ι ι ℂ} (h : AdFam w M) {V : Type} [AddCommGroup V] [Module ℂ V]
    {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) (c d : Fin n) (t : ι → ℂ) :
    E c d * ev E (∑ i, t i • w i) - ev E (∑ i, t i • w i) * E c d = ev E (∑ j, (M c d *ᵥ t) j • w j) := by
  simp only [map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    ← Finset.sum_sub_distrib, ← smul_sub, h.2 V E hE, Finset.smul_sum, Matrix.mulVec, dotProduct, Finset.sum_smul,
    smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem invLift : InvLift := by
  classical
  intro n ε V _ _ E L a hE hL ha
  obtain ⟨ι, _, w, M, t, hM, rfl⟩ := exists_adFam a
  let N : Submodule ℂ (EuclideanSpace ℂ ι) :=
    { carrier := {x | ∀ s ∈ L, ev E (∑ i, x i • w i) s = 0}
      add_mem' := by
        intro x y hx hy s hs
        have := hx s hs
        have := hy s hs
        simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib, map_add, LinearMap.add_apply, *, add_zero]
      zero_mem' := by intro s hs; simp
      smul_mem' := by
        intro r x hx s hs
        have := hx s hs
        simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, map_smul, LinearMap.smul_apply, this,
          smul_zero] }
  have hN : ∀ x, x ∈ N ↔ ∀ s ∈ L, ev E (∑ i, x i • w i) s = 0 := fun x => Iff.rfl
  let D : Fin n → Fin n → Module.End ℂ (EuclideanSpace ℂ ι) := fun c d => Matrix.toEuclideanLin (M c d)
  have hD : ∀ c d x, (D c d x).ofLp = M c d *ᵥ x.ofLp := fun c d x => rfl
  have hadj : ∀ c d x y, ⟪x, D c d y⟫_ℂ = ⟪D d c x, y⟫_ℂ := by
    intro c d x y
    have : M d c = (M c d)ᴴ := by ext i j; simp [Matrix.conjTranspose_apply, ← hM.1 c d]
    simp only [D]
    rw [this, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_left]
  have hDN : ∀ c d, ε c = ε d → ∀ x ∈ N, D c d x ∈ N := by
    intro c d hcd x hx
    rw [hN] at hx ⊢
    intro s hs
    rw [hD, ← hM.comm hE]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hx s hs, hx _ (hL c d hcd s hs), map_zero, sub_zero]
  have ht : ∀ c d, ε c = ε d → D c d (WithLp.toLp 2 t) ∈ N := by
    intro c d hcd
    rw [hN]
    intro s hs
    rw [hD, ← hM.comm hE]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, ha c d hcd s hs, sub_self]
  obtain ⟨k, hk, t', ht', e⟩ := N.exists_add_mem_mem_orthogonal (WithLp.toLp 2 t)
  have h0 : ∀ c d, ε c = ε d → D c d t' = 0 := by
    intro c d hcd
    have h1 : D c d t' ∈ N := by
      have := N.sub_mem (ht c d hcd) (hDN c d hcd k hk)
      rwa [e, map_add, add_sub_cancel_left] at this
    rw [← inner_self_eq_zero (𝕜 := ℂ), hadj]
    exact (Submodule.mem_orthogonal _ _).1 ht' _ (hDN d c hcd.symm _ h1)
  refine ⟨∑ i, t' i • w i, ?_, ?_⟩
  · intro V' _ _ E' hE' c d hcd
    have := hM.comm hE' c d t'.ofLp
    rw [← hD, h0 c d hcd] at this
    have h2 : ev E' (∑ j, (0 : EuclideanSpace ℂ ι).ofLp j • w j) = 0 := by simp
    rw [h2] at this
    exact sub_eq_zero.1 this
  · intro s hs
    have e' : ∀ i, t i = k i + t' i := fun i => congrArg (fun x : EuclideanSpace ℂ ι => x i) e
    have := (hN k).1 hk s hs
    simp only [e', add_smul, Finset.sum_add_distrib, map_add, LinearMap.add_apply, this, zero_add]

end GlobalTheory.CompanionTheory.LKInvLift
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsUnitOfTmulOne
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.QTie

theorem isUnit_of_tmul_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {R : Type} [CommRing R] [Algebra F R] {c : R}
    (h : IsUnit (c ⊗ₜ[F] (1 : E))) : IsUnit c := by
  obtain ⟨bb, -, -⟩ := GlobalTheory.CompanionTheory.SW.OneHerm.exists_basis hσ
  have h1 := h.map (Algebra.norm R (S := R ⊗[F] E))
  have h2 := Algebra.norm_algebraMap_of_basis (Algebra.TensorProduct.basis R bb) c
  rw [Algebra.TensorProduct.algebraMap_apply] at h2
  have h3 : Algebra.norm R (c ⊗ₜ[F] (1 : E)) = c ^ 2 := by simpa using h2
  rw [h3] at h1
  exact (isUnit_pow_iff two_ne_zero).mp h1

def hermAdd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] : R ≃+ HermR R σ 1 where
  toFun := hermScal R σ
  invFun := GlobalTheory.CompanionTheory.SW.OneHerm.hermHalf R σ
  left_inv := GlobalTheory.CompanionTheory.SW.OneHerm.hermHalf_hermScal R hσ
  right_inv := GlobalTheory.CompanionTheory.SW.OneHerm.hermScal_hermHalf R hσ
  map_add' a b := by
    apply Subtype.ext
    ext i j
    change (a + b) ⊗ₜ[F] (1 : E) = a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] (1 : E)
    rw [TensorProduct.add_tmul]

end GlobalTheory.CompanionTheory.SW.QTie

open GlobalTheory.CompanionTheory.SW.OneHerm GlobalTheory.CompanionTheory.SW.QTie in

theorem GlobalTheory.CompanionTheory.SW.QTie.fib_eq_gramFib : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure R), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ν {c | ¬ IsUnit c} = 0 → μ {X | ¬ IsUnit ((fun X : Fin 1 → Fin M → R ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (R) σ J (X 0)) X)} = 0 → ∀ fib, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (fun X : Fin 1 → Fin M → R ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (R) σ J (X 0)) id Set.univ ν {c | IsUnit c} fib → ∀ m, IsGramFib R σ J 1 μ (ν.map (hermScal R σ)) m → ∀ c : R, IsUnit c → fib c = m (hermScal R σ c) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR μ ν hμ hν hνu hμu fib hfib m hm c hc
  classical
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hTK, hLK, hSK, hTK2, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI := hTK
  haveI := hLK
  haveI := hSK
  haveI := hTK2
  haveI := hBor 1 M
  obtain ⟨hL, hS2, hT, hB, hg⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R 1
  haveI := hL
  haveI := hS2
  haveI := hT
  haveI := hB
  obtain ⟨g, hgc, hgf⟩ := hg M J hJ
  obtain ⟨hf1, hf2, hf3⟩ := hfib
  let q : (Fin 1 → Fin M → R ⊗[F] E) → R := fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR R σ J (X 0)
  have hq : ∀ X, q X = hermHalf R σ (g X) := by
    intro X
    change _ = algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((g X : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0)
    rw [← hgf X]
    rfl
  have hgq : ∀ X, g X = hermScal R σ (q X) := by
    intro X
    rw [hq, hermScal_hermHalf R hσ]
  have hdet : ∀ S : HermR R σ 1, IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det ↔ IsUnit (hermHalf R σ S) := by
    intro S
    have hS : ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))).det = (hermHalf R σ S) ⊗ₜ[F] (1 : E) := by
      conv_lhs => rw [← hermScal_hermHalf R hσ S]
      rw [Matrix.det_fin_one]
      rfl
    rw [hS]
    refine ⟨isUnit_of_tmul_one hσ, fun h => ?_⟩
    exact h.map (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[F] E)
  have hU : {X | IsUnit (gramR R σ J X).det} = {X | IsUnit (q X)} := by
    ext X
    simp only [Set.mem_setOf_eq]
    rw [hgf X, hdet, hq]
  have hUnull : μ ({X | IsUnit (gramR R σ J X).det}ᶜ) = 0 := by
    rw [hU]
    exact hμu
  have hemb : MeasurableEmbedding (hermScal R σ) := (hermHomeo R hσ).measurableEmbedding
  have hν' : (ν.map (hermScal R σ)).IsAddHaarMeasure :=
    (hermAdd hσ R).isAddHaarMeasure_map ν (continuous_hermScal R σ) (continuous_hermHalf R σ)
  let m' : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E) := fun S =>
    if IsUnit (hermHalf R σ S) then fib (hermHalf R σ S) else 0
  have hm'u : ∀ s : R, IsUnit s → m' (hermScal R σ s) = fib s := by
    intro s hs
    simp only [m', hermHalf_hermScal R hσ, hs, if_true]
  have hm' : IsGramFib R σ J 1 μ (ν.map (hermScal R σ)) m' := by
    refine ⟨?_, ?_, ?_⟩
    · intro S
      by_cases hS : IsUnit (hermHalf R σ S)
      · have : m' S = fib (hermHalf R σ S) := by simp only [m', hS, if_true]
        rw [this]
        refine measure_mono_null ?_ (hf1 (hermHalf R σ S))
        intro X hX hX'
        apply hX
        have hqX : q X = hermHalf R σ S := by simpa using hX'.1
        refine ⟨?_, ?_⟩
        · change gramR R σ J X = (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E))
          rw [hgf X, hgq X, hqX, hermScal_hermHalf R hσ]
        · change IsUnit (gramR R σ J X).det
          rw [hgf X, hdet, ← hq, hqX]
          exact hS
      · have : m' S = 0 := by simp only [m', hS, if_false]
        rw [this]
        rfl
    · intro φ hφ
      rw [hemb.lintegral_map]
      have h1 : ∫⁻ v in {X | IsUnit (gramR R σ J X).det}, φ v ∂μ = ∫⁻ v in Set.univ, φ v ∂μ := by
        rw [Measure.restrict_univ]
        rw [Measure.restrict_eq_self_of_ae_mem]
        exact measure_eq_zero_iff_ae_notMem.mp hUnull |>.mono fun x hx => by simpa using hx
      rw [h1, hf2 φ hφ]
      refine lintegral_congr_ae ?_
      have hae : ∀ᵐ s ∂ν, IsUnit s := by
        rw [ae_iff]
        exact hνu
      filter_upwards [hae] with s hs
      rw [hm'u s hs]
    · intro φ hφ hφc hφs
      obtain ⟨hi, hcont⟩ := hf3 φ hφ hφc (Set.subset_univ _)
      refine ⟨fun S hS => ?_, ?_⟩
      · have hS' : IsUnit (hermHalf R σ S) := (hdet S).mp hS
        have : m' S = fib (hermHalf R σ S) := by simp only [m', hS', if_true]
        rw [this]
        exact hi _ hS'
      · have hmaps : Set.MapsTo (hermHalf R σ) {S : HermR R σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det} {c | IsUnit c} :=
          fun S hS => (hdet S).mp hS
        refine (hcont.comp (continuous_hermHalf R σ).continuousOn hmaps).congr ?_
        intro S hS
        have hS' : IsUnit (hermHalf R σ S) := (hdet S).mp hS
        have : m' S = fib (hermHalf R σ S) := by simp only [m', hS', if_true]
        simp only [this, Function.comp]
  have := GlobalTheory.CompanionTheory.SW.GramFib.fibre_unique F E σ hσ M J hJ R hR 1 μ (ν.map (hermScal R σ)) m hμ hν' hm m' hm'
    (hermScal R σ c)
  rw [this, hm'u c hc]
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MemUJsetOfMemKset
section
open Matrix
open PI.UpqRep (UJset Kset IsKFin IsKStableOn)

namespace GlobalTheory.CompanionTheory.KFinStab

theorem kFinStab : CompanionTheory.D.DSIC.KFinStab :=
  _root_.UpperTheory.Reformulated.B.Gc1.kFinStab

end GlobalTheory.CompanionTheory.KFinStab
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TransferStatementBisStatement
section
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.TransferStatementBis : StTransfer := by
  first | exact @GlobalTheory.CompanionTheory.HeckeTransfer.stTransfer | exact GlobalTheory.CompanionTheory.HeckeTransfer.stTransfer | (intros; apply GlobalTheory.CompanionTheory.HeckeTransfer.stTransfer <;> assumption)
end

