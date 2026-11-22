import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0053
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0029
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0076
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0025
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0003
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0075
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0033
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0008

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteVolumeInductionCompactSum
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.CountGen

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hE_eq_dot (σ : E →ₐ[F] E) {M : ℕ} (A : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    hE σ A x y = ((σ : E →+* E) ∘ x) ⬝ᵥ (A *ᵥ y) := by
  simp [hE, hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hE_mulVec (σ : E →ₐ[F] E) {M : ℕ} (J g : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) :
    hE σ J (g *ᵥ x) (g *ᵥ y) = hE σ (cT (σ : E →+* E) g * J * g) x y := by
  have h1 : ((σ : E →+* E) ∘ (g *ᵥ x)) = (g.map (σ : E →+* E)) *ᵥ ((σ : E →+* E) ∘ x) := by
    funext i
    exact RingHom.map_mulVec (σ : E →+* E) g x i
  rw [hE_eq_dot, hE_eq_dot, h1, ← Matrix.mulVec_mulVec y (cT (σ : E →+* E) g * J) g,
    ← Matrix.mulVec_mulVec _ (cT (σ : E →+* E) g) J,
    Matrix.dotProduct_mulVec ((σ : E →+* E) ∘ x) (cT (σ : E →+* E) g) _]
  simp only [cT, Matrix.vecMul_transpose]

theorem gramE_mulVec (σ : E →ₐ[F] E) {M n : ℕ} (J g : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → E) :
    gramE σ J (fun a => g *ᵥ X a) = gramE σ (cT (σ : E →+* E) g * J * g) X := by
  funext a b
  exact hE_mulVec σ J g (X a) (X b)

end Alg

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem continuous_actTup (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing (R ⊗[F] E)] {M n : ℕ} (g : GL (Fin M) (R ⊗[F] E)) :
    Continuous (actTup R g : (Fin n → Fin M → R ⊗[F] E) → _) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [actTup, Matrix.mulVec, dotProduct]
  exact continuous_finset_sum _ fun j _ =>
    continuous_const.mul ((continuous_apply j).comp (continuous_apply a))

theorem isCompact_preimage_actTup (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing (R ⊗[F] E)] {M n : ℕ} (g : GL (Fin M) (R ⊗[F] E))
    {Ω : Set (Fin n → Fin M → R ⊗[F] E)} (hΩ : IsCompact Ω) :
    IsCompact (actTup R g ⁻¹' Ω) := by
  have h : actTup R g ⁻¹' Ω = actTup R g⁻¹ '' Ω := by
    ext X
    constructor
    · intro hX
      refine ⟨actTup R g X, hX, ?_⟩
      funext a
      simp [actTup, Matrix.mulVec_mulVec]
    · rintro ⟨Y, hY, rfl⟩
      have : actTup R g (actTup R g⁻¹ Y) = Y := by
        funext a
        simp [actTup, Matrix.mulVec_mulVec]
      simpa [Set.mem_preimage, this] using hY
  rw [h]
  exact hΩ.image (continuous_actTup R g⁻¹)

end Top

theorem finite_count : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∀ (M' : ℕ), M' < M → ∀ J' : Matrix (Fin M') (Fin M') E, IsHermND σ J' → FinVol F E σ M' J') → ∀ t : F, t ≠ 0 → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E), IsCompact Ω → cntI σ J μ 𝓕 {X | gramE σ J X = fun _ _ => algebraMap F E t} (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) < ⊤ := by
  intro F E _ _ _ _ _ σ hcm M J hJ hvol t ht μ 𝓕 hμ h𝓕 Ω hΩ
  by_cases hS : ∃ X : Fin 1 → Fin M → E, gramE σ J X = fun _ _ => algebraMap F E t
  · obtain ⟨X₀, hX₀⟩ := hS
    have hx : hE σ J (X₀ 0) (X₀ 0) = algebraMap F E t := congrFun (congrFun hX₀ 0) 0
    cases M with
    | zero =>
      exfalso
      have h0 : hE σ J (X₀ 0) (X₀ 0) = 0 := by simp [hE, hform]
      rw [h0] at hx
      exact ht ((map_eq_zero (algebraMap F E)).1 hx.symm)
    | succ M₁ =>
      obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
      have htop := (GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)).1
      obtain ⟨g, J₁, hJ₁, hblock, -⟩ :=
        GlobalTheory.CompanionTheory.SW.AlgSplit.split_anisotropic F E σ hcm M₁ J hJ t (X₀ 0) ht hx
      obtain ⟨μ', 𝓕', hμ', h𝓕', -, hcnt⟩ :=
        GlobalTheory.T.fundamental_domain_transport_congruent_form F E σ hcm (M₁ + 1) J hJ g _ hblock μ 𝓕 hμ h𝓕
      rw [hcnt 1 _ _]
      have hset : {X : Fin 1 → Fin (M₁ + 1) → E |
          (fun a => (g : Matrix (Fin (M₁ + 1)) (Fin (M₁ + 1)) E) *ᵥ X a) ∈
            {X : Fin 1 → Fin (M₁ + 1) → E | gramE σ J X = fun _ _ => algebraMap F E t}} =
          {X | gramE σ (blockOne (algebraMap F E t) J₁) X = fun _ _ => algebraMap F E t} := by
        ext X
        simp only [Set.mem_setOf_eq, gramE_mulVec, hblock]
      have hfun : (fun Y : Fin 1 → Fin (M₁ + 1) → AF F ⊗[F] E =>
          Set.indicator Ω (fun _ => (1 : ℝ≥0∞)) (actTup (AF F) (bc (inclR (AF F)) g) Y)) =
          Set.indicator (actTup (AF F) (bc (inclR (AF F)) g) ⁻¹' Ω) (fun _ => (1 : ℝ≥0∞)) := by
        funext Y
        by_cases hY : actTup (AF F) (bc (inclR (AF F)) g) Y ∈ Ω
        · rw [Set.indicator_of_mem hY, Set.indicator_of_mem (Set.mem_preimage.2 hY)]
        · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem (fun h => hY (Set.mem_preimage.1 h))]
      rw [hset, hfun]
      exact GlobalTheory.T.finite_volume_block_one_extension F E σ hcm M₁ J₁ hJ₁ (hvol M₁ (Nat.lt_succ_self M₁) J₁ hJ₁) t ht μ' 𝓕' hμ' h𝓕' _
        (isCompact_preimage_actTup (AF F) _ hΩ)
  · have hemp : {X : Fin 1 → Fin M → E | gramE σ J X = fun _ _ => algebraMap F E t} = ∅ := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hS ⟨X, h⟩
    rw [hemp]
    simp [cntI]

end GlobalTheory.CompanionTheory.SW.CountGen
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicFundamentalDomainCover
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.IsoMain

theorem actW_smul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) (a : R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E) :
    actW R σ J h (a • X) = a • actW R σ J h X := funext fun i => Matrix.mulVec_smul _ a (X i)

set_option maxHeartbeats 1000000 in

theorem integral_isotropic_lines_le_flow_sum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → FinVol F E σ M J → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (μ : Measure (HA (AF F) σ (hypJ J))) (𝓕 : Set (HA (AF F) σ (hypJ J))), IsHaarH F E σ (M + 2) (hypJ J) μ → IsFDH F E σ (M + 2) (hypJ J) μ 𝓕 → ∃ (Y : Set ((Fin 1 → Fin (M + 2) → AF F ⊗[F] E) × (Fin 1 → Fin (M + 2) → AF F ⊗[F] E))) (Kc : ℝ≥0∞), IsCompact Y ∧ Kc < ⊤ ∧ (∀ p ∈ Y, hR (AF F) σ (hypJ J) (p.2 0) (p.1 0) = 1) ∧ ∀ Φ : (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞, Measurable Φ → (∀ (l : E) y, l ≠ 0 → Φ ((inclR (F := F) (AF F) l : AF F ⊗[F] E) • y) = Φ y) → ∀ g : ℤ → ℝ≥0∞, (∀ (j : ℤ), ∀ p ∈ Y, Φ (((τ (Multiplicative.ofAdd (-(j : ℝ))) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • p.1) ≤ g j) → ∀ L : Set (Fin 1 → Fin (M + 2) → E), L ⊆ {X : Fin 1 → Fin (M + 2) → E | X ≠ 0 ∧ gramE σ (hypJ J) X = 0} → (∀ X ∈ L, ∀ X' ∈ L, ∀ l : E, X' = l • X → X' = X) → cntI σ _ μ 𝓕 L Φ ≤ Kc * ∑' j : ℤ, g j * ENNReal.ofReal (Real.exp (-(2 * Module.finrank ℚ F * (M + 1) * (j : ℝ)))) := by
  intro F E _ _ _ _ _ σ hcm M J hJ hfin τ hτ μ 𝓕 hμ h𝓕
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, hsc, -, -, hB, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (AF F)
  have := hB 1 (M + 2)
  have hH := (GlobalTheory.CompanionTheory.SW.BlockForm.blockForms_isHermND F E σ hcm M J hJ).1
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hcm _ _ hH (AF F)
  obtain ⟨ac, a1, a2, -⟩ := hact 1
  obtain ⟨-, -, -, ag⟩ := hact 2
  have : μ.IsHaarMeasure := hμ
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  obtain ⟨P, ν, S, ω, Kc, hP, _, hν, hνU, hω, hKc, hSm, hSν, hSP, hScov⟩ := GlobalTheory.T.hyperbolic_parabolic_siegel_set_bound F E σ hcm M J hJ hfin τ hτ
  obtain ⟨C, hC, hiwa⟩ := GlobalTheory.T.hyperbolic_unitary_stabilizer_cocompact F E σ hcm M J hJ
  obtain ⟨C', K, hC', hK, hcover⟩ := GlobalTheory.CompanionTheory.Adelic.integral_fundamentalDomain_le_siegel _ μ P ν hν hνU C hC
  set e₀ : Fin 1 → Fin (M + 2) → AF F ⊗[F] E := eOne _ (M + 1) with he₀
  set e₁ : Fin 1 → Fin (M + 2) → AF F ⊗[F] E := fun _ => Fin.cons 0 (Fin.cons 1 fun _ => 0) with he₁
  have aC : ∀ X, Continuous fun h : HA (AF F) σ (hypJ J) => actW (AF F) σ _ h⁻¹ X := fun X =>
    ac.comp (continuous_inv.prodMk continuous_const)
  let Γ : Subgroup (HA (AF F) σ (hypJ J)) := HFinIn (AF F) σ (hypJ J)
  have : Countable Γ := (GlobalTheory.CompanionTheory.SW.rational_countable_discrete F E σ hcm _ _ hH).1
  have : Countable (Γ ⊓ P : Subgroup _) := (Subgroup.inclusion_injective (inf_le_left : Γ ⊓ P ≤ Γ)).countable
  have hrat : ∀ γ ∈ Γ, ∀ X, ∃ X' : Fin 1 → Fin (M + 2) → E, actW (AF F) σ _ γ (ratTup (AF F) X) = ratTup (AF F) X' := by
    rintro γ ⟨g, -, e⟩ X
    refine ⟨fun a => g.val *ᵥ X a, funext fun a => funext fun i => ?_⟩
    have e' : (HA.mat (AF F) σ _ γ).val = g.val.map (inclR (AF F)) :=
      (congrArg Units.val e).symm
    simp only [actW, actTup, e', ratTup, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  have he : e₀ = ratTup (AF F) (eOne E (M + 1)) := by
    funext a i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [he₀, eOne, ratTup]
  have hline : ∀ γ ∈ Γ ⊓ P, ∃ l : E, l ≠ 0 ∧ actW (AF F) σ _ γ e₀ = (inclR (AF F) l : AF F ⊗[F] E) • e₀ := by
    intro γ hγ
    obtain ⟨a, ha⟩ := (hP γ).1 hγ.2
    obtain ⟨X, hX⟩ := hrat γ hγ.1 (eOne E (M + 1))
    have h1 : (a : AF F ⊗[F] E) = inclR (AF F) (X 0 0) := by
      have := congrFun (congrFun (ha.symm.trans (he ▸ hX)) 0) 0
      simpa [he₀, eOne, ratTup] using this
    refine ⟨X 0 0, fun h0 => ?_, h1 ▸ ha⟩
    have : Nontrivial (AF F ⊗[F] E) := hinj.nontrivial
    exact a.ne_zero (by rw [h1, h0, map_zero])
  refine ⟨(fun p : (AF F ⊗[F] E)ˣ × HA (AF F) σ (hypJ J) =>
      (((p.1⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • actW (AF F) σ _ p.2⁻¹ e₀,
        sigR (AF F) σ (p.1 : AF F ⊗[F] E) • actW (AF F) σ _ p.2⁻¹ e₁)) '' (ω ×ˢ C'), K * Kc,
    (hω.prod hC').image (((Units.continuous_coe_inv.comp continuous_fst).smul ((aC _).comp continuous_snd)).prodMk
      ((hsc.comp (Units.continuous_val.comp continuous_fst)).smul ((aC _).comp continuous_snd))),
    ENNReal.mul_lt_top hK hKc, ?_, fun Φ hΦ hΦl g hg L hL hLu => ?_⟩
  · rintro _ ⟨⟨a, c⟩, -, rfl⟩
    have h1 : hR (AF F) σ (hypJ J) (actW (AF F) σ _ c⁻¹ e₁ 0) (actW (AF F) σ _ c⁻¹ e₀ 0) =
        hR (AF F) σ (hypJ J) (e₁ 0) (e₀ 0) := congrFun (congrFun (ag c⁻¹ ![e₁ 0, e₀ 0]) 0) 1
    have h2 : hR (AF F) σ (hypJ J) (e₁ 0) (e₀ 0) = 1 := by
      simp [hR, hform, he₀, he₁, eOne, JR, hypJ, Fin.sum_univ_succ]
    have hs : ∀ x, sigR (AF F) σ (sigR (AF F) σ x) = x := GlobalTheory.GaussMean.OneVec.sigR_sigR (AF F) hcm
    rw [h2] at h1
    simp only [hR, hform, Pi.smul_apply, smul_eq_mul, map_mul, hs] at h1 ⊢
    rw [← a.mul_inv, ← mul_one (_ * _), ← h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  · have hw : ∀ X : L, ∃ γ ∈ Γ, actW (AF F) σ _ γ⁻¹ e₀ = ratTup (AF F) X.1 := fun X => by
      obtain ⟨g, hg, e⟩ := GlobalTheory.T.unitary_transitive_on_isotropic_vectors F E σ hcm _ _ hH (eOne E (M + 1) 0) (X.1 0)
        (fun h => one_ne_zero (congrFun h 0)) (fun h => (hL X.2).1 (funext fun a => by rw [Subsingleton.elim a 0]; exact h))
        (by simp [hE, hform, eOne, hypJ, Fin.sum_univ_succ]) (congrFun (congrFun (hL X.2).2 0) 0)
      have hm : bc (inclR (AF F)) g ∈ HR (AF F) σ (hypJ J) := by
        have h1 := congrArg (fun A => A.map (inclR (F := F) (AF F))) hg
        simp only [Matrix.map_mul] at h1
        refine Eq.trans ?_ h1
        have e1 : cT (sigR (AF F) σ) (bc (inclR (F := F) (AF F)) g).val = (cT (σ : E →+* E) g.val).map (inclR (AF F)) := by
          ext1 i j; simp [cT, bc, sigR, inclR]
        rw [e1]
        rfl
      refine ⟨(⟨_, hm⟩ : HR (AF F) σ (hypJ J))⁻¹, Γ.inv_mem ⟨g, hg, rfl⟩, ?_⟩
      rw [he]
      funext a i
      rw [Subsingleton.elim a 0, ratTup, ← e]
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
      rfl
    choose γ hγ hγe using hw
    let Q := Quotient (QuotientGroup.rightRel ((Γ ⊓ P).subgroupOf Γ))
    have hout : ∀ x : Γ, (x : HA (AF F) σ (hypJ J)) * (((Quotient.mk _ x : Q).out : Γ) : HA (AF F) σ (hypJ J))⁻¹ ∈ Γ ⊓ P :=
      fun x => (QuotientGroup.rightRel_apply (s := (Γ ⊓ P).subgroupOf Γ)).1 (Quotient.mk_out x)
    obtain ⟨𝓕', h𝓕', hunf⟩ := GlobalTheory.CompanionTheory.Adelic.unfold_coset_sum_fundamentalDomain _ μ Γ (Γ ⊓ P) inf_le_left 𝓕 h𝓕 Q (fun q => (q.out : Γ)) (fun q => q.out.2)
      fun x hx => ⟨Quotient.mk _ ⟨x, hx⟩, hout ⟨x, hx⟩, fun q hq =>
        (Quotient.out_eq q).symm.trans (Quotient.sound (QuotientGroup.rightRel_apply.2 hq))⟩
    set f : HA (AF F) σ (hypJ J) → ℝ≥0∞ := fun h => Φ (actW (AF F) σ _ h⁻¹ e₀) with hf
    have hfm : Measurable f := hΦ.comp (aC _).measurable
    have hfi : ∀ x ∈ Γ ⊓ P, ∀ h, f (x * h) = f h := fun x hx h => by
      obtain ⟨l, hl, e⟩ := hline _ ((Γ ⊓ P).inv_mem hx)
      simp only [hf, mul_inv_rev, a2, e, actW_smul, hΦl l _ hl]
    let q : L → Q := fun X => Quotient.mk _ ⟨γ X, hγ X⟩
    have hq : Function.Injective q := fun X X' h => by
      obtain ⟨l, -, e⟩ := hline (γ X * (γ X')⁻¹)
        ((QuotientGroup.rightRel_apply (s := (Γ ⊓ P).subgroupOf Γ)).1 (Quotient.exact h.symm))
      have h1 := congrArg (actW (AF F) σ _ (γ X)⁻¹) e
      rw [← a2, inv_mul_cancel_left, actW_smul, hγe, hγe] at h1
      refine Subtype.ext (hLu _ X.2 _ X'.2 l (funext fun a => funext fun i => ?_)).symm
      apply hinj
      simpa [ratTup] using congrFun (congrFun h1 a) i
    have h1 : cntI σ _ μ 𝓕 L Φ ≤ ∫⁻ h in 𝓕', f h ∂μ := by
      rw [← hunf f hfm]
      refine lintegral_mono fun h => le_trans (le_of_eq (tsum_congr fun X => ?_))
        (ENNReal.tsum_comp_le_tsum_of_injective hq fun y => f ((y.out : Γ) * h))
      have h2 : γ X * (((q X).out : Γ) : HA (AF F) σ (hypJ J))⁻¹ ∈ Γ ⊓ P := hout ⟨γ X, hγ X⟩
      rw [← hfi _ h2, ← mul_assoc, inv_mul_cancel_right, hf]
      simp only [mul_inv_rev, a2, hγe]
    have hgm : ∀ j, Measurable ((S j).indicator fun _ => g j) := fun j => measurable_const.indicator (hSm j)
    refine h1.trans ((hcover (Γ ⊓ P) inf_le_right 𝓕' h𝓕' (⋃ j, S j) (MeasurableSet.iUnion hSm)
      (hScov.mono fun p ⟨x, hx, hx', j, hj⟩ => ⟨x, ⟨hx', hx⟩, Set.mem_iUnion.2 ⟨j, hj⟩⟩) f
      (fun p => ∑' j, (S j).indicator (fun _ => g j) p) hfm (Measurable.ennreal_tsum hgm) hfi
      (fun x _ => ?_) fun p hp c hc => ?_).trans ?_)
    · obtain ⟨c, hc, a, ha⟩ := hiwa x
      exact ⟨x * c⁻¹, (hP _).2 ⟨a, ha⟩, c, hc, by rw [inv_mul_cancel_right]⟩
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hp
      obtain ⟨-, a, ha, e⟩ := hSP j p hj
      refine le_trans ?_ (ENNReal.le_tsum j)
      rw [Set.indicator_of_mem hj]
      refine le_trans (le_of_eq ?_) (hg j _ ⟨(a, c), ⟨ha, hc⟩, rfl⟩)
      have h2 := congrArg (fun X => (((τ (Multiplicative.ofAdd (j : ℝ)) * a)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) •
        actW (AF F) σ _ p⁻¹ X) e
      simp only [← a2, inv_mul_cancel, a1, actW_smul, smul_smul, Units.inv_mul, one_smul] at h2
      simp only [hf, mul_inv_rev, a2, ← h2, actW_smul, smul_smul, ofAdd_neg, map_inv, Units.val_mul, mul_comm]
    · rw [mul_assoc]
      gcongr
      refine (setLIntegral_le_lintegral _ _).trans ?_
      rw [lintegral_tsum (f := fun j p => (S j).indicator (fun _ => g j) p) fun j => (hgm j).aemeasurable, ← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum fun j => ?_
      rw [lintegral_indicator_const (hSm j), mul_left_comm]
      gcongr
      exact hSν j

end GlobalTheory.CompanionTheory.SW.IsoMain
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SelfDualStandardMeasuresStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_standard_measures : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∃ ψ, IsCharAF F ψ ∧ ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (SelfDual (cinf • laminf) (fun s t => psiInf F ψ (s * t))) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (SelfDual (c v • lam v) (fun s t => psiV F ψ v (s * t))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.SDOne.selfDual_std | exact GlobalTheory.CompanionTheory.SW.SDOne.selfDual_std | (intros; apply GlobalTheory.CompanionTheory.SW.SDOne.selfDual_std <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilFormulaRangeStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isEulerProd_of_invariant_of_fiber_supported : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ), n = 0 ∨ n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E)), IsGramFib (Ainf F) σ J n (coordW (Ainf F) b laminf n M) (coordHerm (Ainf F) σ b laminf n) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) (m v)) → ∀ I : Measure (Fin n → Fin M → AF F ⊗[F] E), IsLocallyFiniteMeasure I → (∀ h : HA (AF F) σ J, I.map (actW (AF F) σ J h) = I) → I {X | gramR (AF F) σ J X = T.map (inclR (AF F))}ᶜ = 0 → ∃ c : ℝ≥0, IsEulerProd b I c (minf (hermOf (Ainf F) σ T hT)) (fun v => m v (hermOf (Fv F v) σ T hT)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Fact.exists_isEulerProd | exact GlobalTheory.CompanionTheory.SW.Fact.exists_isEulerProd | (intros; apply GlobalTheory.CompanionTheory.SW.Fact.exists_isEulerProd <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionGrowthBound
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core.EiBound

theorem prod_sum_bound {S R : Type} (h : S × R → ℝ) (a : S → ℝ) (K : ℝ) (h0 : ∀ p, 0 ≤ h p)
    (ha : Summable a)
    (hin : ∀ s, Summable (fun r => h (s, r)) ∧ ∑' r, h (s, r) ≤ a s * K) :
    Summable h ∧ ∑' p, h p ≤ (∑' s, a s) * K := by
  have hout : Summable (fun s => ∑' r, h (s, r)) :=
    Summable.of_nonneg_of_le (fun s => tsum_nonneg fun r => h0 _) (fun s => (hin s).2)
      (ha.mul_right K)
  have hs : Summable h := (summable_prod_of_nonneg (fun p => h0 p)).2 ⟨fun s => (hin s).1, hout⟩
  refine ⟨hs, ?_⟩
  rw [hs.tsum_prod, ← tsum_mul_right]
  exact Summable.tsum_le_tsum (fun s => (hin s).2) hout (ha.mul_right K)

theorem exists_decomp (F : Type) [Field F] [NumberField F] :
    ∃ (Q : Type) (out : Q → F), Function.Injective out ∧
      (∀ q q', (∃ r : 𝓞 F, out q - out q' = (r : F)) → q = q') ∧
      Function.Bijective (fun p : Q × 𝓞 F => out p.1 + (p.2 : F)) := by
  let L : AddSubgroup F := (algebraMap (𝓞 F) F).toAddMonoidHom.range
  have hL : ∀ x : F, x ∈ L ↔ ∃ r : 𝓞 F, (r : F) = x := fun x => by
    simp [L, AddMonoidHom.mem_range]
  have hsep : ∀ q q' : F ⧸ L, (∃ r : 𝓞 F, (Quotient.out q : F) - Quotient.out q' = (r : F)) →
      q = q' := by
    rintro q q' ⟨r, hr⟩
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q']
    refine (QuotientAddGroup.eq).2 ?_
    have : -(Quotient.out q : F) + Quotient.out q' = ((-r : 𝓞 F) : F) := by
      push_cast
      linear_combination -hr
    exact (hL _).2 ⟨-r, this.symm⟩
  refine ⟨F ⧸ L, Quotient.out, ?_, hsep, ?_, ?_⟩
  · intro q q' h
    exact hsep q q' ⟨0, by simp [h]⟩
  · rintro ⟨q, r⟩ ⟨q', r'⟩ h
    simp only at h
    have hq : q = q' := hsep q q' ⟨r' - r, by push_cast; linear_combination h⟩
    subst hq
    have : (r : F) = r' := add_left_cancel h
    have : r = r' := RingOfIntegers.ext this
    rw [this]
  · intro b
    have h1 : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk b : F ⧸ L)) : F ⧸ L) =
        QuotientAddGroup.mk b := QuotientAddGroup.out_eq' _
    obtain ⟨r, hr⟩ := (hL _).1 ((QuotientAddGroup.eq).1 h1)
    refine ⟨⟨QuotientAddGroup.mk b, r⟩, ?_⟩
    simp only
    rw [hr]; ring

theorem place_bound (M : ℕ) (hM : 2 ≤ M) (t y : ℝ) (ht : 0 < t) (hy : t ≤ y) :
    Real.sqrt y ^ M * (y * (y ^ M)⁻¹) ≤ ((Real.sqrt t) ^ (M - 2))⁻¹ := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 2 := ⟨M - 2, by omega⟩
  have hy0 : 0 < y := ht.trans_le hy
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hyy : y = Real.sqrt y ^ 2 := (Real.sq_sqrt hy0.le).symm
  have e : Real.sqrt y ^ (k + 2) * (y * (y ^ (k + 2))⁻¹) = (Real.sqrt y ^ k)⁻¹ := by
    generalize Real.sqrt y = s at hs hyy
    subst hyy
    field_simp
    ring
  rw [e, Nat.add_sub_cancel]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hst.le (Real.sqrt_le_sqrt hy) k)

theorem ei_bound : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)]
    (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M →
    ∀ φ : (ι → A F) → ℂ, SB φ → ∀ t : ℝ, 0 < t → ∃ C : ℝ, ∀ τ : InfinitePlace F → ℂ,
    (∀ w, t ≤ (τ w).im) → Summable (fun b => ‖eiTerm ψ lf B ρ P φ τ b‖) ∧
      wt M τ * ∑' b, ‖eiTerm ψ lf B ρ P φ τ b‖ ≤ C := by
  intro F _ _ _ _ lf hlf hO ψ hψ ι _ _ M B ρ P hQ hM φ hφ t ht
  have hTR : IsTotallyReal F := hQ.1
  have hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x := hQ.2.2.2.2.1
  obtain ⟨C1, hC1⟩ := GlobalTheory.T.fourier_coefficient_growth_bound F lf hlf hO ψ hψ ι M B ρ P hQ φ hφ
  obtain ⟨C2, hC2⟩ := GlobalTheory.T.eisenstein_lattice_sum_bound F hTR ρ hρ M (by omega) t ht
  obtain ⟨Q, out, hinj, hsep, hbij⟩ := exists_decomp F
  obtain ⟨hd1, hd2, hd3⟩ := GlobalTheory.T.denominator_power_summable F M hM 1 one_pos
  let a : Q → ℝ := fun q => ((den (out q) : ℝ) ^ M)⁻¹
  have ha0 : ∀ q, 0 ≤ a q := fun q => by positivity
  have ha : Summable a := by
    have h := hd3 (Set.range out) (by
      rintro _ ⟨q, rfl⟩ _ ⟨q', rfl⟩ ⟨r, hr⟩
      rw [hsep q q' ⟨r, by simpa using hr⟩])
    exact (Equiv.ofInjective out hinj).summable_iff.2 h
  have hterm : ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∀ b : F,
      ‖eiTerm ψ lf B ρ P φ τ b‖ ≤
        |C1| * ((den b : ℝ) ^ M)⁻¹ * (∏ w, ‖τ w + (ρ w b : ℝ)‖ ^ M)⁻¹ := by
    intro τ hτ b
    have hc := (GlobalTheory.T.archimedean_gaussian_fourier F ι M B ρ P hQ (fun w => τ w + (ρ w b : ℝ))
      (fun w => by simpa using hτ w)).2.1
    unfold eiTerm
    rw [norm_mul, hc]
    refine mul_le_mul_of_nonneg_right ((hC1 b).trans ?_) (by positivity)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  refine ⟨(∑' q, a q) * |C1| * |C2| * ∏ _w : InfinitePlace F, ((Real.sqrt t) ^ (M - 2))⁻¹, ?_⟩
  intro τ hτ
  have hτ0 : ∀ w, 0 < (τ w).im := fun w => ht.trans_le (hτ w)
  set Y : ℝ := ∏ w, (τ w).im * ((τ w).im ^ M)⁻¹ with hYdef
  have hY0 : 0 ≤ Y := Finset.prod_nonneg fun w _ => by
    have := hτ0 w
    positivity
  let e : Q × 𝓞 F ≃ F := Equiv.ofBijective _ hbij
  let h' : Q × 𝓞 F → ℝ := fun p =>
    |C1| * a p.1 * (∏ w, ‖(τ w + (ρ w (out p.1) : ℝ)) + (ρ w (p.2 : F) : ℝ)‖ ^ M)⁻¹
  have hh'0 : ∀ p, 0 ≤ h' p := fun p => by
    have := ha0 p.1
    positivity
  have hle : ∀ p, ‖eiTerm ψ lf B ρ P φ τ (e p)‖ ≤ h' p := by
    rintro ⟨q, r⟩
    have h1 := hterm τ hτ0 (out q + (r : F))
    have h2 : den (out q + (r : F)) = den (out q) := hd1 _ _
    rw [h2] at h1
    have h3 : ∀ w, τ w + ((ρ w (out q + (r : F)) : ℝ) : ℂ) =
        (τ w + (ρ w (out q) : ℝ)) + (ρ w (r : F) : ℝ) := fun w => by
      rw [map_add]; push_cast; ring
    simp only [h3] at h1
    exact h1
  have hin : ∀ q, Summable (fun r => h' (q, r)) ∧
      ∑' r, h' (q, r) ≤ a q * (|C1| * (|C2| * Y)) := by
    intro q
    obtain ⟨hs, hb⟩ := hC2 (fun w => τ w + (ρ w (out q) : ℝ)) (fun w => by simpa using hτ w)
    have him : ∀ w, (τ w + ((ρ w (out q) : ℝ) : ℂ)).im = (τ w).im := fun w => by simp
    simp only [him] at hb
    have hs' : Summable (fun r : 𝓞 F => |C1| * a q *
        (∏ w, ‖(τ w + (ρ w (out q) : ℝ)) + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹) := hs.mul_left _
    refine ⟨hs', ?_⟩
    have hq0 := ha0 q
    change ∑' r : 𝓞 F, |C1| * a q *
        (∏ w, ‖(τ w + (ρ w (out q) : ℝ)) + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹ ≤ _
    rw [tsum_mul_left]
    calc |C1| * a q * ∑' r : 𝓞 F, (∏ w, ‖(τ w + (ρ w (out q) : ℝ)) + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹
        ≤ |C1| * a q * (|C2| * Y) :=
          mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hY0))
            (by positivity)
      _ = a q * (|C1| * (|C2| * Y)) := by ring
  obtain ⟨hsum', hbd'⟩ := prod_sum_bound h' a (|C1| * (|C2| * Y)) hh'0 ha hin
  have hsumc : Summable (fun p => ‖eiTerm ψ lf B ρ P φ τ (e p)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsum'
  have hsum : Summable (fun b => ‖eiTerm ψ lf B ρ P φ τ b‖) := e.summable_iff.1 hsumc
  refine ⟨hsum, ?_⟩
  have htot : ∑' b, ‖eiTerm ψ lf B ρ P φ τ b‖ ≤ (∑' q, a q) * (|C1| * (|C2| * Y)) := by
    rw [← e.tsum_eq (fun b => ‖eiTerm ψ lf B ρ P φ τ b‖)]
    exact (Summable.tsum_le_tsum hle hsumc hsum').trans hbd'
  have hwt0 : 0 ≤ wt M τ := Finset.prod_nonneg fun w _ => by positivity
  have hA0 : 0 ≤ ∑' q, a q := tsum_nonneg ha0
  have hwY : wt M τ * Y ≤ ∏ _w : InfinitePlace F, ((Real.sqrt t) ^ (M - 2))⁻¹ := by
    rw [hYdef]
    unfold wt
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun w _ => ?_) (fun w _ => place_bound M (by omega) t _ ht (hτ w))
    have := hτ0 w
    positivity
  calc wt M τ * ∑' b, ‖eiTerm ψ lf B ρ P φ τ b‖
      ≤ wt M τ * ((∑' q, a q) * (|C1| * (|C2| * Y))) :=
        mul_le_mul_of_nonneg_left htot hwt0
    _ = (∑' q, a q) * |C1| * |C2| * (wt M τ * Y) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hwY (by positivity)

end GlobalTheory.CompanionTheory.SW.Core.EiBound
end

