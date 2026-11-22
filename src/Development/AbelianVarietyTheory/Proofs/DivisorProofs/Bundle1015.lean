import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0972
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0244
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilGramSignature
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0042
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationConstantOfPowerEq
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumEnormTermMulLeft
section
noncomputable section

namespace GlobalTheory.DefDoubling

open MeasureTheory Filter Topology Set GlobalTheory.Eis GlobalTheory.Cont GlobalTheory.Doubling GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal NNReal

section Main

variable {G G₂ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
  {i : G × G →* G₂} {P Γ₂ K₂ : Subgroup G₂} {Γ K : Subgroup G} [Countable Γ] {r : Γ → Γ₂}
  {μ : Measure G} [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] {𝓕 : Set G} {A : Finset G}
  {ι : Type} [Fintype ι] {kk : ι → G₂} {cc : ι → G₂ → ℂ}

theorem tsum_enorm_term_mul_left {Φ : G₂ → ℂ} (hΦ : LeftInv (P ⊓ Γ₂) Φ) {γ : G₂} (hγ : γ ∈ Γ₂) (g : G₂) :
    ∑' q, ‖term P Γ₂ Φ (γ * g) q‖ₑ = ∑' q, ‖term P Γ₂ Φ g q‖ₑ :=
  (tsum_congr fun q => by rw [term_mul_left hΦ ⟨γ, hγ⟩ g q]).trans ((rmulEquiv P Γ₂ ⟨γ, hγ⟩).tsum_eq fun q => ‖term P Γ₂ Φ g q‖ₑ)

theorem unfold (hi : Continuous i) (hri : ∀ δ, (r δ : G₂) = i (1, δ))
    (hr : Function.Bijective fun δ => mk (P.subgroupOf Γ₂) (r δ)) (hK : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (hKK : ∀ k ∈ K, i (1, k) ∈ K₂)
    (hcov : ∀ x, ∃ a ∈ A, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    {Φ : G₂ → ℂ} (hΦ : LeftInv (P ⊓ Γ₂) Φ) (hΦc : Continuous Φ) (hcc : ∀ j, Continuous (cc j))
    (hexp : ∀ g, ∀ k ∈ K₂, Φ (g * k) = ∑ j, cc j k * Φ (g * kk j)) (hconv : ∀ g, CosetConv P Γ₂ Φ g)
    {c : G → ℂ} (hlaw : ∀ h y, Φ (i (h, h) * y) = c h * Φ y) {w : G → ℂ} (hwc : Continuous w)
    (hw : ∀ x y, w (x * y) = w x * w y) (hwΓ : ∀ γ ∈ Γ, w γ = 1) (hw1 : ∀ x, ‖w x‖ = 1) (h : G) :
    Integrable (fun g => Φ (i (1, g)) * w g) μ ∧ IntegrableOn (fun x => cosetSum P Γ₂ Φ (i (h, x)) * w x) 𝓕 μ ∧
      ∫ x in 𝓕, cosetSum P Γ₂ Φ (i (h, x)) * w x ∂μ = c h * w h * ∫ g, Φ (i (1, g)) * w g ∂μ := by
  have hm : ∀ h, AEStronglyMeasurable (fun x => Φ (i (h, x))) μ := fun h =>
    (hΦc.comp (hi.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  obtain ⟨C, -, ⟨M, hM⟩, hC⟩ := exists_coeff (Γ := Γ) hK hKc A hcov (fun j k => cc j (i (1, k)))
    fun j => (hcc j).comp (hi.comp (continuous_const.prodMk continuous_id))

  set S : G₂ → ℝ≥0∞ := fun g => ∑' q, ‖term P Γ₂ Φ g q‖ₑ with hS
  have hSfin : ∀ g, S g ≠ ⊤ := fun g => by
    have := ENNReal.ofReal_tsum_of_nonneg (fun q => norm_nonneg (term P Γ₂ Φ g q)) (hconv g)
    simp only [ofReal_norm] at this
    change ∑' q, ‖term P Γ₂ Φ g q‖ₑ ≠ ⊤
    rw [← this]
    exact ENNReal.ofReal_ne_top
  set B : ℝ≥0∞ := ∑ a ∈ A, ∑ j, ‖(M : ℂ)‖ₑ * S (i (h, a) * kk j) with hB
  have hδ : ∀ x, ∑' δ : Γ, ‖Φ (i (h, δ * x))‖ₑ = S (i (h, x)) := fun x => by
    change _ = ∑' q, ‖term P Γ₂ Φ (i (h, x)) q‖ₑ
    rw [← (Equiv.ofBijective _ hr).tsum_eq]
    refine tsum_congr fun δ => ?_
    rw [Equiv.ofBijective_apply, term_mk hΦ, hri, ← map_mul, Prod.mk_mul_mk, one_mul]
  have hbd : ∀ x, S (i (h, x)) ≤ B := fun x => by
    obtain ⟨a, ha, γ, hγ, k, hk, rfl, hCx⟩ := hC x
    have e : i (h, γ * a * k) = i (1, γ) * (i (h, a) * i (1, k)) := by
      simp only [← map_mul, Prod.mk_mul_mk, one_mul, mul_one, mul_assoc]
    have hγ2 : i (1, γ) ∈ Γ₂ := hri ⟨γ, hγ⟩ ▸ (r ⟨γ, hγ⟩).2
    change ∑' q, ‖term P Γ₂ Φ _ q‖ₑ ≤ B
    rw [e, tsum_enorm_term_mul_left hΦ hγ2]
    refine (cosetSum_norm_expansion hexp _ (hKK k hk)).trans ?_
    refine le_trans ?_ (Finset.single_le_sum (f := fun a => ∑ j, ‖(M : ℂ)‖ₑ * S (i (h, a) * kk j))
      (fun _ _ => zero_le) ha)
    refine Finset.sum_le_sum fun j _ => mul_le_mul_left ?_ _
    have := hM a j (γ * a * k)
    rw [hCx a j, if_pos rfl] at this
    rw [enorm_le_iff_norm_le, Complex.norm_real, Real.norm_eq_abs]
    exact this.trans (le_abs_self M)
  have hBfin : B ≠ ⊤ := ENNReal.sum_ne_top.2 fun a _ => ENNReal.sum_ne_top.2 fun j _ =>
    ENNReal.mul_ne_top enorm_ne_top (hSfin _)
  have hfin : ∫⁻ x in 𝓕, ∑' δ : Γ, ‖Φ (i (h, δ * x))‖ₑ ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hBfin (measure_lt_top_of_cover h𝓕 hKc A hcov).ne) ?_
    calc ∫⁻ x in 𝓕, ∑' δ : Γ, ‖Φ (i (h, δ * x))‖ₑ ∂μ ≤ ∫⁻ _ in 𝓕, B ∂μ :=
          lintegral_mono fun x => (hδ x).trans_le (hbd x)
      _ = B * μ 𝓕 := setLIntegral_const 𝓕 B
  exact unfold_core i h𝓕 hΦ hri hr hlaw hw hwΓ hw1 hwc.aestronglyMeasurable hm h hfin

theorem holValueAt_integral (hi : Continuous i) (hΓ₂ : ∀ γ ∈ Γ, i (1, γ) ∈ Γ₂) (hK : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (hKK : ∀ k ∈ K, i (1, k) ∈ K₂)
    (hcov : ∀ x, ∃ a ∈ A, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    {Φ : ℂ → G₂ → ℂ} {σ : ℝ} (hΦ : ∀ s : ℂ, σ < s.re → LeftInv (P ⊓ Γ₂) (Φ s)) (hcc : ∀ j, Continuous (cc j))
    (hexp : ∀ s : ℂ, σ < s.re → ∀ g, ∀ k ∈ K₂, Φ s (g * k) = ∑ j, cc j k * Φ s (g * kk j))
    (hconv : ∀ s : ℂ, σ < s.re → ∀ g, CosetConv P Γ₂ (Φ s) g) {w : G → ℂ} (hwc : Continuous w)
    (hw1 : ∀ x, ‖w x‖ = 1) {s₀ : ℂ} {Ψ : G₂ → ℂ} (hΨ : ∀ g, HolValueAt (fun s => cosetSum P Γ₂ (Φ s) g) s₀ (Ψ g))
    (h : G) :
    IntegrableOn (fun x => Ψ (i (h, x)) * w x) 𝓕 μ ∧
      HolValueAt (fun s => ∫ x in 𝓕, cosetSum P Γ₂ (Φ s) (i (h, x)) * w x ∂μ) s₀ (∫ x in 𝓕, Ψ (i (h, x)) * w x ∂μ) := by
  classical
  obtain ⟨C, hCm, ⟨M, hM⟩, hC⟩ := exists_coeff (Γ := Γ) hK hKc A hcov (fun j k => cc j (i (1, k)))
    fun j => (hcc j).comp (hi.comp (continuous_const.prodMk continuous_id))
  haveI : IsFiniteMeasure (μ.restrict 𝓕) :=
    isFiniteMeasure_restrict.2 (measure_lt_top_of_cover h𝓕 hKc A hcov).ne
  have hc : ∀ p : {a // a ∈ A} × ι, Integrable (fun x => C p.1 p.2 x * w x) (μ.restrict 𝓕) := fun p =>
    Integrable.of_bound ((hCm p.1 p.2).aestronglyMeasurable.mul hwc.aestronglyMeasurable) M
      (Eventually.of_forall fun x => by rw [norm_mul, hw1, mul_one]; exact hM _ _ x)
  have hexp' : ∀ s : ℂ, σ < s.re → ∀ x, cosetSum P Γ₂ (Φ s) (i (h, x)) * w x =
      ∑ p : {a // a ∈ A} × ι, C p.1 p.2 x * w x * cosetSum P Γ₂ (Φ s) (i (h, p.1) * kk p.2) := by
    intro s hs x
    obtain ⟨a, ha, γ, hγ, k, hk, hx, hCx⟩ := hC x
    have e : i (h, x) = i (1, γ) * (i (h, a) * i (1, k)) := by
      rw [hx]; simp only [← map_mul, Prod.mk_mul_mk, one_mul, mul_one, mul_assoc]
    rw [e, leftInv_cosetSum (hΦ s hs) _ (hΓ₂ γ hγ),
      cosetSum_expansion (hexp s hs) _ (fun j => hconv s hs _) (hKK k hk), Fintype.sum_prod_type,
      Finset.sum_eq_single (⟨a, ha⟩ : {a // a ∈ A}) (fun b _ hb => by
        simp [hCx, show (b : G) ≠ a from fun e => hb (Subtype.ext e)]) (by simp), Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [hCx, if_pos rfl]; ring
  have key := holValueAt_integral_of_expansion (ν := μ.restrict 𝓕) (X := G) (ι := {a // a ∈ A} × ι)
    (Φ := fun s x => cosetSum P Γ₂ (Φ s) (i (h, x)) * w x) (Ψ := fun x => Ψ (i (h, x)) * w x)
    (c := fun p x => C p.1 p.2 x * w x) (v := fun p s => cosetSum P Γ₂ (Φ s) (i (h, p.1) * kk p.2))
    (w := fun p => Ψ (i (h, p.1) * kk p.2)) (σ := σ) hc hexp' (fun p => hΨ _)
    (fun x => (hΨ _).mul (holValueAt_const _ _))
  exact ⟨key.2.1, key.2.2⟩

end Main

section Flat

variable {G G₂ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
  {i : G × G →* G₂} {P Γ₂ K₂ : Subgroup G₂} {Γ K : Subgroup G} [Countable Γ] {r : Γ → Γ₂}
  {μ : Measure G} [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] {𝓕 : Set G} {A : Finset G}
  {δ : P →* ℝ≥0} {χ : P →* Circle} {f : G₂ → ℂ} {ρ s₀ : ℂ}

end Flat

end GlobalTheory.DefDoubling
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerNormInvariant
section
open scoped Classical

namespace GlobalTheory.LKMid.TwCent

open GlobalTheory.LKMid

variable {H : Type} [Group H] (θ : H →* H)

theorem nrmG_succ' (j : ℕ) (δ : H) : nrmG θ (j + 1) δ = nrmG θ j δ * (⇑θ)^[j] δ := by
  simp [nrmG, List.range_succ, List.map_append, List.prod_append]

theorem mul_map_nrmG (j : ℕ) (δ : H) : δ * θ (nrmG θ j δ) = nrmG θ (j + 1) δ := by
  induction j with
  | zero => simp [nrmG]
  | succ j ih =>
    rw [nrmG_succ' θ (j + 1), nrmG_succ', map_mul, ← mul_assoc, ih, ← Function.iterate_succ_apply' (⇑θ), nrmG_succ' θ j]

theorem iterate_twConj (δ : H) (i : ℕ) (h : H) :
    (⇑((MulAut.conj δ).toMonoidHom.comp θ))^[i] h = nrmG θ i δ * (⇑θ)^[i] h * (nrmG θ i δ)⁻¹ := by
  induction i with
  | zero => simp [nrmG]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply' (⇑θ), ← mul_map_nrmG]
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      map_mul, map_inv, mul_inv_rev, inv_inv]
    group

theorem main : ∀ {H : Type} [Group H] (θ : H →* H) (δ : H) (r : ℕ), 0 < r → (∀ h, (⇑θ)^[r] h = h) →
    (∀ z ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}, δ * θ z * δ⁻¹ ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}) ∧
    (∀ z ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}, (⇑((MulAut.conj δ).toMonoidHom.comp θ))^[r] z = z) := by
  intro H _ θ δ r _ hθ
  have key : δ * θ (nrmG θ r δ) = nrmG θ r δ * δ := by
    rw [mul_map_nrmG, nrmG_succ', hθ]
  have hN : nrmG θ r δ = δ * θ (nrmG θ r δ) * δ⁻¹ := by rw [key]; group
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    have h2 : θ (nrmG θ r δ) * θ z = θ z * θ (nrmG θ r δ) := by rw [← map_mul, ← hz, map_mul]
    symm
    calc nrmG θ r δ * (δ * θ z * δ⁻¹) = δ * (θ (nrmG θ r δ) * θ z) * δ⁻¹ := by
          conv_lhs => rw [hN]
          group
      _ = δ * (θ z * θ (nrmG θ r δ)) * δ⁻¹ := by rw [h2]
      _ = δ * θ z * δ⁻¹ * nrmG θ r δ := by
          conv_rhs => rw [hN]
          group
  · rw [Subgroup.mem_centralizer_singleton_iff] at hz
    rw [iterate_twConj, hθ, ← hz, mul_inv_cancel_right]

end GlobalTheory.LKMid.TwCent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHeckeTestFunctionSupportCompact
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem isTest_support_compact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
    ∃ Ω : Set G.GAf, IsCompact Ω ∧ ∀ g, f g ≠ 0 → g ∈ Ω := by
  intro p _ G L f hf
  obtain ⟨-, -, -, S, hS⟩ := hf
  have hK : IsCompact ((L.K.toSubgroup : Subgroup G.GAf) : Set G.GAf) := L.compact
  refine ⟨⋃ s ∈ S, (fun ab : G.GAf × G.GAf => ab.1 * s * ab.2) ''
      ((L.K.toSubgroup : Set G.GAf) ×ˢ (L.K.toSubgroup : Set G.GAf)), ?_, ?_⟩
  · refine S.isCompact_biUnion fun s _ => (hK.prod hK).image ?_
    fun_prop
  · intro g hg
    obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩ := hS g hg
    exact Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormProductIterateTwistedConj
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem nrmG_succ {H : Type} [Group H] (θ : H →* H) (r : ℕ) (δ : H) :
    nrmG θ (r + 1) δ = nrmG θ r δ * (⇑θ)^[r] δ := by
  simp [nrmG, List.range_succ, List.map_append, List.prod_append]

theorem iter_hom_mul {H : Type} [Group H] (θ : H →* H) (r : ℕ) (x y : H) :
    (⇑θ)^[r] (x * y) = (⇑θ)^[r] x * (⇑θ)^[r] y := by
  induction r generalizing x y with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      map_mul, ih]

theorem iter_hom_inv {H : Type} [Group H] (θ : H →* H) (r : ℕ) (x : H) :
    (⇑θ)^[r] x⁻¹ = ((⇑θ)^[r] x)⁻¹ := by
  induction r generalizing x with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, map_inv, ih]

theorem nrmG_twConj {H : Type} [Group H] (θ : H →* H) (r : ℕ) (δ g : H) :
    nrmG θ r (g⁻¹ * δ * θ g) = g⁻¹ * nrmG θ r δ * (⇑θ)^[r] g ∧
      δ * θ (nrmG θ r δ) = nrmG θ r δ * (⇑θ)^[r] δ := by
  induction r with
  | zero => simp [nrmG]
  | succ r ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [nrmG_succ, nrmG_succ, h1, iter_hom_mul, iter_hom_mul,
        iter_hom_inv, Function.iterate_succ_apply]
      group
    · rw [nrmG_succ, map_mul, ← mul_assoc, h2, mul_assoc, ← Function.iterate_succ_apply' (⇑θ), mul_assoc]

end GlobalTheory.LKMid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix

namespace GlobalTheory.LiftLower

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def csumAt {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ) (f g : S.Forms) : ℂ :=
  star (fun a => σ (S.basis.repr f a)) ⬝ᵥ (S.H.map σ) *ᵥ fun a => σ (S.basis.repr g a)

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

abbrev levSW (i : Fin D.R.m) : Set (GA D (Wc D i)) := levS _ (R.βW i) (R.datWp i R.triv)

abbrev chiW (i : Fin D.R.m) : GA D (Wc D i) → ℂ := Lev.levChi _ (R.βW i) (R.datWp i R.triv)

def partH (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) : Submodule ℂ (R.HW i σ).H :=
  (partFull R.θ (R.MW i σ) (levSW R i) (chiW R i) (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) c).comap (R.HW i σ).e

def IsNormSys (i : Fin D.R.m) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) : Prop :=
  ∀ P d, (¬ ∃ Rp, Hecke₂ (Wc D i) (levSW R i) (chiW R i) (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P d Rp) → c P d = 0

def projH (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : (R.HW i σ).H →ₗ[ℂ] (R.HW i σ).H :=
  ∑ g, RealDat.eC (A := A) σ g • R.gW i σ g

variable (D) in

def hookPlus (i : Fin D.R.m) : ℝ :=
  ∑ ρ : D.what₂.Tau, Real.log (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D i ρ) (aPl D i (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D i ρ) ρ) : ℝ)

structure NumTie (F : Face D A) (b : ℝ) : Prop where
  sizes : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Sizes D i b
  main : ∀ i, (F.Zsc (R.toCx F).zs).l6m i = hookPlus D i
  unit : (F.Zsc (R.toCx F).zs).l6u = (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Lp D b

variable {R}

theorem Q_base (h : R.toLevCh.Is A.μ0) : R.Q A.μ0 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro PP hPP
  refine (h.Q_ram A.μ0 PP).2 (Or.inl hPP) ?_
  rw [h.xi_base]
  intro x _
  rfl

theorem typePart_base (h : R.toLevCh.Is A.μ0) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.typePart R i σ A.μ0 R.triv c = partH R i σ c := by
  classical
  have e : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.finS R A.μ0 = GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.finS GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF
    rw [Q_base h]
    congr 1
    ext; simp
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.typePart partH
  rw [e]

theorem e_projH (h : R.models_gW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (x : (R.HW i σ).H) :
    (R.HW i σ).e (projH R i σ x) = postOn _ (R.eWf i σ) ((R.HW i σ).e x) := by
  unfold projH RealDat.eWf gaL
  rw [LinearMap.sum_apply, map_sum]
  ext v g
  simp only [LinearMap.smul_apply, map_smul, h i σ, postOn_apply, LinearMap.sum_apply, MultilinearMap.sum_apply,
    MultilinearMap.smul_apply]
  rfl

end GlobalTheory.LiftLower

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryEquationBaseChangeAlgHomStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryEquation_baseChange_algHom : ∀ {F E R K : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing K] [Algebra F K] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (φ : R →ₐ[F] K) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)), Formalism.UG.cT (sigR R σ) g * JR R J * g = JR R J → Formalism.UG.cT (sigR K σ) (g.map (Algebra.TensorProduct.map φ (AlgHom.id F E))) * JR K J * g.map (Algebra.TensorProduct.map φ (AlgHom.id F E)) = JR K J := by
  first | exact @GlobalTheory.unitaryEq_baseChange | exact GlobalTheory.unitaryEq_baseChange | (intros; apply GlobalTheory.unitaryEq_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedExtensionBasis
section
open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes GlobalTheory.LKRes.ResSplit

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.LKRes.ResSplit

theorem pow_sub_one_ne_zero (p : ℕ) [Fact p.Prime] {r : ℕ} (hr : 0 < r) : p ^ r - 1 ≠ 0 := by
  have h := Nat.one_lt_pow hr.ne' (Fact.out : p.Prime).one_lt
  omega

theorem Qr_eq_adjoin (p : ℕ) [Fact p.Prime] {r : ℕ} (hr : 0 < r) {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ (p ^ r - 1)) (hζr : ζ ∈ Qr p r) :
    Qr p r = IntermediateField.adjoin ℚ_[p] {ζ} := by
  apply le_antisymm
  · apply UnramifiedExtensions.Kn_le (Q0 p) bot_le
    intro ξ hξ
    rw [residue_cardinality_base_field] at hξ
    have : NeZero (p ^ r - 1) := ⟨pow_sub_one_ne_zero p hr⟩
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ) i
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact hζr

theorem Qr_span_pow (p : ℕ) [Fact p.Prime] {r : ℕ} (hr : 0 < r) (ζ : Qr p r)
    (hζ : IsPrimitiveRoot (ζ : PadicAlgCl p) (p ^ r - 1)) (b : Qr p r) :
    ∃ d : Fin r → ℚ_[p], b = ∑ j : Fin r, d j • ζ ^ (j : ℕ) := by
  have hQ := Qr_eq_adjoin p hr hζ ζ.2
  have hrank : Module.finrank ℚ_[p] (Qr p r) = r := by
    rw [finrank_Kn p (Q0 p) inferInstance hr, IntermediateField.finrank_bot, mul_one]
  have hint : IsIntegral ℚ_[p] (ζ : PadicAlgCl p) := Algebra.IsIntegral.isIntegral _
  set pb := IntermediateField.adjoin.powerBasis hint
  have hdim : pb.dim = r := by
    rw [← PowerBasis.finrank pb]
    exact (congrArg (fun L : IntermediateField ℚ_[p] (PadicAlgCl p) => Module.finrank ℚ_[p] L) hQ).symm.trans hrank
  have hb : (b : PadicAlgCl p) ∈ IntermediateField.adjoin ℚ_[p] {(ζ : PadicAlgCl p)} := by
    rw [← hQ]; exact b.2
  obtain ⟨f, hf, hy⟩ := pb.exists_eq_aeval ⟨b, hb⟩
  rw [hdim] at hf
  have h1 : (b : PadicAlgCl p) = Polynomial.aeval (ζ : PadicAlgCl p) f := by
    have := congrArg Subtype.val hy
    rw [this]
    show IntermediateField.val _ (Polynomial.aeval pb.gen f) = _
    rw [← Polynomial.aeval_algHom_apply]
    rfl
  refine ⟨fun j => f.coeff j, ?_⟩
  apply Subtype.ext
  rw [h1, Polynomial.aeval_eq_sum_range' hf, Finset.sum_range]
  simp [IntermediateField.coe_sum]

theorem KQ_eq_sum_pow : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ), 0 < r →
    ∀ (ζ : Qr p r), IsPrimitiveRoot (ζ : PadicAlgCl p) (p ^ r - 1) →
    ∀ x : KQ p K r, ∃ c : Fin r → K, x = ∑ j : Fin r, inclK p K r (c j) * inclQ p K r ζ ^ (j : ℕ) := by
  intro p _ K r hr ζ hζ x
  have key : ∀ (c : K) (z : Qr p r), inclK p K r c * inclQ p K r z = (c ⊗ₜ[ℚ_[p]] z : K ⊗[ℚ_[p]] Qr p r) := by
    intro c z
    show (c ⊗ₜ[ℚ_[p]] (1 : Qr p r) : K ⊗[ℚ_[p]] Qr p r) * ((1 : K) ⊗ₜ[ℚ_[p]] z) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have h : ∀ y : K ⊗[ℚ_[p]] Qr p r, ∃ c : Fin r → K,
      y = ∑ j : Fin r, (c j ⊗ₜ[ℚ_[p]] (ζ ^ (j : ℕ)) : K ⊗[ℚ_[p]] Qr p r) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a b =>
      obtain ⟨d, hd⟩ := Qr_span_pow p hr ζ hζ b
      refine ⟨fun j => d j • a, ?_⟩
      rw [hd, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    | add y z hy hz =>
      obtain ⟨c, hc⟩ := hy
      obtain ⟨c', hc'⟩ := hz
      refine ⟨c + c', ?_⟩
      rw [hc, hc', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.add_apply, TensorProduct.add_tmul]
  obtain ⟨c, hc⟩ := h x
  refine ⟨c, ?_⟩
  have e : ∀ j : Fin r, inclK p K r (c j) * inclQ p K r ζ ^ (j : ℕ) =
      (c j ⊗ₜ[ℚ_[p]] (ζ ^ (j : ℕ)) : K ⊗[ℚ_[p]] Qr p r) := by
    intro j
    rw [← map_pow, key]
  rw [Finset.sum_congr rfl fun j _ => e j]
  exact hc

end GlobalTheory.LKRes.ResSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationConstantOfPowerEqStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_constant_of_power_eq : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (Z : Scheme.{0}) (f : Z ⟶ Spec (.of O)) (D : LB Z), D.IsLB →
  ∀ sig : (D.pull (genericι f)).Gen, sig.IsGen →
  ∀ (M : ℕ) (n : ℤ) (gen : (lbPow D M).Gen), 1 ≤ M → gen.IsGen → PowEq f ϖ hϖ D sig M n gen →
  ValConst f ϖ D sig M n := by
  first | exact @GlobalTheory.ValConstOfPowEq.valConst_of_powEq | exact GlobalTheory.ValConstOfPowEq.valConst_of_powEq | (intros; apply GlobalTheory.ValConstOfPowEq.valConst_of_powEq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecHeightSmulAlgebraMap
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.ChowHt GlobalTheory.Adelic

namespace GlobalTheory.Adelic

theorem vecHeight_smul_algebraMap (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (hw : Submodule.span F (Set.range w.col) = ⊤) (hA : ∀ σ, (A σ).det ≠ 0)
    (Ω : Type) [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω] [Algebra K Ω] [IsScalarTower F K Ω]
    (y : Fin N → K) (c : Ω) (hy : y ≠ 0) (hc : c ≠ 0) :
    vecHeight w A (c • fun j => algebraMap K Ω (y j)) = pointHeight w A y := by
  set z : Fin N → Ω := c • fun j => algebraMap K Ω (y j) with hz
  let L : IntermediateField K Ω := IntermediateField.adjoin K {c}
  have hcK : IsIntegral K c := ((Algebra.IsAlgebraic.isAlgebraic (R := F) c).tower_top K).isIntegral
  haveI : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional hcK
  haveI : NumberField L := NumberField.of_module_finite K L
  have hcL : c ∈ L := IntermediateField.mem_adjoin_simple_self K c
  have hle : coordField F z ≤ L.restrictScalars F := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨j, rfl⟩
    exact mul_mem hcL (L.algebraMap_mem (y j))
  let ι : coordField F z →ₐ[F] L := IntermediateField.inclusion hle
  letI : Algebra (coordField F z) L := ι.toRingHom.toAlgebra
  haveI : IsScalarTower F (coordField F z) L := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  let z' : Fin N → coordField F z := fun j => ⟨z j, IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩⟩
  let c' : L := ⟨c, hcL⟩
  have hc' : c' ≠ 0 := fun h => hc (congrArg Subtype.val h)
  have hyL : (fun j => algebraMap K L (y j)) ≠ 0 := fun h => hy (funext fun j =>
    (algebraMap K L).injective ((congrFun h j).trans (map_zero _).symm))
  have he : (fun j => algebraMap (coordField F z) L (z' j)) = c' • fun j => algebraMap K L (y j) :=
    funext fun j => Subtype.ext rfl
  have hz' : z' ≠ 0 := fun h => smul_ne_zero hc' hyL (by
    rw [← he, h]; exact funext fun j => map_zero _)
  have h1 := GlobalTheory.T.normalizedPointHeightLattice_algebraMap F (coordField F z) N n w A hw hA L z' hz'
  have h2 := GlobalTheory.T.normalizedPointHeightLattice_smul F L N n w A hw hA _ c' hyL hc'
  have h3 := GlobalTheory.T.normalizedPointHeightLattice_algebraMap F K N n w A hw hA L y hy
  rw [he, h2, h3] at h1
  exact h1.symm

end GlobalTheory.Adelic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerMulTorusIteratedFactorisationStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_mul_torus_iterated_factorisation : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (π : CuspSub E a) (α : HeightOneSpectrum (𝓞 E) → Fin a → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∀ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ) → ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ x ∈ GlobalTheory.JSW.supS E a S, GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.JSW.tl ϖ l) = (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ.1 x := by
  first | exact @GlobalTheory.JSW.whit_mul_tl | exact GlobalTheory.JSW.whit_mul_tl | (intros; apply GlobalTheory.JSW.whit_mul_tl <;> assumption)
end

