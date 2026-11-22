import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0386
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0625
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0391
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0465
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0384
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0020
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0019
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0025
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0044
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0027
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0643
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0639
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0617
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0628
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0640
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0631
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0624
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0637
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0615
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0642
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingBottomRowOrbits
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingIntegralBottomRow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingMirabolicCosetsStatement

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableSingleSegment
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.SquareIntegrableSegments

theorem length_le_one_of_partial_products {h : ℕ} (d e f : Fin h → ℝ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hd : ∀ i, 0 < d i) (he : Antitone e) (hf : ∀ i, f i = q ^ (d i * e i))
    (hpart : ∀ j : Fin h, j.val + 1 < h → ∏ i ∈ Finset.univ.filter (· ≤ j), f (Fin.rev i) < 1)
    (hfull : ∏ i, f (Fin.rev i) = 1) : h ≤ 1 := by
  by_contra hh
  have h2 : 2 ≤ h := by omega
  have hlog : Real.log q ≠ 0 := (Real.log_neg hq0 hq1).ne
  have hprod : ∀ s : Finset (Fin h), ∏ i ∈ s, f i = q ^ (∑ i ∈ s, d i * e i) := fun s => by
    rw [Real.rpow_sum_of_pos hq0]
    exact Finset.prod_congr rfl fun i _ => hf i
  have htot : ∑ i, d i * e i = 0 := by
    have h1 : ∏ i, f i = 1 := by
      rw [← hfull]
      exact (Equiv.prod_comp Fin.revPerm f).symm
    rw [hprod] at h1
    have h3 := congrArg Real.log h1
    rw [Real.log_rpow hq0, Real.log_one] at h3
    exact (mul_eq_zero.1 h3).resolve_right hlog
  obtain ⟨j, hj0, hj⟩ := GlobalTheory.CompanionTheory.Inequalities.weighted_antitone_last_nonpos h d e h2 hd he htot
  have hlt := hpart (Fin.rev j) (by have := j.isLt; rw [Fin.val_rev]; omega)
  have hrw := GlobalTheory.CompanionTheory.FinReversal.prod_filter_le_rev h f (Fin.rev j)
  rw [Fin.rev_rev] at hrw
  rw [hrw, hprod] at hlt
  exact absurd hlt (not_lt.2 (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hq0 hq1.le hj))

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem deg_eq_of_isLSeg {Δ : Segment k} {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (h : IsLSeg Δ π) : Δ.deg = N := by
  obtain ⟨hd, -⟩ := h
  rw [← hd, Segment.sum_term_fst]

theorem sum_deg_of_listing {h : ℕ} {D : Fin h → Segment k} {𝔪 : Multiset (Segment k)}
    (hD : Finset.univ.val.map D = 𝔪) : ∑ i, (D i).deg = (𝔪.map Segment.deg).sum := by
  rw [← hD, Multiset.map_map]
  rfl

theorem exists_class (hE : Zc.LSegExists k) (Δ : Segment k) : ∃ y : IrrGL k, IsLSeg Δ y.rep := by
  obtain ⟨π, hd, hc⟩ := hE Δ
  exact ⟨IrrGL.of π.ρ π.smooth π.irr, hd,
    hc.of_equiv (IrrGL.equivOf π.ρ π.smooth π.irr) (Representation.Equiv.refl _)⟩

theorem card_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    Zc.LSocleGL k → Zl.CasselmanNecSq k → Zc.LSegExists k → ∀ (𝔪 : Multiset (Segment k)) (N : ℕ) {V : Type}
      [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), 1 ≤ N → IsSmooth π → π.IsIrreducible →
        IsSqIntCoeff π → IsL 𝔪 π → 𝔪.card = 1 := by
  intro k _ _ _ _ hS hC hE 𝔪 N V _ _ π hN hsm hirr hsq hL
  choose y hy using exists_class hE
  have hdeg : ∀ Δ, (y Δ).1 = Δ.deg := fun Δ => (deg_eq_of_isLSeg (hy Δ)).symm
  have hpos : ∀ Δ, 0 < (y Δ).1 := fun Δ => by
    rw [hdeg]
    exact Nat.mul_pos Δ.len_pos Δ.d_pos
  choose s hs using fun Δ => GlobalTheory.T.central_character_norm_eq_pow k (y Δ) (hpos Δ)
  obtain ⟨h, D, hD, hanti, hno⟩ := GlobalTheory.CompanionTheory.Multiset.exists_antitone_listing 𝔪 s Segment.Precedes
    fun a b hab => GlobalTheory.T.exponent_lt_of_precedes_of_isLSeg k a b (y a) (y b) (s a) (s b) (hy a) (hy b) (hs a) (hs b) hab
  let x : Fin h → IrrGL k := fun i => y (D i)
  have hLF : LFactors 𝔪 x := ⟨D, ⟨hD, hno⟩, fun i => hy (D i)⟩
  have hsum : ∑ a, (x a).1 = N := by
    obtain ⟨h', x', hd', ⟨D', ⟨hD', -⟩, hx'⟩, -⟩ := hL
    rw [← hd']
    have e1 : ∑ a, (x a).1 = ∑ a, (D a).deg := Finset.sum_congr rfl fun a _ => hdeg (D a)
    have e2 : ∑ a, (x' a).1 = ∑ a, (D' a).deg :=
      Finset.sum_congr rfl fun a _ => (deg_eq_of_isLSeg (hx' a)).symm
    rw [e1, e2, sum_deg_of_listing hD, sum_deg_of_listing hD']
  have hsumrev : ∑ a, (x (Fin.rev a)).1 = N := by
    rw [← hsum]
    exact Equiv.sum_comp Fin.revPerm fun a => (x a).1
  have hsoc := hS 𝔪 h N x hsumrev hLF π hL
  have hposrev : ∀ a, 0 < ((x ∘ Fin.rev) a).1 := fun a => hpos _
  have hjm := GlobalTheory.T.jacquet_multiplicity_pos_of_socle k h N (x ∘ Fin.rev) hsumrev π hsm hposrev hsoc
  have hex := hC N π hN hsm hirr hsq h (x ∘ Fin.rev) hsumrev hposrev hjm
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_unit_pow_tendsto_zero' k
  have hnabs := GlobalTheory.T.norm_lt_one_of_pow_tendsto_zero k t ht
  choose c hc using fun i => GlobalTheory.T.central_character_exists k (x i) t
  obtain ⟨hpart, hfull⟩ := hex t ht (c ∘ Fin.rev) fun i => hc (Fin.rev i)
  have hle : h ≤ 1 := length_le_one_of_partial_products (fun i => ((x i).1 : ℝ)) (fun i => s (D i))
    (fun i => ‖c i‖) (nabs_pos' k t) hnabs (fun i => by exact_mod_cast hpos (D i)) hanti
    (fun i => hs (D i) t (c i) (hc i)) hpart hfull
  have hh0 : h ≠ 0 := by
    rintro rfl
    simp at hsum
    omega
  have hcard : 𝔪.card = h := by
    rw [← hD]
    simp
  omega

end GlobalTheory.CompanionTheory.SquareIntegrableSegments
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapTwistCompactPartInProd
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitUnit

theorem compact_zpowers_fst {H : Type} [Group H] [TopologicalSpace H] [T2Space H] (t : H × H)
    (hc : IsCompact (closure (Subgroup.zpowers t : Set (H × H)))) :
    IsCompact (closure (Subgroup.zpowers t.1 : Set H)) := by
  have hi : IsCompact (Prod.fst '' closure (Subgroup.zpowers t : Set (H × H))) := hc.image continuous_fst
  refine hi.of_isClosed_subset isClosed_closure (closure_minimal ?_ hi.isClosed)
  rintro x ⟨k, rfl⟩
  refine ⟨t ^ k, subset_closure ⟨k, rfl⟩, ?_⟩
  simp

theorem main : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H) (d d' : H),
  Continuous σ → (∀ g, σ (σ g) = g) → (∀ k ∈ K, σ k ∈ K) → d ∈ K → d' ∈ K →
  cptPart (twCent (MonoidHom.id H) (d * σ d')) ≤ K →
  (∀ g : H, g⁻¹ * (d * σ d') * MonoidHom.id H g ∈ K → ∃ t ∈ twCent (MonoidHom.id H) (d * σ d'), t⁻¹ * g ∈ K) →
  cptPart (twCent (swTw σ) (d, d')) ≤ K.prod K ∧
    ∀ y : H × H, y⁻¹ * (d, d') * swTw σ y ∈ K.prod K → ∃ t ∈ twCent (swTw σ) (d, d'), ∃ k ∈ K.prod K, y = t * k := by
  intro H _ _ _ _ σ K d d' _ hσ hK hd hd' hcpt hsurj
  refine ⟨?_, ?_⟩
  · rw [cptPart, Subgroup.closure_le]
    rintro t ⟨ht, hc⟩
    obtain ⟨h₁, h₂⟩ := (mem_twCent_swTw σ hσ d d' t).1 ht
    have hg : t.1 ∈ K :=
      hcpt (Subgroup.subset_closure ⟨h₁, compact_zpowers_fst t hc⟩)
    refine Subgroup.mem_prod.2 ⟨hg, ?_⟩
    rw [h₂]
    exact K.mul_mem (K.mul_mem hd' (hK _ hg)) (K.inv_mem hd')
  · rintro ⟨x₁, x₂⟩ hy
    have hy' := Subgroup.mem_prod.1 hy
    have hz₁ : x₁⁻¹ * d * σ x₂ ∈ K := by simpa using hy'.1
    have hz₂ : x₂⁻¹ * d' * σ x₁ ∈ K := by simpa using hy'.2
    have hN : x₁⁻¹ * (d * σ d') * MonoidHom.id H x₁ ∈ K := by
      have e : x₁⁻¹ * (d * σ d') * MonoidHom.id H x₁ = (x₁⁻¹ * d * σ x₂) * σ (x₂⁻¹ * d' * σ x₁) := by
        simp only [map_mul, map_inv, hσ, MonoidHom.id_apply]
        group
      rw [e]
      exact K.mul_mem hz₁ (hK _ hz₂)
    obtain ⟨g, hg, hk₁⟩ := hsurj x₁ hN
    refine ⟨(g, d' * σ g * d'⁻¹), (mem_twCent_swTw σ hσ d d' _).2 ⟨hg, rfl⟩,
      (g⁻¹ * x₁, d' * σ (g⁻¹ * x₁) * (x₂⁻¹ * d' * σ x₁)⁻¹), ?_, ?_⟩
    · exact Subgroup.mem_prod.2 ⟨hk₁, K.mul_mem (K.mul_mem hd' (hK _ hk₁)) (K.inv_mem hz₂)⟩
    · ext
      · simp
      · simp only [Prod.mk_mul_mk, map_mul, map_inv]
        group

end GlobalTheory.CompanionTheory.SplitUnit

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapTwistCompactPartLe
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

namespace GlobalTheory.CompanionTheory.SplitCpt

theorem cptPart_le_self' {G : Type} [Group G] [TopologicalSpace G] (T : Subgroup G) : cptPart T ≤ T := by
  rw [cptPart, Subgroup.closure_le]
  rintro t ⟨ht, -⟩
  exact ht

theorem mem_map_conj {G : Type} [Group G] (K : Subgroup G) (x c : G) :
    c ∈ K.map (MulAut.conj x).toMonoidHom ↔ x⁻¹ * c * x ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa [mul_assoc] using hk
  · intro h
    refine ⟨_, h, ?_⟩
    simp [mul_assoc]

theorem split_cpt : ∀ {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H) (d d' : H),
  Continuous σ → (∀ g, σ (σ g) = g) → IsOpen (K : Set H) → IsCompact (K : Set H) → (∀ k ∈ K, σ k ∈ K) →
  PositivityTheory.Rg.BcB.G8.Fin.Good (MonoidHom.id H) K (d * σ d') → ∀ y : H × H,
  twCent (swTw σ) (d, d') ⊓ (K.prod K).map (MulAut.conj y).toMonoidHom ≤ cptPart (twCent (swTw σ) (d, d')) ∧
    (twCent (swTw σ) (d, d') ⊓ (K.prod K).map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent (swTw σ) (d, d'))) ≠ 0 := by
  intro H _ _ _ _ σ K d d' _hσc hσ hKo hKc hσK hG y
  set T := twCent (swTw σ) (d, d') with hT
  set Cn := twCent (MonoidHom.id H) (d * σ d') with hCn
  have hKKc : IsCompact (((K.prod K).map (MulAut.conj y).toMonoidHom : Subgroup (H × H)) : Set (H × H)) := by
    rw [Subgroup.coe_map, Subgroup.coe_prod]
    exact (hKc.prod hKc).image (by
      show Continuous fun z : H × H => y * z * y⁻¹
      fun_prop)
  have hKKcl := hKKc.isClosed
  refine ⟨?_, ?_⟩
  · intro t ht
    apply Subgroup.subset_closure
    refine ⟨ht.1, hKKc.of_isClosed_subset isClosed_closure ?_⟩
    exact closure_minimal (fun z hz => (Subgroup.zpowers_le.2 ht.2) hz) hKKcl
  · have hmapC : (cptPart T).map (MonoidHom.fst H H) ≤ cptPart Cn := by
      rw [Subgroup.map_le_iff_le_comap, cptPart, Subgroup.closure_le]
      rintro t ⟨htT, htc⟩
      apply Subgroup.subset_closure
      refine ⟨((mem_twCent_swTw σ hσ d d' t).1 htT).1, ?_⟩
      have hC := htc.image continuous_fst
      refine hC.of_isClosed_subset isClosed_closure (closure_minimal ?_ hC.isClosed)
      rintro _ ⟨k, rfl⟩
      exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩
    set x₃ : H := σ (d'⁻¹ * y.2) with hx₃
    set B : Subgroup H := (Cn ⊓ K.map (MulAut.conj y.1).toMonoidHom) ⊓ (Cn ⊓ K.map (MulAut.conj x₃).toMonoidHom) with hB
    have hB0 : B.relIndex (cptPart Cn) ≠ 0 :=
      Subgroup.relIndex_inf_ne_zero (hG.2 y.1).2 (hG.2 x₃).2
    have hB1 : B.relIndex ((cptPart T).map (MonoidHom.fst H H)) ≠ 0 :=
      mt (Subgroup.relIndex_eq_zero_of_le_right hmapC) hB0
    have hB2 : (B.comap (MonoidHom.fst H H)).relIndex (cptPart T) ≠ 0 := by
      rwa [Subgroup.relIndex_comap]
    have hB3 : (B.comap (MonoidHom.fst H H) ⊓ cptPart T).relIndex (cptPart T) ≠ 0 := by
      rwa [Subgroup.inf_relIndex_right]
    have hle : B.comap (MonoidHom.fst H H) ⊓ cptPart T ≤
        T ⊓ (K.prod K).map (MulAut.conj y).toMonoidHom := by
      rintro c ⟨hcB, hcC⟩
      have hcT : c ∈ T := cptPart_le_self' T hcC
      refine ⟨hcT, ?_⟩
      have h2 := ((mem_twCent_swTw σ hσ d d' c).1 hcT).2
      have hm1 : y.1⁻¹ * c.1 * y.1 ∈ K := (mem_map_conj K _ _).1 hcB.1.2
      have hm3 : x₃⁻¹ * c.1 * x₃ ∈ K := (mem_map_conj K _ _).1 hcB.2.2
      refine (mem_map_conj _ _ _).2 (Subgroup.mem_prod.2 ⟨hm1, ?_⟩)
      have hs := hσK _ hm3
      have e : (y⁻¹ * c * y).2 = σ (x₃⁻¹ * c.1 * x₃) := by
        simp only [Prod.snd_mul, Prod.snd_inv, h2, hx₃, map_mul, map_inv, hσ]
        group
      show (y⁻¹ * c * y).2 ∈ K
      rw [e]
      exact hs
    exact fun h0 => hB3 (Subgroup.relIndex_eq_zero_of_le_left hle h0)

end GlobalTheory.CompanionTheory.SplitCpt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedLanglandsFactorsSquareIntegrable
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.TemperedCore

theorem exists_lFactors_unitary : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.LSocleGL k → Zl.CasselmanNecTemp k → Zc.LSegExists k → ∀ (𝔪 : Multiset (Segment k)) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), 1 ≤ N → IsSmooth π → π.IsIrreducible → IsTemperedCoeff π → IsL 𝔪 π → ∃ (h : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), LFactors 𝔪 x ∧ ∀ (a : Fin h) (t : kˣ) (c : ℂ), Zl.ScalarBy (x a) t c → ‖c‖ = 1 := by
  intro k _ _ _ _ hSoc hCas hSeg 𝔪 N V _ _ π hN hsm hirr htemp hL
  have hy : ∀ Δ : Segment k, ∃ y : IrrGL k, IsLSeg Δ y.rep := fun Δ => by
    obtain ⟨ρ, hρ⟩ := hSeg Δ
    exact ⟨IrrGL.of ρ.ρ ρ.smooth ρ.irr, hρ.of_equiv (IrrGL.equivOf _ _ _)⟩
  choose y hyL using hy
  have hypos : ∀ Δ : Segment k, 0 < (y Δ).1 := fun Δ => by
    rw [← (hyL Δ).deg_eq]
    exact Nat.mul_pos Δ.len_pos Δ.d_pos
  have hs : ∀ Δ : Segment k, ∃ s : ℝ, ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy (y Δ) t c →
      ‖c‖ = nabs k t ^ (((y Δ).1 : ℝ) * s) := fun Δ => GlobalTheory.T.central_character_norm_eq_pow k (y Δ) (hypos Δ)
  choose f hf using hs
  obtain ⟨h, Δ, hΔ, hanti, hnp⟩ := GlobalTheory.T.multiset_antitone_enumeration 𝔪 f Segment.Precedes (fun a b hab =>
    GlobalTheory.T.exponent_lt_of_precedes_of_isLSeg k a b (y a) (y b) (f a) (f b) (hyL a) (hyL b) (hf a) (hf b) hab)
  let x : Fin h → IrrGL k := fun a => y (Δ a)
  have hLF : LFactors 𝔪 x := ⟨Δ, ⟨hΔ, hnp⟩, fun i => hyL _⟩
  have hsumdeg : ∀ {h' : ℕ} (Δ' : Fin h' → Segment k) (x' : Fin h' → IrrGL k),
      Finset.univ.val.map Δ' = 𝔪 → (∀ i, IsLSeg (Δ' i) (x' i).rep) →
      ∑ a, (x' a).1 = (𝔪.map Segment.deg).sum := by
    intro h' Δ' x' hm hx'
    rw [← hm, Multiset.map_map]
    exact Finset.sum_congr rfl fun a _ => ((hx' a).deg_eq).symm
  have hdeg : ∑ a, (x a).1 = N := by
    obtain ⟨h', x', hd', ⟨Δ', ⟨hΔ', -⟩, hx'⟩, -⟩ := hL
    rw [hsumdeg Δ x hΔ (fun i => hyL _), ← hsumdeg Δ' x' hΔ' hx', hd']
  have hdrev : ∑ a, (x (Fin.rev a)).1 = N := by
    rw [← hdeg]
    exact Equiv.sum_comp Fin.revPerm (fun a => (x a).1)
  have hsoc := hSoc 𝔪 h N x hdrev hLF π hL
  have hjm := GlobalTheory.T.jacquet_multiplicity_pos_of_socle k h N (x ∘ Fin.rev) hdrev π hsm (fun a => hypos _) hsoc
  have hW := hCas N π hN hsm hirr htemp h (x ∘ Fin.rev) hdrev (fun a => hypos _) hjm
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_unit_pow_tendsto_zero' k
  have ht1 : nabs k t < 1 := GlobalTheory.T.norm_lt_one_of_pow_tendsto_zero k t ht
  have ht0 : 0 < nabs k t := by
    have h0 : (MeasureTheory.distribHaarChar k t : NNReal) ≠ 0 := fun h0 => by
      have := map_mul (MeasureTheory.distribHaarChar k) t t⁻¹
      simp [h0] at this
    exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 h0)
  have hge : ∀ r : ℝ, nabs k t ^ r ≤ 1 → 0 ≤ r := fun r hr => by
    by_contra hneg
    exact absurd hr (not_le.2 (Real.one_lt_rpow_of_pos_of_lt_one_of_neg ht0 ht1 (not_le.1 hneg)))
  choose c hc using fun a => GlobalTheory.T.central_character_exists k (x a) t
  obtain ⟨hpart, htot⟩ := hW t ht (c ∘ Fin.rev) (fun i => hc _)
  let e : Fin h → ℝ := fun i => f (Δ i)
  let d : Fin h → ℝ := fun i => ((x i).1 : ℝ)
  have hnorm : ∀ i, ‖c i‖ = nabs k t ^ (d i * e i) := fun i => hf (Δ i) t (c i) (hc i)
  have hprod : ∀ S : Finset (Fin h), ∏ i ∈ S, ‖c i‖ = nabs k t ^ (∑ i ∈ S, d i * e i) := fun S => by
    rw [Real.rpow_sum_of_pos ht0]
    exact Finset.prod_congr rfl fun i _ => hnorm i
  have hsum : ∑ i, d i * e i = 0 := by
    have h1 : ∏ i, ‖c i‖ = 1 := by
      rw [← htot]
      exact (Equiv.prod_comp Fin.revPerm (fun i => ‖c i‖)).symm
    rw [hprod] at h1
    refine le_antisymm ?_ (hge _ h1.le)
    have := hge (-∑ i, d i * e i) (by rw [Real.rpow_neg ht0.le, h1, inv_one])
    linarith
  have htail : ∀ j : Fin h, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => j ≤ i), d i * e i := by
    intro j
    by_cases hj : (Fin.rev j).val + 1 < h
    · have h1 := hpart (Fin.rev j) hj
      have h2 := GlobalTheory.T.prod_le_rev_eq_prod_ge h (fun i => ‖c i‖) (Fin.rev j)
      rw [Fin.rev_rev] at h2
      have h3 : ∏ i ∈ Finset.univ.filter (fun i => i ≤ Fin.rev j), ‖(c ∘ Fin.rev) i‖ =
          ∏ i ∈ Finset.univ.filter (fun i => j ≤ i), ‖c i‖ := h2
      rw [h3, hprod] at h1
      exact hge _ h1
    · have hj0 : j.val = 0 := by
        have := j.isLt
        rw [Fin.val_rev] at hj
        omega
      have hf' : Finset.univ.filter (fun i => j ≤ i) = Finset.univ := by
        ext i
        simp [Fin.le_def, hj0]
      rw [hf', hsum]
  have he := GlobalTheory.T.antitone_weighted_sum_zero h d e (fun i => Nat.cast_pos.2 (hypos (Δ i))) hanti hsum htail
  refine ⟨h, x, hdeg, hLF, fun a t' c' hsc => ?_⟩
  have h1 := hf (Δ a) t' c' hsc
  have h2 : f (Δ a) = 0 := he a
  rw [h1, h2, mul_zero, Real.rpow_zero]

end GlobalTheory.CompanionTheory.TemperedCore
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaFourierCoefficientWeylIntegralStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_fourier_coefficient_weyl_integral : ∀ {D : D7} {t ρ : ℕ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) {θ : InfFam D} {b₀ : HermE D ρ} {μ : Measure (Mx D ρ t)} {Ω : G D t → Mx D ρ t → ℂ} (hΩ : IsTh ψ χ θ b₀ μ Ω) {nb : hermA D t → G D t} (hnb : IsNMap nb) {w : G D t} (hw : IsW w) (b : hermA D t) (y₀ : Mx D ρ t), ∫ y, ψ (trA (Matrix.trace (pr b₀ y y₀))) * conj (Ω (w * nb b) y) ∂μ = conj (ψ (halfTr (Matrix.trace (mm b.1 (pr b₀ y₀ y₀)))) * Ω 1 y₀) := by
  first | exact @GlobalTheory.CompanionTheory.RCellInv.fourier_inv | exact GlobalTheory.CompanionTheory.RCellInv.fourier_inv | (intros; apply GlobalTheory.CompanionTheory.RCellInv.fourier_inv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopologicalInfimumStatement
section
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topological_infimum : GlobalTheory.CompanionTheory.EGlue.TopInf := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.Gl0.topInf | exact GlobalTheory.CompanionTheory.EGlue.Gl0.topInf | (intros; apply GlobalTheory.CompanionTheory.EGlue.Gl0.topInf <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionNormZetaBound
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

theorem summable_absNorm_rpow_neg (K : Type) [Field K] [NumberField K] {r : ℝ} (hr : 1 < r) :
    Summable (fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-r)) := by
  have h := (GlobalTheory.Mem.summable_norm_absNorm_cpow K (s := (r : ℂ)) (by simpa using hr))
  refine h.congr fun I => ?_
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_cpow (Nat.cast_nonneg _),
    Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]

theorem sum_torsion_le (K : Type) [Field K] [NumberField K] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)) (hL : IsLat L) {r : ℝ} (hr : 1 < r)
    (S : Finset ((Fin m → K) ⧸ L)) :
    ∑ x ∈ S, (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r))
      ≤ zetaR K r := by
  classical
  set τ : (Fin m → K) ⧸ L → Ideal (𝓞 K) := fun x => Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x
    with hτ
  have hg := summable_absNorm_rpow_neg K hr
  have hfib : ∀ 𝔞 ∈ S.image τ,
      ∑ x ∈ S.filter (fun x => τ x = 𝔞), (Ideal.absNorm (τ x) : ℝ) ^ (-((m : ℝ) + r))
        ≤ (Ideal.absNorm 𝔞 : ℝ) ^ (-r) := by
    intro 𝔞 h𝔞
    obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.mp h𝔞
    have hne : τ x₀ ≠ ⊥ := GlobalTheory.T.lattice_quotient_torsion_nonzero K m L hL x₀
    obtain ⟨hfin, hcard⟩ := GlobalTheory.T.torsion_card_le_absNorm_pow K m L hL (τ x₀) hne
    have hN : (0 : ℝ) < (Ideal.absNorm (τ x₀) : ℝ) := by
      have : Ideal.absNorm (τ x₀) ≠ 0 := fun h => hne (Ideal.absNorm_eq_zero_iff.mp h)
      exact_mod_cast Nat.pos_of_ne_zero this
    have hc : ((S.filter (fun x => τ x = τ x₀)).card : ℝ) ≤ (Ideal.absNorm (τ x₀) : ℝ) ^ m := by
      have hinj : (S.filter (fun x => τ x = τ x₀)).card ≤
          Nat.card {x : (Fin m → K) ⧸ L // ∀ a ∈ τ x₀, a • x = 0} := by
        haveI := Fintype.ofFinite {x : (Fin m → K) ⧸ L // ∀ a ∈ τ x₀, a • x = 0}
        rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
        refine Fintype.card_le_of_injective (fun x => ⟨x.1, fun a ha => ?_⟩) (fun x y h => ?_)
        · have hx := (Finset.mem_filter.mp x.2).2
          rw [← hx] at ha
          exact (Ideal.mem_torsionOf_iff _ _).mp ha
        · have h' : (x : (Fin m → K) ⧸ L) = y :=
            congrArg (fun z : {x : (Fin m → K) ⧸ L // ∀ a ∈ τ x₀, a • x = 0} => z.1) h
          exact Subtype.ext h'
      exact_mod_cast hinj.trans hcard
    have hsum : ∑ x ∈ S.filter (fun x => τ x = τ x₀), (Ideal.absNorm (τ x) : ℝ) ^ (-((m : ℝ) + r))
        = ((S.filter (fun x => τ x = τ x₀)).card : ℝ) *
          (Ideal.absNorm (τ x₀) : ℝ) ^ (-((m : ℝ) + r)) := by
      rw [Finset.sum_congr rfl (g := fun _ => (Ideal.absNorm (τ x₀) : ℝ) ^ (-((m : ℝ) + r)))
        (fun x hx => by rw [(Finset.mem_filter.mp hx).2])]
      simp
    rw [hsum]
    calc _ ≤ (Ideal.absNorm (τ x₀) : ℝ) ^ m * (Ideal.absNorm (τ x₀) : ℝ) ^ (-((m : ℝ) + r)) :=
          mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hN.le _)
      _ = (Ideal.absNorm (τ x₀) : ℝ) ^ (-r) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hN]
          congr 1
          ring
  calc ∑ x ∈ S, (Ideal.absNorm (τ x) : ℝ) ^ (-((m : ℝ) + r))
      = ∑ 𝔞 ∈ S.image τ, ∑ x ∈ S.filter (fun x => τ x = 𝔞),
          (Ideal.absNorm (τ x) : ℝ) ^ (-((m : ℝ) + r)) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem τ hx) _).symm
    _ ≤ ∑ 𝔞 ∈ S.image τ, (Ideal.absNorm 𝔞 : ℝ) ^ (-r) := Finset.sum_le_sum hfib
    _ ≤ zetaR K r :=
        hg.sum_le_tsum _ (fun I _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem sum_torsion (K : Type) [Field K] [NumberField K] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)) (hL : IsLat L) (r : ℝ) (hr : 1 < r) :
    Summable (fun x : (Fin m → K) ⧸ L =>
      (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r))) ∧
    ∑' x : (Fin m → K) ⧸ L,
      (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r))
        ≤ zetaR K r := by
  have hnn : ∀ x : (Fin m → K) ⧸ L,
      0 ≤ (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r)) :=
    fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hs := summable_of_sum_le hnn (sum_torsion_le K m L hL hr)
  exact ⟨hs, hs.tsum_le_of_sum_le (sum_torsion_le K m L hL hr)⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedKernelSupDistributesSubrepsStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_kernel_sup_distributes_subreps : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → ∀ X Y : Subrepresentation ρ, (X ⊔ Y).toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) ≤ X.toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) ⊔ Y.toSubmodule ⊓ twKer ρ (unipB k (Fin N)) (whitChar ψ N) := by
  first | exact @GlobalTheory.CompanionTheory.PRep.WhitSup.sup_inf_twKer_le | exact GlobalTheory.CompanionTheory.PRep.WhitSup.sup_inf_twKer_le | (intros; apply GlobalTheory.CompanionTheory.PRep.WhitSup.sup_inf_twKer_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingBottomRowOrbitsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_bottom_row_orbits : Ad3.R.G2a := by
  first | exact @GlobalTheory.CompanionTheory.RSCoord.coord_exists | exact GlobalTheory.CompanionTheory.RSCoord.coord_exists | (intros; apply GlobalTheory.CompanionTheory.RSCoord.coord_exists <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingIntegralBottomRowStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_integral_bottom_row : Ad3.R.G2b → Ad3.R.G2c := by
  first | exact @GlobalTheory.CompanionTheory.RankinUnfold.complex_unfold_of_nonneg_unfold | exact GlobalTheory.CompanionTheory.RankinUnfold.complex_unfold_of_nonneg_unfold | (intros; apply GlobalTheory.CompanionTheory.RankinUnfold.complex_unfold_of_nonneg_unfold <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingMirabolicCosetsStatementStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_mirabolic_cosets_statement : Ad3.R.G2b := by
  first | exact @GlobalTheory.CompanionTheory.RSUnfold.unfolding_mirabolic_cosets | exact GlobalTheory.CompanionTheory.RSUnfold.unfolding_mirabolic_cosets | (intros; apply GlobalTheory.CompanionTheory.RSUnfold.unfolding_mirabolic_cosets <;> assumption)
end

