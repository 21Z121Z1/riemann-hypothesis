import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1600
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1629
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1621
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3664
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1659
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2659
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3655
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2624
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2655
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3657
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3658
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3663
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3665
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3659
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3207
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2793
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2518
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3378
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0594
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3410
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3463

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRhoPartDeformationDim
section
noncomputable section

namespace GlobalTheory.HTRho
open Module

def trAct {k O X X' : Type*} [Field k] [Ring O] [AddCommGroup X] [Module k X] [AddCommGroup X'] [Module k X']
    (e : X ≃ₗ[k] X') (σ : O →+* Module.End k X) : O →+* Module.End k X' where
  toFun a := e.toLinearMap ∘ₗ σ a ∘ₗ e.symm.toLinearMap
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

theorem trAct_apply {k O X X' : Type*} [Field k] [Ring O] [AddCommGroup X] [Module k X] [AddCommGroup X']
    [Module k X'] (e : X ≃ₗ[k] X') (σ : O →+* Module.End k X) (a : O) (x : X') :
    trAct e σ a x = e (σ a (e.symm x)) := rfl

theorem finrank_homO_trAct {k O X Y X' Y' : Type*} [Field k] [Ring O] [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] [AddCommGroup X'] [Module k X'] [AddCommGroup Y'] [Module k Y']
    (eX : X ≃ₗ[k] X') (eY : Y ≃ₗ[k] Y') (σX : O →+* Module.End k X) (σY : O →+* Module.End k Y) :
    finrank k (homO σX σY) = finrank k (homO (trAct eX σX) (trAct eY σY)) := by
  have h : (homO σX σY).map (LinearEquiv.arrowCongr eX eY).toLinearMap = homO (trAct eX σX) (trAct eY σY) := by
    ext T'
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, mem_homO, mem_homO]
    simp only [LinearEquiv.coe_coe, LinearEquiv.arrowCongr_symm_apply, LinearMap.comp_apply, trAct_apply]
    constructor
    · intro hT a x
      have := congrArg eY (hT a (eX.symm x))
      simpa using this
    · intro hT a x
      have := hT a (eX x)
      rw [LinearEquiv.symm_apply_apply] at this
      rw [this, LinearEquiv.symm_apply_apply]
  rw [← h, LinearEquiv.finrank_map_eq]

end GlobalTheory.HTRho

namespace GlobalTheory.HTRho
open Module GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

universe v
variable {k O C : Type*} {H : Type v} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C] [Algebra C O]

theorem finrank_ks_map_cls [FiniteDimensional k H] (σ : O →+* Module.End k H) (G Z : Submodule k H)
    (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) (hZ : ∀ a, ∀ x ∈ Z, σ a x ∈ Z) (hZG : Z ≤ G) :
    finrank k ((ksSub σ 0 G Z).map (cls G)) =
      finrank k (homO (qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx)) (qAct σ G hG)) := GlobalTheory.T.finrank_ksSub_map_cls_eq_finrank_homO σ G Z hG hZ hZG

theorem finrank_homO_crt {ι W V : Type*} [Fintype ι] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (σW : O →+* Module.End k W) (τ : O →+* Module.End k V)
    (χ : ι → C →+* k) (hχ : Function.Injective χ) (hJ : jSub τ χ ⊤ = ⊥) :
    finrank k (homO σW τ) =
      ∑ i, finrank k (homO σW (qAct τ (mSub τ (χ i) ⊤) (mSub_stable τ (χ i) ⊤ (fun _ _ _ => trivial)))) := GlobalTheory.T.characterAugmentationSubspace_quotientAction_top σW τ χ hχ hJ

theorem finrank_homO_quot {W V : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (σW : O →+* Module.End k W) (τ : O →+* Module.End k V)
    (χ : C →+* k) (hτ : ∀ c, τ (algebraMap C O c) = χ c • 1) :
    finrank k (homO σW τ) =
      finrank k (homO (qAct σW (mSub σW χ ⊤) (mSub_stable σW χ ⊤ (fun _ _ _ => trivial))) τ) := GlobalTheory.T.finrank_homO_eq_augmentationQuotient_of_scalar_character σW τ χ hτ

theorem quot_facts {ι : Type*} (σ : O →+* Module.End k H) (G : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G)
    (χ : ι → C →+* k) :
    (jSub σ χ ⊤ ≤ G → jSub (qAct σ G hG) χ ⊤ = ⊥) ∧
    ∀ i, finrank k ((H ⧸ G) ⧸ mSub (qAct σ G hG) (χ i) ⊤) = finrank k (H ⧸ (G ⊔ mSub σ (χ i) ⊤)) := GlobalTheory.T.finrank_equivariantHom_eq_augmentation_quotient σ G hG χ

theorem finrank_sub_quot {ι : Type*} [Fintype ι] [FiniteDimensional k H] (σ : O →+* Module.End k H)
    (χ : ι → C →+* k) (hχ : Function.Injective χ) (Fil : Submodule k H) (hFil : ∀ a, ∀ x ∈ Fil, σ a x ∈ Fil)
    (ω : C) (r₀ r₁ : k) (hr : r₀ ≠ r₁)
    (hω : (σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1) = 0) (hχω : ∀ i, χ i ω = r₀)
    (hG : ∀ a, ∀ x ∈ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1),
      σ a x ∈ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1))
    (hZ : ∀ a, ∀ x ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)),
      σ a x ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)))
    (hJ : jSub σ χ ⊤ ≤ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1)) (i : ι) :
    let G := Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1)
    let Z := jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1))
    let σW := qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx)
    finrank k ((G ⧸ Z.comap G.subtype) ⧸ mSub σW (χ i) ⊤) + finrank k (H ⧸ (G ⊔ mSub σ (χ i) ⊤)) =
      finrank k (H ⧸ mSub σ (χ i) ⊤) := GlobalTheory.T.finrank_ksSub_quotient_augmentation_of_two_roots σ χ hχ Fil hFil ω r₀ r₁ hr hω hχω hG hZ hJ i

theorem count {ι : Type*} [Fintype ι] [FiniteDimensional k H] (σ : O →+* Module.End k H)
    (χ : ι → C →+* k) (hχ : Function.Injective χ) (Fil : Submodule k H) (hFil : ∀ a, ∀ x ∈ Fil, σ a x ∈ Fil)
    (ω : C) (r₀ r₁ : k) (hr : r₀ ≠ r₁)
    (hω : (σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1) = 0) (hχω : ∀ i, χ i ω = r₀)
    (m n : ℕ) (hm : 0 < m)
    (hrank : ∀ i, finrank k (H ⧸ mSub σ (χ i) ⊤) = m * n)
    (hJ : jSub σ χ ⊤ ≤ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1))
    (hlie : ∀ i, finrank k (H ⧸ ((Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1)) ⊔ mSub σ (χ i) ⊤)) = m)
    (hmor : ∀ i (X Y : Type v) [AddCommGroup X] [Module k X] [FiniteDimensional k X] [AddCommGroup Y] [Module k Y]
      [FiniteDimensional k Y] (σX : O →+* Module.End k X) (σY : O →+* Module.End k Y),
      (∀ c, σX (algebraMap C O c) = χ i c • 1) → (∀ c, σY (algebraMap C O c) = χ i c • 1) →
      m ^ 2 * finrank k (homO σX σY) = finrank k X * finrank k Y) :
    KSDim σ 0 (Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1))
      (jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1))) (Fintype.card ι * (n - 1)) := by
  set G := Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1) with hGdef
  set Z := jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)) with hZdef
  have hωc : ∀ a, σ a * σ (algebraMap C O ω) = σ (algebraMap C O ω) * σ a := fun a => by
    rw [← map_mul, ← map_mul, Algebra.commutes]
  have hRst : ∀ r : k, ∀ a, ∀ x ∈ LinearMap.range (σ (algebraMap C O ω) - r • 1),
      σ a x ∈ LinearMap.range (σ (algebraMap C O ω) - r • 1) := by
    rintro r a _ ⟨y, rfl⟩
    refine ⟨σ a y, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul]
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, hωc]
  have hG : ∀ a, ∀ x ∈ G, σ a x ∈ G := by
    intro a x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact add_mem (Submodule.mem_sup_left (hFil a y hy)) (Submodule.mem_sup_right (hRst r₀ a z hz))
  have hZ : ∀ a, ∀ x ∈ Z, σ a x ∈ Z := jSub_stable σ χ _ (hRst r₁)
  have hZG : Z ≤ G := le_trans (Submodule.span_mono (by
    rintro z ⟨r, lam, c, x, -, hc, rfl⟩; exact ⟨r, lam, c, x, trivial, hc, rfl⟩)) hJ
  have key := GlobalTheory.UPel.Sm.KSCount.ksDim_finrank σ 0 G Z
  rw [finrank_ks_map_cls σ G Z hG hZ hZG] at key
  convert key using 1
  obtain ⟨hF1, hF2⟩ := quot_facts σ G hG χ
  rw [finrank_homO_crt _ _ χ hχ (hF1 hJ)]
  rw [← Finset.card_univ, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finrank_homO_quot _ _ (χ i) (qAct_mSub_algebraMap _ (χ i))]
  have hD := finrank_sub_quot σ χ hχ Fil hFil ω r₀ r₁ hr hω hχω hG hZ hJ i
  have hM := hmor i ((G ⧸ Z.comap G.subtype) ⧸ mSub (qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx)) (χ i) ⊤)
    ((H ⧸ G) ⧸ mSub (qAct σ G hG) (χ i) ⊤) _ _ (qAct_mSub_algebraMap _ (χ i)) (qAct_mSub_algebraMap _ (χ i))
  rw [hF2 i, hlie i] at hM
  simp only at hD
  rw [hlie i, hrank i] at hD
  have h1 := Nat.eq_sub_of_add_eq hD
  rw [h1, ← Nat.mul_sub_one] at hM
  rw [show m * (n - 1) * m = m ^ 2 * (n - 1) by ring] at hM
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) hM).symm

end GlobalTheory.HTRho

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTRho

theorem rhoCount : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → KSDim (GlobalTheory.HTCount.crysAct o₀) 0 (Fil o₀.A ⊔ LinearMap.range (GlobalTheory.HTCount.crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1)) (GlobalTheory.HTCount.lieZ o₀ β) (D.a * (D.n - 1)) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β hβ
  obtain ⟨hFree, hHodge, -, -, -⟩ := GlobalTheory.T.abelianScheme_firstDeRham_structure
  have hA := o₀.ab
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o₀.A hA
  obtain ⟨hfd, -, -⟩ := GlobalTheory.T.finrank_firstDeRhamHomology_hodgeFiltration_of_field hFree hHodge k o₀.A g hA hg
  have hunit : ∀ n : ℕ, n.Coprime p → IsUnit (n : k) := fun n hn => by
    simpa using (b.unit n hn).map β
  set σ := GlobalTheory.HTCount.crysAct o₀ with hσ
  set χ : Fin D.a → (𝓞 D.F →+* k) := fun i => β.comp (b.t i) with hχdef
  have hχ : Function.Injective χ := by
    intro i j hij
    by_contra hne
    have h1 := b.comax i j hne
    have hle : Ideal.span (Set.range fun x => b.t i x - b.t j x) ≤ RingHom.ker β := by
      rw [Ideal.span_le]
      rintro _ ⟨x, rfl⟩
      have := congrArg (fun f : 𝓞 D.F →+* k => f x) hij
      simp only [χ, RingHom.comp_apply] at this
      simp [RingHom.mem_ker, this]
    have h1' : (1 : R) ∈ RingHom.ker β := hle (by rw [h1]; trivial)
    simp at h1'
  have hFil : ∀ a, ∀ x ∈ Fil o₀.A, σ a x ∈ Fil o₀.A := fun a x hx => by
    haveI := o₀.act.hom a
    rw [hσ, GlobalTheory.HTCount.crysAct_apply]
    exact push_mem_Fil _ hx
  have hχω : ∀ i, χ i D.ω = β b.ρ := fun i => by simp [χ, b.t_ω]
  have hchar : ∀ n : ℕ, n.Coprime p → (n : k) ≠ 0 := fun n hn => (hunit n hn).ne_zero
  have hρk : β b.ρ ^ 2 - (D.tr : k) * β b.ρ + (D.nm : k) = 0 := by
    have := congrArg β b.ρ_root
    simpa using this
  have hr : β b.ρ ≠ (D.tr : k) - β b.ρ := by
    intro h
    have hd : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) = 0 := by
      push_cast
      linear_combination (-(D.tr : k) + 2 * β b.ρ) * h - 4 * hρk
    have hp : (p : ℕ).Prime := Fact.out
    have hcop : (D.tr ^ 2 - 4 * D.nm).natAbs.Coprime p := by
      refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hdv => D.disc_p ?_)
      exact Int.natCast_dvd.2 hdv
    apply hchar _ hcop
    have hm := congrArg (Int.cast : ℤ → k) (Int.natAbs_mul_self' (D.tr ^ 2 - 4 * D.nm))
    rw [Int.cast_mul, Int.cast_mul, hd, mul_zero, Int.cast_natCast] at hm
    exact mul_self_eq_zero.1 hm
  have hω : (σ (algebraMap (𝓞 D.F) D.O D.ω) - β b.ρ • 1) * (σ (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : k) - β b.ρ) • 1) = 0 := by
    have e1 : D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
      rw [← D.tr_eq, ← D.nm_eq]; ring
    have e2 : σ (algebraMap (𝓞 D.F) D.O (D.ω * D.ω - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F))) = 0 := by
      rw [e1]; simp
    simp only [map_add, map_sub, map_mul, map_intCast] at e2
    refine LinearMap.ext fun x => ?_
    have e3 := congrArg (fun T => T x) e2
    simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at e3
    simp only [Module.End.intCast_apply, ← Int.cast_smul_eq_zsmul k] at e3
    simp only [LinearMap.smul_apply, Module.End.one_apply, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.zero_apply, map_sub, map_smul]
    set w := σ (algebraMap (𝓞 D.F) D.O D.ω)
    have : β b.ρ * ((D.tr : k) - β b.ρ) = D.nm := by linear_combination -hρk
    linear_combination (norm := module) e3 - hρk • x
  have hS2 := GlobalTheory.T.harrisTaylor_rho_part_lie_deRham_quotient p D R b N ‹_› ‹_› k t o₀ β hβ
  have key := count σ χ hχ (Fil o₀.A) hFil D.ω (β b.ρ) ((D.tr : k) - β b.ρ) hr hω hχω D.m D.n D.m_pos
    (GlobalTheory.T.harrisTaylor_finrank_deRham_quotient_character p D R b N ‹_› ‹_› k t o₀ β hβ) hS2.1 hS2.2
    (fun i X Y _ _ _ _ _ _ σX σY hX hY => by
      let eX := (Module.finBasis k X).equivFun
      let eY := (Module.finBasis k Y).equivFun
      rw [finrank_homO_trAct eX eY σX σY]
      have := GlobalTheory.T.finrank_hom_harrisTaylorOrder_morita p D k hchar (χ i) _ _ (trAct eX σX) (trAct eY σY)
        (fun c => LinearMap.ext fun x => by rw [trAct_apply, hX]; simp) (fun c => LinearMap.ext fun x => by rw [trAct_apply, hY]; simp)
      rwa [← eX.finrank_eq, ← eY.finrank_eq] at this)
  rw [Fintype.card_fin] at key
  exact key

end GlobalTheory.HTRho
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeTjIsogeniesRepresentable
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.IsogRep

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

theorem exists_comp {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁}
    {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
    ∃ m : ObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

theorem exists_factor (hN : 3 ≤ N) (hNp : N.Coprime p) {S₀ S₁ T : Scheme.{0}} {s₀ : S₀ ⟶ Sp R} {s₁ : S₁ ⟶ Sp R}
    {t : T ⟶ Sp R} {o₀ : Obj b N s₀} {o₁ : Obj b N s₁} {o : Obj b N t} {g : S₁ ⟶ S₀} {h : T ⟶ S₁} {x : T ⟶ S₀}
    (e : h ≫ g = x) (m₁ : ObjMap o₁ o₀ g) (m : ObjMap o o₀ x) : ∃ m' : ObjMap o o₁ h, m'.φ ≫ m₁.φ = m.φ := by
  subst e
  obtain ⟨m'⟩ := GlobalTheory.T.harrisTaylorPullback_comp_factors p D R b N _ _ _ _ _ _ o₀ o₁ o g h m₁ m
  obtain ⟨n, hn⟩ := exists_comp m' m₁
  exact ⟨m', hn.symm.trans (GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique_of_base_eq p D R b N hN hNp _ _ _ _ _ _ _ _ n m rfl)⟩

theorem exists_pull {S S' : Scheme.{0}} {s : S ⟶ Sp R} (f : S' ⟶ S) (o : Obj b N s) {s' : S' ⟶ Sp R}
    (e : f ≫ s = s') : ∃ o' : Obj b N s', Nonempty (ObjMap o' o f) := by
  subst e
  exact GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N S S' s f o

theorem isUnit_pow {S : Scheme.{0}} (s : S ⟶ Sp R) (hp : IsUnit ((p : ℕ) : R)) {c : ℕ} (hc : ∃ e : ℕ, c = p ^ e) :
    IsUnit (c : Γ(S, ⊤)) := by
  obtain ⟨e, rfl⟩ := hc
  have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  rwa [← Nat.cast_pow, map_natCast] at this

theorem exists_obj {c : ℕ} {Y : Scheme.{0}} [IsLocallyNoetherian Y] {s : Y ⟶ Sp R} (o : Obj b N s) (B : Over Y)
    [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A) (hp : IsUnit ((p : ℕ) : R)) (hc : ∃ e : ℕ, c = p ^ e)
    (hB : IsAbelianScheme B) (hq : IsQuasiInv c ψ ψ') (h1 : KerStableAt o ψ (𝟙 Y)) (h2 : PolKerAt o ψ' c (𝟙 Y)) :
    ∃ (o' : Obj b N s) (χ : o.A ⟶ o'.A) (θ : o'.A.left ⟶ B.left), IsPIsog c o o' χ ∧
      IsGrpPullback o'.A B (𝟙 Y) θ ∧ ψ.left = χ.left ≫ θ := by
  obtain ⟨act', hact⟩ := GlobalTheory.T.exists_orderAction_descent_along_isogeny p D R b N c Y s o B ψ ψ' hp hc hB hq h1
  obtain ⟨P', hP', w1, w2⟩ := GlobalTheory.T.exists_polarization_descent_of_quasi_isogeny p D R b N c Y s o B ψ ψ' hp hc hB hq h2
  have hlie := GlobalTheory.T.harrisTaylor_lie_of_quasiInverseIsogeny p D R b N c Y s o B ψ ψ' hp hc hB hq act' hact
  haveI := hq.1
  let o' : Obj b N s :=
    { A := B, ab := hB, act := act', P := P', isLB := hP'.1, rig₁ := hP'.2.1, rig₂ := hP'.2.2
      symm := GlobalTheory.T.quasiInverse_root_bundle_symmetric p D R b N c Y s o B ψ ψ' hp hc hB hq P' hP' w1 w2
      ample := GlobalTheory.T.relAmple_diag_root_pullback_quasiInverse p D R b N c Y s o B ψ ψ' hp hc hB hq P' hP' w1 w2
      kerP := GlobalTheory.T.polarization_descent_along_quasi_isogeny_compat p D R b N c Y s o B ψ ψ' hp hc hB hq h2 P' hP' w1 w2
      rosati := GlobalTheory.T.quasiInverse_root_bundle_rosati_descended_action p D R b N c Y s o B ψ ψ' hp hc hB hq P' hP' w1 w2 act' hact
      lie := hlie.1, lieRank := hlie.2
      eta := fun y => o.eta y ≫ ψ
      eta_add := fun x y => by rw [o.eta_add, MonObj.mul_comp]
      eta_lin := fun a x => by rw [o.eta_lin, Category.assoc, hact, Category.assoc]
      eta_ker := fun x => by rw [o.eta_ker, MonObj.one_comp]
      geom := GlobalTheory.T.pow_polarization_iso_pullback_of_descent p D R b N c Y s o B ψ ψ' hp hc hB hq P' hP' w1 w2 act' hact }
  exact ⟨o', ψ, 𝟙 _, ⟨hc, hq.1, hact, fun _ => rfl, ⟨w2⟩, ψ', hq.2.1, hq.2.2.1, hq.2.2.2⟩,
    GlobalTheory.SiegLower.isGrpPullback_id B, (Category.comp_id _).symm⟩

end

theorem exists_rep : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Over S) (o₀ : Obj b N (Y.hom ≫ s)) (m₀ : ObjMap o₀ o Y.hom) (o' : Obj b N (Y.hom ≫ s)) (ψ : o₀.A ⟶ o'.A), IsFinite Y.hom ∧ Etale Y.hom ∧ IsPIsog c o₀ o' ψ ∧ IsTj r w j o₀ o' ψ ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (o₁ o₁' : Obj b N (x ≫ s)) (m : ObjMap o₁ o x) (ψ₁ : o₁.A ⟶ o₁'.A), IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : T ⟶ Y.left, y ≫ Y.hom = x ∧ ∃ (m₀' : ObjMap o₁ o₀ y) (m₁ : ObjMap o₁' o' y), m₀'.φ ≫ ψ.left = ψ₁.left ≫ m₁.φ := by
  intro p _ D R _ _ b N hN hNp hp r w j c _ _ _ hc0 _ S _ s o
  have hc : ∃ e : ℕ, c = p ^ e := hc0.imp fun _ h => h.1
  have hcpos : 0 < c := by
    obtain ⟨e, rfl⟩ := hc
    exact pow_pos (Fact.out : p.Prime).pos e
  obtain ⟨Z, hZf, hZe, hZ⟩ := GlobalTheory.T.isogeny_representable_finite_etale S o.A c o.ab hcpos (isUnit_pow s hp hc)
  obtain ⟨oZ, ⟨mZ⟩⟩ := exists_pull Z.hom o rfl
  obtain ⟨B, _, _, ψ, ψ', hB, hq, huniv⟩ := hZ oZ.A mZ.φ mZ.cart
  obtain ⟨W₁, a₁, c₁, H₁⟩ := GlobalTheory.T.exists_clopen_kernelStable_harrisTaylor p D R b N c _ _ oZ B ψ ψ' hp hc hB hq
  obtain ⟨W₂, a₂, c₂, H₂⟩ := GlobalTheory.T.harrisTaylor_pullback_kernel_locus_isClopen p D R b N c _ _ oZ B ψ ψ' hp hc hB hq
  obtain ⟨W₃, a₃, c₃, H₃⟩ := GlobalTheory.T.exists_clopen_locus_of_annihilator p D R b N c _ _ oZ B ψ ψ' hp hc hB hq r w j
  haveI := hZf
  haveI := hZe
  obtain ⟨Y, i, hYf, hYe, hmono, Hi⟩ := GlobalTheory.LevCover.exists_sub (Z := Z)
    ⟨W₁ ∩ W₂ ∩ W₃, (a₁.inter a₂).inter a₃⟩ ((c₁.inter c₂).inter c₃)
  haveI := hYf
  haveI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have hi : Set.range i.left.base ⊆ W₁ ∩ W₂ ∩ W₃ := (Hi Y i).2 ⟨𝟙 Y, Category.id_comp i⟩
  obtain ⟨o₀, ⟨mi⟩⟩ := exists_pull i.left oZ (s' := Y.hom ≫ s) (by rw [← Category.assoc, Over.w i])
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ObjMap o₀ o Y.hom, m₀.φ = mi.φ ≫ mZ.φ := by
    have H : ∀ g, i.left ≫ Z.hom = g → ∃ m₀ : ObjMap o₀ o g, m₀.φ = mi.φ ≫ mZ.φ := by
      rintro _ rfl
      exact exists_comp mi mZ
    exact H _ (Over.w i)
  obtain ⟨B₀, _, _, θ₀, ψ₀, ψ₀', hB₀, hθ₀, hq₀, e₀, e₀'⟩ :=
    GlobalTheory.T.quasiInverseIsogenyPair_baseChange_grpPullback _ _ i.left oZ.A B c ψ ψ' o₀.A mi.φ hB hq mi.cart
  obtain ⟨o', χ, θ₁, hχ, hθ₁, e₁⟩ := exists_obj o₀ B₀ ψ₀ ψ₀' hp hc hB₀ hq₀
    ((GlobalTheory.T.kernelStable_iff_pulledBack_identity p D R b N _ _ _ _ _ o₀ oZ mi B₀ B θ₀ ψ₀ ψ hθ₀ e₀).1 ((H₁ _ _).1 fun z hz => (hi hz).1.1))
    ((GlobalTheory.T.polKerAt_pullback_of_isGrpPullback p D R b N _ _ _ _ _ o₀ oZ mi B₀ B θ₀ ψ₀' ψ' c hθ₀ e₀').1 ((H₂ _ _).1 fun z hz => (hi hz).1.2))
  have hθ : IsGrpPullback o'.A B i.left (θ₁ ≫ θ₀) := (hθ₁.comp hθ₀).congr (Category.id_comp _) rfl
  have eχ : mi.φ ≫ ψ.left = χ.left ≫ θ₁ ≫ θ₀ := by rw [e₀, e₁, Category.assoc]
  have htj : IsTj r w j o₀ o' χ := (tjAt_id_iff r w j o₀ o' χ).1
    ((GlobalTheory.T.harrisTaylorType_iff_pulledBack_identity p D R b N _ _ _ _ _ o₀ oZ mi o'.A B (θ₁ ≫ θ₀) χ ψ r w j hθ eχ).1
      ((H₃ _ _).1 fun z hz => (hi hz).2))
  refine ⟨Y, o₀, m₀, o', χ, hYf, hYe, hχ, htj, fun T x o₁ o₁' m ψ₁ h1 h2 => ?_⟩
  obtain ⟨ψ₁', hq₁⟩ := h1.exists_quasiInv
  obtain ⟨z, ⟨hz, θ, θ', eθ, hθa, hθb, eψ⟩, zu⟩ := huniv T x o₁.A m.φ o₁'.A ψ₁ ψ₁' m.cart o₁'.ab hq₁
  obtain ⟨mz, hmz⟩ := exists_factor hN hNp hz mZ m
  obtain rfl : θ = mz.φ := mZ.cart.1.hom_ext (eθ.trans hmz.symm) (hθa.1.w.trans mz.cart.1.w.symm)
  have eψ' := GlobalTheory.T.quasiInverseIsogeny_square_compat_comp_quasiInv _ _ z oZ.A B c ψ ψ' o₁.A o₁'.A mz.φ θ' ψ₁ ψ₁' o₁'.ab hcpos hq hq₁ mz.cart eψ
  have hr : Set.range z.base ⊆ W₁ ∩ W₂ ∩ W₃ := Set.subset_inter (Set.subset_inter
    ((H₁ _ z).2 ((GlobalTheory.T.kernelStable_iff_pulledBack_identity p D R b N _ _ _ _ _ o₁ oZ mz o₁'.A B θ' ψ₁ ψ hθb eψ).2 (h1.kerStableAt _)))
    ((H₂ _ z).2 ((GlobalTheory.T.polKerAt_pullback_of_isGrpPullback p D R b N _ _ _ _ _ o₁ oZ mz o₁'.A B θ' ψ₁' ψ' c hθb eψ').2
      (GlobalTheory.T.polarization_kernel_of_p_isogeny_quasi_inverse p D R b N c _ _ o₁ o₁' ψ₁ ψ₁' hp h1 hq₁))))
    ((H₃ _ z).2 ((GlobalTheory.T.harrisTaylorType_iff_pulledBack_identity p D R b N _ _ _ _ _ o₁ oZ mz o₁'.A B θ' ψ₁ ψ r w j hθb eψ).2
      ((tjAt_id_iff r w j o₁ o₁' ψ₁).2 h2)))
  obtain ⟨y, hy⟩ := (Hi (Over.mk x) (Over.homMk z hz)).1 hr
  have hyz : y.left ≫ i.left = z := congrArg CommaMorphism.left hy
  haveI : Mono i.left := inferInstanceAs (Mono ((Over.forget S).map i))
  refine ⟨y.left, ⟨Over.w y, ?_⟩, ?_⟩
  · obtain ⟨m₀', hm⟩ := exists_factor hN hNp hyz mi mz
    let φ₁ : o₁'.A.left ⟶ o'.A.left := hθ.1.lift θ' (o₁'.A.hom ≫ y.left) (by rw [hθb.1.w, Category.assoc, hyz])
    have f1 : φ₁ ≫ θ₁ ≫ θ₀ = θ' := hθ.1.lift_fst _ _ _
    have f2 : φ₁ ≫ o'.A.hom = o₁'.A.hom ≫ y.left := hθ.1.lift_snd _ _ _
    have hφ₁ : IsGrpPullback o₁'.A o'.A y.left φ₁ := hθ.cancel (hθb.congr hyz.symm f1.symm) f2
    have e : m₀'.φ ≫ χ.left = ψ₁.left ≫ φ₁ := by
      apply hθ.1.hom_ext
      · rw [Category.assoc, ← eχ, ← Category.assoc, hm, eψ, Category.assoc, f1]
      · rw [Category.assoc, Over.w χ, m₀'.cart.1.w, Category.assoc, f2, ← Category.assoc, Over.w ψ₁]
    obtain ⟨m₁, hm₁⟩ := GlobalTheory.T.exists_objMap_of_p_isogeny_pullback p D R b N c _ _ _ _ y.left o₁ o₁' o₀ o' m₀' ψ₁ χ φ₁ hp h1 hχ hφ₁ e
    exact ⟨m₀', m₁, by rw [hm₁, e]⟩
  · rintro y' ⟨hy', n₀, n₁, e⟩
    rw [← cancel_mono i.left, hyz]
    have hx : (y' ≫ i.left) ≫ Z.hom = x := by rw [Category.assoc, Over.w i, hy']
    obtain ⟨n, hn⟩ := exists_comp n₀ mi
    obtain ⟨n', hn'⟩ := exists_comp n mZ
    refine zu _ ⟨hx, n₀.φ ≫ mi.φ, n₁.φ ≫ θ₁ ≫ θ₀, ?_, n₀.cart.comp mi.cart, n₁.cart.comp hθ, ?_⟩
    · rw [← hn, ← hn']
      exact GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique_of_base_eq p D R b N hN hNp _ _ _ _ _ _ _ _ n' m hx
    · rw [Category.assoc, eχ, ← Category.assoc, e, Category.assoc]

end GlobalTheory.UPel.HT.ES.IsogRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatSymbolMemMaximalIdealOfKodairaSpencerZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KSZeroMod

theorem intDer {A : Type} [CommRing A] (inst : Algebra ℤ A) (D : @Derivation ℤ A A _ _ _ inst _ _) :
    ∃ D' : @Derivation ℤ A A _ _ _ (Ring.toIntAlgebra A) _ _, ⇑D' = ⇑D := by
  obtain rfl : inst = Ring.toIntAlgebra A := Subsingleton.elim _ _
  exact ⟨D, rfl⟩

theorem exists_basis_isKS_symbol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vY : Module.Basis (Fin n) (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vY a) (dd a)) → ∀ D : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ i, D (bdParam k m d i) ∈ Ideal.span {bdParam k m d i}) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∃ v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) ∧ (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) ∧ IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) (h.Θ.map (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab Y n vY dd hdd D hD h hb hdef
  letI := H.starRing
  haveI : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  haveI : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) :=
    GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _
  have hne : ∀ i, bdParam k m d i ≠ 0 := fun i h => by
    have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i) 1)) h
    simp [MvPowerSeries.coeff_X] at this
  choose v' hv' using fun a => GlobalTheory.ChartKSBracket.tanPt E H (ChartRing k m d) t P Y (vY a)
  obtain ⟨b, hbv⟩ := GlobalTheory.T.uniformisedTangentBasis_of_raynaudBasis E H (ChartRing k m d) t P Y n vY v' hv'
  have hx : spMap (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom ≫ 𝟙 (Sp (ChartRing k m d)) =
      chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) := by
    rw [Category.comp_id, chart, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    rfl
  obtain ⟨b', hb'⟩ := GlobalTheory.TotalFrame.exists_basis_map b _ hx
  have ev : (fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom) ≫ (tv (v' a)).left) =
      fun a => (tv (b' a)).left := funext fun a => by rw [hb', hbv]
  refine ⟨fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom) ≫ (tv (v' a)).left,
    fun a => GlobalTheory.ChartKSBracket.isTanAtG_tv E H _ t (v' a), fun w hw => ?_, ?_⟩
  · rw [ev]
    refine ⟨b'.repr (GlobalTheory.LieMet.tanOf hw), (GlobalTheory.LieMet.isComb_iff _ _ (GlobalTheory.LieMet.tanOf hw)).2 (b'.sum_repr _).symm,
      fun a ha => ?_⟩
    rw [(GlobalTheory.LieMet.isComb_iff _ _ (GlobalTheory.LieMet.tanOf hw)).1 ha, Module.Basis.repr_sum_self]
  · obtain ⟨D', hD'⟩ := intDer _ D
    revert h
    rw [← hD']
    intro h hb hdef
    exact GlobalTheory.T.kodairaSpencer_of_commuting_heat_operators_raynaud E H (ChartRing k m d) t P m (bdParam k m d) gam hmon hne hab Y n vY dd hdd v' hv' D' h hb hdef

set_option maxHeartbeats 1600000 in

theorem symbol_mem_maximalIdeal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∀ Θ, IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ → (∀ a b, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (Θ a b) ∈ maximalIdeal (ChartRing k m d)) → ∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab n v hv hcomb Y n' v' dd hdd D q hq h hb hdef Θ hΘ hm
  letI := H.starRing
  have hD : ∀ i, D (bdParam k m d i) ∈ Ideal.span {bdParam k m d i} := fun i => by
    rw [hq i]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  obtain ⟨w, hw, hwb, hks⟩ := exists_basis_isKS_symbol E H k m d t P gam hmon hli hab Y n' v' dd hdd D hD h hb hdef
  choose C hC using fun c => (hwb (v c) (hv c)).exists
  have hks' := GlobalTheory.KSFrameChange.isKS_frame_change E H (Sp (ChartRing k m d)) t
    ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i)))
    (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) n n' v w (Matrix.of C)
    (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ hv hw hC hΘ
  have heq := GlobalTheory.T.kodairaSpencer_matrix_unique_over_chart_abelian_locus E H k m d t P gam hmon hli hab n' w hw hwb D _ _ hks' hks
  intro a b
  have e := congrArg (fun M => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (M a b)) heq
  simp only [Matrix.map_apply, Iso.inv_hom_id_apply] at e
  rw [← e, Matrix.mul_apply, map_sum]
  refine Ideal.sum_mem _ fun c _ => ?_
  rw [map_mul, Matrix.mul_apply, map_sum, Finset.sum_mul]
  refine Ideal.sum_mem _ fun e' _ => ?_
  rw [map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (hm e' c))

end GlobalTheory.KSZeroMod
end
end

