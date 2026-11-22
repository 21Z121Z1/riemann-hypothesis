import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
import Formalism.PairingDivisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0815
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0862

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationAtTransportIsometry
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.PELU

theorem unifAt_transport : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (D' D'' : PLat O bar) (t : Λ → D'.La) (t' : Λ → D''.La) P P' (y : Sp ℂ ⟶ F.X) e (w : D'.La ≃ₗ[O] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), 0 < N → UnifAt F σ ρ N D' t P y e → IsMarkedIsom N D' D'' t t' w → (∀ x, P' (w x) = h (P x)) → IsPeriod D'' ρ P' → UnifAt F σ ρ N D'' t' P' y (fun z => e (h.symm z)) := by
  intro O _ bar g ρ R _ σ Λ F N D' D'' t t' P P' y e w h hN hU hW hPP' hP'
  obtain ⟨hy, hP, hexp, hker, hact, hweil, heta⟩ := hU
  obtain ⟨hiso, hmark⟩ := hW
  have hQs : ∀ x, h.symm (P' x) = P (w.symm x) := by
    intro x
    rw [h.symm_apply_eq, ← hPP', w.apply_symm_apply]

  have hcomm : ∀ a z, h (ρ a *ᵥ z) = ρ a *ᵥ h z := by
    intro a z
    have hL : ((h.toLinearMap ∘ₗ Matrix.mulVecLin (ρ a)).restrictScalars ℝ) =
        ((Matrix.mulVecLin (ρ a) ∘ₗ h.toLinearMap).restrictScalars ℝ) := by
      apply LinearMap.ext_on hP.2.2.2.1
      rintro _ ⟨x, rfl⟩
      simp only [LinearMap.restrictScalars_apply, LinearMap.coe_comp, Function.comp_apply,
        Matrix.mulVecLin_apply, LinearEquiv.coe_coe]
      rw [← hP.1, ← hPP', ← hPP', map_smul, hP'.1]
    exact congrArg (fun f => f z) hL
  have hcomm' : ∀ a z, h.symm (ρ a *ᵥ z) = ρ a *ᵥ h.symm z := by
    intro a z
    rw [h.symm_apply_eq, hcomm, h.apply_symm_apply]
  set hc := h.symm.toContinuousLinearEquiv with hhc
  have hcc : ∀ z, hc z = h.symm z := fun z => rfl
  have hder : ∀ u v, IsDerivAt0 (fun z => (e (h.symm z)).left) u v ↔ IsDerivAt0 (fun z => (e z).left) (h.symm u) v := by
    intro u v
    unfold IsDerivAt0
    simp only [map_zero]
    refine and_congr Iff.rfl (forall_congr' fun U => forall_congr' fun hU => forall_congr' fun f => ?_)
    have key := hc.comp_right_fderiv (f := fun z => valAt' (e z).left U f) (x := 0)
    have e1 : ((fun z => valAt' (e z).left U f) ∘ hc) = (fun z => valAt' (e (h.symm z)).left U f) := rfl
    rw [e1, map_zero] at key
    rw [key]
    rfl
  refine ⟨hy, hP', ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro z z'
    simp only [map_add]
    exact hexp.1 _ _
  · exact hexp.2.1.comp h.symm.surjective
  · intro U f
    obtain ⟨ho, hd⟩ := hexp.2.2.1 U f
    have hs : {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ (e (h.symm b)).left ⁻¹ᵁ U} =
        hc ⁻¹' {b ∈ (Set.univ : Set (Fin g → ℂ)) | ⊤ ≤ (e b).left ⁻¹ᵁ U} := by
      ext b; simp [hcc]
    rw [hs]
    exact ⟨ho.preimage hc.continuous, hd.comp hc.differentiableOn (Set.mapsTo_preimage _ _)⟩
  · intro u
    obtain ⟨v, hv, huniq⟩ := hexp.2.2.2.1 (h.symm u)
    exact ⟨v, (hder u v.left).2 hv, fun v' hv' => huniq v' ((hder u v'.left).1 hv')⟩
  · intro v hv
    dsimp only at hv
    rw [map_zero] at hv
    obtain ⟨u, hu, huniq⟩ := hexp.2.2.2.2 v hv
    refine ⟨h u, (hder (h u) v.left).2 (by rwa [h.symm_apply_apply]), fun u' hu' => ?_⟩
    rw [← huniq (h.symm u') ((hder u' v.left).1 hu'), h.apply_symm_apply]
  · intro z
    rw [hker]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨w x, by rw [hPP', hx, h.apply_symm_apply]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨w.symm x, (hQs x).symm⟩
  · intro a z
    dsimp only
    rw [hcomm', hact]
  · intro k a b c hk hc'
    have h1 := hweil k (w.symm a) (w.symm b) c hk (by
      rw [hc', ← hiso (w.symm a) (w.symm b), w.apply_symm_apply, w.apply_symm_apply])
    simpa only [map_smul, hQs] using h1
  · intro a
    obtain ⟨x, hx⟩ := hmark a
    rw [heta a]
    have h1 : t' a = w (t a - N • w.symm x) := by
      rw [map_sub, map_nsmul, w.apply_symm_apply, hx, add_sub_cancel_right]
    have hN' : ((N : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have h2 : h.symm ((N : ℂ)⁻¹ • P' (t' a)) = (N : ℂ)⁻¹ • P (t a) + P (-(w.symm x)) := by
      rw [h1, hPP', map_smul, h.symm_apply_apply, map_sub, map_nsmul, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
        inv_mul_cancel₀ hN', one_smul, map_neg, sub_eq_add_neg]
    dsimp only
    rw [h2, hexp.1, (hker _).2 ⟨_, rfl⟩, _root_.mul_one]

end GlobalTheory.PELU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentDoubleCosetCellFiniteDisjointIUnion
section
open Matrix Topology

namespace GlobalTheory.JSW.Cut

open Pointwise

variable {F : Type} [NormedField F] {n : ℕ}

theorem cell_eq_of_mem (B' : Subgroup (GL (Fin n) F)) {x y g : GL (Fin n) F}
    (hx : g ∈ cell x (B' : Set (GL (Fin n) F))) (hy : g ∈ cell y (B' : Set (GL (Fin n) F))) :
    cell x (B' : Set (GL (Fin n) F)) = cell y (B' : Set (GL (Fin n) F)) := by
  obtain ⟨u, hu, k, hk, rfl⟩ := hx
  obtain ⟨u', hu', k', hk', he⟩ := hy
  have hy' : y = (u'⁻¹ * u) * x * (k * k'⁻¹) := by
    calc y = u'⁻¹ * (u' * y * k') * k'⁻¹ := by group
      _ = (u'⁻¹ * u) * x * (k * k'⁻¹) := by rw [← he]; group
  have hx' : x = (u⁻¹ * u') * y * (k' * k⁻¹) := by
    calc x = u⁻¹ * (u * x * k) * k⁻¹ := by group
      _ = (u⁻¹ * u') * y * (k' * k⁻¹) := by rw [he]; group
  ext g
  constructor
  · rintro ⟨v, hv, l, hl, rfl⟩
    refine ⟨v * (u⁻¹ * u'), mul_mem hv (mul_mem (inv_mem hu) hu'), k' * k⁻¹ * l,
      mul_mem (mul_mem hk' (inv_mem hk)) hl, ?_⟩
    rw [hx']; group
  · rintro ⟨v, hv, l, hl, rfl⟩
    refine ⟨v * (u'⁻¹ * u), mul_mem hv (mul_mem (inv_mem hu') hu), k * k'⁻¹ * l,
      mul_mem (mul_mem hk (inv_mem hk')) hl, ?_⟩
    rw [hy']; group

theorem cell_finite_disjoint_union (B B' : Subgroup (GL (Fin n) F)) (hB : IsCompact (B : Set (GL (Fin n) F)))
    (hB' : IsOpen (B' : Set (GL (Fin n) F))) (hle : B' ≤ B) (h₀ : GL (Fin n) F) :
    ∃ s : Finset (GL (Fin n) F), (∀ x ∈ s, x ∈ cell h₀ (B : Set (GL (Fin n) F))) ∧
      cell h₀ (B : Set (GL (Fin n) F)) = (⋃ x ∈ s, cell x (B' : Set (GL (Fin n) F))) ∧
      (s : Set (GL (Fin n) F)).PairwiseDisjoint fun x => cell x (B' : Set (GL (Fin n) F)) := by
  classical

  obtain ⟨t, ht⟩ := hB.elim_finite_subcover (fun b : B => (b : GL (Fin n) F) • (B' : Set (GL (Fin n) F)))
    (fun b => hB'.smul _) (fun b hb => Set.mem_iUnion.2 ⟨⟨b, hb⟩, ⟨1, one_mem _, by simp⟩⟩)
  set S : Finset (GL (Fin n) F) := t.image fun b : B => h₀ * (b : GL (Fin n) F) with hS
  have hSmem : ∀ x ∈ S, x ∈ cell h₀ (B : Set (GL (Fin n) F)) := by
    intro x hx
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨1, one_mem _, b, b.2, by simp⟩
  have hunion : cell h₀ (B : Set (GL (Fin n) F)) = ⋃ x ∈ S, cell x (B' : Set (GL (Fin n) F)) := by
    ext g
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨u, hu, k, hk, rfl⟩
      obtain ⟨b, hbt, hkb⟩ := Set.mem_iUnion₂.1 (ht hk)
      obtain ⟨k', hk', hkk⟩ := hkb
      refine ⟨h₀ * b, Finset.mem_image.2 ⟨b, hbt, rfl⟩, u, hu, k', hk', ?_⟩
      rw [← hkk]; simp [smul_eq_mul, mul_assoc]
    · rintro ⟨x, hx, u, hu, k, hk, rfl⟩
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨u, hu, b * k, mul_mem b.2 (hle hk), by simp [mul_assoc]⟩

  set f : GL (Fin n) F → Set (GL (Fin n) F) := fun x => cell x (B' : Set (GL (Fin n) F)) with hf
  set C : Finset (Set (GL (Fin n) F)) := S.image f with hC
  let rep : C → GL (Fin n) F := fun c => Classical.choose (Finset.mem_image.1 c.2)
  have rep_mem : ∀ c : C, rep c ∈ S := fun c => (Classical.choose_spec (Finset.mem_image.1 c.2)).1
  have rep_eq : ∀ c : C, f (rep c) = c := fun c => (Classical.choose_spec (Finset.mem_image.1 c.2)).2
  refine ⟨C.attach.image rep, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    exact hSmem _ (rep_mem c)
  · rw [hunion]
    ext g
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨x, hx, hg⟩
      have hc : f x ∈ C := Finset.mem_image.2 ⟨x, hx, rfl⟩
      refine ⟨rep ⟨f x, hc⟩, Finset.mem_image.2 ⟨⟨f x, hc⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
      have := rep_eq ⟨f x, hc⟩
      change g ∈ f (rep ⟨f x, hc⟩)
      rw [this]; exact hg
    · rintro ⟨x, hx, hg⟩
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨rep c, rep_mem c, hg⟩
  · intro x hx y hy hxy
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    rw [Function.onFun, Set.disjoint_left]
    intro g hgc hgd
    apply hxy
    have h1 := cell_eq_of_mem B' hgc hgd
    have hcd : c = d := by
      apply Subtype.ext
      rw [← rep_eq c, ← rep_eq d]
      exact h1
    rw [hcd]

theorem cell_finite_disjoint_union' : ∀ {F : Type} [NormedField F] {n : ℕ} (B B' : Subgroup (GL (Fin n) F)), IsCompact (B : Set (GL (Fin n) F)) → IsOpen (B' : Set (GL (Fin n) F)) → B' ≤ B → ∀ h₀ : GL (Fin n) F, ∃ s : Finset (GL (Fin n) F), (∀ x ∈ s, x ∈ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin n) F))) ∧ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin n) F)) = (⋃ x ∈ s, GlobalTheory.JSW.Cut.cell x (B' : Set (GL (Fin n) F))) ∧ (s : Set (GL (Fin n) F)).PairwiseDisjoint fun x => GlobalTheory.JSW.Cut.cell x (B' : Set (GL (Fin n) F)) :=
  fun B B' hB hB' hle h₀ => cell_finite_disjoint_union B B' hB hB' hle h₀

end GlobalTheory.JSW.Cut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValCoordOfMemHatOUnits
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.LUnit

theorem intAt_mul {l : ℕ} {a b : ℂ} (ha : IntAt l a) (hb : IntAt l b) : IntAt l (a * b) := by
  obtain ⟨n, hn, ha⟩ := ha
  obtain ⟨m, hm, hb⟩ := hb
  refine ⟨n * m, Nat.Coprime.mul_left hn hm, ?_⟩
  have e : ((n * m : ℕ) : ℂ) * (a * b) = (n * a) * (m * b) := by push_cast; ring
  rw [e]; exact ha.mul hb

theorem intAt_one (l : ℕ) : IntAt l 1 := ⟨1, Nat.coprime_one_left l, by simpa using isIntegral_one⟩

theorem unitAt_one (l : ℕ) : UnitAt l 1 := ⟨one_ne_zero, intAt_one l, by rw [inv_one]; exact intAt_one l⟩

theorem unitAt_mul {l : ℕ} {a b : ℂ} (ha : UnitAt l a) (hb : UnitAt l b) : UnitAt l (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, intAt_mul ha.2.1 hb.2.1, by rw [mul_inv]; exact intAt_mul ha.2.2 hb.2.2⟩

theorem unitAt_inv {l : ℕ} {a : ℂ} (ha : UnitAt l a) : UnitAt l a⁻¹ :=
  ⟨inv_ne_zero ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩

theorem unitAt_pow {l : ℕ} {a : ℂ} (ha : UnitAt l a) (n : ℕ) : UnitAt l (a ^ n) := by
  induction n with
  | zero => simpa using unitAt_one l
  | succ n ih => rw [pow_succ]; exact unitAt_mul ih ha

theorem unitAt_zpow {l : ℕ} {a : ℂ} (ha : UnitAt l a) (n : ℤ) : UnitAt l (a ^ n) := by
  cases n with
  | ofNat n => simpa using unitAt_pow ha n
  | negSucc n => rw [zpow_negSucc]; exact unitAt_inv (unitAt_pow ha _)

theorem unitAt_prod {l : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, UnitAt l (f i)) :
    UnitAt l (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using unitAt_one l
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact unitAt_mul (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem unitAt_neg {l : ℕ} {a : ℂ} (ha : UnitAt l a) : UnitAt l (-a) := by
  have h1 : UnitAt l (-1) := ⟨by norm_num, ⟨1, Nat.coprime_one_left l, by simpa using isIntegral_one.neg⟩,
    ⟨1, Nat.coprime_one_left l, by simpa using isIntegral_one.neg⟩⟩
  simpa using unitAt_mul h1 ha

theorem intAt_of_pow {l : ℕ} {a : ℂ} {h : ℕ} (hh : 0 < h) (ha : IntAt l (a ^ h)) : IntAt l a := by
  obtain ⟨n, hn, hi⟩ := ha
  refine ⟨n, hn, IsIntegral.of_pow hh ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  have e : ((n : ℂ) * a) ^ (k + 1) = (n : ℂ) ^ k * ((n : ℂ) * a ^ (k + 1)) := by ring
  rw [e]; exact ((isIntegral_natCast (R := ℤ) n).pow _).mul hi

theorem unitAt_of_pow {l : ℕ} {a : ℂ} {h : ℕ} (hh : 0 < h) (ha : UnitAt l (a ^ h)) : UnitAt l a :=
  ⟨fun h0 => ha.1 (by rw [h0, zero_pow hh.ne']), intAt_of_pow hh ha.2.1,
    intAt_of_pow hh (by rw [inv_pow]; exact ha.2.2)⟩

variable {E : Type} [Field E] [NumberField E]

theorem exists_coprime_mul_mem {l : ℕ} (hl : l.Prime) (α : E)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → w.valuation E α ≤ 1) :
    ∃ n : ℕ, n.Coprime l ∧ ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = n * α := by
  have hal : IsAlgebraic ℤ α :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic α)
  obtain ⟨d, hd0, hd⟩ := hal.exists_integral_multiple
  have hD0 : IsIntegral ℤ (((d.natAbs : ℤ)) • α) := by
    rcases Int.natAbs_eq d with e | e
    · rw [← e]; exact hd
    · have : (d.natAbs : ℤ) = -d := by omega
      rw [this, neg_smul]; exact hd.neg
  have hD : IsIntegral ℤ ((d.natAbs : E) * α) := by
    have : ((d.natAbs : ℤ) • α) = (d.natAbs : E) * α := by rw [zsmul_eq_mul, Int.cast_natCast]
    rw [← this]; exact hD0
  obtain ⟨e, m, hm, hDm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hd0) l hl.one_lt.ne'
  refine ⟨m, (Nat.Prime.coprime_iff_not_dvd hl).2 hm |>.symm, ?_⟩
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E _ fun w => ?_
  have hval_nat : ∀ k : ℕ, w.valuation E (k : E) ≤ 1 := fun k => by
    have : (k : E) = algebraMap (𝓞 E) E (k : 𝓞 E) := by simp
    rw [this]; exact w.valuation_le_one _
  by_cases hw : (l : 𝓞 E) ∈ w.asIdeal
  · rw [map_mul]
    exact (mul_le_mul' (hval_nat m) (h w hw)).trans_eq (one_mul _)
  · have h1 : w.valuation E ((l : E) ^ e) = 1 := by
      have : (l : E) = algebraMap (𝓞 E) E (l : 𝓞 E) := by simp
      rw [map_pow, this, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hw, one_pow]
    have h2 : w.valuation E ((d.natAbs : E) * α) ≤ 1 := by
      have : (d.natAbs : E) * α = algebraMap (𝓞 E) E ⟨_, hD⟩ := rfl
      rw [this]; exact w.valuation_le_one _
    rw [hDm] at h2
    push_cast at h2
    rw [mul_assoc, map_mul, h1, one_mul] at h2
    exact h2

theorem unitAt_embed {l : ℕ} (hl : l.Prime) (α : Eˣ)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → w.valuation E (α : E) = 1) (σ : E →+* ℂ) :
    UnitAt l (σ α) := by
  have key : ∀ x : E, (∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → w.valuation E x ≤ 1) → IntAt l (σ x) := by
    intro x hx
    obtain ⟨n, hn, b, hb⟩ := exists_coprime_mul_mem hl x hx
    refine ⟨n, hn, ?_⟩
    have : (n : ℂ) * σ x = σ.toIntAlgHom (algebraMap (𝓞 E) E b) := by
      rw [hb]; simp
    rw [this]
    exact (RingOfIntegers.isIntegral_coe b).map _
  refine ⟨by simp, key _ fun w hw => (h w hw).le, ?_⟩
  rw [← map_inv₀]
  exact key _ fun w hw => by rw [map_inv₀, h w hw, inv_one]

end GlobalTheory.CMVal.LUnit

namespace GlobalTheory.CMVal.LUnit

variable {E : Type} [Field E] [NumberField E]

theorem mul_coord' (z z' : Af E) (w : HeightOneSpectrum (𝓞 E)) : (z * z') w = z w * z' w := rfl

theorem pow_coord (z : Af E) (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) : (z ^ n) w = (z w) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, ← ih]; rfl

theorem val_coord_of_mem_hatOUnits {c : Ideal (OF E)} {u : (Af E)ˣ} (hu : u ∈ hatOUnits c) (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((u : Af E) w) = 1 := by
  have h1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (Conv.mem_integers_of_mem_hatO hu.1 w)
  have h2 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (Conv.mem_integers_of_mem_hatO hu.2 w)
  have h3 : Valued.v ((u : Af E) w) * Valued.v ((↑u⁻¹ : Af E) w) = 1 := by
    rw [← map_mul, ← mul_coord', Units.mul_inv]
    exact map_one _
  refine le_antisymm h1 ?_
  by_contra hlt
  rw [not_le] at hlt
  have h4 : Valued.v ((u : Af E) w) * Valued.v ((↑u⁻¹ : Af E) w) ≤ Valued.v ((u : Af E) w) * 1 := mul_le_mul' le_rfl h2
  rw [h3, mul_one] at h4
  exact absurd h4 (not_le.2 hlt)

theorem modF_of_mem_hatOUnits {c : Ideal (OF E)} {u : (Af E)ˣ} (hu : u ∈ hatOUnits c) : modF u = 1 := by
  unfold modF
  simp [val_coord_of_mem_hatOUnits hu]

theorem modF_pow (y : (Af E)ˣ) (n : ℕ) : modF (y ^ n) = modF y ^ n := by
  induction n with
  | zero =>
    unfold modF
    simp only [pow_zero, Units.val_one]
    exact finprod_eq_one_of_forall_eq_one fun w => by
      have : (1 : Af E) w = 1 := rfl
      rw [this, map_one]; simp
  | succ n ih => rw [pow_succ, (GlobalTheory.CMVal.modF_mul_pos_principal E).1, ih, pow_succ]

theorem unitAt_norm {l : ℕ} (hl : l.Prime) (α : Eˣ)
    (h : ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → w.valuation E (α : E) = 1) :
    UnitAt l (((|(Algebra.norm ℚ (α : E) : ℝ)| : ℝ) : ℂ)) := by
  have h1 : UnitAt l (((Algebra.norm ℚ (α : E) : ℝ) : ℂ)) := by
    have e : (((Algebra.norm ℚ (α : E) : ℝ) : ℂ)) = algebraMap ℚ ℂ (Algebra.norm ℚ (α : E)) := by simp
    rw [e, Algebra.norm_eq_prod_embeddings ℚ ℂ]
    exact unitAt_prod _ _ fun σ _ => unitAt_embed hl α h σ.toRingHom
  rcases abs_choice ((Algebra.norm ℚ (α : E) : ℝ)) with e | e
  · rw [e]; exact h1
  · rw [e, Complex.ofReal_neg]; exact unitAt_neg h1

end GlobalTheory.CMVal.LUnit

open GlobalTheory.CMVal.LUnit in

theorem GlobalTheory.CMVal.value_unitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (χ : HChar E) (l : ℕ), c ≠ ⊥ → l.Prime →
    HasInf χ φ (fun i => (κ i : ℤ) + s) → (∀ y ∈ hatOUnits c, finPart χ y = 1) → ∀ y : (Af E)ˣ,
    (∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → Valued.v ((y : Af E) w) = 1) →
    UnitAt l ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ)) := by
  intro E _ _ _ I _ φ _ s κ c χ l hc hl hinf hχ y hy
  classical
  have hfin := GlobalTheory.CMVal.PicFin.finite_picO E c hc
  have hpos : 0 < Nat.card (PicO c) := Nat.card_pos
  have hmem : y ^ Nat.card (PicO c) ∈ (princ ⊔ hatOUnits c : Subgroup (Af E)ˣ) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_card_eq_one'
  obtain ⟨p, ⟨α, rfl⟩, u, hu, hpu⟩ := Subgroup.mem_sup.1 hmem
  set h := Nat.card (PicO c)

  have hval : ∀ w : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ w.asIdeal → w.valuation E (α : E) = 1 := by
    intro w hw
    have e1 : Units.map (algebraMap E (Af E)).toMonoidHom α = y ^ h * u⁻¹ := eq_mul_inv_of_mul_eq hpu
    have e2 : Valued.v (((Units.map (algebraMap E (Af E)).toMonoidHom α : (Af E)ˣ) : Af E) w) = w.valuation E (α : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (α : E)
    rw [← e2, e1, Units.val_mul, mul_coord', Units.val_pow_eq_pow_val, pow_coord, map_mul, map_pow, hy w hw, one_pow,
      one_mul, val_coord_of_mem_hatOUnits (inv_mem hu) w]

  have hf : ((finPart χ y : ℂ)) ^ h = ((χ.inf α : ℂˣ) : ℂ)⁻¹ := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← hpu, map_mul, hχ u hu, mul_one,
      eq_inv_of_mul_eq_one_left (finPart_mul_inf χ α), Units.val_inv_eq_inv_val]
  have hm : modF y ^ h = (|(Algebra.norm ℚ (α : E) : ℝ)|)⁻¹ := by
    rw [← modF_pow, ← hpu, (GlobalTheory.CMVal.modF_mul_pos_principal E).1, modF_of_mem_hatOUnits hu, mul_one,
      (GlobalTheory.CMVal.modF_mul_pos_principal E).2.2]
  have hpow : ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ)) ^ h =
      ((χ.inf α : ℂˣ) : ℂ)⁻¹ * ((((|(Algebra.norm ℚ (α : E) : ℝ)| : ℝ) : ℂ))⁻¹) ^ s := by
    rw [mul_pow, hf, ← Complex.ofReal_pow, ← pow_mul, mul_comm s h, pow_mul, hm]
    push_cast
    ring
  refine unitAt_of_pow hpos ?_
  rw [hpow]
  refine unitAt_mul (unitAt_inv ?_) (unitAt_pow (unitAt_inv (unitAt_norm hl α hval)) s)
  rw [(hasInfRatio_iff χ φ _).1 hinf α]
  refine unitAt_prod _ _ fun i _ => unitAt_zpow (unitAt_mul (unitAt_embed hl α hval (φ i)) (unitAt_inv ?_)) _
  exact unitAt_embed hl α hval ((starRingEnd ℂ).comp (φ i))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationDerivWeierstrassPOddTorsion
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory

theorem finset_prod_eq_one_of_le_one_eq_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (f : ι → Γ) (hle : ∀ i ∈ s, f i ≤ 1)
    (hprod : ∏ i ∈ s, f i = 1) : ∀ i ∈ s, f i = 1 := by
  intro i hi
  refine le_antisymm (hle i hi) ?_
  rw [← Finset.mul_prod_erase s f hi] at hprod
  have h2 : ∏ j ∈ s.erase i, f j ≤ 1 :=
    Finset.prod_le_one' (fun j hj => hle j (Finset.mem_of_mem_erase hj))
  calc (1 : Γ) = f i * ∏ j ∈ s.erase i, f j := hprod.symm
    _ ≤ f i := mul_le_of_le_one_right' h2

theorem valuation_derivWeierstrassP_torsion_odd :
    ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 →
      V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → Odd N →
      ∀ z, z ∉ L.lattice → (N : ℂ) * z ∈ L.lattice →
        V.valuation (L.derivWeierstrassP z) = V.valuation u ^ 3 := by
  intro L β u V N hβ hβim hu hN hodd z hz hNz
  classical
  have hN0 : (N : ℂ) ≠ 0 := by
    have : N ≠ 0 := by rintro rfl; exact absurd hodd (by decide)
    exact_mod_cast this
  have hstab : MulStable L (N : ℂ) := by
    intro ω hω
    have := L.lattice.smul_mem (N : ℤ) hω
    simpa [zsmul_eq_mul] using this
  have hΔ := latticeCurve_Δ_ne_zero L
  have hvΔ : V.valuation (latticeCurve L).Δ ≠ 0 := by
    simpa using hΔ
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply hvΔ
    rw [← hu]; simp
  have hvu : V.valuation u ≠ 0 := by simpa using hu0
  obtain ⟨S, hS⟩ := kerRepsExist L (N : ℂ) hN0 hstab
  have hcard := kerRepsCard L (N : ℂ) S hN0 hstab hS
  have hcardN : S.card + 1 = N * N := by
    have : ((S.card + 1 : ℕ) : ℝ) = ((N * N : ℕ) : ℝ) := by
      push_cast; rw [hcard]; simp [Complex.normSq_apply]
    exact_mod_cast this
  have heven : Even S.card := by
    have hodd2 : Odd (N * N) := hodd.mul hodd
    rw [← hcardN] at hodd2
    obtain ⟨k, hk⟩ := hodd2
    exact ⟨k, by omega⟩
  have hpf := GlobalTheory.T.prod_derivWeierstrassP_kerReps_pow_four_mul' L (N : ℂ) S hN0 hstab hS heven
  have hmem : ∀ t ∈ S, V.valuation (L.derivWeierstrassP t / u ^ 3) ≤ 1 := by
    intro t ht
    rw [ValuationSubring.valuation_le_one_iff]
    exact (GlobalTheory.T.torsion_weierstrassP_mem_valuationSubring L β u V N hβ hβim hu hN t t (hS.1 t ht).2 (hS.1 t ht).2 (hS.1 t ht).1
      (hS.1 t ht).1).1
  have hprod : ∏ t ∈ S, V.valuation (L.derivWeierstrassP t / u ^ 3) ^ 4 = 1 := by
    have hv := congrArg V.valuation hpf
    simp only [map_mul, map_pow, map_prod, hN, one_pow, mul_one] at hv
    simp only [map_div₀, map_pow, div_pow, Finset.prod_div_distrib, Finset.prod_pow,
      Finset.prod_const, ← pow_mul]
    rw [hv, ← hu, ← pow_mul, div_eq_one_iff_eq (pow_ne_zero _ hvu)]
    ring_nf
  have hall := finset_prod_eq_one_of_le_one_eq_one S _ (fun t ht => pow_le_one' (hmem t ht) 4) hprod
  obtain ⟨t, ht, hzt⟩ := hS.2.2 z (by simpa [mul_comm] using hNz) hz
  have hper : L.derivWeierstrassP z = L.derivWeierstrassP t := by
    have := L.derivWeierstrassP_add_coe t ⟨z - t, hzt⟩
    simpa using this
  have h1 : V.valuation (L.derivWeierstrassP t / u ^ 3) = 1 := by
    have h4 := hall t ht
    by_contra hne
    have hlt : V.valuation (L.derivWeierstrassP t / u ^ 3) < 1 := lt_of_le_of_ne (hmem t ht) hne
    exact absurd h4 (ne_of_lt (pow_lt_one' hlt (by norm_num)))
  rw [hper]
  rw [map_div₀, map_pow, div_eq_one_iff_eq (pow_ne_zero _ hvu)] at h1
  exact h1
end GlobalTheory
end

