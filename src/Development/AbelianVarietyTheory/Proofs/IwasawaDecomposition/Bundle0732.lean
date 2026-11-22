import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0702
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionBarycentreCellNextStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0712
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0694
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0711
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0667
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0698
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0673
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0687
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0705
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0689
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2506
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0713
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarLabEvalZOfEqOne
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.StarLab

variable {O : Type} [CommRing O]

def IsCentreRay (w : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (B : X → X → ℝ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ ∃ β : LinearMap.BilinForm ℤ X, w.evalZ β = 1 ∧ ∀ a b, t * B a b = β a b

theorem isCentreRay_comp (w : InvFun O) {X X₁ : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] [Module.Projective O X₁] {r : X →ₗ[O] X₁}
    (hr : Function.Surjective r) (B : X₁ → X₁ → ℝ) :
    IsCentreRay w X (fun a b => B (r a) (r b)) ↔ IsCentreRay w X₁ B := by
  constructor
  · rintro ⟨t, ht, β, hw, hβ⟩
    obtain ⟨s, hs⟩ := Module.projective_lifting_property r LinearMap.id hr
    have hs' : ∀ x, r (s x) = x := fun x => LinearMap.congr_fun hs x
    refine ⟨t, ht, pull s β, ?_, fun x y => ?_⟩
    · have e : pull r (pull s β) = β := LinearMap.ext₂ fun a b => by
        have h1 := hβ (s (r a)) (s (r b))
        have h2 := hβ a b
        simp only [hs'] at h1
        simp only [pull_apply]
        exact_mod_cast h1.symm.trans h2
      rw [← evalZ_pull w hr, e, hw]
    · have := hβ (s x) (s y)
      simp only [hs'] at this
      simpa only [pull_apply] using this
  · rintro ⟨t, ht, β, hw, hβ⟩
    exact ⟨t, ht, pull r β, by rw [evalZ_pull w hr, hw], fun a b => by simp only [pull_apply, hβ]⟩

open Classical in

def starLab (lab w : InvFun O) : InvFun O where
  toFun n B := if IsCentreRay w (Fin n → O) B then -1 else Real.exp (lab.toFun n B) - 1
  inv n m r hr B := by
    simp only [isCentreRay_comp w hr B, lab.inv n m r hr B]
  zero B := by
    have : ¬ IsCentreRay w (Fin 0 → O) B := by
      rintro ⟨t, -, β, hw, -⟩
      rw [InvFun.evalZ, w.eval_of_subsingleton] at hw
      norm_num at hw
    rw [if_neg this, lab.zero, Real.exp_zero, sub_self]

open Classical in

theorem starLab_eval (lab w : InvFun O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    [Module.Projective O X] (B : X → X → ℝ) :
    (starLab lab w).eval X B = if IsCentreRay w X B then -1 else Real.exp (lab.eval X B) - 1 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [(starLab lab w).eval_eq hr, lab.eval_eq hr]
  simp only [starLab, isCentreRay_comp w hr B]

variable {X : Type} [AddCommGroup X]

open Classical in

theorem starLab_evalZ_of_eq_one (lab w : InvFun O) [Module O X] [Module.Finite O X] [Module.Projective O X]
    {β : LinearMap.BilinForm ℤ X} (h : w.evalZ β = 1) : (starLab lab w).evalZ β = -1 := by
  rw [InvFun.evalZ, starLab_eval, if_pos ⟨1, one_pos, β, h, fun a b => one_mul _⟩]

theorem starLab_evalZ_of_not (lab w : InvFun O) [Module O X] [Module.Finite O X] [Module.Projective O X]
    {β : LinearMap.BilinForm ℤ X} (h : ¬ IsCentreRay w X (fun a b => (β a b : ℝ))) :
    (starLab lab w).evalZ β = Real.exp (lab.evalZ β) - 1 := by
  rw [InvFun.evalZ, starLab_eval, if_neg h]; rfl

theorem isCentreRay_smul_iff (w : InvFun O) [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X) {k : ℕ}
    (hk : 0 < k) :
    IsCentreRay w X (fun a b => ((((k : ℤ) • β) a b : ℤ) : ℝ)) ↔ IsCentreRay w X (fun a b => (β a b : ℝ)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  constructor
  · rintro ⟨t, ht, β', hw, h⟩
    refine ⟨t * k, mul_pos ht hk', β', hw, fun a b => ?_⟩
    rw [← h a b]; simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]; ring
  · rintro ⟨t, ht, β', hw, h⟩
    refine ⟨t / k, div_pos ht hk', β', hw, fun a b => ?_⟩
    rw [← h a b]; simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]; field_simp

theorem starLab_evalZ_smul (lab w : InvFun O) [Module O X] [Module.Finite O X] [Module.Projective O X]
    (β : LinearMap.BilinForm ℤ X) {k : ℕ} (hk : 0 < k) (hlab : lab.evalZ ((k : ℤ) • β) = lab.evalZ β) :
    (starLab lab w).evalZ ((k : ℤ) • β) = (starLab lab w).evalZ β := by
  unfold InvFun.evalZ at hlab ⊢
  rw [starLab_eval, starLab_eval, hlab]
  by_cases hc : IsCentreRay w X (fun a b => (β a b : ℝ))
  · rw [if_pos ((isCentreRay_smul_iff w β hk).2 hc), if_pos hc]
  · rw [if_neg (mt (isCentreRay_smul_iff w β hk).1 hc), if_neg hc]

theorem exists_of_isCentreRay {bar : O → O} (w : InvFun O) [Module O X] [Module.Finite O X]
    {β : LinearMap.BilinForm ℤ X} (hb : β ∈ balForms bar X) (hp : ∀ y, 0 ≤ β y y)
    (h : IsCentreRay w X (fun a b => (β a b : ℝ))) :
    ∃ t : ℝ, 0 < t ∧ ∃ β' : LinearMap.BilinForm ℤ X, β' ∈ balForms bar X ∧ (∀ y, 0 ≤ β' y y) ∧ w.evalZ β' = 1 ∧
      toReal β' = t • toReal β := by
  obtain ⟨t, ht, β', hw, h⟩ := h
  simp only at h
  refine ⟨t, ht, β', ⟨fun y z => ?_, fun a y z => ?_⟩, fun y => ?_, hw, LinearMap.ext₂ fun a b => ?_⟩
  · have : (β' y z : ℝ) = β' z y := by rw [← h, ← h, hb.1 y z]
    exact_mod_cast this
  · have : (β' (a • y) z : ℝ) = β' y (bar a • z) := by rw [← h, ← h, hb.2 a y z]
    exact_mod_cast this
  · have : (0 : ℝ) ≤ β' y y := by rw [← h]; exact mul_nonneg ht.le (by exact_mod_cast hp y)
    exact_mod_cast this
  · simp [← h]

theorem InRCone.of_toReal_eq_smul {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {β β' : LinearMap.BilinForm ℤ X}
    (hβ : InRCone γ β) {t : ℝ} (ht : 0 ≤ t) (e : toReal β' = t • toReal β) : InRCone γ β' := by
  obtain ⟨c, hc, e'⟩ := hβ
  refine ⟨fun i => t * c i, fun i => mul_nonneg ht (hc i), ?_⟩
  rw [e, e', Finset.smul_sum]
  simp only [smul_smul]

theorem exists_isFaceCut {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (hh : ∀ j, 0 ≤ h (γ j)) : ∃ (m' : ℕ) (s : Fin m' ↪ Fin m), IsFaceCut γ s h := by
  classical
  let e := Fintype.equivFin {j : Fin m // h (γ j) = 0}
  refine ⟨_, e.symm.toEmbedding.trans (Function.Embedding.subtype _), hh, fun j => ⟨fun hj => ⟨e ⟨j, hj⟩, by simp⟩, ?_⟩⟩
  rintro ⟨i, rfl⟩
  exact (e.symm i).2

theorem inRCone_face {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {s : Fin m' ↪ Fin m}
    {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (hf : IsFaceCut γ s h) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone γ β)
    (h0 : h β = 0) : InRCone (fun j => γ (s j)) β := by
  classical
  obtain ⟨c, hc, e⟩ := hβ
  have h1 := apply_eq_of_toReal_eq e h
  rw [h0, Int.cast_zero] at h1
  have hz : ∀ i, c i * (h (γ i) : ℝ) = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hc i) (by exact_mod_cast hf.1 i))).1 h1.symm i
      (Finset.mem_univ _)
  have hc0 : ∀ i, i ∉ Set.range s → c i = 0 := fun i hi => by
    have hpos : (h (γ i) : ℝ) ≠ 0 := by exact_mod_cast fun h' => hi ((hf.2 i).1 h')
    exact (mul_eq_zero.1 (hz i)).resolve_right hpos
  refine ⟨fun j => c (s j), fun j => hc _, ?_⟩
  rw [e]
  have hm := Finset.sum_map Finset.univ s (fun i => c i • toReal (γ i))
  rw [← hm]
  refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_).symm
  rw [hc0 i (fun ⟨j, hj⟩ => hi (Finset.mem_map.2 ⟨j, Finset.mem_univ _, hj⟩)), zero_smul]

theorem IsFaceCut.apply_eq_zero {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {s : Fin m' ↪ Fin m}
    {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (hf : IsFaceCut γ s h) {β : LinearMap.BilinForm ℤ X}
    (hβ : InRCone (fun j => γ (s j)) β) : h β = 0 := by
  obtain ⟨c, hc, e⟩ := hβ
  have h1 := apply_eq_of_toReal_eq e h
  simp only [(hf.2 _).2 ⟨_, rfl⟩, Int.cast_zero, mul_zero, Finset.sum_const_zero] at h1
  exact_mod_cast h1

theorem inRCone_of_sub {m m' : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (s : Fin m' → Fin m)
    {β : LinearMap.BilinForm ℤ X} (hβ : InRCone (fun j => γ (s j)) β) : InRCone γ β :=
  inRCone_trans (fun j => inRCone_self γ (s j)) hβ

theorem isTwInv_starLab {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {lab w : InvFun (𝓞 E)}
    (hl : IsTwInv H lab) (hw : IsTwInv H w) : IsTwInv H (starLab lab w) := by
  intro σ hσ n B
  let e : (Fin n → 𝓞 E) ≃ₗ[ℤ] (Fin n → 𝓞 E) :=
    AddEquiv.toIntLinearEquiv (AddEquiv.piCongrRight fun _ => σ.toAddEquiv)
  have he : ∀ a, e a = fun i => σ (a i) := fun a => rfl
  have hwt : ∀ β : LinearMap.BilinForm ℤ (Fin n → 𝓞 E),
      w.evalZ (β.compl₁₂ e.toLinearMap e.toLinearMap) = w.evalZ β := fun β => by
    simp only [InvFun.evalZ, InvFun.eval_pi, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, he]
    exact hw σ hσ n (fun a b => (β a b : ℝ))
  have key : IsCentreRay w (Fin n → 𝓞 E) (fun a b => B (fun i => σ (a i)) (fun i => σ (b i))) ↔
      IsCentreRay w (Fin n → 𝓞 E) B := by
    constructor
    · rintro ⟨t, ht, β, h1, h2⟩
      refine ⟨t, ht, β.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap, ?_, fun a b => ?_⟩
      · rw [← hwt, ← h1]
        congr 1
        ext a b
        simp
      · have := h2 (e.symm a) (e.symm b)
        simp only [← he, LinearEquiv.apply_symm_apply] at this
        simpa using this
    · rintro ⟨t, ht, β, h1, h2⟩
      exact ⟨t, ht, β.compl₁₂ e.toLinearMap e.toLinearMap, by rw [hwt, h1], fun a b => by
        simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, he, h2]⟩
  have hlab := hl σ hσ n B
  simp only [starLab]
  by_cases hc : IsCentreRay w (Fin n → 𝓞 E) B
  · rw [if_pos (key.2 hc), if_pos hc]
  · rw [if_neg (mt key.1 hc), if_neg hc, hlab]

end GlobalTheory.PolFan.StarLab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarMemIntegralLattice
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.HeightCounting.Up

theorem fixedField_star_stable : PrN → AllSt fun _ _ _ _ _ _ x => ∀ y : (Dof x).LL0, star (y : (Dof x).what₂.LL) ∈ (Dof x).LL0 := by
  intro _
  refine StepW.of_all fun K B f T w _ _ _ P x y => ?_
  exact (IntermediateField.normal_iff_forall_map_le.1 B.coeffGaloisSubfield_isGalois.to_normal
    (starRingEnd (Dof x).what₂.LL).toRatAlgHom) ⟨_, y.2, rfl⟩

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionBarycentreCellNextStageStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starSubdivision_barycentre_cell_next_stage : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ lab φ' w : InvFun O) (i : ℕ) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (b a : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X) (u : Fin a → LinearMap.BilinForm ℤ X), IsCell bar ψ v → Function.Injective (fun j => lab.evalZ (u j)) → (∀ j, ((i + 1 : ℕ) : ℝ) < lab.evalZ (u j)) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ ((i + 1 : ℕ) : ℝ)) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → ¬ InRCone v β → ((i + 1 : ℕ) : ℝ) < lab.evalZ β) → (∀ (d : Fin b → ℤ) (c : Fin a → ℤ), ∑ j, c j • u j = ∑ k, d k • v k → c = 0) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℕ, lab.evalZ β = n) → (∀ (m' : ℕ) (s : Fin m' ↪ Fin b) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut v s h → IsCell bar ψ (fun j => v (s j))) → (∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → lab.evalZ β = ((i + 1 : ℕ) : ℝ) → ∃ β₁ ∈ balForms bar X, (∀ y, 0 ≤ β₁ y y) ∧ w.evalZ β₁ = 1 ∧ InRCone γ β₁) → (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms bar X, (∀ y, 0 ≤ β' y y) → w.evalZ β = 1 → w.evalZ β' = 1 → InRCone (Fin.append v u) β → InRCone (Fin.append v u) β' → β = β') → (∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β₀ → ∀ (c₀ : ℝ) (c : Fin b → ℝ), 0 < c₀ → (∀ k, 0 ≤ c k) → toReal β = c₀ • toReal β₀ + ∑ k, c k • toReal (v k) → lab.evalZ β₀ ≤ lab.evalZ β) → ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → lab.evalZ β₀ = ((i + 1 : ℕ) : ℝ) → InRCone (Fin.append v u) β₀ → (∀ (m' : ℕ) (s : Fin m' ↪ Fin (b + a)) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut (Fin.append v u) s h → 0 < h β₀ → IsCell bar φ' (Fin.cons β₀ fun j => Fin.append v u (s j))) → ∀ (m' : ℕ) (s : Fin m' ↪ Fin (b + a)) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut (Fin.append v u) s h → 0 < h β₀ → ∃ (b' a' : ℕ) (v' : Fin b' → LinearMap.BilinForm ℤ X) (u' : Fin a' → LinearMap.BilinForm ℤ X), IsCell bar φ' (Fin.append v' u') ∧ IsCell bar ψ v' ∧ (∀ k, InRCone (Fin.append v' u') ((Fin.cons β₀ fun j => Fin.append v u (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) k)) ∧ Function.Injective (fun j => lab.evalZ (u' j)) ∧ (∀ j, (i : ℝ) < lab.evalZ (u' j)) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v' β → lab.evalZ β ≤ i) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v' u') β → ¬ InRCone v' β → (i : ℝ) < lab.evalZ β) ∧ ∀ (d : Fin b' → ℤ) (c : Fin a' → ℤ), ∑ j, c j • u' j = ∑ k, d k • v' k → c = 0 := by
  first | exact @GlobalTheory.PolFan.star_cell_bary_step | exact GlobalTheory.PolFan.star_cell_bary_step | (intros; apply GlobalTheory.PolFan.star_cell_bary_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionDepthHostFixingAutInvariantStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starSubdivisionDepth_hostFixingAut_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ψ w : InvFun (𝓞 E)), IsTwInv H ψ → IsTwInv H w → IsTwInv H (starDepth H.bar ψ w) := by
  first | exact @GlobalTheory.PolFan.isTwInv_starDepth | exact GlobalTheory.PolFan.isTwInv_starDepth | (intros; apply GlobalTheory.PolFan.isTwInv_starDepth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionSubordinateToFanStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starSubdivision_subordinate_to_fan : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ w ψ' : InvFun O), IsStarOf bar q ψ w ψ' → Subordinate bar q ψ' ψ := by
  first | exact @GlobalTheory.PolFan.subordinate_of_isStarOf | exact GlobalTheory.PolFan.subordinate_of_isStarOf | (intros; apply GlobalTheory.PolFan.subordinate_of_isStarOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepsPin
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.UpPin

theorem steps_pin : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ∀ cDep : ℝ, (SettingsFormsExistList hL cDep → SettingsFormsExist hL) ∧ (SeriesExistList hL cDep → SeriesExist hL) ∧
    (ModuliPointsExistList hL cDep → SB2 hL) ∧ (StepW Start HasBare → SA hL → SMt → SRat hL → SCusp hL → SettingsFormsExistList hL cDep → SeriesExistList hL cDep →
      ModuliPointsExistList hL cDep → SC hL → SFinl hL cDep → ∀ (S : SExt) (Γ : GeoP), StepW Start (Has3 (prmR (NEl hL cDep) S Γ).s)) := by
  intro hL cDep
  refine ⟨fun h => h.trans (StepW.of_all ?_), fun h => h.trans (StepW.of_all ?_), fun h => h.trans (StepW.of_all ?_), ?_⟩
  · intro K B f T w _ _ H P x l
    obtain ⟨x', hx', -⟩ := H P x l
    exact ⟨x', hx'⟩
  · intro K B f T w _ _ H P x l
    obtain ⟨x', hx', -⟩ := H P x l
    exact ⟨x', hx'⟩
  · intro K B f T w _ _ H P x l
    obtain ⟨x', hx', -⟩ := H P x l
    exact ⟨x', hx'⟩
  · intro hB hA hMt hRat hCu hB0 hB1 hB2 hC hFin S Γ
    have h := hB.and (hA.and (hMt.and (hRat.and (hCu.and (hB0.and (hB1.and (hB2.and (hC.and hFin))))))))
    refine h.trans (StepW.of_all ?_)
    intro K B f T w _ _ H
    obtain ⟨⟨P, x, hLoc, -⟩, a, mt, rat, cu, b0, b1, b2, c, fin⟩ := H
    obtain ⟨x1, ⟨la⟩, -⟩ := a P x hLoc
    obtain ⟨imt⟩ := mt P x1
    obtain ⟨irat⟩ := rat P x1 la
    have li : LI hL x1 := { toLA := la, mt := imt, rat := irat, cusp := cu P x1 la }
    obtain ⟨x2, ⟨l0⟩, p2⟩ := b0 P x1 li
    obtain ⟨x3, ⟨l1⟩, p3⟩ := b1 P x2 l0
    obtain ⟨x4, ⟨l2⟩, p4⟩ := b2 P x3 l1
    obtain ⟨sc⟩ := c P x4 l2
    obtain ⟨Z, v, -, -⟩ := fin P x4 { toStrictHenselianAcyclic := l2, c := sc } S Γ (p4 (p3 p2))
    exact ⟨Z, ⟨v⟩⟩

end GlobalTheory.HeightCounting.UpPin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SuperadditiveOfCellsCoverConeStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.superadditive_of_cells_cover_cone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], (∀ B ∈ psdCone bar X, ∃ (e : X ≃ₗ[O] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell bar φ γ ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i)) → ∀ B ∈ psdCone bar X, ∀ B' ∈ psdCone bar X, evalR φ B + evalR φ B' ≤ evalR φ (B + B') := by
  first | exact @GlobalTheory.PolFan.CoverSuper.superadd_of_cover | exact GlobalTheory.PolFan.CoverSuper.superadd_of_cover | (intros; apply GlobalTheory.PolFan.CoverSuper.superadd_of_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaAutomorphicWeilDataPreservedDivisionLattice
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000

namespace GlobalTheory.Mem.Top.Bl.ThTTr

open Formalism.L2.Theta Formalism.L2.JoinChr
open scoped TensorProduct
open Formalism.BasicNotions.TH (tauE)

section Gen

variable {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)

theorem isAutFun_tr {V : TH.HSp D} {φ : GA D V → ℂ} :
    IsAutFun (D := D) V φ ↔ IsAutFun (D := setDiv D N h) V φ :=
  ⟨fun x => ⟨x.left, x.level, x.cont⟩, fun x => ⟨x.left, x.level, x.cont⟩⟩

theorem isAutFunSm_tr {θ : D.what₂.Tau → (GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : TH.HSp D}
    {φ : GA D V → ℂ} : IsAutFunSm (D := D) θ V φ ↔ IsAutFunSm (D := setDiv D N h) θ V φ :=
  ⟨fun x => ⟨(isAutFun_tr N h).1 x.toIsAutFun, x.smooth, x.zfin, x.growth⟩,
   fun x => ⟨(isAutFun_tr N h).2 x.toIsAutFun, x.smooth, x.zfin, x.growth⟩⟩

theorem isThetaFun_tr {ψ : AddChar (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ} {V W : TH.HSp D} {f : WA V W → ℂ} :
    IsThetaFun (D := D) ψ V W f ↔ IsThetaFun (D := setDiv D N h) ψ V W f :=
  ⟨fun x => ⟨x.quasi, x.level, x.cont, x.smooth⟩, fun x => ⟨x.quasi, x.level, x.cont, x.smooth⟩⟩

theorem isPolFock_tr {ψ : AddChar (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ}
    {θ : D.what₂.Tau → (GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V W : TH.HSp D}
    {A : ∀ τ : D.what₂.Tau, Matrix (Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2) (Fin V.rank) ℂ}
    {B : ∀ τ : D.what₂.Tau, Matrix (Fin (W.sig (tauE D τ)).1 ⊕ Fin (W.sig (tauE D τ)).2) (Fin W.rank) ℂ}
    {f : WA V W → ℂ} :
    IsPolFock (D := D) ψ θ V W A B f ↔ IsPolFock (D := setDiv D N h) ψ θ V W A B f :=
  ⟨fun ⟨J, x, rest⟩ => ⟨J, ⟨x.cont, x.real, x.sq, x.symp, x.kcomm, x.defin⟩, rest⟩,
   fun ⟨J, x, rest⟩ => ⟨J, ⟨x.cont, x.real, x.sq, x.symp, x.kcomm, x.defin⟩, rest⟩⟩

@[reducible] def besDatTr {A B : TH.HSp D} {ι : A.V →ₗ[D.host.E] B.V} (d : BesDat (D := D) A B ι) :
    BesDat (D := setDiv D N h) A B ι := { d with }

set_option maxHeartbeats 4000000 in

def thetaTiedTr {X : ThetaX D} (T : ThetaTied D X) : ThetaTied (setDiv D N h) (thTr N h X) :=
  { T with ev_aut := fun V F => (isAutFun_tr N h).1 (T.ev_aut V F) }

set_option maxHeartbeats 4000000 in

def weilTiedTr {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) :
    WeilTied (setDiv D N h) (thTr N h X) (thetaTiedTr N h T) :=
  { Wl with
    evS_range := fun V W hne => (Wl.evS_range V W hne).trans (Set.ext fun _ => isThetaFun_tr N h)
    om_tw := { Wl.om_tw with } }

set_option maxHeartbeats 4000000 in

theorem weilTiedEq_tr {X : ThetaX D} {T : ThetaTied D X} {Wl : WeilTied D X T} (e : WeilCompatibleEquivariance Wl) :
    WeilCompatibleEquivariance (weilTiedTr N h Wl) :=
  { e with
    evS_range := fun V W hr => (e.evS_range V W hr).trans (Set.ext fun _ => isThetaFun_tr N h)
    om_tw := { e.om_tw with } }

set_option maxHeartbeats 4000000 in

def allTiedTr {X : ThetaX D} {A : TH.ProvA} (a : AllTied D X A) : AllTied (setDiv D N h) (thTr N h X) A where
  T := thetaTiedTr N h a.T
  sm := ⟨a.sm.1, fun θ hθ V hV => (a.sm.2 θ hθ V hV).trans (Set.ext fun _ => isAutFunSm_tr N h)⟩
  ty := { a.ty with }
  W := weilTiedTr N h a.W
  unr := a.unr
  kf := { a.kf with
    kfin := ⟨a.kf.kfin.1, fun θ hθ V W h1 h2 h3 Φ => (a.kf.kfin.2 θ hθ V W h1 h2 h3 Φ).trans (isPolFock_tr N h)⟩ }
  phiUp := a.phiUp
  B := { a.B with dat := fun A B ι ho p => besDatTr N h (a.B.dat A B ι ho p) }
  real := { a.real with }
  prov := { a.prov with }

end Gen

end GlobalTheory.Mem.Top.Bl.ThTTr

open GlobalTheory.Mem.Top.Bl.ThTTr in
set_option maxHeartbeats 16000000 in

theorem GlobalTheory.Mem.Top.Bl.ThTTr.thT_setDiv : ∀ {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) {Wt : Set B.places.Pl} {nch : NChoice (w.D Z)} (n : NchT w Z Wt nch) (th : ThetaX (w.D Z)) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), ThT n th → Nonempty (ThT (nchTTr w Z N h n) (thTr (D := w.D Z) N h th)) := by
  intro B f T w Z Wt nch n th N h t
  exact ⟨{ provA := t.provA
           all := allTiedTr (D := w.D Z) N h t.all
           weq := weilTiedEq_tr (D := w.D Z) N h t.weq
           chr := { t.chr with }
           same := { t.same with }
           std := t.std
           io := t.io }⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaScaledThreeValue
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.RayHoriz GlobalTheory.RayRos GlobalTheory.RayRosEx
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RayRosEx.ThetaPull

section Jets

variable {S : Type} [CommRing S] {ρ : Type}

end Jets

section Vals

theorem val_comp_stalkMap {X Y Z W : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (κ : W ⟶ Z) (r : Z ⟶ Y) {w : W} {J : (W ⟶ X) → L.ι} (hJ : Good L w J) :
    Units.map (κ.stalkMap w).hom.toMonoidHom (val t r (κ w) fun ψ => J (κ ≫ ψ)) = val t (κ ≫ r) w J := by
  rw [val_of t (κ ≫ r) w J (fun k => J (κ ≫ r ≫ φ k)) fun k => by rw [Category.assoc]]
  have h : r (κ w) ∈ LB.wchart L φ fun k => J (κ ≫ r ≫ φ k) := Set.mem_iInter.2 fun k => hJ (κ ≫ r ≫ φ k)
  exact Units.ext ((congrArg (κ.stalkMap w).hom (gm_val r (κ w) _ h _)).trans
    ((Scheme.Hom.germ_stalkMap_apply κ (r ⁻¹ᵁ (LB.wchart L φ fun k => J (κ ≫ r ≫ φ k))) w h _).trans
      (gm_val (κ ≫ r) w _ h _).symm))

end Vals

end GlobalTheory.RayRosEx.ThetaPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricChartsPolarizedModel
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.FanTheta

theorem isLB_detOm_of_smooth {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) (hpq : 1 ≤ D.p + D.q)
    (hsm : SmoothOfRelativeDimension D.dim (genStr Y)) : (GlobalTheory.FlagMod.detOm Y).IsLB := by
  have e : spMap (RingHom.id c.F) = 𝟙 _ := by
    simp [spMap]
  haveI : IsIso (spMap (RingHom.id c.F)) := by rw [e]; infer_instance
  haveI : IsIso (genι Y) := inferInstance
  have hs : SmoothOfRelativeDimension D.dim Y.s := by
    have hw : Y.s = inv (genι Y) ≫ genStr Y ≫ spMap (RingHom.id c.F) := by
      rw [← pullback.condition, IsIso.inv_hom_id_assoc]
    rw [hw]
    have := (inferInstance :
      SmoothOfRelativeDimension (0 + (D.dim + 0)) (inv (genι Y) ≫ genStr Y ≫ spMap (RingHom.id c.F)))
    simpa using this
  have hθ : GlobalTheory.Models.HasTheta Y.t.G Y.t.PP.L := GlobalTheory.T.hasFibrewiseNonvanishingThetaSection_of_smooth_model E H D hpq l Xo c Y hs
  exact GlobalTheory.FlagMod.isLB_detOm (GlobalTheory.CompHS.TorFlagEx.pushInvertible_of_hasTheta Y hθ)

theorem isLB_detOm : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (φ : InvFun (𝓞 E)) (Y : Model Xo c (RingHom.id c.F)) (BD : GlobalTheory.EffCartierData Y.X) (d : ℕ), 1 ≤ D.p + D.q → SmoothOfRelativeDimension D.dim (genStr Y) → FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Y.t.G) → (∀ x ∈ genBd Y, GlobalTheory.MumfordChart.HasChartOf φ Y BD d x) → (GlobalTheory.FlagMod.detOm Y).IsLB := by
  intro E _ _ _ H D l Xo c _ Y _ _ hpq hsm _ _ _
  exact isLB_detOm_of_smooth Y hpq hsm

end GlobalTheory.FanTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCoordSquaresCorrespondStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_coord_squares_correspond' : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ β : D'.toPre.X, D'.toPre.c (2 • β) ≫ Φ.hom = D.toPre.c (xe (2 • β)) → ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val ((U.gt e).t (xe (2 • β))) r z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ D'.toPre.Oφ (U'.gt e).pG (2 • β) κ) ^ Oinvε κ) * val ((U'.gt e).t (2 • β)) r z J' ^ 2 := by
  first | exact @GlobalTheory.torus_coord_squares_correspond | exact GlobalTheory.torus_coord_squares_correspond | (intros; apply GlobalTheory.torus_coord_squares_correspond <;> assumption)
end

