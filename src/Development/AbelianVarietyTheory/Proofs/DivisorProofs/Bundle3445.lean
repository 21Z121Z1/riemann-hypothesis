import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0693
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2893
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2917
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3425
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3421
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3426
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3414
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3418
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2348
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3413
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeastIntCombinationMinimiserCellUnitary
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc.FinTypes

theorem single : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], IsPolFanOn bar φ Y → ∀ (n N : ℕ) [NeZero N], 3 ≤ N → Odd N → ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → ∀ b₀ ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b₀ x x) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b₀ (μ cl) (μ cl) ≤ b₀ α α) → ∃ (ι : ℕ) (L : Finset ((Fin n → ZMod N) → ℤ)), 1 ≤ ι ∧ ∀ b' ∈ balForms bar Y, (∀ x, 0 ≤ b' x x) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) → (∀ ν ∈ L, (ι : ℝ) * φ.evalZ b' ≤ ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl)) ∧ ∃ ν ∈ L, (ι : ℝ) * φ.evalZ b' = ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl) := by
  classical
  intro O _ bar φ Y _ _ _ _ hY n N _ hN3 hNo eb μ hμ b₀ hb₀ hpos hmin
  obtain ⟨p, m, γ, hcone, hcov⟩ := GlobalTheory.T.exists_finite_cones_polarized_fan_level_structure O bar φ Y hY n N hN3 eb μ hμ b₀ hb₀ hpos hmin
  obtain ⟨Nℓ, ℓ, hNℓ, hℓ⟩ := GlobalTheory.T.exists_invFun_eq_min_intLinearForms_on_cones O bar φ Y p m γ hcone
  choose D ν hD hν using fun i : Fin p => GlobalTheory.T.linForm_symmBilin_eq_sum_lifts_odd Y n N hN3 hNo eb μ hμ (ℓ i)
  obtain ⟨E, hDE⟩ : ∃ E : Fin p → ℕ, ∀ i, D i * E i = ∏ j, D j :=
    ⟨fun i => ∏ j ∈ Finset.univ.erase i, D j, fun i => Finset.mul_prod_erase _ _ (Finset.mem_univ i)⟩
  have hDp : 0 < ∏ j, D j := Finset.prod_pos (fun j _ => hD j)
  refine ⟨Nℓ * ∏ j, D j, Finset.univ.image (fun i c => (E i : ℤ) * ν i c), ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hNℓ.ne' hDp.ne')
  intro b' hb' hp hm
  have hcv := hcov b' hb' hp hm
  obtain ⟨hle, i1, heq⟩ := hℓ b' hb' hp hcv
  have key : ∀ i, ∑ c, (((E i : ℤ) * ν i c : ℤ) : ℝ) * ((b' (μ c) (μ c) : ℤ) : ℝ)
      = ((E i : ℝ) * (D i : ℝ)) * ((ℓ i b' : ℤ) : ℝ) := by
    intro i
    have h' : (((∑ c, ν i c * b' (μ c) (μ c) : ℤ)) : ℝ) = (((D i : ℤ) * ℓ i b' : ℤ) : ℝ) := by
      rw [hν i b' hb'.1]
    push_cast at h' ⊢
    calc ∑ c, (E i : ℝ) * (ν i c : ℝ) * (b' (μ c) (μ c) : ℝ)
        = (E i : ℝ) * ∑ c, (ν i c : ℝ) * (b' (μ c) (μ c) : ℝ) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun c _ => ?_); ring
      _ = _ := by rw [h']; ring
  have hι : ∀ i, ((Nℓ * ∏ j, D j : ℕ) : ℝ) = ((E i : ℝ) * (D i : ℝ)) * (Nℓ : ℝ) := by
    intro i; rw [← hDE i]; push_cast; ring
  refine ⟨fun ν' hν' => ?_, ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hν'
    have hc : (0 : ℝ) ≤ (E i : ℝ) * (D i : ℝ) := by positivity
    calc ((Nℓ * ∏ j, D j : ℕ) : ℝ) * φ.evalZ b'
        = ((E i : ℝ) * (D i : ℝ)) * ((Nℓ : ℝ) * φ.evalZ b') := by rw [hι i]; ring
      _ ≤ ((E i : ℝ) * (D i : ℝ)) * ((ℓ i b' : ℤ) : ℝ) := mul_le_mul_of_nonneg_left (hle i) hc
      _ = _ := (key i).symm
  · refine ⟨_, Finset.mem_image.mpr ⟨i1, Finset.mem_univ _, rfl⟩, ?_⟩
    calc ((Nℓ * ∏ j, D j : ℕ) : ℝ) * φ.evalZ b'
        = ((E i1 : ℝ) * (D i1 : ℝ)) * ((Nℓ : ℝ) * φ.evalZ b') := by rw [hι i1]; ring
      _ = ((E i1 : ℝ) * (D i1 : ℝ)) * ((ℓ i1 b' : ℤ) : ℝ) := by rw [heq]
      _ = _ := (key i1).symm

theorem P1 : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y], IsPolFanOn bar φ Y → ∀ (n N : ℕ) [NeZero N], 3 ≤ N → Odd N → ∀ (ebY : Y ≃ₗ[ℤ] (Fin n → ℤ)), ∃ (ι : ℕ) (𝓛₀ : Finset (Finset ((Fin n → ZMod N) → ℤ))), 1 ≤ ι ∧ ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (ebX : X ≃ₗ[ℤ] (Fin n → ℤ)) (f : X ≃ₗ[O] Y), ∀ b ∈ balForms bar X, (∀ x, x ≠ 0 → 0 < b x x) → ∀ μ : (Fin n → ZMod N) → X, (∀ cl i, ((ebX (μ cl) i : ℤ) : ZMod N) = cl i) → (∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → ∃ L ∈ 𝓛₀, ∀ b' ∈ balForms bar X, (∀ x, 0 ≤ b' x x) → (∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) → (∀ ν ∈ L, (ι : ℝ) * φ.evalZ b' ≤ ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl)) ∧ ∃ ν ∈ L, (ι : ℝ) * φ.evalZ b' = ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl) := by
  classical
  intro O _ bar φ Y _ _ _ _ hY n N _ hN3 hNo ebY
  obtain ⟨S, hS⟩ := GlobalTheory.T.finite_minimiser_systems_balanced_forms_upto_aut O bar φ Y hY n N hN3 ebY
  have hP : ∀ μ' : (Fin n → ZMod N) → Y,
      ((∀ cl i, ((ebY (μ' cl) i : ℤ) : ZMod N) = cl i) ∧ ∃ b₀ ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b₀ x x) ∧
        (∀ cl (α : Y), (∀ i, ((ebY α i : ℤ) : ZMod N) = cl i) → b₀ (μ' cl) (μ' cl) ≤ b₀ α α)) →
      ∃ (ι : ℕ) (L : Finset ((Fin n → ZMod N) → ℤ)), 1 ≤ ι ∧ ∀ b' ∈ balForms bar Y, (∀ x, 0 ≤ b' x x) →
        (∀ cl (α : Y), (∀ i, ((ebY α i : ℤ) : ZMod N) = cl i) → b' (μ' cl) (μ' cl) ≤ b' α α) →
        (∀ ν ∈ L, (ι : ℝ) * φ.evalZ b' ≤ ∑ cl, (ν cl : ℝ) * b' (μ' cl) (μ' cl)) ∧
          ∃ ν ∈ L, (ι : ℝ) * φ.evalZ b' = ∑ cl, (ν cl : ℝ) * b' (μ' cl) (μ' cl) :=
    fun μ' ⟨h1, b₀, hb₀, h2, h3⟩ => single O bar φ Y hY n N hN3 hNo ebY μ' h1 b₀ hb₀ h2 h3
  choose! ιf Lf hιf hLf using hP
  set ι : ℕ := ∏ μ' ∈ S, max (ιf μ') 1 with hιdef
  refine ⟨ι, S.biUnion fun μ' => Finset.univ.image fun σ : Equiv.Perm (Fin n → ZMod N) =>
    (Lf μ').image fun ν c => ((ι / ιf μ' : ℕ) : ℤ) * ν (σ c), ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun _ _ => by omega)
  intro X _ _ _ ebX f b hb hbp μ hμ hmin
  have hbY : pull f.symm.toLinearMap b ∈ balForms bar Y := pull_mem _ hb
  have hbYp : ∀ x, x ≠ 0 → 0 < pull f.symm.toLinearMap b x x := fun x hx => by
    simpa using hbp (f.symm x) (by simpa using hx)
  obtain ⟨e, he⟩ := hS _ hbY hbYp
  set g : Y ≃ₗ[O] X := e.trans f.symm with hg
  obtain ⟨σ, hσ1, hσ2⟩ := GlobalTheory.T.transport_classMinimisers_along_linearEquiv O Y X n N ebY ebX g μ hμ
  set μ' : (Fin n → ZMod N) → Y := fun c => g.symm (μ (σ c)) with hμ'
  have hpull : ∀ β : LinearMap.BilinForm ℤ X, pull e.toLinearMap (pull f.symm.toLinearMap β) = pull g.toLinearMap β :=
    fun β => LinearMap.ext₂ fun x y => rfl
  have hmem : μ' ∈ S := he μ' hσ1 (by rw [hpull]; exact hσ2 b hmin)
  have hgb : pull g.toLinearMap b ∈ balForms bar Y := pull_mem _ hb
  have hgp : ∀ x, x ≠ 0 → 0 < pull g.toLinearMap b x x := fun x hx => by
    simpa using hbp (g x) (by simpa using hx)
  have hPμ : (∀ cl i, ((ebY (μ' cl) i : ℤ) : ZMod N) = cl i) ∧ ∃ b₀ ∈ balForms bar Y, (∀ x, x ≠ 0 → 0 < b₀ x x) ∧
        (∀ cl (α : Y), (∀ i, ((ebY α i : ℤ) : ZMod N) = cl i) → b₀ (μ' cl) (μ' cl) ≤ b₀ α α) :=
    ⟨hσ1, _, hgb, hgp, hσ2 b hmin⟩
  have hι1 := hιf _ hPμ
  have hL := hLf _ hPμ
  have hdvd : ιf μ' ∣ ι := by
    have := Finset.dvd_prod_of_mem (fun μ'' => max (ιf μ'') 1) hmem
    simpa [max_eq_left hι1] using this
  set k : ℕ := ι / ιf μ' with hk
  have hkι : (ι : ℝ) = k * ιf μ' := by exact_mod_cast (Nat.div_mul_cancel hdvd).symm
  refine ⟨(Lf μ').image fun ν c => ((k : ℕ) : ℤ) * ν (σ.symm c),
    Finset.mem_biUnion.2 ⟨μ', hmem, Finset.mem_image.2 ⟨σ.symm, Finset.mem_univ _, rfl⟩⟩, ?_⟩
  intro b' hb' hb'p hb'min
  have key := hL (pull g.toLinearMap b') (pull_mem _ hb') (fun x => hb'p _) (hσ2 b' hb'min)
  have hφ' : φ.evalZ (pull g.toLinearMap b') = φ.evalZ b' := evalZ_pull φ g.surjective b'
  have hq : ∀ c, pull g.toLinearMap b' (μ' c) (μ' c) = b' (μ (σ c)) (μ (σ c)) := fun c => by
    simp [μ']
  have hsum : ∀ ν : (Fin n → ZMod N) → ℤ,
      ∑ c, ((((k : ℕ) : ℤ) * ν (σ.symm c) : ℤ) : ℝ) * b' (μ c) (μ c) =
        k * ∑ c, (ν c : ℝ) * pull g.toLinearMap b' (μ' c) (μ' c) := fun ν => by
    rw [Finset.mul_sum, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hq]; simp; ring
  have hlhs : (ι : ℝ) * φ.evalZ b' = k * ((ιf μ' : ℝ) * φ.evalZ (pull g.toLinearMap b')) := by
    rw [hφ', hkι]; ring
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  refine ⟨fun ν' hν' => ?_, ?_⟩
  · obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hν'
    rw [hsum, hlhs]
    exact mul_le_mul_of_nonneg_left (key.1 ν hν) hk0
  · obtain ⟨ν, hν, heq⟩ := key.2
    exact ⟨_, Finset.mem_image_of_mem _ hν, by rw [hsum, hlhs, heq]⟩

end GlobalTheory.UPoinc.FinTypes

theorem GlobalTheory.UPoinc.finite_types_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ : InvFun (𝓞 E)), IsPolFan H.bar q φ → ∀ (N : ℕ) [NeZero N], 3 ≤ N → Odd N → ∃ (B ι : ℕ) (𝓛 : ∀ n : ℕ, Finset (Finset ((Fin n → ZMod N) → ℤ))), 1 ≤ ι ∧ ∀ (n : ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (eb : X ≃ₗ[ℤ] (Fin n → ℤ)), n < B ∧ ∀ (b : LinearMap.BilinForm ℤ X), b ∈ balForms H.bar X → (∀ y, y ≠ 0 → 0 < b y y) → ∀ μ : (Fin n → ZMod N) → X, (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → ∃ L ∈ 𝓛 n, ∀ b' : LinearMap.BilinForm ℤ X, b' ∈ balForms H.bar X → (∀ y, 0 ≤ b' y y) → (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) → (∀ ν ∈ L, (ι : ℝ) * φ.evalZ b' ≤ ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl)) ∧ ∃ ν ∈ L, (ι : ℝ) * φ.evalZ b' = ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl) := by
  intro E _ _ _ H q φ hφ N _ hN3 hNo
  classical
  obtain ⟨R, Y, hY⟩ := GlobalTheory.ProjModFinIso.finitely_many_iso_classes E q
  set B : ℕ := Module.finrank ℚ E * q + 1 with hB
  have hP : ∀ (n : ℕ) (k : Fin R), ∃ (ι : ℕ) (𝓛₀ : Finset (Finset ((Fin n → ZMod N) → ℤ))), 1 ≤ ι ∧
      ((Module.Finite (𝓞 E) (Y k) ∧ Module.Projective (𝓞 E) (Y k) ∧ Module.finrank (𝓞 E) (Y k) ≤ q ∧
        Nonempty (Y k ≃ₗ[ℤ] (Fin n → ℤ))) →
      ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (ebX : X ≃ₗ[ℤ] (Fin n → ℤ))
        (f : X ≃ₗ[𝓞 E] Y k), ∀ b ∈ balForms H.bar X, (∀ x, x ≠ 0 → 0 < b x x) → ∀ μ : (Fin n → ZMod N) → X,
        (∀ cl i, ((ebX (μ cl) i : ℤ) : ZMod N) = cl i) →
        (∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) →
        ∃ L ∈ 𝓛₀, ∀ b' ∈ balForms H.bar X, (∀ x, 0 ≤ b' x x) →
          (∀ cl (α : X), (∀ i, ((ebX α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) →
          (∀ ν ∈ L, (ι : ℝ) * φ.evalZ b' ≤ ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl)) ∧
            ∃ ν ∈ L, (ι : ℝ) * φ.evalZ b' = ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl)) := by
    intro n k
    by_cases hC : Module.Finite (𝓞 E) (Y k) ∧ Module.Projective (𝓞 E) (Y k) ∧ Module.finrank (𝓞 E) (Y k) ≤ q ∧
        Nonempty (Y k ≃ₗ[ℤ] (Fin n → ℤ))
    · obtain ⟨h1, h2, h3, ⟨ebY⟩⟩ := hC
      obtain ⟨ι, 𝓛₀, hι, h⟩ := GlobalTheory.UPoinc.FinTypes.P1 (𝓞 E) H.bar φ (Y k) (hφ (Y k) h3) n N hN3 hNo ebY
      exact ⟨ι, 𝓛₀, hι, fun _ => h⟩
    · exact ⟨1, ∅, le_rfl, fun h => (hC h).elim⟩
  choose ιf 𝓛f hιf h𝓛f using hP
  set ι : ℕ := ∏ n ∈ Finset.range B, ∏ k, ιf n k with hιdef
  have hιpos : 0 < ι := Finset.prod_pos fun n _ => Finset.prod_pos fun k _ => hιf n k
  refine ⟨B, ι, fun n => Finset.univ.biUnion fun k =>
    (𝓛f n k).image fun L => L.image fun ν c => ((ι / ιf n k : ℕ) : ℤ) * ν c, hιpos, ?_⟩
  intro n X _ _ _ _ hXq eb
  obtain ⟨hfinZ, -, hrk⟩ := GlobalTheory.finite_projective_int_of_ringOfIntegers E X
  have hn : Module.finrank ℤ X = n := by rw [eb.finrank_eq, Module.finrank_fin_fun]
  have hnB : n < B := by
    rw [hB, ← hn, hrk]
    have := Nat.mul_le_mul_left (Module.finrank ℚ E) hXq
    omega
  refine ⟨hnB, ?_⟩
  intro b hb hbp μ hμ hmin
  obtain ⟨k, ⟨f⟩⟩ := hY X hXq
  haveI h1 : Module.Finite (𝓞 E) (Y k) := Module.Finite.equiv f
  haveI h2 : Module.Projective (𝓞 E) (Y k) := Module.Projective.of_equiv f
  have h3 : Module.finrank (𝓞 E) (Y k) ≤ q := f.finrank_eq ▸ hXq
  have h4 : Nonempty (Y k ≃ₗ[ℤ] (Fin n → ℤ)) := ⟨f.symm.toAddEquiv.toIntLinearEquiv.trans eb⟩
  obtain ⟨L, hL, hLb⟩ := h𝓛f n k ⟨h1, h2, h3, h4⟩ X eb f b hb hbp μ hμ hmin
  have hdvd : ιf n k ∣ ι := by
    have h5 : ∏ k, ιf n k ∣ ι := Finset.dvd_prod_of_mem (fun n => ∏ k, ιf n k) (Finset.mem_range.2 hnB)
    exact (Finset.dvd_prod_of_mem (fun k => ιf n k) (Finset.mem_univ k)).trans h5
  set c : ℕ := ι / ιf n k with hc
  have hcι : (ι : ℝ) = c * ιf n k := by exact_mod_cast (Nat.div_mul_cancel hdvd).symm
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  refine ⟨L.image fun ν cl => ((c : ℕ) : ℤ) * ν cl,
    Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, Finset.mem_image.2 ⟨L, hL, rfl⟩⟩, ?_⟩
  intro b' hb' hb'p hb'min
  obtain ⟨hle, ν₀, hν₀, heq⟩ := hLb b' hb' hb'p hb'min
  have hsum : ∀ ν : (Fin n → ZMod N) → ℤ, ∑ cl, ((((c : ℕ) : ℤ) * ν cl : ℤ) : ℝ) * b' (μ cl) (μ cl) =
      c * ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl) := fun ν => by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun cl _ => ?_; push_cast; ring
  have hlhs : (ι : ℝ) * φ.evalZ b' = c * ((ιf n k : ℝ) * φ.evalZ b') := by rw [hcι]; ring
  refine ⟨fun ν' hν' => ?_, ⟨_, Finset.mem_image_of_mem _ hν₀, by rw [hsum, hlhs, heq]⟩⟩
  obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hν'
  rw [hsum, hlhs]
  exact mul_le_mul_of_nonneg_left (hle ν hν) hc0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSliceTrivialOfWeilPairingOneTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilKernel

theorem triv_slice_of_forall_weilIs_one : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (n : ℕ), (n : k) ≠ 0 → ∀ a : Over.mk x ⟶ A, a ^ n = 1 → (∀ b : Over.mk x ⟶ A, b ^ n = 1 → Out.WeilIs (G2 A) P (n : ℤ) (lift a 1) (lift 1 b) 1) → (∃ t : (P.pull (lift (snd A (Over.mk x) ≫ a) (fst A (Over.mk x))).left).Gen, t.IsGen) := by
  intro S A _ _ P hA hL h1 h2 k _ _ p n hn a ha hpair
  have hB : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have ht2 : Triv (AbDual.ev P (𝟙 A) (1 : A ⟶ A)) := h2
  obtain ⟨r, hr⟩ : Triv (P.pull (eSec (A ⊗ A))) := by
    have e := (AbDual.triv_ev_iff hL _ _).2 (AbDual.evc_one_right hL ht2 (1 : 𝟙_ (Over S) ⟶ A))
    have e' : lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A) = η[A ⊗ A] := by
      ext <;> simp [Hom.one_def]
    rw [AbDual.ev, e'] at e
    exact e
  obtain ⟨t, ht⟩ := WeilIntegral.triv_theta CubeTop.cubeTheorem hB hL
  obtain ⟨t', ht', hn'⟩ := AbLaw.Cube.exists_normalised hL t ht
  let M : RigLB (A ⊗ A) := ⟨P, r, hL, hr⟩
  have c : CubicalStr (A ⊗ A) M := AbLaw.Cube.cubicalOfNormalised globalFns_holds hB M t' ht' hn'
  have ha' : (lift a (1 : Over.mk p ⟶ A)) ^ n = 1 := WeilIntegral.lift_pow ha (one_pow n)

  have s1 : ∀ b : Over.mk p ⟶ A, b ^ n = 1 → CubWeil c n (lift a 1) (lift 1 b) 1 := fun b hb =>
    (cubWeil_iff_weilIs (c := c) globalFns_holds hB ha' (WeilIntegral.lift_pow (one_pow n) hb) 1).2 (hpair b hb)

  have s2 : ∀ b : Over.mk p ⟶ A, b ^ n = 1 → CubWeil c n (lift b 1) (lift a 1) 1 := by
    intro b hb
    have h := RaynaudAxis.cubWeil_one_of_triv_pull S (A ⊗ A) A (lift (𝟙 A) 1) hA inferInstance M c h2 n
      (Over.mk p) b a hb ha
    simpa using h

  have s3 : ∀ z : Over.mk p ⟶ A ⊗ A, z ^ n = 1 → CubWeil c n (lift a 1) z 1 := by
    intro z hz
    have e : lift (z ≫ fst A A) 1 * lift 1 (z ≫ snd A A) = z := by
      ext <;> simp [MonObj.mul_comp]
    have hz1 : (z ≫ fst A A) ^ n = 1 := by rw [← MonObj.pow_comp, hz]; simp
    have hz2 : (z ≫ snd A A) ^ n = 1 := by rw [← MonObj.pow_comp, hz]; simp
    have h := ((s2 _ hz1).mul_left (s1 _ hz2).symm).symm
    rw [e] at h
    simpa using h

  have ht := OrthKer.mem_kernel_of_cubWeil_orthogonal k S p (A ⊗ A) hB M c n hn (lift a 1) ha' s3
  have hD : (translDiff (A ⊗ A) P (lift a 1)).IsLB := LB.isLB_linComb hL _ _
  have h0 : CechPic.cls _ hD = 0 := (CechPic.cls_eq_zero_iff hD).2 ht

  have e := AbDual.pull_translDiff hL (lift a 1) hD (snd A (Over.mk p)) (lift 1 (fst A (Over.mk p)))
  rw [h0, map_zero] at e
  have k1 : (snd A (Over.mk p) ≫ lift a 1) * lift 1 (fst A (Over.mk p)) =
      lift (snd A (Over.mk p) ≫ a) (fst A (Over.mk p)) := by
    ext <;> simp [MonObj.mul_comp]
  have k2 : CechPic.pull (lift (1 : A ⊗ Over.mk p ⟶ A) (fst A (Over.mk p))).left (CechPic.cls P hL) = 0 := by
    have e1 : AbDual.evc hL (1 : A ⟶ A) (𝟙 A) = 0 := (AbDual.triv_ev_iff hL _ _).1 h1
    have e2 : lift (1 : A ⊗ Over.mk p ⟶ A) (fst A (Over.mk p)) =
        fst A (Over.mk p) ≫ lift (1 : A ⟶ A) (𝟙 A) := by
      ext <;> simp
    have e3 : CechPic.pull (lift (1 : A ⟶ A) (𝟙 A)).left (CechPic.cls P hL) = 0 := e1
    rw [e2, Over.comp_left, CechPic.pull_comp, e3, map_zero]
  rw [k1, k2, sub_zero] at e
  exact (AbDual.triv_ev_iff hL _ _).2 e.symm

end GlobalTheory.WeilKernel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeatOperatorValuesRingOperatorFractionField
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatVal

theorem rsT_self {Y : Scheme.{0}} {O₀ : Y.Opens} (s : Γ(Y, O₀)) : rsT s O₀ = s := by
  simp [GlobalTheory.KS.rsT]

theorem valR_eq {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR x U f = ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (x.appLE U ⊤ h).hom) f := by
  unfold valR; rw [dif_pos h]; rfl

theorem value_opV_ringOp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (c : R), c ≠ 0 → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (DV : Derivation ℤ Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), (∀ r, DV (GlobalTheory.HeatV.resV R c r) = GlobalTheory.HeatV.resV R c (D r)) → ∀ (iota : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) →+* (FractionRing Ω)), (∀ r, iota (GlobalTheory.HeatV.resV R c r) = (algebraMap Ω (FractionRing Ω)) (φ r)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → Fld t.G.left) (u : Fin n → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (pf pf' : ∀ i, Γ(t.G.left, W i)) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → (∀ i, W i ≤ t.PP.L.U (j i)) → (∀ i, IsField (W i) (d i)) → (∀ i O (h : O ≤ W i) (a : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), d i O (GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) a) = GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) (DV a)) → (∀ (k : ℕ) i i' O (h : O ≤ W i ⊓ W i') (f : Γ(t.G.left, O)), GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k O (h.trans (inf_le_left.trans (hW i))) (pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * f) = pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i') (pf i') (pf' i') k O (h.trans (inf_le_right.trans (hW i'))) f) → ∃ (dt : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u' : Fin n → (FractionRing Ω)) (p p' : (FractionRing Ω)), (∀ r, dt ((algebraMap Ω (FractionRing Ω)) (φ r)) = (algebraMap Ω (FractionRing Ω)) (φ (D r))) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (σ σ' : SecM (𝟙 t.G.left) t.PP.L k) (r a : R) (ω : Ω), (∀ i, rsT (σ'.f fun _ => j i) (W i) = GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c r) * (GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c a) * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k (W i) (hW i) (rsT (σ.f fun _ => j i) (W i)) - 2 * (k : Γ(t.G.left, W i)) * GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c (D a)) * rsT (σ.f fun _ => j i) (W i))) → IsValue (𝟙 _) t.PP.L x' g k σ ω → ∃ ω' : Ω, IsValue (𝟙 _) t.PP.L x' g k σ' ω' ∧ (algebraMap Ω (FractionRing Ω)) ω' = (algebraMap Ω (FractionRing Ω)) (φ r) * ((algebraMap Ω (FractionRing Ω)) (φ a) * ringOp ⇑dt (fun b => ⇑(δL b)) (iota.mapMatrix Θ₁) u' p p' k ((algebraMap Ω (FractionRing Ω)) ω) - 2 * (k : (FractionRing Ω)) * (algebraMap Ω (FractionRing Ω)) (φ (D a)) * (algebraMap Ω (FractionRing Ω)) ω) := by
  intro E _ _ _ H R _ _ _ _ _ _ t c hc n v' D Ω _ _ _ φ x' δ dd' hadic hx' hinv hδφ hval hinj g hg δL hδL Θ₁ DV hDV iota hiota J W j d u pf pf' hW hcov hWU hfield hlift hglue
  have hφ : Function.Injective φ := GlobalTheory.T.injective_ringMap_of_pointValues_detect_functions R t.G Ω φ x' hx' hinj
  have hφc : φ c ≠ 0 := fun h => hc (hφ (by rw [h, map_zero]))
  haveI : CharZero Ω := charZero_of_injective_ringHom (φ.comp (algebraMap ℚ R)).injective
  haveI : CharZero (FractionRing Ω) :=
    charZero_of_injective_ringHom (IsFractionRing.injective Ω (FractionRing Ω))
  obtain ⟨i0, hi0⟩ := GlobalTheory.T.exists_cover_member_containing_fractionField_point R t.G Ω φ x' hx' c hφc J W hcov
  obtain ⟨dt0, hdt0⟩ := GlobalTheory.T.exists_derivation_fractionRing_of_vectorField t.G.left Ω x' hinj (W i0) (d i0) (hfield i0) hi0
  have hddv := fun a => GlobalTheory.T.pointValue_fractionField_comm_vectorField t.G.left Ω x' (dd' a) (δ a) (δL a) (hinv a).1 (hval a) (hδL a)
  have hcst := GlobalTheory.T.pointValue_fractionField_eq_basicOpen_extension R t.G Ω φ x' hx' c iota hiota (W i0) (hW i0) hi0
  obtain ⟨e₀, he₀⟩ := GlobalTheory.T.chartFunction_eq_value_mul_unit_pow_fractionField t.G.left t.PP.L t.PP.isLB Ω x' g (j i0) (W i0) (hWU i0) hi0
  set ψ : Γ(t.G.left, W i0) →+* FractionRing Ω :=
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Ω))).hom.hom.comp
      ((spMap (algebraMap Ω (FractionRing Ω)) ≫ x').appLE (W i0) ⊤ hi0).hom with hψ
  have hv : ∀ f, valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') (W i0) f = ψ f :=
    fun f => valR_eq _ _ hi0 f
  have hd0 : ∀ F, ψ (d i0 (W i0) F) = dt0 (ψ F) := by
    intro F; rw [← hv, ← hv]; exact hdt0 _ _ le_rfl hi0
  have hdd : ∀ a F, ψ (dd' a (W i0) F) = δL a (ψ F) := by
    intro a F; rw [← hv, ← hv]; exact hddv a _ _ hi0
  have hc' : ∀ θ, ψ (GlobalTheory.HeatV.cst t.G.hom _ (hW i0) θ) = iota θ := by
    intro θ; rw [← hv]; exact hcst θ
  obtain ⟨dt, u', p, p', hdt, hgauge⟩ := GlobalTheory.T.heatRingOperator_conj_by_pow_nonzero Ω n dt0 δL (iota.mapMatrix Θ₁) two_ne_zero
    (fun a => iota (u a)) (ψ (pf i0)) (ψ (pf' i0)) (e₀ : FractionRing Ω) e₀.ne_zero
  have hdtR : ∀ r, dt (algebraMap Ω (FractionRing Ω) (φ r)) = algebraMap Ω (FractionRing Ω) (φ (D r)) := by
    intro r
    rw [hdt _ (fun a => by rw [hδL, hδφ, map_zero]), ← hiota, ← hiota, ← hc', ← hc', ← hd0]
    have := hlift i0 (W i0) le_rfl (GlobalTheory.HeatV.resV R c r)
    rw [this, hDV]
  refine ⟨dt, u', p, p', hdtR, ?_⟩
  intro k hk σ σ' r a ω hσ' hω
  have hop : ∀ F, ψ (GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i0) (pf i0) (pf' i0) k (W i0) (hW i0) F) =
      ringOp ⇑dt0 (fun b => ⇑(δL b)) (iota.mapMatrix Θ₁) (fun a => iota (u a)) (ψ (pf i0)) (ψ (pf' i0)) k (ψ F) := by
    intro F
    simp only [GlobalTheory.HeatV.opV, ringOp, map_add, map_sub, map_mul, map_sum, map_natCast, map_ofNat, map_pow, hd0, hdd,
      hc', rsT_self, RingHom.mapMatrix_apply, Matrix.map_apply]
  obtain ⟨ω', hω'⟩ := GlobalTheory.T.exists_sectionValue_in_frame_localRing_point t.G.left t.PP.L t.PP.isLB Ω x' g hg k σ'
  refine ⟨ω', hω', ?_⟩
  have h1 := he₀ k σ ω hω
  have h2 := he₀ k σ' ω' hω'
  rw [hv] at h1 h2
  have h3 := congrArg ψ (hσ' i0)
  simp only [map_mul, map_sub, map_natCast, map_ofNat, hop, hc', hiota] at h3
  rw [h1, h2, mul_comm (algebraMap Ω (FractionRing Ω) ω) ((e₀ : FractionRing Ω) ^ k), hgauge] at h3
  apply mul_left_cancel₀ (pow_ne_zero k e₀.ne_zero)
  linear_combination h3

end GlobalTheory.HeatVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrimitiveDeRhamCohomologyOfAdditivePeriodsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_primitiveDeRhamCohomology_of_additive_periods : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (c : FirstDeRham (str A)) (p : u.Λ →+ ℂ), IsPer u.ex u.Λ (cmp1 (str A) c) p → c ∈ primDR A := by
  first | exact @GlobalTheory.CechPer.mem_primDR_of_isPer | exact GlobalTheory.CechPer.mem_primDR_of_isPer | (intros; apply GlobalTheory.CechPer.mem_primDR_of_isPer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointDerivationsEqZeroKillingBothFactorsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointDerivations_eq_zero_killing_both_factors : ∀ (Z Z' X X' : Scheme.{0}) (p : Z ⟶ X) (p' : Z' ⟶ X') (φ : Z' ⟶ Z) (g : X' ⟶ X), IsPullback φ p' p g → ∀ (U : X.affineOpens) (U' : X'.affineOpens), U'.1 ≤ g ⁻¹ᵁ U.1 → ∀ (W₀ : Z.Opens), W₀ ≤ p ⁻¹ᵁ U.1 → ∀ (O : Z'.Opens), O ≤ φ ⁻¹ᵁ W₀ ⊓ p' ⁻¹ᵁ U'.1 → ∀ (S : Type) [CommRing S] [IsLocalRing S] (g₀ : Sp S ⟶ Z'), ⊤ ≤ g₀ ⁻¹ᵁ O → ∀ (Δ : ∀ O' : Z'.Opens, Γ(Z', O') → S), (∀ O' : Z'.Opens, O' ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O' → ∀ f f', Δ O' (f + f') = Δ O' f + Δ O' f') → (∀ O' : Z'.Opens, O' ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O' → ∀ f f', Δ O' (f * f') = valR g₀ O' f * Δ O' f' + valR g₀ O' f' * Δ O' f) → (∀ (O₁ O₂ : Z'.Opens) (h : O₂ ≤ O₁), O₁ ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O₂ → ∀ f, Δ O₂ (resG Z' h f) = Δ O₁ f) → (∀ (O₀ : Z.Opens) (O' : Z'.Opens) (h : O' ≤ φ ⁻¹ᵁ O₀), O₀ ≤ W₀ → O' ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O' → ∀ f₀, Δ O' ((φ.appLE O₀ O' h).hom f₀) = 0) → (∀ (O' : Z'.Opens) (h : O' ≤ p' ⁻¹ᵁ U'.1), O' ≤ O → ⊤ ≤ g₀ ⁻¹ᵁ O' → ∀ r, Δ O' ((p'.appLE U'.1 O' h).hom r) = 0) → ∀ f, Δ O f = 0 := by
  first | exact @GlobalTheory.KSBaseChangeLocal.eq_zero_of_kills_both | exact GlobalTheory.KSBaseChangeLocal.eq_zero_of_kills_both | (intros; apply GlobalTheory.KSBaseChangeLocal.eq_zero_of_kills_both <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationDlogCocycleCoboundaryClosedFibreChar
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

namespace GlobalTheory.ChartCob

theorem resG_appLE {Y Z : Scheme.{0}} (f : Y ⟶ Z) {O : Z.Opens} {V V' : Y.Opens} (h : V ≤ f ⁻¹ᵁ O) (h' : V' ≤ V)
    (s : Γ(Z, O)) : resG Y h' ((f.appLE O V h).hom s) = (f.appLE O V' (h'.trans h)).hom s := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_resG {Y Z : Scheme.{0}} (f : Y ⟶ Z) {O O' : Z.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ O') (h' : O' ≤ O)
    (s : Γ(Z, O)) :
    (f.appLE O' V h).hom (resG Z h' s) = (f.appLE O V (fun _ hx => h' (h hx))).hom s := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem isCoc_pullback {Y Z : Scheme.{0}} (f : Y ⟶ Z) {J : Type} (W : J → Z.Opens)
    (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) (hc : GlobalTheory.CechFin.IsCoc W c) :
    GlobalTheory.CechFin.IsCoc (fun i => f ⁻¹ᵁ W i)
      (fun i i' => (f.appLE (W i ⊓ W i') (f ⁻¹ᵁ W i ⊓ f ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i')) := by
  intro i i' i''
  have h3 : f ⁻¹ᵁ W i ⊓ f ⁻¹ᵁ W i' ⊓ f ⁻¹ᵁ W i'' ≤ f ⁻¹ᵁ (W i ⊓ W i' ⊓ W i'') := fun _ hx => hx
  have e := congrArg (f.appLE (W i ⊓ W i' ⊓ W i'') (f ⁻¹ᵁ W i ⊓ f ⁻¹ᵁ W i' ⊓ f ⁻¹ᵁ W i'') h3).hom
    (hc i i' i'')
  rw [map_add, appLE_resG, appLE_resG, appLE_resG] at e
  exact (congrArg₂ (· + ·) (resG_appLE f _ _ _) (resG_appLE f _ _ _)).trans (e.trans (resG_appLE f _ _ _).symm)

theorem isCoc_sum {Z X : Scheme.{0}} (p : Z ⟶ X) (U : X.Opens) (L : LB Z) (hL : L.IsLB) {n : ℕ}
    (δ : Fin n → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)) (hδ : ∀ a, IsField (p ⁻¹ᵁ U) (δ a))
    {J : Type} (W : J → Z.Opens) (j : J → L.ι) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U) (hj : ∀ i, W i ≤ L.U (j i))
    (r : Fin n → Γ(X, U)) :
    GlobalTheory.CechFin.IsCoc W (fun i i' => ∑ b, (p.appLE U (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) *
      (δ b (W i ⊓ W i') (resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i')).val) *
        resG Z (inf_le_inf (hj i) (hj i')) (L.g (j i) (j i'))⁻¹.val)) := by
  intro i i' i''
  simp only [map_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have e := GlobalTheory.DlogCocycle.dlog_cocycle Z L hL _ (δ b) (hδ b) J W j hWU hj i i' i''
  rw [map_mul (resG Z _) ((p.appLE _ _ _).hom _), map_mul (resG Z _) ((p.appLE _ _ _).hom _),
    map_mul (resG Z _) ((p.appLE _ _ _).hom _), resG_appLE, resG_appLE, resG_appLE, ← e, mul_add]

theorem isCob_pbT {Y Z : Scheme.{0}} (f : Y ⟶ Z) {I : Type} (V Ω : I → Z.Opens)
    (hle : ∀ a, f ⁻¹ᵁ V a ≤ f ⁻¹ᵁ Ω a) (c : ∀ a b : I, Γ(Z, Ω a ⊓ Ω b)) (h : ∀ a, Γ(Y, f ⁻¹ᵁ Ω a))
    (hh : ∀ a b, (f.appLE (Ω a ⊓ Ω b) (f ⁻¹ᵁ Ω a ⊓ f ⁻¹ᵁ Ω b) (fun _ hx => hx)).hom (c a b) =
      resG Y inf_le_left (h a) - resG Y inf_le_right (h b)) :
    GlobalTheory.KS.IsCob (fun a => f ⁻¹ᵁ V a) (fun a b => GlobalTheory.KS.pbT f (c a b) (f ⁻¹ᵁ V a ⊓ f ⁻¹ᵁ V b)) := by
  refine ⟨fun a => -resG Y (hle a) (h a), fun a b => ?_⟩
  have e := (resG_appLE f _ (inf_le_inf (hle a) (hle b)) _).symm.trans
    (congrArg (resG Y (inf_le_inf (hle a) (hle b))) (hh a b))
  rw [map_sub, GlobalTheory.DlogCocycle.resG_resG, GlobalTheory.DlogCocycle.resG_resG] at e
  have hab : f ⁻¹ᵁ V a ⊓ f ⁻¹ᵁ V b ≤ f ⁻¹ᵁ (Ω a ⊓ Ω b) := fun x hx => ⟨hle a hx.1, hle b hx.2⟩
  simp only [GlobalTheory.KS.pbT, GlobalTheory.KS.rsT]
  rw [dif_pos hab, dif_pos inf_le_left, dif_pos inf_le_right, map_neg, map_neg,
    GlobalTheory.DlogCocycle.resG_resG, GlobalTheory.DlogCocycle.resG_resG]
  refine e.trans ?_
  ring

theorem chart_isCob : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (hj : ∀ i, W i ≤ t.PP.L.U (j i)) (m : Ideal Γ(X, U.1)) (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (ι : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) ι → ∀ (r : Fin n → Γ(X, U.1)) (h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i)), (∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (∑ b, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r b) * (δ b (W i ⊓ W i') (resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i')).val) * resG t.G.left (inf_le_inf (hj i) (hj i')) (t.PP.L.g (j i) (j i'))⁻¹.val)) = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → GlobalTheory.KS.IsCob (fun a => ι ⁻¹ᵁ t.PP.L.U a) (fun a b => GlobalTheory.KS.pbT ι (∑ c, (t.G.hom.appLE U.1 ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (inf_le_left.trans inf_le_right)).hom (r c) * (δ c ((t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) ⊓ (t.PP.L.U b ⊓ t.G.hom ⁻¹ᵁ U.1)) (resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b).val) * resG t.G.left (inf_le_inf inf_le_left inf_le_left) (t.PP.L.g a b)⁻¹.val)) (ι ⁻¹ᵁ t.PP.L.U a ⊓ ι ⁻¹ᵁ t.PP.L.U b)) := by
  intro E _ _ _ H X t U n δ hδ J W j _ hsup hWU hj m A _ ι hι r h' hh'
  have htop : ∀ x : A.left, x ∈ ι ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1) := by
    intro x
    have hw := hι.1.w
    have : x ∈ (ι ≫ t.G.hom) ⁻¹ᵁ U.1 := by
      rw [hw]
      show (A.hom ≫ spMap (Ideal.Quotient.mk m) ≫ chart U) x ∈ (U.1 : Set X)
      rw [← U.2.range_fromSpec]
      exact ⟨(A.hom ≫ spMap (Ideal.Quotient.mk m)) x, rfl⟩
    exact this
  let Ω : J ⊕ t.PP.L.ι → t.G.left.Opens := Sum.elim W (fun a => t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1)
  let jj : J ⊕ t.PP.L.ι → t.PP.L.ι := Sum.elim j id
  have hΩU : ∀ q, Ω q ≤ t.G.hom ⁻¹ᵁ U.1 := by
    rintro (i | a)
    · exact hWU i
    · exact inf_le_right
  have hΩj : ∀ q, Ω q ≤ t.PP.L.U (jj q) := by
    rintro (i | a)
    · exact hj i
    · exact inf_le_left
  have hc := isCoc_pullback ι Ω _ (isCoc_sum t.G.hom U.1 t.PP.L t.PP.isLB δ hδ Ω jj hΩU hΩj r)
  obtain ⟨h, hh⟩ := GlobalTheory.CechFin.isCob_of_isCob_subcover A.left (J ⊕ t.PP.L.ι) (fun q => ι ⁻¹ᵁ Ω q)
    (Set.range Sum.inl) (by
      intro q x _
      have hx : ι x ∈ ⨆ i, W i := by rw [hsup]; exact htop x
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨Sum.inl i, TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, rfl⟩, hi⟩⟩)
    _ hc (fun q => match q with | Sum.inl i => h' i | Sum.inr _ => 0) (by
      rintro _ ⟨i, rfl⟩ _ ⟨i', rfl⟩
      exact hh' i i')
  exact isCob_pbT ι t.PP.L.U (fun a => t.PP.L.U a ⊓ t.G.hom ⁻¹ᵁ U.1) (fun a x hx => ⟨hx, htop x⟩) _
    (fun a => h (Sum.inr a)) (fun a b => hh (Sum.inr a) (Sum.inr b))

end GlobalTheory.ChartCob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveCrystallineBaseChangeNilpotentThickeninStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveCrystalline_baseChange_nilpotent_thickening : ∀ (A₀ : Over (Sp ℂ)) [GrpObj A₀] (g : ℕ), IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : ℂ, π (algebraMap ℂ D a) = a) → ∀ (k : GrpMor (dp0 ℂ) (𝟙 _) A₀ κ (spMap π) A₀ (algebraMap ℂ D) (𝟙 _) (Over.Hom.left (𝟙 A₀))), k.IsBC ∧ Submodule.span D (Set.range k.pull) = ⊤ := by
  first | exact @GlobalTheory.primCris_isBC_of_nilThick | exact GlobalTheory.primCris_isBC_of_nilThick | (intros; apply GlobalTheory.primCris_isBC_of_nilThick <;> assumption)
end

