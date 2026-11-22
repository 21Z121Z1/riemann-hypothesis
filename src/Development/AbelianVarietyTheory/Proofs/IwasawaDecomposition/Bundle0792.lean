import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0694
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0710
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0755
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0687
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinRepsProjectiveFinrankLeNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinkowskiWeylOrthantConeIntegralConstraints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0773
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChoiceTwistedChainsFormsClasses
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0774
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthCommonDenominatorRankLe
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarDen

section Cone

variable {X : Type} [AddCommGroup X] {m m' : ℕ}

theorem rcone_add {γ : Fin m → LinearMap.BilinForm ℤ X} {B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (h : B ∈ rcone γ)
    (h' : B' ∈ rcone γ) : B + B' ∈ rcone γ := by
  obtain ⟨t, ht, rfl⟩ := h
  obtain ⟨t', ht', rfl⟩ := h'
  exact ⟨t + t', fun i => add_nonneg (ht i) (ht' i), by simp [add_smul, Finset.sum_add_distrib]⟩

theorem rcone_smul {γ : Fin m → LinearMap.BilinForm ℤ X} {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (h : B ∈ rcone γ) {a : ℝ}
    (ha : 0 ≤ a) : a • B ∈ rcone γ := by
  obtain ⟨t, ht, rfl⟩ := h
  exact ⟨a • t, fun i => mul_nonneg ha (ht i), by simp [Finset.smul_sum, smul_smul]⟩

theorem rcone_zero (γ : Fin m → LinearMap.BilinForm ℤ X) : (0 : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) ∈ rcone γ :=
  ⟨0, fun _ => le_rfl, by simp⟩

theorem rcone_gen (γ : Fin m → LinearMap.BilinForm ℤ X) (j : Fin m) : toReal (γ j) ∈ rcone γ := by
  obtain ⟨c, hc, e⟩ := inRCone_self γ j
  exact ⟨c, hc, e⟩

theorem rcone_sum {γ : Fin m → LinearMap.BilinForm ℤ X} {ι : Type} (S : Finset ι) (f : ι → X →ₗ[ℤ] X →ₗ[ℤ] ℝ)
    (hf : ∀ i ∈ S, f i ∈ rcone γ) : ∑ i ∈ S, f i ∈ rcone γ :=
  Finset.sum_induction _ (· ∈ rcone γ) (fun _ _ => rcone_add) (rcone_zero γ) hf

theorem rcone_mono {γ : Fin m → LinearMap.BilinForm ℤ X} {γ' : Fin m' → LinearMap.BilinForm ℤ X}
    (h : ∀ i, ∃ j, γ i = γ' j) {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : B ∈ rcone γ) : B ∈ rcone γ' := by
  obtain ⟨t, ht, rfl⟩ := hB
  refine rcone_sum _ _ fun i _ => ?_
  obtain ⟨j, hj⟩ := h i
  rw [hj]
  exact rcone_smul (rcone_gen γ' j) (ht i)

theorem lin_cons (u : LinearMap.BilinForm ℤ X) (γ : Fin m → LinearMap.BilinForm ℤ X)
    (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (β : LinearMap.BilinForm ℤ X) (a : ℝ) (c : Fin m → ℝ)
    (h : toReal β = a • toReal u + ∑ i, c i • toReal (γ i)) : (ℓ β : ℝ) = a * ℓ u + ∑ i, c i * ℓ (γ i) := by
  have h1 : ∑ i : Fin (m + 2), (Fin.cons (-1) (Fin.cons a c) : Fin (m + 2) → ℝ) i •
      toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X)
        ((Fin.cons β (Fin.cons u γ) : Fin (m + 2) → LinearMap.BilinForm ℤ X) i)) = 0 := by
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, LinearMap.id_apply, h]
    simp only [neg_smul, one_smul]
    abel
  have h2 := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) (fun _ _ h => h) ℓ h1
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h2
  linarith

end Cone

section Depth

variable {O : Type} [CommRing O] {bar : O → O} {ψ w : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m : ℕ}

theorem depth_eq_of_star {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCell bar ψ γ)
    {v : LinearMap.BilinForm ℤ X} (hvb : v ∈ balForms bar X) (hvp : ∀ y, 0 ≤ v y y) (hvw : w.evalZ v = 1)
    (hvc : InRCone γ v) (hv0 : v ≠ 0)
    (huniq : ∀ v' ∈ balForms bar X, (∀ y, 0 ≤ v' y y) → w.evalZ v' = 1 → InRCone γ v' → v' = v)
    {m' : ℕ} {s : Fin m' ↪ Fin m} {h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (hF : IsFaceCut γ s h) (hhv : 0 < h v)
    {β : LinearMap.BilinForm ℤ X} (hβ : toReal β ∈ rcone (Fin.cons v fun j => γ (s j))) :
    (h v : ℝ) * (starDepth bar ψ w).evalZ β = h β := by
  obtain ⟨t, ht, hβt⟩ := hβ
  rw [Fin.sum_univ_succ] at hβt
  simp only [Fin.cons_zero, Fin.cons_succ] at hβt
  have hs0 : ∀ j, h (γ (s j)) = 0 := fun j => (hF.2 (s j)).2 ⟨j, rfl⟩
  have hhβ : (h β : ℝ) = t 0 * h v := by
    rw [lin_cons v (fun j => γ (s j)) h β (t 0) (fun j => t j.succ) hβt]
    simp [hs0]
  have hvR : (0 : ℝ) < h v := by exact_mod_cast hhv
  have hface : ∑ j, t j.succ • toReal (γ (s j)) ∈ rcone γ :=
    rcone_sum _ _ fun j _ => rcone_smul (rcone_gen γ (s j)) (ht j.succ)
  have hvR' : toReal v ∈ rcone γ := by
    obtain ⟨c, hc, e⟩ := hvc
    exact ⟨c, hc, e⟩
  have hBγ : toReal β ∈ rcone γ := by
    rw [hβt]; exact rcone_add (rcone_smul hvR' (ht 0)) hface
  have hlow : t 0 ≤ evalR (starDepth bar ψ w) (toReal β) :=
    GlobalTheory.T.centreDepth_le_starDepth_of_cell O bar ψ w X m γ (toReal β) v (t 0) hγ hBγ hvb hvp hvw hvc hv0 huniq (ht 0)
      (by rw [hβt, add_sub_cancel_left]; exact hface)
  have hup : evalR (starDepth bar ψ w) (toReal β) ≤ t 0 := by
    refine GlobalTheory.PolFan.evalR_starDepth_le O bar ψ w X m γ (toReal β) (t 0) hγ hBγ (ht 0) ?_
    intro v' hb hp hw1 hc t' ht' hmem
    obtain rfl := huniq v' hb hp hw1 hc
    obtain ⟨e, he, hee⟩ := hmem
    have h1 := lin_cons v' γ h β t' e (by rw [← hee]; abel)
    have h2 : 0 ≤ ∑ i, e i * (h (γ i) : ℝ) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (he i) (by exact_mod_cast hF.1 i)
    rw [hhβ] at h1
    nlinarith
  rw [evalR_toReal] at hlow hup
  rw [hhβ, le_antisymm hup hlow]
  ring

end Depth

section Den

theorem common_den {ι : Type} [Finite ι] (A : ι → Set ℝ)
    (h : ∀ i, ∃ D : ℕ, 0 < D ∧ ∀ x ∈ A i, ∃ n : ℤ, (D : ℝ) * x = n) :
    ∃ D : ℕ, 0 < D ∧ ∀ i, ∀ x ∈ A i, ∃ n : ℤ, (D : ℝ) * x = n := by
  classical
  choose D hD hA using h
  haveI := Fintype.ofFinite ι
  refine ⟨∏ i, D i, Finset.prod_pos fun i _ => hD i, fun i x hx => ?_⟩
  obtain ⟨n, hn⟩ := hA i x hx
  refine ⟨(∏ j ∈ Finset.univ.erase i, D j : ℕ) * n, ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ D (Finset.mem_univ i)]
  push_cast
  rw [← hn]
  ring

variable {O : Type} [CommRing O] {bar : O → O} {ψ w : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem cell_den {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCell bar ψ γ)
    (hw : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
      ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1)
    (hu : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms bar X, (∀ y, 0 ≤ β' y y) →
      w.evalZ β = 1 → w.evalZ β' = 1 → InRCone γ β → InRCone γ β' → β = β') :
    ∃ D : ℕ, 0 < D ∧ ∀ β : LinearMap.BilinForm ℤ X, toReal β ∈ rcone γ →
      ∃ n : ℤ, (D : ℝ) * (starDepth bar ψ w).evalZ β = n := by
  classical
  by_cases hc : ∃ v ∈ balForms bar X, (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v
  · obtain ⟨v, hvb, hvp, hvw, hvc⟩ := hc
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact absurd (hw 0 hvb hvp hvw 0 0 (by simp)) (by norm_num)
    have huniq : ∀ v' ∈ balForms bar X, (∀ y, 0 ≤ v' y y) → w.evalZ v' = 1 → InRCone γ v' → v' = v :=
      fun v' hb hp hw1 hc' => hu v' hb hp v hvb hvp hw1 hvw hc' hvc
    let A : Set (Fin m) → Set ℝ := fun Z => {x | ∃ β : LinearMap.BilinForm ℤ X, x = (starDepth bar ψ w).evalZ β ∧
      ∃ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), Set.range s = Z ∧ IsFaceCut γ s h ∧
        0 < h v ∧ toReal β ∈ rcone (Fin.cons v fun j => γ (s j))}
    have hA : ∀ Z, ∃ D : ℕ, 0 < D ∧ ∀ x ∈ A Z, ∃ n : ℤ, (D : ℝ) * x = n := by
      intro Z
      by_cases hne : ∃ x, x ∈ A Z
      · obtain ⟨-, β₀, -, m₀, s₀, h₀, hs₀, hF₀, hh₀, -⟩ := hne
        refine ⟨(h₀ v).toNat, by omega, ?_⟩
        rintro x ⟨β, rfl, m', s, h, hs, hF, hh, hβ⟩
        have hF' : IsFaceCut γ s h₀ := ⟨hF₀.1, fun j => by rw [hF₀.2 j, hs₀, hs]⟩
        have key := depth_eq_of_star hγ hvb hvp hvw hvc hv0 huniq hF' hh₀ hβ
        refine ⟨h₀ β, ?_⟩
        have e : (((h₀ v).toNat : ℤ) : ℝ) = (h₀ v : ℝ) := by rw [Int.toNat_of_nonneg hh₀.le]
        rw [← key, ← e]
        norm_cast
      · push_neg at hne
        exact ⟨1, one_pos, fun x hx => (hne x hx).elim⟩
    obtain ⟨D, hD, hall⟩ := common_den A hA
    refine ⟨D, hD, fun β hβ => ?_⟩
    obtain ⟨m', s, h, hF, hh, hβ'⟩ := GlobalTheory.StarCover.star_cover X m γ v (toReal β) (fun i y z => (hγ.mem i).1 y z)
      hγ.nonneg hv0 hvc hβ
    exact hall (Set.range s) _ ⟨β, rfl, m', s, h, rfl, hF, hh, hβ'⟩
  · push_neg at hc
    refine ⟨1, one_pos, fun β hβ => ⟨0, ?_⟩⟩
    have hup := GlobalTheory.PolFan.evalR_starDepth_le O bar ψ w X m γ (toReal β) 0 hγ hβ le_rfl
      fun v hb hp hw1 hc' => absurd hc' (hc v hb hp hw1)
    rw [evalR_toReal] at hup
    have h0 : 0 ≤ (starDepth bar ψ w).evalZ β := starDepth_eval_nonneg _
    rw [le_antisymm hup h0]
    simp

end Den

section Module

variable {O : Type} [CommRing O] {bar : O → O} {ψ w : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem module_den (hX : IsPolyFanOn bar ψ X)
    (hw : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
      ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1)
    (hu : ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ →
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms bar X, (∀ y, 0 ≤ β' y y) →
        w.evalZ β = 1 → w.evalZ β' = 1 → InRCone γ β → InRCone γ β' → β = β') :
    ∃ D : ℕ, 0 < D ∧ ∀ β : LinearMap.BilinForm ℤ X, toReal β ∈ psdCone bar X →
      ∃ n : ℤ, (D : ℝ) * (starDepth bar ψ w).evalZ β = n := by
  classical
  obtain ⟨S, hS, hcov⟩ := hX.finite
  haveI : Finite {T : Set (LinearMap.BilinForm ℤ X) | T ⊆ S} := hS.finite_subsets.to_subtype
  let A : {T : Set (LinearMap.BilinForm ℤ X) | T ⊆ S} → Set ℝ := fun T =>
    {x | ∃ β : LinearMap.BilinForm ℤ X, x = (starDepth bar ψ w).evalZ β ∧ ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X),
      IsCell bar ψ γ ∧ Set.range γ = T.1 ∧ toReal β ∈ rcone γ}
  have hA : ∀ T, ∃ D : ℕ, 0 < D ∧ ∀ x ∈ A T, ∃ n : ℤ, (D : ℝ) * x = n := by
    intro T
    by_cases hne : ∃ x, x ∈ A T
    · obtain ⟨-, -, -, m₀, γ₀, hγ₀, hr₀, -⟩ := hne
      obtain ⟨D, hD, hden⟩ := cell_den hγ₀ hw (hu m₀ γ₀ hγ₀)
      refine ⟨D, hD, ?_⟩
      rintro x ⟨β, rfl, m, γ, -, hr, hβ⟩
      refine hden β (rcone_mono (fun i => ?_) hβ)
      have : γ i ∈ Set.range γ₀ := by rw [hr₀, ← hr]; exact ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := this
      exact ⟨j, hj.symm⟩
    · push_neg at hne
      exact ⟨1, one_pos, fun x hx => (hne x hx).elim⟩
  obtain ⟨D, hD, hall⟩ := common_den A hA
  refine ⟨D, hD, fun β hβ => ?_⟩
  obtain ⟨e, m, γ, c, hγ, hγS, hc, hsum⟩ := hcov _ hβ
  have hpull : toReal (pull e.toLinearMap β) = ∑ i, c i • toReal (γ i) := by
    rw [← hsum]
    exact LinearMap.ext₂ fun a b => by simp
  have hval : (starDepth bar ψ w).evalZ (pull e.toLinearMap β) = (starDepth bar ψ w).evalZ β :=
    evalZ_pull _ e.surjective β
  rw [← hval]
  exact hall ⟨Set.range γ, by rintro _ ⟨i, rfl⟩; exact hγS i⟩ _
    ⟨pull e.toLinearMap β, rfl, m, γ, hγ, rfl, c, hc, hpull⟩

end Module

theorem starDepth_den : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)),
    IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∃ D₀ : ℕ, 0 < D₀ ∧ ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
      [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X,
        (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (D₀ : ℝ) * (starDepth H.bar ψ w).evalZ β = n := by
  intro E _ _ _ H q ψ w hψ hw
  obtain ⟨n, R, hR, hcls⟩ := GlobalTheory.exists_fin_reps_projective_finrank_le E q
  have key : ∀ k : Fin n, ∃ D : ℕ, 0 < D ∧ ∀ x ∈ {x : ℝ | ∃ β ∈ balForms H.bar (R k), (∀ y, 0 ≤ β y y) ∧
      haveI := (hR k).1; x = (starDepth H.bar ψ w).evalZ β}, ∃ z : ℤ, (D : ℝ) * x = z := fun k => by
    haveI := (hR k).1
    haveI := (hR k).2.1
    obtain ⟨-, h2, h3⟩ := hw (R k) (hR k).2.2
    obtain ⟨D, hD, hA⟩ := module_den (hψ (R k) (hR k).2.2) h2 h3
    refine ⟨D, hD, ?_⟩
    rintro x ⟨β, hβ, hp, rfl⟩
    exact hA β (toReal_mem_psdCone_of_nonneg E H (R k) β hβ hp)
  obtain ⟨D₀, hD₀, hall⟩ := common_den _ key
  refine ⟨D₀, hD₀, fun X _ _ _ _ hX β hβ hp => ?_⟩
  obtain ⟨k, ⟨f⟩⟩ := hcls X hX
  haveI := (hR k).1
  have hval : (starDepth H.bar ψ w).evalZ (pull f.symm.toLinearMap β) = (starDepth H.bar ψ w).evalZ β :=
    evalZ_pull _ f.symm.surjective β
  rw [← hval]
  exact hall k _ ⟨_, pull_mem _ hβ, fun y => hp _, rfl⟩

example (n : ℕ) (B : (Fin n → ℤ) → (Fin n → ℤ) → ℝ) : (starDepth id (InvFun.minVal ℤ) (zeroFun ℤ)).toFun n B = 0 :=
  starDepth_zeroFun n B

end GlobalTheory.PolFan.StarDen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthLeOnCentreCell
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolFan.StarOnCell

variable {X : Type} [AddCommGroup X]

theorem ell_of_eq {n : ℕ} (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) {β : LinearMap.BilinForm ℤ X}
    {u : Fin n → LinearMap.BilinForm ℤ X} {c : Fin n → ℝ} (h : toReal β = ∑ i, c i • toReal (u i)) :
    (ℓ β : ℝ) = ∑ i, c i * ℓ (u i) := by
  have h1 : ∑ i : Fin (n + 1), (Fin.cons (-1) c : Fin (n + 1) → ℝ) i •
      toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X)
        ((Fin.cons β u : Fin (n + 1) → LinearMap.BilinForm ℤ X) i)) = 0 := by
    simp [Fin.sum_univ_succ, h]
  have h2 := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) (fun _ _ h => h) ℓ h1
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h2
  simp at h2
  linarith

theorem ell_of_sub_mem {m : ℕ} (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) {β v : LinearMap.BilinForm ℤ X}
    {γ : Fin m → LinearMap.BilinForm ℤ X} {t : ℝ} (h : toReal β - t • toReal v ∈ rcone γ) :
    ∃ d : Fin m → ℝ, (∀ j, 0 ≤ d j) ∧ (ℓ β : ℝ) = t * ℓ v + ∑ j, d j * ℓ (γ j) := by
  obtain ⟨d, hd, e⟩ := h
  refine ⟨d, hd, ?_⟩
  have e' : toReal β = ∑ i : Fin (m + 1), (Fin.cons t d : Fin (m + 1) → ℝ) i •
      toReal ((Fin.cons v γ : Fin (m + 1) → LinearMap.BilinForm ℤ X) i) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← e]
    abel
  rw [ell_of_eq ℓ e', Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem inRCone_of_sum {p n : ℕ} {δ : Fin p → LinearMap.BilinForm ℤ X} {u : Fin n → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} (x : Fin p → ℝ) (hx : ∀ i, 0 ≤ x i) (e : toReal β = ∑ i, x i • toReal (δ i))
    (h : ∀ i, x i ≠ 0 → InRCone u (δ i)) : InRCone u β := by
  classical
  have hi : ∀ i, ∃ g : Fin n → ℝ, (∀ j, 0 ≤ g j) ∧ x i • toReal (δ i) = ∑ j, g j • toReal (u j) := by
    intro i
    by_cases h0 : x i = 0
    · exact ⟨0, fun _ => le_rfl, by simp [h0]⟩
    obtain ⟨c, hc, hcs⟩ := h i h0
    exact ⟨fun j => x i * c j, fun j => mul_nonneg (hx i) (hc j), by
      rw [hcs, Finset.smul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]⟩
  choose g hg hgs using hi
  refine ⟨fun j => ∑ i, g i j, fun j => Finset.sum_nonneg fun i _ => hg i j, ?_⟩
  rw [e, Finset.sum_congr rfl fun i _ => hgs i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_smul]

theorem exists_nat_of_inRCone {n : ℕ} (u : Fin n → LinearMap.BilinForm ℤ X) (β : LinearMap.BilinForm ℤ X)
    (hβ : InRCone u β) : ∃ (k : ℕ) (c : Fin n → ℕ), 0 < k ∧ k • β = ∑ i, c i • u i := by
  classical
  obtain ⟨c, hc, e⟩ := hβ
  obtain ⟨r, v, hiff, -⟩ := GlobalTheory.MinkWeylReal.cone_orthant_fg (n + 1) ∅
    (Set.range fun ab : X × X => (Fin.cons (-β ab.1 ab.2) (fun i => u i ab.1 ab.2) : Fin (n + 1) → ℤ))
    Set.finite_empty
  have h1 : (∀ i, 0 ≤ (Fin.cons 1 c : Fin (n + 1) → ℝ) i) ∧
      (∀ a ∈ (∅ : Set (Fin (n + 1) → ℤ)), ∑ i, (a i : ℝ) * (Fin.cons 1 c : Fin (n + 1) → ℝ) i ≤ 0) ∧
      (∀ b ∈ Set.range fun ab : X × X => (Fin.cons (-β ab.1 ab.2) (fun i => u i ab.1 ab.2) : Fin (n + 1) → ℤ),
        ∑ i, (b i : ℝ) * (Fin.cons 1 c : Fin (n + 1) → ℝ) i = 0) := by
    refine ⟨fun i => Fin.cases (by simp) (fun j => by simpa using hc j) i, by simp, ?_⟩
    rintro _ ⟨⟨a, b⟩, rfl⟩
    have he := LinearMap.congr_fun₂ e a b
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at he
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Int.cast_neg, mul_one]
    rw [he]
    rw [show ∑ i, (u i a b : ℝ) * c i = ∑ i, c i * (u i a b : ℝ) from
      Finset.sum_congr rfl fun i _ => mul_comm _ _]
    ring
  obtain ⟨e', he', ht⟩ := (hiff _).1 h1
  have h0 := congr_fun ht 0
  simp only [Fin.cons_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h0
  obtain ⟨k, hk⟩ : ∃ k, v k 0 ≠ 0 := by
    by_contra hne
    push_neg at hne
    simp [hne] at h0
  have hv := (hiff fun i => (v k i : ℝ)).2 ⟨Pi.single k 1, fun j => by
    by_cases h : j = k <;> simp [Pi.single_apply, h], by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single k (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
    simp⟩
  obtain ⟨-, -, hV⟩ := hv
  refine ⟨v k 0, fun i => v k i.succ, Nat.pos_of_ne_zero hk, ?_⟩
  ext a b
  have h2 := hV _ ⟨(a, b), rfl⟩
  rw [Fin.sum_univ_succ] at h2
  simp only [Fin.cons_zero, Fin.cons_succ, Int.cast_neg] at h2
  have h3 : ((v k 0 : ℤ) * β a b : ℝ) = ((∑ i, (v k i.succ : ℤ) * u i a b : ℤ) : ℝ) := by
    push_cast
    rw [show ∑ i, ((v k i.succ : ℝ) * (u i a b : ℝ)) = ∑ i, (u i a b : ℝ) * (v k i.succ : ℝ) from
      Finset.sum_congr rfl fun i _ => mul_comm _ _]
    linarith
  have h4 : (v k 0 : ℤ) * β a b = ∑ i, (v k i.succ : ℤ) * u i a b := by exact_mod_cast h3
  simpa [LinearMap.sum_apply] using h4

end GlobalTheory.PolFan.StarOnCell

namespace GlobalTheory.PolFan.StarOnCell

variable {O : Type} [CommRing O] {bar : O → O} {ψ w : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}

theorem mul_starDepth_le (hγ : IsCell bar ψ γ) {β₀ : LinearMap.BilinForm ℤ X}
    (huniq : ∀ v ∈ balForms bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → v = β₀)
    (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (hh : ∀ j, 0 ≤ h (γ j)) (hpos : 0 < h β₀)
    {β : LinearMap.BilinForm ℤ X} (hβ : InRCone γ β) :
    (h β₀ : ℝ) * (starDepth bar ψ w).evalZ β ≤ h β := by
  obtain ⟨c, hc, e⟩ := hβ
  have hpos' : (0 : ℝ) < h β₀ := by exact_mod_cast hpos
  have hhβ : (0 : ℝ) ≤ h β := by
    rw [ell_of_eq h e]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (by exact_mod_cast hh i)
  have key := evalR_starDepth_le O bar ψ w X m γ (toReal β) ((h β : ℝ) / h β₀) hγ ⟨c, hc, e⟩
    (div_nonneg hhβ hpos'.le) (fun v hv hvp hwv hvin t ht hrest => by
      obtain rfl := huniq v hv hvp hwv hvin
      obtain ⟨d, hd, hrel⟩ := ell_of_sub_mem h hrest
      rw [le_div_iff₀ hpos']
      have : (0 : ℝ) ≤ ∑ j, d j * h (γ j) :=
        Finset.sum_nonneg fun j _ => mul_nonneg (hd j) (by exact_mod_cast hh j)
      linarith)
  rw [evalR_toReal] at key
  calc (h β₀ : ℝ) * (starDepth bar ψ w).evalZ β ≤ h β₀ * ((h β : ℝ) / h β₀) :=
        mul_le_mul_of_nonneg_left key hpos'.le
    _ = h β := by field_simp

end GlobalTheory.PolFan.StarOnCell

open GlobalTheory.PolFan.StarOnCell in

theorem GlobalTheory.PolFan.starDepth_on_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ w : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∀ (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X,
    (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m)
    (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ →
    (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β →
      (h β₀ : ℝ) * (starDepth H.bar ψ w).evalZ β ≤ h β) ∧
    (starDepth H.bar ψ w).evalZ β₀ = 1 ∧ (∀ j, (starDepth H.bar ψ w).evalZ (γ (s j)) = 0) ∧
    ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β →
      (h β₀ : ℝ) * (starDepth H.bar ψ w).evalZ β = h β →
      ∃ (k : ℕ) (c : Fin (m' + 1) → ℕ), 0 < k ∧
        k • β = ∑ i, c i • (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) i := by
  intro E _ _ _ H q ψ w _ hc X _ _ _ _ hX m γ hγ β₀ hβ₀ hβ₀p hw hin m' s h hf hpos
  have huniq : ∀ v ∈ balForms H.bar X, (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → v = β₀ :=
    fun v hv hvp hwv hvin => (hc X hX).2.2 m γ hγ v hv hvp β₀ hβ₀ hβ₀p hwv hw hvin hin
  have hne : β₀ ≠ 0 := by
    rintro rfl
    have := (hc X hX).2.1 0 hβ₀ hβ₀p hw 2 0 (by simp)
    omega
  have hpos' : (0 : ℝ) < h β₀ := by exact_mod_cast hpos
  have hI : ∀ β, InRCone γ β → (h β₀ : ℝ) * (starDepth H.bar ψ w).evalZ β ≤ h β :=
    fun β hβ => mul_starDepth_le hγ huniq h hf.1 hpos hβ
  refine ⟨fun β _ _ hβ => hI β hβ, ?_, ?_, ?_⟩
  ·
    refine le_antisymm ?_ ?_
    · have := hI β₀ hin
      nlinarith
    · have hl := GlobalTheory.T.centreDepth_le_starDepth_of_cell (𝓞 E) H.bar ψ w X m γ (toReal β₀) β₀ 1 hγ (by
        obtain ⟨c, hc0, e⟩ := hin; exact ⟨c, hc0, e⟩) hβ₀ hβ₀p hw hin hne huniq zero_le_one
        (by rw [one_smul, sub_self]; exact ⟨0, fun _ => le_rfl, by simp⟩)
      rwa [evalR_toReal] at hl
  ·
    intro j
    have h0 : h (γ (s j)) = 0 := (hf.2 (s j)).2 ⟨j, rfl⟩
    have := hI (γ (s j)) (inRCone_self γ (s j))
    rw [h0, Int.cast_zero] at this
    have hnn : 0 ≤ (starDepth H.bar ψ w).evalZ (γ (s j)) := starDepth_eval_nonneg _
    nlinarith
  ·
    intro β _ _ hβ heq
    have hβr : toReal β ∈ rcone γ := by obtain ⟨c, hc0, e⟩ := hβ; exact ⟨c, hc0, e⟩
    obtain ⟨m'', s'', h'', hf'', hpos'', t, ht, e⟩ :=
      GlobalTheory.StarCover.star_cover X m γ β₀ (toReal β) (fun i => (hγ.mem i).1) hγ.nonneg hne hin hβr
    have hpos''' : (0 : ℝ) < h'' β₀ := by exact_mod_cast hpos''

    have r2 := ell_of_eq h'' e
    rw [Fin.sum_univ_succ] at r2
    simp only [Fin.cons_zero, Fin.cons_succ] at r2
    have z2 : ∀ j, (h'' (γ (s'' j)) : ℝ) = 0 := fun j => by
      rw [(hf''.2 (s'' j)).2 ⟨j, rfl⟩, Int.cast_zero]
    simp only [z2, mul_zero, Finset.sum_const_zero, add_zero] at r2
    have hle : (starDepth H.bar ψ w).evalZ β ≤ t 0 := by
      have := mul_starDepth_le hγ huniq h'' hf''.1 hpos'' hβ
      rw [r2] at this
      nlinarith

    have r1 := ell_of_eq h e
    rw [Fin.sum_univ_succ] at r1
    simp only [Fin.cons_zero, Fin.cons_succ] at r1
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ t j.succ * (h (γ (s'' j)) : ℝ) := fun j _ =>
      mul_nonneg (ht _) (by exact_mod_cast hf.1 _)
    have hsum : ∑ j, t j.succ * (h (γ (s'' j)) : ℝ) = 0 := by
      refine le_antisymm ?_ (Finset.sum_nonneg hnn)
      nlinarith
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum
    have hcone : InRCone (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) β := by
      refine inRCone_of_sum t ht e fun i hi => ?_
      refine Fin.cases (fun _ => ?_) (fun j hj => ?_) i hi
      · simpa using inRCone_self (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) 0
      · have h0 : (h (γ (s'' j)) : ℝ) = 0 := (mul_eq_zero.1 (hz j (Finset.mem_univ _))).resolve_left hj
        have h0' : h (γ (s'' j)) = 0 := by exact_mod_cast h0
        obtain ⟨k, hk⟩ := (hf.2 (s'' j)).1 h0'
        simpa [hk] using inRCone_self (Fin.cons β₀ fun j => γ (s j) : Fin (m' + 1) → LinearMap.BilinForm ℤ X) k.succ
    exact exists_nat_of_inRCone _ β hcone
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffProdDetHermitianSquarePowNonneStatement
section
open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeFormCoeff_prod_det_hermitianSquare_pow_nonneg : ∀ {n : ℕ} {κ : Type} [Fintype κ] (m r e : κ → ℕ) (T : ∀ t, V n →ₗ[ℂ] Matrix (Fin (m t)) (Fin (r t)) ℂ),
    0 ≤ topCoeff (∏ t, (sqPoly (T t)).det ^ e t) := by
  first | exact @GlobalTheory.PointFormSign.topCoeff_prod_det_sqPoly_pow_nonneg | exact GlobalTheory.PointFormSign.topCoeff_prod_det_sqPoly_pow_nonneg | (intros; apply GlobalTheory.PointFormSign.topCoeff_prod_det_sqPoly_pow_nonneg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChoiceTwistedChainsFormsClassesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumnChoice_twistedChains_formsClasses : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ a v, inQ a v ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → (∀ u j v h, (F u).glevJ.fr j v h = 1) → ∃ (T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ) (J : Formalism.L2.Herm.TwChJointS T H) (W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F), Formalism.L2.Herm.TwChMu0 T ∧ I.StdW l Z l0 W ∧ Nonempty (SymmetricTwistedJointForms T F) := by
  first | exact @GlobalTheory.Mem.Col2.TC.tw_chains | exact GlobalTheory.Mem.Col2.TC.tw_chains | (intros; apply GlobalTheory.Mem.Col2.TC.tw_chains <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverseStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unique_integral_lift_norm_p_inverse : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (p : ℕ) [Fact p.Prime] (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [CompleteSpace C], ‖(p : C)‖ = (p : ℝ)⁻¹ → ∀ (x : Sp ↥(intO C) ⟶ X), (∀ x' : Sp ↥(intO C) ⟶ X, spMap (intO C).subtype ≫ x' = spMap (intO C).subtype ≫ x → x' = x) → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber ↥(intO C)) ⟶ t.G.left)), IsTanBasis t x e → ∀ (n : ℕ) (h : Fin n → Fin g → ↥(intO C)), (∀ c : TorsChar t x (p ^ 1), ∃ j, DlogIs t p 1 c e (h j)) → (∀ j, ∃ c : TorsChar t x (p ^ 1), DlogIs t p 1 c e (h j)) → ∀ (a : Fin g → C) (w : Sp (DualNumber C) ⟶ t.G.left), IsCombAtG t (spMap (intO C).subtype ≫ x) (fun i => spMap (dualMap (intO C).subtype) ≫ e i) a w → (w ∈ latHT t p (spMap (intO C).subtype ≫ x) ↔ (∀ j, ‖∑ i, (h j i : C) * a i‖ ≤ 1) ∧ ∀ i, ‖(p : C) * a i‖ ≤ 1) := by
  first | exact @GlobalTheory.HTLevel.mem_latHT_iff | exact GlobalTheory.HTLevel.mem_latHT_iff | (intros; apply GlobalTheory.HTLevel.mem_latHT_iff <;> assumption)
end

