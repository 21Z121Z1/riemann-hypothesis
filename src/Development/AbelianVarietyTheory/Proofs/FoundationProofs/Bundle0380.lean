import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TargetAlt
section
open Formalism.MainNotions.N

namespace GlobalTheory.ConjugateIrreducibility

private theorem isIrrSub_of_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (H H' : Subgroup Γ)
    (hHH : ∀ s ∈ H, s ∈ H') (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k)
    (hconj : ∀ s : Γ, (r' : Γ → GL (Fin n) k) s = g * (r : Γ → GL (Fin n) k) s * g⁻¹)
    (hne : (⊤ : Submodule k (Fin n → k)) ≠ ⊥)
    (hmin : ∀ W : Submodule k (Fin n → k), W ≤ ⊤ → IsInv (MonoidHom.comp r (Subgroup.subtype H)) W →
      W = ⊥ ∨ W = ⊤) :
    IsIrrSub (MonoidHom.comp r' (Subgroup.subtype H')) ⊤ := by
  refine ⟨hne, fun _ _ _ => Submodule.mem_top, fun W _ hinv => ?_⟩

  let W₀ : Submodule k (Fin n → k) := W.comap (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k))
  have hmem : ∀ v, v ∈ W₀ ↔ (g : Matrix (Fin n) (Fin n) k).mulVec v ∈ W := fun v => by
    simp [W₀, Matrix.toLin'_apply]
  have hinv₀ : IsInv (MonoidHom.comp r (Subgroup.subtype H)) W₀ := by
    intro s v hv
    rw [hmem] at hv ⊢
    have key : (g : Matrix (Fin n) (Fin n) k).mulVec ((r s.1 : Matrix (Fin n) (Fin n) k).mulVec v) =
        (r' s.1 : Matrix (Fin n) (Fin n) k).mulVec ((g : Matrix (Fin n) (Fin n) k).mulVec v) := by
      simp [hconj, Matrix.mulVec_mulVec, mul_assoc]
    have h1 := hinv ⟨s, hHH s s.2⟩ _ hv
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at h1 ⊢
    rw [key]
    exact h1
  have hback : ∀ w, ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec w ∈ W₀ ↔ w ∈ W := fun w => by
    rw [hmem, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rcases hmin W₀ le_top hinv₀ with h0 | htop
  · left
    rw [eq_bot_iff]
    intro w hw
    have h1 := (hback w).mpr hw
    rw [h0, Submodule.mem_bot] at h1
    have h2 := congrArg (Matrix.mulVec (g : Matrix (Fin n) (Fin n) k)) h1
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    rw [h2]
    exact Submodule.zero_mem _
  · right
    rw [eq_top_iff]
    intro w _
    exact (hback w).mp (htop ▸ Submodule.mem_top)

theorem main {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (H H' : Subgroup Γ) (hHH : ∀ s ∈ H, s ∈ H')
    (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k)
    (hconj : ∀ s : Γ, (r' : Γ → GL (Fin n) k) s = g * (r : Γ → GL (Fin n) k) s * g⁻¹)
    (hirr : IsIrrSub (MonoidHom.comp r (Subgroup.subtype H)) ⊤) :
    IsIrrSub (MonoidHom.comp r' (Subgroup.subtype H')) ⊤ := by
  obtain ⟨hne, -, hmin⟩ := hirr
  exact isIrrSub_of_conj H H' hHH r r' g hconj hne hmin

theorem target : ∀ {Γ k : Type} [inst : Group Γ] [inst_1 : Field k] {n : ℕ} (H H' : Subgroup Γ), (∀ s ∈ H, s ∈ H') → ∀ (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k), (∀ (s : Γ), (r' : Γ → GL (Fin n) k) s = g * (r : Γ → GL (Fin n) k) s * g⁻¹) → Formalism.MainNotions.N.IsIrrSub (MonoidHom.comp r (Subgroup.subtype H)) ⊤ → Formalism.MainNotions.N.IsIrrSub (MonoidHom.comp r' (Subgroup.subtype H')) ⊤ := by
  intro Γ k _ _ n H H' hHH r r' g hconj hirr
  obtain ⟨hne, -, hmin⟩ := hirr
  exact isIrrSub_of_conj H H' hHH r r' g hconj hne hmin

end GlobalTheory.ConjugateIrreducibility
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceFormNeZeroOfStableLineIrreducible
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open GlobalTheory.Sl2Ad

namespace GlobalTheory.Sl2Ad

theorem form_ne_zero_of_isIrr : ∀ {K : Type} [Field K] [CharZero K] {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin 2) K), IsIrr ρ →
    ∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, ad (ρ g) *ᵥ y = c • y) → form y y ≠ 0 := by
  intro K _ _ Γ _ ρ hirr y hy hstab hform
  have hq : y 0 * y 1 + y 2 * y 2 = 0 := by
    rw [form_apply] at hform
    have h2 : (2 : K) * (y 0 * y 1 + y 2 * y 2) = 0 := by linear_combination hform
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hconj : ∀ g, ∃ c : K, ofCoord y * (ρ g : Matrix (Fin 2) (Fin 2) K) = (ρ g : Matrix (Fin 2) (Fin 2) K) * (c • ofCoord y) := by
    intro g
    obtain ⟨c, hc⟩ := hstab g⁻¹
    refine ⟨c, ?_⟩
    have h1 := coord_conj_ofCoord (ρ g⁻¹) y
    rw [hc] at h1
    have htr : ((ρ g⁻¹ : Matrix (Fin 2) (Fin 2) K) * ofCoord y * (((ρ g⁻¹)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).trace = 0 := by
      rw [trace_conj, trace_ofCoord]
    have h2 := ofCoord_coord htr
    rw [h1] at h2
    have h3 : ofCoord (c • y) = c • ofCoord y := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [ofCoord]
    rw [h3, map_inv, inv_inv] at h2
    have hu : (ρ g : Matrix (Fin 2) (Fin 2) K) * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  let Wk : Submodule K (Fin 2 → K) := LinearMap.ker (Matrix.mulVecLin (ofCoord y))
  have hmem : ∀ x, x ∈ Wk ↔ ofCoord y *ᵥ x = 0 := fun x => by
    simp [Wk, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  have hinv : IsInv ρ Wk := by
    intro g x hx
    rw [hmem] at hx ⊢
    obtain ⟨c, hc⟩ := hconj g
    have hs : (c • ofCoord y) *ᵥ x = c • (ofCoord y *ᵥ x) := by
      ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
    rw [Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec, hs, hx, smul_zero, Matrix.mulVec_zero]
  have hy0 : ∀ a b c : K, a = 0 → b = 0 → c = 0 → y 0 = a → y 1 = b → y 2 = c → False := by
    intro a b c ha hb hc h0 h1 h2
    apply hy
    ext i; fin_cases i
    · simpa [ha] using h0
    · simpa [hb] using h1
    · simpa [hc] using h2
  rcases hirr.2.2 Wk le_top hinv with h | h
  · have hv1 : (![y 0, -y 2] : Fin 2 → K) ∈ Wk := by
      rw [hmem]; ext i; fin_cases i <;> simp [ofCoord, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> first | linear_combination | linear_combination hq | linear_combination -hq
    have hv2 : (![y 2, y 1] : Fin 2 → K) ∈ Wk := by
      rw [hmem]; ext i; fin_cases i <;> simp [ofCoord, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> first | linear_combination | linear_combination hq | linear_combination -hq
    rw [h, Submodule.mem_bot] at hv1 hv2
    have a0 := congrFun hv1 0
    have a1 := congrFun hv1 1
    have b1 := congrFun hv2 1
    simp at a0 a1 b1
    exact hy0 0 0 0 rfl rfl rfl a0 b1 a1
  · have hv1 : (Pi.single 0 1 : Fin 2 → K) ∈ Wk := h ▸ Submodule.mem_top
    have hv2 : (Pi.single 1 1 : Fin 2 → K) ∈ Wk := h ▸ Submodule.mem_top
    rw [hmem] at hv1 hv2
    have a0 := congrFun hv1 0
    have a1 := congrFun hv1 1
    have b0 := congrFun hv2 0
    simp [ofCoord, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at a0 a1 b0
    exact hy0 0 0 0 rfl rfl rfl b0 a1 a0

end GlobalTheory.Sl2Ad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.VanishOrdOfKatoUse
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.VanishKato

theorem tw_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (a b : Γ →* kˣ) :
    tw (tw r a) b = tw r (b * a) := by
  ext1 s
  apply Units.ext
  simp only [tw_val, smul_smul, MonoidHom.mul_apply, Units.val_mul]

theorem cont_of_ker {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (f : Γ →* H) (U : Set Γ) (hU : IsOpen U) (h1 : 1 ∈ U)
    (h : ∀ s ∈ U, f s = 1) : Continuous f := by
  refine continuous_of_continuousAt_one f ?_
  refine (continuousAt_const (y := (1 : H))).congr ?_
  filter_upwards [hU.mem_nhds h1] with s hs
  exact (h s hs).symm

theorem cont_kills {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (M : ℕ) (hM : 1 ≤ M) (φ : G ℚ Ω →* (Qbar l)ˣ) (hφ : KillsMu M φ) : Continuous φ := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hM] using hζ
  refine cont_of_ker φ (⋂ ζ ∈ {ζ : Ω | ζ ^ M = 1}, (MulAction.stabilizer (Ω ≃ₐ[ℚ] Ω) ζ : Set (Ω ≃ₐ[ℚ] Ω)))
    (hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral ζ) ?_ ?_
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · intro s hs
    simp only [Set.mem_iInter] at hs
    exact hφ s fun ζ hζ => hs ζ hζ

end GlobalTheory.Ord2.VanishKato

namespace GlobalTheory.Ord2

end GlobalTheory.Ord2

end
end

