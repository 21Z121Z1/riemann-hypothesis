import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0039
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0037
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0036
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0032
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0014
import Development.DiscreteGroups.GlobalIrreducibility.ExistsUniformizerValuation

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzGalOne
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module ValuativeRel

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def ResIso : Prop :=
  ∀ (L E' Ω : Type) [Field L] [NumberField L] [Field E'] [NumberField E'] [Field Ω] [Algebra L Ω] [Algebra E' Ω]
    [IsAlgClosure L Ω] [IsAlgClosure E' Ω] (g : ℕ) [Fact g.Prime] (n : ℕ) (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 L)) (hv : IsPlaceOver A v) (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w'),
    normV v = g ^ n → normV w' = g ^ n →
    ∀ (K : Type) [Field K] (red : 𝓞 E' →+* K), Function.Surjective red → RingHom.ker red = w'.asIdeal →
    ∃ κ : 𝓀[v.adicCompletion L] ≃+* K, ∀ (u : 𝒪[v.adicCompletion L]) (y : 𝓞 L) (x : 𝓞 E'),
      Valued.v ((u : v.adicCompletion L) - algebraMap L (v.adicCompletion L) (y : L)) < 1 →
      A.valuation (algebraMap L Ω (y : L) - algebraMap E' Ω (x : E')) < 1 →
      κ (IsLocalRing.residue 𝒪[v.adicCompletion L] u) = red x

theorem lpOfChar_congr {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) {χ χ' : Weil h →* ℂˣ} (e : χ = χ')
    (hχ : IsSmooth χ) (hχ' : IsSmooth χ') : WD.lpOfChar h χ hχ = WD.lpOfChar h χ' hχ' := by
  subst e; rfl

theorem regular_ne_one {g n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] {ξ : Kˣ →* ℂˣ}
    (hξ : GlobalTheory.Published.IsRegularChar g n ξ) : ξ ≠ 1 := by
  intro h1
  have := hξ 0 1 (by omega) (by omega) (by rw [h1, one_pow, one_pow])
  omega

theorem nmChar_pow {g : ℕ} [Fact g.Prime] {K : Type} [Field K] [Algebra (ZMod g) K] (χ₀ : (ZMod g)ˣ →* ℂˣ) :
    nmChar K χ₀ ^ g = nmChar K χ₀ := by
  ext z
  simp only [MonoidHom.pow_apply, nmChar, MonoidHom.comp_apply, ← map_pow]
  congr 2
  ext
  simp [ZMod.pow_card]

theorem regular_mul_nm_ne_one {g n : ℕ} [Fact g.Prime] (hn : 2 ≤ n) {K : Type} [Field K] [Algebra (ZMod g) K]
    {ξ : Kˣ →* ℂˣ} (hξ : GlobalTheory.Published.IsRegularChar g n ξ) (χ₀ : (ZMod g)ˣ →* ℂˣ) : ξ * nmChar K χ₀ ≠ 1 := by
  intro h1
  have hξe : ξ = (nmChar K χ₀)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have := hξ 0 1 (by omega) (by omega) (by rw [hξe, pow_zero, pow_one, pow_one, inv_pow, nmChar_pow])
  omega

end DiscreteGroups.sglob.DzType

end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.ExistsColChar
section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix DiscreteGroups.sglob.LConvGenM DiscreteGroups.sglob.LConvGenF

namespace DiscreteGroups.sglob.LConvGenR

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GL (Fin n) k) V) (ψ : AddChar k Circle)

theorem exists_col_char {c : kˣ} (hc : HasConductor ψ c) (hs : IsSmooth π) (j : ℕ) (hj : j < n)
    (h0 : KN π ψ (j + 1) ≠ ⊤) (S : Finset (Fin n)) : ∃ ξ : Fin n → k, KN π ψ (j + 1) ⊔ KUS π ψ j S ξ ≠ ⊤ := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by rw [KUS_empty, sup_bot_eq]; exact h0⟩
  | insert a S ha ih =>
    obtain ⟨ξ, hξ⟩ := ih
    let σ : k → V →ₗ[ℂ] V := fun t => π (colU j (Pi.single a t))
    have hadd : ∀ s t, σ (s + t) = σ s * σ t := fun s t => by
      simp only [σ]; rw [Pi.single_add, colU_add, map_mul]
    have hW : ∀ t, ∀ w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j S ξ, σ t w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j S ξ :=
      fun t w hw => W_stable π ψ j S ξ _ hw
    obtain ⟨ξa, hξa⟩ := exists_character_sup_ne_top ψ σ hc hadd _ hW (fun v => smooth_col π hs j hj a v) hξ
    refine ⟨Function.update ξ a ξa, fun htop => hξa (eq_top_iff.2 ?_)⟩
    rw [← htop]
    refine sup_le (le_sup_left.trans le_sup_left) (Submodule.span_le.2 ?_)
    rintro _ ⟨c, hcS, v, rfl⟩
    set cS := Function.update c a 0 with hcS'
    have hcS0 : ∀ r ∉ S, cS r = 0 := by
      intro r hr
      by_cases hra : r = a
      · subst hra; simp [cS]
      · rw [hcS', Function.update_of_ne hra]; exact hcS r (by simp [hra, hr])
    have hsplit : c = Pi.single a (c a) + cS := by
      funext r
      by_cases hra : r = a
      · subst hra; simp [cS]
      · simp [cS, hra, Pi.single_apply]
    have hdot : dotj j (Function.update ξ a ξa) c =
        dotj j (Function.update ξ a ξa) (Pi.single a (c a)) + dotj j ξ cS := by
      conv_lhs => rw [hsplit]
      rw [dotj_add, dotj_update j ξ cS a ξa (by simp [cS])]
    have e : π (colU j c) v - ((ψ (dotj j (Function.update ξ a ξa) c) : Circle) : ℂ) • v =
        σ (c a) (π (colU j cS) v - ((ψ (dotj j ξ cS) : Circle) : ℂ) • v) +
        ((ψ (dotj j ξ cS) : Circle) : ℂ) • (σ (c a) v -
          ((ψ (dotj j (Function.update ξ a ξa) (Pi.single a (c a))) : Circle) : ℂ) • v) := by
      have hcol : π (colU j c) v = σ (c a) (π (colU j cS) v) := by
        conv_lhs => rw [hsplit]
        rw [colU_add, map_mul, Module.End.mul_apply]
      rw [hcol, hdot, AddChar.map_add_eq_mul, Circle.coe_mul, map_sub, map_smul, smul_sub, smul_smul,
        mul_comm ((ψ (dotj j (Function.update ξ a ξa) (Pi.single a (c a))) : Circle) : ℂ)]
      abel
    show _ ∈ _
    rw [e]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (hW _ _ (Submodule.mem_sup_right
      (Submodule.subset_span ⟨cS, hcS0, v, rfl⟩)))) (Submodule.smul_mem _ _ ?_)
    rw [dotj_single]
    by_cases haj : a.val < j
    · rw [if_pos haj, Function.update_self]
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨c a, v, rfl⟩)
    · rw [if_neg haj, AddChar.map_zero_eq_one, Circle.coe_one, one_smul]
      simp only [σ]
      rw [colU_single_of_ge j (by omega), map_one, Module.End.one_apply, sub_self]
      exact Submodule.zero_mem _

end DiscreteGroups.sglob.LConvGenR
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.SuppConst
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
  {ψ₀ : AddChar (ZMod g) Circle} {ψ : AddChar (w.adicCompletion E) Circle}

include hi in

theorem supp_const (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) (h0 : ψ₀ ≠ 1) {n : ℕ}
    (τ : FDRep ℂ (Gn g n)) (hτ : IsCusp τ.character) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (φ : τ →ₗ[ℂ] V)
    (hφ : ∀ (κ : GL (Fin n) ℤ_[g]) (x : τ),
      φ (τ.ρ (red g n κ) x) = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ)) (φ x))
    (L : Module.Dual ℂ V) (hL : IsFunctional ψ π L) (x : τ) (d : Fin n → ℤ)
    (h : L (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ x)) ≠ 0) : ∀ a b, d a = d b := by
  have hcons : ∀ (j : ℕ) (hj : j + 1 < n), d ⟨j, by omega⟩ = d ⟨j + 1, hj⟩ := by
    intro j hj
    rcases lt_trichotomy (d ⟨j, by omega⟩) (d ⟨j + 1, hj⟩) with hlt | heq | hgt
    · exact absurd (step_up i hi hψ h0 τ π φ hφ L hL x d ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl hlt) h
    · exact heq
    · exact absurd (step_down i hi hψ τ hτ π φ hφ L hL x d ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl hgt) h
  have hall : ∀ (j : ℕ) (hj : j < n), d ⟨j, hj⟩ = d ⟨0, by omega⟩ := by
    intro j
    induction j with
    | zero => intro hj; rfl
    | succ j ih => intro hj; rw [← hcons j hj, ih (by omega)]
  intro a b
  exact (hall a.val a.isLt).trans (hall b.val b.isLt).symm

end DiscreteGroups.sglob.DzRed
end
end

