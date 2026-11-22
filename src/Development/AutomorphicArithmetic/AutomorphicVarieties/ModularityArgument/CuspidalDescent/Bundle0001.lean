import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.DescUse
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.Sd

namespace UpperTheory.V.Z.Desc

def RegWt {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (π : CuspSub E n) : Prop :=
  ∀ v : InfinitePlace E, ∃ (φ : E →+* ℂ) (lam : DomWeight n), InfinitePlace.mk φ = v ∧ StrictAnti lam.w ∧ π.HasInfChar φ (infOfWeight lam)

def DescUse : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (p : ℕ), p.Prime → ∀ S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), S.Finite →
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∈ S → IsSplitAt w) →
      (∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → w.under (𝓞 (maximalRealSubfield E)) ∈ S) →
    ∀ n : ℕ, 2 ≤ n → n ≤ 4 → ∀ π : CuspSub E n, (CG.mk π).IsRegAlg → RegWt π → GlobalTheory.ContraPair.DualIsConj π →
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∉ S → ∃ B, (CG.mk π).HasSat w B) →
      ∃ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ ∧ (∀ w : HeightOneSpectrum (𝓞 E), ¬ IsSplitAt w → IsUnramU σ w) ∧
        ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, IsSplitAt w →
          ∃ (τ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ),
            IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ ∧ GlobalTheory.LFun.HasSatGL w τ.ρ B ∧ (CG.mk π).HasSat w B

structure EigVec {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (c : HeightOneSpectrum (𝓞 F) → ℕ) (ω : (Af F)ˣ →* ℂˣ) (m : HeightOneSpectrum (𝓞 F) → Fin 2 → ℤ)
    (mu : HeightOneSpectrum (𝓞 F) → ℂ) (π : TR.CuspSub F 2) (x : π.V) : Prop where
  ne : x ≠ 0
  eig : ∀ w, x ∈ Hi.fixd (π.locRep w) (K1 w (c w)) ∧ Uop w (π.locRep w) (c w) x = mu w • x
  cen : ∀ z, π.finPart (Matrix.GeneralLinearGroup.scalar (Fin 2) z) x = (ω z : ℂ) • x
  inf : ∀ w, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ τ : F →+* Qbar l, EmbAt w τ →
    π.HasInfChar (InfinitePlace.mk (ι.toRingHom.comp τ)) (infOf (m w))

def WcUse : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (l : ℕ) [Fact l.Prime], l ≠ 2 → Module.finrank ℚ F = 2 →
    (∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → Ideal.absNorm w.asIdeal = l ∧ ((l : ℕ) : 𝓞 F) ∉ w.asIdeal ^ 2) →
    ∀ (ι : Qbar l ≃+* ℂ) (s : ℤ) (c : HeightOneSpectrum (𝓞 F) → ℕ), {w | c w ≠ 0}.Finite → (∃ u, c u ≠ 0 ∧ normV u = 2) →
    ∀ (ω : (Af F)ˣ →* ℂˣ) (m m' : HeightOneSpectrum (𝓞 F) → Fin 2 → ℤ) (mu : HeightOneSpectrum (𝓞 F) → ℂ) (π : TR.CuspSub F 2) (x : π.V),
    EigVec ι c ω m mu π x →
    (∀ w, c w ≠ 0 → ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ‖ι.symm (mu w)‖ = 1) →
    (∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → c w = 1 ∧ m w 1 + 2 ≤ m w 0 ∧ m w 0 + m w 1 = s ∧
      ‖ι.symm (mu w) * (normV w : Qbar l) ^ m w 0‖ = 1 ∧
      m' w 1 + 2 ≤ m' w 0 ∧ m' w 0 + m' w 1 = s ∧ ((l : ℤ) - 1) ∣ m' w 0 - m w 0) →
    ∃ (mu' : HeightOneSpectrum (𝓞 F) → ℂ) (π' : TR.CuspSub F 2) (y : π'.V), EigVec ι c ω m' mu' π' y ∧
      (∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ‖ι.symm (mu' w) - ι.symm (mu w)‖ < 1) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal →
        ‖ι.symm (mu' w) * (normV w : Qbar l) ^ m' w 0 - ι.symm (mu w) * (normV w : Qbar l) ^ m w 0‖ < 1

def WcGal : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    Module.finrank ℚ F = 2 →
    (∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → Ideal.absNorm w.asIdeal = l ∧ ((l : ℕ) : 𝓞 F) ∉ w.asIdeal ^ 2) →
    ∀ (ι : Qbar l ≃+* ℂ) (ξ : G F Ω →* (Qbar l)ˣ) s c m a π r, OrdForm ι ξ s c m a π r →
    (∃ u, c u ≠ 0 ∧ normV u = 2) → ∀ m' : HeightOneSpectrum (𝓞 F) → Fin 2 → ℤ,
    (∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → m' w 1 + 2 ≤ m' w 0 ∧ m' w 0 + m' w 1 = s ∧ ((l : ℤ) - 1) ∣ m' w 0 - m w 0) →
    ∃ π' r', OrdForm ι ξ s c m' a π' r' ∧ ∀ g i, ‖(r' g : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.coeff i -
      (r g : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.coeff i‖ < 1

end UpperTheory.V.Z.Desc
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.IrrComp
section
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.LocGL UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Gu
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem irreducible_component_of_speh {E : Type} [Field E] [NumberField E] [IsCMField E] {n m : ℕ} (U : Submodule ℂ (UA E n → ℂ))
    (hn : ∑ _i : Fin 1, m = n) (P : CuspSub E n) (w : HeightOneSpectrum (𝓞 E))
    (ρ : SmIrr (GL (Fin n) (w.adicCompletion E))) (σ : SmIrr (GL (Fin m) (w.adicCompletion E)))
    (hρ : P.IsLocComp w ρ) (hs : IsSpeh (cl ρ) 1 σ.ρ)
    (hc : IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd (N := fun _ : Fin 1 => m) hn w fun _ => σ))
    (τ : SmIrr (GL (Fin n) (w.adicCompletion E))) (hτ : P.IsLocComp w τ) :
    IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ := by
  obtain rfl : m = n := by simpa using hn
  obtain ⟨φ₀⟩ := GlobalTheory.LocGL.nonempty_equiv_multiProd_one σ.smooth
    (GlobalTheory.SmGL.stdBlocks (fun _ : Fin 1 => m) hn)
    (fun a i => Fin.ext (by rw [GlobalTheory.SmGL.stdBlocks_val]; obtain rfl := Subsingleton.elim a 0; simp))
  obtain ⟨hd, h1⟩ := hs
  obtain ⟨hd', h2⟩ := GlobalTheory.LocGL.isSpeh_one (cl ρ)
  obtain ⟨e⟩ := h1.unique h2
  obtain ⟨u⟩ := GlobalTheory.CuspRep.LocUniq.isLocComp_unique P w τ ρ hτ hρ
  let q : τ.ρ.Equiv (locProd (N := fun _ : Fin 1 => m) hn w fun _ => σ) :=
    (u.trans ((IrrGL.equivOf ρ.ρ ρ.smooth ρ.irred).trans e)).trans φ₀
  obtain ⟨-, f, f0, fm, fe⟩ := hc
  refine ⟨τ.irred, f ∘ₗ q.toLinearMap, fun h0 => f0 (LinearMap.ext fun v => ?_), fun v => fm _, fun x v => ?_⟩
  · obtain ⟨u', rfl⟩ := q.toLinearEquiv.surjective v
    exact LinearMap.congr_fun h0 u'
  · exact (congrArg f (LinearMap.congr_fun (q.isIntertwining' _) v)).trans (fe x _)

theorem UpperTheory.V.Z.Desc.irrComp :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (U : Submodule ℂ (UA E n → ℂ)) (hn : ∑ _i : Fin 1, 1 * n = n) (P : CuspSub E n)
    (w : HeightOneSpectrum (𝓞 E)) (ρ : SmIrr (GL (Fin n) (w.adicCompletion E))) (σ : SmIrr (GL (Fin (1 * n)) (w.adicCompletion E))),
    P.IsLocComp w ρ → IsSpeh (cl ρ) 1 σ.ρ →
    IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) (locProd (N := fun _ : Fin 1 => 1 * n) hn w fun _ => σ) →
    ∀ τ, P.IsLocComp w τ → IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ := by
  intro E _ _ _ n U hn P w ρ σ hρ hs hc τ hτ
  exact irreducible_component_of_speh U hn P w ρ σ hρ hs hc τ hτ
end

