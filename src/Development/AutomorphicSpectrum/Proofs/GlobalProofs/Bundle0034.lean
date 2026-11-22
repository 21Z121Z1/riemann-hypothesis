import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0021
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0022
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0031
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0033
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0028
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0029
import ReciprocityTheory.Hypotheses.GalCoh
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.Transport
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ExistsApplyEqOfMemDec
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.Inertia
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0002
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0001
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0003

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuationAlt
section
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem stage (ι : Type) [Fintype ι] (r l : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (w : (Fin r → ℕ) → ℚ)
    (hr : r ≤ Fintype.card ι) (hl : 0 < l) (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j) (hw : GoodWeight l w) (k : ℕ) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s | -(k : ℝ) < s.re} ∧
      (∀ s : ℂ, 1 < s.re → G s = ∑' m, (w m : ℂ) * coneTerm a b s m) ∧
      ∀ p : ℕ, p < k → (∀ m : Fin r → ℕ, ∃ q : ℚ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (q : ℝ)) →
        ∃ q : ℚ, G (-(p : ℂ)) = (q : ℂ) := by
  classical
  obtain ⟨Q, x, cs, u, hu, hcs, hsum⟩ := GlobalTheory.T.weight_sum_as_finite_differences r l (Fintype.card ι * k + 2) w hl hw
  refine ⟨fun s => ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m, ?_, ?_, ?_⟩
  · have h : ∀ q ∈ (Finset.univ : Finset Q), DifferentiableOn ℂ
        (fun s => ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m) {s : ℂ | -(k : ℝ) < s.re} :=
      fun q _ => GlobalTheory.T.cone_series_differentiable_left_strip ι r a b ha hb k (Fintype.card ι * k + 2) (cs q) (u q) le_rfl (hu q) (hcs q)
    have h2 := DifferentiableOn.sum h
    have h3 : (fun s : ℂ => ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m) =
        ∑ q, fun s : ℂ => ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m := by
      funext s
      simp [Finset.sum_apply]
    rw [h3]
    exact h2
  · intro s hs
    exact (hsum (coneTerm a b s) (GlobalTheory.T.cone_series_summable_right_half_plane ι r a b hr ha hb s hs)).symm
  · intro p hp hrat
    have hN : Fintype.card ι * p < Fintype.card ι * k + 2 := by
      have := Nat.mul_le_mul_left (Fintype.card ι) hp.le
      omega
    choose q hq using fun t => GlobalTheory.T.shintani_values_negative_integers_rational ι r a b (u t) (cs t) (Fintype.card ι * k + 2) p hN (hcs t) hrat
    refine ⟨∑ t, q t, ?_⟩
    simp only [Rat.cast_sum]
    exact Finset.sum_congr rfl fun t _ => hq t

theorem abelContinuation : AbelContinuation := by
  intro ι _ r l a b w hr hl ha hb hw
  choose G hG hGeq hGrat using fun k : ℕ => stage ι r l a b w hr hl ha hb hw k
  obtain ⟨T, hT, hTG⟩ := GlobalTheory.T.analytic_continuation_from_strips (fun s => ∑' m, (w m : ℂ) * coneTerm a b s m) G hG hGeq
  refine ⟨T, hT, ?_, ?_⟩
  · intro s hs
    have hs0 : -((0 : ℕ) : ℝ) < s.re := by
      rw [Nat.cast_zero, neg_zero]
      linarith
    rw [hTG 0 s hs0, hGeq 0 s hs]
    have hper : ∀ (i : Fin r) (m : Fin r → ℕ), w (m + Pi.single i l) = w m := by
      obtain ⟨h1, -⟩ := hw
      exact fun i m => h1 m i
    obtain ⟨C, hC⟩ := GlobalTheory.T.periodic_weight_bounded r l w hl hper
    have hcone := GlobalTheory.T.cone_series_summable_right_half_plane ι r a b hr ha hb s hs
    refine Summable.hasSum (Summable.of_norm ?_)
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) (hcone.norm.mul_left C)
    have hwm : ‖(w m : ℂ)‖ ≤ C := by simpa using hC m
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hwm (norm_nonneg _)
  · intro p hrat
    have hp : -((p + 1 : ℕ) : ℝ) < (-(p : ℂ)).re := by norm_num
    rw [hTG (p + 1) _ hp]
    exact hGrat (p + 1) p (Nat.lt_succ_self p) hrat

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.DualityForAbsGal
section
open CategoryTheory MonoidalCategory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel NumberField IsDedekindDomain Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.Hypotheses₂

attribute [local instance 2000] Rep.hV2

theorem dualityFor_absGal (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (hK : FiniteDimensional ℚ_[p] K) (l : ℕ) [Fact l.Prime] (r : ℕ)
    (χ : (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) →* (ZMod (l ^ r))ˣ)
    (hχ : ∀ (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (ζ : PadicAlgCl p), ζ ^ (l ^ r) = 1 →
      σ ζ = ζ ^ ((χ σ : ZMod (l ^ r)).val))
    (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation (ZMod (l ^ r)) (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) M)
    (hrho : ContAction rho) : ReciprocityTheory.Neutral.Bridge.DualityFor χ rho hrho := by
  obtain ⟨hsep, _, _, hloc, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gcField p K hK
  have hl : (l ^ r : ℕ) ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ r) := ⟨hl⟩
  have : CharZero K := algebraRat.charZero K
  have hn : ((l ^ r : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hl
  obtain ⟨e⟩ := nonempty_addEquiv_galRootsOfUnity (K := K) (Ksep := PadicAlgCl p) hn
  have hD : ∀ (g : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (m : ZMod (l ^ r)),
      e.symm ((χ g : ZMod (l ^ r)) * m) =
        (galRootsOfUnity.{0} K (PadicAlgCl p) (l ^ r)).ρ g (e.symm m) := by
    intro g m
    have key : ∀ x : Additive (rootsOfUnity (l ^ r) (PadicAlgCl p)),
        (galRootsOfUnity.{0} K (PadicAlgCl p) (l ^ r)).ρ g x =
          (χ g : ZMod (l ^ r)).val • x := by
      intro x
      rw [galRootsOfUnity_ρ_apply]
      apply Additive.toMul.injective
      rw [toMul_ofMul, toMul_nsmul]
      apply Subtype.ext
      apply Units.ext
      rw [coe_galRootsOfUnityHom_apply, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val]
      refine hχ g _ ?_
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 x.toMul.2, Units.val_one]
    refine Eq.trans ?_ (key _).symm
    refine Eq.trans ?_ (map_nsmul e.symm _ m)
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
  exact PositivityTheory.LocalTateOrthogonality.Gcoh.tate_core PositivityTheory.LocalTateOrthogonality.Gcoh.gcRep PositivityTheory.LocalTateOrthogonality.Gcoh.gc0
    PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 (galRootsOfUnity.{0} K (PadicAlgCl p) (l ^ r))
    (localDualityHypotheses hn)
    (fun A _ _ hA => finite_cohomology_galois_top K (PadicAlgCl p) hn A hA 1)
    χ e.symm hD M rho hrho

theorem localTateDuality : ReciprocityTheory.Gal.LocalTateDuality := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ A rho v _ hA hrho
  obtain ⟨p, hp, hpv⟩ := exists_prime_mem_asIdeal v
  haveI : Fact p.Prime := ⟨hp⟩
  have hval : A.valuation ((p : ℕ) : Ω) < 1 := by
    have := (hA ((p : ℕ) : 𝓞 F)).2 hpv
    simpa using this
  obtain ⟨ι, h⟩ := ReciprocityTheory.Neutral.Cmp.exists_compat F A hval
  let E : ReciprocityTheory.Neutral.Cmp.GK F ι ≃ₜ* Dec (F := F) A := ReciprocityTheory.Neutral.Cmp.equiv h
  let χ : Dec (F := F) A →* (ZMod (l ^ r))ˣ := (cycMod F Ω l r).comp (Dec (F := F) A).subtype
  have hχ : ∀ (σ : ReciprocityTheory.Neutral.Cmp.GK F ι) (ζ : PadicAlgCl p), ζ ^ (l ^ r) = 1 →
      σ ζ = ζ ^ (((χ.comp (E : ReciprocityTheory.Neutral.Cmp.GK F ι →* Dec (F := F) A)) σ :
        (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
    intro σ ζ hζ
    have e1 := ReciprocityTheory.Neutral.Cmp.cycZ_res (F := F) ι l σ
    have e3 : (χ.comp (E : ReciprocityTheory.Neutral.Cmp.GK F ι →* Dec (F := F) A)) σ =
        Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom
          (cyclotomicCharacter (PadicAlgCl p) l (σ : PadicAlgCl p ≃+* PadicAlgCl p)) := by
      rw [← e1]
      rfl
    rw [e3]
    exact cyclotomicCharacter.spec (L := PadicAlgCl p) l (σ : PadicAlgCl p ≃+* PadicAlgCl p) ζ hζ
  have hD := dualityFor_absGal p (ReciprocityTheory.Neutral.Cmp.Kloc F ι)
    (ReciprocityTheory.Neutral.Cmp.finiteDimensional_Kloc ι) l r
    (χ.comp (E : ReciprocityTheory.Neutral.Cmp.GK F ι →* Dec (F := F) A)) hχ M
    (rho.comp (E : ReciprocityTheory.Neutral.Cmp.GK F ι →* Dec (F := F) A))
    (ReciprocityTheory.Neutral.Bridge.contAction_comp E hrho)
  exact ReciprocityTheory.Neutral.Bridge.DualityFor.of_comp E χ hrho hD

end GlobalTheory.CompanionTheory.Hypotheses₂
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsShintaniConeDomainStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_shintani_cone_domain : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
  ∃ (ι : Type) (_ : Fintype ι) (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), IsConeDomain 𝔣 r v := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_coneDomain | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_coneDomain | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_coneDomain <;> assumption)
end

