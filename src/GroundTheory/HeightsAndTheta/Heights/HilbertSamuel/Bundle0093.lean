import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0082
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0083
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0062
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0063
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0025

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullSectionIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def PullSectionIntegral.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
      ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, ∀ j : Fin (D + 1), aeval y (L j) ≠ 0 →
        s / aeval y (L j) ^ (q * τ) ∈
          integralClosure (Algebra.adjoin ℚ (Set.range fun i => aeval y (L i) / aeval y (L j))) Ω

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsZeroCocycleSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ZeroCocycleSection.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ),
    ∀ v ∈ KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 0,
      ∃ s ∈ chartLat y a 1, GenOnFibres.secCoch y ℤ s a = v

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.VanishOfVanishNsmul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem vanish_of_vanish_nsmul {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M]
    [Module S M] [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (N : K → ℤ) {q : ℕ}
    (hq : 1 ≤ q)
    (h : ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → Subsingleton (KH.cechHc ι 𝓜 (e + (c * q) • N) 1))
    (e : K → ℤ) : ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → Subsingleton (KH.cechHc ι 𝓜 (e + c • N) 1) := by
  choose c₀ hc₀ using fun r : ℕ => h (e + r • N)
  refine ⟨((Finset.range q).sup c₀ + 1) * q, fun c hc => ?_⟩
  have hr : c % q ∈ Finset.range q := Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
  have h1 : c₀ (c % q) ≤ (Finset.range q).sup c₀ := Finset.le_sup (f := c₀) hr
  have h2 : (Finset.range q).sup c₀ + 1 ≤ c / q := (Nat.le_div_iff_mul_le (by omega)).mpr hc
  have h3 := hc₀ (c % q) (c / q) (by omega)
  have e' : e + (c % q) • N + (c / q * q) • N = e + c • N := by
    rw [add_assoc, ← add_smul, Nat.mod_add_div' c q]
  rwa [e'] at h3

theorem KleimanVarietyH1Generation.proof (hK : KH.KAmpStatement) (hDev : H1VanishingDevissage.Statement)
    (hGen : GenerationOfH1Vanishing.Statement) : KleimanVarietyH1Generation.Statement := by
  intro F _ K _ _ ι _ _ I Q α b a hI hQ hN hb ha
  refine hGen F K ι Q _ inferInstance (hDev F K ι Q _ inferInstance fun P hP hQP e => ?_)

  obtain ⟨D, hKD, hD⟩ := Targets.ContractMixedField.exists_dim hP
  have hPd : IsProjVarF P (D - Fintype.card K) := ⟨hP, by rw [hD, Nat.sub_add_cancel hKD]⟩
  have hNP : KH.NefOnF I P α := fun W hW hPW => hN W hW (hQP.trans hPW)

  obtain ⟨q, hq, -, hvan⟩ := hK F K ι I P _ α b a hI hPd hNP hb ha
  exact vanish_of_vanish_nsmul _ _ hq hvan e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

