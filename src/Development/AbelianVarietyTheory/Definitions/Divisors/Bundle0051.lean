import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopRankPowers
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsMultiHomogeneousFixFirstBlock
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.WeilRangeOfAll
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWACase

open GlobalTheory.SWLit

def WeilRange : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → 2 * n < m →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ Φ ∈ schA F κ, FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ}) →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  ∀ g, Cont.HolValueAt
    (fun s => Eis.cosetSum (siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype) (ratU σ J₂)
      (flatOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K (fun g => om (1, g) Φ 0)
        (((m : ℂ) - (n : ℂ)) / 2) s) g)
    (((m : ℂ) - (n : ℂ)) / 2) ((if n < m then 1 else 2 : ℂ) * ⨍ h in 𝓕, thetaSum F (om (h, g) Φ) ∂ν)

def MidRange : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → n < m ∧ m ≤ 2 * n →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ Φ ∈ schA F κ, FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ}) →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  ∀ g, Cont.HolValueAt
    (fun s => Eis.cosetSum (siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype) (ratU σ J₂)
      (flatOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K (fun g => om (1, g) Φ 0)
        (((m : ℂ) - (n : ℂ)) / 2) s) g)
    (((m : ℂ) - (n : ℂ)) / 2) ((if n < m then 1 else 2 : ℂ) * ⨍ h in 𝓕, thetaSum F (om (h, g) Φ) ∂ν)

def LowRange : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → m ≤ n →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ Φ ∈ schA F κ, FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ}) →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  ∀ g, Cont.HolValueAt
    (fun s => Eis.cosetSum (siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype) (ratU σ J₂)
      (flatOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K (fun g => om (1, g) Φ 0)
        (((m : ℂ) - (n : ℂ)) / 2) s) g)
    (((m : ℂ) - (n : ℂ)) / 2) ((if n < m then 1 else 2 : ℂ) * ⨍ h in 𝓕, thetaSum F (om (h, g) Φ) ∂ν)

theorem range_cases (n m : ℕ) : 2 * n < m ∨ (n < m ∧ m ≤ 2 * n) ∨ m ≤ n := by omega

theorem weilRange_of_all (h : GlobalTheory.Published.SiegelWeilAnisotropicWitt) : WeilRange :=
  fun F E _ _ _ _ _ σ hCM hU ψ hψ n m hn hm _ => h F E σ hCM hU ψ hψ n m hn hm

theorem midRange_of_all (h : GlobalTheory.Published.SiegelWeilAnisotropicWitt) : MidRange :=
  fun F E _ _ _ _ _ σ hCM hU ψ hψ n m hn hm _ => h F E σ hCM hU ψ hψ n m hn hm

theorem lowRange_of_all (h : GlobalTheory.Published.SiegelWeilAnisotropicWitt) : LowRange :=
  fun F E _ _ _ _ _ σ hCM hU ψ hψ n m hn hm _ => h F E σ hCM hU ψ hψ n m hn hm

theorem all_of_ranges (h₁ : WeilRange) (h₂ : MidRange) (h₃ : LowRange) : GlobalTheory.Published.SiegelWeilAnisotropicWitt := by
  intro F E _ _ _ _ _ σ hCM hU ψ hψ n m hn hm
  rcases range_cases n m with h | h | h
  · exact h₁ F E σ hCM hU ψ hψ n m hn hm h
  · exact h₂ F E σ hCM hU ψ hψ n m hn hm h
  · exact h₃ F E σ hCM hU ψ hψ n m hn hm h

theorem all_iff_ranges : GlobalTheory.Published.SiegelWeilAnisotropicWitt ↔ WeilRange ∧ MidRange ∧ LowRange :=
  ⟨fun h => ⟨weilRange_of_all h, midRange_of_all h, lowRange_of_all h⟩, fun h => all_of_ranges h.1 h.2.1 h.2.2⟩

example (n m : ℕ) :
    ¬ (2 * n < m ∧ n < m ∧ m ≤ 2 * n) ∧ ¬ (2 * n < m ∧ m ≤ n) ∧ ¬ ((n < m ∧ m ≤ 2 * n) ∧ m ≤ n) := by omega

example (n : ℕ) (hn : 1 ≤ n) :
    (∃ m, 1 ≤ m ∧ 2 * n < m) ∧ (∃ m, 1 ≤ m ∧ n < m ∧ m ≤ 2 * n) ∧ ∃ m, 1 ≤ m ∧ m ≤ n :=
  ⟨⟨2 * n + 1, by omega⟩, ⟨2 * n, by omega⟩, ⟨n, by omega⟩⟩

example (n m : ℕ) :
    (2 * n < m → (if n < m then 1 else 2 : ℂ) = 1) ∧ (n < m ∧ m ≤ 2 * n → (if n < m then 1 else 2 : ℂ) = 1) ∧
    (m ≤ n → (if n < m then 1 else 2 : ℂ) = 2) :=
  ⟨fun h => if_pos (by omega), fun h => if_pos h.1, fun h => if_neg (by omega)⟩

example (n m : ℕ) : 2 * n < m ↔ (n : ℝ) / 2 < ((m : ℝ) - (n : ℝ)) / 2 := by
  constructor
  · intro h
    have : (2 * n : ℝ) < m := by exact_mod_cast h
    linarith
  · intro h
    have : (2 * n : ℝ) < m := by linarith
    exact_mod_cast this

end GlobalTheory.SWACase

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers

namespace GlobalTheory.HSCore

structure Quoted : Prop where
  kv : GlobalTheory.Published.KawamataViehweg
  l2 : GlobalTheory.Published.L2ExtensionLogCanonical
  gaga : GlobalTheory.Published.SerreHolomorphicSections
  nef : GlobalTheory.Published.NefNumerics
  chow : GlobalTheory.Published.ChowFormExists
  chowInt : GlobalTheory.Published.ChowFormIntExists
  chowCut : GlobalTheory.Published.ChowFormHyperplaneSection
  len : GlobalTheory.Published.ProperIntersectionLength

variable {F : Type} [Field F] [NumberField F]

def rho0 (T : Tuple F) (l : ℕ) : ℝ := 8 * T.D * T.del * T.n * l * T.abelian₂

def rho1 (T : Tuple F) (l : ℕ) : ℝ := rho0 T l * (1 + 1 / (8 * T.D * T.del))

structure WellChosen (T : Tuple F) (h : ℝ) (l : ℕ) (E : Type) [Field E] [NumberField E] [Algebra F E]
    (s : Fin T.D → Fin T.N → E) : Prop where
  lt_l : T.theta h ^ 20 < l
  l_le : (l : ℝ) ≤ 2 * T.theta h ^ 20
  mem : ∀ i, s i ∈ T.latticeOver E
  good : T.IsGoodSection E s
  card : ((T.geomPts E (T.linSection E s)).ncard : ℤ) = T.del
  ne : ∀ i, s i ≠ 0
  norm_le : ∀ i (τ : E →+* ℂ), T.normAt τ (s i) ≤ rho1 T l
  lower : ((T.D : ℝ) + 1) * T.del * h + T.D * T.del * Real.log (rho0 T l) -
    T.del * (((T.D : ℝ) + 1) * (harmonic (T.N - 1) : ℝ) / 2 + Real.log 2 / T.del + 1 / 8) ≤
      T.cycleHeight E (T.linSection E s)
  upper : T.cycleHeight E (T.linSection E s) ≤ ((T.D : ℝ) + 1) * T.del * h + T.del * ∑ i, T.meanLogNorm (s i)
  residue : ∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ → l ≤ Ideal.absNorm P

def DelPos : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → T.Birational → 0 < T.del

def Choice : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), IsTotallyComplex F → T.IsAdelic → ∀ h, T.IsHeight h →
    ∃ (l : ℕ) (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra F E) (s : Fin T.D → Fin T.N → E),
      WellChosen T h l E s

def Split (T : Tuple F) (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E) : Prop :=
  ∀ x : Sp (AlgebraicClosure E) ⟶ (T.linSection E s).subscheme,
    x ≫ (T.linSection E s).subschemeι ≫ (T.toLinSys.baseChange E).str = spMap (algebraMap E (AlgebraicClosure E)) →
    ∃ x₀ : Sp E ⟶ (T.linSection E s).subscheme, x = spMap (algebraMap E (AlgebraicClosure E)) ≫ x₀

structure Coord {K : Type} [Field K] [NumberField K] (G : Geo K) {s : Fin G.D → Fin G.N → K} (hs : G.IsGood s) (δ : ℕ) where

  ev : ∀ j : ℕ, G.SecOn s j ≃ₗ[K] (Fin δ → K)

  y : Fin δ → Fin G.N → K

  c₂ : (K →+* ℂ) → Fin δ → ℝ
  y_ne : ∀ p, y p ≠ 0
  c₂_pos : ∀ σ p, 0 < c₂ σ p
  c₂_conj : ∀ σ p, c₂ ((starRingEnd ℂ).comp σ) p = c₂ σ p
  mul : ∀ (j : ℕ) (u : Fin G.N → K) (g : G.SecOn s j),
    ev (j + 1) (mulSecOn G.isLB₂ G.isLB (G.comb u) (Nat.cast_succ j).symm g) = fun p => (∑ k, u k * y p k) * ev j g p
  sq : ∀ (j : ℕ) (σ : K →+* ℂ) (m : ℕ) (c : Fin m → ℂ) (g : Fin m → G.SecOn s j),
    csq (hs.normOn j) σ c g =
      ∑ p, ‖∑ i, c i * σ (ev j (g i) p)‖ ^ 2 / (c₂ σ p * archSize (G.A σ) (fun k => σ (y p k)) ^ j) ^ 2

def Claim (X : Data F) (C h J : ℝ) : Prop :=
  0 ≤ X.z ∧ X.z ≤ 1 ∧
    (1 - X.z) * (X.T * h - 3 * ((X.D : ℝ) + 1) * |h| - J - C * (X.D : ℝ) ^ 2 * (X.logRho C h + Real.log X.T) -
        ((X.T : ℝ) + X.D + 1) * Real.log X.beta - ((X.T : ℝ) + (X.D : ℝ) ^ 2) * (X.g + 2)) -
      X.z * (X.T * (Real.log 2 + X.logRho C h + Real.log X.beta / 2) + Real.log X.LamD + Real.log X.LamT) ≤
    X.degM X.T / X.d

def HSBound : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (X : Data F), X.Hyp → ∀ h, X.IsHeight h → ∀ C, 26 ≤ C → 0 < X.d ∧ Claim X C h X.J

def RankLow : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : Geo F), IsNef F G.LA → IsBig F G.LA → ∀ T : ℕ,
    ((T - 1).choose G.D : ℤ) * G.del ≤ Module.finrank F (G.global T)

def KerRes : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Geo K), IsNef K G.LA → IsBig K G.LA →
    ∀ (s : Fin G.D → Fin G.N → K), G.IsGood s → ∀ l : ℕ, G.D ≤ l + 1 →
      ∀ f ∈ Fil (G.ideal s) 1 (G.global (l + 1)), ∃ m : Fin G.D → G.Sec l, (∀ i, m i ∈ G.global l) ∧ f = ∑ i, G.mulW l (s i) (m i)

def FilMono : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Geo K), IsNef K G.LA → IsBig K G.LA →
    ∀ (s : Fin G.D → Fin G.N → K), G.IsGood s → ∀ (a j l : ℕ) (h : j + a = l), G.D ≤ j →
      ∀ f ∈ Fil (G.ideal s) a (G.global l), ∃ m : MonoDeg (Fin G.D) a → G.Sec j,
        (∀ α, m α ∈ G.global j) ∧ f = ∑ α, mulPow G s h α (m α)

def Extension : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Geo K) (s : Fin G.D → Fin G.N → K) (hs : G.IsGood s), (∀ i, s i ≠ 0) →
    ∀ (σ : K →+* ℂ) (j : ℕ), G.D ≤ j → ExtensionBound σ hs j

example (X : Data F) (C h J : ℝ) (H : Claim X C h J) : X.z ≤ 1 := H.2.1

end GlobalTheory.HSCore
end
end

