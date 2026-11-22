import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.WpBridge
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.AddLaw
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.StAddRight

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.AddDbl
section
noncomputable section

namespace PI.GalTorsConj.W

open Formalism.L2.Th1.F
open Filter Topology

namespace ZetaDoubling

open OriginCoordinatesAdd

def mu (L : PeriodPair) (z : ℂ) : ℂ :=
  (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) / L.derivWeierstrassP z

lemma hasDerivAt_two_mul (z : ℂ) : HasDerivAt (fun y : ℂ => 2 * y) 2 z := by
  simpa using (hasDerivAt_id z).const_mul (2 : ℂ)

lemma ev_two (L : PeriodPair) {z : ℂ} (h2 : 2 * z ∉ L.lattice) :
    ∀ᶠ z' in 𝓝 z, 2 * z' ∉ L.lattice := by
  have ho : IsOpen ((fun y : ℂ => 2 * y) ⁻¹' (L.lattice : Set ℂ)ᶜ) :=
    L.isClosed_lattice.isOpen_compl.preimage (continuous_const.mul continuous_id)
  exact ho.mem_nhds h2

lemma ev_self (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) : ∀ᶠ z' in 𝓝 z, z' ∉ L.lattice :=
  L.isClosed_lattice.isOpen_compl.mem_nhds hz

lemma derivWeierstrassP_ne_zero (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) (h2 : 2 * z ∉ L.lattice) :
    L.derivWeierstrassP z ≠ 0 := by
  intro h
  exact h2 ((pDerivZero L z hz).1 h)

lemma hasDerivAt_mu (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) (hy : L.derivWeierstrassP z ≠ 0) :
    HasDerivAt (mu L)
      ((12 * L.weierstrassP z * L.derivWeierstrassP z * L.derivWeierstrassP z
        - (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) * (6 * L.weierstrassP z ^ 2 - L.g₂ / 2))
        / L.derivWeierstrassP z ^ 2) z := by
  have hN := (((hasDerivAt_wp L hz).pow 2).const_mul (6 : ℂ)).sub_const (L.g₂ / 2)
  have hQ := hN.div (pSecond L z hz) hy
  refine (hQ.congr_of_eventuallyEq (f₁ := mu L)
    (Filter.Eventually.of_forall (fun y => rfl))).congr_deriv ?_
  simp only [Pi.pow_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  ring

lemma zetaDbl (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) (h2 : 2 * z ∉ L.lattice) :
    wZeta L (2 * z) = 2 * wZeta L z + mu L z / 2 := by
  have hy := derivWeierstrassP_ne_zero L hz h2
  have hs : wSigma L z ≠ 0 := fun h => hz ((sigmaZero L z).1 h)
  have hF := (sigmaLogDeriv L (2 * z) h2).comp z (hasDerivAt_two_mul z)
  have hG := (pSecond L z hz).neg.mul ((sigmaLogDeriv L z hz).pow 4)
  have heq : (fun y => -L.derivWeierstrassP y * wSigma L y ^ 4) =ᶠ[𝓝 z]
      (wSigma L ∘ fun y : ℂ => 2 * y) := by
    filter_upwards [ev_self L hz] with y hy'
    exact (sigmaDouble L y hy').symm
  have e := (hF.congr_of_eventuallyEq heq).unique hG
  rw [sigmaDouble L z hz] at e
  simp only [Pi.pow_apply, Pi.neg_apply, Nat.cast_ofNat, show (4 : ℕ) - 1 = 3 from rfl] at e
  have e2 : wZeta L (2 * z) * (-L.derivWeierstrassP z) * 2 =
      -(6 * L.weierstrassP z ^ 2 - L.g₂ / 2) + -L.derivWeierstrassP z * (4 * wZeta L z) := by
    apply mul_right_cancel₀ (pow_ne_zero 4 hs)
    linear_combination e
  have hy2 : (2 : ℂ) * L.derivWeierstrassP z ≠ 0 := mul_ne_zero two_ne_zero hy
  have e3 : wZeta L (2 * z) = (6 * L.weierstrassP z ^ 2 - L.g₂ / 2 +
      4 * L.derivWeierstrassP z * wZeta L z) / (2 * L.derivWeierstrassP z) := by
    rw [eq_div_iff hy2]
    linear_combination -e2
  rw [e3]
  unfold mu
  field_simp
  ring

lemma dblA (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) (h2 : 2 * z ∉ L.lattice) :
    L.weierstrassP (2 * z) = L.weierstrassP z -
      (12 * L.weierstrassP z * L.derivWeierstrassP z * L.derivWeierstrassP z
        - (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) * (6 * L.weierstrassP z ^ 2 - L.g₂ / 2))
        / L.derivWeierstrassP z ^ 2 / 4 := by
  have hy := derivWeierstrassP_ne_zero L hz h2
  have hL := (zetaHasDeriv L (2 * z) h2).comp z (hasDerivAt_two_mul z)
  have hR := ((zetaHasDeriv L z hz).const_mul (2 : ℂ)).add ((hasDerivAt_mu L hz hy).div_const 2)
  have heq : (fun y => 2 * wZeta L y + mu L y / 2) =ᶠ[𝓝 z] (wZeta L ∘ fun y : ℂ => 2 * y) := by
    filter_upwards [ev_self L hz, ev_two L h2] with y h1 h3
    exact (zetaDbl L h1 h3).symm
  have e := (hL.congr_of_eventuallyEq heq).unique hR
  linear_combination (-1 / 2 : ℂ) * e

lemma dbl_alg (x y g : ℂ) (hy : y ≠ 0) :
    x - (12 * x * y * y - (6 * x ^ 2 - g / 2) * (6 * x ^ 2 - g / 2)) / y ^ 2 / 4 = dblX x y g := by
  unfold dblX
  field_simp
  ring

lemma dblB (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) (h2 : 2 * z ∉ L.lattice) :
    L.weierstrassP (2 * z) = dblX (L.weierstrassP z) (L.derivWeierstrassP z) L.g₂ := by
  rw [dblA L hz h2]
  exact dbl_alg _ _ _ (derivWeierstrassP_ne_zero L hz h2)

end ZetaDoubling

open OriginCoordinatesAdd ZetaDoubling in

theorem dblLaw : DblLaw := by
  intro L z hz h2
  refine ⟨dblB L hz h2, ?_⟩
  have hy := derivWeierstrassP_ne_zero L hz h2
  have hL := (hasDerivAt_wp L h2).comp z (hasDerivAt_two_mul z)
  have hR := (((hasDerivAt_mu L hz hy).pow 2).div_const (4 : ℂ)).sub
    ((hasDerivAt_wp L hz).const_mul (2 : ℂ))
  have heq : (fun y => mu L y ^ 2 / 4 - 2 * L.weierstrassP y) =ᶠ[𝓝 z]
      (L.weierstrassP ∘ fun y : ℂ => 2 * y) := by
    filter_upwards [ev_self L hz, ev_two L h2] with y h1 h3
    show mu L y ^ 2 / 4 - 2 * L.weierstrassP y = L.weierstrassP (2 * y)
    rw [dblB L h1 h3]
    rfl
  have e := (hL.congr_of_eventuallyEq heq).unique hR
  simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one] at e
  unfold mu at e
  unfold dblY
  rw [← dbl_alg _ _ _ hy]
  linear_combination (1 / 2 : ℂ) * e

end PI.GalTorsConj.W

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.MulDefs
section
noncomputable section

namespace PI.GalTorsConj.W

open Formalism.L2.Th1.F

def TorsField : Prop :=
  ∀ (L : PeriodPair) (M : IntermediateField ℚ ℂ), L.g₂ ∈ M → L.g₃ ∈ M →
    ∃ M₁ : IntermediateField ℚ ℂ, M ≤ M₁ ∧ (∀ x ∈ M₁, IsAlgebraic M x) ∧
      ∀ (n : ℕ) (t : ℂ), 0 < n → (n : ℂ) * t ∈ L.lattice → t ∉ L.lattice →
        L.weierstrassP t ∈ M₁ ∧ L.derivWeierstrassP t ∈ M₁

def ExtRho : Prop :=
  ∀ (M M₁ : IntermediateField ℚ ℂ) (h : M ≤ M₁), (∀ x ∈ M₁, IsAlgebraic M x) →
    ∀ ρ : M →ₐ[ℚ] ℂ, ∃ ρ₁ : M₁ →ₐ[ℚ] ℂ, ∀ x : M, ρ₁ (IntermediateField.inclusion h x) = ρ x

def Descent : Prop :=
  ∀ (M M₁ : IntermediateField ℚ ℂ) (h : M ≤ M₁), (∀ x ∈ M₁, IsAlgebraic M x) →
    ∀ x : M₁, (∀ σ : M₁ →ₐ[ℚ] ℂ, (∀ y : M, σ (IntermediateField.inclusion h y) = (y : ℂ)) →
      σ x = (x : ℂ)) → (x : ℂ) ∈ M

def veluF (L : PeriodPair) (S : Finset ℂ) (z : ℂ) : ℂ :=
  L.weierstrassP z + ∑ P ∈ S, (L.weierstrassP (z + P) - L.weierstrassP P)

def veluD (L : PeriodPair) (S : Finset ℂ) (z : ℂ) : ℂ :=
  L.derivWeierstrassP z + ∑ P ∈ S, L.derivWeierstrassP (z + P)

def veluU (L : PeriodPair) (S : Finset ℂ) : Set ℂ :=
  {z | z ∉ L.lattice ∧ ∀ P ∈ S, z + P ∉ L.lattice}

def IsogD : Prop :=
  ∀ (L : PeriodPair) (c : ℂ) (S : Finset ℂ), c ≠ 0 → MulStable L c → IsKerReps L c S →
    ∀ z, c * z ∉ L.lattice → c ^ 3 * L.derivWeierstrassP (c * z) = veluD L S z

def TorsDense : Prop :=
  ∀ L : PeriodPair, Dense {t : ℂ | ∃ n : ℕ, 0 < n ∧ (n : ℂ) * t ∈ L.lattice}

def IsogODE : Prop :=
  ∀ (L : PeriodPair) (c : ℂ) (S : Finset ℂ), c ≠ 0 → (∀ P ∈ S, P ∉ L.lattice) →
    (∀ P ∈ S, ∀ Q ∈ S, P - Q ∈ L.lattice → P = Q) →
    (∀ z ∈ veluU L S, veluD L S z ^ 2 =
      4 * veluF L S z ^ 3 - c ^ 4 * L.g₂ * veluF L S z - c ^ 6 * L.g₃) →
    MulStable L c ∧ (∀ P ∈ S, c * P ∈ L.lattice) ∧
      ∀ z ∈ veluU L S, c * z ∉ L.lattice ∧ c ^ 2 * L.weierstrassP (c * z) = veluF L S z ∧
        c ^ 3 * L.derivWeierstrassP (c * z) = veluD L S z

def MulSt : Prop :=
  ∀ (L L' : PeriodPair) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (hg2 : L.g₂ ∈ M)
    (hg3 : L.g₃ ∈ M), L'.g₂ = ρ ⟨_, hg2⟩ → L'.g₃ = ρ ⟨_, hg3⟩ →
    ∀ c : ℂ, MulStable L c → ∀ hc : c ∈ M, ρ ⟨c, hc⟩ = c →
      ∀ t t', St L L' M ρ t t' → St L L' M ρ (c * t) (c * t')

end PI.GalTorsConj.W

end
end

