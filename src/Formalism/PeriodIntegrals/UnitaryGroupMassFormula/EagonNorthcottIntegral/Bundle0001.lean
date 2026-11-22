import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.YHom

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.DivisionPartitionTotal
section
noncomputable section

namespace PI.EagonNorthcottZ

open MvPolynomial PI.EagonNorthcott

def DivisionKillsEarlier : Prop := ∀ (D : ℕ) (ι : Fin D → Fin D ⊕ Fin D), Function.Injective ι → ∀ (m l : Fin D), l < m → ∀ f : P D,
  Dop ι m (X (ι l) * f) = 0

def DivisionCommutesLater : Prop := ∀ (D : ℕ) (ι : Fin D → Fin D ⊕ Fin D), Function.Injective ι → ∀ (m l : Fin D), m < l → ∀ f : P D,
  Dop ι m (X (ι l) * f) = X (ι l) * Dop ι m f

def DivisionPartitionUpto : Prop := ∀ (D : ℕ) (ι : Fin D → Fin D ⊕ Fin D), Function.Injective ι → ∀ (m : Fin D) (f : P D),
  ∑ i ∈ Finset.univ.filter (· < m), X (ι i) * Dop ι i f + Dop ι m (X (ι m) * f) = f

def DivisionPartitionTotal : Prop := ∀ (D : ℕ) (ι : Fin D → Fin D ⊕ Fin D), Function.Injective ι → ∀ f : P D,
  (∀ μ ∈ f.support, ∃ i, 0 < μ (ι i)) → ∑ i, X (ι i) * Dop ι i f = f

def DGy : Prop := ∀ (D a : ℕ) (i : Fin D) (f : P D), YHom (a + 1) f → YHom a (Dop Sum.inr i f)

def DGy0 : Prop := ∀ (D : ℕ) (i : Fin D) (f : P D), YHom 0 f → Dop Sum.inr i f = 0

def DGx : Prop := ∀ (D a : ℕ) (i : Fin D) (f : P D), YHom a f → YHom a (Dop Sum.inl i f)

def NoX {D : ℕ} (f : P D) : Prop := f ∈ Set.range (rename Sum.inr : S D → P D)

def IsCyc {D : ℕ} (a j : ℕ) (ω : W D) : Prop := Gr a j ω ∧ K ys ω = 0

def IsZL {D : ℕ} (a j : ℕ) (ω : W D) : Prop := IsCyc a j ω ∧ ∀ J, NoX (ω J)

def Phi {D r : ℕ} (b : Fin r → W D) (v : Fin r → S D) : W D := fun J => ∑ k, inx (v k) * b k J

def IsZBasis {D : ℕ} (a j : ℕ) {r : ℕ} (b : Fin r → W D) : Prop :=
  LinearIndependent ℤ b ∧ ∀ ω, IsZL a j ω ↔ ω ∈ Submodule.span ℤ (Set.range b)

def b0 {D m : ℕ} (e : Fin m → Fin D → ℕ) : Fin m → W D := fun k J => if J = ∅ then ∏ i, ys i ^ e k i else 0

def LBasis : Prop := ∀ D a j : ℕ, ∃ (r : ℕ) (b : Fin r → W D), IsZBasis a j b

def LEnum : Prop := ∀ D a : ℕ, ∃ (m : ℕ) (e : Fin m → Fin D → ℕ), Function.Injective e ∧ ∀ α : Fin D → ℕ, α ∈ Set.range e ↔ ∑ i, α i = a

def LBasis0 : Prop := ∀ (D a m : ℕ) (e : Fin m → Fin D → ℕ), Function.Injective e →
  (∀ α : Fin D → ℕ, α ∈ Set.range e ↔ ∑ i, α i = a) → IsZBasis a 0 (b0 e)

def LVan : Prop := ∀ D a j : ℕ, max D 1 ≤ j → ∀ ω : W D, IsZL a j ω → ω = 0

def LInj : Prop := ∀ (D a j r : ℕ) (b : Fin r → W D), IsZBasis a j b → Function.Injective (Phi b)

def LRan : Prop := ∀ (D a j r : ℕ) (b : Fin r → W D), IsZBasis a j b → ∀ ω, (∃ v, Phi b v = ω) ↔ IsCyc a j ω

def LCt : Prop := ∀ (D a j : ℕ) (i : Fin D) (ω : W D), IsZL a (j + 1) ω → IsZL a j (ct i ω)

def LKx : Prop := ∀ (D : ℕ) (ω : W D), K xs ω = fun J => ∑ i, xs i * ct i ω J

end PI.EagonNorthcottZ
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.ExactSecondDegreeZero
section
noncomputable section

namespace PI.EagonNorthcottZ

open MvPolynomial PI.EagonNorthcott

def Anti : Prop := ∀ (D : ℕ) (t u : Fin D → P D) (ω : W D), K t (K u ω) = - K u (K t ω)

def Sq : Prop := ∀ (D : ℕ) (t : Fin D → P D) (ω : W D), K t (K t ω) = 0

def KLin : Prop := ∀ (D : ℕ) (t : Fin D → P D) (ω η : W D), K t (ω - η) = K t ω - K t η ∧ K t (-ω) = - K t ω

def GrLin : Prop := ∀ (D a j : ℕ) (ω η : W D), Gr a j ω → Gr a j η → Gr a j (ω - η) ∧ Gr a j (-ω)

def GrX : Prop := ∀ (D a j : ℕ) (ω : W D), Gr a (j + 1) ω → Gr a j (K xs ω)

def GrY : Prop := ∀ (D a j : ℕ) (ω : W D), Gr a (j + 1) ω → Gr (a + 1) j (K ys ω)

def AugK : Prop := ∀ (D : ℕ) (η : W D), mu (K xs η ∅) = mu (K ys η ∅)

def ExX : Prop := ∀ (D a j : ℕ) (ω : W D), Gr a (j + 1) ω → K xs ω = 0 → ∃ ζ, Gr a (j + 2) ζ ∧ K xs ζ = ω

def ExY : Prop := ∀ (D a j : ℕ) (ω : W D), Gr (a + 1) (j + 1) ω → K ys ω = 0 → ∃ θ, Gr a (j + 2) θ ∧ K ys θ = ω

def ExYz : Prop := ∀ (D j : ℕ) (ω : W D), Gr 0 (j + 1) ω → K ys ω = 0 → ω = 0

def ExactSecondDegreeZero : Prop := ∀ (D a : ℕ) (ω : W D), Gr (a + 1) 0 ω → ∃ θ, Gr a 1 θ ∧ K ys θ = ω

def Aug0 : Prop := ∀ (D : ℕ) (ω : W D), Gr 0 0 ω → mu (ω ∅) = 0 → ω = 0

def Main : Prop := ∀ (D a j : ℕ) (ω : W D), Gr a (j + 1) ω → K ys ω = 0 → K xs ω = 0 →
  ∃ η, Gr a (j + 2) η ∧ K ys η = 0 ∧ K xs η = ω

def EagonNorthcottIntegralExactness : Prop := ∀ (D a : ℕ) (ω : W D), Gr a 0 ω → mu (ω ∅) = 0 → ∃ η, Gr a 1 η ∧ K ys η = 0 ∧ K xs η = ω

def Frame : Prop := ∀ D a : ℕ, ∃ (n : ℕ → ℕ) (e : Fin (n 0) → Fin D → ℕ)
    (C : ∀ j, Matrix (Fin (n j)) (Fin (n (j + 1))) (Fin D → ℤ)) (Φ : ∀ j, (Fin (n j) → S D) → W D),
  Shape D a n e C ∧ (∀ j, Function.Injective (Φ j)) ∧ (∀ j, Φ j 0 = 0) ∧
    (∀ j ω, (∃ v, Φ j v = ω) ↔ (Gr a j ω ∧ K ys ω = 0)) ∧
    (∀ j v, Φ j (dmap (X : Fin D → S D) (C j) v) = K xs (Φ (j + 1) v)) ∧
    ∀ v, aug (X : Fin D → S D) e v = mu (Φ 0 v ∅)

def AugRange : Prop := ∀ (D a m : ℕ) (e : Fin m → Fin D → ℕ), (∀ α : Fin D → ℕ, α ∈ Set.range e ↔ ∑ i, α i = a) →
  LinearMap.range (aug (X : Fin D → S D) e) = Ideal.span (Set.range (X : Fin D → S D)) ^ a

end PI.EagonNorthcottZ
end
end

