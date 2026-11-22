import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
import Formalism.LocalToGlobal.CharacterGerms.Bundle0023
import Formalism.LocalToGlobal.CharacterGerms.MaximalOfValuationGeOne
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Formalism.SharpRestriction.GrowthBounds.DataG
import Formalism.SharpRestriction.ParConsts

-- bundled from Formalism.SharpRestriction.GrowthBounds.MixedCoefficientClosed
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def pairSubst {τ : Type} (a b : κ → MvPowerSeries τ C) : Fin 2 × κ → MvPowerSeries τ C :=
  fun q => if q.1 = 0 then a q.2 else b q.2

def hAt (X : RawChart C d I κ) {τ : Type} (a b : κ → MvPowerSeries τ C) : MvPowerSeries τ C :=
  MvPowerSeries.subst (pairSubst a b) X.h

def IsPt (V : VF C) {τ : Type} (a : κ → MvPowerSeries τ C) : Prop :=
  ∀ i, MvPowerSeries.constantCoeff (a i) = 0 ∧ IntS V (a i)

def BiInt (X : RawChart C d I κ) (V : VF C) : Prop :=
  ∀ (τ : Type) [Finite τ] (n : ℕ) (a : ℕ → κ → MvPowerSeries τ C) (s c : κ → MvPowerSeries τ C),
    (∀ k, IsPt V (a k)) → IsPt V s → IsPt V c →
    (∀ i, MvPowerSeries.subst s (X.lg i) = ∑ k ∈ Finset.range n, MvPowerSeries.subst (a k) (X.lg i)) →
    IntS V (mvExp (∑ k ∈ Finset.range n, hAt X (a k) c - hAt X s c)) ∧
      IntS V (mvExp (∑ k ∈ Finset.range n, hAt X c (a k) - hAt X c s))

structure Basic (X : RawChart C d I κ) (V : VF C) : Prop where
  lg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0
  exlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C)
  lin : ∀ i (μ : κ →₀ ℕ), μ.degree ≤ 1 →
    MvPowerSeries.coeff μ (X.lg i) = MvPowerSeries.coeff μ (MvPowerSeries.X i : MvPowerSeries κ C)
  axis0 : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0
  axis1 : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 1) → MvPowerSeries.coeff e X.h = 0
  uint : ∀ g c i, V.Ge 0 (X.u g c i)
  hmis : ∀ (g : Fin 2) (c : I g) (q : JJ I g), X.ty g c ≠ X.ty (1 - g) q →
    V.Ge 0 (X.sg1 (X.u g c) (X.u (1 - g) q))

def NormRel (X : RawChart C d I κ) (l n : ℕ) (ζ : C) (γ δ : κ → PowerSeries C) : Prop :=
  ∀ i, PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (alongCv δ (X.lg i)) =
    ∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) (alongCv γ (X.lg i))

def phi (X : RawChart C d I κ) (l : ℕ) (ζ : C) (γ δ : κ → PowerSeries C) (v : κ → C) : PowerSeries C :=
  PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ (l ^ 2)) (alongCv δ (X.sg v)) -
    ∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) (alongCv γ (X.sg v))

def StepA (X : RawChart C d I κ) (V : VF C) (H : ∀ g, X.CartHyp V g) : Prop :=
  ∀ ζ : C, IsPrimitiveRoot ζ V.l → ∀ (g : Fin 2) (a : ZMod d) (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C),
    (RawChart.cart (H g)).Good a w x → (∀ c, V.MM ((RawChart.cart (H g)).V2 x c)) →
    ∃ γ δ : κ → PowerSeries C, IsCv V γ ∧ IsCv V δ ∧ NormRel X V.l (V.l ^ 2) ζ γ δ ∧
      (∀ i, V.MM (PowerSeries.coeff 1 (δ i))) ∧
      ∀ q : JJ I g, V.Ge 0 ((RawChart.cart (H g)).c0' x q) ∧
        V.MM (PowerSeries.coeff V.l (phi X V.l ζ γ δ (X.u (1 - g) q)) - (RawChart.cart (H g)).c0' x q) ∧
        V.MM (PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ (X.u (1 - g) q)) - (V.l : C) * x 2 (Sum.inr q))

def StepB (X : RawChart C d I κ) (V : VF C) : Prop :=
  ∀ ζ : C, IsPrimitiveRoot ζ V.l → ∀ (g : Fin 2) (q : JJ I g),
    ∃ (z ε : κ → PowerSeries C) (m : JJ I g → C), IsCv V z ∧ IsCv V ε ∧ NormRel X V.l V.l ζ z ε ∧
      (∀ i, PowerSeries.coeff 1 (z i) = X.u (1 - g) q i) ∧
      (∀ i, PowerSeries.coeff 1 (ε i) = ∑ q' : JJ I g, m q' * X.u (1 - g) q' i) ∧ ∀ q', V.Ge 0 (m q')

def LemC (X : RawChart C d I κ) (V : VF C) : Prop :=
  ∀ ζ : C, IsPrimitiveRoot ζ V.l → ∀ γ δ z ε : κ → PowerSeries C, IsCv V γ → IsCv V δ → IsCv V z → IsCv V ε →
    NormRel X V.l (V.l ^ 2) ζ γ δ → NormRel X V.l V.l ζ z ε → (∀ i, V.MM (PowerSeries.coeff 1 (δ i))) →
    V.MM (PowerSeries.coeff V.l (phi X V.l ζ γ δ fun i => PowerSeries.coeff 1 (z i)) ^ V.l -
      PowerSeries.coeff (V.l ^ 2) (phi X V.l ζ γ δ fun i => PowerSeries.coeff 1 (ε i)))

end SelfConjCharts

def GoodCurveClosed : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ), SelfConjCharts.Basic X V → ∀ H : ∀ g, X.CartHyp V g, SelfConjCharts.StepA X V H

def OtherGroupCurvesClosed : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ), SelfConjCharts.Basic X V → (∀ g, X.CartHyp V g) → SelfConjCharts.StepB X V

def MixedCoefficientClosed : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ), SelfConjCharts.Basic X V → SelfConjCharts.BiInt X V → SelfConjCharts.LemC X V

def BiadditiveOnColumns : Prop := AllSelf fun _ _ V _ _ _ _ X => SelfConjCharts.BiInt X V

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SelectionLemmas
section
noncomputable section

open scoped BigOperators

namespace Formalism.MainNotions.SelectionLemmas

open Formalism.MainNotions.G

variable {p : ℕ} {O : Type} [CommRing O]

def esymmOn {ι : Type} (VV : Finset ι) (κ : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ B ∈ VV.powersetCard k, ∏ v ∈ B, κ v

def monoN (G : GAtP p) (VV B : Finset (Fin G.P.nV)) (m : ℕ) (Sv : Fin G.P.nV → ℕ) (x : G.Fn) : G.Fn :=
  ((p : G.O) ^ (∑ v ∈ VV \ B, Sv v)) •
    ((B.sort (· ≤ ·)).foldr (fun v f => (G.yv v)^[m] ∘ f) id) x

def prodIdeal (G : GAtP p) (VV : Finset (Fin G.P.nV)) (m : ℕ) (Sv : Fin G.P.nV → ℕ)
    (M : Submodule G.O G.Fn) : Submodule G.O G.Fn :=
  Submodule.span G.O (⋃ B ∈ VV.powerset, monoN G VV B m Sv '' (M : Set G.Fn))

def tau {ι : Type} (VV : Finset ι) (m D : ℕ) (t : ι → ℕ) : ℕ := ∑ v ∈ VV, m * (t v + D + 1)

def IsSaturatedIn {X : Type} [AddCommGroup X] [Module O X] (M' M : Submodule O X) : Prop :=
  M' ≤ M ∧ ∀ (a : O) (x : X), x ∈ M → a ≠ 0 → a • x ∈ M' → x ∈ M'

def adm1 (_D : Formalism.BasicNotions.D7) (G : GAtP p) : Prop := G.TrivStab

def adm2 (_D : Formalism.BasicNotions.D7) (G : GAtP p) : Prop := G.FinClasses

def adm3 (_D : Formalism.BasicNotions.D7) (G : GAtP p) : Prop :=
  ∀ (u v : Fin G.P.nV) (F : G.Fn), G.yv u (G.yv v F) = G.yv v (G.yv u F)

def admitted (D : Formalism.BasicNotions.D7) (G : GAtP p) : Prop := adm1 D G ∧ adm2 D G ∧ adm3 D G

def Conclusion1 (_D : Formalism.BasicNotions.D7) (G : GAtP p) : Prop :=
  ∀ (VV : Finset (Fin G.P.nV)) (t Sv : Fin G.P.nV → ℕ) (Dd cStar S m : ℕ) (κ : Fin G.P.nV → ℝ),
    1 ≤ m → (∀ v ∈ VV, Sv v ≤ S) →
    (∀ v ∈ VV, LPprime (W := G.P.W v) (Qq := G.P.Qq v) (O := G.O) (Kf := G.Kf) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r
      (G.P.lam0 v) (t v) Dd (κ v) cStar) →
    let M := G.Mna
    let d : ℕ := G.dna
    let N := prodIdeal G VV m Sv M
    let τ : ℕ := tau VV m Dd t
    ((∀ β : ℕ, Formalism.G0.AllButLE (p : G.O) M N
        ⌊(d : ℝ) * (m : ℝ) ^ (β + 1) * esymmOn VV κ (β + 1)⌋₊ (τ + β * S)) ∧
      Formalism.G0.AllButLE (p : G.O) M N 0 (∑ v ∈ VV, Sv v)) ∧
    ((m : ℝ) * ∑ v ∈ VV, κ v ≤ 1 / 2 →
      let Sig : ℝ := (m : ℝ) * ∑ v ∈ VV, κ v
      let Nst := N ⊓ (Ideal.span {(p : G.O) ^ τ}) • M
      (∀ β : ℕ, (d : ℝ) * (m : ℝ) ^ (β + 1) * esymmOn VV κ (β + 1) ≤
          (d : ℝ) * Sig ^ (β + 1) / ((β + 1).factorial : ℝ)) ∧
      (∃ ℓ : ℕ, Module.length G.O (↥M ⧸ Submodule.comap M.subtype Nst) = ℓ ∧
        (ℓ : ℝ) ≤ ((Module.length G.O (G.O ⧸ Ideal.span {(p : G.O)})).toNat : ℝ) *
          ((d : ℝ) * τ + 2 * S * Sig * d)) ∧
      ∀ (M' : Submodule G.O G.Fn) (hM' : IsSaturatedIn M' M),
        Nst ⊓ M' ≤ (Ideal.span {(p : G.O) ^ τ}) • M' ∧
        Function.Injective (Submodule.mapQ (Submodule.comap M'.subtype Nst) (Submodule.comap M.subtype Nst)
          (Submodule.inclusion hM'.1) (fun _ hx => hx)) ∧
        ∀ (Y : Type) [AddCommGroup Y] [Module G.O Y] (K : G.Fn →ₗ[G.O] Y) (Z : Submodule G.O Y),
          N.map K ≤ Z → (Nst ⊓ M').map K ≤ Z)

def IntegralityFromMetric (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : Formalism.BasicNotions.GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    admitted D (D.gat u w h) → Conclusion1 D (D.gat u w h)

def RationalPlaneProblemLocal (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) (G : GAtP p), admitted D G → Conclusion1 D G

def FamilyGlobalDerivation {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), IntegralityFromMetric (Fm.D x i)

end Formalism.MainNotions.SelectionLemmas
end
end

