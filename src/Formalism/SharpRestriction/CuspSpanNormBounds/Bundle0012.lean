import Formalism.SharpRestriction.CuspSpanNormBounds.ThinScalesBound
import Formalism.SharpRestriction.CuspSpanNormBounds.ChainLength
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0011

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.JointEvBounds
section
namespace Formalism.MainNotions

theorem JointEigenvalueBoundsFromAnyDatum.first_hypothesis_of_lifting (D : Formalism.BasicNotions.D7) (C : ℝ) (h : ThinScalesBound.aux₃ D C) : JointEigenvalueBoundsFromAnyDatum.adm1 D :=
  fun F _ _ _ E _ _ _ _ M hM => h.2.1 F E M hM

theorem JointEigenvalueBoundsFromAnyDatum.second_hypothesis_of_lifting (D : Formalism.BasicNotions.D7) (C : ℝ) (h : ThinScalesBound.aux₃ D C) : JointEigenvalueBoundsFromAnyDatum.adm2 D :=
  fun F _ _ _ E _ _ _ _ M hM => h.2.2 F E M hM

theorem JointEigenvalueBoundsFromAnyDatum.integrality_of_commutation (D : Formalism.BasicNotions.D7) (C : ℝ) (h : ThinScalesBound.aux₃ D C) : JointEigenvalueBoundsFromAnyDatum.adm3 D :=
  fun hk => (h.1 hk).1

theorem JointEigenvalueBoundsFromAnyDatum.fourth_hypothesis_of_lifting (D : Formalism.BasicNotions.D7) (C : ℝ) (h : ThinScalesBound.aux₃ D C) : JointEigenvalueBoundsFromAnyDatum.ArchimedeanSignatureMatching D C :=
  fun hk => (h.1 hk).2.1

theorem JointEigenvalueBoundsFromAnyDatum.sizes_bound_of_log_estimates (D : Formalism.BasicNotions.D7) (C : ℝ) (h : ThinScalesBound.aux₃ D C) : JointEigenvalueBoundsFromAnyDatum.adm5 D :=
  fun hk => (h.1 hk).2.2.1

theorem JointEigenvalueBoundsFromAnyDatum.lifting_bounds_of_theorem_c (D : Formalism.BasicNotions.D7) (C : ℝ) (h : ThinScalesBound.aux₃ D C) : JointEigenvalueBoundsFromAnyDatum.adm10 D :=
  fun hk => (h.1 hk).2.2.2

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

theorem JointEvBounds.ownEv_of_all {P : ∀ x, Fm.Ix x → Prop} (h : ∀ x i, P x i) :
    S.OwnEv Fm fun _ _ x i => P x i :=
  ⟨0, fun x _ i => h x i⟩

theorem JointEigenvalueBoundsFromAnyDatum.theta_norm_family_of_linked (h : ThinScalesBound.OrbitValuationBound Fm) : JointEigenvalueBoundsFromAnyDatum.admF1 Fm :=
  let ⟨C, h⟩ := h; JointEvBounds.ownEv_of_all Fm fun x i => JointEigenvalueBoundsFromAnyDatum.first_hypothesis_of_lifting _ C (h x i)

theorem JointEigenvalueBoundsFromAnyDatum.theta_condition_family_of_linked (h : ThinScalesBound.OrbitValuationBound Fm) : JointEigenvalueBoundsFromAnyDatum.admF2 Fm :=
  let ⟨C, h⟩ := h; JointEvBounds.ownEv_of_all Fm fun x i => JointEigenvalueBoundsFromAnyDatum.second_hypothesis_of_lifting _ C (h x i)

theorem JointEigenvalueBoundsFromAnyDatum.stabiliser_family_of_definite (h : ThinScalesBound.OrbitValuationBound Fm) : JointEigenvalueBoundsFromAnyDatum.admF3 Fm :=
  let ⟨C, h⟩ := h; JointEvBounds.ownEv_of_all Fm fun x i => JointEigenvalueBoundsFromAnyDatum.integrality_of_commutation _ C (h x i)

theorem JointEigenvalueBoundsFromAnyDatum.injectivity_family_of_theorem (h : ThinScalesBound.OrbitValuationBound Fm) : JointEigenvalueBoundsFromAnyDatum.admF4 Fm :=
  let ⟨C, h⟩ := h; ⟨C, JointEvBounds.ownEv_of_all Fm fun x i => JointEigenvalueBoundsFromAnyDatum.fourth_hypothesis_of_lifting _ C (h x i)⟩

theorem JointEigenvalueBoundsFromAnyDatum.family_ev_bound_of_source (h : ThinScalesBound.OrbitValuationBound Fm) : JointEigenvalueBoundsFromAnyDatum.admF5 Fm :=
  let ⟨C, h⟩ := h; JointEvBounds.ownEv_of_all Fm fun x i => JointEigenvalueBoundsFromAnyDatum.sizes_bound_of_log_estimates _ C (h x i)

theorem JointEigenvalueBoundsFromAnyDatum.familyRowsCount_of_thinScalesBound (h : ThinScalesBound.OrbitValuationBound Fm) : JointEigenvalueBoundsFromAnyDatum.FamilyRowsCountHypothesis Fm :=
  let ⟨C, h⟩ := h; JointEvBounds.ownEv_of_all Fm fun x i => JointEigenvalueBoundsFromAnyDatum.lifting_bounds_of_theorem_c _ C (h x i)

theorem JointEigenvalueBoundsFromAnyDatum.AdmF_of {Y : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, S.TermTie (Fm.D x i)}
    (X : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), S.LocalSplitGroups.TermLocs (Fm.D x i) (Y x hx i))
    (cN : ∀ x (i : Fm.Ix x), (Fm.D x i).what₂.Word → (Fm.D x i).what₂.Word → ℝ)
    (h : ThinScalesBound.OrbitValuationBound Fm) (h6 : JointEigenvalueBoundsFromAnyDatum.admF6 Fm) (h7 : JointEigenvalueBoundsFromAnyDatum.admF7 Fm) (h8 : JointEigenvalueBoundsFromAnyDatum.admF8 Fm X cN)
    (h9 : JointEigenvalueBoundsFromAnyDatum.admF9 Fm X) : JointEigenvalueBoundsFromAnyDatum.AdmF Fm X cN :=
  ⟨JointEigenvalueBoundsFromAnyDatum.theta_norm_family_of_linked Fm h, JointEigenvalueBoundsFromAnyDatum.theta_condition_family_of_linked Fm h, JointEigenvalueBoundsFromAnyDatum.stabiliser_family_of_definite Fm h, JointEigenvalueBoundsFromAnyDatum.injectivity_family_of_theorem Fm h,
    JointEigenvalueBoundsFromAnyDatum.family_ev_bound_of_source Fm h, h6, h7, h8, h9, JointEigenvalueBoundsFromAnyDatum.familyRowsCount_of_thinScalesBound Fm h⟩

end Family

end Formalism.MainNotions
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.PairOfInputs
section
open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.DoubleDerivativeSmoothness

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

def KApproxAt (σ : Mx k r → (H →L[ℂ] H)) : Prop :=
  ∀ v ∈ smoothVecs (k := k) (r := r) σ, ∀ Ws : List (List (Mx k r)), (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) →
    ∀ ε : ℝ, 0 < ε → ∃ v' : H, IsKFinHpk (k := k) (r := r) σ v' ∧ v' ∈ smoothVecs (k := k) (r := r) σ ∧
      v' - v ∈ smoothVecs (k := k) (r := r) σ ∧ ‖v' - v‖ < ε ∧ ∀ w ∈ Ws, ‖dsigW σ w (v' - v)‖ < ε

def DecDDAt (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) (w0 : H) : Prop :=
  ∀ u ∈ DDsp σ w0, ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) ∧
    ∀ x ∈ smoothVecs (k := k) (r := r) σ, Integrable (FI z c π σ u x) (μW.prod μN) ∧
      ∫ p, ‖FI z c π σ u x p‖ ∂(μW.prod μN) ≤ C * (Ws.map fun w => ‖dsigW σ w x‖).sum

def ExtDDOf : Prop :=
  ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN : Measure (Mt k r))
    (σ : Mx k r → (H →L[ℂ] H)) (w0 : H),
    DDSmoothAt σ w0 → KApproxAt σ → DecDDAt z c π μW μN σ w0 → ExtDDAt z c π μW μN σ w0

def KZeroOf : Prop :=
  ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H)),
    KApproxAt σ → KZeroAt z c π σ

def DDInputs (D : D7) (Ch Cg Cq : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (lam0 μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (ka b κ : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx D.R.k D.R.rS → (H →L[ℂ] H)) (μG νq νq' : Measure (Mt D.R.k D.R.rS)) (w0 : H),
    NearbyChamberParameters D Ch Cg Cq L lam0 μ ka b κ → IsDSHpk D.R.k D.R.rS L.ε μ σ → IsLowUnitH D.R.k D.R.rS L.ε μ σ w0 →
    IsHaarOn (UH (Hpk D.R.k D.R.rS)) μG → IsQuotMeas μG (muSof L.μW L.μN) νq → IsQuotMeas μG (muSof L.μW' L.μN) νq' →
      DDSmoothAt σ w0 ∧ KApproxAt σ ∧ DecDDAt L.z L.c L.π L.μW L.μN σ w0 ∧ DecDDAt L.z' L.c L.π' L.μW' L.μN σ w0

end Formalism.MainNotions.DoubleDerivativeSmoothness
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.TrD
section
open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

variable {k r : ℕ}

def trD (L : LocBessel k r) (κ τ : ℝ) (κN₁ : ENNReal)
    (hz : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z))
    (hz' : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z'))
    (hπ : IsHCTypeW k r ((τ : ℂ) • L.z) L.u (fun x => L.π (cjI k r κ τ x)))
    (hπ' : IsHCTypeW k r ((τ : ℂ) • L.z') L.u' (fun x => L.π' (cjI k r κ τ x)))
    (hμW : IsHaarOn (UWset k r ((τ : ℂ) • L.z)) (L.μW.map (cjT k r κ τ)) ∧ L.μW.map (cjT k r κ τ) Set.univ = 1)
    (hμW' : IsHaarOn (UWset k r ((τ : ℂ) • L.z')) (L.μW'.map (cjT k r κ τ)) ∧
      L.μW'.map (cjT k r κ τ) Set.univ = 1) : LocBessel k r where
  ε := L.ε
  lam := L.lam
  hlam := L.hlam
  z := (τ : ℂ) • L.z
  z' := (τ : ℂ) • L.z'
  hz := hz
  hz' := hz'
  u := L.u
  u' := L.u'
  Hs := L.Hs
  σ := L.σ
  hσ := L.hσ
  Wp := L.Wp
  π := fun x => L.π (cjI k r κ τ x)
  hπ := hπ
  Wq := L.Wq
  π' := fun x => L.π' (cjI k r κ τ x)
  hπ' := hπ'
  c := (κ : ℂ) * L.c
  μW := L.μW.map (cjT k r κ τ)
  μW' := L.μW'.map (cjT k r κ τ)
  hμW := hμW
  hμW' := hμW'
  κN := κN₁

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end

