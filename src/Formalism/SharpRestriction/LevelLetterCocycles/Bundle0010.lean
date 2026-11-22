import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.LocalRingCardinality.DataParams₂
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
section
noncomputable section

namespace Formalism.MainNotions.AdmissibleParameterJ

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual NumberField IsDedekindDomain

variable {D : D7}

section Sets

variable (D)

def c0 : ℚ := ((D.R.t : ℚ) - 1) / 2

def sz (j : ℕ) (ρ : D.what₂.Tau) : ℚ :=
  if h : j - 1 < D.R.m then (D.hc ρ).e ⟨j - 1, h⟩ else 0

def cloudJ (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ :=
  {q | ∃ a : Fin (D.R.k - 1), q = sz D j ρ + (D.hc ρ).v a + c0 D}

def lowJ (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ :=
  {q | ∃ a : Fin D.R.m, q = sz D j ρ - (D.hc ρ).b a + c0 D}

def blockJ : Set ℚ := {q | ∃ c : ℕ, c < D.R.t ∧ q = c}

def Jp (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ := cloudJ D j ρ ∪ lowJ D j ρ ∪ blockJ D

def refl (q : ℚ) : ℚ := ((D.R.t : ℚ) - 1) - q

def reflS (S : Set ℚ) : Set ℚ := {q | refl D q ∈ S}

def Jm (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ := reflS D (Jp D j ρ)

def JJ (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ := if up then Jp D j ρ else Jm D j ρ

def cloudT (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ :=
  if up then cloudJ D j ρ else reflS D (cloudJ D j ρ)

def lowT (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ :=
  if up then lowJ D j ρ else reflS D (lowJ D j ρ)

def JW (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : Set ℚ := cloudT D up j ρ ∪ lowT D up j ρ

def dualS (S : Set ℚ) : Set ℚ := {q | -q - 1 ∈ S}

def PPm (j : ℕ) (ρ : D.what₂.Tau) : Multiset ℚ :=
  (Finset.univ.val.map fun a : Fin (D.R.k - 1) => (D.hc ρ).v a) +
  (Finset.univ.val.map fun a : Fin D.R.m => -(D.hc ρ).b a) +
  ((Finset.range D.R.t).val.map fun c : ℕ => -sz D j ρ + ((D.R.t : ℚ) + 1) / 2 - ((c : ℚ) + 1))

end Sets

section Emb

variable (D)

def PlaceOf (ρ : D.what₂.Tau) (g : D.R.GG) : Prop :=
  ((D.eTau ρ : D.R.Psi) : D.R.GG) = g ∨
    ((D.eTau ρ : D.R.Psi) : D.R.GG) * D.R.cc = g

def TypeU (ep : Bool) (g : D.R.GG) : Prop := (g ∈ D.R.Psi ↔ ep = true)

def ReadAt (i : D.nd.Loc) (τ₀ : D.host.E →+* Qbar (D.nd.l i)) (g : D.R.GG)
    (ρ : D.what₂.Tau) : Prop :=
  (D.naut.iotaQC i).toRingHom.comp τ₀ = D.host.emb g ∧ PlaceOf D ρ g

variable {D}

def gEmb {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) :
    D.host.E →+* Qbar (D.nd.l i) :=
  (C.LL.1.val.toRingHom).comp (τ.toRingHom.comp (Br.cEw D.nbr i w hw))

end Emb

section Stmt

variable (D)

def rQ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    GE D.nd →* GL (Fin D.R.nV) (Qbar (D.nd.l i)) :=
  mapRep (iotaOQ D.nd D.naut i) (r x)

def rankOneCharacterQbar (i : D.nd.Loc) : GE D.nd →* GL (Fin 1) (Qbar (D.nd.l i)) :=
  mapRep (iotaOQ D.nd D.naut i) (PairedCharacterCondition.chiGL i)

open Classical in

def hodgeTateJumpsAtModulesForSign (ep : Bool) : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1),
      ∃ (g : D.R.GG) (ρ : D.what₂.Tau), ReadAt D i (gEmb C τ) g ρ ∧
        (∀ (x : D.nd.X i) (a : ℤ),
          (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) τ a ↔
            (a : ℚ) ∈ JJ D (decide (TypeU D ep g)) (D.nd.j i) ρ) ∧
          multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) τ a =
            (if (a : ℚ) ∈ JJ D (decide (TypeU D ep g)) (D.nd.j i) ρ then 1 else 0) ∧
          (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) τ a ↔
            (a : ℚ) ∈ dualS (JJ D (decide (TypeU D ep g)) (D.nd.j i) ρ)) ∧
          multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) τ a =
            (if (a : ℚ) ∈ dualS (JJ D (decide (TypeU D ep g)) (D.nd.j i) ρ) then 1 else 0)) ∧
        ∀ (ρπ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), π ∈ D.nd.Z i →
          TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρπ π → ∀ a : ℤ,
          (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρπ π))) τ a ↔
            (a : ℚ) ∈ JW D (decide (TypeU D ep g)) (D.nd.j i) ρ) ∧
          multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρπ π))) τ a =
            (if (a : ℚ) ∈ JW D (decide (TypeU D ep g)) (D.nd.j i) ρ then 1 else 0) ∧
          (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρπ π))) τ a ↔
            (a : ℚ) ∈ dualS (JW D (decide (TypeU D ep g)) (D.nd.j i) ρ)) ∧
          multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρπ π))) τ a =
            (if (a : ℚ) ∈ dualS (JW D (decide (TypeU D ep g)) (D.nd.j i) ρ) then 1 else 0)

def ConclusionJa : Prop := ∃ ep : Bool, hodgeTateJumpsAtModulesForSign D ep

variable {D} (L : SizeData₂ D)

def CloudCentreDistance : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ρ : D.what₂.Tau,
    (∀ q ∈ cloudJ D j ρ, ((sz D j ρ : ℚ) : ℝ) ≤ ((q - c0 D : ℚ) : ℝ) ∧
      ((q - c0 D : ℚ) : ℝ) ≤ (sz D j ρ : ℝ) + L.Sc) ∧
    (∀ q ∈ lowJ D j ρ, ((D.R.t : ℚ) + 3) / 2 ≤ |q - c0 D| ∧ ((|q - c0 D| : ℚ) : ℝ) ≤ L.etaSz) ∧
    (∀ q ∈ blockJ D, |q - c0 D| ≤ c0 D) ∧
    (cloudJ D j ρ).ncard = D.R.k - 1 ∧ (lowJ D j ρ).ncard = D.R.m ∧ (Jp D j ρ).ncard = D.R.nV

def jcCondition : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ρ : D.what₂.Tau,
    (∀ q ∈ lowJ D j ρ, (-L.etaSz + (c0 D : ℝ) ≤ (q : ℝ) ∧ q ≤ -2) ∨
      ((D.R.t : ℚ) + 1 ≤ q ∧ (q : ℝ) ≤ L.etaSz + (c0 D : ℝ))) ∧
    (∀ up, (-1 : ℚ) ∉ JJ D up j ρ ∧ (D.R.t : ℚ) ∉ JJ D up j ρ) ∧
    (∀ q ∈ cloudJ D j ρ, (D.R.t : ℚ) + 1 < q) ∧
    (0 : ℚ) ∉ cloudJ D j ρ ∪ lowJ D j ρ

variable (D) in

def JumpLowsSignCount : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ρ : D.what₂.Tau,
    {q ∈ lowJ D j ρ | q < 0}.ncard = D.R.m - j ∧ {q ∈ lowJ D j ρ | 0 < q}.ncard = j ∧
    {q ∈ lowT D false j ρ | q < 0}.ncard = j ∧ {q ∈ lowT D false j ρ | 0 < q}.ncard = D.R.m - j ∧
    {q ∈ JW D true j ρ | q < 0}.ncard = D.R.m - j ∧ {q ∈ JW D false j ρ | q < 0}.ncard = D.R.k - 1 + j

def hJ : ℝ := L.sc.b + L.Sc + L.etaSz + D.R.t

def JumpAbsoluteBound : Prop :=
  (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ρ : D.what₂.Tau, ∀ up, ∀ q ∈ JJ D up j ρ,
    |(q : ℝ)| ≤ L.sc.b + L.Sc + L.etaSz + 1 + (c0 D : ℝ)) ∧
  L.sc.b + L.Sc + L.etaSz + 1 + (c0 D : ℝ) ≤ hJ L ∧ L.sc.b ≤ hJ L ∧ hJ L ≤ 2 * L.sc.b

def DualCloudSizes : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ρ : D.what₂.Tau,
    (∀ up, ∀ u ∈ dualS (cloudT D up j ρ),
      ((sz D j ρ - ((D.R.t : ℚ) + 1) / 2 : ℚ) : ℝ) ≤ ((|u| : ℚ) : ℝ) ∧
      ((|u| : ℚ) : ℝ) ≤ ((sz D j ρ + ((D.R.t : ℚ) + 1) / 2 : ℚ) : ℝ) + L.Sc) ∧
    (∀ up, ∀ u ∈ dualS (lowT D up j ρ),
      -L.etaSz - ((D.R.t : ℝ) + 1) / 2 ≤ (u : ℝ) ∧ (u : ℝ) ≤ L.etaSz - ((D.R.t : ℝ) + 1) / 2) ∧
    (∀ up, (0 : ℚ) ∉ dualS (JW D up j ρ)) ∧
    {u ∈ dualS (JW D false j ρ) | u < 0}.ncard = D.R.m - j ∧
    {u ∈ dualS (JW D true j ρ) | u < 0}.ncard = D.R.k - 1 + j

def ThickPlaceCloudSizes : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ρ : D.what₂.Tau,
    ((D.eTau ρ : D.R.GG) ∈ D.host.thickPlaces →
      ∀ up, ∀ u ∈ dualS (cloudT D up j ρ),
        L.sc.b - ((D.R.t : ℝ) + 1) / 2 ≤ ((|u| : ℚ) : ℝ) ∧
        ((|u| : ℚ) : ℝ) ≤ L.sc.b - ((D.R.t : ℝ) + 1) / 2 + (L.etaSz + D.R.t + 2) + L.Sc) ∧
    ∀ up, ∀ u ∈ dualS (lowT D up j ρ ∪ blockJ D), ((|u| : ℚ) : ℝ) ≤ L.etaSz + D.R.t + 2

def JumpConditions : Prop := ConclusionJa D ∧ CloudCentreDistance L ∧ jcCondition L ∧ JumpLowsSignCount D ∧ JumpAbsoluteBound L ∧ DualCloudSizes L ∧ ThickPlaceCloudSizes L

end Stmt

section admitted

variable (D)

def DeRhamFamilyAway : Prop := ∀ i r, GoodR D.nd i r → SumRepresentations.At.G2 D.nd D.naut i r

def DeRhamFamilyTypePrimes : Prop :=
  ∀ i r, GoodR D.nd i r → (D.nd.l i = D.host.g 0 ∨ D.nd.l i = D.host.g 1) →
    ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ x,
      D.naut.IsdRW i (rQ D i r x) w ∧
      ∀ τ₀, InducesW D.nd i τ₀ w → D.naut.jumpsW i (rQ D i r x) τ₀ = D.naut.locAutHodgeTateWeightsLevelZero i τ₀

def AdmDict : Prop :=
  ∃ ep : Bool, ∀ (i : D.nd.Loc) (τ₀ : D.host.E →+* Qbar (D.nd.l i)) g ρ, ReadAt D i τ₀ g ρ →
    ∃ (sg : ℚ) (cτ : ℤ), (TypeU D ep g → sg = 1) ∧ (¬ TypeU D ep g → sg = -1) ∧
      (D.naut.locAutHodgeTateWeightsLevelZero i τ₀).map (fun n : ℤ => (n : ℚ)) =
        (PPm D (D.nd.j i) ρ).map (fun p => sg * p + cτ) ∧
      ∀ w, InducesW D.nd i τ₀ w → D.naut.IsdRW i (rankOneCharacterQbar D i) w ∧
        (D.naut.jumpsW i (rankOneCharacterQbar D i) τ₀).map (fun n : ℤ => (n : ℚ)) =
          {sg * (-sz D (D.nd.j i) ρ) - c0 D + cτ}

def AdmRead : Prop :=
  ∀ i r, GoodR D.nd i r →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1),
      InducesW D.nd i (gEmb C τ) w ∧
      (∃ g : D.R.GG, (D.naut.iotaQC i).toRingHom.comp (gEmb C τ) = D.host.emb g) ∧
      ∀ x, D.naut.IsdRW i (rQ D i r x) w → D.naut.IsdRW i (rankOneCharacterQbar D i) w →
        ∀ c : ℤ, D.naut.jumpsW i (rankOneCharacterQbar D i) (gEmb C τ) = {c} →
          (∀ a : ℤ,
            multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) τ a =
              ((D.naut.jumpsW i (rQ D i r x) (gEmb C τ)).count (a + c) : ℤ) ∧
            multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x))) τ a =
              ((D.naut.jumpsW i (rQ D i r x) (gEmb C τ)).count (c - 1 - a) : ℤ)) ∧
          (∀ M : GE D.nd →* Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i),
            (M = rTwO D.nd i r x ∨ M = rDuO D.nd i r x) → ∀ a : ℤ,
            (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a ↔
              multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C M)) τ a ≠ 0)) ∧
          ∀ (ρπ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), x ∈ D.nd.Z i →
            TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρπ x → ∀ a : ℤ,
            multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρπ x))) τ a =
              multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) τ a -
                (if 0 ≤ a ∧ a < (D.R.t : ℤ) then 1 else 0) ∧
            multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρπ x))) τ a =
              multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρπ x))) τ (-a - 1) ∧
            (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρπ x))) τ a ↔
              multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρπ x))) τ a ≠ 0) ∧
            (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρπ x))) τ a ↔
              multV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρπ x))) τ a ≠ 0)

variable {D} (L : SizeData₂ D)

def AdmPar : Prop :=
  L.etaSz + D.R.t + L.Sc < L.sc.w'' D.R.n ∧ 3 * L.sc.w'' D.R.n ≤ L.sc.b ∧
    (∀ tt, (L.bT tt : ℝ) + L.sc.b' / L.sc.x ≤ L.sc.b) ∧ (D.R.t : ℝ) ≤ L.etaSz

def AdmJ : Prop :=
  DeRhamFamilyAway D ∧ CrysIffWD D.nd D.naut ∧ DeRhamFamilyTypePrimes D ∧ AdmDict D ∧ AdmRead D ∧ AdmPar L

variable (D) in

def JumpBoundClosedForm : Prop := ∀ L : SizeData₂ D, AdmJ L → JumpConditions L

end admitted

end Formalism.MainNotions.AdmissibleParameterJ

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.HerrClassFieldOfNorms
section
noncomputable section

namespace Formalism.MainNotions.HerrComplexNaturality

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def FN (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LocalSituation.adm9 D HW F

def HerrNaturality (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm17 D HW F

def AdmNat (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F

def HerrNaturalityTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmNat D HW F → HerrNaturality D HW F

theorem herr_naturality_theorem_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : HerrNaturalityTheorem D HW F := by
  intro h l _ K s LL g
  refine ⟨(h l K s LL g).2.2, ?_⟩
  intro hg T T' f pr pr' hp
  have h1 := (h l K s LL g).1 hg T
  exact (h1.2.2 T' f pr pr' hp).symm

theorem herr_naturality_iff (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : HerrNaturality D HW F ↔ Formalism.MainNotions.HerrCohomologyExtensions.adm18 D HW F := Iff.rfl

def HerrExtensionClass (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm16 D HW F

def AdmExt (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := FN D HW F ∧ Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFreeGlobal D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.WachCharacterisation D HW F

def HerrExtensionTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmExt D HW F → HerrExtensionClass D HW F

theorem herr_extension_iff (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : HerrExtensionClass D HW F ↔ Formalism.MainNotions.HerrCohomologyExtensions.adm16 D HW F := Iff.rfl

def HerrExtensionUpToUnit (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    Formalism.MainNotions.ElementDenominator.coreHerrExt ((HW l).W K s LL h) ∧ Formalism.MainNotions.ElementDenominator.coreHerrExtΔ ((HW l).W K s LL h)

def AdmExtU (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := HerrExtensionClass D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFreeGlobal D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.ConclusionE D HW F

def HerrExtensionUnitTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmExtU D HW F → HerrExtensionUpToUnit D HW F

theorem herr_class_maps_of_naturality (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h1 : HerrNaturality D HW F) (h2 : HerrExtensionUpToUnit D HW F) : Formalism.MainNotions.ElementDenominator.HerrClassMapsLocal D HW F :=
  fun l _ K s LL h => ⟨(h1 l K s LL h).1, (h1 l K s LL h).2, (h2 l K s LL h).1, (h2 l K s LL h).2⟩

theorem herr_class_maps_iff (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Formalism.MainNotions.ElementDenominator.HerrClassMapsLocal D HW F ↔ HerrNaturality D HW F ∧ HerrExtensionUpToUnit D HW F :=
  ⟨fun H => ⟨fun l _ K s LL h => ⟨(H l K s LL h).1, (H l K s LL h).2.1⟩,
    fun l _ K s LL h => (H l K s LL h).2.2⟩, fun H => herr_class_maps_of_naturality D HW F H.1 H.2⟩

end Formalism.MainNotions.HerrComplexNaturality
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.IsobaricMultiplicityOne
section
noncomputable section

namespace Formalism.MainNotions.N.T2

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N

namespace SumRepresentations

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def StrongMultiplicityOneCuspidalSums : Prop :=
  (∀ Pa Pa' : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ p.d = 1) → (∀ p ∈ Pa', 1 ≤ p.a ∧ p.d = 1) →
    (∀ᶠ w in Filter.cofinite, isoLoc N A Pa w = isoLoc N A Pa' w) → Pa.Perm Pa')

def IsobaricMultiplicityOne : Prop :=
  (∀ Pa Pa' : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
    (∀ p ∈ Pa', 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
    (∀ᶠ w in Filter.cofinite, isoLoc N A Pa w = isoLoc N A Pa' w) → Pa.Perm Pa')

end SumRepresentations

end Formalism.MainNotions.N.T2

namespace Formalism.MainNotions.N.T2
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations in

theorem litGoodO : Formalism.MainNotions.N.LitGoodO := by
  intro l _ LL
  haveI : FiniteDimensional ℚ_[l] LL.1 := LL.2
  refine ⟨⟨inferInstance, inferInstance, inferInstance⟩, LL.2, isModuleTopologyOfFiniteDimensional,
    inferInstance, ?_⟩
  have hr : Set.range (algebraMap (OL LL) LL.1) = ((OL LL).toSubring.toAddSubgroup : Set LL.1) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [hr]
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0)
    (Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos) ?_)
  intro x hx
  show x ∈ OL LL
  rw [Formalism.BasicNotions.Examples₂.LB.mem_OL]
  have : ‖x‖ < 1 := by simpa using hx
  exact le_of_lt this
end Formalism.MainNotions.N.T2
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LocalCongruenceBound
section
noncomputable section

namespace Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  Module

variable {D : D7}

def LocalCongruenceBound (CT eta : ℕ) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (c : ℚ) : Prop :=
  ∃ N r' : ℕ, 2 ≤ N ∧ N ≤ D.R.nV + 1 ∧ 1 ≤ r' ∧ 4 * r' ≤ N ^ 2 ∧
    (c : ℝ) ≤ ((D.R.f * (2 * ((2 * D.R.r + D.R.t * 2) *
        (CT * (N * r' + (eta + D.R.t + 1) * (N + r'))))) : ℕ) : ℝ) +
      (Br.sPi D.loc D.nbr i ρ π : ℝ) +
      (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℝ)) +
      (padicValNat (D.nd.l i) (hE D.host) : ℝ) + 4 * D.R.nV * (D.nd.vdel i : ℝ) +
      D.R.t * (∑ q ∈ D.nd.Q i, (vZeta i q : ℝ))

end Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.TypePrimeCongruences
section
noncomputable section

namespace Formalism.MainNotions.TypePrimeCongruences

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

def TypePrimeChoiceConclusions (D : D7) : Prop := @PairedCharacterCondition.TypePrimeChoiceLemmas D

def TypePrimeWildIdempotentChoice (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k → HG D.nd D.naut i →
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GoodR D.nd i r →
    ∀ π ∈ D.nd.Z i, TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π → PairedCharacterCondition.WildIdempotentChoice i r ρ π

def TypePrimeHypotheses (D : D7) : Prop := SumRepresentations.adm5 D ∧ SumRepresentations.Conclusion41 D ∧ AutomorphicSideWildInertia.ResidualIrreducibleGood D ∧ TypePrimeWildIdempotentChoice D

def TypePrimeConclusionsOfHypotheses (D : D7) : Prop := TypePrimeHypotheses D → TypePrimeChoiceConclusions D

end Formalism.MainNotions.TypePrimeCongruences
end
end

