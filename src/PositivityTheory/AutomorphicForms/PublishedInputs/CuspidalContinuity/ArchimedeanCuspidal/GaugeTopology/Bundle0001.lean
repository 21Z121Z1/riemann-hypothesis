import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.FComb
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Filter Topology
open scoped ValuativeRel

namespace Ad3.LFS

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def psm (ψ : AddChar F Circle) (x : F) : ℂ := (ψ (-x) : ℂ)

def WL (ψ : AddChar F Circle) (W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (lam : ℂ) (f : F → ℂ)
    (g : GL (Fin 3) F) : ℂ :=
  mp (GeneralLinearGroup.det g) (1 + lam) *
    ∫ h, W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2 + lam) *
      ∫ x, Φ ((h : Matrix (Fin 2) (Fin 2) F) * blk x * (g : Matrix (Fin 3) (Fin 3) F)) * f (x 1) ∂vol2 ψ ∂hG ψ

def fL (ψ : AddChar F Circle) (φ : F → ℂ) (x : F) : ℂ := ∫ b, φ b * (ψ (-(b * x)) : ℂ) ∂selfDualMeasure ψ

def NZ (ψ : AddChar F Circle) (φ : F → ℂ) : Prop :=
  φ ∈ schwartzBruhat F ∧ (∀ᶠ x in 𝓝 (0 : F), φ x = 0) ∧ ∫ x, φ x ∂selfDualMeasure ψ = 0

def PU (ψ : AddChar F Circle) (W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (lam : ℂ)
    (c : Fˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ k, inn ψ Φ k 1 * mp (GeneralLinearGroup.det k) (3 / 2 + lam) *
    ∫ a, W' (dg2 a 1 * k⁻¹) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2) ∂multHaar F ∂hG ψ

variable (F) in

def kq : ℂ := (((multHaarConst F).toReal)⁻¹ : ℝ)

end D

def F0 : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) W' Φ, WL ψ W' Φ 0 (psm ψ) = Wp ψ W' Φ

def FPrim : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ → ∀ c, IsUnit1 c → ∀ s lam : ℂ,
    1 / 4 < s.re → -(1 / 16) < lam.re →
      Integrable (zF (WL ψ W' Φ lam (psm ψ)) c s) (multHaar F) ∧
        ∫ a, zF (WL ψ W' Φ lam (psm ψ)) c s a ∂multHaar F = PU ψ W' Φ lam c s

def FHolP : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ → ∀ c, IsUnit1 c → ∀ s : ℂ,
    1 / 4 < s.re → DifferentiableOn ℂ (fun lam => PU ψ W' Φ lam c s) {lam | -(1 / 16) < lam.re}

def FDual : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ → ∀ φ, NZ ψ φ → ∀ c, IsUnit1 c →
    ∀ s lam : ℂ, 1 / 4 < s.re → s.re < 3 / 4 → 1 - s.re < lam.re → lam.re < 1 →
      ∫ p, zF' (WL ψ W' Φ lam (fL ψ φ)) c s p ∂((multHaar F).prod (selfDualMeasure ψ)) =
        kq F * ((c (-1) : ℂˣ) : ℂ) * (gam ψ (ν * c) s * gam ψ (ν⁻¹ * c) s) *
          localZeta (fL ψ φ) c⁻¹ (1 - s - lam) * PU ψ W' Φ lam c s

def FHolD : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ → ∀ φ, NZ ψ φ → ∀ c, IsUnit1 c →
    ∀ s : ℂ, 1 / 4 < s.re → s.re < 3 / 4 →
      DifferentiableOn ℂ (fun lam => ∫ p, zF' (WL ψ W' Φ lam (fL ψ φ)) c s p ∂((multHaar F).prod (selfDualMeasure ψ)))
          {lam | 0 < lam.re ∧ lam.re < 1} ∧
        ContinuousWithinAt (fun lam => ∫ p, zF' (WL ψ W' Φ lam (fL ψ φ)) c s p ∂((multHaar F).prod (selfDualMeasure ψ)))
          {lam | 0 ≤ lam.re ∧ lam.re < 1} 0

def FHolT : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ φ, NZ ψ φ → ∀ c : Fˣ →* ℂˣ, IsUnit1 c → ∀ s : ℂ,
    Differentiable ℂ (fun lam => localZeta (fL ψ φ) c⁻¹ (1 - s - lam))

def FTwo : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ → ∀ φ, NZ ψ φ → ∀ c, IsUnit1 c →
    ∀ s : ℂ, 1 / 4 < s.re → s.re < 3 / 4 →
      ∫ p, zF' (WL ψ W' Φ 0 (fL ψ φ)) c s p ∂((multHaar F).prod (selfDualMeasure ψ)) =
        kq F * localZeta φ c s * ∫ p, zF' (Wp ψ W' Φ) c s p ∂((multHaar F).prod (selfDualMeasure ψ))

def FTate : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ φ, NZ ψ φ → ∀ c : Fˣ →* ℂˣ, IsUnit1 c → ∀ s : ℂ,
    0 < s.re → s.re < 1 →
      localZeta (fL ψ φ) c⁻¹ (1 - s) = ((c (-1) : ℂˣ) : ℂ) * gam ψ c s * localZeta φ c s

def FPhi : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ c : Fˣ →* ℂˣ, IsUnit1 c → ∀ s : ℂ, 0 < s.re → s.re < 1 →
    ∃ φ, NZ ψ φ ∧ localZeta φ c s ≠ 0

def FComb : Prop := F0 → FPrim → FHolP → FDual → FHolD → FHolT → FTwo → FTate → FPhi → SFeW

end Ad3.LFS
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace Ad3.LFS

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def col3 (k : Matrix (Fin 2) (Fin 2) F) (y : Fin 2 → F) : Matrix (Fin 2) (Fin 3) F :=
  !![k 0 0, k 0 1, y 0; k 1 0, k 1 1, y 1]

def pft (ψ : AddChar F Circle) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ) (k : Matrix (Fin 2) (Fin 2) F) (ξ : Fin 2 → F) : ℂ :=
  ∫ y, Φ (col3 k y) * (ψ (-(∑ j, ξ j * y j)) : ℂ) ∂vol2 ψ

def SG (W : GL (Fin 3) F → ℂ) : Prop :=
  ∃ C : ℝ, ∀ (a b : Fˣ), ∀ k ∈ GLnLocal.integralGL F 3,
    ‖W (dg (a * b) b 1 * k)‖ ≤ C * ((modulus (a : F) : ℝ) * modulus (b : F)) ^ (3 / 4 : ℝ)

def Supp (W : GL (Fin 3) F → ℂ) : Prop :=
  ∃ B : ℝ, ∀ (a b : Fˣ), ∀ k ∈ GLnLocal.integralGL F 3,
    W (dg (a * b) b 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B ∧ (modulus (b : F) : ℝ) ≤ B

def Sm (W : GL (Fin 3) F → ℂ) : Prop := ∃ U : OpenSubgroup (GL (Fin 3) F), ∀ g, ∀ u ∈ U, W (g * u) = W g

def om (R : ℝ) (t : Fˣ) : Set (GL (Fin 2) F) :=
  {k | (∀ i j, (modulus ((k : Matrix (Fin 2) (Fin 2) F) i j) : ℝ) ≤ R) ∧
    ∀ j, (modulus ((t : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) : ℝ) ≤ R}

end D

def GTorus : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ → ∀ t₁ t₂ : Fˣ,
    Wp ψ W' Φ (dg t₁ t₂ 1) = mp (t₁ * t₂) (1 / 2) *
      ∫ k, W' (dg2 t₁ t₂ * k⁻¹) * mp (GeneralLinearGroup.det k) (1 / 2) *
        pft ψ Φ (k : Matrix (Fin 2) (Fin 2) F) (fun j => (t₂ : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) ∂hG ψ

def GFour : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ Φ ∈ SB F, ∃ C R : ℝ, ∀ k ξ,
    ‖pft ψ Φ k ξ‖ ≤ C ∧
      (pft ψ Φ k ξ ≠ 0 → (∀ i j, (modulus (k i j) : ℝ) ≤ R) ∧ ∀ j, (modulus (ξ j) : ℝ) ≤ R)

def GInt2 : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ V', WhittakerModelGL2 ψ ν ν⁻¹ V' → ∀ W' ∈ V',
    ∀ R : ℝ, ∃ C : ℝ, ∀ t₁ t₂ : Fˣ,
      Integrable ((om R t₂).indicator fun k => ‖W' (dg2 t₁ t₂ * k⁻¹)‖ * (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ))
        (hG ψ) ∧
      ∫ k, (om R t₂).indicator (fun k => ‖W' (dg2 t₁ t₂ * k⁻¹)‖ * (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ)) k ∂hG ψ ≤
        C * (modulus (t₁ : F) : ℝ) ^ (1 / 4 : ℝ) * (modulus (t₂ : F) : ℝ) ^ (-(1 / 2) : ℝ)

def GTorP : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ →
    ∃ C : ℝ, ∀ t₁ t₂ : Fˣ, ‖Wp ψ W' Φ (dg t₁ t₂ 1)‖ ≤ C * (modulus (t₁ : F) : ℝ) ^ (3 / 4 : ℝ)

def GTor : Prop := GTorus → GFour → GInt2 → GTorP

def GK : Prop :=
  STrans → SSmoothW → GTorP →
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ → SG (Wp ψ W' Φ)

def GInt : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (W : GL (Fin 3) F → ℂ), Sm W → SG W → Supp W →
    ∀ s : ℂ, 1 / 4 < s.re → Integrable (zF W 1 s) (multHaar F)

def GInt' : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (W : GL (Fin 3) F → ℂ),
    (∀ x y z g, W (uni x y z * g) = (ψ (x + z) : ℂ) * W g) → (∀ (a : Fˣ) g, W (dg a a a * g) = W g) →
    Sm W → SG W → Supp W →
    ∀ s : ℂ, s.re < 3 / 4 → Integrable (zF' W 1 s) ((multHaar F).prod (selfDualMeasure ψ))

end Ad3.LFS
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.UBranch
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace Ad3.LFS

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

variable (F) in

def Φ0 : Matrix (Fin 2) (Fin 3) F → ℂ := Set.indicator {X | ∀ i j, X i j ∈ 𝒪[F]} 1

def s2 (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) : GL (Fin 2) F → ℂ :=
  sphericalWhittaker (Circle.coeHom.compAddChar ψ) ![ν (unifUnit F), ν⁻¹ (unifUnit F)]

def W0 (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) : GL (Fin 3) F → ℂ := Wp ψ (s2 ψ ν) (Φ0 F)

end D

def UPhi : Prop := ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F], Φ0 F ∈ SB F

def UK : Prop := STrans → UPhi →
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ), ∀ g, ∀ k ∈ integralGL F 3, W0 ψ ν (g * k) = W0 ψ ν g

def UUni : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F],
    ∀ u ∈ unipotent F 3,
      u = uni ((u : Matrix (Fin 3) (Fin 3) F) 0 1) ((u : Matrix (Fin 3) (Fin 3) F) 0 2)
        ((u : Matrix (Fin 3) (Fin 3) F) 1 2) ∧
      ∀ ψ₀ : AddChar F ℂ, Whittaker.psiN ψ₀ u =
        ψ₀ ((u : Matrix (Fin 3) (Fin 3) F) 0 1 + (u : Matrix (Fin 3) (Fin 3) F) 1 2)

def UNonDom : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ W : GL (Fin 3) F → ℂ,
    (∀ x y z g, W (uni x y z * g) = (ψ (x + z) : ℂ) * W g) →
    (∀ g, ∀ k ∈ integralGL F 3, W (g * k) = W g) →
    ∀ l : Fin 3 → ℤ, ¬ Antitone l → W (torusPow F 3 l) = 0

def UDomA : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → IsUnramifiedChar ν →
    ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ l : Fin 3 → ℤ, Antitone l →
      W0 ψ ν (torusPow F 3 l) = c₀ * halfModulus F l *
        ∑ a ∈ Finset.Icc (l 1) (l 0), ∑ b ∈ Finset.Icc (l 2) (l 1),
          evalAt ![ν (unifUnit F), (ν (unifUnit F))⁻¹] (schur ![a, b])

def UBranch : Prop :=
  ∀ (α : ℂˣ) (l : Fin 3 → ℤ), Antitone l →
    evalAt ![α, 1, α⁻¹] (schur l) =
      ∑ a ∈ Finset.Icc (l 1) (l 0), ∑ b ∈ Finset.Icc (l 2) (l 1), evalAt ![α, α⁻¹] (schur ![a, b])

def UGlue : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F],
    ∀ ψ₀ : AddChar F ℂ, (∀ x ∈ 𝒪[F], ψ₀ x = 1) → ∀ (z : Fin 3 → ℂˣ) (W : GL (Fin 3) F → ℂ) (c : ℂ),
    (∀ u ∈ unipotent F 3, ∀ g, W (u * g) = Whittaker.psiN ψ₀ u * W g) →
    (∀ g, ∀ k ∈ integralGL F 3, W (g * k) = W g) →
    (∀ l, W (torusPow F 3 l) = c * sphericalWhittaker ψ₀ z (torusPow F 3 l)) →
    W = c • sphericalWhittaker ψ₀ z

end Ad3.LFS
end
end

