import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.StrictlyAntitoneWeights.GaussianCaseFreeExponents

-- bundled from Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.StrictlyAntitoneWeights.ConstantCoeffAtReducedPoint
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TV NumberField MvPowerSeries Formalism.MainNotions.GradedPowerSeriesLemmas

namespace Formalism.MainNotions.V.Pf.V3

variable {D : D7} {V : VData D}
variable {l : ℕ} [Fact l.Prime] {e : ℕ} {χ : Chi D} {K : IntermediateField ℚ QbarQ} {g1 : GQ}

structure Comparison₂ (T : Formalism.MainNotions.UnitaryThreeHeightBounds.UnitaryThreeLiftingProblem V l e χ K g1) (P : Pres V l e χ K g1) where

  v : T.P.lPl
  pt : Ideal (T.P.RV v).C
  hpt : Formalism.MainNotions.UnitaryThreeHeightBounds.IsRt T v pt

  Jh : Ideal (MvPowerSeries (Fin P.a) (V.Ol l))
  Jh_closed : Formalism.MainNotions.UnusedSlot38.IsClosedAdic Jh
  Jh_hom : Formalism.MainNotions.UnusedSlot38.IsHomog (W P.wt) Jh
  ideal_constantCoeff_zero : ∀ f ∈ Jh, constantCoeff f = 0
  h𝔓 : P.𝔓 = PofJ P.wt Jh

  b : ℕ
  wz : Fin b → ℤ
  eA : (MvPowerSeries (Fin P.a) (V.Ol l) ⧸ Jh) ≃+* MvPowerSeries (Fin b) ((T.P.RV v).C ⧸ pt)
  eA_O : ∀ x : T.P.O, eA (Ideal.Quotient.mk Jh (C (T.eO x))) =
    C (Ideal.Quotient.mk pt (algebraMap T.P.O (T.P.RV v).C x))

  generator_mem_weight_ideal : ∀ i, eA.symm (X i) ∈ Formalism.MainNotions.UnusedSlot38.Aj (W P.wt) Jh (cj (wz i))
  eA_R : ∀ (j : ℤ) (x : (T.P.RV v).C), Formalism.BasicNotions.V1.IsEigen (T.P.coV v) (fun _ => j) x →
    eA.symm (C (Ideal.Quotient.mk pt x)) ∈ Formalism.MainNotions.UnusedSlot38.Aj (W P.wt) Jh (cj j)

  generator_constantCoeff_zero : ∀ i, Ideal.Quotient.lift Jh (constantCoeff (σ := Fin P.a) (R := V.Ol l)) ideal_constantCoeff_zero (eA.symm (X i)) = 0
  constantCoeff_at_reduced_point : ∀ φ₀ : (T.P.RV v).C →ₐ[T.P.O] T.P.O, Formalism.MainNotions.UnitaryThreeHeightBounds.IsInitialPoint T v φ₀ → ∀ x : (T.P.RV v).C,
    Ideal.Quotient.lift Jh (constantCoeff (σ := Fin P.a) (R := V.Ol l)) ideal_constantCoeff_zero
      (eA.symm (C (Ideal.Quotient.mk pt x))) = T.eO (φ₀ x)

  toS : (MvPowerSeries (Fin P.a) (V.Ol l) ⧸ Jh) →+* V.S3hat l e χ K g1
  toS_surj : Function.Surjective toS
  toS_ker : RingHom.ker toS = Ideal.span ((fun f : PT (V.Ol l) P.wt => Ideal.Quotient.mk Jh (f : MvPowerSeries (Fin P.a) (V.Ol l))) ''
    (Set.range P.F ∪ Set.range P.G ∪ Set.range P.E1 ∪ Set.range P.E2 ∪ Set.range P.Z))
  toS_S : ∀ f : PT (V.Ol l) P.wt, toS (Ideal.Quotient.mk Jh (f : MvPowerSeries (Fin P.a) (V.Ol l))) =
    V.S3emb l e χ K g1 (P.eS (mkS P.𝔓 P.F P.G P.E1 P.E2 P.Z f))

  toS_loc : ∀ x : (T.P.RV v).C, toS (eA.symm (C (Ideal.Quotient.mk pt x))) =
    T.eS (T.Q.q (Formalism.MainNotions.UnusedSlot38.resMap T.P v x))

  card_weight_neg_two_eq : P.s = 1 + Fintype.card {i // wz i = -2}
  cnt_r : P.r = 2 + Fintype.card {i // wz i = -1}
  cnt_m : P.m = 3 + Fintype.card {i // wz i = 0}
  cnt_r' : P.r' + 1 = 4 + Fintype.card {i // wz i = 1}
  card_weight_two_eq : P.s' + 1 = 2 + Fintype.card {i // wz i = 2}

variable (V)

def StepPresT : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ T : Formalism.MainNotions.UnitaryThreeHeightBounds.UnitaryThreeLiftingProblem V l e χ K g1, ∃ P : Pres V l e χ K g1,
      Nonempty (Comparison₂ T P) ∧ DataM P.𝔓 P.F P.G P.E1 P.E2 P.Z

def FirstModuleCondition : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ (T : Formalism.MainNotions.UnitaryThreeHeightBounds.UnitaryThreeLiftingProblem V l e χ K g1) (P : Pres V l e χ K g1), Comparison₂ T P →
      DataM P.𝔓 P.F P.G P.E1 P.E2 P.Z → M1 P.𝔓 P.F P.G P.Z P.r' P.s' l

def StepSha : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ (T : Formalism.MainNotions.UnitaryThreeHeightBounds.UnitaryThreeLiftingProblem V l e χ K g1) (P : Pres V l e χ K g1), Comparison₂ T P →
      DataM P.𝔓 P.F P.G P.E1 P.E2 P.Z → V.Vlen l e χ ≤ VPrime P.𝔓 P.F

theorem stepA_of (h1 : StepPresT V) (h2 : FirstModuleCondition V) (h3 : StepSha V) : StepA V := by
  intro hG l _ e χ K _ g1 dat
  obtain ⟨T⟩ := hG.1.1 l e χ K dat.data g1 dat.norm
  obtain ⟨P, ⟨tie⟩, hD⟩ := h1 hG l e χ K g1 dat T
  exact ⟨P, hD, h2 hG l e χ K g1 dat T P tie hD, h3 hG l e χ K g1 dat T P tie hD⟩

end Formalism.MainNotions.V.Pf.V3
end
end

-- bundled from Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.StrictlyAntitoneWeights.StepEpsFrob
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TV NumberField IsDedekindDomain Polynomial

namespace Formalism.MainNotions.V.Pf.V3

variable {D : D7} (V : VData D)

abbrev epsK (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ QbarQ) : K.fixingSubgroup →* (QbarL l)ˣ :=
  (epsL l).comp K.fixingSubgroup.subtype

def StepEpsFrob : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (p : ℕ), p.Prime → p ≠ l →
    ∀ Fr : FrobAt K p, ((epsL l (Fr.φ : GQ) : (QbarL l)ˣ) : QbarL l) = ((Fr.q : ℕ) : QbarL l)⁻¹

def StepFrobQ : Prop :=
  ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (p : ℕ), p.Prime → ∀ Fr : FrobAt K p,
    Formalism.ConjugateSelfDual.IsPlaceOver (F := ℚ) Fr.A Fr.vp ∧ Formalism.ConjugateSelfDual.normV Fr.vp = p ∧
    ∃ σp : GQ, Formalism.ConjugateSelfDual.IsFrob (F := ℚ) Fr.A p σp ∧ (σp ^ Fr.h)⁻¹ * (Fr.σ : GQ) ∈ Formalism.ConjugateSelfDual.Inertia (F := ℚ) Fr.A

def StepShape : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ ξ : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ → Both3 ξ →
    Formalism.ConjugateSelfDual.Irred (VData.toRecRep (V.rho3 ξ)) ∨
      ∃ ρ₂ : K.fixingSubgroup →* GL (Fin 2) (QbarL l), Formalism.ConjugateSelfDual.Irred (VData.toRecRep ρ₂) ∧
        IsDirSum (m := 2) (k := 1) (V.rho3 ξ) ρ₂ (charRep 1)

def StepCont : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ ξ : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ → Continuous (V.rho3 ξ)

def StepPtLoc : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ ξ : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ →
    (∀ q : ℕ, q.Prime → q ≠ l → ∀ σ : K.fixingSubgroup, (σ : GQ) ∈ V.Iq q →
      (σ : GQ) ∈ Formalism.MainNotions.UnitaryThreeHeightBounds.FixMu (condV D) → V.rho3 ξ σ = 1) ∧
    V.Crys l 3 (HcrSub l (V.aOf l χ) (V.Dq l ⊓ K.fixingSubgroup)) (V.plc l)
      ((V.rho3 ξ).comp (Subgroup.inclusion (inf_le_left.trans inf_le_right))) ∧
    ∀ τ, Formalism.MainNotions.UnitaryThreeHeightBounds.IndPl V l (HcrSub l (V.aOf l χ) (V.Dq l ⊓ K.fixingSubgroup)) τ →
      V.HT l 3 (HcrSub l (V.aOf l χ) (V.Dq l ⊓ K.fixingSubgroup)) (V.plc l)
        ((V.rho3 ξ).comp (Subgroup.inclusion (inf_le_left.trans inf_le_right))) τ =
          ({-(e : ℤ), 0, (e : ℤ)} : Multiset ℤ)

def StepPtOrd : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ ξ : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ →
    IsCSDOne (VData.toRecRep (V.rho3 ξ)) ∧
      OrdFixAbove (VData.toRecRep (V.rho3 ξ)) ![(e : ℤ), 0, -(e : ℤ)] (condV D)

def StepW : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ ξ : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ →
    ∀ ρ₂ : K.fixingSubgroup →* GL (Fin 2) (QbarL l), Formalism.ConjugateSelfDual.Irred (VData.toRecRep ρ₂) →
    IsDirSum (m := 2) (k := 1) (V.rho3 ξ) ρ₂ (charRep 1) →
    ∃ W : GQ →* GL (Fin 2) (QbarL l), Continuous W ∧ IsIsoRep (W.comp K.fixingSubgroup.subtype) ρ₂ ∧
      Formalism.ConjugateSelfDual.IsOdd W ∧ Formalism.ConjugateSelfDual.Irred W ∧ Formalism.ConjugateSelfDual.AlmostUnram W ∧ V.DeRham l 2 ⊤ (V.plc l) (onTop W) ∧
      (∀ τ, V.HT l 2 ⊤ (V.plc l) (onTop W) τ = ({-(e : ℤ), (e : ℤ)} : Multiset ℤ)) ∧
      (∃ a b : GQ →* (QbarL l)ˣ, (∀ g : GQ,
          ‖(W g : Matrix (Fin 2) (Fin 2) (QbarL l)).trace - ((a g : QbarL l) + (b g : QbarL l))‖ < 1 ∧
          ‖(W g : Matrix (Fin 2) (Fin 2) (QbarL l)).det - (a g : QbarL l) * (b g : QbarL l)‖ < 1) ∧
        (l = 3 → ∃ g ∈ V.Dq 3, ¬ ‖((a g : QbarL l) / (b g : QbarL l)) - (epsL l g : QbarL l)‖ < 1)) ∧
      (∀ q : ℕ, q.Prime → q ≠ l → ∀ σ : GQ, σ ∈ V.Iq q → σ ∈ Formalism.MainNotions.UnitaryThreeHeightBounds.FixMu (condV D * dK K) → W σ = 1) ∧
      V.Iq l ≤ K.fixingSubgroup ∧
      V.Crys l 2 (HcrSub l (V.aOf l χ) (V.Dq l ⊓ K.fixingSubgroup)) (V.plc l)
        (W.comp (HcrSub l (V.aOf l χ) (V.Dq l ⊓ K.fixingSubgroup)).subtype) ∧
      (LW V l e χ K g1 → ∃ π : (V.spec ℚ 2).Rep, IsWeight2 V π (2 * e + 1) ∧ IsVg V π (twistRep W ((epsL l) ^ e)⁻¹))

def StepOrbIso : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ ξ ξ' : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ → V.IsPt3 ξ' → Both3 ξ →
    Both3 ξ' → IsIsoRep (V.rho3 ξ) (V.rho3 ξ') → SameOrbit3 ξ ξ'

def Lab3 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ p : ℕ, p.Prime → ¬ p ∣ 30 * l * condV D * dK K → ∀ Fr : FrobAt K p,
    ∀ ξ : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ → Formalism.ConjugateSelfDual.Irred (VData.toRecRep (V.rho3 ξ)) →
    ∃ π ∈ Sig3G V K e,
      V.IsRi π (VData.toRecRep (twistRep (V.rho3 ξ) (epsK l K)⁻¹)) ∧
      V.iotaC l ((V.rho3 ξ Fr.φ : GL (Fin 3) (QbarL l)) : Matrix (Fin 3) (Fin 3) (QbarL l)).trace = t3 V Fr π

def Lab2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → LW V l e χ K g1 → ∀ p : ℕ, p.Prime → ¬ p ∣ 30 * l * condV D * dK K → ∀ Fr : FrobAt K p,
    ∀ ξ : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ →
    ∀ ρ₂ : K.fixingSubgroup →* GL (Fin 2) (QbarL l), Formalism.ConjugateSelfDual.Irred (VData.toRecRep ρ₂) →
    IsDirSum (m := 2) (k := 1) (V.rho3 ξ) ρ₂ (charRep 1) →
    ∃ π ∈ Sig2G V (condV D * dK K) e, ∃ W : GQ →* GL (Fin 2) (QbarL l), Continuous W ∧ Formalism.ConjugateSelfDual.Irred W ∧
      IsIsoRep (W.comp K.fixingSubgroup.subtype) ρ₂ ∧ V.IsRi π (twistRep W ((epsL l) ^ e)⁻¹) ∧
      V.iotaC l ((V.rho3 ξ Fr.φ : GL (Fin 3) (QbarL l)) : Matrix (Fin 3) (Fin 3) (QbarL l)).trace = t2 V e Fr π

def LabInj3 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ ξ ξ' : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ → V.IsPt3 ξ' → Both3 ξ →
    Both3 ξ' → Formalism.ConjugateSelfDual.Irred (VData.toRecRep (V.rho3 ξ)) → Formalism.ConjugateSelfDual.Irred (VData.toRecRep (V.rho3 ξ')) →
    ∀ π : (V.spec K 3).Rep, V.IsRi π (VData.toRecRep (twistRep (V.rho3 ξ) (epsK l K)⁻¹)) →
    V.IsRi π (VData.toRecRep (twistRep (V.rho3 ξ') (epsK l K)⁻¹)) → SameOrbit3 ξ ξ'

def LabInj2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ ξ ξ' : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ → V.IsPt3 ξ' → Both3 ξ →
    Both3 ξ' → ∀ ρ₂ ρ₂' : K.fixingSubgroup →* GL (Fin 2) (QbarL l),
    IsDirSum (m := 2) (k := 1) (V.rho3 ξ) ρ₂ (charRep 1) → IsDirSum (m := 2) (k := 1) (V.rho3 ξ') ρ₂' (charRep 1) →
    ∀ W W' : GQ →* GL (Fin 2) (QbarL l), Continuous W → Continuous W' → Formalism.ConjugateSelfDual.Irred W → Formalism.ConjugateSelfDual.Irred W' →
    IsIsoRep (W.comp K.fixingSubgroup.subtype) ρ₂ → IsIsoRep (W'.comp K.fixingSubgroup.subtype) ρ₂' →
    ∀ π : (V.spec ℚ 2).Rep, V.IsRi π (twistRep W ((epsL l) ^ e)⁻¹) → V.IsRi π (twistRep W' ((epsL l) ^ e)⁻¹) →
    SameOrbit3 ξ ξ'

end Formalism.MainNotions.V.Pf.V3
end
end

