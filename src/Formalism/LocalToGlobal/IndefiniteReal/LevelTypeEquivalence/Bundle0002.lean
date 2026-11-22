import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFCA

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.BaseSt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def InfFamExists : Prop :=
  ∃ θ : Datum.InfFam D, IsInfFam θ

def InfFamUnique : Prop :=
  ∀ θ θ' : Datum.InfFam D, IsInfFam θ → IsInfFam θ' → θ = θ'

def InfSplit : Prop :=
  ∀ θ : Datum.InfFam D, IsInfFam θ →
    ∃ e : (Ainf D.host.F ⊗[D.host.F] D.host.E) ≃+* (D.what₂.Tau → ℂ),
      Continuous e ∧ Continuous e.symm ∧ ∀ x τ, e x τ = θ τ x

def AtTauExUnique : Prop :=
  ∀ θ : Datum.InfFam D, IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ),
    gᴴ * gramAt D V τ * g = gramAt D V τ → ∃! h : GA D V, IsAtTau θ V τ g h

def AtTauUnitary : Prop :=
  ∀ θ : Datum.InfFam D, IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : GA D V),
    IsAtTau θ V τ g h → gᴴ * gramAt D V τ * g = gramAt D V τ

def AtTauHom : Prop :=
  ∀ θ : Datum.InfFam D, IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau),
    atTau θ V τ 1 = 1 ∧
    (∀ g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ, gᴴ * gramAt D V τ * g = gramAt D V τ →
      g'ᴴ * gramAt D V τ * g' = gramAt D V τ → atTau θ V τ (g * g') = atTau θ V τ g * atTau θ V τ g') ∧
    ContinuousOn (atTau θ V τ) {g | gᴴ * gramAt D V τ * g = gramAt D V τ}

def GATop : Prop :=
  ∀ V : HSp D, IsTopologicalGroup (GA D V) ∧ LocallyCompactSpace (GA D V) ∧ T2Space (GA D V) ∧
    SecondCountableTopology (GA D V) ∧ BorelSpace (GA D V)

def GQDiscrete : Prop :=
  ∀ V : HSp D, DiscreteTopology (GQ V)

def FundDomExists : Prop :=
  ∀ V : HSp D, ∃ 𝓕 : Set (GA D V), MeasurableSet 𝓕 ∧ ∀ μ : Measure (GA D V), IsFundamentalDomain (GQ V) 𝓕 μ

def MinfExUnique : Prop :=
  ∀ p q : ℕ, ∃! m : Measure (UpqT p q), Lev.IsMinf m

variable {D}

def IsLevelA (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) : Prop :=
  IsCompact (Lev.levA V K : Set (GA D V)) ∧ IsOpen (((Lev.levA V K).subgroupOf (GfC V)) : Set (GfC V))

variable (D)

def MeasLevExists : Prop :=
  ∀ V : HSp D, V.SigOK → ∀ K : Subgroup (GL (Fin V.rank) (Lev.EAf D)), IsLevelA V K → ∃ μ, Lev.IsMeasLev V K μ

def MeasLevDefExists : Prop :=
  ∀ V : HSp D, V.SigOK → V.IsDefinite → ∀ K : Subgroup (GL (Fin V.rank) (Lev.EAf D)), IsLevelA V K →
    ∃ μ, Lev.IsMeasLevDef V K μ

def MeasFDExists : Prop :=
  ∀ V : HSp D, V.SigOK → ∀ K : Subgroup (GL (Fin V.rank) (Lev.EAf D)), IsLevelA V K →
    ∃ μ 𝓕, Lev.IsMeasFD V K μ 𝓕

end Formalism.IndefR.Eqv

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.EqZeroOfMemFactorial
section
namespace Formalism.IndefR.Eqv.AdelDual

open Filter Topology

section Val

open IsDedekindDomain NumberField

theorem exists_pow_lt {c a : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hc : c < 1) : ∃ k : ℕ, c ^ k < a := by
  rcases eq_or_ne c 0 with rfl | hc0
  · exact ⟨1, by simpa using (zero_lt_iff.mpr ha)⟩
  obtain ⟨α, rfl⟩ := WithZero.ne_zero_iff_exists.mp hc0
  obtain ⟨β, rfl⟩ := WithZero.ne_zero_iff_exists.mp ha
  have hα : Multiplicative.toAdd α < 0 := by
    have h1 : ((α : WithZero (Multiplicative ℤ))) < ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      simpa using hc
    rw [WithZero.coe_lt_coe] at h1
    exact h1
  refine ⟨(Multiplicative.toAdd β).natAbs + 1, ?_⟩
  rw [← WithZero.coe_pow, WithZero.coe_lt_coe]
  show Multiplicative.toAdd (α ^ ((Multiplicative.toAdd β).natAbs + 1)) < Multiplicative.toAdd β
  rw [toAdd_pow, nsmul_eq_mul]
  set a := Multiplicative.toAdd α
  set b := Multiplicative.toAdd β
  have ha1 : a ≤ -1 := by omega
  have h2 : -((b.natAbs : ℕ) : ℤ) ≤ b := by omega
  have h3 : (((b.natAbs + 1 : ℕ) : ℤ)) * a ≤ -(((b.natAbs + 1 : ℕ) : ℤ)) := by
    have : (0 : ℤ) ≤ ((b.natAbs + 1 : ℕ) : ℤ) := by positivity
    nlinarith
  push_cast at h3 ⊢
  have h4 := neg_abs_le b
  linarith

variable {F : Type} [Field F] [NumberField F]

theorem val_natCast_le_one (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : Valued.v (n : v.adicCompletion F) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ]; exact (Valuation.map_add _ _ _).trans (max_le ih (by simp))

theorem val_factorial_anti (v : HeightOneSpectrum (𝓞 F)) {m m' : ℕ} (h : m ≤ m') :
    Valued.v ((m'.factorial : ℕ) : v.adicCompletion F) ≤ Valued.v ((m.factorial : ℕ) : v.adicCompletion F) := by
  induction m', h using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, map_mul]
    calc Valued.v ((k + 1 : ℕ) : v.adicCompletion F) * Valued.v ((k.factorial : ℕ) : v.adicCompletion F)
        ≤ 1 * Valued.v ((k.factorial : ℕ) : v.adicCompletion F) :=
          mul_le_mul' (val_natCast_le_one v (k + 1)) le_rfl
      _ = _ := one_mul _
      _ ≤ _ := ih

theorem val_factorial_le (v : HeightOneSpectrum (𝓞 F)) (N : ℕ) (hN : 1 ≤ N) (k : ℕ) :
    Valued.v (((N * k).factorial : ℕ) : v.adicCompletion F) ≤ Valued.v ((N : ℕ) : v.adicCompletion F) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨m, hm⟩ : ∃ m, N * (k + 1) = m + 1 := ⟨N * (k + 1) - 1, by
      have : 1 ≤ N * (k + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega⟩
    rw [hm, Nat.factorial_succ, Nat.cast_mul, map_mul, pow_succ, mul_comm (Valued.v _ ^ k)]
    have h1 : Valued.v ((m + 1 : ℕ) : v.adicCompletion F) ≤ Valued.v ((N : ℕ) : v.adicCompletion F) := by
      rw [← hm, Nat.cast_mul, map_mul]
      calc Valued.v ((N : ℕ) : v.adicCompletion F) * Valued.v ((k + 1 : ℕ) : v.adicCompletion F)
          ≤ Valued.v ((N : ℕ) : v.adicCompletion F) * 1 := mul_le_mul' le_rfl (val_natCast_le_one v _)
        _ = _ := mul_one _
    have h2 : Valued.v ((m.factorial : ℕ) : v.adicCompletion F) ≤ Valued.v ((N : ℕ) : v.adicCompletion F) ^ k :=
      (val_factorial_anti v (by
        have : N * k + N = m + 1 := by rw [← hm]; ring
        omega)).trans ih
    exact mul_le_mul' h1 h2

theorem exists_nat_val_lt_one (v : HeightOneSpectrum (𝓞 F)) :
    ∃ N : ℕ, 1 ≤ N ∧ Valued.v ((N : ℕ) : v.adicCompletion F) < 1 := by
  refine ⟨Ideal.absNorm v.asIdeal, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  · have e : ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) = (((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) :
        v.adicCompletion F) := by
      exact (map_natCast (algebraMap (𝓞 F) (v.adicCompletion F)) _).symm
    rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact Ideal.absNorm_mem _

theorem eq_zero_of_mem_factorial (x : FiniteAdeleRing (𝓞 F) F)
    (h : ∀ n : ℕ, ∃ y ∈ Formalism.IndefR.PHeisFC.Ohat F, x = n.factorial • y) : x = 0 := by
  refine RestrictedProduct.ext _ _ fun v => ?_
  by_contra hne
  have hne' : x v ≠ 0 := fun h0 => hne (by exact h0)
  have hx0 : Valued.v (x v) ≠ 0 := (Valuation.ne_zero_iff _).mpr hne'
  obtain ⟨N, hN1, hN⟩ := exists_nat_val_lt_one v
  obtain ⟨k, hk⟩ := exists_pow_lt hx0 hN
  obtain ⟨y, hy, rfl⟩ := h (N * k)
  have hyv : Valued.v (y v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp (hy v)
  have e : ((N * k).factorial • y) v = (((N * k).factorial : ℕ) : v.adicCompletion F) * y v := by
    rw [nsmul_eq_mul]; rfl
  have : Valued.v (((N * k).factorial • y) v) ≤ Valued.v ((N : ℕ) : v.adicCompletion F) ^ k := by
    rw [e, map_mul]
    calc _ ≤ Valued.v (((N * k).factorial : ℕ) : v.adicCompletion F) * 1 := mul_le_mul' le_rfl hyv
      _ = _ := mul_one _
      _ ≤ _ := val_factorial_le v N hN1 k
  exact absurd (lt_of_le_of_lt this hk) (lt_irrefl _)

end Val

end Formalism.IndefR.Eqv.AdelDual
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ThetaSquareIntegrable
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def ipO {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f f' : WO S T → ℂ) : ℂ :=
  ∫ w in 𝓕, f w * starRingEnd ℂ (f' w) ∂μ

def ThetaSquareIntegrable (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), (∀ x, ‖ψ x‖ = 1) →
    ∀ f, IsThetaFunO ψ S T f → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratL T S) 𝓕 μ → MemLp f 2 (μ.restrict 𝓕)

def IpUnit (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
      ∀ p f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → ipO μ 𝓕 (om p f) (om p f') = ipO μ 𝓕 f f'

def CoefBound (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
      ∀ p f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' →
        ‖ipO μ 𝓕 (om p f) f'‖ ≤ Real.sqrt (nrm2 μ 𝓕 f) * Real.sqrt (nrm2 μ 𝓕 f')

def CoefCont (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    FirstCountableTopology (GA D S) → FirstCountableTopology (GA D T) →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
      ∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → Continuous fun p => ipO μ 𝓕 (om p f) f'

def IsRealFrame {S T : HSp D} {k : ℕ} (L : (Fin k → ℝ) →+ WO S T) : Prop :=
  Continuous L ∧ (∀ t, (L t).map (finPart D) = 0) ∧ ∀ w : WO S T, w.map (finPart D) = 0 → ∃ t, L t = w

def dH (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {k n : ℕ} (L : (Fin k → ℝ) →+ WO S T) (l : Fin n → Fin k)
    (f : WO S T → ℂ) (w : WO S T) : ℂ :=
  iteratedFDeriv ℝ n (fun t : Fin k → ℝ => heisO ψ S T (L t) f w) 0 (fun i => Pi.single (l i) 1)

def sobO (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {k : ℕ} (L : (Fin k → ℝ) →+ WO S T) (N : ℕ)
    (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f : WO S T → ℂ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), ∑ l : Fin n → Fin k, Real.sqrt (∫ w in 𝓕, ‖dH ψ L l f w‖ ^ 2 ∂μ)

def ThetaSob (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) →
    ∃ (k : ℕ) (L : (Fin k → ℝ) →+ WO S T) (N : ℕ), IsRealFrame L ∧
      ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) →
        ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
          ∃ C : ℝ, ∀ f, IsThetaFunO ψ S T f → (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u f = f) →
            ∀ w, ‖f w‖ ≤ C * sobO ψ L N μ 𝓕 f

def IsHgtInf (θ : InfFam D) (V : HSp D) (hgt : GA D V → ℝ) : Prop :=
  ∀ a ∈ GinfC V, 1 ≤ hgt a ∧ ∀ τ i j, ‖θ τ (infPart D (mt V a i j))‖ ≤ hgt a ∧ ‖θ τ (infPart D (mt V a⁻¹ i j))‖ ≤ hgt a

def ThetaGrowth (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ θ : InfFam D, IsInfFam θ → ∀ (hS : GA D S → ℝ) (hT : GA D T → ℝ), IsHgtInf θ S hS → IsHgtInf θ T hT →
      ∀ f, IsThetaFunO ψ S T f → ∀ K : Set (GA D S × GA D T), IsCompact K →
        ∃ (N : ℕ) (C : ℝ), ∀ k ∈ K, ∀ a ∈ GinfC S, ∀ b ∈ GinfC T,
          ‖thetaKO om (a * k.1) (b * k.2) f‖ ≤ C * (hS a * hT b) ^ N

def ThetaGrowthRat (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ θ : InfFam D, IsInfFam θ → ∀ hS : GA D S → ℝ, IsHgtInf θ S hS →
      ∀ f, IsThetaFunO ψ S T f → ∀ (K : Set (GA D S)) (K' : Set (GA D T)), IsCompact K → IsCompact K' →
        ∃ (N : ℕ) (C : ℝ), ∀ k ∈ K, ∀ a ∈ GinfC S, ∀ γ ∈ GQ T, ∀ c ∈ K',
          ‖thetaKO om (a * k) (γ * c) f‖ ≤ C * hS a ^ N

end Formalism.IndefR.Eqv

end
end

