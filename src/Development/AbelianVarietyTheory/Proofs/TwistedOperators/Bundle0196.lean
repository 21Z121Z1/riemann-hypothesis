import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0173
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0108
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix GlobalTheory.Chain GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Chain.RealIt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev LPol (b a : ℕ) : Type := MvPolynomial (Fin b × Fin a) ℂ

section Local

variable {a b : ℕ} (ε : Fin a → Bool) (ε' : Fin b → Bool)

def rai (i : Fin b) (j : Fin a) : Module.End ℂ (LPol b a) :=
  sgn (ε j) • (if ε' i = ε j then LinearMap.mulLeft ℂ (MvPolynomial.X (i, j))
    else -(MvPolynomial.pderiv (i, j)).toLinearMap)

def low (i : Fin b) (j : Fin a) : Module.End ℂ (LPol b a) :=
  sgn (ε j) • (if ε' i = ε j then (MvPolynomial.pderiv (i, j)).toLinearMap
    else LinearMap.mulLeft ℂ (MvPolynomial.X (i, j)))

def locS (X : Matrix (Fin a) (Fin a) ℂ) : Module.End ℂ (LPol b a) :=
  ∑ j, ∑ k, X j k • ∑ i, (rai ε ε' i j * low ε ε' i k + if j = k then (1 / 2 : ℂ) • 1 else 0)

def locT (Y : Matrix (Fin b) (Fin b) ℂ) : Module.End ℂ (LPol b a) :=
  ∑ i, ∑ l, Y i l • ∑ j, (rai ε ε' i j * low ε ε' l j + if i = l then (1 / 2 : ℂ) • 1 else 0)

def IsPolyIso {p q r s : ℕ} (e : Ix p q ≃ Fin a) (e' : Ix r s ≃ Fin b) (κ : LPol b a ≃ₗ[ℂ] Pol p q r s) : Prop :=
  (∀ (Z : Mat p q) (P : LPol b a), κ (locS ε ε' (Matrix.reindex e e Z) P) = fockAct1 p q r s Z (κ P)) ∧
    ∀ (Z : Mat r s) (P : LPol b a), κ (locT ε ε' (Matrix.reindex e' e' Z) P) = fockAct2 p q r s Z (κ P)

end Local

structure IsCoverIt {p q r s : ℕ} {T₁ : GrpData p q} {T₂ : GrpData r s} (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H) : Prop where
  bdd : ∀ P, ∃ c : ℝ, ∀ y, ‖B P y‖ ≤ c * ‖y‖
  kfin : ∀ P y, B P y ∈ Set.range R₁.ι
  ne : ∀ y, y ≠ 0 → ∃ P, B P y ≠ 0
  src : ∀ Z ∈ upq p q, ∀ P y,
    HasDerivAt (fun t : ℝ => R₁.U.π (T₁.expt (t • Z)) (B P y)) (B (fockAct1 p q r s Z P) y) 0
  tgt : ∀ Z ∈ upq r s, ∀ P y,
    HasDerivAt (fun t : ℝ => B P (R₂.U.π (T₂.expt (t • Z)) y)) (-B (fockAct2 p q r s Z P) y) 0

variable {D : D7}

def glue {a b : ℕ} (P : D.what₂.Tau → LPol b a) : PolF D b a :=
  ∏ τ, MvPolynomial.rename (fun s => (τ, s)) (P τ)

open Classical in

def GlueLaw (D : D7) (a b : ℕ) : Prop :=
  Submodule.span ℂ (Set.range (glue : (D.what₂.Tau → LPol b a) → PolF D b a)) = ⊤ ∧
    ∀ (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (P : D.what₂.Tau → LPol b a),
      (∀ X, fockS τ ε ε' X (glue P) = glue (Function.update P τ (locS ε ε' X (P τ)))) ∧
        ∀ Y, fockT τ ε ε' Y (glue P) = glue (Function.update P τ (locT ε ε' Y (P τ)))

variable {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S')

structure LocIt (τ : D.what₂.Tau) (aS aT : ℚ) (A : LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ) : Prop where
  sm : ∀ P y, A P y ∈ M.sm τ
  ne : ∃ P, ∃ y ∈ M'.sm τ, A P y ≠ 0
  adj : ∀ P w, ∃ w', ∀ y, ⟪w, A P y⟫_ℂ = ⟪w', y⟫_ℂ
  src : ∀ X ∈ lieAt V τ, ∀ P y, HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (A P y))
    (A (locS (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) P - ((aT : ℂ) * X.trace) • P) y) 0
  tgt : ∀ Y ∈ lieAt W τ, ∀ P y, HasDerivAt (fun t : ℝ => A P (M'.rep τ (NormedSpace.exp (t • Y)) y))
    (-A (locT (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) P + ((aS : ℂ) * Y.trace) • P) y) 0

def srcOp (τ : D.what₂.Tau) (aT : ℚ) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Module.End ℂ (PolF D W.rank V.rank) :=
  fockS τ (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) + (-((aT : ℂ) * X.trace)) • 1

def tgtOp (τ : D.what₂.Tau) (aS : ℚ) (Y : Matrix (Fin W.rank) (Fin W.rank) ℂ) : Module.End ℂ (PolF D W.rank V.rank) :=
  fockT τ (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) + ((aS : ℂ) * Y.trace) • 1

structure GlobIt (aS aT : D.what₂.Tau → ℚ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M)
    (I : PolF D W.rank V.rank →ₗ[ℂ] (⨂[ℂ] τ, M'.H τ) →ₗ[ℂ] ⨂[ℂ] τ, M.H τ) : Prop where
  incl : ∀ φ v, inclT M (It φ v) = I φ (inclT M' v)
  ne : It ≠ 0
  adj : ∀ φ w, ellT M w ∘ₗ I φ ∈ Submodule.span ℂ (Set.range (ellT M'))
  src : ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ x w,
    HasDerivAt (fun t : ℝ => ellT M w (actT M τ (NormedSpace.exp (t • X)) (I φ x)))
      (ellT M w (I (srcOp M M' τ (aT τ) X φ) x)) 0
  tgt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ x w,
    HasDerivAt (fun t : ℝ => ellT M w (I φ (actT M' τ (NormedSpace.exp (t • Y)) x)))
      (-ellT M w (I (tgtOp M M' τ (aS τ) Y φ) x)) 0

structure TensorLaw : Prop where
  sep : ∀ x : ⨂[ℂ] τ, M.H τ, (∀ w, ellT M w x = 0) → x = 0
  inj : Function.Injective (inclT M)
  one : ∀ τ, actT M τ 1 = LinearMap.id
  mul : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    actT M τ (g * g') = actT M τ g ∘ₗ actT M τ g'
  adj : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, ∃ w', ellT M w ∘ₗ actT M τ g = ellT M w'

def ChosenSeries (X : ProvA) : Prop :=
  ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → HasParam (X.ds p q lam) lam

end GlobalTheory.Chain.RealIt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassTermConvergesOfLintegralUnfoldingEq
section
open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

namespace GlobalTheory.ClassTerm

theorem hasClassInt_of_lintegral_eq : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [DiscreteTopology Γ] (γ : H), γ ∈ Γ → ∀ (μ : Measure H) (𝓕 : Set H) (ν : Measure (Quot (cent γ))) (a : ℝ≥0∞), a < ⊤ → (∀ G : H → ℝ≥0∞, Measurable G → ∫⁻ x in 𝓕, ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, G (x⁻¹ * δ * x) ∂μ = a * ∫⁻ q, G (q.out⁻¹ * γ * q.out) ∂ν) → ∀ (f : H → ℂ) (c : ℂ), Continuous f → HasCompactSupport f → Integrable (fun q : Quot (cent γ) => f (q.out⁻¹ * γ * q.out)) ν → ∫ q, f (q.out⁻¹ * γ * q.out) ∂ν = c → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.HasClassInt Γ μ 𝓕 γ f (a.toReal * c) := by
  intro H _ _ _ _ _ _ _ _ Γ _ γ hγ μ 𝓕 ν a ha hL f c hf hfc hint hc
  classical
  have hmemΓ : ∀ δ ∈ GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, δ ∈ Γ := by
    rintro _ ⟨g, hg, rfl⟩
    exact mul_mem (mul_mem (inv_mem hg) hγ) hg
  let ι : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ → Γ := fun δ => ⟨δ, hmemΓ _ δ.2⟩
  have hι : Function.Injective ι := fun a b h => Subtype.ext (congrArg Subtype.val h :)
  haveI : Countable (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ) := hι.countable
  have hcont : ∀ δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, Continuous fun x : H => x⁻¹ * (δ : H) * x := fun δ => by
    fun_prop
  have hfm : Measurable f := hf.measurable
  have hfs : StronglyMeasurable f := hf.stronglyMeasurable

  have hfin : ∀ x, (Function.support fun δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ => f (x⁻¹ * δ * x)).Finite := by
    intro x
    have hC : IsCompact ((fun z => x * z * x⁻¹) '' tsupport f) := hfc.isCompact.image (by fun_prop)
    refine ((finite_mem_compact (Γ := Γ) hC).preimage hι.injOn).subset ?_
    intro δ hδ
    refine ⟨x⁻¹ * δ * x, subset_tsupport f hδ, ?_⟩
    show x * (x⁻¹ * (δ : H) * x) * x⁻¹ = δ
    group
  have hsum : ∀ x, Summable fun δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ => f (x⁻¹ * δ * x) := fun x =>
    summable_of_hasFiniteSupport (hfin x)

  have hem : Measurable (fun q : Quot (cent γ) => q.out⁻¹ * γ * q.out) := by
    have hli : LeftInv (cent γ) (fun x : H => x⁻¹ * γ * x) := by
      intro t ht x
      have hcomm : γ * t = t * γ := Subgroup.mem_centralizer_iff.1 ht γ (Set.mem_singleton γ)
      have h1 : t⁻¹ * γ * t = γ := by rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
      calc (t * x)⁻¹ * γ * (t * x) = x⁻¹ * (t⁻¹ * γ * t) * x := by group
        _ = x⁻¹ * γ * x := by rw [h1]
    exact measurable_descend hli (by fun_prop : Continuous fun x : H => x⁻¹ * γ * x).measurable
  set m1 : Measure H := Measure.sum fun δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ =>
    (μ.restrict 𝓕).map (fun x => x⁻¹ * (δ : H) * x) with hm1
  set m2 : Measure H := a • ν.map (fun q : Quot (cent γ) => q.out⁻¹ * γ * q.out) with hm2
  have hm12 : m1 = m2 := Measure.ext_of_lintegral _ fun G hG => by
    rw [hm1, hm2, lintegral_sum_measure, lintegral_smul_measure, lintegral_map hG hem,
      tsum_congr (fun δ => lintegral_map hG (hcont δ).measurable), smul_eq_mul, ← hL G hG]
    exact (lintegral_tsum (f := fun (δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ) x => G (x⁻¹ * (δ : H) * x))
      (fun δ => (hG.comp (hcont δ).measurable).aemeasurable)).symm
  have hint2 : Integrable f (ν.map fun q : Quot (cent γ) => q.out⁻¹ * γ * q.out) :=
    (integrable_map_measure hfs.aestronglyMeasurable hem.aemeasurable).2 hint
  have hintm2 : Integrable f m2 := hint2.smul_measure ha.ne
  have hintm1 : Integrable f m1 := hm12 ▸ hintm2
  have hval2 : ∫ x, f x ∂m2 = (a.toReal : ℂ) * c := by
    rw [hm2, integral_smul_measure, integral_map hem.aemeasurable hfs.aestronglyMeasurable, hc, Complex.real_smul]
  have hval1 : ∫ x, f x ∂m1 = ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, ∫ x in 𝓕, f (x⁻¹ * δ * x) ∂μ := by
    rw [hm1, integral_sum_measure (hm1 ▸ hintm1)]
    exact tsum_congr fun δ => integral_map (hcont δ).measurable.aemeasurable hfs.aestronglyMeasurable
  have hfinL : ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, ∫⁻ x in 𝓕, ‖f (x⁻¹ * δ * x)‖ₑ ∂μ ≠ ∞ := by
    have h := hintm1.hasFiniteIntegral
    change ∫⁻ x, ‖f x‖ₑ ∂m1 < ∞ at h
    rw [hm1, lintegral_sum_measure] at h
    refine ne_of_lt (lt_of_eq_of_lt (tsum_congr fun δ => ?_) h)
    exact (lintegral_map hfm.enorm (hcont δ).measurable).symm
  have hKm : Measurable (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel Γ γ f) :=
    measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ)))
      (f := fun (s : Finset (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ)) x => ∑ δ ∈ s, f (x⁻¹ * (δ : H) * x))
      (fun s => Finset.measurable_sum s fun δ _ => hfm.comp (hcont δ).measurable)
      (tendsto_pi_nhds.2 fun x => (hsum x).hasSum)
  refine ⟨hsum, ⟨hKm.aestronglyMeasurable, ?_⟩, ?_⟩
  · change ∫⁻ x, ‖GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel Γ γ f x‖ₑ ∂μ.restrict 𝓕 < ∞
    calc ∫⁻ x, ‖GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel Γ γ f x‖ₑ ∂μ.restrict 𝓕
        ≤ ∫⁻ x, ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, ‖f (x⁻¹ * δ * x)‖ₑ ∂μ.restrict 𝓕 :=
          lintegral_mono fun x => enorm_tsum_le_tsum_enorm
      _ = ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, ∫⁻ x in 𝓕, ‖f (x⁻¹ * δ * x)‖ₑ ∂μ :=
          lintegral_tsum (fun δ => (hfm.comp (hcont δ).measurable).enorm.aemeasurable)
      _ < ∞ := hfinL.lt_top
  · show ∫ x in 𝓕, ∑' δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ, f (x⁻¹ * δ * x) ∂μ = _
    rw [integral_tsum (f := fun (δ : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ratClass Γ γ) x => f (x⁻¹ * (δ : H) * x)) (fun δ => (hfm.comp (hcont δ).measurable).aestronglyMeasurable) hfinL, ← hval1, hm12, hval2]

end GlobalTheory.ClassTerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjLocalTwistedLFactorRatioInertEqZetaSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta

theorem conj_LvTw_div_dLoc_inert : ∀ (D : D7) (B : Fam D.host.E) (m : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w) → Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2 → (B w).map star = B w → (m w : ℂ) = (-1) ^ D.R.nV → quadSign D v = -1 → starRingEnd ℂ (LvTw B m v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ)) = eulerFac (B w) (((star (m w) : ℂˣ) : ℂ) * ((qV D.host.F v : ℂ) ^ (D.R.t + 1))⁻¹) * ∏ j ∈ Finset.range D.R.r, (1 - (-(qV D.host.F v : ℂ)) ^ j * (((star (m w) : ℂˣ) : ℂ) * ((qV D.host.F v : ℂ) ^ (D.R.r + D.R.t))⁻¹)) := by
  intro D B m v w hv hq hB hm hs
  set q : ℕ := Ideal.absNorm v.asIdeal with hqdef
  have hqV : qV D.host.F v = q := rfl
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (GlobalTheory.LFun.one_lt_absNorm v).ne_bot
  have hstar : ((star (m w) : ℂˣ) : ℂ) = (-1) ^ D.R.nV := by
    rw [Units.coe_star, hm]; simp
  have hinv : ((m w : ℂ))⁻¹ = (-1) ^ D.R.nV := by rw [hm, ← inv_pow, inv_neg, inv_one]
  have hnp : npow v (-(2 * ((1 + (D.R.t : ℂ)) / 2))) = ((q : ℂ) ^ (D.R.t + 1))⁻¹ := by
    rw [npow, show -(2 * ((1 + (D.R.t : ℂ)) / 2)) = -((D.R.t + 1 : ℕ) : ℂ) by push_cast; ring,
      Complex.cpow_neg, Complex.cpow_natCast]
  rw [LvTw_inert B m hv hq, hnp, hinv, hstar, hqV, map_div₀, Complex.conj_ofReal]
  have hx : starRingEnd ℂ ((-1 : ℂ) ^ D.R.nV * ((q : ℂ) ^ (D.R.t + 1))⁻¹) =
      (-1 : ℂ) ^ D.R.nV * ((q : ℂ) ^ (D.R.t + 1))⁻¹ := by simp
  have hconjE : starRingEnd ℂ (eulerFac (B w) ((-1 : ℂ) ^ D.R.nV * ((q : ℂ) ^ (D.R.t + 1))⁻¹)) =
      eulerFac (B w) ((-1 : ℂ) ^ D.R.nV * ((q : ℂ) ^ (D.R.t + 1))⁻¹) := by
    conv_rhs => rw [← hB]
    simp only [eulerFac, eulerPoly, map_inv₀, map_multiset_prod, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, map_sub, map_one, map_mul, Units.coe_star, hx]
    rfl
  rw [hconjE, div_eq_mul_inv]
  congr 1
  have hqt : ∀ i : ℕ, quadTerm D v i = (-1 : ℝ) ^ i / (q : ℝ) ^ i := by
    intro i; rw [quadTerm, hs]
  have hd : ((dLoc D v : ℝ) : ℂ)⁻¹ = ∏ i ∈ Finset.Ioc D.R.t (D.R.r + D.R.t), (1 - (-1 : ℂ) ^ i / (q : ℂ) ^ i) := by
    rw [dLoc, Complex.ofReal_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr (by rfl) fun i _ => ?_
    rw [Complex.ofReal_inv, inv_inv, hqt]
    push_cast; ring
  rw [hd]
  have key : ∀ a j : ℕ, (-1 : ℂ) ^ a / (q : ℂ) ^ a = (-(q : ℂ)) ^ j * ((-1 : ℂ) ^ (a + j) * ((q : ℂ) ^ (a + j))⁻¹) := by
    intro a j
    calc (-1 : ℂ) ^ a / (q : ℂ) ^ a = ((-1 : ℂ) ^ j * (-1) ^ j) * ((-1 : ℂ) ^ a / (q : ℂ) ^ a) * ((q : ℂ) ^ j * ((q : ℂ) ^ j)⁻¹) := by
          rw [← mul_pow, neg_one_mul, neg_neg, one_pow, mul_inv_cancel₀ (pow_ne_zero _ hq0)]; ring
      _ = _ := by rw [neg_pow, pow_add, pow_add, mul_inv]; ring
  refine Finset.prod_nbij' (fun i => D.R.r + D.R.t - i) (fun j => D.R.r + D.R.t - j) ?_ ?_ ?_ ?_ ?_
  · intro i hi; rw [Finset.mem_Ioc] at hi; rw [Finset.mem_range]; omega
  · intro j hj; rw [Finset.mem_range] at hj; rw [Finset.mem_Ioc]; omega
  · intro i hi; rw [Finset.mem_Ioc] at hi; omega
  · intro j hj; rw [Finset.mem_range] at hj; omega
  · intro i hi
    have hi' := Finset.mem_Ioc.1 hi
    have e : D.R.nV = i + (D.R.r + D.R.t - i) := by show D.R.r + D.R.t = _; omega
    rw [e, key i (D.R.r + D.R.t - i), ← e]
    show _ = 1 - _ * (_ * ((q : ℂ) ^ (D.R.r + D.R.t))⁻¹)
    rfl

end GlobalTheory.FinZeta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjLocalTwistedLFactorRatioSplitEqZetaSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocZetaSplit

theorem prod_map_conj_eq (A : Multiset ℂˣ) (hA : A.map star = A.map (·⁻¹)) (f : ℂ → ℂ) :
    (A.map fun b : ℂˣ => f (starRingEnd ℂ (b : ℂ))).prod = (A.map fun b : ℂ ˣ => f ((b : ℂ)⁻¹)).prod := by
  have h := congrArg (fun M : Multiset ℂˣ => (M.map fun b : ℂˣ => f (b : ℂ)).prod) hA
  simpa [Multiset.map_map, Function.comp_def, Units.coe_star, Units.val_inv_eq_inv_val] using h

theorem conj_LvTw_div_dLoc : ∀ (D : D7) (B : Fam D.host.E) (m : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w w' : HeightOneSpectrum (𝓞 D.host.E)), w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w ∨ u = w') → Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal → Ideal.absNorm w'.asIdeal = Ideal.absNorm v.asIdeal → B w' = (B w).map (·⁻¹) → (B w).map star = (B w).map (·⁻¹) → m w * m w' = 1 → ‖(m w : ℂ)‖ = 1 → quadSign D v = 1 → starRingEnd ℂ (LvTw B m v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ)) = eulerFac ((B w).map (star (m w) * ·)) (npow w (-((1 + (D.R.t : ℂ)) / 2))) * eulerFac ((B w).map fun β => (star (m w) * β)⁻¹) (npow w (-((1 + (D.R.t : ℂ)) / 2))) * ∏ i ∈ Finset.Ioc D.R.t (D.R.r + D.R.t), (1 - ((qV D.host.E w : ℂ) ^ i)⁻¹) := by
  intro D B m v w w' hne hv hqw hqw' hB' hstar hm1 hnorm hsign
  classical
  set s : ℂ := (1 + (D.R.t : ℂ)) / 2 with hs
  set X : ℂ := npow w (-s) with hXdef
  set μ : ℂ := (m w : ℂ) with hμ
  have hX : starRingEnd ℂ X = X := by
    have : X = (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-((1 + (D.R.t : ℝ)) / 2)) : ℝ) := by
      rw [hXdef, npow, Complex.ofReal_cpow (by positivity)]
      push_cast
      rfl
    rw [this, Complex.conj_ofReal]
  have hX' : npow w' (-s) = X := by rw [hXdef, npow, npow, hqw, hqw']
  have hinv : ((m w' : ℂ))⁻¹ = μ := inv_eq_of_mul_eq_one_left (by rw [hμ, ← Units.val_mul, hm1, Units.val_one])
  have hμc : starRingEnd ℂ μ = μ⁻¹ := (Complex.inv_eq_conj hnorm).symm
  have hμc' : starRingEnd ℂ μ⁻¹ = μ := by rw [map_inv₀, hμc, inv_inv]
  have e : Formalism.L2.Host.aboveF (L := D.host.E) D.host.F v = {w, w'} := by ext u; simp [mem_aboveF, hv]
  have hL : LvTw B m v s = ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod *
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod := by
    rw [LvTw_eq, e, Finset.prod_pair hne, hB', Multiset.map_map, hX', hinv]
    simp only [Function.comp_def, Units.val_inv_eq_inv_val]
    rfl
  have hc1 : starRingEnd ℂ ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod =
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod := by
    rw [map_multiset_prod, Multiset.map_map]
    have := prod_map_conj_eq (B w) hstar (fun z => (1 - z * μ * X)⁻¹)
    simp only [Function.comp_def, map_inv₀, map_sub, map_one, map_mul, hμc', hX]
    exact this
  have hc2 : starRingEnd ℂ ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod =
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod := by
    rw [map_multiset_prod, Multiset.map_map]
    have := prod_map_conj_eq (B w) hstar (fun z => (1 - z⁻¹ * μ⁻¹ * X)⁻¹)
    simp only [inv_inv] at this
    simp only [Function.comp_def, map_inv₀, map_sub, map_one, map_mul, hμc, hX]
    exact this
  have hstarμ : ((star (m w) : ℂˣ) : ℂ) = μ⁻¹ := by rw [Units.coe_star, ← hμc]; rfl
  have hr1 : eulerFac ((B w).map (star (m w) * ·)) X = ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod := by
    rw [eulerFac_eq_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
    simp only [Function.comp_apply, Units.val_mul, hstarμ]
    ring
  have hr2 : eulerFac ((B w).map fun β => (star (m w) * β)⁻¹) X =
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod := by
    rw [eulerFac_eq_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
    simp only [Function.comp_apply, Units.val_inv_eq_inv_val, Units.val_mul, hstarμ, mul_inv, inv_inv]
    ring
  have hd : (dLoc D v : ℂ) = (∏ i ∈ Finset.Ioc D.R.t (D.R.r + D.R.t), (1 - ((qV D.host.E w : ℂ) ^ i)⁻¹))⁻¹ := by
    rw [← Finset.prod_inv_distrib, dLoc]
    push_cast
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [quadTerm, hsign, qV, hqw]
  rw [map_div₀, Complex.conj_ofReal, hd, div_inv_eq_mul, hL, map_mul, hc1, hc2, hr1, hr2]
  ring

end GlobalTheory.LocZetaSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedThetaCharactersRestrictionRamification
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjSplitChars
open Formalism.L2.Host

variable {E : Type} [Field E] [NumberField E]

theorem twVal_of_unit (χ : HChar E) (w : ℝ) (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ) (hk : P.valuation E (k : E) = 1) :
    twVal χ w P k = ((χ.locK P k : ℂˣ) : ℂ) := by
  have h0 : Formalism.L2.Host.ordF P k = 0 := by simp [Formalism.L2.Host.ordF, hk]
  simp [twVal, h0]

theorem isClopen_oneUnits (P : HeightOneSpectrum (𝓞 E)) :
    IsClopen {x : (P.adicCompletion E)ˣ | Valued.v ((x : P.adicCompletion E) - 1) < 1} := by
  have := (Valued.isClopen_ball (P.adicCompletion E) (r := 1)).preimage
      (f := fun x : (P.adicCompletion E)ˣ => (x : P.adicCompletion E) - 1)
      ((Units.continuous_val (M := P.adicCompletion E)).sub continuous_const)
  convert this using 1
  ext x
  simp

theorem tameAt_of_locK (χ : HChar E) (P : HeightOneSpectrum (𝓞 E))
    (h : ∀ u : Eˣ, P.valuation E ((u : E) - 1) < 1 → χ.locK P u = 1) : χ.TameAt P := by
  have key : ∀ x : (P.adicCompletion E)ˣ, Valued.v ((x : P.adicCompletion E) - 1) < 1 → χ.loc P x = 1 := by
    intro x
    refine (GlobalTheory.Mem.Chr.Determ.denseRange_atFin P).induction_on
      (p := fun x => Valued.v ((x : P.adicCompletion E) - 1) < 1 → χ.loc P x = 1) x ?_ fun k hk => h k ?_
    · exact isClosed_imp (isClopen_oneUnits P).2
        (isClosed_eq (χ.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele P)) continuous_const)
    · have e : ((atFin P k : (P.adicCompletion E)ˣ) : P.adicCompletion E) - 1 =
          algebraMap E (P.adicCompletion E) ((k : E) - 1) := by
        rw [map_sub, map_one]; rfl
      rwa [e, Formalism.UG.P.levelaf_valued_algebraMap] at hk
  intro x _ hx
  refine key x (lt_of_le_of_lt hx ?_)
  rw [← WithZero.exp_zero]
  exact WithZero.exp_lt_exp.2 (by norm_num)

theorem locK_conj {s : ℂ ≃+* ℂ} {w : ℝ} {χ χ' : HChar E} (h : IsGalConj s w χ χ') (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ)
    (hk : P.valuation E (k : E) = 1) : ((χ'.locK P k : ℂˣ) : ℂ) = s ((χ.locK P k : ℂˣ) : ℂ) := by
  have := h P k
  rwa [twVal_of_unit _ _ _ _ hk, twVal_of_unit _ _ _ _ hk] at this

theorem unrAt_conj {s : ℂ ≃+* ℂ} {w : ℝ} {χ χ' : HChar E} (h : IsGalConj s w χ χ') {P : HeightOneSpectrum (𝓞 E)}
    (hu : χ.UnrAt P) : χ'.UnrAt P :=
  GlobalTheory.EtaConjType.unrAt_of_locK χ' P fun u hu' => Units.ext (by
    rw [locK_conj h P u hu', GlobalTheory.NormOneUnit.locK_unr hu hu', Units.val_one, map_one])

theorem tameAt_conj {s : ℂ ≃+* ℂ} {w : ℝ} {χ χ' : HChar E} (h : IsGalConj s w χ χ') {P : HeightOneSpectrum (𝓞 E)}
    (ht : χ.TameAt P) : χ'.TameAt P := by
  refine tameAt_of_locK χ' P fun u hu => Units.ext ?_
  have h1 : P.valuation E ((1 : Eˣ) : E) = 1 := by simp
  have hu1 : P.valuation E (u : E) = 1 := by
    have := Valuation.map_eq_of_sub_lt (P.valuation E) (x := 1) (y := (u : E)) (by rwa [map_one])
    rwa [map_one] at this
  rw [locK_conj h P u hu1, GlobalTheory.NormOneUnit.locK_tame ht h1 (by simpa using hu), map_one, Units.val_one, map_one]

open Classical in

theorem conj_chars_res : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ i t s cμ cη m, IsConjChars R i t s cμ cη m → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → GlobalTheory.StepLaw.ResAt cμ PP (m PP) ∧ GlobalTheory.StepLaw.ResAt (cμ * cη⁻¹) PP (m PP)) ∧ (∀ Z : Finset (Pl D.host.E), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → PP ∈ Z) → GlobalTheory.StepLaw.UnrOff cμ Z ∧ GlobalTheory.StepLaw.UnrOff (cμ * cη⁻¹) Z) ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ finS R t → UnrAt cμ w ∧ UnrAt (cμ * cη⁻¹) w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL i t s cμ cη m hc
  obtain ⟨μ', η', hμ, hη, ecμ, ecη, hres⟩ := hc
  obtain ⟨-, p1, p2, p3⟩ := GlobalTheory.T.levelCharacters_unramified_off_levelPlaces D T R.toLevCh A.μ0 hL t
  have uη : ∀ P, η'.UnrAt P := fun P => unrAt_conj hη (R.C.isEta.unr P)
  have uμ : ∀ P : Pl D.host.E, (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → PP.under (𝓞 D.host.F) ≠ P.under (𝓞 D.host.F)) →
      μ'.UnrAt P := fun P hP => unrAt_conj hμ (((p3 P hP).2 i).mul (p3 P hP).1)
  have tμ : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → μ'.TameAt PP := by
    intro PP hPP
    refine tameAt_conj hμ ?_
    rcases hPP with hP | hP
    · exact ((R.C.isMu0 i).tame PP).mul ((p1 PP hP).levelLe 1)
    · exact ((p2 PP hP i).levelLe 1).mul (hL.xi_tame t PP)
  have rη : ∀ PP, GlobalTheory.StepLaw.ResAt cη⁻¹ PP 1 := fun PP => by
    have := ((GlobalTheory.T.ideleChar_restrict_localUnits_residueChar D cη η' ecη PP).2 (uη PP)).inv
    rwa [inv_one] at this
  have uoη : ∀ Z, GlobalTheory.StepLaw.UnrOff cη Z := fun Z v ε hε _ =>
    GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D cη η' ecη v ε hε fun P _ => uη P
  refine ⟨fun PP hPP => ?_, fun Z hZ => ?_, fun w hw => ?_⟩
  · have h1 := (GlobalTheory.T.ideleChar_restrict_localUnits_residueChar D cμ μ' ecμ PP).1 (m PP) (tμ PP hPP) (hres PP hPP)
    refine ⟨h1, ?_⟩
    have := h1.mul (rη PP)
    rwa [mul_one] at this
  · have h1 : GlobalTheory.StepLaw.UnrOff cμ Z := fun v ε hε hv =>
      GlobalTheory.T.isUnramifiedAtPlaceIdempotent_of_heckeChar_unramified_above D cμ μ' ecμ v ε hε fun P hP => uμ P fun PP hPP => hP ▸ hv PP (hZ PP hPP)
    exact ⟨h1, h1.mul (uoη Z).inv⟩
  · have hw' : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → PP.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F) := fun PP hPP he =>
      hw (Finset.mem_image.2 ⟨PP, Finset.mem_union.2 hPP, he⟩)
    have h1 : UnrAt cμ w := (unrAt_iff_of_chrEq ecμ w).2 (uμ w hw')
    exact ⟨h1, h1.mul ((unrAt_iff_of_chrEq ecη w).2 (uη w)).inv⟩

end GlobalTheory.ConjSplitChars

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContDiffProdLinearMapUpperRightLowerRightBlocks
section
open MeasureTheory

namespace GlobalTheory.FockFamily

theorem contDiff_blockB_blockD {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (J : ℝ → (V × V) →ₗ[ℝ] (V × V)) (hJ : ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockB (J t)) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockD (J t)) := by
  constructor
  · rw [contDiff_clm_apply_iff]
    intro q
    simpa only [blockB_apply] using (hJ (0, q)).fst
  · rw [contDiff_clm_apply_iff]
    intro q
    simpa only [blockD_apply] using (hJ (0, q)).snd

end GlobalTheory.FockFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CutIsometry
section
namespace GlobalTheory.TruncationIsometry

open Matrix

theorem cT_cut {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (ε : R) (hσ : σ ε = ε)
    (M : Matrix (Fin n) (Fin n) R) :
    Formalism.UG.cT σ (ε • M + ((1 : R) - ε) • (1 : Matrix (Fin n) (Fin n) R)) =
      ε • Formalism.UG.cT σ M + ((1 : R) - ε) • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Formalism.UG.cT, hσ]
  · have h' : j ≠ i := fun e => h e.symm
    simp [Formalism.UG.cT, hσ, Matrix.one_apply_ne h, Matrix.one_apply_ne h']

theorem cut_isometry {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (ε : R) (hσ : σ ε = ε) (hε : ε * ε = ε)
    (J M : Matrix (Fin n) (Fin n) R) (hM : Formalism.UG.cT σ M * J * M = J) :
    Formalism.UG.cT σ (ε • M + ((1 : R) - ε) • (1 : Matrix (Fin n) (Fin n) R)) * J *
      (ε • M + ((1 : R) - ε) • (1 : Matrix (Fin n) (Fin n) R)) = J := by
  have h1 : ε * (1 - ε) = 0 := by rw [mul_sub, mul_one, hε, sub_self]
  have h2 : (1 - ε) * ε = 0 := by rw [mul_comm, h1]
  have h3 : (1 - ε) * (1 - ε) = 1 - ε := by rw [mul_sub, mul_one, h2, sub_zero]
  rw [cT_cut σ ε hσ M]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    smul_add, smul_smul, hM, hε, h1, h2, h3, zero_smul, add_zero, zero_add]
  rw [← add_smul, add_sub_cancel, one_smul]

end GlobalTheory.TruncationIsometry
end

