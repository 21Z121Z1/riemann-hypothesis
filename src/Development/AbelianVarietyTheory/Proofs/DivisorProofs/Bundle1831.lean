import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1797
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1768
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1800
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierSchwartzStable
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylFour

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F : Type} [Field F] [NumberField F]

theorem exists_circle_conductor (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl F) (h1 : ∃ x, psiLoc ψ v x ≠ 1) :
    ∃ (χ : AddChar (Fv F v) Circle) (c : (Fv F v)ˣ), GlobalTheory.SplitWeil.HasConductor χ c ∧
      ∀ x, (χ x : ℂ) = GlobalTheory.LatVac.psiAt ψ v x := by
  have hc : Continuous (GlobalTheory.LatVac.psiAt ψ v) := GlobalTheory.VacAny.continuous_psiV hψ v
  let χ : AddChar (Fv F v) Circle :=
    { toFun := fun x => ⟨GlobalTheory.LatVac.psiAt ψ v x, mem_sphere_zero_iff_norm.2 (GlobalTheory.norm_addChar_nonarch _ hc x)⟩
      map_zero_eq_one' := Circle.ext (by simp)
      map_add_eq_mul' := fun a b => Circle.ext (AddChar.map_add_eq_mul _ a b) }
  have hχ : ∀ x, (χ x : ℂ) = GlobalTheory.LatVac.psiAt ψ v x := fun _ => rfl
  have hχc : Continuous χ := continuous_induced_rng.2 hc
  have hχ1 : χ ≠ 1 := fun h => by
    obtain ⟨x, hx⟩ := h1
    refine hx ?_
    rw [← GlobalTheory.LatVac.psiAt_apply, ← hχ, h]
    simp
  obtain ⟨c, hc0⟩ := GlobalTheory.SplitWeil.exists_hasConductor_of_continuous χ hχc hχ1
  exact ⟨χ, c, hc0, hχ⟩

theorem isSelfDualFor_measV (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl F) (h1 : ∃ x, psiLoc ψ v x ≠ 1) :
    IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) (measV ψ v) := by
  obtain ⟨χ, c, hc, hχ⟩ := exists_circle_conductor ψ hψ v h1
  have h : ∃ ν, IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) ν := by
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    obtain ⟨ν, hν⟩ := GlobalTheory.SplitWeil.exists_isSelfDual_of_hasConductor hc
    refine ⟨ν, hν.1, fun f hf => ?_⟩
    simpa only [hχ] using hν.2 f hf
  rw [measV, dif_pos h]
  exact h.choose_spec

theorem fourV_sb : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : Pl F, (∃ x, psiLoc ψ v x ≠ 1) →
    ∀ (κ : Type) [Fintype κ],
    (∀ φ ∈ SB (κ → Fv F v), fourV ψ v φ ∈ SB (κ → Fv F v)) ∧
    (∀ φ ∈ SB (κ → Fv F v), ∀ χ ∈ SB (κ → Fv F v), fourV ψ v (φ + χ) = fourV ψ v φ + fourV ψ v χ) ∧
    ∀ (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ SB (κ → Fv F v), schr (GlobalTheory.LatVac.psiAt ψ v) w φ ∈ SB (κ → Fv F v) := by
  intro F _ _ ψ hψ v h1 κ _
  classical
  have hcont : Continuous (GlobalTheory.LatVac.psiAt ψ v) := GlobalTheory.VacAny.continuous_psiV hψ.1 v
  obtain ⟨χ, c, hc, hχ⟩ := exists_circle_conductor ψ hψ.1 v h1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : SecondCountableTopology (Fv F v) := GlobalTheory.SplitWeil.secondCountable _
  haveI := (isSelfDualFor_measV ψ hψ.1 v h1).1
  refine ⟨fun φ hφ => ?_, fun φ hφ φ' hφ' => ?_, fun w φ hφ => GlobalTheory.SchrSBFin.schr_mem_SB v _ hcont w φ hφ⟩
  · have h := GlobalTheory.SplitWeil.FourierPi.fourier_mem_SB (Measure.pi fun _ : κ => measV ψ v) hc hφ
    simp only [hχ] at h
    exact h
  · have hint : ∀ f ∈ SB (κ → Fv F v), ∀ y : κ → Fv F v,
        Integrable (fun x => f x * GlobalTheory.LatVac.psiAt ψ v (x ⬝ᵥ y)) (Measure.pi fun _ : κ => measV ψ v) := fun f hf y =>
      Continuous.integrable_of_hasCompactSupport
        (hf.1.continuous.mul (hcont.comp (continuous_id.dotProduct continuous_const))) hf.2.mul_right
    funext y
    simp only [fourV, Pi.add_apply, add_mul]
    exact integral_add (hint φ hφ y) (hint φ' hφ' y)

end GlobalTheory.WeylFour

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalGaussSumIntegerDvdResidueCardPow
section
noncomputable section

namespace GlobalTheory.GaussDiv

section Finite

theorem exists_int_of_pow_eq_one {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {z : ℂ} {n : ℕ} (hn : 0 < n)
    (hz : z ^ n = 1) (h : z ∈ Set.range σ) : ∃ g : NumberField.RingOfIntegers K, σ g = z := by
  obtain ⟨x, rfl⟩ := h
  have hx : x ^ n = 1 := σ.injective (by rw [map_pow, hz, map_one])
  have hi : IsIntegral ℤ x := IsIntegral.of_pow hn (by rw [hx]; exact isIntegral_one)
  exact ⟨⟨x, hi⟩, rfl⟩

theorem exists_int_gauss {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {R : Type} [CommRing R] [Fintype R]
    [DecidableEq R] [Fintype Rˣ] (m : Ideal R) (hm : ∀ x : R, IsUnit x ↔ x ∉ m) (ψ : AddChar R ℂ)
    (hψ : ∀ d : R, (∀ x, ψ (d * x) = 1) → d = 0) (χ : Rˣ →* ℂ) (hχ : ∀ u, ‖χ u‖ = 1) (t₀ : Rˣ)
    (ht₀ : ∀ x ∈ m, ((t₀ : R) - 1) * x = 0) (hχt₀ : χ t₀ ≠ 1) (hr : ∀ u, χ u ∈ Set.range σ)
    (hζ : ∀ ζ : ℂ, ζ ^ Fintype.card R = 1 → ζ ∈ Set.range σ) :
    ∃ g g' : NumberField.RingOfIntegers K, σ g = ∑ u : Rˣ, (χ u)⁻¹ * ψ u ∧
      g * g' = (Fintype.card R : NumberField.RingOfIntegers K) := by
  have hN := GlobalTheory.gauss_units_norm_sq m hm ψ hψ χ (map_mul χ) hχ t₀ ht₀ hχt₀
  have h1 : ∀ u, ∃ g : NumberField.RingOfIntegers K, σ g = χ u := fun u =>
    exists_int_of_pow_eq_one σ (Fintype.card_pos (α := Rˣ)) (by rw [← map_pow, pow_card_eq_one, map_one]) (hr u)
  have h2 : ∀ y, ∃ g : NumberField.RingOfIntegers K, σ g = ψ y := fun y => by
    have : ψ y ^ Fintype.card R = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
    exact exists_int_of_pow_eq_one σ (Fintype.card_pos (α := R)) this (hζ _ this)
  choose a ha using h1
  choose b hb using h2
  have hinv : ∀ u, χ u⁻¹ = (χ u)⁻¹ := fun u =>
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])
  have hg : σ ((∑ u : Rˣ, a u⁻¹ * b u : NumberField.RingOfIntegers K) : K) = ∑ u : Rˣ, (χ u)⁻¹ * ψ u := by
    simp only [map_sum, map_mul, ha, hb, hinv]
  have hg' : σ ((∑ u : Rˣ, a u * b (-u) : NumberField.RingOfIntegers K) : K) =
      starRingEnd ℂ (∑ u : Rˣ, (χ u)⁻¹ * ψ u) := by
    simp only [map_sum, map_mul, ha, hb]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Complex.inv_eq_conj (hχ z), Complex.conj_conj, AddChar.map_neg_eq_conj]
  refine ⟨_, ∑ u : Rˣ, a u * b (-u), hg, ?_⟩
  apply NumberField.RingOfIntegers.ext
  apply σ.injective
  have e : ∀ x y : NumberField.RingOfIntegers K, σ ((x * y : NumberField.RingOfIntegers K) : K) = σ x * σ y :=
    fun x y => by simp only [map_mul]
  rw [e, hg, hg', Complex.mul_conj, Complex.normSq_eq_norm_sq, hN]
  simp

end Finite

section Local

open ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.GaussNonvanish

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem card_res (e : ℕ) : Fintype.card (Res k e) = resCard k ^ e := by
  rw [← Nat.card_eq_fintype_card]
  have hne : IsLocalRing.maximalIdeal 𝒪[k] ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have hq := cardQuot_pow_of_prime (P := IsLocalRing.maximalIdeal 𝒪[k]) hne (i := e)
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at hq
  exact hq

theorem val_rep_sub {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (y : Res k c) (a : 𝒪[k])
    (h : y = Ideal.Quotient.mk _ a) : valuation k (rep y - a) ≤ valuation k (ϖ : k) ^ c :=
  (mk_eq_mk_iff hϖ c (Quotient.out y) a).1 (by rw [Ideal.Quotient.mk_out, h])

open Classical in

theorem exists_int_gS {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {ψl : k → ℂ}
    (hadd : ∀ x y, ψl (x + y) = ψl x * ψl y) (hO : ∀ x : k, valuation k x ≤ 1 → ψl x = 1)
    (hcond : ∀ x : k, (∀ y : k, valuation k y ≤ 1 → ψl (x * y) = 1) → valuation k x ≤ 1)
    {ϖ : kˣ} (hϖ : IsUnif ϖ) {c : ℕ} (hc1 : 1 ≤ c) {ν : kˣ →* ℂˣ} (hc : CondLE ϖ c ν)
    (hmin : ∃ u ∈ unitCong (ϖ ^ (c - 1)), ν u ≠ 1) (hun : ∀ x, ‖(ν x : ℂ)‖ = 1)
    (hr : ∀ x : kˣ, valuation k (x : k) = 1 → (ν x : ℂ) ∈ Set.range σ)
    (hζ : ∀ ζ : ℂ, ζ ^ (resCard k ^ c) = 1 → ζ ∈ Set.range σ) :
    ∃ g g' : NumberField.RingOfIntegers K, σ g = gS ψl ν hϖ hc1 1 ∧
      g * g' = (resCard k : NumberField.RingOfIntegers K) ^ c := by
  have hdiv : ∀ a b : k, valuation k (a - b) ≤ valuation k (ϖ : k) ^ c →
      ψl (a / (ϖ : k) ^ c) = ψl (b / (ϖ : k) ^ c) := fun a b h => by
    apply psi_congr hadd hO
    rw [← sub_div, map_div₀, map_pow]
    exact div_le_one_of_le₀ h zero_le'
  have hmul : ∀ x y : Res k c, valuation k (rep (x * y) - rep x * rep y) ≤ valuation k (ϖ : k) ^ c := fun x y =>
    val_rep_sub hϖ (x * y) (Quotient.out x * Quotient.out y)
      (by rw [map_mul, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out])
  let Ψ : AddChar (Res k c) ℂ :=
    { toFun := fun y => ψl (rep y / (ϖ : k) ^ c)
      map_zero_eq_one' := by
        rw [hdiv _ 0 (val_rep_sub hϖ (0 : Res k c) 0 (map_zero _).symm), zero_div]
        exact hO 0 (by simp)
      map_add_eq_mul' := fun x y => by
        rw [← hadd, ← add_div]
        exact hdiv _ _ (val_rep_sub hϖ (x + y) (Quotient.out x + Quotient.out y)
          (by rw [map_add, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out])) }
  let χ : (Res k c)ˣ →* ℂ :=
    { toFun := fun u => ν (uRep hϖ hc1 u)
      map_one' := by
        rw [nu_congr hϖ hc1 hc (b := 1) (by simp) (val_rep_sub hϖ (1 : Res k c) 1 (map_one _).symm)]
        simp
      map_mul' := fun u w => by
        rw [nu_congr hϖ hc1 hc (b := uRep hϖ hc1 u * uRep hϖ hc1 w)
          (by simp [val_rep_unit hϖ hc1]) (hmul u w)]
        simp }
  have hΨ : ∀ d : Res k c, (∀ x, Ψ (d * x) = 1) → d = 0 := fun d hd => by
    have h3 := hcond (rep d / (ϖ : k) ^ c) fun a ha => by
      rw [← hd (Ideal.Quotient.mk _ ⟨a, ha⟩), div_mul_eq_mul_div]
      exact (hdiv _ _ (val_rep_sub hϖ _ (Quotient.out d * ⟨a, ha⟩) (by rw [map_mul, Ideal.Quotient.mk_out]))).symm
    rw [← Ideal.Quotient.mk_out d, ← map_zero (Ideal.Quotient.mk _)]
    apply (mk_eq_mk_iff hϖ c _ _).2
    have e2 : rep d = rep d / (ϖ : k) ^ c * (ϖ : k) ^ c := by field_simp
    change valuation k (rep d - 0) ≤ _
    rw [sub_zero, e2, map_mul, map_pow]
    exact mul_le_of_le_one_left' h3
  haveI : Nontrivial (Res k c) := Ideal.Quotient.nontrivial_iff.2 fun h =>
    (IsLocalRing.maximalIdeal.isMaximal 𝒪[k]).ne_top (top_le_iff.1 (h.ge.trans (Ideal.pow_le_self (by omega))))
  haveI : IsLocalRing (Res k c) := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  obtain ⟨u, ⟨hu1, hu2⟩, hν⟩ := hmin
  have hu' : IsUnit (⟨u, hu1.le⟩ : 𝒪[k]) :=
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 hu1
  set ub : (Res k c)ˣ := (hu'.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c))).unit with hub_def
  have hub : (ub : Res k c) = Ideal.Quotient.mk _ ⟨u, hu1.le⟩ := rfl
  have ht₀ : ∀ x ∈ IsLocalRing.maximalIdeal (Res k c), ((ub : Res k c) - 1) * x = 0 := fun x hx => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha : valuation k (a : k) < 1 := lt_of_le_of_ne a.2 fun h => hx
      (((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 h).map _)
    have hx' : valuation k (a : k) ≤ valuation k (ϖ : k) := by rw [hϖ]; exact le_uniformizer_iff.2 ha
    have hu2' : valuation k ((u : k) - 1) ≤ valuation k (ϖ : k) ^ (c - 1) := by
      simpa [Units.val_pow_eq_pow_val] using hu2
    rw [hub, ← map_one (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c)), ← map_sub, ← map_mul,
      ← map_zero (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c))]
    apply (mk_eq_mk_iff hϖ c _ _).2
    change valuation k (((u : k) - 1) * a - 0) ≤ _
    rw [sub_zero, map_mul]
    calc valuation k ((u : k) - 1) * valuation k (a : k) ≤ valuation k (ϖ : k) ^ (c - 1) * valuation k (ϖ : k) :=
          mul_le_mul' hu2' hx'
      _ = valuation k (ϖ : k) ^ c := by rw [← pow_succ]; congr 1; omega
  have hχt₀ : χ ub ≠ 1 := by
    change ((ν (uRep hϖ hc1 ub) : ℂˣ) : ℂ) ≠ 1
    rw [nu_congr hϖ hc1 hc (b := u) hu1 (val_rep_sub hϖ _ _ hub)]
    exact fun h => hν (Units.ext h)
  obtain ⟨g, g', h1, h2⟩ := exists_int_gauss σ (IsLocalRing.maximalIdeal (Res k c))
    (fun x => by simp [IsLocalRing.mem_maximalIdeal]) Ψ hΨ χ (fun u => hun _) ub ht₀ hχt₀
    (fun u => hr _ (val_rep_unit hϖ hc1 u)) (by rwa [card_res])
  refine ⟨g, g', ?_, by rw [h2, card_res, Nat.cast_pow]⟩
  rw [h1]
  unfold gS
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [one_mul, Units.val_inv_eq_inv_val]
  rfl

end Local

end GlobalTheory.GaussDiv

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (gauss unifAt PsiUnr)

open ValuativeRel GlobalTheory.SplitFlip GlobalTheory.GaussNonvanish GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in

theorem GlobalTheory.GaussDiv.gauss_dvd_pow : ∀ {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)
    (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (ν : (Fv F v)ˣ →* ℂˣ), PsiUnr ψ v →
    Continuous (fun x : (Fv F v)ˣ => (ν x : ℂ)) → (∀ x, ‖(ν x : ℂ)‖ = 1) → 1 ≤ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν →
    (∀ x : (Fv F v)ˣ, (x : Fv F v) ∈ v.adicCompletionIntegers F → ((x⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F →
      (ν x : ℂ) ∈ Set.range σ) →
    (∀ ζ : ℂ, ζ ^ (Ideal.absNorm v.asIdeal ^ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν) = 1 → ζ ∈ Set.range σ) →
    ∃ g g' : 𝓞 K, σ g = gauss ψ ν ∧ g * g' = ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ^ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν := by
  intro F _ _ K _ _ σ ψ v ν hψ hcont hun hc1 hr hζ
  have hϖ : IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  have hadd : ∀ x y, psiLoc ψ v (x + y) = psiLoc ψ v x * psiLoc ψ v y := fun x y => by
    simp only [psiLoc, map_add]
    exact AddChar.map_add_eq_mul ψ _ _
  have hO : ∀ x : Fv F v, valuation (Fv F v) x ≤ 1 → psiLoc ψ v x = 1 := fun x hx => by
    have := ((hψ 1).2 ((val_le_one_iff v 1).1 (by simp))) x ((val_le_one_iff v x).1 hx)
    rwa [one_mul] at this
  have hcond : ∀ x : Fv F v, (∀ y : Fv F v, valuation (Fv F v) y ≤ 1 → psiLoc ψ v (x * y) = 1) →
      valuation (Fv F v) x ≤ 1 := fun x h =>
    (val_le_one_iff v x).2 ((hψ x).1 fun y hy => h y ((val_le_one_iff v y).2 hy))
  have hne : {c | CondLE (unifAt v) c ν}.Nonempty := exists_condLE hϖ ν hcont
  have hmem : CondLE (unifAt v) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν) ν := Nat.sInf_mem hne
  have hmin : ∃ u ∈ unitCong (unifAt v ^ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν - 1)), ν u ≠ 1 := by
    have hlt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν - 1 < sInf {c | CondLE (unifAt v) c ν} := by
      show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν - 1 < GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν
      omega
    have h : ¬ CondLE (unifAt v) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν - 1) ν := Nat.notMem_of_lt_sInf hlt
    simpa [CondLE] using h
  have hq : GlobalTheory.SplitWeil.resCard (Fv F v) = Ideal.absNorm v.asIdeal := GlobalTheory.LFun.SatBoundGL.resCard_completion v
  obtain ⟨g, g', h1, h2⟩ := GlobalTheory.GaussDiv.exists_int_gS σ hadd hO hcond hϖ hc1 hmem hmin hun
    (fun x hx => hr x ((val_le_one_iff v _).1 hx.le)
      ((val_le_one_iff v _).1 (by rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one])))
    (by rwa [hq])
  refine ⟨g, g', ?_, by rw [h2, hq]⟩
  rw [h1]
  unfold gauss gS
  refine Finset.sum_congr rfl fun y _ => ?_
  have hr := rep_ne_zero hϖ hc1 y
  unfold rep at hr
  rw [dif_neg hr, one_mul]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeIndicatorFourier
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylFour.IndOSelf

open ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F : Type} [Field F] [NumberField F]

local instance borelFvAt (v : Pl F) : BorelSpace (Fv F v) := ⟨rfl⟩

theorem mem_int_iff {v : Pl F} (x : Fv F v) : x ∈ 𝒪[Fv F v] ↔ x ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  haveI : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (Fv F v))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

theorem exists_nat_mul_mem (v : Pl F) (x : Fv F v) :
    ∃ N : ℕ, N ≠ 0 ∧ (N : Fv F v) * x ∈ v.adicCompletionIntegers F := by
  obtain ⟨b, hb, hbx⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb0
  · have h1 := congrArg (algebraMap (𝓞 F) (v.adicCompletion F)) hc
    rw [map_mul, map_natCast] at h1
    rw [← h1, mul_assoc, mul_comm _ x]
    exact mul_mem (HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v c) hbx

theorem norm_psiAt (ψ : AddChar (AF F) ℂ) (v : Pl F) (hψ : PsiUnr ψ v) (x : Fv F v) :
    ‖GlobalTheory.LatVac.psiAt ψ v x‖ = 1 := by
  obtain ⟨N, hN, hx⟩ := exists_nat_mul_mem v x
  have h1 : GlobalTheory.LatVac.psiAt ψ v ((N : Fv F v) * x) = 1 := by
    have := ((hψ 1).2 (one_mem _)) _ hx
    rwa [one_mul] at this
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow] at h1
  exact Complex.norm_eq_one_of_pow_eq_one h1 hN

def psiC (ψ : AddChar (AF F) ℂ) (v : Pl F) (hψ : PsiUnr ψ v) : AddChar (Fv F v) Circle where
  toFun x := ⟨GlobalTheory.LatVac.psiAt ψ v x, mem_sphere_zero_iff_norm.2 (norm_psiAt ψ v hψ x)⟩
  map_zero_eq_one' := Subtype.ext (AddChar.map_zero_eq_one _)
  map_add_eq_mul' x y := Subtype.ext (AddChar.map_add_eq_mul _ x y)

theorem coe_psiC (ψ : AddChar (AF F) ℂ) (v : Pl F) (hψ : PsiUnr ψ v) (x : Fv F v) :
    ((psiC ψ v hψ x : Circle) : ℂ) = GlobalTheory.LatVac.psiAt ψ v x := rfl

theorem hasConductor_psiC (ψ : AddChar (AF F) ℂ) (v : Pl F) (hψ : PsiUnr ψ v) :
    GlobalTheory.SplitWeil.HasConductor (psiC ψ v hψ) 1 := by
  intro x
  have e1 : ∀ y, psiC ψ v hψ y = 1 ↔ GlobalTheory.LatVac.psiAt ψ v y = 1 := fun y =>
    ⟨fun h => by rw [← coe_psiC ψ v hψ, h]; rfl, fun h => Circle.ext (by rw [coe_psiC ψ v hψ, h]; rfl)⟩
  rw [Units.val_one, map_one, ← Valuation.mem_integer_iff, mem_int_iff, ← hψ x]
  simp only [e1]
  constructor
  · intro h y hy
    apply h
    rw [map_mul]
    have : valuation (Fv F v) y ≤ 1 := (Valuation.mem_integer_iff _ _).1 ((mem_int_iff y).2 hy)
    exact mul_le_of_le_one_right' this
  · intro h y hy
    by_cases hx : x = 0
    · subst hx
      rw [map_zero, le_zero_iff, map_eq_zero] at hy
      subst hy
      exact AddChar.map_zero_eq_one _
    · have hyx : y / x ∈ v.adicCompletionIntegers F := by
        rw [← mem_int_iff, Valuation.mem_integer_iff, map_div₀,
          div_le_one₀ (by rw [zero_lt_iff, Ne, map_eq_zero]; exact hx)]
        exact hy
      have := h _ hyx
      rwa [mul_div_cancel₀ _ hx] at this

theorem indO_mem_SB (v : Pl F) (κ : Type) [Fintype κ] : GlobalTheory.SympChange.indO (κ := κ) v ∈ SB (κ → Fv F v) := by
  set S : Set (κ → Fv F v) := {x | ∀ i, x i ∈ v.adicCompletionIntegers F} with hSdef
  have hS : S = Set.univ.pi fun _ => ((ValuativeRel.valuation (Fv F v)).integer : Set (Fv F v)) := by
    ext x; simp [S, mem_int_iff]
  have hc : IsCompact S := hS ▸ isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_int _
  have ho : IsOpen S := hS ▸ isOpen_set_pi Set.finite_univ fun _ _ => GlobalTheory.SplitWeil.isOpen_int _
  have hcl : IsClosed S := hc.isClosed
  have hind : GlobalTheory.SympChange.indO (κ := κ) v = S.indicator 1 := rfl
  rw [hind]
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_,
    HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  by_cases hx : x ∈ S
  · filter_upwards [ho.mem_nhds hx] with y hy
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl
  · filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem exists_selfDual (ψ : AddChar (AF F) ℂ) (v : Pl F) (hψ : PsiUnr ψ v) :
    ∃ ν, IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) ν := by
  obtain ⟨ν, hν⟩ := GlobalTheory.SplitWeil.exists_isUnitVol (Fv F v)
  have h := GlobalTheory.SplitWeil.isSelfDual_of_isUnitVol ν (hasConductor_psiC ψ v hψ) hν
  exact ⟨ν, h.1, fun f hf => h.2 f hf⟩

theorem isUnitVol_measV (ψ : AddChar (AF F) ℂ) (v : Pl F) (hψ : PsiUnr ψ v) :
    GlobalTheory.SplitWeil.IsUnitVol (measV ψ v) := by
  have hex := exists_selfDual ψ v hψ
  have hm : measV ψ v = hex.choose := by simp only [measV, dif_pos hex]
  have hs := hex.choose_spec
  rw [hm]
  exact (GlobalTheory.SplitWeil.isUnitVol_iff_isSelfDual (hasConductor_psiC ψ v hψ) _).2 ⟨hs.1, fun f hf => hs.2 f hf⟩

theorem fourV_indO (ψ : AddChar (AF F) ℂ) (v : Pl F) (hψ : PsiUnr ψ v) (κ : Type) [Fintype κ] :
    fourV ψ v (GlobalTheory.SympChange.indO (κ := κ) v) = GlobalTheory.SympChange.indO v := by
  classical
  have hU := isUnitVol_measV ψ v hψ
  haveI := hU.1
  haveI := GlobalTheory.SplitWeil.secondCountable (Fv F v)
  have hball : GlobalTheory.SplitWeil.cball (1 : (Fv F v)ˣ) = ((ValuativeRel.valuation (Fv F v)).integer : Set (Fv F v)) := by
    ext x; simp [GlobalTheory.SplitWeil.cball, Valuation.mem_integer_iff]
  have hbox : GlobalTheory.SplitWeil.FourierPi.box κ (1 : (Fv F v)ˣ) = {x | ∀ i, x i ∈ v.adicCompletionIntegers F} := by
    ext x; simp [GlobalTheory.SplitWeil.FourierPi.box, hball, ← mem_int_iff]
  have hvol : (Measure.pi fun _ : κ => measV ψ v).real (GlobalTheory.SplitWeil.FourierPi.box κ 1) = 1 := by
    simp [Measure.real, GlobalTheory.SplitWeil.FourierPi.box, Measure.pi_pi, hball, hU.2]
  funext y
  have h := GlobalTheory.SplitWeil.FourierPi.fourier_indicator_pi (Measure.pi fun _ : κ => measV ψ v)
    (hasConductor_psiC ψ v hψ) 1 y
  rw [mul_inv_cancel, hvol, hbox] at h
  exact h

theorem indO_self_fourier : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (v : Pl F)
    (κ : Type) [Fintype κ], GlobalTheory.SympChange.indO (κ := κ) v ∈ SB (κ → Fv F v) ∧
    (PsiUnr ψ v → fourV ψ v (GlobalTheory.SympChange.indO (κ := κ) v) = GlobalTheory.SympChange.indO v) := by
  intro F _ _ ψ _ v κ _
  exact ⟨indO_mem_SB v κ, fun h => fourV_indO ψ v h κ⟩

end GlobalTheory.WeylFour.IndOSelf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateShellLeDivModulus
section
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

namespace GlobalTheory.ResLine

theorem modulus_mul_measure_shell_le : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M), SemiLat N M Λ ν π DN DM → ∀ (μ : Measure G) (D : Set G), μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → ∀ C : Set G, IsCompact C → ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ (b : G) (κ : ℝ≥0∞), (∀ m ∈ M, b * m = m * b) → (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (b * u * b⁻¹) ∂ν = κ * ∫⁻ u : N, f u ∂ν) → ∀ S : Set G, MeasurableSet S → (∀ x ∈ S, ∃ u ∈ N, ∃ m ∈ M, ∃ y ∈ C, b * x = u * m * y) → κ * μ (S ∩ D) ≤ B := by
  intro G _ _ _ _ _ _ _ _ N M Λ _ ν π DN DM hL μ D hμ hD C hC
  obtain ⟨U, c, hU, hμU, hc, hlow⟩ := GlobalTheory.T.semidirectAverage_indicator_lower_bound G N M Λ ν π DN DM hL μ hμ C hC
  have hX : ν DN * π DM * μ U ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hL.finN hL.finM) hμU
  refine ⟨ν DN * π DM * μ U / c, ENNReal.div_ne_top hX hc, ?_⟩
  intro b κ hb hκ S hS hSx
  rw [ENNReal.le_div_iff_mul_le (Or.inl hc) (Or.inr hX)]
  have hφ : Measurable (U.indicator (1 : G → ℝ≥0∞)) := measurable_one.indicator hU.measurableSet
  have hw := GlobalTheory.T.lintegral_two_step_unfolding_semidirect_lattice G N M Λ ν π DN DM hL μ D hμ hD
    (fun x => U.indicator (1 : G → ℝ≥0∞) (b * x)) (hφ.comp (measurable_const_mul b))
  rw [lintegral_mul_left_eq_self (U.indicator (1 : G → ℝ≥0∞)) b,
    lintegral_indicator_one hU.measurableSet] at hw
  rw [← hw]
  have h1 : κ * μ (S ∩ D) * c = ∫⁻ x in D, S.indicator (fun _ => κ * c) x ∂μ := by
    rw [lintegral_indicator_const hS, Measure.restrict_apply hS]; ring
  rw [h1]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx]
    obtain ⟨u₀, hu₀, m₀, hm₀, y, hy, hxy⟩ := hSx x hx
    have h2 := hlow u₀ hu₀ m₀ hm₀ y hy
    rw [← hxy] at h2
    refine le_trans (mul_le_mul_right h2 κ) (le_trans (lintegral_const_mul_le _ _) (le_of_eq ?_))
    refine lintegral_congr fun m => ?_
    have h3 := hκ (fun g => U.indicator (1 : G → ℝ≥0∞) (g * m * (b * x)))
      (hφ.comp ((measurable_id.mul_const _).mul_const _))
    rw [← h3]
    refine lintegral_congr fun u => ?_
    congr 1
    have h4 := hb m m.2
    calc b * (u : G) * b⁻¹ * m * (b * x) = b * u * b⁻¹ * (m * b) * x := by group
      _ = b * u * b⁻¹ * (b * m) * x := by rw [h4]
      _ = b * (u * m * x) := by group
  · rw [Set.indicator_of_notMem hx]; exact zero_le

end GlobalTheory.ResLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedModelThetaFunctionBoundedStatement
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orientedModelThetaFunction_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
      ∀ f : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ ψ f → ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  first | exact @GlobalTheory.TowerFD.thetaFunOF_bounded | exact GlobalTheory.TowerFD.thetaFunOF_bounded | (intros; apply GlobalTheory.TowerFD.thetaFunOF_bounded <;> assumption)
end

