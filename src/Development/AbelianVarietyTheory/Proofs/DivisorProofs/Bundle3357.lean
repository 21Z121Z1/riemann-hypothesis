import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3343
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2338
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2343
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3174
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3301
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3300
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3251
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0290
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1810
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3329
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3350
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0880
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3128
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3349
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0613
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0620
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3351
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2870
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelMapFlatExtension
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.BdryGeo

theorem unit_of_vV (T : CDVR) {x : T.Fr} (hx : x ≠ 0) (h0 : vV T.V x = 0) :
    ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = x := by
  have hne : valV T.V x ≠ 0 := valV_ne_zero hx
  have h1 : valV T.V x = 1 := by
    have h2 : WithZero.log (valV T.V x) = 0 := by simpa [vV] using h0
    rw [← WithZero.exp_log hne, h2, WithZero.exp_zero]
  have hunit : ∀ z : T.V, (IsDiscreteValuationRing.maximalIdeal T.V).valuation T.Fr (algebraMap T.V T.Fr z) = 1 →
      IsUnit z := fun z hz => by
    have hzn := (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem _).1 hz
    by_contra hn
    exact hzn ((IsLocalRing.mem_maximalIdeal z).2 hn)
  rcases ValuationRing.isInteger_or_isInteger T.V x with ⟨z, hz⟩ | ⟨z, hz⟩
  · obtain ⟨u, rfl⟩ := hunit z (by rw [hz]; exact h1)
    exact ⟨u, hz⟩
  · obtain ⟨u, rfl⟩ := hunit z (by
      rw [hz, map_inv₀]
      change (valV T.V x)⁻¹ = 1
      rw [h1, inv_one])
    refine ⟨u⁻¹, ?_⟩
    rw [map_units_inv, hz, inv_inv]

theorem descend (T₀ T : CDVR) (i : T₀.V →+* T.V) (iF : T₀.Fr →+* T.Fr)
    (hiF : ∀ a, algebraMap T.V T.Fr (i a) = iF (algebraMap T₀.V T₀.Fr a)) (hi : Function.Injective i)
    (hil : IsLocalHom i) (v : T₀.Fr) (u : T.Vˣ) (hv : iF v = algebraMap T.V T.Fr (u : T.V)) :
    ∃ w : T₀.Vˣ, algebraMap T₀.V T₀.Fr w = v := by
  have hinjT : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
  rcases ValuationRing.isInteger_or_isInteger T₀.V v with ⟨z, hz⟩ | ⟨z, hz⟩
  · have h1 : i z = u := hinjT (by rw [hiF, hz, hv])
    have : IsUnit z := (isUnit_map_iff i z).1 (h1 ▸ u.isUnit)
    obtain ⟨w, rfl⟩ := this
    exact ⟨w, hz⟩
  · have h1 : i z = ((u⁻¹ : T.Vˣ) : T.V) := hinjT (by rw [hiF, hz, map_inv₀, hv, map_units_inv])
    have : IsUnit z := (isUnit_map_iff i z).1 (h1 ▸ (u⁻¹).isUnit)
    obtain ⟨w, rfl⟩ := this
    refine ⟨w⁻¹, ?_⟩
    rw [map_units_inv, hz, inv_inv]

theorem secVal_isUnit : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F)
    (r₀ : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀) (x : ℝ), Laws U x →
    ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ)
      (Xw : Y.X.Opens), p.Prime → IsCover Y r hle Z la p Xw →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A),
      IsOpenImmersion ξ → ξ ≫ Y.s = spMap β → IsUnit (p : A) → ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Xw →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
    ∀ 𝔭 : PrimeSpectrum A, 𝔭.asIdeal.height = 1 → ξ 𝔭 ∉ Set.range Y.j →
    ∃ (T : CDVR) (iT : Localization.AtPrime 𝔭.asIdeal →+* T.V), Function.Injective iT ∧ IsLocalHom iT ∧
      ∀ v : T.Fr, (∀ (k : Type) [Field k] (φ : T.Fr →+* k),
        SecValAt Y r ν τ.1 s.sig ξ e U₁ U₂ k (φ.comp ((algebraMap T.V T.Fr).comp (iT.comp (algebraMap A _)))) (φ v)) →
        ∃ w : T.Vˣ, algebraMap T.V T.Fr w = v := by
  intro hP1 hP2 hP3 E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw hp hcov A _ _ _ _ ξ β hξo hξβ
    hpA hgen g e U₁ h₁ U₂ h₂ htan heig hd1 hd2 𝔭 h𝔭 _
  obtain ⟨hover, -, hpW, hpc, hXw, -, hZ, -, -⟩ := hcov
  have hβu := GlobalTheory.T.base_ring_units_invert_p E H l' c' W p hp hpW A β hpA
  haveI : CharZero A := by
    refine ⟨fun m n hmn => ?_⟩
    have hinjβ : Function.Injective β := by
      rw [injective_iff_map_eq_zero]
      intro a ha
      by_contra h0
      exact (hβu a h0).ne_zero ha
    have h := hinjβ (show β m = β n by rw [map_natCast, map_natCast]; exact hmn)
    exact_mod_cast congrArg (fun t : c'.V W => ((t : c'.F) : ℂ)) h
  obtain ⟨T₀, iT, hinj, hloc⟩ := GlobalTheory.T.exists_dvr_over_height_one A 𝔭 h𝔭
  let α₀ : A →+* T₀.V := iT.comp (algebraMap A (Localization.AtPrime 𝔭.asIdeal))
  have hα₀ : Function.Injective α₀ :=
    hinj.comp (IsLocalization.injective _ 𝔭.asIdeal.primeCompl_le_nonZeroDivisors)
  have hψ : Function.Injective ((algebraMap T₀.V T₀.Fr).comp α₀) :=
    (IsFractionRing.injective T₀.V T₀.Fr).comp hα₀
  obtain ⟨yy₀, hyy₀⟩ := GlobalTheory.T.generic_fibre_point_field E H Dw l' Xo' c' W Y p hp hpW hpc A ξ (hXw hgen) T₀.Fr _ hψ
  obtain ⟨T, i, iF, hiF, hi, hil, io, y₀, hio, hpt⟩ :=
    GlobalTheory.T.integral_model_domain_over_inclusion E H Dw l l' Xo Xo' c c' W Y r ν hle hover A ξ β hξβ hβu T₀ α₀ hα₀ yy₀ hyy₀
  refine ⟨T₀, iT, hinj, hloc, fun v hv => ?_⟩
  let α : A →+* T.V := i.comp α₀
  have hφeq : iF.comp ((algebraMap T₀.V T₀.Fr).comp (iT.comp (algebraMap A _))) = (algebraMap T.V T.Fr).comp α :=
    RingHom.ext fun a => (hiF _).symm
  let yy : Sp T.Fr ⟶ Xo'.XF c' := spMap iF ≫ yy₀
  have hyy : yy ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp α) ≫ ξ := by
    rw [← hφeq, Category.assoc, hyy₀, sp_sp]
  have hpt' : (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1 = yy ≫ r) := by
    rw [hpt, Category.assoc]
  obtain ⟨w₁, w₂, g₁, g₂, hc1, hc2, ⟨hc3, hc4⟩, ⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩⟩ :=
    GlobalTheory.T.integral_model_conjugate_embedding E H Dw l l' Xo Xo' c c' W Y r ν hle hover τ.1 A ξ β hξβ g e U₁ h₁ U₂ h₂ htan heig hd1 hd2 T α io y₀ yy
      hyy hpt'
  letI := io.toAlgebra
  have hv' := hv T.Fr iF
  rw [hφeq] at hv'
  have key := hv' io.toAlgebra yy hyy y₀.1 y₀.2.1 hpt' w₁ w₂ g₁ g₂ hc1 hc2 hc3 hc4
  have hLies : GlobalTheory.AllWt.LiesOn Z y₀.1 := by
    intro s'
    rw [hpt']
    apply hZ
    have hs' : s' = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.Fr) := Subsingleton.elim _ _
    have e1 : (yy ≫ Y.j) s' ∈ Xw := by
      rw [hyy, hs', bot_map (φ := (algebraMap T.V T.Fr).comp α) ((IsFractionRing.injective T.V T.Fr).comp (hi.comp hα₀))]
      exact hgen
    exact e1
  have hn := GlobalTheory.T.archimedean_section_integral_frame hP1 hP2 hP3 E H Dw l Xo c r₀ U x hL Z τ s T io y₀ hio hLies
  have hev0 : evI y₀ s.sig ≠ 0 := by
    intro h0
    rw [h0, nval_zero] at hn
    exact EReal.top_ne_zero hn
  have hvv : vV T.V (evI y₀ s.sig) = 0 := by
    rw [nval_of_ne hev0] at hn
    have : ((vV T.V (evI y₀ s.sig) : ℝ) / ((1 : ℕ) : ℝ) : ℝ) = 0 := by exact_mod_cast hn
    simpa using this
  obtain ⟨u₃, hu₃⟩ := unit_of_vV T hev0 hvv
  have hkey : iF v = algebraMap T.V T.Fr ((u₂ * u₃ * u₁⁻¹ : T.Vˣ) : T.V) := by
    have hne : algebraMap T.V T.Fr (u₁ : T.V) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 u₁.ne_zero
    rw [Units.val_mul, Units.val_mul, map_mul, map_mul, hu₂, hu₃, map_units_inv, hu₁]
    have : iF v * g₁.det = g₂.det * evI y₀ s.sig := key
    rw [← hu₁] at this ⊢
    field_simp
    linear_combination this
  exact descend T₀ T i iF hiF hi hil v _ hkey

end GlobalTheory.FlatModel.BdryGeo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawOfIsLawOf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.Chart

variable {p : ℕ} {k : Type} [CommRing k] {d : ℕ} {G : PDivGroup p k}

def firstFactor (A : Type) [CommRing A] [Bialgebra k A] : A ⊗[k] A →ₐ[k] A :=
  Algebra.TensorProduct.lift (AlgHom.id k A) ((Algebra.ofId k A).comp (Bialgebra.counitAlgHom k A))
    (fun _ _ => Commute.all _ _)

theorem firstFactor_comul (A : Type) [CommRing A] [Bialgebra k A] (a : A) :
    firstFactor A (Coalgebra.comul (R := k) a) = a := by
  have h : (firstFactor A).toLinearMap =
      (TensorProduct.rid k A).toLinearMap ∘ₗ (Coalgebra.counit (R := k) (A := A)).lTensor A := by
    apply TensorProduct.ext'
    intro a b
    simp [firstFactor, Algebra.smul_def, mul_comm]
  have := LinearMap.congr_fun h (Coalgebra.comul (R := k) a)
  simp only [AlgHom.toLinearMap_apply] at this
  rw [this, LinearMap.comp_apply, Coalgebra.lTensor_counit_comul]
  simp

end GlobalTheory.Katz.Chart

namespace GlobalTheory.Katz.Chart

variable {p : ℕ} {k : Type} [CommRing k] {d : ℕ} {G : PDivGroup p k}

theorem firstFactor_ev₂ (c : Chart G d) (n : ℕ) (f : MvPowerSeries (Fin d ⊕ Fin d) k) :
    firstFactor (G.A n) (c.ev₂ n f) =
      c.ev n (at2 f (fun i => (X i : MvPowerSeries (Fin d) k)) (fun _ => 0)) := by
  have hy : ∀ j : Fin d ⊕ Fin d, IsNilpotent ((Sum.elim (c.x n) (fun _ => (0 : G.A n))) j) := by
    intro j; cases j with
    | inl i => exact c.nil n i
    | inr i => exact IsNilpotent.zero
  have h2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n ⊗[k] G.A n)).2 (G.A n) (firstFactor (G.A n))
    (c.x₂ n) (c.nil₂ n) _ hy (by
      intro j; cases j with
      | inl i => simp [Chart.x₂, firstFactor]
      | inr i => simp [Chart.x₂, firstFactor, c.aug]) f
  have h1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin d ⊕ Fin d) (G.A n)).1 (Fin d) (c.ev n)
    (fun t => by rw [Chart.ev, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]; exact c.nil n t)
    (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) k)) (fun _ => 0))
    (by intro j; cases j with
      | inl i => exact constantCoeff_X i
      | inr i => exact map_zero _)
    _ hy (by
      intro j; cases j with
      | inl i => simp [Chart.ev, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate]
      | inr i => simp) f
  exact h2.trans h1.symm

end GlobalTheory.Katz.Chart

namespace GlobalTheory

theorem Katz.Chart.isLaw_of_isLawOf : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k)
    (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → IsLaw μ := by
  intro p k _ d G c μ hμ
  have hcomp : ∀ (n : ℕ) (i : Fin d), pullbackTwo (G.res n) (Coalgebra.comul (R := k) (c.x (n + 1) i))
      = Coalgebra.comul (R := k) (c.x n i) := fun n i => by
    rw [pullTwo_comul, c.res]
  refine ⟨((GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).2 μ hμ).1, ?_, ?_, ?_⟩
  · funext i
    obtain ⟨f, -, huniq⟩ := (GlobalTheory.T.functions_eq_series_in_chart p k d G c).2.2 (fun n => c.x n i) (fun n => c.res n i)
    have hX : ∀ n, c.ev n (X i) = c.x n i := fun n => GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate _ _ _ _ _ i
    have hA : ∀ n, c.ev n (op μ (fun i => (X i : MvPowerSeries (Fin d) k)) (fun _ => 0) i) =
        c.x n i := fun n => by
      rw [op, ← firstFactor_ev₂, hμ, firstFactor_comul]
    exact (huniq _ hA).trans (huniq _ hX).symm
  · intro i
    obtain ⟨s, -, huniq⟩ := (GlobalTheory.T.chart_square_coordinates_present_levels p k d G c).2 (fun n => Coalgebra.comul (R := k) (c.x n i))
      (fun n => hcomp n i)
    have h1 : ∀ n, c.ev₂ n (Katz.swap (μ i)) = Coalgebra.comul (R := k) (c.x n i) := fun n => by
      rw [((GlobalTheory.T.connectedChart_evalSquare_variables_swap_constant p k d G c) n).2.2.1, hμ, Coalgebra.comm_comul]
    exact (huniq _ h1).trans (huniq _ (fun n => hμ n i)).symm
  · funext i
    have hinj := (GlobalTheory.T.eq_zero_of_eval_cube_levels p k d G c).2
      (op μ (op μ x1 x2) x3 i - op μ x1 (op μ x2 x3) i) (fun n h => by
        rw [map_sub, ((GlobalTheory.T.connectedPDivGroupChart_coboundaryTwo_coord p k d G c μ hμ n h).2 i), sub_self])
    exact sub_eq_zero.1 hinj

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFormalGroupCocycleIffMemCocycles
section
set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem isCoc_iff_mem_cocycles : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k)
    (c : Chart G d), ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ →
    ∀ s, IsCoc μ s ↔ (fun n => c.ev₂ n s) ∈ G.cocycles := by
  intro p k _ d G c μ hμ s
  have hcomp : ∀ n, pullbackTwo (G.res n) (c.ev₂ (n + 1) s) = c.ev₂ n s :=
    fun n => (GlobalTheory.T.functions_eq_series_in_chart p k d G c).2.1 n s
  have hnil := (GlobalTheory.T.eq_zero_of_eval_cube_levels p k d G c).1
  have hinj := (GlobalTheory.T.eq_zero_of_eval_cube_levels p k d G c).2
  have hcob : ∀ n, evA k _ (hnil n) (cob2 μ s) = cobTwo k (G.A n) (c.ev₂ n s) :=
    fun n => (GlobalTheory.T.connectedPDivGroupChart_coboundaryTwo_coord p k d G c μ hμ n (hnil n)).1 s
  have hswap : ∀ n, c.ev₂ n (Katz.swap s) = TensorProduct.comm k _ _ (c.ev₂ n s) :=
    fun n => (GlobalTheory.T.connectedChart_evalSquare_variables_swap_constant p k d G c n).2.2.1 s
  constructor
  · rintro ⟨h2, hs⟩ n
    refine ⟨mem_symCocycles.2 ⟨?_, ?_⟩, hcomp n⟩
    · rw [← hcob n, h2, map_zero]
    · rw [← hswap n, hs]
  · intro h
    refine ⟨?_, ?_⟩
    · refine hinj _ fun n hn => ?_
      have e := hcob n
      rw [(mem_symCocycles.1 (h n).1).1] at e
      exact e
    · obtain ⟨t, -, ht⟩ := (GlobalTheory.T.chart_square_coordinates_present_levels p k d G c).2 (fun n => c.ev₂ n s) hcomp
      have h1 := ht (Katz.swap s) fun n => by
        rw [hswap n]; exact (mem_symCocycles.1 (h n).1).2
      have h2 := ht s fun n => rfl
      rw [h1, h2]

end GlobalTheory.Katz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftTestPositiveLevelsKappa
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

namespace GlobalTheory.Stage3

theorem stage3 : Hypotheses3 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → R.toRealDat.LUnif → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PLevW F ∧ (R.toCx3 F).PartsW false ∧ R.PHecke F ∧ A3.fam3.TypesSep3 ∧ ∃ tr, R.TrISem F tr ∧ GlobalTheory.Hk3.TrISepWith A3 tr := by
  intro P D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hT hM hU hL hPos hK
  obtain ⟨_hGiven, hGS, hCD, hLI, _hTR, _hUI, _hUIW⟩ := GlobalTheory.T.multiplicity_one_gives_lift_data P R F hT hM
  obtain ⟨hOk, hGU, hGE, _hBlk, hA, hB⟩ := GlobalTheory.T.multiplicity_one_gives_unit_equiv P R F hT hM
  have hJ := (GlobalTheory.Hk3.inertJunk_iff A3).1 hT.junk
  have hLev : R.PLevW F := GlobalTheory.LevW.levW_of_parts P.q2 P.q1 R F hLI hT.ok hT.char hT.ex hJ hGS hCD hM hGE hPos hK hA hL hU
  have hW : (R.toCx3 F).PartsW false :=
    GlobalTheory.SumW.partsW_base P.q2 P.q1 R F hLI hT.ok hT.char hT.ex hJ hGS hCD hM hOk.1 hGE hPos hK hB hU
  obtain ⟨-, hH, hTS, htr⟩ := GlobalTheory.Hk3.HeckeClose.heckeClose P.q1 P.q3 P.q2 R F 1 hT.ok hT.char hT.ex hT.junk hT.ser hT.trSem hU
    hGU hGE hLev hA hB hK hW
  exact ⟨hLev, hW, hH, hTS, htr⟩

end GlobalTheory.Stage3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsAlongOfSmoothInj
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem liftsAlong_of_smooth_inj : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), SmoothOfRelativeDimension g U.hom → Fam A M → Inj A M → ∀ (B : Type) [CommRing B] [IsLocalRing B] (t : B), t ∈ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * Ideal.span {t} = ⊥ → LiftsAlong A M B (Ideal.span {t}) := by
  intro R _ A _ g hA hg U M hU hM hI B _ _ t ht hsq
  have : Smooth U.hom := hU.smooth
  have : LocallyOfFiniteType U.hom := inferInstance
  have hF : FieldChart A M := fieldChart_of_inj _ A hA g hg U M hU hM hI
  have hT : TanLift A M := tanLift_of_fieldChart _ A hA U M hM hI hF
  have hS : SmallLift A M := GlobalTheory.T.liftsAlong_smallExtension_of_dualNumber_lifting _ A hA U M hM hI hT
  exact GlobalTheory.T.liftsAlong_principal_small_extension R A U M hM hS B t ht hsq

end GlobalTheory.DualOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfCompatibleAdicReductionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_of_compatible_adic_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), IsProper X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (A A' : LB X.left), A.IsLB → A'.IsLB → ∀ c : ∀ e, LB.Iso (A.pull (b e)) (A'.pull (b e)), (∀ e, (c e).IsGen) → (∀ e z k k', b e z ∈ A.U k → b e z ∈ A'.U k' → Geo.Tor.gw (c (e + 1)) (β e) z k' (fun _ => k) = Geo.Tor.gw (c e) (𝟙 _) z k' (fun _ => k)) → LBIso A A' := by
  first | exact @GlobalTheory.FormalAlg.lbIso_of_compatible_reductions | exact GlobalTheory.FormalAlg.lbIso_of_compatible_reductions | (intros; apply GlobalTheory.FormalAlg.lbIso_of_compatible_reductions <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityOneRationalRowsSized
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

namespace GlobalTheory.Stage2

theorem stage2 : Hypotheses3 → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ (L : SizeData₂ D), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → Nonempty (ParameterChoice' D L) → TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) ∧ (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) ∧ R.PrincipalLevelBijective F := by
  intro P eps heps
  have hE : GlobalTheory.Published.SiegelEisensteinContinuation := GlobalTheory.Published.siegelEisensteinContinuation_of_doublingMethod P.q9
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.definite_positivity_both_levels_short_list P.q5 P.q3 P.q4 P.q6 P.q2 P.q1 P.q7 P.q8 hE P.q10 P.q12 eps heps
  refine ⟨x₀, ?_⟩
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F L hLe hLx hSz hPar hT hM hRow
  obtain ⟨pV⟩ := hPar
  obtain ⟨_hGiven, _hGS, _hCD, _hLI, hTR, hUI, _hUIW⟩ := GlobalTheory.T.multiplicity_one_gives_lift_data P R F hT hM
  obtain ⟨_hOk, _hGU, hGE, hBlk, _hA, _hB⟩ := GlobalTheory.T.multiplicity_one_gives_unit_equiv P R F hT hM
  have hJ := (GlobalTheory.Hk3.inertJunk_iff A3).1 hT.junk
  have hPos : ∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos :=
    hx₀ (s := 1) R F L pV hLe hLx hSz hT.ok hT.char hT.ex hT.host hT.ccK hT.guard hT.types hTR hGE hBlk hRow
  have hScal := GlobalTheory.T.thetaLift_positiveScalars_basePlace P.q5 P.q3 P.q4 P.q6 P.q2 P.q1 P.q7 P.q8 hE P.q10 P.q11 R F hT.ok hT.char hT.ex hT.host
    hT.params hT.ccK hT.guard hT.types hTR hJ hGE hPos
  exact ⟨hPos, hScal, GlobalTheory.PrimIn.principalLevel_rows_bijective_of_parts R F hT.ok hT.char hUI hRow hBlk⟩

end GlobalTheory.Stage2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordThickeningEndomorphismMapsSectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumford_thickening_endomorphism_maps_sections : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∃ N : ℕ, 1 ≤ N ∧ ∃ S : ∀ k : ℕ, H0 U.LG.L k → H0 U.LG.L (N * k), (∀ (k e : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂)) ∧ (∀ k : ℕ, 3 ≤ k → ∃ s₀ : H0 U.LG.L k, SecCoNonzero U.LG.L ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left s₀ (S k s₀)) := by
  first | exact @GlobalTheory.MumSec.main | exact GlobalTheory.MumSec.main | (intros; apply GlobalTheory.MumSec.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyDescentSeparatedEmbeddingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_descentSeparatedEmbedding : ∀ σ : Setup, σ.Common → Nonempty (Emb σ) := by
  first | exact @GlobalTheory.Desc.nonempty_emb | exact GlobalTheory.Desc.nonempty_emb | (intros; apply GlobalTheory.Desc.nonempty_emb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDescentIdealThetaModelToClopenComponentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_descent_ideal_thetaModel_to_clopen_component : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = W → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) → (∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a}) → ∃ (k : ℕ) (J : Z.IdealSheafData), 1 ≤ k ∧ (∀ x ∈ J.support, x ∈ W ∧ x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → idlAlong J (ξ₁ ≫ X₁.π) = idlAlong J₁ ξ₁ ^ k := by
  first | exact @GlobalTheory.NormDown.normDescent | exact GlobalTheory.NormDown.normDescent | (intros; apply GlobalTheory.NormDown.normDescent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianModelFibreSpecializationChainStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelianModel_fibre_specialization_chain : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ y y' : Y.Z, πY y = z₁ → πY y' = z₁ → Relation.EqvGen (fun a b : Y.Z => πY a = z₁ ∧ πY b = z₁ ∧ a ⤳ b) y y' := by
  first | exact @GlobalTheory.SpecChain.fibre_chain | exact GlobalTheory.SpecChain.fibre_chain | (intros; apply GlobalTheory.SpecChain.fibre_chain <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleMapInjectiveCardCokerOfIsogenyStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateModuleMap_injective_card_coker_of_isogeny : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A B : AbVar K) (f : A ⟶ B), IsIsogeny f → Function.Injective (tmap l A B f) ∧ Nat.card (Tl l B ⧸ LinearMap.range (tmap l A B f)) = l ^ padicValNat l (deg f) := by
  first | (exact @GlobalTheory.AV.AbVar.tmap_injective_card_coker_of_isIsogeny) | (exact GlobalTheory.AV.AbVar.tmap_injective_card_coker_of_isIsogeny) | (intros; apply GlobalTheory.AV.AbVar.tmap_injective_card_coker_of_isIsogeny  <;> assumption)
end

