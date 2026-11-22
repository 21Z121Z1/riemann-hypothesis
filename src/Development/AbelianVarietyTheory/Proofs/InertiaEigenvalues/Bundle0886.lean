import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0881
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0876
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0791
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0882
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0874
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0300
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0790
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NegOneNotMemNatLat

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspRepBumpDataSatakeUnitaryStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspRep_bump_data_satake_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CG E a), π.IsUnitary →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π →
    ∃ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin a → ℂˣ) (π₀ : CuspSub E a) (ω : HChar E),
      (∀ w, Finset.univ.val.map (α w) = sat π w) ∧ CG.mk π₀ = π ∧ ω.IsUnitary ∧ π₀.HasCentChar ω ∧ π₀.IsUnitary ∧
      ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, HasSatGL w.1 (π₀.locRep w.1) (Finset.univ.val.map (α w)) := by
  first | (exact @GlobalTheory.BumpData.bumpData) | (exact GlobalTheory.BumpData.bumpData) | (intros; apply GlobalTheory.BumpData.bumpData  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelNatBumpRankinSelbergCell
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.RSParams

variable {E : Type} [Field E] [NumberField E]

theorem valued_natCast (v : HeightOneSpectrum (𝓞 E)) (N : ℕ) :
    Valued.v (N : v.adicCompletion E) = v.intValuation (N : 𝓞 E) := by
  have h := v.valuedAdicCompletion_eq_valuation (K := E) (N : 𝓞 E)
  rw [v.valuation_of_algebraMap] at h
  simpa using h

theorem exists_nat (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ w ∈ S, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ S) (k : ℕ) :
    ∃ N : ℕ, 0 < N ∧ (∀ v ∈ S, (N : 𝓞 E) ∈ v.asIdeal ^ k) ∧ ∀ v ∉ S, (N : 𝓞 E) ∉ v.asIdeal := by
  classical
  set q : HeightOneSpectrum (𝓞 E) → Ideal ℤ := fun w => Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal with hq
  have hq0 : ∀ w, q w ≠ ⊥ := fun w h => by
    have hm : ((Ideal.absNorm w.asIdeal : ℕ) : ℤ) ∈ q w := by
      rw [hq, Ideal.mem_comap, map_natCast]
      exact Ideal.absNorm_mem _
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at hm
    exact w.ne_bot hm
  set 𝔞 : Ideal ℤ := ∏ w ∈ S, q w with h𝔞
  set n : ℤ := Submodule.IsPrincipal.generator 𝔞 with hn
  have hspan : Ideal.span {n} = 𝔞 := Ideal.span_singleton_generator 𝔞
  have h𝔞0 : 𝔞 ≠ ⊥ := by
    rw [h𝔞, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    exact fun w _ => hq0 w
  have hn0 : n ≠ 0 := fun h => h𝔞0 (by rw [← hspan, h, Ideal.span_singleton_eq_bot])
  set N₀ : ℕ := n.natAbs with hN₀
  have hN₀q : ∀ w ∈ S, (N₀ : ℤ) ∈ q w := fun w hw => by
    have h1 : (N₀ : ℤ) ∈ 𝔞 := by
      rw [← hspan, Ideal.mem_span_singleton]
      exact Int.dvd_natAbs.2 dvd_rfl
    exact Ideal.prod_le_inf.trans (Finset.inf_le hw) h1
  refine ⟨N₀ ^ k, pow_pos (Int.natAbs_pos.2 hn0) k, fun v hv => ?_, fun v hv h => ?_⟩
  · have h1 : (N₀ : 𝓞 E) ∈ v.asIdeal := by
      have := hN₀q v hv
      rwa [hq, Ideal.mem_comap, map_natCast] at this
    rw [Nat.cast_pow]
    exact Ideal.pow_mem_pow h1 k
  · rw [Nat.cast_pow] at h
    have h1 : (N₀ : 𝓞 E) ∈ v.asIdeal := v.isPrime.mem_of_pow_mem k h
    have h2 : (N₀ : ℤ) ∈ q v := by rwa [hq, Ideal.mem_comap, map_natCast]
    have h3 : n ∈ q v := by
      obtain ⟨c, hc⟩ := (Int.natAbs_dvd.2 (dvd_refl n) : (N₀ : ℤ) ∣ n)
      rw [hc]
      exact Ideal.mul_mem_right _ _ h2
    haveI hp : (q v).IsPrime := Ideal.comap_isPrime _ _
    have h4 : 𝔞 ≤ q v := by rw [← hspan, Ideal.span_singleton_le_iff_mem]; exact h3
    obtain ⟨w, hw, hle⟩ := (Ideal.IsPrime.prod_le hp).1 h4
    have hmax : (q w).IsMaximal := (Ideal.comap_isPrime _ w.asIdeal).isMaximal (hq0 w)
    have heq : q w = q v := hmax.eq_of_le hp.ne_top hle
    exact hv (hS w hw v heq.symm)

variable [IsTotallyComplex E]

theorem mem_natLat_iff {N : ℕ} (hN : 0 < N) (z : Af E) :
    z ∈ GlobalTheory.RSJ.natLat E N ↔ ∀ v : HeightOneSpectrum (𝓞 E), Valued.v (z v) ≤ Valued.v (N : v.adicCompletion E) := by
  constructor
  · rintro ⟨y, hy, rfl⟩ v
    change Valued.v ((N : v.adicCompletion E) * y v) ≤ _
    rw [map_mul]
    exact mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hy v))
  · intro h
    set c : Af E := algebraMap E (Af E) ((N : E)⁻¹) with hc
    have hcN : c * (N : Af E) = 1 := by
      rw [hc, ← map_natCast (algebraMap E (Af E)), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), map_one]
    refine ⟨z * c, fun v => ?_, ?_⟩
    · have e : c v * (N : v.adicCompletion E) = 1 := congrArg (fun x : Af E => x v) hcN
      have e' : Valued.v (c v) * Valued.v (N : v.adicCompletion E) = 1 := by rw [← map_mul, e, map_one]
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (z v * c v) ≤ 1
      rw [map_mul, ← e', mul_comm (Valued.v (c v))]
      exact mul_le_mul_of_nonneg_right (h v) zero_le'
    · calc z = z * (c * (N : Af E)) := by rw [hcN, mul_one]
        _ = (N : Af E) * (z * c) := by ring

end GlobalTheory.RSParams

open GlobalTheory.RSParams in

theorem GlobalTheory.RSParams.exists_level_nat_bump : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∈ S, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ S) →
    ∀ V : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (V : Set (GL (Fin (m + 1)) (Af E))) →
    (∀ w ∉ S, ∀ k ∈ KGL w (m + 1), locGL E (m + 1) w k ∈ V) →
    ∃ (N : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ (Pi.single (Fin.last m) 1) ≠ 0 ∧
      (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) ∧
      GlobalTheory.RSLocalPart.levelAt (m + 1) S J ⊆ V ∧
      (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) ∧
      (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) ∧
      (∀ z z' : Af E, (∀ v ∈ S, z v = z' v) → (∀ v ∉ S, z v ∈ v.adicCompletionIntegers E) →
        (∀ v ∉ S, z' v ∈ v.adicCompletionIntegers E) → (z ∈ GlobalTheory.RSJ.natLat E N ↔ z' ∈ GlobalTheory.RSJ.natLat E N)) := by
  intro E _ _ _ m S hS V hV hw
  classical
  obtain ⟨J, hJS, -, hJV⟩ := GlobalTheory.RSLocalPart.exists_levelAt_subset S V hV hw
  set k : ℕ := ∑ v ∈ S, (FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat with hk
  obtain ⟨N, hN, hNS, hNc⟩ := exists_nat S hS k
  have hv1 : ∀ v : HeightOneSpectrum (𝓞 E), Valued.v (N : v.adicCompletion E) ≤ 1 := fun v => by
    rw [valued_natCast]; exact v.intValuation_le_one _
  have hvS : ∀ v ∈ S, Valued.v (N : v.adicCompletion E) ≤
      WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) := fun v hv => by
    rw [valued_natCast]
    refine ((v.intValuation_le_pow_iff_mem _ k).2 (hNS v hv)).trans (WithZero.exp_le_exp.2 ?_)
    have h1 : FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E) ≤
        ((FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat : ℤ) := Int.self_le_toNat _
    have h2 : (FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat ≤ k :=
      Finset.single_le_sum (f := fun v => (FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)).toNat)
        (fun _ _ => Nat.zero_le _) hv
    omega
  have hvn : ∀ v ∉ S, Valued.v (N : v.adicCompletion E) = 1 := fun v hv => by
    rw [valued_natCast]
    exact le_antisymm (v.intValuation_le_one _) (not_lt.1 fun h => hNc v hv ((v.intValuation_lt_one_iff_mem _).1 h))
  have he : (Pi.single (Fin.last m) 1 : Fin (m + 1) → Cinf E) ∈ GlobalTheory.RSTheta.rowSet E (Fin.last m) := fun w => by
    simp
  obtain ⟨ρ, hts, hcs, hcd, hr, h1⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    ((GlobalTheory.RSTheta.isOpen_rowSet (E := E) (Fin.last m)).mem_nhds he)
  have hr' : ∀ u, ρ u ∈ Set.Icc (0 : ℝ) 1 := fun u => hr ⟨u, rfl⟩
  refine ⟨N, J, fun u => (ρ u : ℂ), hN, Complex.ofRealCLM.contDiff.comp hcd, hcs.comp_left Complex.ofReal_zero,
    (tsupport_comp_subset Complex.ofReal_zero ρ).trans hts, fun u => ⟨by simpa using (hr' u).1, by simp⟩,
    by simp [h1], hJS, hJV, fun z hz v => ?_, fun z hz v hv => ?_, fun z z' hzz hz hz' => ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact ((mem_natLat_iff hN z).1 hz v).trans (hv1 v)
  · exact ((mem_natLat_iff hN z).1 hz v).trans (hvS v hv)
  · rw [mem_natLat_iff hN, mem_natLat_iff hN]
    refine forall_congr' fun v => ?_
    by_cases hv : v ∈ S
    · rw [hzz v hv]
    · rw [hvn v hv]
      exact ⟨fun _ => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hz' v hv),
        fun _ => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hz v hv)⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMirabolicWhittakerReductionCellStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mirabolic_whittaker_reduction_cell : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (F : GA E (m + 1) → ℂ)
    (U : Subgroup (GL (Fin (m + 1)) (Af E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
    (∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g) →
    (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g) →
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    (∀ y : Fin (m + 1) → Af E, y - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ κ ∈ U, (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
        ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
          pLoc E w (y j)) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, IsUnit (pInf E (g.val (Fin.last m) (Fin.last m))) →
      (fun i => pFin E (g.val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ p ∈ GlobalTheory.JSW.mirS E T m, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T,
        ‖GlobalTheory.JSW.whit F (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g *
          (infGL E (m + 1) (GlobalTheory.RSTheta.rowGL (Fin.last m) (fun i => pInf E (g.val (Fin.last m) i))))⁻¹)‖ =
        ‖GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l.1)‖ := by
  first | exact @GlobalTheory.WhitRed.exists_mirabolic | exact GlobalTheory.WhitRed.exists_mirabolic | (intros; apply GlobalTheory.WhitRed.exists_mirabolic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSetupPinnedCh
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeriesTie.ComplexCh

variable {D : D7}

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

open GlobalTheory.SeriesTie.Complex (eGc levOf castG levOf_mem levOf_chi)

theorem exists_setup_ch (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (F3 : Face3 D A3) (hC : Rl.Char3 F3)
    (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair)
    (hS0c : ∀ i, ∀ P ∈ D.ntw.S0 i, ∀ P', Formalism.BasicNotions.IsConjPl D.host P P' → P' ∈ D.ntw.S0 i)
    (hS02 : ∀ i, placesOver D.host.E 2 ⊆ ↑(D.ntw.S0 i))
    (hS0A : ∀ i P, P ∉ D.ntw.S0 i → FractionalIdeal.count D.host.E P D.host.AA = 0)
    (hδ : ∃ art : Ideles D.host.E →* Gab D.host.E D.nd.Om, IsGlobalArtin art ∧ ∀ i b,
      ∃ (κ : FractionRing (D.ntw.O0 i) →+* Qbar (D.ntw.l i)) (ι : Qbar (D.ntw.l i) ≃+* ℂ),
        (∀ x, ι (κ ((if b then D.ntw.emb0 i else D.ntw.emb0b i) x)) = embLL0 D x) ∧
        GlobalTheory.GalChar.IsGal art κ ι (Rl.C.delAt (D.ntw.l i)) (fun _ => 0) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)))
    (hcard : ∀ i k, Cardinal.mk (FractionRing (D.ntw.Ok i k)) ≤ Cardinal.continuum)
    (hspl : (Ideal.primesOver (Ideal.span {(D.host.pde : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E ∧
      (Ideal.primesOver (Ideal.span {(D.host.pde' : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E)
    (hq : D.host.pde ≠ D.host.q ∧ D.host.pde' ≠ D.host.q)
    (ch : D.ntw.Tw → Set (PlE D.host)) (hch1 : ∀ i, IsChoice (D := D) (ch i))
    (hch2 : ∀ i, {P : Pl D.host.E | ∃ t, P ∈ Rl.Q t ∧ P ∈ D.ntw.pD i} ⊆ ch i) :
    ∃ ρ : Setup D.ntw, ρ.Good ∧ RealPin Rl cG ρ ∧ ρ.LevelOf D.nexp ∧ ρ.ch = ch ∧
      ∀ i, ρ.bad i = GlobalTheory.SeriesTie.normProd (D.ntw.S0 i) := by
  classical
  obtain ⟨art, hart, hδ⟩ := hδ
  choose κ ι hκι hG using hδ
  obtain ⟨κA, hκ1, hκ2, hκ3⟩ := GlobalTheory.CharTransport.exists_hom D
  let rc : Recip D D.nd.Om := ⟨κA, art⟩
  have hrc : rc.Good := ⟨hκ1, hκ2, hκ3, hart⟩
  obtain ⟨e, ek, he1, he2, he3⟩ := GlobalTheory.T.exists_ladicCoefficientField_embeddings_complex D D.nd D.ntw (fun i b => (ι i b).toRingHom.comp (κ i b)) hκι hcard
  choose F hF hFstd hFψ hFθ hFsT hFBS hFBT hFΛS hFΛT hFβS hFβT hFf hFlS hFlT using GlobalTheory.T.exists_good_frame_realisation D Γ Pl0 I0 T A3 Ks Rl F3 hC
  let f : ∀ i, Bool → (D.ntw.O0 i →+* ℂ) := fun i b =>
    ((e i b).comp (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)))).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))
  have hfi : ∀ i b, Function.Injective (f i b) := fun i b =>
    ((e i b).injective.comp (IsFractionRing.injective (D.ntw.O i) (FractionRing (D.ntw.O i)))).comp (D.ntw.O_inj i)
  let de : D.ntw.Tw → Bool → Twist D Circle := fun i b =>
    twistOf rc (f i b) (ch i) (D.ntw.pD i) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))
  have hde : ∀ i b, (de i b).Good := fun i b => GlobalTheory.T.artin_twisting_character_delta_good D rc hrc i (ch i) (hch1 i) (f i b) (hfi i b) b
  have hpl : ∀ i b, PlacesOK Rl.Pg (de i b).Q := fun i _ =>
    GlobalTheory.T.typePlaces_twistPlaces_goodPosition D Γ Pl0 I0 T A3 Ks Rl A3.A.μ0 hC.lev hspl hq i (ch i) (hch1 i)
  have hB := fun i j b => GlobalTheory.T.liftBaseData_isGood_twist D Γ Pl0 I0 T A3 Ks Rl F3 hC j (F j) (hF j) (de i b) (hde i b) (hpl i b)
  choose w mu hwp hwm hBg using hB
  let P : D.ntw.Tw → ∀ j : Fin D.R.m, Bool → LevelP Rl.Pg (Wc D j).rank ℂ := fun i j b =>
    ⟨(levOf (eGc Rl cG j) D.nexp.U ((Units.map (e i b).toMonoidHom).comp (D.nexp.psiU i b))).1,
      (levOf (eGc Rl cG j) D.nexp.U ((Units.map (e i b).toMonoidHom).comp (D.nexp.psiU i b))).2⟩
  let B : D.ntw.Tw → ∀ j : Fin D.R.m, Bool → Base (Vc D j) (Wc D j) := fun i j b =>
    ⟨(hF j).rank_le, F j, ⟨Rl.Pg, P i j b, mu i j b⟩, de i b, w i j b, Rl.mu0 ((j : ℕ) + 1), Rl.eta⟩
  have hBG : ∀ i j b, (B i j b).Good := fun i j b => hBg i j b (P i j b)
  have hom : ∀ i j b (χ : (AE D)ˣ →* Circle), ∃ ω : PairRep (Vc D j) (Wc D j),
      ∀ t : Twist D Circle, t.Good → t.chi = χ → (B i j b).IsWeil χ ω := by
    intro i j b χ
    by_cases h : ∃ t : Twist D Circle, t.Good ∧ t.chi = χ
    · obtain ⟨t, ht, rfl⟩ := h
      obtain ⟨ω, hω⟩ := GlobalTheory.T.exists_weilRep_good_twist D _ _ (B i j b) hW (hBG i j b) (hFstd j) t ht
      exact ⟨ω, fun _ _ _ => hω⟩
    · exact ⟨1, fun t ht h' => absurd ⟨t, ht, h'⟩ h⟩
  choose om hom using hom
  have hcl : ∀ i j b (t : Twist D Circle), ∃ (m : ℕ) (h : Fin m → GA D (Vc D j)),
      IsClassSystem (Vc D j) ((B i j b).levJ t) h := fun i j b t =>
    exists_isClassSystem (B i j b) (hBG i j b).frame t
  choose m rep hrep using hcl
  let ρ : Setup D.ntw :=
    { rc := rc
      ch := ch
      bad := fun i => ∏ P ∈ D.ntw.S0 i, Ideal.absNorm P.asIdeal
      e := e
      ek := ek
      B := B
      om := om
      Cl := fun i j b t => Fin (m i j b t)
      rep := rep
      β := fun j P => DetBases.std _ _ _
      eG := fun _ j _ => eGc Rl cG j }
  refine ⟨ρ, ?_, ?_, ?_, rfl, fun _ => rfl⟩
  · exact
      { rc := hrc
        ch := hch1
        bad_ne := fun i => Finset.prod_ne_zero_iff.2 fun P _ h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
        goodSetup_bad_mem_badPlaces := fun i P hP => by
          obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun Q : Pl D.host.E => Ideal.absNorm Q.asIdeal) hP
          change ((∏ P ∈ D.ntw.S0 i, Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
          rw [hc, Nat.cast_mul]
          exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
        goodSetup_badPlaces_conj := hS0c
        goodSetup_placesOverTwo_subset := hS02
        goodSetup_count_eq_zero_off_badPlaces := hS0A
        e_LL0 := he1
        ek_e := fun i b k x => he2 i b k x
        base := hBG
        latS := fun _ j _ => hFlS j
        latT := fun _ j _ => hFlT j
        Pg := fun _ _ _ P hP => GlobalTheory.T.typePlaces_mem_placesOver_generators D Γ Pl0 I0 T A3 Ks Rl F3 hC P hP
        delta := fun _ _ _ => rfl
        weil := fun i j b t ht => hom i j b t.chi t ht rfl
        classes := fun i j b t _ _ => hrep i j b t }
  · exact
      { psi := fun _ j _ => hFψ j
        inf := fun _ j _ => hFθ j
        cartT := fun _ j _ => hFsT j
        onbS := fun _ j _ τ => hFBS j τ
        onbT := fun _ j _ => hFBT j
        latS := fun _ j _ => hFΛS j
        latT := fun _ j _ => hFΛT j
        frS := fun _ j _ => hFβS j
        frT := fun _ j _ => hFβT j
        vac := fun _ j _ => hFf j
        Pg := fun _ _ _ => rfl
        grp := fun _ j _ g P h h' a c => rfl
        mu0 := fun _ _ _ => rfl
        eta := fun _ _ _ => rfl
        delta := fun i j b => by
          exact GlobalTheory.T.twistingCharacter_ladicGaloisCharacter_eq_hecke D rc i (κ i b) (ι i b) (Rl.C.delAt (D.ntw.l i)) (D.ntw.delta i) b hrc (D.ntw.delta_open i) (hG i b)
            (f i b) (fun y hy => he3 i b y hy) (ch i) (D.ntw.pD i)
        deltaPl := fun i t P hP hPD => hch2 i ⟨t, hP, hPD⟩
        ap := fun i j b τ => hwp i j b τ
        am := fun i j b τ => hwm i j b τ }
  · exact
      { U_eq := fun i j b g => levOf_mem (eGc Rl cG j) D.nexp.U ((Units.map (e i b).toMonoidHom).comp (D.nexp.psiU i b)) g
        psiU_eq := fun i j b u hu => congrArg Units.val
          (levOf_chi (eGc Rl cG j) D.nexp.U ((Units.map (e i b).toMonoidHom).comp (D.nexp.psiU i b)) u hu) }

end GlobalTheory.SeriesTie.ComplexCh

end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwInputs.SetupPinCh

end GlobalTheory.TwInputs.SetupPinCh

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicMapExtremalVectorEqPhaseSmulLettersStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicMap_extremalVector_eq_phase_smul_letters : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsCoefMap R i c0 → ∀ lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank ≃ FVar D (Wc D i).rank (Vc D i).rank, IsLetters (T.Q.Dw ((i : ℕ) + 1)) lt → ∃ ka : ℂ, ‖ka‖ = 1 ∧ ∃ J : VsV D i ℂ →ₗ[ℂ] MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) ℂ, (∀ v, J v ∈ HHa (T.Q.Dw ((i : ℕ) + 1)).mult (Vc D i).rank ℂ ComplexEmbedding.conjugate (InPsi T.Q.H) (fun τ j => wtA (κ i) (τ, j))) ∧ (∀ k : Subfield ℂ, (∀ x ∈ T.Q.c.F, x ∈ k) → ∀ v : VsV D i ℂ, (∀ m, MvPolynomial.coeff m (v : Formalism.L2.DIV.Pol ℂ D.what₂.Tau (Vc D i).rank) ∈ k) → ∀ mo, (J v).coeff mo ∈ k) ∧ ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ v, pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f (R.ioP i (PiTensorProduct.tprod ℂ u) (c0 v)) = ka • stdF R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) f (MvPolynomial.rename lt (J v)) := by
  first | exact @GlobalTheory.SerIntLetters.io_eq_phase_smul_harmLetters | exact GlobalTheory.SerIntLetters.io_eq_phase_smul_harmLetters | (intros; apply GlobalTheory.SerIntLetters.io_eq_phase_smul_harmLetters <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdeleModuleDetDiagonalUniformiserMulStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleModule_det_diagonalUniformiser_mul : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ),
    (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (g : GA E n),
      (ideleModule E (GeneralLinearGroup.det (GlobalTheory.CellDec.tl n ϖ l * g)) : ℝ) =
        (∏ v ∈ l.support, ((qV E v : ℝ) ^ (∑ i, l v i))⁻¹) * (ideleModule E (GeneralLinearGroup.det g) : ℝ) := by
  first | exact @GlobalTheory.CellDec.DetMod.ideleModule_det_tl_mul | exact GlobalTheory.CellDec.DetMod.ideleModule_det_tl_mul | (intros; apply GlobalTheory.CellDec.DetMod.ideleModule_det_tl_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdelicAbsDetPowDiagonalUniformizerMul
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
namespace GlobalTheory.CellEvalDet

open Matrix

variable {E : Type} [Field E] [NumberField E]

theorem detPow_eq_rpow {n : ℕ} (x : ℝ) (g : GA E n) :
    GlobalTheory.RSJ.detPow E n x g =
      ((GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ) := by
  have hpos := (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g)).2
  rw [Real.rpow_def_of_pos hpos, ← GlobalTheory.IdeleLogNormCompare.logNorm_eq_log_ideleModule]
  simp only [GlobalTheory.RSJ.detPow, chiDet, GlobalTheory.HeckeGal.Model.absPow, MonoidHom.coe_comp, Function.comp_apply]
  change ‖Complex.exp ((x : ℂ) * (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det g) : ℂ))‖ = _
  rw [Complex.norm_exp]
  congr 1
  simp [mul_comm]

theorem det_diagT {R : Type} [CommRing R] {n : ℕ} (t : Fin n → Rˣ) :
    GeneralLinearGroup.det (GlobalTheory.SmGL.diagT R (Fin n) t) = ∏ i, t i := by
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, GlobalTheory.SmGL.val_diagT, det_diagonal, Units.coe_prod]

def posVal : {r : ℝ // 0 < r} →* ℝ where
  toFun r := r
  map_one' := rfl
  map_mul' _ _ := rfl

theorem qV_pos (v : HeightOneSpectrum (𝓞 E)) : (0 : ℝ) < qV E v :=
  lt_of_le_of_ne (Nat.cast_nonneg _) (GlobalTheory.AdeleScale.qV_ne_zero v).symm

end GlobalTheory.CellEvalDet

open GlobalTheory.CellEvalDet Matrix in

theorem GlobalTheory.CellEvalDet.detPow_tl_mul : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (x : ℝ) (g : GA E n),
    GlobalTheory.RSJ.detPow E n x (GlobalTheory.CellDec.tl n ϖ l * g) =
      (∏ w ∈ l.support, (qV E w : ℝ) ^ (-x * ∑ i, (l w i : ℝ))) * GlobalTheory.RSJ.detPow E n x g := by
  intro E _ _ _ n ϖ hϖ l x g
  rw [GlobalTheory.RSJ.Model.detPow_mul, detPow_eq_rpow x (GlobalTheory.CellDec.tl n ϖ l)]
  congr 1
  have hdet : GeneralLinearGroup.det (GlobalTheory.CellDec.tl n ϖ l) =
      ∏ i, finId E (GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun y : Fin n → ℤ => y i) rfl l)) := by
    unfold GlobalTheory.CellDec.tl
    rw [det_finGL, det_diagT, map_prod]
  have hmod : ((GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det (GlobalTheory.CellDec.tl n ϖ l)) : ℝ)) =
      ∏ i, ∏ v ∈ l.support, ((qV E v : ℝ) ^ (l v i))⁻¹ := by
    rw [hdet, map_prod]
    change posVal (∏ i, _) = _
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    change ((GroundTheory.Global.IdeleGroup.ideleModule E _ : ℝ)) = _
    rw [GlobalTheory.AdeleScale.ideleModule_finId_adl ϖ hϖ _ l.support (fun v hv => by
      rw [Finsupp.notMem_support_iff] at hv; simp [hv])]
    simp
  rw [hmod, Finset.prod_comm, ← Real.finset_prod_rpow _ _ (fun v _ =>
    Finset.prod_nonneg fun i _ => inv_nonneg.2 (zpow_nonneg (Nat.cast_nonneg _) _))]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hq := qV_pos (E := E) v
  have e : ∀ i, ((qV E v : ℝ) ^ (l v i))⁻¹ = (qV E v : ℝ) ^ (-(l v i : ℝ)) := fun i => by
    rw [Real.rpow_neg hq.le, Real.rpow_intCast]
  simp_rw [e]
  rw [← Real.rpow_sum_of_pos hq, ← Real.rpow_mul hq.le]
  congr 1
  rw [Finset.sum_neg_distrib]
  ring
end

