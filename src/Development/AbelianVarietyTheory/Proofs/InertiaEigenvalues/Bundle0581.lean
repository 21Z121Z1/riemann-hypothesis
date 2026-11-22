import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0565
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsNormalChartsOfCoveringCharts
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0006
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0004
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0403
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0438
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0058
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0416
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0172
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0569
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.ThetaScalarFamilyOfEigenvalue
import Formalism.SharpRestriction.LevelLetterCocycles.ExportBoundOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0570
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0476
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateLogNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTatePeriodGaloisExpansion
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralOfIntegralAtAlgebraicPointsSmooth
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer

namespace GlobalTheory.ChartIntegral

open GlobalTheory.Reg.NormalCharts GlobalTheory.PlaceCompletion

theorem exists_quotient_of_bounded (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O] [CommRing A] [IsDomain A]
    [Algebra O A] [Algebra.FiniteType O A] [IsIntegrallyClosed A]
    (hOA : Function.Injective (algebraMap O A)) (e : A) (he : e ≠ 0) (f : FractionRing A)
    (hf : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →+* V), (∀ a, φ (algebraMap O A a) = algebraMap O V a) → φ e ≠ 0 →
      ∀ a b : A, f * algebraMap A _ b = algebraMap A _ a → φ b ≠ 0 → φ b ∣ φ a) :
    ∃ x s : A, s - 1 ∈ Ideal.map (algebraMap O A) (IsLocalRing.maximalIdeal O) ∧
      f * algebraMap A _ s = algebraMap A _ x := by
  have hid : Function.Injective (algebraMap O O) := fun _ _ h => h
  have : IsLocalHom (algebraMap O O) := ⟨fun _ h => h⟩
  obtain ⟨s, hs, hint⟩ := GlobalTheory.isIntegral_mul_of_bounded_at_points O O hid
    (GlobalTheory.exists_integral_point_of_complete_case
      (fun O B _ _ _ _ _ _ _ _ _ _ M hM hsp e he => GlobalTheory.exists_integral_point_through O B M hM hsp e he)
      O O hid) A (FractionRing A) hOA e he f
    (fun V _ _ _ _ _ φ hφ => hf V φ (fun a => RingHom.congr_fun hφ a))
  obtain ⟨x, hx⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  exact ⟨x, s, hs, by rw [hx, _root_.mul_comm]⟩

theorem integral_of_integral_at_algebraic_points :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (la : HeightOneSpectrum (𝓞 K)) (gens : Finset Ω) (e : Ω), Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤ → e ≠ 0 → e ∈ Subring.closure (Set.range ((algebraMap K Ω).comp (la.valuation K).valuationSubring.subtype) ∪ (gens : Set Ω)) → Algebra.Smooth K (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))) → ∀ r : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (∀ (T : CDVR) (io : K →+* T.Fr) (n : ℕ), OverLa la T.V io n → T.FinRes → ∀ ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →+* T.Fr, (∀ k : K, ψ (algebraMap K _ k) = io k) → (∀ g : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (g : Ω) ∈ gens → InV T (ψ g)) → InV T (ψ r)) → ∀ (T : CDVR) (io : K →+* T.Fr) (n : ℕ), OverLa la T.V io n → ∀ ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →+* T.Fr, (∀ k : K, ψ (algebraMap K _ k) = io k) → (∀ g : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (g : Ω) ∈ gens → InV T (ψ g)) → InV T (ψ r) := by
  intro K Ω _ _ _ _ la gens e hgen he hemem hsm r hr T io n ho ψ hψK hψg
  obtain ⟨T₀, io₀, hov, hfin, hinit⟩ := exists_initial_completion K la
  have hβ : ∀ a : (la.valuation K).valuationSubring,
      io₀ ((la.valuation K).valuationSubring.subtype a) ∈ Set.range (algebraMap T₀.V T₀.Fr) := fun a =>
    exists_algebraMap_eq_of_valV_le_one (by
      rw [valV_eq_pow_of_overLa hov]
      exact pow_le_one₀ zero_le a.2)
  obtain ⟨J, finJ, A, acr, adom, alg, α, hA, hK, hg, hcov⟩ :=
    GlobalTheory.exists_normal_charts_over_dvr K Ω T₀.V io₀ gens {e} hgen
      (fun e' he' => by
        obtain rfl := Finset.mem_singleton.1 he'
        refine ⟨he, Subring.closure_mono ?_ hemem⟩
        refine Set.union_subset_union_left _ ?_
        rintro _ ⟨a, rfl⟩
        exact ⟨_, hβ a, rfl⟩)
      (fun e' he' => by
        obtain rfl := Finset.mem_singleton.1 he'
        exact hsm)
  obtain ⟨g, χ, hloc, hχio, hχg, -⟩ := hinit T io n ho
  have hχg' : ∀ a, χ (algebraMap T₀.V T₀.Fr a) = algebraMap T.V T.Fr (g a) :=
    fun a => RingHom.congr_fun hχg a
  obtain ⟨j, φ, hφW, hφO, hφψ⟩ := hcov e (Finset.mem_singleton_self e) T.Fr (imageVal T.V T.Fr) χ ψ
    (fun k => (hψK k).trans (RingHom.congr_fun hχio k).symm)
    (fun a => (mem_imageVal _).2 ⟨g a, (hχg' a).symm⟩)
    (fun x hx => (mem_imageVal _).2 (hψg x hx))
  obtain ⟨φ', hφ'⟩ := exists_corestrict (V := T.V) φ fun x => (mem_imageVal _).1 (hφW x)
  have hc : ∀ a, φ' (algebraMap T₀.V (A j) a) = g a := fun a =>
    IsFractionRing.injective T.V T.Fr (by rw [hφ', hφO, hχg'])
  obtain ⟨hft, -, hic⟩ := hA j
  have hOA : Function.Injective (algebraMap T₀.V (A j)) := by
    intro a b hab
    apply IsFractionRing.injective T₀.V T₀.Fr
    apply χ.injective
    exact (hφO a).symm.trans ((congrArg φ hab).trans (hφO b))
  obtain ⟨eb, heb⟩ : α j e ∈ Set.range (algebraMap (A j) (FractionRing (A j))) := by
    refine (Subring.closure_le (t := (algebraMap (A j) (FractionRing (A j))).range.comap (α j))).2 ?_ hemem
    rintro x (⟨a, rfl⟩ | hx)
    · obtain ⟨x, hx⟩ := hβ a
      have := hK j ((la.valuation K).valuationSubring.subtype a) x 1 (by rw [map_one, _root_.mul_one, hx])
      rw [map_one, map_one, _root_.mul_one] at this
      exact ⟨_, this.symm⟩
    · exact hg j x hx
  have heb0 : eb ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, map_eq_zero] at heb
    exact he heb
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T₀.V
  obtain ⟨x, s, hs, hxs⟩ := exists_quotient_of_bounded T₀.V (A j) hOA eb heb0 (α j r) (by
    intro V _ _ _ _ _ ρ hρ h0 a b hab hb
    obtain ⟨hinj, hlocV, hcpl, hch, hfin'⟩ := GlobalTheory.dvr_finite_over_complete_dvr T₀.V V
    obtain ⟨χ', m, hm, hχ', hv⟩ := exists_ramification (K' := FractionRing V) (F := T₀.Fr)
      (algebraMap T₀.V V) hinj hlocV
    obtain ⟨ψ', hψ'⟩ := (GlobalTheory.Reg.openChart_regular_away K Ω T₀.V (A j) io₀ gens e (α j) eb ϖ hϖ he heb
      (hK j) (hg j)).2 (FractionRing V) ((algebraMap V (FractionRing V)).comp ρ) (by
        change algebraMap V (FractionRing V) (ρ _) ≠ 0
        rw [map_mul, hρ]
        simpa using mul_ne_zero ((map_ne_zero_iff _ hinj).2 hϖ.ne_zero) h0)
    replace hψ' : ∀ (r : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))) (x s : A j),
        α j r * algebraMap (A j) _ s = algebraMap (A j) _ x →
        ψ' r * algebraMap V _ (ρ s) = algebraMap V _ (ρ x) := hψ'
    let T' : CDVR := { V := V }
    have hψK' : ∀ k : K, ψ' (algebraMap K _ k) = (χ'.comp io₀) k := by
      intro k
      obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := T₀.V) (io₀ k)
      have hb0 : algebraMap T₀.V T₀.Fr b ≠ 0 := by simpa using nonZeroDivisors.ne_zero hb
      have h1 : io₀ k * algebraMap T₀.V _ b = algebraMap T₀.V _ a := by
        rw [← hab, div_mul_cancel₀ _ hb0]
      have h2 := hψ' (algebraMap K _ k) _ _ (hK j k a b h1)
      rw [hρ, hρ, ← hχ', ← hχ', ← h1, map_mul] at h2
      exact mul_right_cancel₀ ((map_ne_zero χ').2 hb0) h2
    obtain ⟨v, hv'⟩ : ψ' r ∈ Set.range (algebraMap V (FractionRing V)) :=
      hr T' (χ'.comp io₀) (m * 1) (hov.bc χ' hm hv) (hfin' hfin) ψ' hψK' (fun y hy => by
        obtain ⟨x, hx⟩ := hg j y hy
        have := hψ' y x 1 (by rw [map_one, _root_.mul_one, hx])
        rw [map_one, map_one, _root_.mul_one] at this
        exact ⟨ρ x, this.symm⟩)
    refine ⟨v, IsFractionRing.injective V (FractionRing V) ?_⟩
    rw [← hψ' r a b hab, ← hv', map_mul, _root_.mul_comm])
  have hm : φ' (s - 1) ∈ IsLocalRing.maximalIdeal T.V := by
    refine (Ideal.map_le_iff_le_comap (K := (IsLocalRing.maximalIdeal T.V).comap φ')).2 ?_ hs
    intro a ha
    change φ' (algebraMap T₀.V (A j) a) ∈ IsLocalRing.maximalIdeal T.V
    rw [hc]
    exact fun hu => ha (hloc.map_nonunit a hu)
  have hu : IsUnit (φ' s) := by
    by_contra hnu
    have h1 : φ' s - φ' (s - 1) ∈ IsLocalRing.maximalIdeal T.V := sub_mem hnu hm
    rw [← map_sub, sub_sub_cancel, map_one] at h1
    exact h1 isUnit_one
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have h2 := hφψ r x s hxs
  refine ⟨φ' x * w, ?_⟩
  rw [map_mul, hφ', ← h2, ← hφ', _root_.mul_assoc, ← map_mul, hw, map_one, _root_.mul_one]

end GlobalTheory.ChartIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysOfCrystallineBreuilKisinFrame
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.CrTop

theorem map_smul_ring {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ} (c : R)
    (M : Matrix (Fin d) (Fin d) R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

theorem pow_cancel {R : Type} [CommRing R] {lr : R} (h : ∀ x : R, lr * x = 0 → x = 0) (n : ℕ) :
    ∀ x : R, lr ^ n * x = 0 → x = 0 := by
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih => intro x hx; exact ih x (h _ (by rw [← mul_assoc, ← pow_succ']; exact hx))

theorem smul_cancel {R : Type} [CommRing R] {c : R} (h : ∀ x : R, c * x = 0 → x = 0) {d : ℕ}
    {M M' : Matrix (Fin d) (Fin d) R} (hM : c • M = c • M') : M = M' := by
  ext i j
  have := congrFun (congrFun hM i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact sub_eq_zero.1 (h _ (by rw [mul_sub, this, sub_self]))

theorem crys_of_frame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (N : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (F : Frame bk N d fun g => (ρ g).val), F.IsCr → IsCrys (P.PD K) (qRep ρ) := by
  intro l _ K bk τ hτ P AI T N d ρ F hcr
  obtain ⟨Y, Y', hY, hYY⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N d (fun g => (ρ g).val) F.toPre
  obtain ⟨-, hR1, hE2⟩ := GlobalTheory.T.frame_ainf_matrix_frobenius_galois_eqs l K bk τ hτ N d (fun g => (ρ g).val) F Y Y' hY hYY
  obtain ⟨k, Q, Q', hQQ, hQu, hQ'u, hQφ⟩ := GlobalTheory.T.exists_frobenius_section_acris_breuilKisin l K bk N d F.A F.A' F.A_mul
  obtain ⟨htf, -, ⟨v, hv⟩, hφι, hσι⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  set ι := algebraMap (Ainf l) (Per.Acris l) with hι

  have key : ∀ g : ↥(GK K), (F.ε g).map (fun a => ι (WittVector.frobenius a)) * Q.map (sigA (g : GQ l)) = Q := by
    intro g
    set σ := sigA (g : GQ l) with hσdef
    set fA : bk.S →+* Per.Acris l := (ι.comp bk.ev).comp (frobS l bk.a) with hfA
    set f0 : bk.S →+* Per.Acris l := fA.comp ((PowerSeries.C).comp PowerSeries.constantCoeff) with hf0
    set ε' := (F.ε g).map (fun a => ι (WittVector.frobenius a)) with hε'
    have hfr : ∀ s : bk.S, fA s = ι (WittVector.frobenius (bk.ev s)) := fun s => by
      simp only [hfA, RingHom.comp_apply, bk.ev_frob]
    have hfix : ∀ c : Wq l bk.a, σ (fA (PowerSeries.C c)) = fA (PowerSeries.C c) := fun c => by
      rw [hfr, hσdef, hσι, ← GlobalTheory.RingBasics.φA_apply, ← ActLaws.φA_σA, bk.ev_C, bk.gal_w g c]
    have hcomm : ∀ x, phiA l (σ x) = σ (phiA l x) := fun x => by
      simp only [hσdef]
      exact GlobalTheory.CrisMaps.phiA_sigA (g : GQ l) x
    have he₀ : ∃ w : (Per.Acris l)ˣ, f0 bk.E = (l : Per.Acris l) * w := by
      obtain ⟨w, hw⟩ := bk.coeff_zero
      have hc : PowerSeries.constantCoeff bk.E = (l : Wq l bk.a) * w := by
        rw [← hw]; simp
      refine ⟨((Units.map (PowerSeries.C (R := Wq l bk.a)).toMonoidHom w).map fA.toMonoidHom), ?_⟩
      simp [hf0, hc]

    have hBB : F.A.map fA * F.A'.map fA = fA bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
      rw [← Matrix.map_mul, F.A_mul, map_smul_ring, map_pow, Matrix.map_one _ (map_zero _) (map_one _)]
    have hAA : F.A.map f0 * F.A'.map f0 = f0 bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
      rw [← Matrix.map_mul, F.A_mul, map_smul_ring, map_pow, Matrix.map_one _ (map_zero _) (map_one _)]
    have hσA₀ : (F.A.map f0).map σ = F.A.map f0 := by
      ext i j; simp only [Matrix.map_apply, hf0, RingHom.comp_apply]; exact hfix _
    have hσe₀ : σ (f0 bk.E) = f0 bk.E := by simp only [hf0, RingHom.comp_apply]; exact hfix _
    have hσf : ∀ s : bk.S, ι (WittVector.frobenius (Per.σA (g : GQ l) (bk.ev s))) = σ (fA s) := fun s => by
      rw [hfr, hσdef, hσι, ← GlobalTheory.RingBasics.φA_apply, ← GlobalTheory.RingBasics.φA_apply, ActLaws.φA_σA]
    have h2 : fA bk.E ^ N • (ε' * (F.A.map fA).map σ) = σ (fA bk.E) ^ N • (F.A.map fA * ε'.map (phiA l)) := by
      have e := congrArg (fun M => M.map (ι.comp WittVector.frobenius)) (hE2 g)
      simp only [map_smul_ring, Matrix.map_mul, Matrix.map_map, map_pow, RingHom.comp_apply] at e
      convert e using 3
      · rw [hfr]
      · ext i j; simp [hε']
      · ext i j; simp only [Matrix.map_apply, Function.comp_apply, RingHom.comp_apply]; rw [hσf]
      · rw [hσf]
      · ext i j; simp only [Matrix.map_apply, Function.comp_apply, RingHom.comp_apply]; rw [hfr]
      · ext i j; simp only [Matrix.map_apply, Function.comp_apply, RingHom.comp_apply, hε']; rw [hφι]
    have hL1 := GlobalTheory.T.frobenius_equation_of_twisted_cocycle_defect (Per.Acris l) (phiA l) σ d N k (l : Per.Acris l) (fA bk.E) (f0 bk.E) Q Q' (F.A.map fA) (F.A'.map fA)
      (F.A.map f0) (F.A'.map f0) ε' htf ⟨v, hv⟩ he₀ hcomm (map_natCast _ _) (map_natCast _ _) hσe₀ hσA₀ hQQ hBB hAA hQφ h2

    obtain ⟨w₀, hw₀⟩ := he₀
    set D := Q' * ε' * Q.map σ - (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) with hD
    have hDeq : (l : Per.Acris l) ^ (2 * N) • D = F.A.map f0 * D.map (phiA l) * (((w₀⁻¹ : (Per.Acris l)ˣ) : Per.Acris l) ^ (2 * N) • F.A'.map f0) := by
      rw [Matrix.mul_smul, ← hL1, smul_smul, hw₀]
      congr 1
      rw [mul_pow, mul_left_comm, ← mul_pow, Units.inv_mul, one_pow, mul_one]

    set u := ι (bk.ev X) with hu
    set π := Ideal.Quotient.mk (Ideal.span {u}) with hπ
    have hz : ∀ M : Matrix (Fin d) (Fin d) (Per.Acris l), (∀ i j, u ∣ M i j) ↔ M.map π = 0 := fun M => by
      constructor
      · intro h; ext i j
        simpa [hπ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using h i j
      · intro h i j
        have := congrFun (congrFun h i) j
        simpa [hπ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using this
    have hQ1 : Q.map π = ((l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))).map π := by
      rw [← sub_eq_zero, ← Matrix.map_sub _ (map_sub π)]; exact (hz _).1 hQu
    have hQ'1 : Q'.map π = ((l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))).map π := by
      rw [← sub_eq_zero, ← Matrix.map_sub _ (map_sub π)]; exact (hz _).1 hQ'u
    have hdvdφ : bk.ev X ∣ WittVector.frobenius (bk.ev X) := by
      rw [bk.ev_X, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
      exact dvd_pow_self _ (Fact.out : l.Prime).ne_zero
    have hε1 : ε'.map π = 1 := by
      have : ∀ i j, u ∣ (ε' - 1) i j := fun i j => by
        obtain ⟨c, hc⟩ := hcr g i j
        have e1 : (ε' - 1) i j = ι (WittVector.frobenius ((F.ε g - 1) i j)) := by
          simp only [hε', Matrix.sub_apply, Matrix.map_apply, map_sub]
          by_cases hij : i = j
          · subst hij; simp
          · simp [Matrix.one_apply_ne hij]
        rw [e1, hc, map_mul, map_mul]
        exact dvd_mul_of_dvd_left (map_dvd ι hdvdφ) _
      rw [← sub_eq_zero, ← Matrix.map_one π (map_zero _) (map_one _), ← Matrix.map_sub _ (map_sub π)]
      exact (hz _).1 this
    have hQσ : (Q.map σ).map π = ((l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))).map π := by
      have hdσ : u ∣ σ u := by
        rw [hu, hσdef, hσι]; exact map_dvd ι ((galois_discMap l K bk).1 (g : GQ l))
      have : ∀ i j, u ∣ (Q.map σ - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j := fun i j => by
        have e1 : (Q.map σ - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j =
            σ ((Q - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j) := by
          by_cases hij : i = j
          · subst hij; simp
          · simp [Matrix.one_apply_ne hij]
        obtain ⟨c, hc⟩ := hQu i j
        rw [e1, hc, map_mul]
        exact dvd_mul_of_dvd_left hdσ _
      rw [← sub_eq_zero, ← Matrix.map_sub _ (map_sub π)]; exact (hz _).1 this
    have hdiv : ∀ i j, ι (bk.ev X) ∣ D i j := by
      refine (hz D).2 ?_
      rw [hD, Matrix.map_sub _ (map_sub π), Matrix.map_mul, Matrix.map_mul, hQ'1, hε1, hQσ]
      simp only [map_smul_ring, Matrix.map_one _ (map_zero _) (map_one _), mul_one, smul_mul_smul_comm, map_pow]
      rw [← pow_add, ← two_mul, sub_self]
    have hD0 := GlobalTheory.T.acris_frobenius_matrix_eq_zero_of_dvd l K bk d (2 * N) D (F.A.map f0) _ hdiv hDeq
    have hM : Q' * ε' * Q.map σ = (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) :=
      sub_eq_zero.1 hD0
    refine smul_cancel (pow_cancel htf (2 * k)) ?_
    have := congrArg (fun M => Q * M) hM
    simp only [← Matrix.mul_assoc, hQQ, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] at this
    exact this
  obtain ⟨U, hU, hinv⟩ := GlobalTheory.T.exists_invariant_unit_matrix_bcris_frame l K bk τ hτ N d k ρ Y Y' F.ε Q Q' hYY hR1 hQQ key
  exact GlobalTheory.T.isCrystalline_of_invariant_unit_bcris_matrix l K P AI T d ρ U hU hinv

end GlobalTheory.CrTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGaloisRatComplexImageRayClassField
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Published GlobalTheory.RayTopGalois GlobalTheory.FieldSize

namespace GlobalTheory.RayNatGalois

theorem isModulus_transport {K K' N : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field N]
    [NumberField N] [Algebra K N] [Algebra K' N] (s : K ≃+* K')
    (hs : ∀ x, algebraMap K' N (s x) = algebraMap K N x) [IsGalois K N] [IsGalois K' N] {𝔪 : Ideal (𝓞 K)}
    {𝔪' : Ideal (𝓞 K')} (hm' : 𝔪' ≠ ⊥) (hmm : ∀ x, RingOfIntegers.mapRingEquiv s x ∈ 𝔪' ↔ x ∈ 𝔪)
    (h : ∀ χ : (N ≃ₐ[K] N) →* ℂˣ, IsModulus N χ 𝔪) (χ : (N ≃ₐ[K'] N) →* ℂˣ) : IsModulus N χ 𝔪' := by
  have hc : ∀ a : 𝓞 K, IsCoprime (Ideal.span {RingOfIntegers.mapRingEquiv s a}) 𝔪' →
      IsCoprime (Ideal.span {a}) 𝔪 := fun a H => by
    rw [Ideal.isCoprime_iff_exists] at H ⊢
    obtain ⟨i, hi, j, hj, hij⟩ := H
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hi
    obtain ⟨c, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective c
    obtain ⟨j, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective j
    refine ⟨c * a, Ideal.mem_span_singleton'.2 ⟨c, rfl⟩, j, (hmm j).1 hj,
      (RingOfIntegers.mapRingEquiv s).injective ?_⟩
    rw [map_add, map_mul, hij, map_one]
  refine ⟨hm', fun 𝔭 hp => ?_, fun α β hr => ?_⟩
  · obtain ⟨𝔮, rfl⟩ := (primeEquiv s).surjective 𝔭
    rw [heckeVal_transport s hs]
    refine (h _).2.1 𝔮 fun H => hp (Ideal.dvd_iff_le.2 fun x hx => ?_)
    obtain ⟨y, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective x
    change (RingOfIntegers.mapRingEquiv s).symm (RingOfIntegers.mapRingEquiv s y) ∈ 𝔮.asIdeal
    rw [RingEquiv.symm_apply_apply]
    exact Ideal.le_of_dvd H ((hmm y).1 hx)
  · obtain ⟨a, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective α
    obtain ⟨b, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective β
    have ha : a ≠ 0 := fun h => hr.1 (by rw [h, map_zero])
    have hb : b ≠ 0 := fun h => hr.2.1 (by rw [h, map_zero])
    rw [heckeIdeal_transport s hs χ ha, heckeIdeal_transport s hs χ hb]
    refine (h _).2.2 a b ⟨ha, hb, hc _ hr.2.2.1, hc _ hr.2.2.2.1, (hmm _).1 ?_, fun φ => ?_⟩
    · rw [map_sub]; exact hr.2.2.2.2.1
    · have := hr.2.2.2.2.2 (φ.comp s.symm.toRingHom)
      change 0 < φ (s.symm (s a)) * φ (s.symm (s b)) at this
      rwa [s.symm_apply_apply, s.symm_apply_apply] at this

theorem exists_extension {L N : Type} [Field L] [NumberField L] [Field N] [NumberField N] [i : Algebra L N]
    [hab : IsAbelianGalois L N] {n : ℕ} (hn : n ≠ 0) (h : IsRay N (Ideal.span {(n : 𝓞 L)})) (s : L ≃+* L) :
    ∃ f : N →+* N, ∀ x, f (algebraMap L N x) = algebraMap L N (s x) := by
  have hb : Ideal.span {(n : 𝓞 L)} ≠ ⊥ := by simpa using hn
  have hmm : ∀ x, RingOfIntegers.mapRingEquiv s x ∈ Ideal.span {(n : 𝓞 L)} ↔ x ∈ Ideal.span {(n : 𝓞 L)} :=
    fun x => by
      rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton,
        ← map_dvd_iff (RingOfIntegers.mapRingEquiv s) (a := (n : 𝓞 L)) (b := x), map_natCast]
  let j : Algebra L N := ((@algebraMap L N _ _ i).comp s.symm.toRingHom).toAlgebra
  have hs : ∀ x, @algebraMap L N _ _ j (s x) = @algebraMap L N _ _ i x := fun x =>
    congrArg (@algebraMap L N _ _ i) (s.symm_apply_apply x)
  have hab' := @isAbelianGalois_transport L L N _ _ _ _ i j s hs _ hab
  have hm := @GlobalTheory.RayMaximal.isModulus_of_isRay L _ _ N _ _ i hab _ _ h dvd_rfl hb
  obtain ⟨f⟩ := @rayClassFieldMaximalSt_holds L N N _ _ _ _ i hab _ _ j hab' _ hb h
    (@isModulus_transport L L N _ _ _ _ _ _ i j s hs (@IsAbelianGalois.toIsGalois _ _ _ _ i hab)
      (@IsAbelianGalois.toIsGalois _ _ _ _ j hab') _ _ hb hmm hm)
  refine ⟨@AlgHom.toRingHom L N N _ _ _ j i f, fun x => ?_⟩
  rw [← hs]
  exact @AlgHom.commutes L N N _ _ _ j i f (s x)

theorem isGalois_of_isRay_nat (K : Type) {L N : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field N]
    [NumberField N] [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] [IsGalois K L]
    [IsAbelianGalois L N] {n : ℕ} (hn : n ≠ 0) (h : IsRay N (Ideal.span {(n : 𝓞 L)})) : IsGalois K N := by
  refine IsGalois.of_fixedField_eq_bot K N (eq_bot_iff.2 fun x hx => ?_)
  rw [IntermediateField.mem_fixedField_iff] at hx
  obtain ⟨y, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := L) x).2 fun σ =>
    hx (σ.restrictScalars K) trivial
  obtain ⟨z, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) y).2 fun s => by
    obtain ⟨f, hf⟩ := exists_extension hn h s.toRingEquiv
    let g : N →ₐ[K] N := { f with
      commutes' := fun k => by
        rw [IsScalarTower.algebraMap_apply K L N]
        exact (hf _).trans (congrArg _ (s.commutes k)) }
    exact (algebraMap L N).injective ((hf y).symm.trans
      (hx (AlgEquiv.ofBijective g (Algebra.IsAlgebraic.algHom_bijective g)) trivial))
  rw [← IsScalarTower.algebraMap_apply]
  exact IntermediateField.algebraMap_mem _ z

theorem isGalois_fieldRange : ∀ {K H : Type} [Field K] [NumberField K] [IsGalois ℚ K] [Field H] [NumberField H]
    [Algebra K H] [IsAbelianGalois K H] {n : ℕ}, n ≠ 0 → GlobalTheory.FieldSize.IsRay H (Ideal.span {(n : 𝓞 K)}) →
    ∀ j : H →+* ℂ, IsGalois ℚ j.toRatAlgHom.fieldRange := by
  intro K H _ _ _ _ _ _ _ n hn h j
  have : IsGalois ℚ H := isGalois_of_isRay_nat ℚ hn h
  exact IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField j.toRatAlgHom)

end GlobalTheory.RayNatGalois

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsJumpVIffOfExactCrystallineLatticesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isJumpV_iff_of_exact_crystalline_lattices : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsSESLat (Qp := ℚ_[l]) ι π → IsCrys (P.PD K) T₀.ρ → IsCrys (P.PD K) T₁.ρ → IsCrys (P.PD K) T₂.ρ → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV (P.PD K) T₁.ρ τ a ↔ IsJumpV (P.PD K) T₀.ρ τ a ∨ IsJumpV (P.PD K) T₂.ρ τ a := by
  first | exact @GlobalTheory.Per.SESJumps.isJumpV_iff_of_isSESLat | exact GlobalTheory.Per.SESJumps.isJumpV_iff_of_isSESLat | (intros; apply GlobalTheory.Per.SESJumps.isJumpV_iff_of_isSESLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LadicDescentStepToOEStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ladic_descent_step_to_OE : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (κ : Type) [Fintype κ] (x b : κ → WCb l) (c : κ → κ → WCb l), (∀ i j, c i j ∈ bk.OE) → (∀ j, b j ∈ bk.OE) → (∀ j, x j = ∑ i, frobW l (x i) * c i j + b j) → (∀ g : ↥(GK K), bk.FixFlat g → ∀ j, galW l (g : GQ l) (x j) = x j) → ∃ v x' b' : κ → WCb l, (∀ j, v j ∈ bk.OE) ∧ (∀ j, b' j ∈ bk.OE) ∧ (∀ j, x j = v j + ((l : ℕ) : WCb l) * x' j) ∧ (∀ j, x' j = ∑ i, frobW l (x' i) * c i j + b' j) ∧ ∀ g : ↥(GK K), bk.FixFlat g → ∀ j, galW l (g : GQ l) (x' j) = x' j := by
  first | exact @GlobalTheory.BSP.BK.descent_step | exact GlobalTheory.BSP.BK.descent_step | (intros; apply GlobalTheory.BSP.BK.descent_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinkNAlongFamilyOfLocalBounds
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.LinkFam

theorem main : ∀ {eps : ℝ} (Fm : FamP eps), ConclF Fm → Formalism.MainNotions.LinkN Fm := by
  intro eps Fm hC
  obtain ⟨C, x0, h⟩ := hC
  have hA : Formalism.MainNotions.TwistedPlaces.AdmF Fm := ⟨C, x0, fun x hx hx1 i hS => by
    obtain ⟨X, hX⟩ := h x hx hx1 i hS
    exact GlobalTheory.T.admittedStatements_of_localBoundsConclusion_alt _ _ _ X C hX⟩
  exact Formalism.MainNotions.N.linkN_of Fm hA (Formalism.MainNotions.TwistedPlaces.stmtF_holds Fm)

end GlobalTheory.LinkFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCocyclesMemSpanPushoutSummandLatticeStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCocycles_mem_span_pushout_summandLattice : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))),
    GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M)
      (F : Finset (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)),
      (F : Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)) ⊆ cutCoc i w hw r Xs M →
      ∃ X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw),
        IsSummandTw i w hw r Xs X ∧
        Submodule.span (Br.OLL D.nbr i w hw) (F : Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)) ≤
          BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) X (locU i w hw M hSub.1) (Br.locLat D.nbr i w hw M) := by
  first | exact @GlobalTheory.Pass.LocDual.OneX.main | exact GlobalTheory.Pass.LocDual.OneX.main | (intros; apply GlobalTheory.Pass.LocDual.OneX.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateEndomorphismUniqueStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.AinfK GroundTheory.LocalField.FormalGroup GlobalTheory.AcrisK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_endomorphism_unique : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) [Finite (IsLocalRing.ResidueField ↥(OL K))] (π : ↥(OL K)) (hπ : Irreducible π),
    ∃ hf : IsLubinTateSeries π (ltSeries K π),
      ∀ (a : ↥(OL K)) (φ : PowerSeries ↥(OL K)), IsLTEndo K π a φ ↔ φ = (lubinTateHom hπ hf hf a).toPowerSeries := by
  first | exact @GlobalTheory.PZ.isLTEndo_iff_eq_lubinTateHom | exact GlobalTheory.PZ.isLTEndo_iff_eq_lubinTateHom | (intros; apply GlobalTheory.PZ.isLTEndo_iff_eq_lubinTateHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateLogNeZeroStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.AinfK GroundTheory.LocalField.FormalGroup GlobalTheory.AcrisK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_log_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (hπ : Irreducible π) (f : PowerSeries ↥(OL K))
    (hf : IsLubinTateSeries π f) (x : AK K) (hx : thetaK K x = 0), x ∉ RingHom.ker (thetaK K) ^ 2 → ltLog hπ hf x hx ≠ 0 := by
  first | exact @GlobalTheory.LogFirstOrder.ltLog_ne_zero | exact GlobalTheory.LogFirstOrder.ltLog_ne_zero | (intros; apply GlobalTheory.LogFirstOrder.ltLog_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTatePeriodGaloisExpansionStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.AinfK GroundTheory.LocalField.FormalGroup GlobalTheory.AcrisK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_period_galois_expansion : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l), LTData K χ π z →
    ∃ ω : AK K, ω ≠ 0 ∧ thetaK K ω = 0 ∧ frobq K ω = inO K π * ω + ω ^ resCard K ∧
      ∀ (g : ↥(GK K)) (a : ↥(OL K)) (φ : PowerSeries ↥(OL K)), (a : ↥K.1) = (χ g : ↥K.1) → IsLTEndo K π a φ →
        ∀ n : ℕ, gal K g ω - ∑ j ∈ Finset.range n, inO K (PowerSeries.coeff j φ) * ω ^ j ∈ RingHom.ker (thetaK K) ^ n := by
  first | exact @GlobalTheory.LTOmega.main | exact GlobalTheory.LTOmega.main | (intros; apply GlobalTheory.LTOmega.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapDcrisEqDdRCrystallineUnramifiedStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_Dcris_eq_DdR_crystalline_unramified : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), Function.Bijective (algebraMap ↥(K0 K) ↥K.1) → ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → (Dcris (P.PD K) ρ).map (ιV (P.PD K) (LL := ↥LL.1) (V := V)) = DdR (P.PD K) ρ ∧ ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ∧ finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) = finrank ↥LL.1 V ∧ ∀ a : ℤ, FildR (P.PD K) ρ τ a = (FilCris (P.PD K) ρ a ⊓ DcrisL (P.PD K) ρ (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1))).map (ιV (P.PD K) (LL := ↥LL.1) (V := V)) := by
  first | exact @GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR | exact GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR | (intros; apply GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR <;> assumption)
end

