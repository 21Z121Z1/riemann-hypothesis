import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0268
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0209
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0265

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TransLoc

section General

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_smul_mem_of_mem_span (N : Submodule (𝓞 K) V) {x : V} (hx : x ∈ Submodule.span K (N : Set V)) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ a • x ∈ N := by
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K (N : Set V) x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.ne_zero t.2, ht⟩

theorem exists_smul_le_of_fg (N N' : Submodule (𝓞 K) V) (hfg : N'.FG)
    (h : ∀ x ∈ N', x ∈ Submodule.span K (N : Set V)) : ∃ a : 𝓞 K, a ≠ 0 ∧ ∀ x ∈ N', a • x ∈ N := by
  classical
  obtain ⟨s, rfl⟩ := hfg
  have h1 : ∀ y : s, ∃ a : 𝓞 K, a ≠ 0 ∧ a • (y : V) ∈ N := fun y =>
    exists_smul_mem_of_mem_span N (h y (Submodule.subset_span y.2))
  choose a ha0 ha using h1
  refine ⟨∏ y, a y, Finset.prod_ne_zero_iff.mpr fun y _ => ha0 y, ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨y, hy⟩ : s)), mul_smul]
    exact N.smul_mem _ (ha ⟨y, hy⟩)
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact N.add_mem hy hz
  | smul c y _ hy => rw [smul_comm]; exact N.smul_mem _ hy

omit [Module K V] [IsScalarTower (𝓞 K) K V] in

theorem mem_of_forall_locP (N : Submodule (𝓞 K) V) {x : V}
    (h : ∀ w : HeightOneSpectrum (𝓞 K), x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N) : x ∈ N := by
  by_contra hx
  have hI : N.comap (LinearMap.toSpanSingleton (𝓞 K) V x) ≠ ⊤ := by
    intro h1
    have : (1 : 𝓞 K) ∈ N.comap (LinearMap.toSpanSingleton (𝓞 K) V x) := h1 ▸ Submodule.mem_top
    exact hx (by simpa using this)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hI
  have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)
  obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime, hm0⟩
  exact hs (hle (by simpa using hsx))

omit [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem localization_le_of_smul_mem (w : HeightOneSpectrum (𝓞 K)) {N N' : Submodule (𝓞 K) V} {a : 𝓞 K} (ha : a ∉ w.asIdeal)
    (h : ∀ x ∈ N', a • x ∈ N) : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N' ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal N := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨a * s, Submonoid.mul_mem _ ha hs, by rw [mul_smul]; exact h _ hx⟩

theorem exists_dvd_mul {w w' : HeightOneSpectrum (𝓞 K)} (hw : w' ≠ w) {d : 𝓞 K} (hd : d ≠ 0) :
    ∃ s ∉ w.asIdeal, ∃ u ∉ w'.asIdeal, d ∣ u * s := by
  classical
  have hI : Ideal.span {d} ≠ ⊥ := by simpa using hd
  obtain ⟨Q, hQ, hdQ⟩ := Ideal.eq_prime_pow_mul_coprime hI w'.asIdeal (hpm := w'.isMaximal)
  set k := Multiset.count w'.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {d}))
  have h1 : ¬ w'.asIdeal ^ k ≤ w.asIdeal := by
    intro h
    have h2 := Ideal.IsPrime.le_of_pow_le (hP := w.isPrime) h
    exact hw (HeightOneSpectrum.ext (w'.isMaximal.eq_of_le w.isPrime.ne_top h2))
  have h2 : ¬ Q ≤ w'.asIdeal := by
    intro h
    rw [sup_eq_left.mpr h] at hQ
    exact w'.isPrime.ne_top hQ
  obtain ⟨s, hs, hs'⟩ := SetLike.not_le_iff_exists.mp h1
  obtain ⟨u, hu, hu'⟩ := SetLike.not_le_iff_exists.mp h2
  refine ⟨s, hs', u, hu', ?_⟩
  rw [← Ideal.mem_span_singleton, hdQ, mul_comm u]
  exact Ideal.mul_mem_mul hs hu

end General

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

theorem span_colLat_one : Submodule.span K (colLat (1 : GL (Fin n) K) : Set (Fin n → K)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun K (Fin n)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨j, rfl⟩
  refine Submodule.subset_span ⟨j, ?_⟩
  funext a
  simp [Matrix.one_apply, Pi.single_apply]

theorem exists_isBasisAt_one (M : Submodule (𝓞 K) (Fin n → K)) (hM : Submodule.IsLattice K M) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 K), a ∉ w.asIdeal → IsBasisAt w M 1 := by
  obtain ⟨a, ha0, ha⟩ := exists_smul_le_of_fg (colLat (1 : GL (Fin n) K)) M hM.fg
    (fun x _ => by rw [span_colLat_one]; trivial)
  obtain ⟨b, hb0, hb⟩ := exists_smul_le_of_fg M (colLat (1 : GL (Fin n) K))
    (Submodule.fg_span (Set.finite_range _)) (fun x _ => by rw [hM.span_eq_top]; trivial)
  refine ⟨a * b, mul_ne_zero ha0 hb0, fun w hw => le_antisymm ?_ ?_⟩
  · exact localization_le_of_smul_mem w (fun h => hw (w.asIdeal.mul_mem_right _ h)) ha
  · exact localization_le_of_smul_mem w (fun h => hw (w.asIdeal.mul_mem_left _ h)) hb

theorem polyAction_smul_int (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (a : 𝓞 K) (F : Pol K ι n) :
    actP lam g (a • F) = a • actP lam g F :=
  ((actP lam g).restrictScalars (𝓞 K)).map_smul a F

theorem mem_VV_of_locP (lam : ι → DomWeight n) {T : Submodule (𝓞 K) (Pol K ι n)}
    (hT : Submodule.span K (T : Set (Pol K ι n)) = VV K lam) (w : HeightOneSpectrum (𝓞 K))
    (B : ι → GL (Fin n) K) {F : Pol K ι n} (hF : actP lam B⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T) : F ∈ VV K lam := by
  obtain ⟨s, hs, hx⟩ := hF
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
    rintro rfl
    exact hs w.asIdeal.zero_mem
  have h1 : algebraMap (𝓞 K) K s • actP lam B⁻¹ F ∈ VV K lam := by
    rw [algebraMap_smul, ← hT]
    exact Submodule.subset_span hx
  have h2 := polyAction_mem_VV lam B (((VV K lam).smul_mem_iff hs0).mp h1)
  rwa [← polyAction_mul, mul_inv_cancel, polyAction_one₂] at h2

theorem mem_map_actP (lam : ι → DomWeight n) (B : ι → GL (Fin n) K) (N : Submodule (𝓞 K) (Pol K ι n))
    (F : Pol K ι n) : F ∈ N.map ((actP lam B).restrictScalars (𝓞 K)) ↔ actP lam B⁻¹ F ∈ N := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    show actP lam B⁻¹ (actP lam B y) ∈ _
    rw [← polyAction_mul, inv_mul_cancel, polyAction_one₂]
    exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    show actP lam B (actP lam B⁻¹ F) = F
    rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂]

theorem mem_transLat (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n))
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (F : Pol K ι n) :
    F ∈ transLat lam T M ↔ ∀ (w : HeightOneSpectrum (𝓞 K)) (B : ι → GL (Fin n) K),
      (∀ τ, IsBasisAt w (M τ) (B τ)) → actP lam B⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T := by
  simp only [transLat, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]

theorem transLat_colLat (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n)) (B : ι → GL (Fin n) K)
    (hI : ∀ (w : HeightOneSpectrum (𝓞 K)) (B' : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (colLat (B τ)) (B' τ)) →
      ∀ F : Pol K ι n, actP lam B⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T → actP lam B'⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T) :
    transLat lam T (fun τ => colLat (B τ)) = T.map ((actP lam B).restrictScalars (𝓞 K)) := by
  ext F
  rw [mem_map_actP, mem_transLat]
  constructor
  · intro h
    exact mem_of_forall_locP T fun w => h w B fun _ => rfl
  · intro h w B' hB'
    exact hI w B' hB' F ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact h⟩

theorem locP_transLat (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n))
    (hT : Submodule.span K (T : Set (Pol K ι n)) = VV K lam)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ))
    (hI : ∀ (w : HeightOneSpectrum (𝓞 K)) (B B' : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (M τ) (B τ)) →
      (∀ τ, IsBasisAt w (M τ) (B' τ)) → ∀ F : Pol K ι n,
      (actP lam B⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T ↔ actP lam B'⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T))
    (w : HeightOneSpectrum (𝓞 K)) (B : ι → GL (Fin n) K) (hB : ∀ τ, IsBasisAt w (M τ) (B τ)) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (transLat lam T M) =
      (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T).map ((actP lam B).restrictScalars (𝓞 K)) := by
  classical
  ext F
  rw [mem_map_actP]
  constructor
  · rintro ⟨s, hs, hF⟩
    obtain ⟨t, ht, h⟩ := (mem_transLat lam T M _).mp hF w B hB
    refine ⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩
    rw [mul_smul]
    exact (congrArg (fun x => t • x ∈ T) (polyAction_smul_int lam B⁻¹ s F)).mp h
  · intro hF
    have hV : F ∈ VV K lam := mem_VV_of_locP lam hT w B hF
    have hd : ∀ g : ι → GL (Fin n) K, ∃ d : 𝓞 K, d ≠ 0 ∧ d • actP lam g F ∈ T := fun g =>
      exists_smul_mem_of_mem_span T (hT ▸ polyAction_mem_VV lam g hV)
    choose a ha0 ha using fun τ => exists_isBasisAt_one (M τ) (hM τ)
    obtain ⟨d, hd0, hdF⟩ := hd (1 : ι → GL (Fin n) K)⁻¹
    have hc0 : Ideal.span {d * ∏ τ, a τ} ≠ 0 := by
      simpa using mul_ne_zero hd0 (Finset.prod_ne_zero_iff.mpr fun τ _ => ha0 τ)
    have hfin := Ideal.finite_factors hc0
    have hloc : ∀ w' : HeightOneSpectrum (𝓞 K), ∃ s ∉ w.asIdeal, ∀ B' : ι → GL (Fin n) K,
        (∀ τ, IsBasisAt w' (M τ) (B' τ)) → s • actP lam B'⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w'.asIdeal T := by
      intro w'
      by_cases hw : w' = w
      · subst hw
        refine ⟨1, (Ideal.ne_top_iff_one _).mp w'.isPrime.ne_top, fun B' hB' => ?_⟩
        exact Submodule.smul_mem _ _ ((hI w' B B' hB hB' F).mp hF)
      by_cases hex : ∃ B₀ : ι → GL (Fin n) K, ∀ τ, IsBasisAt w' (M τ) (B₀ τ)
      · obtain ⟨B₀, hB₀⟩ := hex
        obtain ⟨e, he0, heF⟩ := hd B₀⁻¹
        obtain ⟨s, hs, u, hu, c, hc⟩ := exists_dvd_mul hw he0
        refine ⟨s, hs, fun B' hB' => ?_⟩
        rw [← polyAction_smul_int]
        refine (hI w' B₀ B' hB₀ hB' _).mp ⟨u, hu, ?_⟩
        erw [polyAction_smul_int, ← mul_smul, hc, mul_comm, mul_smul]
        exact T.smul_mem _ heF
      · exact ⟨1, (Ideal.ne_top_iff_one _).mp w.isPrime.ne_top, fun B' hB' => absurd ⟨B', hB'⟩ hex⟩
    choose s hs hsF using hloc
    refine ⟨∏ w' ∈ hfin.toFinset, s w', Submonoid.prod_mem _ fun w' _ => hs w', ?_⟩
    rw [mem_transLat]
    intro w' B' hB'
    erw [polyAction_smul_int]
    by_cases hw' : w' ∈ hfin.toFinset
    · erw [← Finset.prod_erase_mul _ _ hw', mul_smul]
      exact Submodule.smul_mem _ _ (hsF w' B' hB')
    · refine Submodule.smul_mem _ _ ?_
      have hn : d * ∏ τ, a τ ∉ w'.asIdeal := by
        simpa [Ideal.dvd_span_singleton] using hw'
      have h1 : ∀ τ, IsBasisAt w' (M τ) ((1 : ι → GL (Fin n) K) τ) := fun τ =>
        ha τ w' fun h => hn (w'.asIdeal.mul_mem_left _
          (w'.asIdeal.mem_of_dvd (Finset.dvd_prod_of_mem a (Finset.mem_univ τ)) h))
      exact (hI w' 1 B' h1 hB' F).mp ⟨d, fun h => hn (w'.asIdeal.mul_mem_right _ h), hdF⟩

theorem nabDelLoc_free_leVV : NabDelLoc ∧ NabDelFree ∧ NabLeVV := by
  refine ⟨?_, ?_, ?_⟩
  · intro K _ _ ι _ n lam M hM w B hB
    exact ⟨locP_transLat lam _ (GlobalTheory.StdLatSpan.std_fg_span K ι n lam).2.2.1 M hM
        (fun w B B' => GlobalTheory.T.nabIndep_and_delIndep_local_conditions.1 K ι n lam w M B B') w B hB,
      locP_transLat lam _ (GlobalTheory.StdLatSpan.std_fg_span K ι n lam).2.2.2 M hM
        (fun w B B' => GlobalTheory.T.nabIndep_and_delIndep_local_conditions.2 K ι n lam w M B B') w B hB⟩
  · intro K _ _ ι _ n lam B
    exact ⟨transLat_colLat lam _ B fun w B' hB' F =>
        (GlobalTheory.T.nabIndep_and_delIndep_local_conditions.1 K ι n lam w _ B B' (fun _ => rfl) hB' F).mp,
      transLat_colLat lam _ B fun w B' hB' F =>
        (GlobalTheory.T.nabIndep_and_delIndep_local_conditions.2 K ι n lam w _ B B' (fun _ => rfl) hB' F).mp⟩
  · intro K _ _ ι _ n lam M hM F hF
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 K)
    have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)
    let w : HeightOneSpectrum (𝓞 K) := ⟨m, hm.isPrime, hm0⟩
    choose B hB using fun τ => GlobalTheory.LatBasisAt.basisAtEx K n (M τ) (hM τ) w
    exact mem_VV_of_locP lam (GlobalTheory.StdLatSpan.std_fg_span K ι n lam).2.2.1 w B ((mem_transLat lam _ M F).mp hF w B hB)

end GlobalTheory.TransLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeierstrassPFormalGroupLogUniformises
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.WpForm

open PowerSeries

theorem exists_subst_inverse {R : Type*} [CommRing R] (l : PowerSeries R)
    (h0 : constantCoeff l = 0) (h1 : coeff 1 l = 1) :
    ∃ ex : PowerSeries R, constantCoeff ex = 0 ∧
      subst ex l = (X : PowerSeries R) ∧ subst l ex = (X : PowerSeries R) := by
  have hA : GlobalTheory.FormalInv.linearPart (fun _ : Unit => (l : MvPowerSeries Unit R)) = 1 := by
    ext i j
    exact h1
  obtain ⟨v, hv, h, h'⟩ := (GlobalTheory.FormalInv.exists_substInv_iff
    (u := fun _ : Unit => (l : MvPowerSeries Unit R)) (fun _ => h0)).2 (hA ▸ isUnit_one)
  exact ⟨v (), hv (), h (), h' ()⟩

theorem subst_eq_of_equation {K : Type} [Field K] [CharZero K] {a b : K}
    {P m q M : PowerSeries K} (hP : IsWpSer a b P) (hm : constantCoeff m = 1)
    (hq : constantCoeff q = 1)
    (hd : X * derivative K q - 2 * q = derivative K (X * m) * M)
    (hM : M ^ 2 = 4 * q ^ 3 - C a * X ^ 4 * q - C b * X ^ 6) :
    (subst (X * m : PowerSeries K) P : PowerSeries K) = m ^ 2 * q := by
  set l : PowerSeries K := X * m with hl
  have h0 : constantCoeff l = 0 := by simp [hl]
  have h1 : coeff 1 l = 1 := by
    rw [hl, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul]; simpa using hm
  obtain ⟨ex, he0, he1, he2⟩ := exists_subst_inverse l h0 h1
  have sl : HasSubst l := HasSubst.of_constantCoeff_zero' h0
  have se : HasSubst ex := HasSubst.of_constantCoeff_zero' he0
  have hle : ∀ f : PowerSeries K, (subst l (subst ex f : PowerSeries K) : PowerSeries K) = f := by
    intro f
    rw [subst_comp_subst_apply se sl, he2]
    exact congrFun MvPowerSeries.subst_self f
  have hel : ∀ f : PowerSeries K, (subst ex (subst l f : PowerSeries K) : PowerSeries K) = f := by
    intro f
    rw [subst_comp_subst_apply sl se, he1]
    exact congrFun MvPowerSeries.subst_self f
  set Q : PowerSeries K := subst ex (m ^ 2 * q) with hQ
  have hQl : (subst l Q : PowerSeries K) = m ^ 2 * q := hle _
  have hw : derivative K l = m + X * derivative K m := by
    rw [hl, Derivation.leibniz]; simp [add_comm]
  have hw0 : derivative K l ≠ 0 := by
    intro h
    have := congrArg constantCoeff (hw.symm.trans h)
    simp [hm] at this
  have hch := derivative_subst (f := Q) sl
  rw [hQl, Derivation.leibniz, Derivation.leibniz_pow] at hch
  simp only [smul_eq_mul, nsmul_eq_mul] at hch
  have key : l * (subst l (derivative K Q) : PowerSeries K) - 2 * (m ^ 2 * q) = m ^ 3 * M := by
    apply mul_right_cancel₀ hw0
    have hch' : m ^ 2 * derivative K q + q * (2 * (m * derivative K m)) =
        (subst l (derivative K Q) : PowerSeries K) * derivative K l := by simpa using hch
    linear_combination -l * hch' + m ^ 3 * hd - 2 * m ^ 2 * q * hw +
      (m ^ 2 * derivative K q + q * (2 * (m * derivative K m))) * hl
  have hQW : IsWpSer a b Q := by
    constructor
    · have h2 : ∀ f : PowerSeries K, constantCoeff (subst ex f : PowerSeries K) = constantCoeff f := by
        intro f
        have hf := eq_X_mul_shift_add_const f
        conv_lhs => rw [hf]
        rw [← coe_substAlgHom se, map_add, map_mul, substAlgHom_X, map_add, map_mul, he0,
          C_eq_algebraMap, AlgHom.commutes]
        simp
      rw [hQ, h2]; simp [hm, hq]
    · rw [← hel (_ ^ 2), ← hel (_ - C b * X ^ 6)]
      congr 1
      have hD : derivativeFun Q = derivative K Q := rfl
      rw [hD, ← coe_substAlgHom sl]
      simp only [map_pow, map_sub, map_mul, map_ofNat, substAlgHom_X, C_eq_algebraMap,
        AlgHom.commutes]
      rw [coe_substAlgHom sl, hQl]
      simp only [C_eq_algebraMap] at hM
      change (l * _ - _) ^ 2 = _ - algebraMap K (PowerSeries K) a * l ^ 4 * _ -
        algebraMap K (PowerSeries K) b * l ^ 6
      rw [key, hl]
      linear_combination m ^ 6 * hM
  rw [(GlobalTheory.WpSeries.existsUnique_isWpSer K a b).unique hP hQW, hQl]

theorem dX_eq_derivative {K : Type*} [CommRing K] (f : PowerSeries K) : dX f = derivative K f := by
  ext n
  simp [dX, coeff_derivative, mul_comm]

theorem derivative_flog {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p])
    (wq : PowerSeries ℂ_[p]) : derivative ℂ_[p] (flog W wq) = omegaW W wq := by
  ext n
  have : ((n : ℂ_[p]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp [flog, coeff_derivative, this]

theorem wp_flog : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq P : PowerSeries ℂ_[p]), IsWq W wq → IsWpSer (W.c₄ / 12) (W.c₆ / 216) P → PowerSeries.X ^ 2 * (PowerSeries.subst (flog W wq) P : PowerSeries ℂ_[p]) = flog W wq ^ 2 * lineSer wq⁻¹ (-(W.b₂ / 12)) := by
  intro p _ W wq P hwq hP
  have hw1 := GlobalTheory.GenusOneDatum.constantCoeff_of_isWq hwq
  obtain ⟨m, hm⟩ := X_dvd_iff.2 (GlobalTheory.GenusOneDatum.constantCoeff_flog W wq)
  have hm1 : constantCoeff m = 1 := by
    have := GlobalTheory.GenusOneDatum.coeff_one_flog hwq
    rw [hm, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul] at this
    simpa using this
  have he : wq * wq⁻¹ = 1 := PowerSeries.mul_inv_cancel wq (by rw [hw1]; exact one_ne_zero)
  have he1 : constantCoeff wq⁻¹ = 1 := by simp [PowerSeries.constantCoeff_inv, hw1]
  set e := wq⁻¹ with hedef
  set N : PowerSeries ℂ_[p] := C W.a₁ * X + C W.a₃ * X ^ 3 * wq - 2 with hN
  have h2 : constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
  have hω : omegaW W wq * (wq * N) = -2 * wq - X * derivative ℂ_[p] wq := by
    have hu : (wq * N)⁻¹ * (wq * N) = 1 :=
      PowerSeries.inv_mul_cancel _ (by simp [hN, hw1, h2])
    have : omegaW W wq = (-2 * wq - X * derivative ℂ_[p] wq) * (wq * N)⁻¹ := by
      rw [← dX_eq_derivative]; rfl
    rw [this, mul_assoc, hu, mul_one]
  have hde : wq * derivative ℂ_[p] e + e * derivative ℂ_[p] wq = 0 := by
    have := congrArg (derivative ℂ_[p]) he
    rw [Derivation.leibniz] at this
    simpa using this
  set r := W.b₂ / 12 with hr
  have hq : lineSer e (-r) = e + C r * X ^ 2 := by simp [lineSer]
  have hdq : derivative ℂ_[p] (e + C r * X ^ 2) = derivative ℂ_[p] e + C r * (2 * X) := by
    rw [map_add, Derivation.leibniz, Derivation.leibniz_pow]; simp
  have hW : wq = 1 + C W.a₁ * X * wq + C W.a₂ * X ^ 2 * wq + C W.a₃ * X ^ 3 * wq ^ 2 +
    C W.a₄ * X ^ 4 * wq ^ 2 + C W.a₆ * X ^ 6 * wq ^ 3 := hwq
  have hW' : e ^ 2 = e ^ 3 + C W.a₁ * X * e ^ 2 + C W.a₂ * X ^ 2 * e ^ 2 + C W.a₃ * X ^ 3 * e +
      C W.a₄ * X ^ 4 * e + C W.a₆ * X ^ 6 := by
    linear_combination e ^ 3 * hW + (-e ^ 2 + C W.a₁ * X * e ^ 2 + C W.a₂ * X ^ 2 * e ^ 2 +
      (C W.a₃ * X ^ 3 + C W.a₄ * X ^ 4) * e * (wq * e + 1) +
      C W.a₆ * X ^ 6 * ((wq * e) ^ 2 + wq * e + 1)) * he
  have hNe : N * e = C W.a₁ * X * e + C W.a₃ * X ^ 3 - 2 * e := by
    rw [hN]; linear_combination C W.a₃ * X ^ 3 * he
  have c2 : (12 : PowerSeries ℂ_[p]) * C r = C W.a₁ ^ 2 + 4 * C W.a₂ := by
    have : 12 * r = W.a₁ ^ 2 + 4 * W.a₂ := by rw [hr, WeierstrassCurve.b₂]; ring
    simpa only [map_mul, map_add, map_pow, map_ofNat] using congrArg (C (R := ℂ_[p])) this
  have c4 : (C (W.c₄ / 12) : PowerSeries ℂ_[p]) =
      12 * C r ^ 2 - 2 * (2 * C W.a₄ + C W.a₁ * C W.a₃) := by
    have : W.c₄ / 12 = 12 * r ^ 2 - 2 * (2 * W.a₄ + W.a₁ * W.a₃) := by
      rw [hr, WeierstrassCurve.c₄, WeierstrassCurve.b₄]; ring
    rw [this]; simp only [map_mul, map_add, map_sub, map_pow, map_ofNat]
  have c6 : (C (W.c₆ / 216) : PowerSeries ℂ_[p]) =
      2 * C r * (2 * C W.a₄ + C W.a₁ * C W.a₃) - 8 * C r ^ 3 - (C W.a₃ ^ 2 + 4 * C W.a₆) := by
    have : W.c₆ / 216 = 2 * r * (2 * W.a₄ + W.a₁ * W.a₃) - 8 * r ^ 3 - (W.a₃ ^ 2 + 4 * W.a₆) := by
      rw [hr, WeierstrassCurve.c₆, WeierstrassCurve.b₄, WeierstrassCurve.b₆]; ring
    rw [this]; simp only [map_mul, map_add, map_sub, map_pow, map_ofNat]
  have main := subst_eq_of_equation (m := m) (q := e + C r * X ^ 2) (M := N * e) hP hm1
    (by simp [he1])
    (by
      rw [← hm, derivative_flog, hdq]
      linear_combination -e ^ 2 * hω + X * e * hde +
        (omegaW W wq * N * e + 2 * e - X * derivative ℂ_[p] e) * he)
    (by
      rw [hNe, c4, c6]
      linear_combination 4 * hW' - X ^ 2 * e ^ 2 * c2)
  rw [hq, hm, main]
  ring

end GlobalTheory.WpForm
end
end

