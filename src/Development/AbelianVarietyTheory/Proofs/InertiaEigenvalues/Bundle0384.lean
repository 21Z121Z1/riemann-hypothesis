import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0085
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0261
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0285
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0292
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsGenIsUnitSub
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0357
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0366

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTeichmullerLogUnitBcris
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.LogU
open GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem isLogJ_pow {e : Per.Fl l} (hJ : InJ (Per.tm e - 1)) {y : Per.Acris l} (hy : IsLogJ (Per.tm e - 1) y) :
    ∀ m : ℕ, IsLogJ (Per.tm (e ^ m) - 1) ((m : Per.Acris l) * y)
  | 0 => by simpa using (isLogJ_zero : IsLogJ (l := l) 0 0)
  | m + 1 => by
    have h := GlobalTheory.T.isAcrisLogOneAdd_add_of_mul l _ _ _ _ (inJ_pow hJ m) hJ (isLogJ_pow hJ hy m) hy
    have e1 : Per.tm (e ^ (m + 1)) - 1 = (Per.tm (e ^ m) - 1) + (Per.tm e - 1) +
        (Per.tm (e ^ m) - 1) * (Per.tm e - 1) := by
      rw [pow_succ, show Per.tm (e ^ m * e) = Per.tm (e ^ m) * Per.tm e from
        map_mul (WittVector.teichmuller l) _ _]
      ring
    rw [e1]
    convert h using 1
    push_cast
    ring

theorem iter_mul (a b : Per.Fl l) (m : ℕ) : ((frobeniusEquiv (Per.Fl l) l).symm)^[m] (a * b) =
    ((frobeniusEquiv (Per.Fl l) l).symm)^[m] a * ((frobeniusEquiv (Per.Fl l) l).symm)^[m] b := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul]

theorem iter_one (m : ℕ) : ((frobeniusEquiv (Per.Fl l) l).symm)^[m] 1 = 1 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, map_one]

theorem rootT_mul (a b : Per.Fl l) (m : ℕ) : rootT (a * b) m = rootT a m * rootT b m := by
  simp only [rootT, iter_mul, map_mul]

theorem rootT_one (m : ℕ) : rootT (1 : Per.Fl l) m = 1 := by
  simp only [rootT, iter_one, map_one]

theorem exists_gal_log (C : Core l) (x : Per.Fl l) (hx : IsUnit x) (g : GQ l) (c : ℤ_[l])
    (H : ∀ m, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT x m) :
    ∃ e : Per.Fl l, e.untilt = 1 ∧ Per.σF g x = x * e ∧
      IsLogA e (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l c) * C.t) := by
  obtain ⟨v, hv⟩ := hx.exists_left_inv
  have hxe : Per.σF g x = x * (v * Per.σF g x) := by rw [← mul_assoc, mul_comm x v, hv, one_mul]
  have hre : ∀ m, rootT (v * Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val := by
    intro m
    have hu : IsUnit (rootT x m) := by
      have h1 := congrArg (fun z => rootT z m) hv
      simp only [rootT_mul, rootT_one] at h1
      exact ⟨⟨rootT x m, rootT v m, by rw [mul_comm]; exact h1, h1⟩, rfl⟩
    apply hu.mul_left_cancel
    rw [← rootT_mul, ← hxe, H m, mul_comm]
  have he1 : (v * Per.σF g x).untilt = 1 := by
    have := hre 0
    simp only [rootT, Function.iterate_zero, id] at this
    rw [this, TAct.eps_untilt C, one_pow]
  have hr : ∀ m, (rootT (v * Per.σF g x) m : ℂ_[l]) =
      algebraMap (Om l) ℂ_[l] (C.ζ m ^ (PadicInt.toZModPow m c).val) := by
    intro m
    rw [hre m, SubmonoidClass.coe_pow, C.ε_root m, map_pow]
  obtain ⟨y, hy⟩ := Model.exists_isLogA he1
  exact ⟨_, he1, hxe, GlobalTheory.Pst.NoLog.log_eq C _ c y hr hy ▸ hy⟩

theorem map_inv_units {R : Type} [CommRing R] (f : R →+* R) (u : Rˣ) (h : f u = u) :
    f (↑u⁻¹ : R) = ↑u⁻¹ := by
  have h1 := congrArg f (Units.inv_mul u)
  rw [map_mul, h, map_one] at h1
  calc f (↑u⁻¹ : R) = f ↑u⁻¹ * (↑u * ↑u⁻¹) := by rw [Units.mul_inv, mul_one]
    _ = ↑u⁻¹ := by rw [← mul_assoc, h1, one_mul]

theorem exists_log_unit : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (x : OCb l), IsUnit x → ∃ b : Per.Bcris l, Per.φB l b = (l : Per.Bcris l) * b ∧ ∀ (g : GQ l) (c : ℤ_[l]), (∀ m, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT x m) → Per.σB g b = b + Per.zB l c * C.tB := by
  intro l _ C x hx
  obtain ⟨ω, x₁, N, hxω, hJ, hω⟩ := GlobalTheory.T.tilt_unit_teichmuller_principal_unit_split l x hx
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_acris_log_one_add l _ hJ
  have hpow := isLogJ_pow hJ hy
  obtain ⟨u, hu⟩ := (isUnit_l_Bcris l).pow N
  have hωu : IsUnit ω := isUnit_of_mul_isUnit_left (hxω ▸ hx)
  refine ⟨↑u⁻¹ * algebraMap (Per.Acris l) (Per.Bcris l) y, ?_, fun g c H => ?_⟩
  · have h2 := isLogJ_extends (GlobalTheory.CrisMaps.phiA_extends l) hy
    have h3 : Per.φA l (Per.tm (x₁ ^ l ^ N) - 1) = Per.tm ((x₁ ^ l ^ N) ^ l) - 1 := by
      rw [map_sub, map_one, show Per.φA l (Per.tm (x₁ ^ l ^ N)) = Per.tm ((x₁ ^ l ^ N) ^ l) from
        GlobalTheory.RingIface.phiA_teich l _]
    rw [h3] at h2
    have h1 : GlobalTheory.MemLoc.phiA l y = (l : Per.Acris l) * y := isLogJ_unique h2 (hpow l)
    have hφY : Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) y) =
        (l : Per.Bcris l) * algebraMap (Per.Acris l) (Per.Bcris l) y := by
      have : Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) y) =
          algebraMap _ _ (GlobalTheory.MemLoc.phiA l y) :=
        GlobalTheory.CrisMaps.φB_phiA l y
      rw [this, h1, map_mul, map_natCast]
    have hφu : Per.φB l (↑u⁻¹ : Per.Bcris l) = ↑u⁻¹ :=
      map_inv_units _ u (by rw [hu, map_pow, map_natCast])
    rw [map_mul, hφu, hφY]
    ring
  · obtain ⟨e, he1, hgx, hle⟩ := exists_gal_log C x hx g c H
    have hgω : Per.σF g ω = ω := hω g e he1 hgx
    have hgx₁ : Per.σF g x₁ = x₁ * e := by
      apply hωu.mul_left_cancel
      rw [← mul_assoc, ← hxω, ← hgx, hxω, map_mul, hgω]
    have hge₁ : Per.σF g (x₁ ^ l ^ N) = x₁ ^ l ^ N * e ^ l ^ N := by rw [map_pow, hgx₁, mul_pow]
    have hle' := TAct.logA_pow C.j_cris he1 hle (l ^ N)
    have hsum := GlobalTheory.T.isAcrisLogOneAdd_add_of_mul l _ _ _ _ hJ (inJ_mu (e := e ^ l ^ N) (by rw [map_pow, he1, one_pow])) hy hle'
    have hσ := isLogJ_extends (GlobalTheory.CrisMaps.sigA_extends g) hy
    have hw : Per.σA g (Per.tm (x₁ ^ l ^ N) - 1) = (Per.tm (x₁ ^ l ^ N) - 1) + mu (e ^ l ^ N) +
        (Per.tm (x₁ ^ l ^ N) - 1) * mu (e ^ l ^ N) := by
      rw [map_sub, map_one, show Per.σA g (Per.tm (x₁ ^ l ^ N)) = Per.tm (Per.σF g (x₁ ^ l ^ N)) from
        GlobalTheory.RingIface.sigA_teich l g _, hge₁, mu,
        show Per.tm (x₁ ^ l ^ N * e ^ l ^ N) = Per.tm (x₁ ^ l ^ N) * Per.tm (e ^ l ^ N) from
        map_mul (WittVector.teichmuller l) _ _]
      ring
    rw [hw] at hσ
    have hy' := isLogJ_unique hσ hsum
    have hσY : Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) y) =
        algebraMap _ _ (GlobalTheory.MemLoc.sigA g y) :=
      GlobalTheory.CrisMaps.σB_sigA g y
    have hσu : Per.σB g (↑u⁻¹ : Per.Bcris l) = ↑u⁻¹ :=
      map_inv_units _ u (by rw [hu, map_pow, map_natCast])
    have hul : (↑u⁻¹ : Per.Bcris l) * ((l ^ N : ℕ) : Per.Bcris l) = 1 := by
      rw [Nat.cast_pow, ← hu, Units.inv_mul]
    rw [map_mul, hσu, hσY, hy', map_add, map_mul, map_mul, map_natCast]
    rw [GlobalTheory.RingIface.zB_eq_aB_zA l c, GlobalTheory.RingIface.aB_eq_alg l (Per.zA l c)]
    simp only [Core.tB]
    linear_combination (algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l c)) *
      algebraMap (Per.Acris l) (Per.Bcris l) C.t) * hul

end GlobalTheory.LogU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTrivialCocycleCrystallinePeriodData
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem wseed_of_seed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (s : Seed bk d ρ τ), ∃ s' : WSeed bk d ρ τ, ∀ g, s'.κ g = 1 := by
  intro l _ K bk τ _ d ρ s
  refine ⟨{ s with κ := fun _ => 1, gal := ?_, fix := fun _ _ => rfl, nopole := ?_, log := ?_ }, fun _ => rfl⟩
  · intro g G hG
    rw [Matrix.mul_one]
    exact s.gal g G hG
  · intro g G hG i j
    obtain ⟨k, hk⟩ := s.nopole bk.ι ((ainfHom K g).comp bk.ι)
    have h1 := map_dvd bk.iA (hk i j)
    have hX : (s.X.map bk.iS).map G = s.X.map (fun x => bk.iA (Per.σA (g : GQ l) (bk.ev x))) := by
      ext a b
      simp only [Matrix.map_apply, BK.iS, RingHom.comp_apply]
      exact hG.ext _
    have hu : IsUnit (bk.iA ((l : Ainf l) ^ k)) := by
      rw [map_pow, map_natCast]
      exact (isUnit_l_disc l (bk.ev X) bk.ρ₀).pow k
    change bk.iA ((bk.ev bk.E) ^ (2 * s.N)) ∣ bk.iA ((l : Ainf l) ^ k * (s.X'.map bk.ev * s.X.map (fun x => Per.σA (g : GQ l) (bk.ev x))) i j) at h1
    rw [map_mul] at h1
    rw [Matrix.mul_one, hX]
    have h2 := (hu.dvd_mul_left).1 h1
    convert h2 using 1
    · simp only [BK.iS, RingHom.comp_apply, map_pow]
    · simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, BK.iS, RingHom.comp_apply]
  · intro m
    refine ⟨0, 1, fun i j => by simp, fun g G hG i j => ?_⟩
    simp [Matrix.map_one]

end GlobalTheory.BKLim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittResidueFieldInRingOfIntegers
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.Res

open IsLocalRing

theorem exists_teich {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    [Fintype (ResidueField O)] (x : O) :
    ∃ t : O, t ^ Fintype.card (ResidueField O) = t ∧ t - x ∈ maximalIdeal O := by
  have hq : 1 < Fintype.card (ResidueField O) := Fintype.one_lt_card
  obtain ⟨t, h1, h2⟩ := HenselianRing.is_henselian (I := maximalIdeal O)
    (Polynomial.X ^ Fintype.card (ResidueField O) - Polynomial.X)
    (Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hq)) x
    (by
      rw [← residue_eq_zero_iff]
      simp [FiniteField.pow_card])
    (by
      change IsUnit (residue O _)
      simp [Polynomial.derivative_X_pow, FiniteField.cast_card_eq_zero])
  exact ⟨t, by simpa [sub_eq_zero] using h1, h2⟩

theorem sol_mem_range {O F : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    [Fintype (ResidueField O)] [Field F] (f : O →+* F) (hf : Function.Injective f) (y : F)
    (hy : y ^ Fintype.card (ResidueField O) = y) : ∃ t, f t = y := by
  classical
  have hq : 1 < Fintype.card (ResidueField O) := Fintype.one_lt_card
  have : ∀ r : ResidueField O, ∃ t : O, t ^ Fintype.card (ResidueField O) = t ∧ residue O t = r := fun r => by
    obtain ⟨x, rfl⟩ := residue_surjective r
    obtain ⟨t, h1, h2⟩ := exists_teich x
    exact ⟨t, h1, by rwa [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]⟩
  choose t h1 h2 using this
  have hinj : Function.Injective fun r => f (t r) := fun r s h => by
    rw [← h2 r, ← h2 s, hf h]
  set P : Polynomial F := Polynomial.X ^ Fintype.card (ResidueField O) - Polynomial.X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F hq
  have hd : P.natDegree = Fintype.card (ResidueField O) := FiniteField.X_pow_card_sub_X_natDegree_eq F hq
  have hm : ∀ z : F, z ^ Fintype.card (ResidueField O) = z → z ∈ P.roots.toFinset := fun z hz => by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
    simp [hP, hz]
  have hs : Finset.univ.image (fun r => f (t r)) = P.roots.toFinset := by
    refine Finset.eq_of_subset_of_card_le (fun z hz => ?_) ?_
    · obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hz
      exact hm _ (by rw [← map_pow, h1])
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ← hd]
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' P)
  obtain ⟨r, -, hr⟩ := Finset.mem_image.1 (hs ▸ hm y hy)
  exact ⟨_, hr⟩

theorem exists_witt_residue : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∃ (a : ℕ) (_ : NeZero a) (w : Wq l a →ₐ[ℤ_[l]] ↥(OL K)), Kunr l a ≤ K.1 ∧ (∀ c, intToOC K (w c) = Per.θ l (wA l a c)) ∧ ∀ x : ↥(OL K), ∃ c, ¬ IsUnit (x - w c) := by
  intro l hl K
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hfin : Module.Finite ℤ_[l] ↥(OL K) := finite_OL K
  have hfin' : Module.Finite ℤ_[l] ↥(integralClosure ℤ_[l] ↥K.1) := hfin
  have hdvr : IsDiscreteValuationRing ↥(OL K) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr ℤ_[l] ℚ_[l] ↥K.1
  have hfa := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful ℤ_[l] ℚ_[l] ↥K.1
  have hloc : IsLocalHom (algebraMap ℤ_[l] ↥(OL K)) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom ℤ_[l] ↥K.1
  have hc : IsAdicComplete (maximalIdeal ↥(OL K)) ↥(OL K) :=
    GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[l] _
  have hF : Finite (ResidueField ↥(OL K)) :=
    ResidueField.finite_of_finite (R := ℤ_[l]) (Finite.of_equiv _ PadicInt.residueField.symm.toEquiv)
  have := Fintype.ofFinite (ResidueField ↥(OL K))
  have hch : CharP (ResidueField ↥(OL K)) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue ↥(OL K)), residue_eq_zero_iff, ← map_natCast (algebraMap ℤ_[l] ↥(OL K)),
      mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff, ← mem_nonunits_iff]
    exact PadicInt.p_nonunit
  obtain ⟨a, -, ha⟩ := FiniteField.card (ResidueField ↥(OL K)) l
  have hne : NeZero (a : ℕ) := ⟨a.ne_zero⟩
  let f : ↥(OL K) →+* Om l := K.1.val.toRingHom.comp (OL K).val.toRingHom
  have hf : Function.Injective f := fun _ _ h => Subtype.ext (Subtype.ext h)
  have hle : Kunr l a ≤ K.1 := IntermediateField.adjoin_le_iff.2 fun y hy => by
    obtain ⟨t, rfl⟩ := sol_mem_range f hf y (by rw [ha]; exact hy)
    exact (t : ↥K.1).2
  have : HasUnr a K := ⟨hle⟩
  refine ⟨a, hne, thetaW a K, hle, intToOC_thetaW a K, fun x => ?_⟩
  obtain ⟨t, h1, h2⟩ := exists_teich x
  rw [ha] at h1
  suffices ∃ c, thetaW a K c = t by
    obtain ⟨c, rfl⟩ := this
    exact ⟨c, fun h => h2 (by simpa using h.neg)⟩
  rcases eq_or_ne t 0 with rfl | h0
  · exact ⟨0, map_zero _⟩
  obtain ⟨z, ω, hω, hz, -⟩ := exists_gen l a
  have h3 := one_lt_pow_l l a
  have : NeZero (l ^ (a : ℕ) - 1) := ⟨by omega⟩
  obtain ⟨k, -, hk⟩ := hω.eq_pow_of_pow_eq_one (ξ := f t) (by
    rw [← map_pow, ← map_one f]
    congr 1
    exact mul_right_cancel₀ h0 (by rw [← pow_succ, Nat.sub_add_cancel h3.le, one_mul, h1]))
  refine ⟨WittVector.teichmuller l z ^ k, intToOC_injective K ?_⟩
  rw [intToOC_thetaW, map_pow, map_pow, wA_teich, WittVector.fontaineTheta_teichmuller]
  refine Subtype.ext ?_
  rw [SubmonoidClass.coe_pow, GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz]
  exact (map_pow (algebraMap (Om l) ℂ_[l]) ω k).symm.trans (congrArg _ hk)

end GlobalTheory.BSP.Res
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittVectorLiftOfIsAdicComplete
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.WittLift

variable (l : ℕ) [hl : Fact l.Prime] {C : Type} [CommRing C] (J : Ideal C)

theorem ghost_eq (n : ℕ) (x : _root_.WittVector l C) :
    _root_.WittVector.ghostComponent n x =
      ∑ i ∈ Finset.range (n + 1), (l : C) ^ i * x.coeff i ^ l ^ (n - i) := by
  rw [_root_.WittVector.ghostComponent_apply, aeval_wittPolynomial]

theorem ghost_mem_pow (hlJ : (l : C) ∈ J) (n : ℕ) (x : _root_.WittVector l C)
    (hx : ∀ i, x.coeff i ∈ J) : _root_.WittVector.ghostComponent n x ∈ J ^ n := by
  rw [ghost_eq]
  refine Ideal.sum_mem _ fun i _ => ?_
  have h1 : (l : C) ^ i ∈ J ^ i := Ideal.pow_mem_pow hlJ i
  have h2 : x.coeff i ^ l ^ (n - i) ∈ J ^ (l ^ (n - i)) := Ideal.pow_mem_pow (hx i) _
  have h3 : (l : C) ^ i * x.coeff i ^ l ^ (n - i) ∈ J ^ (i + l ^ (n - i)) := by
    rw [pow_add]; exact Ideal.mul_mem_mul h1 h2
  refine Ideal.pow_le_pow_right ?_ h3
  have : n - i < l ^ (n - i) := Nat.lt_pow_self hl.out.one_lt
  omega

def liftW (y : _root_.WittVector l (C ⧸ J)) : _root_.WittVector l C :=
  _root_.WittVector.mk l (fun i => Function.surjInv Ideal.Quotient.mk_surjective (y.coeff i))

theorem map_liftW (y : _root_.WittVector l (C ⧸ J)) :
    _root_.WittVector.map (Ideal.Quotient.mk J) (liftW l J y) = y := by
  ext i
  rw [_root_.WittVector.map_coeff]
  simp only [liftW, _root_.WittVector.coeff_mk]
  exact Function.surjInv_eq Ideal.Quotient.mk_surjective _

def gh (hlJ : (l : C) ∈ J) (n : ℕ) : _root_.WittVector l (C ⧸ J) →+* C ⧸ J ^ n :=
  RingHom.liftOfRightInverse (_root_.WittVector.map (Ideal.Quotient.mk J)) (liftW l J) (map_liftW l J)
    ⟨(Ideal.Quotient.mk (J ^ n)).comp (_root_.WittVector.ghostComponent n), fun x hx => by
      rw [RingHom.mem_ker] at hx ⊢
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      refine ghost_mem_pow l J hlJ n x fun i => ?_
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← _root_.WittVector.map_coeff, hx,
        _root_.WittVector.zero_coeff]⟩

theorem gh_map (hlJ : (l : C) ∈ J) (n : ℕ) (x : _root_.WittVector l C) :
    gh l J hlJ n (_root_.WittVector.map (Ideal.Quotient.mk J) x) =
      Ideal.Quotient.mk (J ^ n) (_root_.WittVector.ghostComponent n x) :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ x

end GlobalTheory.WittLift

namespace GlobalTheory.WittLift

variable (l : ℕ) [hl : Fact l.Prime] {C : Type} [CommRing C] (J : Ideal C)
variable (k : Type) [CommRing k] [CharP k l] [PerfectRing k l]

theorem symm_iter_pow (n : ℕ) (x : k) :
    (iterateFrobeniusEquiv k l (n + 1)).symm x ^ l = (iterateFrobeniusEquiv k l n).symm x := by
  apply (iterateFrobeniusEquiv k l n).injective
  rw [RingEquiv.apply_symm_apply, iterateFrobeniusEquiv_def, ← pow_mul, ← pow_succ',
    ← iterateFrobeniusEquiv_def k l (n + 1), RingEquiv.apply_symm_apply]

theorem symm_iter_zero (x : k) : (iterateFrobeniusEquiv k l 0).symm x = x := by
  apply (iterateFrobeniusEquiv k l 0).injective
  rw [RingEquiv.apply_symm_apply, iterateFrobeniusEquiv_zero_apply]

variable {k} (ψ : k →+* C ⧸ J)

def wn (n : ℕ) : _root_.WittVector l k →+* _root_.WittVector l (C ⧸ J) :=
  _root_.WittVector.map (ψ.comp (iterateFrobeniusEquiv k l n).symm.toRingHom)

def yh (n : ℕ) (w : _root_.WittVector l k) : _root_.WittVector l C := liftW l J (wn l J ψ n w)

theorem mk_yh_coeff (n : ℕ) (w : _root_.WittVector l k) (i : ℕ) :
    Ideal.Quotient.mk J ((yh l J ψ n w).coeff i) = ψ ((iterateFrobeniusEquiv k l n).symm (w.coeff i)) := by
  rw [← _root_.WittVector.map_coeff, yh, map_liftW, wn, _root_.WittVector.map_coeff]
  rfl

def fn (hlJ : (l : C) ∈ J) (n : ℕ) : _root_.WittVector l k →+* C ⧸ J ^ n :=
  (gh l J hlJ n).comp (wn l J ψ n)

theorem fn_apply (hlJ : (l : C) ∈ J) (n : ℕ) (w : _root_.WittVector l k) :
    fn l J ψ hlJ n w = Ideal.Quotient.mk (J ^ n) (_root_.WittVector.ghostComponent n (yh l J ψ n w)) := by
  rw [fn, RingHom.comp_apply, ← gh_map l J hlJ n, yh, map_liftW]

theorem step (hlJ : (l : C) ∈ J) (n : ℕ) (w : _root_.WittVector l k) :
    _root_.WittVector.ghostComponent (n + 1) (yh l J ψ (n + 1) w) -
      _root_.WittVector.ghostComponent n (yh l J ψ n w) ∈ J ^ n := by
  set y := yh l J ψ (n + 1) w with hy
  let z : _root_.WittVector l C := _root_.WittVector.mk l (fun i => y.coeff i ^ l)
  have hz : _root_.WittVector.map (Ideal.Quotient.mk J) z = wn l J ψ n w := by
    ext i
    rw [_root_.WittVector.map_coeff, _root_.WittVector.coeff_mk, map_pow, hy, mk_yh_coeff, ← map_pow,
      symm_iter_pow, wn, _root_.WittVector.map_coeff]
    rfl
  have h1 : _root_.WittVector.ghostComponent n (yh l J ψ n w) - _root_.WittVector.ghostComponent n z ∈ J ^ n := by
    rw [← Ideal.Quotient.eq, ← fn_apply, ← gh_map l J hlJ, hz, fn, RingHom.comp_apply]
  have h2 : _root_.WittVector.ghostComponent (n + 1) y - _root_.WittVector.ghostComponent n z =
      (l : C) ^ (n + 1) * y.coeff (n + 1) := by
    have ha : _root_.WittVector.ghostComponent (n + 1) y =
        (∑ i ∈ Finset.range (n + 1), (l : C) ^ i * y.coeff i ^ l ^ (n + 1 - i)) +
          (l : C) ^ (n + 1) * y.coeff (n + 1) := by
      rw [ghost_eq, Finset.sum_range_succ, Nat.sub_self, pow_zero, pow_one]
    have hb : _root_.WittVector.ghostComponent n z =
        ∑ i ∈ Finset.range (n + 1), (l : C) ^ i * y.coeff i ^ l ^ (n + 1 - i) := by
      rw [ghost_eq]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      simp only [z, _root_.WittVector.coeff_mk]
      rw [← pow_mul, ← pow_succ']
      congr 3
      omega
    rw [ha, hb]; ring
  have h3 : (l : C) ^ (n + 1) * y.coeff (n + 1) ∈ J ^ n :=
    Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlJ _))
  rw [← h2] at h3
  have := Ideal.sub_mem _ h3 h1
  convert this using 1
  abel

theorem compat (hlJ : (l : C) ∈ J) (w : _root_.WittVector l k) {m n : ℕ} (hle : m ≤ n) :
    _root_.WittVector.ghostComponent n (yh l J ψ n w) -
      _root_.WittVector.ghostComponent m (yh l J ψ m w) ∈ J ^ m := by
  induction n, hle using Nat.le_induction with
  | base => rw [sub_self]; exact Ideal.zero_mem _
  | succ n hmn ih =>
    have := Ideal.add_mem _ (Ideal.pow_le_pow_right hmn (step l J ψ hlJ n w)) ih
    convert this using 1
    abel

end GlobalTheory.WittLift

namespace GlobalTheory.WittLift

variable (l : ℕ) [hl : Fact l.Prime] {C : Type} [CommRing C] (J : Ideal C)
variable {k : Type} [CommRing k] [CharP k l] [PerfectRing k l] (ψ : k →+* C ⧸ J)

theorem fn_compat (hlJ : (l : C) ∈ J) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp (fn l J ψ hlJ n) = fn l J ψ hlJ m := by
  refine RingHom.ext fun w => ?_
  rw [RingHom.comp_apply, fn_apply, fn_apply, Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
  exact compat l J ψ hlJ w hle

end GlobalTheory.WittLift

namespace GlobalTheory

theorem exists_wittVector_lift_of_isAdicComplete :
    ∀ (l : ℕ) [Fact l.Prime] (k : Type) [CommRing k] [CharP k l] [PerfectRing k l] (C : Type) [CommRing C]
      (J : Ideal C), (l : C) ∈ J → IsAdicComplete J C → ∀ ψ : k →+* C ⧸ J,
      ∃ ω : WittVector l k →+* C, ∀ w, Ideal.Quotient.mk J (ω w) = ψ (w.coeff 0) := by
  intro l _ k _ _ _ C _ J hlJ hC ψ
  haveI := hC
  refine ⟨IsAdicComplete.liftRingHom J (WittLift.fn l J ψ hlJ) (WittLift.fn_compat l J ψ hlJ), fun w => ?_⟩
  have h0 : Ideal.Quotient.mk (J ^ 1)
      (IsAdicComplete.liftRingHom J (WittLift.fn l J ψ hlJ) (WittLift.fn_compat l J ψ hlJ) w) =
      Ideal.Quotient.mk (J ^ 1) (_root_.WittVector.ghostComponent 1 (WittLift.yh l J ψ 1 w)) := by
    rw [IsAdicComplete.mk_liftRingHom, WittLift.fn_apply]
  have h1 := Ideal.Quotient.eq.mp h0
  rw [pow_one] at h1
  rw [Ideal.Quotient.eq.mpr h1, WittLift.ghost_eq, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [pow_zero, one_mul, Nat.sub_zero, pow_one, Nat.sub_self, map_add, map_mul, map_pow]
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hlJ, zero_mul, add_zero, WittLift.mk_yh_coeff, ← map_pow,
    WittLift.symm_iter_pow, WittLift.symm_iter_zero]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpStarOfLowTermsRemovedStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expStar_of_low_terms_removed : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (g : GQ l), IsGen (LT l).χQ K s g → ∀ w : ℕ → Om l, (∀ j, w j ∈ Ks K s) → ∀ b ∈ FilB (LT l) 0, (∀ h ∈ Hinf K, NearZ (LT l) (e + 1) ((LT l).actQdR h b - b)) → NearZ (LT l) (e + 1) (∑ j ∈ Finset.range (e + 1), oB (LT l) (w j) * tD (LT l) ^ j + (qB (LT l) (((LT l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (LT l).actQdR g b - b)) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) (logZl l ((LT l).χQ g : ℚ_[l]))⁻¹ * w e) := by
  first | exact @GlobalTheory.ExpImage.LowTerms.expStar_of_sum | exact GlobalTheory.ExpImage.LowTerms.expStar_of_sum | (intros; apply GlobalTheory.ExpImage.LowTerms.expStar_of_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExportAllOfSixInputs
section
open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem GlobalTheory.exportAll_of_six_inputs :
    ∀ (D : D7) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ), admissibleIndexBoundAllPowers D.nexp (BlochKatoReduction.bk0 D) N0 → IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E →
      IntegralHeckeForms.GroupAlgebraIntegrality D.nexp → IntegralHeckeForms.admT4 D.nexp E → IntegralHeckeForms.TwistedSeriesSpecialisation D.nexp → IntegralHeckeForms.GoodLatticePoints D.nexp →
      ∀ i, D.ntw.NonzeroIndexPlace i → goodTwistExistsAllCoprimePowers D.nexp (BlochKatoReduction.bk0 D) E N0 i :=
  fun D E N0 h2 h3 h5 h7 h10 h11 i hi =>
    GlobalTheory.ExportFromInputs.twistModule_all_character_powers_of_admissible D.nexp (BlochKatoReduction.bk0 D) E N0 h2 h3 h5 h7 h10 h11 i hi
end

