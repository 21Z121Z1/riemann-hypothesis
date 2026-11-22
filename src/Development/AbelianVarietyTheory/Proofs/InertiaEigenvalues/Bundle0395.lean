import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0363
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
import Formalism.LocalToGlobal.NormalizedHeckeFactors.GlobalDatumRegularityOfTypesCompatibility
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import GroundTheory.LocalFields.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0361
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0347
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0279
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0364
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0288
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0362
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvAwayOfPure
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.PurityInvariants

theorem isRoot_of_eigen {R K : Type} [CommRing R] [Field K] (f : R →+* K) (ι : K →+* ℂ) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (c : K) (x : Fin n → K) (hx : x ≠ 0)
    (h : (M.map f).mulVec x = c • x) : (M.charpoly.map (ι.comp f)).IsRoot (ι c) := by
  classical
  have hdet : (Matrix.scalar (Fin n) c - M.map f).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨x, hx, ?_⟩
    rw [Matrix.sub_mulVec, h]
    ext j
    simp [Matrix.scalar_apply]
  have hroot : ((M.map f).charpoly).eval c = 0 := by
    rw [Matrix.eval_charpoly]
    exact hdet
  unfold Polynomial.IsRoot
  rw [← Polynomial.map_map, ← Matrix.charpoly_map, Polynomial.eval_map, Polynomial.eval₂_hom,
    hroot, map_zero]

theorem eigen_of_dual {R K : Type} [CommRing R] [Field K] (f : R →+* K) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (hM : IsUnit M.det) (c : R) (x : Fin n → K)
    (h : ((c • M⁻¹.transpose).map f).mulVec x = x) : (M.transpose.map f).mulVec x = f c • x := by
  have key : M.transpose * (c • M⁻¹.transpose) = c • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [Matrix.mul_smul, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hM, Matrix.transpose_one]
  calc (M.transpose.map f).mulVec x
      = (M.transpose.map f).mulVec (((c • M⁻¹.transpose).map f).mulVec x) := by rw [h]
    _ = ((M.transpose * (c • M⁻¹.transpose)).map f).mulVec x := by
        rw [Matrix.mulVec_mulVec, Matrix.map_mul]
    _ = f c • x := by
        rw [key]
        ext j
        simp [Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite f, ite_mul, Finset.sum_ite_eq]

theorem one_lt_norm {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    (1 : ℝ) < ((normV v : ℕ) : ℝ) := by
  have h1 : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hne1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have hne0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have : 1 < normV v := by omega
  exact_mod_cast this

theorem noInv_of_pure : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i) (ι : FractionRing (D.ntw.O0 i) →+* ℂ), Pure i s ι → ∀ v, v ∉ placesOver D.host.E (D.ntw.l i) → v ∉ Spl (X := D.ntw) i → NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  intro D i s ι hP v hv hs
  have hq : (1 : ℝ) < ((normV v : ℕ) : ℝ) := one_lt_norm v
  have ht : (5 : ℝ) ≤ (D.R.t : ℝ) := by
    have := D.R.rank_add_five_le
    exact_mod_cast (by omega : 5 ≤ D.R.t)
  have hlt : ((normV v : ℕ) : ℝ) ^ ((1 - (D.R.t : ℝ)) / 2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  have hl : ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by
    intro h
    apply hv
    unfold placesOver
    exact h
  constructor
  · intro A hA x hx
    by_contra hx0
    obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob (F := D.host.E) hA
    have hdec : σ ∈ Dec (F := D.host.E) A := by
      unfold Formalism.ConjugateSelfDual.IsFrob at hσ
      exact hσ.1
    have e := hx σ hdec
    have hr := isRoot_of_eigen (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))) ι (Tmat i s σ) 1 x hx0
      (by rw [one_smul]; exact e)
    have hn := hP v hv hs A hA σ hσ _ hr
    rw [map_one, norm_one] at hn
    linarith
  · intro A hA x hx
    by_contra hx0
    obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob (F := D.host.E) hA
    have hdec : σ ∈ Dec (F := D.host.E) A := by
      unfold Formalism.ConjugateSelfDual.IsFrob at hσ
      exact hσ.1
    have e := hx σ hdec
    have hu : IsUnit (Tmat i s σ).det := by
      unfold Tmat
      rw [Matrix.det_smul]
      exact ((Units.isUnit _).pow _).mul ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _))
    have e2 := eigen_of_dual (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))) (Tmat i s σ) hu
      ((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) x (by unfold Tdual at e; exact e)
    have hr := isRoot_of_eigen (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))) ι (Tmat i s σ).transpose _ x hx0 e2
    rw [Matrix.charpoly_transpose] at hr
    have hn := hP v hv hs A hA σ hσ _ hr
    have hc : ((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = (normV v : ℕ) := by
      unfold eps0
      rw [MonoidHom.comp_apply, Units.coe_map]
      exact (congrArg (algebraMap _ (D.ntw.O0 i)) (ReciprocityTheory.Gal.cycZ_of_isFrob hl hA hσ)).trans (map_natCast _ _)
    rw [hc, map_natCast, map_natCast, Complex.norm_natCast] at hn
    linarith

end GlobalTheory.PurityInvariants
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointParameterIsTypeParameterOfTameStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointParameterIsTypeParameter_of_tame : ∀ D : D7, (∀ S : Formalism.L2.ParC D, ∃ σ' : D.ntypes.Par, ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut S.1 w) → SumRepresentations.tie0 D → SumRepresentations.adm5 D → (∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)) → LabDepth D → DepthZ D → ParSurj D := by
  first | exact @GlobalTheory.ParOfPoint.main | exact GlobalTheory.ParOfPoint.main | (intros; apply GlobalTheory.ParOfPoint.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperRamificationGroupAbelianNat
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem pow_mem_upperRamificationGroup_abelian_nat :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
      (M : IntermediateField F (SeparableClosure F)) [FiniteDimensional F ↥M] [IsAbelianGalois F ↥M] (p e n : ℕ),
      OrdIs F p e → ∀ σ ∈ upperRamificationGroup F ↥M (n : ℝ),
        σ ^ p ∈ upperRamificationGroup F ↥M ((min (2 * n) (n + e) : ℕ) : ℝ) := by
  intro F _ _ _ _ M _ _ p e n h σ hσ
  rw [← map_unitFiltrationUnits_restrictAb_localArtinMap (Ω := SeparableClosure F) M n] at hσ
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hσ
  rw [← map_unitFiltrationUnits_restrictAb_localArtinMap (Ω := SeparableClosure F) M
    (min (2 * n) (n + e)), ← map_pow]
  exact Subgroup.mem_map_of_mem _ (GlobalTheory.T.pow_prime_mem_unitFiltrationUnits_min F p e n h x hx)

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulSubMemOfRootsModPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_mul_sub_mem_pow_of_eval_mem_pow : ∀ (R : Type) [CommRing R] (I : Ideal R) (p : Polynomial R) (x y b lam : R) (n : ℕ), p.eval x ∈ I ^ n → p.eval y ∈ I ^ n → x - y ∈ I → b * (Polynomial.derivative p).eval x - lam ∈ I → lam ^ n * (x - y) ∈ I ^ n := by
  first | exact @GlobalTheory.pow_mul_sub_mem_of_roots_mod_pow | exact GlobalTheory.pow_mul_sub_mem_of_roots_mod_pow | (intros; apply GlobalTheory.pow_mul_sub_mem_of_roots_mod_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeNotMemSqAndDeltaNotMem
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.LSq

def cInt (l : ℕ) (n : ℕ) : ℤ := ((n : ℤ) - (n : ℤ) ^ l) / l

theorem l_mul_cInt (l : ℕ) [hl : Fact l.Prime] (n : ℕ) : (l : ℤ) * cInt l n = (n : ℤ) - (n : ℤ) ^ l := by
  unfold cInt
  apply Int.mul_ediv_cancel'
  have h : (((n : ℤ) - (n : ℤ) ^ l : ℤ) : ZMod l) = 0 := by
    push_cast; rw [ZMod.pow_card, sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h

theorem δ_natCast (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (D : Delta l A) (n : ℕ) :
    D.δ (n : A) = ((cInt l n : ℤ) : A) := by
  induction n with
  | zero =>
    have : cInt l 0 = 0 := by
      unfold cInt; simp [zero_pow hl.out.ne_zero]
    simp [this, Delta.δ_zero]
  | succ n ih =>
    have h := D.δ_add (n : A) 1
    rw [D.δ_one, ih] at h
    push_cast
    rw [h]
    have key : cInt l (n + 1) = cInt l n - ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : ℤ) * (n : ℤ) ^ k := by
      have h0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
      apply mul_left_cancel₀ h0
      have e1 := l_mul_cInt l (n + 1)
      have e2 := l_mul_cInt l n
      have h5 : ((n : ℤ) + 1) ^ l = (n : ℤ) ^ l + 1 ^ l + (l : ℤ) *
          ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : ℤ) * (n : ℤ) ^ k * (1 : ℤ) ^ (l - k) := by
        rw [add_pow_prime_eq' hl.out]
        congr 2
        refine Finset.sum_congr rfl fun k _ => by ring
      simp only [one_pow, mul_one] at h5
      push_cast at e1
      rw [mul_sub, e1, e2, h5]; ring
    rw [key, Int.cast_sub, Int.cast_sum]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, one_pow, mul_one, add_zero]

theorem cInt_self (l : ℕ) [hl : Fact l.Prime] : cInt l l = 1 - (l : ℤ) ^ (l - 1) := by
  have h0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  apply mul_left_cancel₀ h0
  rw [l_mul_cInt, mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hl.out.one_le]

theorem δ_l (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (D : Delta l A) :
    D.δ (l : A) = 1 - (l : A) ^ (l - 1) := by
  rw [δ_natCast, cInt_self]; push_cast; ring

theorem δ_mem_of_mem_sq (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (D : Delta l A) (m : Ideal A)
    (hlm : (l : A) ∈ m) {x : A} (hx : x ∈ m ^ 2) : D.δ x ∈ m := by
  rw [sq] at hx
  have hl0 := hl.out.ne_zero
  suffices x ∈ m ∧ D.δ x ∈ m from this.2
  refine Submodule.mul_induction_on hx (fun a ha b hb => ⟨m.mul_mem_right b ha, ?_⟩) ?_
  · rw [D.δ_mul]
    refine m.add_mem (m.add_mem (m.mul_mem_right _ (m.pow_mem_of_mem ha _ (Nat.pos_of_ne_zero hl0)))
      (m.mul_mem_right _ (m.pow_mem_of_mem hb _ (Nat.pos_of_ne_zero hl0)))) ?_
    exact m.mul_mem_right _ (m.mul_mem_right _ hlm)
  · rintro x y ⟨hx, hδx⟩ ⟨hy, hδy⟩
    refine ⟨m.add_mem hx hy, ?_⟩
    rw [D.δ_add]
    refine m.sub_mem (m.add_mem hδx hδy) (m.sum_mem fun k hk => ?_)
    obtain ⟨hk0, hkl⟩ := Finset.mem_Ioo.1 hk
    exact m.mul_mem_left _ (m.pow_mem_of_mem hy _ (Nat.sub_pos_of_lt hkl))

theorem l_not_mem_sq : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (m : Ideal A),
    m ≠ ⊤ → (l : A) ∈ m → (l : A) ∉ m ^ 2 ∧ D.δ (l : A) ∉ m := by
  intro l hl A _ D m hm hlm
  have hδ : D.δ (l : A) ∉ m := by
    intro h
    rw [δ_l] at h
    have h2 : (l : A) ^ (l - 1) ∈ m :=
      m.pow_mem_of_mem hlm _ (Nat.sub_pos_of_lt hl.out.one_lt)
    exact hm ((Ideal.eq_top_iff_one _).2 (by simpa using m.add_mem h h2))
  exact ⟨fun h => hδ (δ_mem_of_mem_sq l D m hlm h), hδ⟩

end GlobalTheory.BSP.LSq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowDvdTiltUniformizerPowAcrisEventually
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.AcrisPow
variable {l : ℕ} [hl : Fact l.Prime]

theorem eventually_lt_two_pow (A B : ℕ) : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → A * n + B < 2 ^ n := by
  refine ⟨4 * (A + B + 1), fun n hn => ?_⟩
  set m := 2 * (A + B + 1) with hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show m ≤ n by omega)
  have hk : m ≤ k := by omega
  have h1 : m < 2 ^ m := Nat.lt_two_pow_self
  have h2 : k < 2 ^ k := Nat.lt_two_pow_self
  have h3 : (m + 1) * (k + 1) ≤ 2 ^ m * 2 ^ k := Nat.mul_le_mul h1 h2
  rw [pow_add]
  have h4 : A * (m + k) + B < (m + 1) * (k + 1) := by nlinarith
  omega

theorem dvd_pow_acris0 (ξ : Ainf l) (hξ : Per.θ l ξ = 0) :
    ((l : ℕ) : Per.Acris0 l) ∣ algebraMap (Ainf l) (Per.Acris0 l) ξ ^ l := by
  have hp : l.Prime := Fact.out
  have hlu : IsUnit ((l : ℕ) : Per.AinfP l) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Per.AinfP l) ((l : ℕ) : Per.Ainf l)
    rwa [map_natCast] at this
  have hf : IsUnit ((l.factorial : ℕ) : Per.AinfP l) := by
    obtain ⟨c, hc⟩ := GlobalTheory.Per.exists_factorial_mul_eq_pow_ainf l l
    have h2 := congrArg (algebraMap (Per.Ainf l) (Per.AinfP l)) hc
    rw [map_mul, map_pow, map_natCast, map_natCast] at h2
    exact isUnit_of_mul_isUnit_left (h2 ▸ hlu.pow l)
  obtain ⟨v, hv⟩ := hf.exists_right_inv
  have hx : ((l.factorial : ℕ) : Per.AinfP l) * (v * algebraMap (Per.Ainf l) (Per.AinfP l) ξ ^ l) =
      algebraMap (Per.Ainf l) (Per.AinfP l) ξ ^ l := by rw [← mul_assoc, hv, one_mul]
  generalize v * algebraMap (Per.Ainf l) (Per.AinfP l) ξ ^ l = x at hx
  have hxD : x ∈ Per.Acris0 l := GlobalTheory.RingIface.dividedPower_mem_Acris0 l ξ l x hξ hx
  have hfac : ((l.factorial : ℕ) : Per.AinfP l) =
      ((l : ℕ) : Per.AinfP l) * (((l - 1).factorial : ℕ) : Per.AinfP l) := by
    rw [← Nat.cast_mul, Nat.mul_factorial_pred hp.ne_zero]
  refine ⟨(((l - 1).factorial : ℕ) : Per.Acris0 l) * ⟨x, hxD⟩, Subtype.ext ?_⟩
  simp only [SubmonoidClass.coe_pow, Subalgebra.coe_algebraMap, Subalgebra.coe_mul, SubringClass.coe_natCast]
  rw [← hx, hfac, mul_assoc]

theorem dvd_X_pow {K : FinExt l} (bk : BK K) :
    (l : Per.Acris l) ∣ ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ^ (bk.Ep.natDegree * l) := by
  set f := algebraMap (Ainf l) (Per.Acris l)
  have hξ : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  have h1 : (l : Per.Acris l) ∣ f (bk.ev bk.E) ^ l := by
    have := map_dvd (algebraMap (Per.Acris0 l) (Per.Acris l)) (dvd_pow_acris0 _ hξ)
    rw [map_natCast, map_pow, ← GlobalTheory.RingIface.tower l] at this
    exact this
  have h2 : (l : Per.Acris l) ∣ f (bk.ev bk.E) - f (bk.ev X) ^ bk.Ep.natDegree := by
    have := map_dvd f (AinfDiv.dvd_E bk)
    rwa [map_natCast, map_sub, map_pow] at this
  have h3 : (l : Per.Acris l) ∣ f (bk.ev bk.E) ^ l - (f (bk.ev X) ^ bk.Ep.natDegree) ^ l :=
    h2.trans (sub_dvd_pow_sub_pow _ _ l)
  have h4 := dvd_sub h1 h3
  rw [sub_sub_cancel, ← pow_mul] at h4
  simpa [RingHom.comp_apply] using h4

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (c M : ℕ), ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    (l : Per.Acris l) ^ (c * n + M) ∣ ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ^ (l ^ n - 1) := by
  intro l _ K bk c M
  set e := bk.Ep.natDegree
  obtain ⟨n₀, hn₀⟩ := eventually_lt_two_pow (e * l * c) (e * l * M)
  refine ⟨n₀, fun n hn => ?_⟩
  have hlt := hn₀ n hn
  have h2l : 2 ^ n ≤ l ^ n := Nat.pow_le_pow_left (Fact.out : l.Prime).two_le n
  have hle : e * l * (c * n + M) ≤ l ^ n - 1 := by
    have : e * l * (c * n + M) = e * l * c * n + e * l * M := by ring
    omega
  have hk := pow_dvd_pow_of_dvd (dvd_X_pow bk) (c * n + M)
  rw [← pow_mul] at hk
  exact hk.trans (pow_dvd_pow _ hle)

end GlobalTheory.AcrisPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimitiveCentralIdempotentEqSimpleRepIdempotentStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveCentralIdempotent_eq_simpleRepIdempotent : ∀ (g a : ℕ) [Fact g.Prime] (L : PairedCharacterCondition.LzData g) (τ : L.Irr a), ∃ ρ : FDRep ℂ (GL (Fin a) (ZMod g)), CategoryTheory.Simple ρ ∧ L.idem τ = Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ := by
  first | exact @GlobalTheory.PrimCentIdem.main | exact GlobalTheory.PrimCentIdem.main | (intros; apply GlobalTheory.PrimCentIdem.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismLocalizationSpanNonZeroDivisorBoundedTorsio
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem pow_mul_eq_zero_of_invertible {A : Type} [CommRing A] (I : Ideal A) (hI : Module.Invertible A ↥I)
    (f c : A) (h : ∀ x ∈ I, ∃ k : ℕ, f ^ k * (c * x) = 0) : ∃ K : ℕ, f ^ K * c = 0 := by
  classical
  have hfg : I.FG := Module.Finite.iff_fg.1 inferInstance
  obtain ⟨S, hS⟩ := hfg
  let k : A → ℕ := fun x => if hx : x ∈ I then (h x hx).choose else 0
  have hk : ∀ x ∈ I, f ^ k x * (c * x) = 0 := fun x hx => by
    simp only [k, dif_pos hx]; exact (h x hx).choose_spec
  refine ⟨S.sup k, ?_⟩
  have hle : I ≤ LinearMap.ker (LinearMap.mulLeft A (f ^ S.sup k * c)) := by
    rw [← hS, Submodule.span_le]
    intro x hx
    have hxI : x ∈ I := hS ▸ Submodule.subset_span hx
    have hkx : k x ≤ S.sup k := Finset.le_sup (f := k) hx
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.mulLeft_apply]
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hkx
    rw [hj, pow_add]
    linear_combination (f ^ j) * hk x hxI
  apply eq_of_smul_eq_smul (α := ↥I)
  intro y
  have := hle y.2
  rw [LinearMap.mem_ker, LinearMap.mulLeft_apply] at this
  ext
  simp [this]

theorem locAway_span_nzd_bdd (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (f d : B.A)
    (hG : GenAway B f d) (M : Submonoid B.A) (hf : f ∈ M) :
    B.I.map (algebraMap B.A (Localization M)) = Ideal.span {algebraMap B.A (Localization M) d} ∧
    algebraMap B.A (Localization M) d ∈ nonZeroDivisors (Localization M) ∧
    ∃ N : ℕ, ∀ (x : Localization M) (m : ℕ), (l : Localization M) ^ m * x ∈
      Ideal.span {algebraMap B.A (Localization M) d} →
      (l : Localization M) ^ N * x ∈ Ideal.span {algebraMap B.A (Localization M) d} := by
  set φ := algebraMap B.A (Localization M) with hφ
  have hu : IsUnit (φ f) := IsLocalization.map_units (Localization M) (⟨f, hf⟩ : M)
  have h1 : B.I.map φ = Ideal.span {φ d} := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      obtain ⟨k, hk⟩ := hG.2 x hx
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hk
      rw [Ideal.mem_comap, ← Ideal.unit_mul_mem_iff_mem _ (hu.pow k), ← map_pow, ← map_mul, ← hc, map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ hG.1
  refine ⟨h1, ?_, ?_⟩
  · rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    rw [mul_comm, hφ, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨t, ht⟩ := hx
    obtain ⟨K, hK⟩ := pow_mul_eq_zero_of_invertible B.I B.inv f ((t : B.A) * a) (fun x hx => by
      obtain ⟨k, hk⟩ := hG.2 x hx
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hk
      exact ⟨k, by linear_combination c * ht - (t : B.A) * a * hc⟩)
    rw [IsLocalization.mk'_eq_zero_iff]
    exact ⟨⟨f ^ K * t, M.mul_mem (M.pow_mem hf K) t.2⟩, by simp only; linear_combination hK⟩
  · obtain ⟨n, hn⟩ := B.bdd
    refine ⟨n, fun x m hx => ?_⟩
    rw [← h1] at hx ⊢
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    have e : ∀ j : ℕ, (l : Localization M) ^ j * IsLocalization.mk' (Localization M) a s =
        IsLocalization.mk' (Localization M) ((l : B.A) ^ j * a) s := fun j => by
      rw [← IsLocalization.mul_mk'_eq_mk'_of_mul, map_pow, map_natCast]
    rw [e, IsLocalization.mk'_mem_map_algebraMap_iff] at hx ⊢
    obtain ⟨s', hs', hI⟩ := hx
    refine ⟨s', hs', ?_⟩
    have h0 : (l : B.A ⧸ B.I) ^ m * Ideal.Quotient.mk B.I (s' * a) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk B.I), ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      convert hI using 1; ring
    have h2 := hn _ ⟨m, h0⟩
    rw [← map_natCast (Ideal.Quotient.mk B.I), ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at h2
    convert h2 using 1; ring

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PureOfAttached
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal

theorem pure_of_tripleAtt : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i),
    TripleAtt D.naut bkP i s → ∃ ι, Pure i s ι := by
  rintro D bkP i s ⟨ι, π₁, π, -, hA, hR, -⟩
  refine ⟨ι, fun v hl hS A hAv σ hσ z hz => ?_⟩
  have hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := fun k hk =>
    hS ⟨Or.inl (Set.mem_iUnion.2 ⟨k, hk⟩), hl⟩
  have hp : v ∉ D.ntw.pD i := fun hk => hS ⟨Or.inr (Finset.mem_coe.2 hk), hl⟩
  have hu := hR.unr v hg hp
  have hf := hA.frob v hl hu A σ hAv hσ
  have ht := (D.naut.tempered_unr _ hu).1 (hA.temp v hl)
  rw [Tgl_coe] at hf
  rw [hf, D.naut.frobEig_tw _ _ hu, IsRoot.def, eval_multiset_prod, Multiset.prod_eq_zero_iff] at hz
  simp only [Multiset.mem_map] at hz
  obtain ⟨_, ⟨_, ⟨α, hα, rfl⟩, rfl⟩, h0⟩ : ∃ p, (∃ β, (∃ α, α ∈ D.naut.frobEig (D.naut.locG π v) ∧
      α * ((normV v : ℕ) : ℂ) ^ (((1 - (D.R.t : ℝ)) / 2 : ℝ) : ℂ) = β) ∧ Polynomial.X - C β = p) ∧ eval z p = 0 := hz
  have hpos : 0 < normV v := by
    have : Finite (𝓞 D.host.E ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
    exact Nat.card_pos
  rw [eval_sub, eval_X, eval_C, sub_eq_zero] at h0
  rw [h0, norm_mul, ht α hα, one_mul, Complex.norm_natCast_cpow_of_pos hpos, Complex.ofReal_re]

end GlobalTheory.TripleGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioInvariantInK0
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.FracInv

theorem tied_frac_invariant : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K : FinExt l) (a b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, P.actQ g a * b = a * P.actQ g b) →
      ∃ c : ↥(K0 K), a = algebraMap ↥(K0 K) P.R.B c * b := by
  intro l _ P AI T K a b hb h
  have hF : IsField P.R.BdR := GlobalTheory.Per.FontaineBound.isField_of_tied T
  have h' : ∀ g, b * (P.PD K).actB g a = (P.PD K).actB g b * a := by
    intro g
    have := h g.1 g.2
    rw [P.PD_actB, P.PD_actB, mul_comm, this, mul_comm]
  obtain ⟨c, hc⟩ := GlobalTheory.Per.FontaineBound.frac_dR (P.PD K) hF ((P.PD K).ι b) ((P.PD K).ι a)
    (fun h0 => hb ((P.PD K).ι_inj (h0.trans (map_zero _).symm)))
    (fun g => by rw [← (P.PD K).ι_comm, ← (P.PD K).ι_comm, ← map_mul, ← map_mul, h' g])
  have hcU : (c : Om l) ∈ MaximalUnramifiedExtension l := by
    refine GlobalTheory.FracAlg.mem_Kur_of_ratio l P AI T a b (c : Om l) hb ?_
    have h1 := hc
    rw [P.PD_ι, P.PD_ι] at h1
    exact h1
  refine ⟨⟨c, c.2, hcU⟩, (P.PD K).ι_inj ?_⟩
  rw [map_mul, AlgHom.commutes, hc]
  rfl

end GlobalTheory.Per.FracInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueIndepOfNotReducibleOverUnramifiedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_indep_of_not_reducibleOverUnramified : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (m : ℕ) (u : n → P.R.BdR) (a : ℤ), IsRat r ρ → ¬ Splits r ρ → (∀ i, u i ∈ Fil P 0) → (∃ i, u i ∉ Fil P 1) → (∀ g : ↥(GK K), (matD P ρ m g).mulVec (fun i => P.actQdR (g : GQ l) (u i)) = algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ a : ℚ_[l]ˣ) : ℚ_[l]) • u) → ∀ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) → ∑ i, kd P (c i) * u i ∈ Fil P 1 → c = 0 := by
  first | exact @GlobalTheory.PMon.residue_indep_of_not_splits | exact GlobalTheory.PMon.residue_indep_of_not_splits | (intros; apply GlobalTheory.PMon.residue_indep_of_not_splits <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerCocyclesScalarChangeTransferStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selmerCocycles_scalarChange_transfer : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (Λ : Type) [CommRing Λ] [Algebra (X.O0 i) Λ] (Λ' : Type) [CommRing Λ'] [Algebra (X.O0 i) Λ'] (φ : Λ →ₐ[X.O0 i] Λ') (κ : GE N →* Λˣ) (κ' : GE N →* Λ'ˣ), (∀ g, ((κ' g : Λ'ˣ) : Λ') = φ (κ g : Λˣ)) → ∀ (Y : Type) [AddCommGroup Y] [Module Λ Y] [Module Λ' Y] [TopologicalSpace Y] [DiscreteTopology Y], (∀ (a : Λ) (y : Y), a • y = φ a • y) → (∀ g m, repOn (Tgl i s) κ Y g m = repOn (Tgl i s) κ' Y g m) ∧ ∀ Q f, SelC bkP i s κ Y Q f ↔ SelC bkP i s κ' Y Q f := by
  first | exact @GlobalTheory.NewPrime.ScalarChange.selC_transfer | exact GlobalTheory.NewPrime.ScalarChange.selC_transfer | (intros; apply GlobalTheory.NewPrime.ScalarChange.selC_transfer <;> assumption)
end

