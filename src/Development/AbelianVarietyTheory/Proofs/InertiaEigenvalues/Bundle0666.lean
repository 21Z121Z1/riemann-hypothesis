import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPullBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToAmbCoefH1EqCoefAmbToAmb
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0440
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0258
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0610
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowSmulEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VanishOfLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0503
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPresTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0627
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0647
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0276
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0552
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0592
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0629
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0479
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0523
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0598
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0634
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0652
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0612
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0419
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0547
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0415
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0235
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0648
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0653
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedLatticeCohomologyTheoremTOP
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
open GlobalTheory.PhiGam GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.TopBridge

theorem freeH_of_vanish_euler : Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), S.Vanish → S.FreeH := by
  intro heul l _ P S hV
  obtain ⟨hs, ht, -, -, -⟩ := S.hyp
  obtain ⟨hDVR, -, -, hA, hF, hFr⟩ := GlobalTheory.CoefInt.integers_laws l S.LL
  haveI := hDVR
  haveI := hFr
  exact GlobalTheory.FreeCoh.free_and_tensIso_gal S.Γ hs.2.2.2.2.2 hA hF
    (GlobalTheory.LocalIntegers.isOpen_integers l S.LL)
    (fun U hU => GlobalTheory.FreeCoh.pow_mul_mem_nhds S.LL S.Γ.lam hs.2.2.2.2.2 U hU)
    ht.2.2.1.1 (GlobalTheory.AdmClasses.not_isUnit_integers l S.LL) hV.1 hV.2 ht.1 hs.2.2.1
    (fun M _ _ _ π hlm hlc h0 h2 => GlobalTheory.T.card_H1_local_euler_formula heul l S.K S.O M π hlm hlc h0 h2)

theorem stmtAt_of_real (hdual : Formalism.GaloisCohomology.LocalTateDualityK) (heul : Formalism.GaloisCohomology.LocalEulerCharK)
    {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (htied : Nonempty (LocTied l P AI))
    (hreal : ∀ S : TopSit P, S.Real)
    (hbk : ∀ K LL : FinExt l, CaseA K LL → tableLineDegreeTwo.BlochKatoJumpDimension (P.PD K) (LL := ↥LL.1) (O := ↥(OL LL)) (IK K)) :
    GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.ErrorExponentStatement P := by
  intro K LL n r _ emb D Γ hs ht h1 h2 h3
  let S : TopSit P := ⟨K, LL, n, r, emb, D, Γ, ⟨hs, ht, h1, h2, h3⟩⟩
  have hCC : S.CrysCalc := GlobalTheory.TopSteps.CrysRules.crysCalc AI htied S
  have hR : S.Real := hreal S
  have hV : S.Vanish := GlobalTheory.TopVanish.vanish_of_real hdual S hR
  have hF : S.FreeH := freeH_of_vanish_euler heul S hV
  have hCl : S.Closed := GlobalTheory.AdmClosure.admissible_closed S
  have hStd : S.StdAdm := GlobalTheory.TopSteps.StdAdm.stdAdm S hCC hCl
  have hL0 : S.Lem0 S.Γ.W₀ := (GlobalTheory.AdmClasses.admissibleLocalSituation_admissible_classes S hCl hStd).1
  have hFS : S.FSummand :=
    GlobalTheory.TopSteps.FinSummandJumps.fSummand S (hbk K LL hs.2.1) hCC hV hF
  have hFA : S.FinAdm :=
    GlobalTheory.FiniteAdm.finAdm S hCC (GlobalTheory.FontaineExtensionCriteria.extCrys_of_tied P AI htied) hCl hStd hL0
  have hPsi : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi := GlobalTheory.PsiShiftProof.lemmaPsi
  have hRB : S.ResBound S.Γ.W₀ S.D.dsum := GlobalTheory.ResidueBound.resBound_dsum hPsi S hR hL0
  refine ⟨hV.1, hV.2, hF.1, hFS, fun X _ _ _ => ⟨hF.2 X, ?_⟩⟩
  exact GlobalTheory.AdmFinite.cls_eq_H1fX S hL0 hF hFS hFA hRB X

theorem twistedLatticeCohomology_theoremTOP : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    tableLineDegreeTwo.Stmt D HW F Cm := by
  intro D HW F Cm hA l _ K LL hK lam hlam
  have htied : Nonempty (LocTied l (D.loc l) (D.locA l)) := ⟨D.locT l⟩
  have h18 := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h19 := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hreal : ∀ S : TopSit (D.loc l), S.Real := fun S =>
    GlobalTheory.BasePairs.real_of_presented (D.locA l) (HW l) (F l) S
      (GlobalTheory.RedFun.realD (D.locA l) (HW l) (F l) S)
      (GlobalTheory.T.wachLattice_usedProperties_of_admitted D HW F Cm hA l S.K S.LL S.hyp.1.2.1)
      (GlobalTheory.TopSteps.CrysRules.crysCalc (D.locA l) htied S)
  exact GlobalTheory.T.exactLocalConditions_topCore (D.loc l) (D.locA l) htied (HW l)
    (stmtAt_of_real h18.1 h18.2 (D.loc l) (D.locA l) htied hreal (fun K' LL' hc => h19 l K' LL' hc))
    (GlobalTheory.TopSteps.CharVanish.stmt_of_real (D.loc l) (D.locA l) htied hreal)
    (GlobalTheory.TopSteps.admissibleUntwistedCharUnramified_of_residueRealisation (D.loc l) (D.locA l) htied hreal)
    K LL hK lam hlam

end GlobalTheory.TopBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedMatrixCongruenceLiftSequence
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.LimLink

theorem dvd_iff_map_eq {R : Type*} [CommRing R] {p q : Type*} (a : R) (A B : Matrix p q R) :
    (∀ i j, a ∣ (A - B) i j) ↔
      A.map (Ideal.Quotient.mk (Ideal.span {a})) = B.map (Ideal.Quotient.mk (Ideal.span {a})) := by
  first
  | exact @_root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq
  | exact _root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq
  | (apply _root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DvdSubMapMk.dvd_sub_iff_map_mk_eq ..)

theorem map_smul_ringHom {R S : Type*} [CommRing R] [CommRing S] {p q : Type*} (f : R →+* S) (r : R)
    (A : Matrix p q R) : (r • A).map f = f r • A.map f := by
  ext i j; simp

end GlobalTheory.BKLim.LimLink

open GlobalTheory.BKLim.LimLink in
theorem GlobalTheory.BKLim.limit_basis_link_mod : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Pre bk N (tw.d' n) fun g => (tw.ρ' n g).val) (T0 : Matrix (Fin d) (Fin d) (WCb l)) (R : ∀ n, Matrix (Fin d) (Fin (tw.d' n)) (WCb l)), (∀ n i j, (l : WCb l) ^ n ∣ (zW (tw.Pi n) * (F n).T - T0 * R n) i j) → (∀ n, ∃ m, n ≤ m ∧ ∀ s : Fin (tw.d' m) → bk.S, ∃ v : Fin d → WCb l, (∀ i, (l : WCb l) ^ n ∣ (v - R m *ᵥ fun j => bk.evW (s j)) i) ∧ ∀ k, ∃ s' : Fin (tw.d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ v : Fin d → WCb l, (∀ k, ∃ s' : Fin (tw.d' k) → bk.S, ∀ i, (l : WCb l) ^ k ∣ (v - R k *ᵥ fun j => bk.evW (s' j)) i) → (∀ i, v i ∈ bk.OE) ∧ ∃ y : Fin d → Ainf l, (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ v)) → ∀ (Y : Matrix (Fin d) (Fin d) (Ainf l)) (T : Matrix (Fin d) (Fin d) (WCb l)), Y.map (inclW l) = inclW l τ ^ N • T → (∀ y : Fin d → Ainf l, (∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun i => inclW l (y i)) = inclW l τ ^ N • (T0 *ᵥ w)) → ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a)) → ∀ n, ∃ m, n ≤ m ∧ ∃ (Rn : Matrix (Fin d) (Fin (tw.d' m)) bk.S) (Q : Matrix (Fin (tw.d' m)) (Fin d) (Ainf l)), (∀ i j, (l : WCb l) ^ n ∣ (zW (tw.Pi m) * (F m).T - T * Rn.map bk.evW) i j) ∧ ∀ i j, (l : WCb l) ^ n ∣ (Y.map (inclW l) * (Rn.map bk.ev * Q).map (inclW l) - inclW l τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j := by
  intro l _ K bk τ hτ d N ρ tw F T0 R H1 H2 H3 Y T hY H5 n
  obtain ⟨hu, -, -, -⟩ := GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ
  have huN : IsUnit (inclW l τ ^ N) := hu.pow N
  obtain ⟨π, key, key'⟩ : ∃ π : WCb l →+* (WCb l ⧸ Ideal.span {(l : WCb l) ^ n}),
      (∀ {p q : ℕ} (A B : Matrix (Fin p) (Fin q) (WCb l)),
        (∀ i j, (l : WCb l) ^ n ∣ (A - B) i j) → A.map π = B.map π) ∧
      (∀ {p q : ℕ} (A B : Matrix (Fin p) (Fin q) (WCb l)),
        A.map π = B.map π → ∀ i j, (l : WCb l) ^ n ∣ (A - B) i j) :=
    ⟨_, fun A B => (dvd_iff_map_eq _ A B).1, fun A B => (dvd_iff_map_eq _ A B).2⟩
  obtain ⟨m, hnm, hm⟩ := H2 n
  have hcol : ∀ j : Fin (tw.d' m), ∃ (v : Fin d → WCb l) (c : Fin d → bk.S),
      (∀ i, (l : WCb l) ^ n ∣ v i - R m i j) ∧ T0 *ᵥ v = T *ᵥ fun a => bk.evW (c a) := by
    intro j
    obtain ⟨v, hv1, hv2⟩ := hm (Pi.single j 1)
    obtain ⟨hOE, y, hy⟩ := H3 v hv2
    obtain ⟨c, hc⟩ := H5 y ⟨v, hOE, hy⟩
    refine ⟨v, c, ?_, ?_⟩
    · intro i
      have hs : (fun a => bk.evW ((Pi.single j (1 : bk.S) : Fin (tw.d' m) → bk.S) a))
          = Pi.single j 1 := by
        funext a; by_cases h : a = j
        · subst h; simp
        · simp [Pi.single_apply, h]
      have := hv1 i
      rw [hs] at this
      simpa [Matrix.mulVec_single_one] using this
    · have h1 : (fun i => inclW l (y i)) = inclW l τ ^ N • (T *ᵥ fun a => bk.evW (c a)) := by
        rw [hc]; funext i
        rw [RingHom.map_mulVec, hY, Matrix.smul_mulVec]
        rfl
      rw [hy] at h1
      exact huN.smul_left_cancel.1 h1
  choose V C hV hVC using hcol
  let Rn : Matrix (Fin d) (Fin (tw.d' m)) bk.S := Matrix.of fun i j => C j i
  have hTR : T * Rn.map bk.evW = T0 * Matrix.of (fun i j => V j i) := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (hVC j) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Rn]
    exact this.symm
  have hfirst : (zW (tw.Pi m) * (F m).T).map π = (T * Rn.map bk.evW).map π := by
    have e1 : (zW (tw.Pi m) * (F m).T).map π = (T0 * R m).map π :=
      key _ _ (fun i j => (pow_dvd_pow _ hnm).trans (H1 m i j))
    have e2 : (R m).map π = (Matrix.of fun i j => V j i).map π :=
      key _ _ (fun i j => by
        have := hV j i
        rw [← dvd_neg]; simpa [neg_sub] using this)
    rw [e1, hTR, Matrix.map_mul, Matrix.map_mul, e2]
  obtain ⟨Ym, Y'm, hYm, hYY⟩ :=
    GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N (tw.d' m) (fun g => (tw.ρ' m g).val) (F m)
  obtain ⟨Sm, hSm⟩ := (tw.onto m).surj
  refine ⟨m, hnm, Rn, Y'm * Sm.map (algebraMap ℤ_[l] (Ainf l)), key' _ _ hfirst, ?_⟩
  have hinc : ∀ x : ℤ_[l], inclW l (algebraMap ℤ_[l] (Ainf l) x) = algebraMap ℤ_[l] (WCb l) x :=
    fun x => (inclWA l).commutes x
  have hFY : (F m).T * Y'm.map (inclW l) = inclW l τ ^ N • (1 : Matrix (Fin (tw.d' m)) (Fin (tw.d' m)) (WCb l)) := by
    apply huN.smul_left_cancel.1
    rw [← Matrix.smul_mul, ← hYm, ← Matrix.map_mul, hYY, map_smul_ringHom,
      Matrix.map_one _ (map_zero _) (map_one _), smul_smul, map_pow, ← pow_add, two_mul]
  have hQ : ((Rn.map bk.ev) * (Y'm * Sm.map (algebraMap ℤ_[l] (Ainf l)))).map (inclW l)
      = Rn.map bk.evW * (Y'm.map (inclW l) * zW Sm) := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map]
    congr 2
    ext i j
    simp [hinc]
  have hS1 : (zW (tw.Pi m * Sm)).map π = (1 : Matrix (Fin d) (Fin d) (WCb l)).map π := by
    apply key
    intro i j
    have e : (zW (tw.Pi m * Sm) - 1) i j = algebraMap ℤ_[l] (WCb l) ((tw.Pi m * Sm - 1 : Matrix (Fin d) (Fin d) ℤ_[l]) i j) := by
      simp only [zW, Matrix.sub_apply, Matrix.map_apply, map_sub]
      congr 1
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [e]
    refine (pow_dvd_pow _ hnm).trans ?_
    have := map_dvd (algebraMap ℤ_[l] (WCb l)) (hSm i j)
    simpa using this
  have hE : inclW l τ ^ N • (zW (tw.Pi m) * (F m).T * (Y'm.map (inclW l) * zW Sm))
      = inclW l τ ^ (2 * N) • zW (tw.Pi m * Sm) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (F m).T, hFY, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, smul_smul,
      ← pow_add, ← two_mul]
    simp only [zW, Matrix.map_mul]
  apply key'
  calc (Y.map (inclW l) * (Rn.map bk.ev * (Y'm * Sm.map (algebraMap ℤ_[l] (Ainf l)))).map (inclW l)).map π
      = (inclW l τ ^ N • ((T * Rn.map bk.evW) * (Y'm.map (inclW l) * zW Sm))).map π := by
        rw [hQ, hY, Matrix.smul_mul, ← Matrix.mul_assoc]
    _ = (inclW l τ ^ N • ((zW (tw.Pi m) * (F m).T) * (Y'm.map (inclW l) * zW Sm))).map π := by
        rw [map_smul_ringHom, map_smul_ringHom, Matrix.map_mul, Matrix.map_mul (L := zW (tw.Pi m) * (F m).T), hfirst]
    _ = (inclW l τ ^ (2 * N) • zW (tw.Pi m * Sm)).map π := by rw [hE]
    _ = (inclW l τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (WCb l))).map π := by
        rw [map_smul_ringHom, map_smul_ringHom, hS1]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentColumnWhittakerTransformNeZero
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem colT_ne_zero_of_good : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ →
    ∀ (m : ℕ) (f : GA E a → ℂ), m + 1 < a → Good ψ (m + 1) f → f ≠ 0 → colT ψ (m + 1) f ≠ 0 := by
  intro E _ _ a ψ hψ m f hma hG hf
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, f g₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (funext h)
  have hPer : Per (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (fun x => f (blkU x * g₀)) :=
    per_blk hG.cont (fun c g => hG.left _ (isMir_blkU c) g) g₀
  have hΦ0 : (fun x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E => f (blkU x * g₀)) ≠ 0 := by
    intro h
    have h1 := congrFun h 0
    simp only [Pi.zero_apply] at h1
    apply hg₀
    have e : (blkU (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E) : GA E a) = 1 := posU_zero _
    rw [e, one_mul] at h1
    exact h1
  obtain ⟨ξ, hξ⟩ : ∃ ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E, coefF ψ (m + 1) ξ f g₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hΦ0 (GlobalTheory.T.periodic_eq_zero_of_fourier_coefficients_zero E _ ψ hψ _ hPer h)
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    apply hξ
    have hv := hG.van (m + 1) (Nat.succ_pos m) le_rfl g₀
    have e : ∀ x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E, ψ (-dot (0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) x) = 1 := by
      intro x
      simp [dot]
    simp only [coefF, e, one_mul]
    exact hv
  obtain ⟨γ, hγ, hγξ⟩ := GlobalTheory.T.exists_rationalMirabolic_moving_row_to_last E a m hma ξ hξ0
  intro h
  apply hξ
  have h1 := congrFun h (ratGL E a γ * g₀)
  simp only [Pi.zero_apply, colT] at h1
  rw [GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul E a ψ hψ m f hG.cont hG.left γ hγ (eLast a (m + 1)) g₀] at h1
  have e : (fun t : UnipotentBlockColumnIndex a (m + 1) (m + 1) => ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), eLast a (m + 1) s * γ.val s.1.1 t.1.1) = ξ :=
    funext hγξ
  rw [e] at h1
  exact h1

end GlobalTheory.CuspGeneric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnrCrysAtRangePrime
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubX

theorem unrCrysAtRangePrime : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (L : SizeData₂ D) (X : KillingConditions.HubData D), (∀ i, GoodR D.nd i (X.r i)) → SumRepresentations.tie0 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → AdmissibleParameterJ.DeRhamFamilyAway D → GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D → GlobalTheory.HubX.MuUnr D → ∀ i : D.nd.Loc, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (D.nbr i w hw).Kw.1 ≤ Loc.MaximalUnramifiedExtension (D.nd.l i)) ∧ ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), C.IsGood → ∀ x : D.nd.X i, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i (X.r i) x))) := by
  intro hF D L X hgood ht0 ha2 ha5 hG2 hpar hmu i _ hg hR _
  obtain ⟨h23, hqd, -⟩ := hR
  have hchi := GlobalTheory.T.chi_one_away_from_type hF D ht0 ha2 ha5 hpar hmu i hg
  have hg0 : D.nd.l i ≠ D.host.g 0 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hg1 : D.nd.l i ≠ D.host.g 1 := fun h => hg (by simp [TwistedPlaces.gset, h])
  refine ⟨GlobalTheory.T.hostCompletion_le_maxUnramified_padic D i (fun h => h23 (Or.inl h)) (fun h => hqd (Or.inl h)) (fun h => hqd (Or.inr h)), ?_⟩
  intro w hw C _ x
  exact GlobalTheory.T.crystalline_local_coefficients hF D i (X.r i) (hgood i) (hG2 i (X.r i) (hgood i)) hg0 hg1 hchi w hw C x

end GlobalTheory.HubX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedTrivialLocal
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.UnramifiedTrivial

theorem unramifiedCocycles_le_blochKatoFinite_trivial {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
    (T : LocTied l P AI) (K LL : FinExt l) :
    Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K) ≤
      finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) := by
  intro c hc
  obtain ⟨hZ, x, hx⟩ := hc
  refine ⟨hZ, ?_⟩
  obtain ⟨hcont, hadd⟩ := hZ
  haveI := LL.2
  let v := Module.finBasis ℚ_[l] ↥LL.1
  have hI : ∀ g ∈ IK K, c g = 0 := fun g hg => by simpa using hx g hg
  have hex : ∀ i, ∃ b : P.R.B, ∀ g : ↥(GK K),
      P.actQ g b - b = algebraMap ℚ_[l] _ (v.coord i (c g)) := fun i =>
    GlobalTheory.UnramifiedCrys.exists_rat AI T K (fun g => v.coord i (c g))
      ((v.coord i).continuous_of_finiteDimensional.comp hcont)
      (fun g h => by rw [hadd, map_add]; rfl) (fun g hg => by rw [hI g hg, map_zero])
  choose b hb using hex
  refine ⟨∑ i, v i ⊗ₜ[ℚ_[l]] b i, fun g => ?_⟩
  rw [map_sum, ← Finset.sum_sub_distrib]
  conv_lhs => rw [← v.sum_repr (c g), TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : actVB (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) g (v i ⊗ₜ[ℚ_[l]] b i) =
      v i ⊗ₜ[ℚ_[l]] P.actQ g (b i) := by
    rw [← P.PD_actB]
    rfl
  rw [h1, ← TensorProduct.tmul_sub, hb, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  rfl

theorem Z1ur_ne_bot {l : ℕ} [Fact l.Prime] (K LL : FinExt l) :
    Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K) ≠ ⊥ := by
  obtain ⟨δ, hδc, hδa, hδI, g₀, hg₀⟩ := GlobalTheory.UnramZl.exists_unramified_character l K
  haveI := LL.2
  let c : ↥(GK K) → ↥LL.1 := fun g => algebraMap ℚ_[l] ↥LL.1 (δ g)
  have hcc : Continuous c :=
    (Algebra.linearMap ℚ_[l] ↥LL.1).continuous_of_finiteDimensional.comp hδc
  have hmem : c ∈ Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K) := by
    refine ⟨⟨hcc, fun g h => ?_⟩, 0, fun g hg => ?_⟩
    · simp [c, hδa, map_add]
    · simp [c, hδI g hg]
  intro h
  rw [h] at hmem
  have := congrFun ((Submodule.mem_bot _).1 hmem) g₀
  exact hg₀ (by simpa [c] using this)

end GlobalTheory.UnramifiedTrivial

namespace GlobalTheory.UnramifiedTrivial
theorem finrank_Z1f_trivial {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) :
    finrank ↥LL.1 ↥(finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) =
      finrank ↥LL.1 (FiniteCohomology (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) := by
  have hB1 : B1 (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, rfl⟩
    ext g
    simp [cob]
  have hc : (B1 (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)).comap
      (finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)).subtype = ⊥ := by
    rw [hB1, Submodule.comap_bot, Submodule.ker_subtype]
  exact (Submodule.quotEquivOfEqBot _ hc).finrank_eq.symm
end GlobalTheory.UnramifiedTrivial

namespace GlobalTheory.UnramifiedTrivial
theorem unrTriv_of_finrank {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)
    (T : LocTied l P AI) (K LL : FinExt l)
    (h1 : finrank ↥LL.1 (FiniteCohomology (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) = 1) :
    UnrTriv (P.PD K) (LL := ↥LL.1) (IK K) := by
  have hZ : finrank ↥LL.1 ↥(finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) = 1 :=
    (finrank_Z1f_trivial P K LL).trans h1
  haveI : FiniteDimensional ↥LL.1 ↥(finiteCocycles (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) :=
    Module.finite_of_finrank_eq_succ hZ
  have hle := unramifiedCocycles_le_blochKatoFinite_trivial AI T K LL
  haveI := Submodule.finiteDimensional_of_le hle
  have hpos : 0 < finrank ↥LL.1 ↥(Z1ur (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1) (IK K)) := by
    refine Nat.pos_of_ne_zero fun h0 => Z1ur_ne_bot K LL ?_
    exact Submodule.finrank_eq_zero.1 h0
  unfold UnrTriv
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [hZ]; exact hpos)).symm
end GlobalTheory.UnramifiedTrivial

namespace GlobalTheory.UnramifiedTrivial

theorem unrTriv : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K LL : FinExt l), UnrTriv (P.PD K) (LL := ↥LL.1) (IK K) := by
  intro l _ P AI T K LL
  haveI := LL.2
  obtain ⟨hgood, -⟩ := GlobalTheory.LocalIntegers.good_integers l LL
  let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := ↥LL.1
      ρ := 1
      cont := fun x => (continuous_const : Continuous fun _ : ↥(GK K) => x) }
  have hDR : IsDR (P.PD K) A.ρ := GlobalTheory.CrysExt.isDR_trivial (P.PD K)
  obtain ⟨hfin, hdim⟩ := GlobalTheory.T.finrank_H1f_de_rham l P AI T K ↥LL.1 ↥(OL LL) hgood A hDR
  have hH0 : H0V A.ρ = ⊤ := by
    refine eq_top_iff.2 fun x _ => (Submodule.mem_iInf _).2 fun g => ?_
    simp [A, H0V]
  have hFil : DdR (P.PD K) A.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := A.V) 0 = DdR (P.PD K) A.ρ := by
    refine inf_eq_left.2 fun x hx => ?_
    change x ∈ DdR (P.PD K) (Representation.trivial ↥LL.1 ↥(GK K) ↥LL.1) at hx
    rw [GlobalTheory.CrysExt.ddR_trivial] at hx
    obtain ⟨z, rfl⟩ := hx
    exact GlobalTheory.CrysExt.incl_mem_FilV (P.PD K) le_rfl z
  have e1 : finrank ↥LL.1 ↥(H0V A.ρ) = 1 := by rw [hH0, finrank_top]; exact Module.finrank_self _
  have e2 : finrank ↥LL.1 ↥(DdR (P.PD K) A.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := A.V) 0) = finrank ↥LL.1 ↥(DdR (P.PD K) A.ρ) := by rw [hFil]
  have h1' : finrank ↥LL.1 (FiniteCohomology (P.PD K) A.ρ) = 1 := by omega
  have h1 : finrank ↥LL.1 (FiniteCohomology (P.PD K) (1 : Representation ↥LL.1 ↥(GK K) ↥LL.1)) = 1 := h1'
  exact unrTriv_of_finrank AI T K LL h1

end GlobalTheory.UnramifiedTrivial
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XNygaardExtComesFromBaseFieldStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.X_nygaard_ext_comes_from_base_field : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL) (hle : K.1 ≤ K'.1), K0 K' = K0 K → ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (z' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)), z' ∈ aN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').X → ∃ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X, ((F l).E K s LL h).tie.jD T z = toTW hle T (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) z') := by
  first | exact @GlobalTheory.NL.XNTransfer.main | exact GlobalTheory.NL.XNTransfer.main | (intros; apply GlobalTheory.NL.XNTransfer.main <;> assumption)
end

