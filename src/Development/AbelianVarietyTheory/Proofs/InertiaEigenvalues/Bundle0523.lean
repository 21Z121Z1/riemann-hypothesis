import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0490
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0099
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0373
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0499
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0070
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0323
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0370
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0491
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentCoefficientsAinfModPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_descent_coefficients_ainf_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' n : ℕ) (R : Matrix (Fin d) (Fin d') (WCb l)) (x : Fin d → WCb l) (a : Fin d' → Ainf l), (∀ i j, R i j ∈ bk.OE) → (∀ i, x i ∈ bk.OE) → (∀ i, (l : WCb l) ^ n ∣ (x - R *ᵥ fun j => inclW l (a j)) i) → ∃ s : Fin d' → bk.S, ∀ i, (l : WCb l) ^ n ∣ (x - R *ᵥ fun j => bk.evW (s j)) i := by
  first | exact @GlobalTheory.descentCoefficients | exact GlobalTheory.descentCoefficients | (intros; apply GlobalTheory.descentCoefficients <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopePointFactorsThroughSection
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isHausdorff_of_le_ideal {R : Type} [CommRing R] {I J : Ideal R} (h : I ≤ J) (hJ : IsHausdorff J R) :
    IsHausdorff I R := by
  refine ⟨fun x hx => hJ.haus x fun n => ?_⟩
  have h1 := hx n
  rw [SModEq.sub_mem] at h1 ⊢
  exact Submodule.smul_mono_left (Ideal.pow_right_mono h n) h1

theorem map_frobenius_charP {l : ℕ} [Fact l.Prime] {R O : Type} [CommRing R] [CharP R l] [CommRing O] [CharP O l]
    (ψ : R →+* O) (x : WittVector l R) :
    WittVector.map ψ (WittVector.frobenius x) = WittVector.frobenius (WittVector.map ψ x) := by
  ext n
  rw [WittVector.map_coeff, WittVector.coeff_frobenius_charP, WittVector.coeff_frobenius_charP,
    WittVector.map_coeff, map_pow]

theorem hom_comp_apply {l : ℕ} {R : Type} [CommRing R] {P P' P'' : Obj l R} (g : Hom P' P'') (f : Hom P P')
    (a : P.A) : (g.comp f).f a = g.f (f.f a) := rfl

theorem hom_eq_id_apply {l : ℕ} {R : Type} [CommRing R] {P P' : Obj l R} (g : Hom P' P) (f : Hom P P')
    (h : g.comp f = Hom.id P) (a : P.A) : g.f (f.f a) = a := by
  rw [← hom_comp_apply, h]; rfl

theorem hom_eq_comp_apply {l : ℕ} {R : Type} [CommRing R] {P P' P'' Q : Obj l R} (g : Hom P' P'') (f : Hom P P')
    (g' : Hom Q P'') (f' : Hom P Q) (h : g.comp f = g'.comp f') (a : P.A) : g.f (f.f a) = g'.f (f'.f a) := by
  rw [← hom_comp_apply, h]; rfl

theorem mapE_facts {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) (O : Type) [CommRing O] [IsDomain O]
    [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O) (hx0 : ψ bk.flat ≠ 0)
    (hxu : ¬ IsUnit (ψ bk.flat)) (hxc : IsAdicComplete (Ideal.span {ψ bk.flat}) O) :
    WittVector.map ψ (bk.ev bk.E) ∈ nonZeroDivisors (WittVector l O) ∧
    IsHausdorff ((Ideal.span {((l : ℕ) : WittVector l (OCb l))} ⊔ Ideal.span {bk.ev bk.E}).map (WittVector.map ψ))
      (WittVector l O) := by
  obtain ⟨w, -, hwE⟩ := GlobalTheory.T.breuilKisin_eisenstein_image_teichmuller_pow l K bk O ψ hxu
  have hE0 : WittVector.map ψ (bk.ev bk.E) ≠ 0 := fun h => by
    have h1 := congrArg (WittVector.constantCoeff (p := l) (R := O)) h
    rw [hwE, map_add, map_mul, map_pow, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero,
      WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, map_zero] at h1
    exact hx0 ((pow_eq_zero_iff bk.deg_pos.ne').1 h1)
  refine ⟨mem_nonZeroDivisors_of_ne_zero hE0, isHausdorff_of_le_ideal ?_
    (GlobalTheory.T.wittVector_teichmuller_isAdicComplete_of_perfect l O (ψ bk.flat) hx0 hxc).2.toIsHausdorff⟩
  rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_natCast]
  refine sup_le le_sup_left ?_
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, hwE]
  exact Ideal.add_mem _ (Ideal.mem_sup_right (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ bk.deg_pos))
    (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

theorem isHausdorff_map_congr {A B : Type} [CommRing A] [CommRing B] {I J : Ideal A} {g h : A →+* B} (hIJ : I = J)
    (hgh : g = h) (H : IsHausdorff (J.map h) B) : IsHausdorff (I.map g) B := by
  subst hIJ; subst hgh; exact H

theorem envPoint_eq {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X))
    (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O)
    (hx0 : ψ bk.flat ≠ 0) (hxu : ¬ IsUnit (ψ bk.flat)) (hxc : IsAdicComplete (Ideal.span {ψ bk.flat}) O)
    (F : En.Q.A →+* WittVector l O) (hFφ : ∀ a, F (En.Q.D.φ a) = WittVector.frobenius (F a))
    (hFinl : F.comp En.inl.f = WittVector.map ψ) (s : Hom En.Q (ainfObj K)) (hs1 : s.comp En.inl = Hom.id _)
    (hinr : F (BK.hf En.inr X) = WittVector.map ψ (s.f (BK.hf En.inr X))) (a : En.Q.A) :
    F a = WittVector.map ψ (s.f a) := by
  have hFi : ∀ b : WittVector l (OCb l), F (En.inl.f b) = WittVector.map ψ b := fun b => RingHom.congr_fun hFinl b
  have htfW : ∀ c : WittVector l O, ((l : ℕ) : WittVector l O) * c = 0 → c = 0 := fun c hc =>
    WittVector.eq_zero_of_p_mul_eq_zero c (by rw [mul_comm, hc])
  obtain ⟨F', hF'a⟩ : ∃ F' : En.Q.A →+* WittVector l O, ∀ a, F' a = WittVector.map ψ (s.f a) :=
    ⟨(WittVector.map ψ).comp s.f, fun _ => rfl⟩
  have hF'φ : ∀ a, F' (En.Q.D.φ a) = WittVector.frobenius (F' a) := fun a =>
    ((hF'a _).trans (congrArg (WittVector.map ψ) (Hom.f_φ s a))).trans
      ((map_frobenius_charP ψ (s.f a)).trans (congrArg WittVector.frobenius (hF'a a).symm))
  have hinl : ∀ b, F (En.inl.f b) = F' (En.inl.f b) := fun b =>
    (hFi b).trans ((congrArg (WittVector.map ψ) (hom_eq_id_apply s En.inl hs1 b).symm).trans (hF'a _).symm)
  have hE := (mapE_facts bk O ψ hx0 hxu hxc).1
  have hH := (mapE_facts bk O ψ hx0 hxu hxc).2
  have hnzd : F (En.inl.f (bk.ev bk.E)) ∈ nonZeroDivisors (WittVector l O) := by
    rw [hFi]; exact hE
  have hI : (ainfObj K).I = Ideal.span {bk.ev bk.E} := bk.span_ev.symm
  have hhaus : IsHausdorff ((Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ (ainfObj K).I).map (F.comp En.inl.f))
      (WittVector l O) :=
    isHausdorff_map_congr (congrArg (Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ ·) hI) hFinl hH
  have hFF : F = F' :=
    GlobalTheory.T.breuilKisinPrismCoproduct_hom_eq_of_agree l K bk (ainfObj K) (bk.ev bk.E) (bk.ev X) En (WittVector l O) WittVector.frobenius F F'
      htfW hFφ hF'φ hinl (hinr.trans (hF'a _).symm) hnzd hhaus
  rw [hFF, hF'a]

theorem envPoint_factors : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K)
    (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharP O l] [PerfectRing O l] (f : En.Q.A →+* O), f (En.inl.f (bk.ev X)) ≠ 0 →
    ¬ IsUnit (f (En.inl.f (bk.ev X))) → IsAdicComplete (Ideal.span {f (En.inl.f (bk.ev X))}) O →
    ∃ (g : ↥(GK K)) (s : Hom En.Q (ainfObj K)) (ψ : OCb l →+* O), s.comp En.inl = Hom.id _ ∧
      s.comp En.inr = (ainfHom K g).comp bk.ι ∧
      ∀ a, f a = ψ (WittVector.coeff (p := l) (R := OCb l) (s.f a) 0) := by
  intro l _ K bk En O _ _ _ _ _ f hx0 hxu hxc
  have hcc : Function.Surjective (WittVector.constantCoeff (p := l) (R := OCb l)) := fun y =>
    ⟨WittVector.teichmuller l y, by rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩
  let f0 : WittVector l (OCb l) →+* O := f.comp En.inl.f
  have hker : RingHom.ker (WittVector.constantCoeff (p := l) (R := OCb l)) ≤ RingHom.ker f0 := by
    rw [WittVector.ker_constantCoeff, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      map_natCast, CharP.cast_eq_zero]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : OCb l →+* O, ∀ a : WittVector l (OCb l), f (En.inl.f a) = ψ (a.coeff 0) :=
    ⟨RingHom.liftOfSurjective _ hcc ⟨f0, hker⟩, fun a =>
      (RingHom.liftOfSurjective_comp_apply _ hcc ⟨f0, hker⟩ a).symm⟩
  have hflat : f (En.inl.f (bk.ev X)) = ψ bk.flat := by
    rw [hψ, bk.ev_X, WittVector.teichmuller_coeff_zero]
  rw [hflat] at hx0 hxu hxc
  obtain ⟨htf, -, -⟩ := GlobalTheory.T.ainf_envelope_mod_prime_properties l K bk En
  obtain ⟨F, hF0, hFφ⟩ := GlobalTheory.T.exists_frobenius_compatible_wittVector_lift l En.Q.A En.Q.D.φ
    (fun a => ⟨En.Q.D.δ a, by rw [En.Q.D.φ_eq]; ring⟩) htf O f
  have hFinl : F.comp En.inl.f = WittVector.map ψ :=
    GlobalTheory.T.wittVector_ringHom_eq_map_of_coeff_zero l (OCb l) O (F.comp En.inl.f) ψ (fun a => (hF0 (En.inl.f a)).trans (hψ a))
  have hFi : ∀ b : WittVector l (OCb l), F (En.inl.f b) = WittVector.map ψ b := fun b => RingHom.congr_fun hFinl b

  have hφX : En.Q.D.φ (BK.hf En.inr X) = BK.hf En.inr X ^ l :=
    calc En.Q.D.φ (BK.hf En.inr X) = BK.hf En.inr (frobS l bk.a X) := (Hom.f_φ En.inr X).symm
      _ = BK.hf En.inr (X ^ l) := by rw [frobS_X]
      _ = _ := map_pow _ _ _
  set v := F (BK.hf En.inr X) with hvdef
  have hv : WittVector.frobenius v = v ^ l := by
    rw [hvdef, ← hFφ, hφX, map_pow]
  have hvt := GlobalTheory.T.wittVector_eq_teichmuller_of_frobenius_eq_pow_self l O v hv
  have e1 : F (En.inl.f (bk.ev X)) = WittVector.teichmuller l (ψ bk.flat) := by
    rw [hFi, bk.ev_X, WittVector.map_teichmuller]
  have e2 : F (En.inl.f (bk.ev bk.E)) = WittVector.map ψ (bk.ev bk.E) := hFi _
  have h1 : v = F (En.inl.f (bk.ev X)) + F (En.inl.f (bk.ev bk.E)) * F En.w := by
    have := congrArg F En.w_eq
    rwa [map_add, map_mul] at this
  rw [e1, e2] at h1
  have hdvd : WittVector.map ψ (bk.ev bk.E) ∣
      WittVector.teichmuller l (v.coeff 0) - WittVector.teichmuller l (ψ bk.flat) :=
    ⟨F En.w, by rw [← hvt]; linear_combination h1⟩
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_galois_conj_of_teichmuller_congr l K bk O ψ hx0 hxu hxc (v.coeff 0) hdvd
  obtain ⟨s, ⟨hs1, hs2⟩, -⟩ := En.univ (ainfObj K) (Hom.id _) ((ainfHom K g).comp bk.ι)

  have hinr : F (BK.hf En.inr X) = WittVector.map ψ (s.f (BK.hf En.inr X)) := by
    have h2 : s.f (BK.hf En.inr X) = Per.σA (g : GQ l) (bk.ev X) :=
      hom_eq_comp_apply s En.inr _ _ hs2 X
    have h3 : WittVector.map ψ (Per.σA (g : GQ l) (bk.ev X)) =
        WittVector.teichmuller l (ψ (Per.σF (g : GQ l) bk.flat)) := by
      rw [bk.ev_X, GlobalTheory.RingIface.sigA_teich, WittVector.map_teichmuller]
    refine Eq.trans ?_ ((congrArg (WittVector.map ψ) h2).trans h3).symm
    exact hvdef.symm.trans (hvt.trans (congrArg (WittVector.teichmuller l) hg))
  refine ⟨g, s, ψ, hs1, hs2, fun a => ?_⟩
  rw [← hF0, envPoint_eq bk En O ψ hx0 hxu hxc F hFφ hFinl s hs1 hinr a]
  exact WittVector.map_coeff ψ (s.f a) 0

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHomEisensteinSpanAndNonZeroDivisorStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (g : Hom bk.prism B), B.I = Ideal.span {BK.hf g bk.E} ∧ BK.hf g bk.E ∈ nonZeroDivisors B.A := by
  first | exact @GlobalTheory.BSP.hf_E_span_and_regular | exact GlobalTheory.BSP.hf_E_span_and_regular | (intros; apply GlobalTheory.BSP.hf_E_span_and_regular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEStabilityProperties
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.OEStable

variable {l : ℕ} [hl : Fact l.Prime]

theorem perfect_Cb : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  refine ⟨algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm a) /
    algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm b), ?_⟩
  rw [frobenius_def, div_pow, ← map_pow (algebraMap (OCb l) (Cb l)),
    ← map_pow (algebraMap (OCb l) (Cb l)), frobeniusEquiv_symm_pow_p,
    frobeniusEquiv_symm_pow_p]

theorem eq_zero_of_forall_dvd (z : WCb l) (h : ∀ n, ((l : ℕ) : WCb l) ^ n ∣ z) : z = 0 := by
  ext m
  obtain ⟨y, hy⟩ := h (m + 1)
  rw [hy, mul_comm, WittVector.mul_pow_charP_coeff_zero _ (Nat.lt_succ_self m)]
  simp

private theorem sigmaA_eq_map_pt (g : GQ l) (a : Ainf l) : Per.σA g a = WittVector.map (Per.σF g) a := by
  apply GlobalTheory.Prism.inclW_injective
  rw [← galW_inclW]
  exact WittVector.ext fun n => autCb_alg l (galTilt l g) (a.coeff n)

variable {K : FinExt l} (bk : BK K)

theorem sat (w : WCb l) (hw : ((l : ℕ) : WCb l) * w ∈ bk.OE) : w ∈ bk.OE := by
  haveI := perfect_Cb (l := l)
  obtain ⟨ek, pr, hek, hinj, -, -⟩ := GlobalTheory.T.exists_residueTilt_injective_retract l K bk
  intro n
  obtain ⟨m, s, y, h⟩ := hw (n + 1)
  have h0 : (bk.evW s).coeff 0 = 0 := by
    have e : bk.evW s = (bk.evW X ^ m * w - ((l : ℕ) : WCb l) ^ n * y) * ((l : ℕ) : WCb l) := by
      linear_combination -h
    rw [e, WittVector.mul_charP_coeff_zero]
  have h1 : (bk.ev s).coeff 0 = 0 := by
    have e : (bk.evW s).coeff 0 = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := WittVector.map_coeff _ _ _
    rw [e] at h0
    exact IsFractionRing.injective (OCb l) (Cb l) (h0.trans (map_zero _).symm)
  have h2 : PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) s = 0 :=
    hinj (by rw [hek, h1, map_zero])
  have h3 : ∀ i, ∃ c : Wq l bk.a, coeff i s = ((l : ℕ) : Wq l bk.a) * c := fun i => by
    have h4 := congrArg (coeff i) h2
    rw [coeff_map, map_zero] at h4
    have h5 : coeff i s ∈ RingHom.ker (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) := h4
    rw [WittVector.ker_constantCoeff, Ideal.mem_span_singleton] at h5
    exact h5
  choose c hc using h3
  have h5 : s = ((l : ℕ) : bk.S) * PowerSeries.mk c := by
    ext i
    rw [hc, ← map_natCast (C (R := Wq l bk.a)) l, coeff_C_mul, coeff_mk]
  refine ⟨m, PowerSeries.mk c, y, ?_⟩
  apply sub_eq_zero.1
  apply WittVector.eq_zero_of_p_mul_eq_zero
  rw [h5, map_mul, map_natCast] at h
  linear_combination h

theorem closed (w : WCb l) (h : ∀ n : ℕ, ∃ v ∈ bk.OE, ((l : ℕ) : WCb l) ^ n ∣ w - v) : w ∈ bk.OE := by
  intro n
  obtain ⟨v, hv, z, hz⟩ := h n
  obtain ⟨m, s, y, hy⟩ := hv n
  exact ⟨m, s, y + bk.evW X ^ m * z, by linear_combination hy + bk.evW X ^ m * hz⟩

theorem frob (w : WCb l) (hw : w ∈ bk.OE) : frobW l w ∈ bk.OE := by
  intro n
  obtain ⟨m, s, y, h⟩ := hw n
  have key : ∀ t : bk.S, frobW l (bk.evW t) = bk.evW (frobS l bk.a t) := fun t => by
    rw [BK.evW, RingHom.comp_apply, RingHom.comp_apply, frobW_inclW, bk.ev_frob]
  refine ⟨l * m, frobS l bk.a s, frobW l y, ?_⟩
  have h' := congrArg (frobW l) h
  simp only [map_mul, map_add, map_pow, map_natCast, key, frobS_X] at h'
  rw [pow_mul]
  linear_combination h'

theorem gal (g : ↥(GK K)) (hg : bk.FixFlat g) (w : WCb l) (hw : w ∈ bk.OE) : galW l (g : GQ l) w = w := by
  obtain ⟨-, -, -, hflat, -, hcomp, -⟩ := GlobalTheory.T.ainf_divisibility_breuilKisin_facts l K bk
  haveI := (GlobalTheory.T.wittVector_teichmuller_isAdicComplete_of_perfect l (OCb l) bk.flat hflat hcomp).1
  have hteich : Per.σA (g : GQ l) (WittVector.teichmuller l bk.flat) = WittVector.teichmuller l bk.flat := by
    rw [sigmaA_eq_map_pt, WittVector.map_teichmuller]
    exact congrArg _ hg
  have hfix : (Per.σA (g : GQ l)).comp bk.ev = bk.ev := by
    refine ringHom_ext_of_sep _ _ (fun r => ?_) ?_ ?_
    · rw [RingHom.comp_apply, bk.ev_C, bk.gal_w]
    · rw [RingHom.comp_apply, bk.ev_X, hteich]
    · intro x hx
      rw [RingHom.comp_apply, bk.ev_X, hteich] at hx
      refine IsHausdorff.haus' (I := Ideal.span {WittVector.teichmuller l bk.flat}) x fun n => ?_
      simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact hx n
  have hW : ∀ t : bk.S, galW l (g : GQ l) (bk.evW t) = bk.evW t := fun t => by
    change galW l _ (inclW l (bk.ev t)) = inclW l (bk.ev t)
    rw [galW_inclW, ← RingHom.comp_apply (Per.σA _) bk.ev, hfix]
  obtain ⟨-, -, hu, -, -⟩ := GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field l K bk
  apply sub_eq_zero.1
  apply eq_zero_of_forall_dvd
  intro n
  obtain ⟨m, s, y, h⟩ := hw n
  have h' := congrArg (galW l (g : GQ l)) h
  simp only [map_mul, map_add, map_pow, map_natCast, hW] at h'
  obtain ⟨u, hu'⟩ := hu.pow m
  have e : (u : WCb l) * (galW l (g : GQ l) w - w) =
      ((l : ℕ) : WCb l) ^ n * (galW l (g : GQ l) y - y) := by
    rw [hu']; linear_combination h' - h
  refine ⟨(↑u⁻¹ : WCb l) * (galW l (g : GQ l) y - y), ?_⟩
  calc galW l (g : GQ l) w - w = (↑u⁻¹ : WCb l) * ((u : WCb l) * (galW l (g : GQ l) w - w)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [e]; ring

theorem inv (w : WCb l) (hw : w ∈ bk.OE) (hu : IsUnit w) : ∃ w' ∈ bk.OE, w * w' = 1 := by
  haveI := perfect_Cb (l := l)
  obtain ⟨-, -, -, -, hinv⟩ := GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field l K bk
  obtain ⟨u, rfl⟩ := hu
  have hy : WittVector.constantCoeff (p := l) (R := Cb l) u ∈
      bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) := Subring.mem_map.2 ⟨u, hw, rfl⟩
  obtain ⟨v, hv, hvy⟩ := Subring.mem_map.1 (hinv _ hy)
  have hne : WittVector.constantCoeff (p := l) (R := Cb l) u ≠ 0 := by
    intro h0
    have h1 := congrArg (WittVector.constantCoeff (p := l) (R := Cb l)) u.mul_inv
    rw [map_mul, h0, zero_mul, map_one] at h1
    exact zero_ne_one h1
  have h1 : (u : WCb l) * v - 1 ∈ RingHom.ker (WittVector.constantCoeff (p := l) (R := Cb l)) := by
    rw [RingHom.mem_ker, map_sub, map_mul, hvy, map_one, mul_inv_cancel₀ hne, sub_self]
  rw [WittVector.ker_constantCoeff, Ideal.mem_span_singleton] at h1
  obtain ⟨z, hz⟩ := h1
  have hz' : z ∈ bk.OE := sat bk z (by
    rw [← hz]; exact sub_mem (mul_mem hw hv) (one_mem _))
  have huv : (u : WCb l) * v = 1 - (-((l : ℕ) : WCb l) * z) := by linear_combination hz
  have hi : (↑u⁻¹ : WCb l) * u = 1 := Units.inv_mul u
  refine ⟨↑u⁻¹, closed bk _ fun n => ⟨v * ∑ i ∈ Finset.range n, (-((l : ℕ) : WCb l) * z) ^ i,
    mul_mem hv (sum_mem fun i _ => pow_mem (mul_mem (neg_mem (natCast_mem _ l)) hz') i),
    ⟨(↑u⁻¹ : WCb l) * (-z) ^ n, ?_⟩⟩, u.mul_inv⟩
  have hgeom := geom_sum_mul_neg (-((l : ℕ) : WCb l) * z) n
  have hq : (-((l : ℕ) : WCb l) * z) ^ n = ((l : ℕ) : WCb l) ^ n * (-z) ^ n := by
    rw [neg_mul, ← mul_neg, mul_pow]
  linear_combination (-(↑u⁻¹ : WCb l)) * hgeom - ((↑u⁻¹ : WCb l) * ∑ i ∈ Finset.range n,
    (-((l : ℕ) : WCb l) * z) ^ i) * huv + (v * ∑ i ∈ Finset.range n, (-((l : ℕ) : WCb l) * z) ^ i) * hi
    - (↑u⁻¹ : WCb l) * hq

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ w : WCb l, ((l : ℕ) : WCb l) * w ∈ bk.OE → w ∈ bk.OE) ∧ (∀ w : WCb l, (∀ n : ℕ, ∃ v ∈ bk.OE, ((l : ℕ) : WCb l) ^ n ∣ w - v) → w ∈ bk.OE) ∧ (∀ w ∈ bk.OE, frobW l w ∈ bk.OE) ∧ (∀ g : ↥(GK K), bk.FixFlat g → ∀ w ∈ bk.OE, galW l (g : GQ l) w = w) ∧ ∀ w ∈ bk.OE, IsUnit w → ∃ w' ∈ bk.OE, w * w' = 1 := by
  intro l _ K bk
  exact ⟨sat bk, closed bk, frob bk, fun g hg w hw => gal bk g hg w hw, inv bk⟩

end GlobalTheory.OEStable
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPartCOfPartAPartBFiniteLevelStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_partC_of_partA_partB_finite_level : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l, bkACore (P.PD K) → bkBCore (P.PD K) → Formalism.MainNotions.LocalSituation.bkC (P.PD K) := by
  first | exact @GlobalTheory.BKFinLevel.bkC_of_bkA_bkB | exact GlobalTheory.BKFinLevel.bkC_of_bkA_bkB | (intros; apply GlobalTheory.BKFinLevel.bkC_of_bkA_bkB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZero
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP

theorem ne_one_of_isEps {l : ℕ} [hl : Fact l.Prime] {ε : OCb l} (hε : GlobalTheory.MemLoc.IsEps ε) : ε ≠ 1 := by
  rintro rfl
  exact hε.2 (by simp)

theorem coeff_zero_ne_zero_of_isPer {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) {τ : Ainf l}
    (hτ : bk.IsPer τ) : τ.coeff 0 ≠ 0 := by
  obtain ⟨-, ε, η, hε, hφ⟩ := hτ
  intro h
  have h1 := congrArg (WittVector.constantCoeff (p := l) (R := OCb l)) hφ
  simp only [map_mul, map_sub, map_one, WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP,
    WittVector.teichmuller_coeff_zero, h] at h1
  rw [zero_pow hl.out.ne_zero] at h1
  have hη : (η : Ainf l).coeff 0 ≠ 0 := by
    have := η.isUnit.map (WittVector.constantCoeff (p := l) (R := OCb l))
    rw [WittVector.constantCoeff_apply] at this
    exact this.ne_zero
  exact mul_ne_zero hη (sub_ne_zero.2 (ne_one_of_isEps hε)) h1.symm

theorem ρ₀_pos_lt_one {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have hl1 : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < 1 / (bk.Ep.natDegree : ℝ) := one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)
  exact ⟨NNReal.rpow_pos (zero_lt_one.trans hl1), NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (neg_neg_of_pos he)⟩

theorem isUnit_inclW_of_isPer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    IsUnit (inclW l τ) ∧ bk.iA τ ≠ 0 ∧ τ ≠ 0 ∧ ∀ g : GQ l, IsUnit (inclW l (Per.σA g τ)) := by
  intro l _ K bk τ hτ
  have h0 := coeff_zero_ne_zero_of_isPer bk hτ
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    exact h0 (WittVector.zero_coeff _ _ _)
  have hU : IsUnit (inclW l τ) := by
    refine WittVector.isUnit_of_coeff_zero_ne_zero _ ?_
    rw [inclW, WittVector.map_coeff]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 h0
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ (ρ₀_pos_lt_one bk).1 (ρ₀_pos_lt_one bk).2).1
  refine ⟨hU, fun h => hτ0 (hinj (h.trans (map_zero _).symm)), hτ0, fun g => ?_⟩
  rw [← galW_inclW]
  exact hU.map (galW l g)

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCoproductFaithfullyFlatModAdicPoStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinPrismCoproduct_faithfullyFlat_mod_adic_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (t p : B.A) (En : Env bk B t p) (m : ℕ), (qmap En.inl m).FaithfullyFlat := by
  first | exact @GlobalTheory.BSP.envFF | exact GlobalTheory.BSP.envFF | (intros; apply GlobalTheory.BSP.envFF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCoproductIsPushoutBaseChangeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinPrismCoproduct_isPushout_base_change : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B B' : Obj l ↥(OL K)) (t p : B.A) (k : Hom B B') (En : Env bk B t p) (En' : Env bk B' (k.f t) (k.f p)), ∃ k' : Hom En.Q En'.Q, IsPO En.inl k k' En'.inl := by
  first | exact @GlobalTheory.BSP.env_isPO | exact GlobalTheory.BSP.env_isPO | (intros; apply GlobalTheory.BSP.env_isPO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCrystalBasisAndSpanStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinPrism_crystal_basis_and_span : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∃ b : ι → E.M (ϖ.prism a), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) ∧ ∀ x : E.M (ϖ.prism a), ∃ (N : ℕ) (c : ι → Fin N → O) (s : ι → Fin N → (ϖ.prism a).A), x = ∑ j, ∑ q, s j q • (oE (c j q)).u (ϖ.prism a) (b j) := by
  first | exact @GlobalTheory.BKBasis.main | exact GlobalTheory.BKBasis.main | (intros; apply GlobalTheory.BKBasis.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismHomsAgreeWittAndModIdealStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinPrism_homs_agree_witt_and_mod_ideal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), (∀ w, BK.hf f (PowerSeries.C w) = BK.hf g (PowerSeries.C w)) ∧ BK.hf f X - BK.hf g X ∈ B.I ∧ B.I = Ideal.span {BK.hf f bk.E} := by
  first | exact @GlobalTheory.BSP.IdealSubMembership.main | exact GlobalTheory.BSP.IdealSubMembership.main | (intros; apply GlobalTheory.BSP.IdealSubMembership.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CMemDeltaCommuteLocusSubringOfIsHausdorffStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.C_mem_deltaCommuteLocusSubring_of_isHausdorff : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Type) [CommRing C] (DC : Delta l C) (J : Ideal C), (l : C) ∈ J → IsHausdorff J C → ∀ σ : (Wq l a)⟦X⟧ →+* C, ∀ w : Wq l a, PowerSeries.C w ∈ δLocus (deltaS l a) DC σ := by
  first | exact @GlobalTheory.BSP.C_mem_δLocus_of_hausdorff | exact GlobalTheory.BSP.C_mem_δLocus_of_hausdorff | (intros; apply GlobalTheory.BSP.C_mem_δLocus_of_hausdorff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeWildJumpSumOfElementaryAbelianStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_le_wildJumpSum_of_elementaryAbelian : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → A ≤ lowerRamificationGroup K L 0 → OrdIs L p E → (∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ B) → (∀ σ ∈ A, σ ^ p ∈ B) → ¬ A ≤ B → Nat.card ↥A ≤ jumpSum (wild K L) A B := by
  first | exact @GlobalTheory.PMon.Ram.card_le_jumpSum_wild | exact GlobalTheory.PMon.Ram.card_le_jumpSum_wild | (intros; apply GlobalTheory.PMon.Ram.card_le_jumpSum_wild <;> assumption)
end

