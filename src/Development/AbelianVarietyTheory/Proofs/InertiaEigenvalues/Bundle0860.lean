import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0844
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0386
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0499
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0817
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0847

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesIntegralSourceTranslationRightMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries.DualType

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SourceTrans

variable {D : D7}

theorem idem_mul_idemAt {Q : Finset (Pl D.host.E)} (hQ : SplitSet Q) {PP : Pl D.host.E} (hP : PP ∈ Q) :
    (idem Q + cA D (idem Q)) * (idemAt PP + cA D (idemAt PP)) = idemAt PP + cA D (idemAt PP) := by
  have he : idemAt PP * idemAt PP = idemAt PP := (hQ.isIdemAt hP).1.1
  have h1 : idem Q * idemAt PP = idemAt PP := by
    rw [idem, Finset.sum_mul, Finset.sum_eq_single PP (fun q hq hne => hQ.mul_eq_zero hq hP (Ne.symm hne))
      (fun h => absurd hP h), he]
  have h2 : idem Q * cA D (idemAt PP) = 0 := by
    rw [idem, Finset.sum_mul]
    exact Finset.sum_eq_zero fun q hq => hQ.mul_conj hq hP
  have h3 : cA D (idem Q) * idemAt PP = 0 := by
    rw [idem, map_sum, Finset.sum_mul]
    exact Finset.sum_eq_zero fun q hq => by rw [mul_comm]; exact hQ.mul_conj hP hq
  have h4 : cA D (idem Q) * cA D (idemAt PP) = cA D (idemAt PP) := by rw [← map_mul, h1]
  rw [add_mul, mul_add, mul_add, h1, h2, h3, h4, add_zero, zero_add]

theorem suppAt_idem_of {Q : Finset (Pl D.host.E)} (hQ : SplitSet Q) {PP : Pl D.host.E} (hP : PP ∈ Q) {V : HSp D}
    {g : GA D V} (h : SuppAt (idemAt PP) V g) : SuppAt (idem Q) V g := by
  intro i j
  rw [← h i j, ← mul_assoc, idem_mul_idemAt hQ hP]

theorem suppAt_single {PP : Pl D.host.E} {V : HSp D} {g : GA D V} (h : SuppAt (idemAt PP) V g) :
    SuppAt (idem {PP}) V g := by
  rw [idem, Finset.sum_singleton]
  exact h

end GlobalTheory.SourceTrans

namespace GlobalTheory.SourceTrans

section LocalLift

open Formalism.MainNotions.S Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.ParahoricLift GlobalTheory.LevSplit Formalism.L2.NTheta

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem exists_local_lift' {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hf : IsFrame β Λ) (hsd : HatSelfDual D.sp.cm.sig V.gram Λ)
    {P : Pl D.host.E} {e : Formalism.L2.Theta.AE D} (he : IsIdemAt e P) (k : GL (Fin V.rank) (kP P)) :
    ∃ κ : GA D V, Formalism.L2.Theta.SuppAt e V κ ∧ κ ∈ GfC V ∧ Lev.finE V κ ∈ St β ∧ redFn β P (Lev.finE V κ) = k := by
  have := P.isPrime
  obtain ⟨p, hp, hpp, hres⟩ := exists_idem_int he
  obtain ⟨Y₀, hY₀, hdet⟩ := exists_matrix_lift (Ideal.Quotient.mk P.asIdeal) Ideal.Quotient.mk_surjective k
  obtain ⟨u, hu⟩ := finSw_div_int he (d := Y₀.det) fun h => hdet (Ideal.Quotient.eq_zero_iff_mem.2 h)
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Y₀.map (oToS D.host.F D.host.E) := ⟨_, rfl⟩
  have hu' : u * Y.det = p := by
    rw [hY, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact Subtype.ext (hu.trans hp.symm)
  have hmm := conj_inv_part β p u Y hu' hpp
  rw [hp] at hmm
  obtain ⟨κ, hs, hκ⟩ := split_lift_fin V he.1 _ _ hmm
  have hP : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  have hsf := supp_fin V (f := e + cA D e) hs
  rw [← hp] at hκ
  have hfs : finSw D (e + cA D e) = p + Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p := by
    rw [RingHom.map_add, finSw_cA, hp]
  have hSt : Lev.finE V κ ∈ St β :=
    mem_St_of_part D.sp.cm.sig V.gram Λ β hf hsd p u hpp (sigR_int p.2) Y hu' (Lev.finE V κ)
      (finE_mem_UA V κ) _ hfs hsf hκ
  refine ⟨κ, hs, (T3 P e _ hP).2.2.1 κ hs, hSt, Units.ext ?_⟩
  rw [redFn_of_smul_eq β P _ hSt p hres Y hκ, hY, ← hY₀]
  exact Matrix.ext fun i j => resS_oToS P _

end LocalLift

end GlobalTheory.SourceTrans

namespace GlobalTheory.SourceTrans

section LocalLift

open Formalism.MainNotions.S Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.ParahoricLift GlobalTheory.LevSplit Formalism.L2.NTheta

variable {D : D7}

theorem hatSelfDual_of {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSelfDualC V Λ) :
    HatSelfDual D.sp.cm.sig V.gram Λ := by
  obtain ⟨-, -, -, -, hcc, -, -, hG, hdet, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have h1 : ∀ s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun _ h => sigR_int h
  have h2 : ∀ z, z ∈ GlobalTheory.AdLat.hat1 D.host.F
      ((1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) ↔
      swp D.host.F D.host.E z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro z
    rw [← GlobalTheory.LatDual.integralTensorAdeles_eq_adelicCompletion_one]
    exact GlobalTheory.IdemSupport.mem_intAE_iff z
  have h3 : ∀ x, D.sp.cm.sig x = GlobalTheory.Member.cF D x := fun _ => rfl
  have hmem : ∀ v : Fin V.rank → D.host.E, (∀ y ∈ Λ, (∑ a, ∑ b, v a * V.gram.transpose a b * GlobalTheory.Member.cF D (y b)) ∈
      (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔ v ∈ Λ := by
    intro v
    rw [h.2 v]
    refine forall₂_congr fun y _ => ?_
    rw [FractionalIdeal.mem_one_iff]
    have e : ∑ a, ∑ b, v a * V.gram.transpose a b * GlobalTheory.Member.cF D (y b) = ∑ i, ∑ j, star (y i) * V.gram i j * v j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.transpose_apply]
      change v j * V.gram i j * star (y i) = _
      ring
    rw [e]
  exact hatL_selfDual_gen (GlobalTheory.Member.cF D) D.sp.cm.sig h3 V.gram Λ h.1.fg h.1.span_eq_top hcc hG hdet hmem h1 h2

end LocalLift

variable {D : D7} {S T : HSp D} {B : Base S T}

theorem suppAt_list_prod {e : AE D} {V : HSp D} (L : List (GA D V)) (h : ∀ g ∈ L, SuppAt e V g) : SuppAt e V L.prod := by
  induction L with
  | nil => exact GlobalTheory.SplitHecke.suppAt_one V
  | cons a L ih =>
    rw [List.prod_cons]
    exact GlobalTheory.SplitHecke.suppAt_mul (h a List.mem_cons_self) (ih fun g hg => h g (List.mem_cons_of_mem _ hg))

open Classical in

theorem exists_lift_at (hB : B.Good) {Q : Finset (Pl D.host.E)} (hQ : B.admitted Q)
    (hb : ∀ PP : ↥Q, GL (Fin S.rank) (kP PP.1)) :
    ∃ k : GA D S, k ∈ GfC S ∧ Lev.finE S k ∈ St B.F.βS ∧ SuppAt (idem Q) S k ∧
      ∀ PP : ↥Q, redFn B.F.βS PP.1 (Lev.finE S k) = hb PP := by
  have hsQ : SplitSet Q := (dualTypePlaces_isSplitNonconjugate_of_admissible hQ).mono (fun PP hP => Finset.mem_union_right _ (Finset.mem_union_right _ hP))
  have hsd := hatSelfDual_of hB.frame.sdS
  choose κ h1 h2 h3 h4 using fun PP : ↥Q => exists_local_lift' hB.frame.frS hsd (hsQ.isIdemAt PP.2) (hb PP)
  have hnd : (Finset.univ : Finset ↥Q).toList.Nodup := Finset.nodup_toList _
  have hmem : ∀ PP, PP ∈ (Finset.univ : Finset ↥Q).toList := fun PP => Finset.mem_toList.2 (Finset.mem_univ _)
  have hSt : ∀ g ∈ (Finset.univ : Finset ↥Q).toList.map κ, Lev.finE S g ∈ St B.F.βS := by
    intro g hg
    obtain ⟨PP, -, rfl⟩ := List.mem_map.1 hg
    exact h3 PP
  obtain ⟨hS, hr⟩ := GlobalTheory.ParahoricLift.redFn_list_prod S B.F.βS _ hSt
  refine ⟨((Finset.univ : Finset ↥Q).toList.map κ).prod, (GfC S).list_prod_mem fun g hg => ?_, hS,
    suppAt_list_prod _ fun g hg => ?_, fun PP => ?_⟩
  · obtain ⟨PP, -, rfl⟩ := List.mem_map.1 hg
    exact h2 PP
  · obtain ⟨PP, -, rfl⟩ := List.mem_map.1 hg
    exact suppAt_idem_of hsQ PP.2 (h1 PP)
  · rw [hr PP.1, List.map_map, GlobalTheory.ParahoricLift.prod_map_single hnd (hmem PP) _ fun PP' hne => ?_]
    · exact h4 PP
    · exact GlobalTheory.ExportSeries.redFn_eq_one_of_suppAt B.F.βS hsQ (Finset.singleton_subset_iff.2 PP'.2) PP.2
        (fun h => hne (Subtype.ext (Finset.mem_singleton.1 h).symm)) (h3 PP') (suppAt_single (h1 PP'))

end GlobalTheory.SourceTrans

namespace GlobalTheory.SourceTrans

variable {D : D7} {S T : HSp D} {B : Base S T}

open Classical in
theorem om_src_move (hB : B.Good) (hS : S.SigOK) {ω : PairRep S T} (hω : B.IsWeil 1 ω)
    {Q : Finset (Pl D.host.E)} (hQ : B.admitted Q) (hb : ∀ PP : ↥Q, GL (Fin S.rank) (kP PP.1))
    {k : GA D S} (hk : k ∈ GfC S) (sk : Lev.finE S k ∈ St B.F.βS) (hs : SuppAt (idem Q) S k)
    (hr : ∀ PP : ↥Q, redFn B.F.βS PP.1 (Lev.finE S k) = hb PP)
    (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) :
    ω (k, 1) (B.vecAt Q φ) = B.vecAt Q (fun PP y => φ PP (y * (hb PP).val)) := by
  have hν : (Twist.triv Circle Q : Twist D Circle).Good := Twist.triv_good ((dualTypePlaces_isSplitNonconjugate_of_admissible hQ).mono
    (fun PP hP => Finset.mem_union_right _ (Finset.mem_union_right _ hP)))
  have hsplit := dualTypePlaces_isSplitNonconjugate_of_admissible hQ
  have hQsub : Q ⊆ allP B Q := fun PP hP => Finset.mem_union_right _ (Finset.mem_union_right _ hP)
  have hred1 : ∀ PP ∈ allP B Q, PP ∉ Q → redFn B.F.βS PP (Lev.finE S k) = 1 := fun PP hP hPQ =>
    GlobalTheory.ExportSeries.redFn_eq_one_of_suppAt B.F.βS hsplit hQsub hP hPQ sk hs
  have hpg : ∀ PP ∈ B.G.Pg, PP ∉ Q := fun PP hP h => Finset.disjoint_left.1 hQ.1.disj hP (Finset.mem_union_right _ h)
  have hdq : ∀ PP ∈ B.de.Q, PP ∉ Q := fun PP hP h => Finset.disjoint_left.1 hQ.2 hP h
  have hD : ∀ x, B.F.datumFn B.G (B.de.Q ∪ Q) (B.locFn Q φ) x =
      1 * B.F.datumFn B.G (B.de.Q ∪ Q) (B.locFn Q (fun PP y => φ PP (y * (hb PP).val))) (actO S T k 1 x) := fun x => by
    rw [datumFn_act B.F B.G (B.de.Q ∪ Q) sk (one_mem_St T _) (a := 1) (b := 1) (ω' := B.locFn Q φ)
      (fun y => by
        rw [one_mul]
        refine GlobalTheory.PlaceDatum.omegaG_congr _ _ _ _ fun PP hP => ?_
        change _ = y PP
        simp [hred1 PP (Finset.mem_union_left _ hP) (hpg PP hP), finE_one, redFn_one])
      (fun y => by
        simp only [finE_one, inv_one, Units.val_one, Matrix.one_mul, one_mul]
        unfold Base.locFn
        congr 1
        · refine Finset.prod_congr rfl fun PP hP => ?_
          dsimp only
          rw [hred1 PP (Finset.mem_union_right _ (Finset.mem_union_left _ hP)) (hdq PP hP)]
          simp
        · refine Finset.prod_congr rfl fun PP _ => ?_
          dsimp only
          rw [hr PP, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]) x]
    ring
  refine (om_vec_move hB hS hν hQ hω hk (one_mem _) sk (one_mem_St T _) hD).trans ?_
  have hv : vacC B (Twist.triv Circle Q) k 1 = 1 := by
    unfold vacC
    refine Finset.prod_eq_one fun PP hP => ?_
    rw [map_one, redFn_one, map_one, map_one, mul_one]
    by_cases hPQ : PP ∈ Q
    · rw [resP_q (ν := Twist.triv Circle Q) hQ hPQ]
      simp [Twist.resC, Twist.triv]
    · rw [hred1 PP hP hPQ, map_one, map_one, inv_one]
  rw [hv, Units.val_one, one_mul, one_smul]
  rfl

open Classical in
theorem om_src_fock (hB : B.Good) (hS : S.SigOK) {ω : PairRep S T} (hω : B.IsWeil 1 ω)
    {Q : Finset (Pl D.host.E)} (hQ : B.admitted Q) (hb : ∀ PP : ↥Q, GL (Fin S.rank) (kP PP.1))
    {k : GA D S} (hk : k ∈ GfC S) (sk : Lev.finE S k ∈ St B.F.βS) (hs : SuppAt (idem Q) S k)
    (hr : ∀ PP : ↥Q, redFn B.F.βS PP.1 (Lev.finE S k) = hb PP)
    (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) (P : PolF D T.rank S.rank) :
    ω (k, 1) (B.F.fock (B.vecAt Q φ) P) = B.F.fock (B.vecAt Q (fun PP y => φ PP (y * (hb PP).val))) P := by
  have hth : IsThetaFunO B.F.ψ S T (B.vecAt Q φ) :=
    GlobalTheory.GalLift.Vec.theta_of_thetaAt hB.frame.vac.1 hB.frame.vac.2.inf (Base.isThetaAt_vecAt hB hQ φ) hB.frame.vac.2.theta
  rw [Frame.fock, (GlobalTheory.OrientedHeis.om_pureTensorO D _ _ S T _ _ ω hω hB.frame.vac.2.inf (fun _ => 1) (fun _ => 1)
      (fun τ => (B.F.BS τ).val) (fun τ => (B.F.BS τ).val) B.F.sT B.F.sT B.F.BT B.F.BT k 1
      (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hk])
      (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _)])
      (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hk])
      (fun τ => by simp [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _)]) _ hth P).2,
    om_src_move hB hS hω hQ hb hk sk hs hr φ]
  rfl

end GlobalTheory.SourceTrans

open GlobalTheory.SourceTrans in
theorem GlobalTheory.SourceTrans.exists_series_vecAt_translate_eq_series_mul : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ ω : PairRep S T, B.IsWeil 1 ω → ∀ (Q : Finset (Pl D.host.E)), B.admitted Q → ∀ hb : ∀ PP : ↥Q, GL (Fin S.rank) (kP PP.1), ∃ hQ, SuppAt (idem Q) S hQ ∧ ∀ (φ : ∀ PP : ↥Q, Matrix (Fin T.rank) (Fin S.rank) (kP PP.1) → ℂ) (h : GA D S) (P : PolF D T.rank S.rank), series B.F ω (B.vecAt Q fun PP y => φ PP (y * (hb PP).val)) h P = series B.F ω (B.vecAt Q φ) (h * hQ) P := by
  intro D S T B hB hS ω hω Q hQ hb
  obtain ⟨k, hk, sk, hs, hr⟩ := exists_lift_at hB hQ hb
  refine ⟨k, hs, fun φ h P => ?_⟩
  funext g
  rw [series_apply, series_apply, show ((h * k, g) : GA D S × GA D T) = (h, g) * (k, 1) by simp, map_mul,
    Module.End.mul_apply, om_src_fock hB hS hω hQ hb hk sk hs hr φ P]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedThetaGeneratorEqClassSumIntegralForm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwTraceCx

open GlobalTheory.ClassTrace

variable {D : D7}

noncomputable def lift (V : HSp D) (x : Bridge.Gf V) : GA D V := Classical.choose (GlobalTheory.ThetaCommutation.exists_fin_part V x)

theorem lift_mem (V : HSp D) (x : Bridge.Gf V) : lift V x ∈ GfC V :=
  (Classical.choose_spec (GlobalTheory.ThetaCommutation.exists_fin_part V x)).1

theorem finPt_lift (V : HSp D) (x : Bridge.Gf V) : finPt V (lift V x) = x :=
  (Classical.choose_spec (GlobalTheory.ThetaCommutation.exists_fin_part V x)).2

theorem eq_of_finPt (V : HSp D) {a b : GA D V} (ha : a ∈ GfC V) (hb : b ∈ GfC V) (h : finPt V a = finPt V b) :
    a = b := by
  have h1 : finHom V a = finHom V b := congrArg Subtype.val h
  have h2 : a⁻¹ * b ∈ GinfC V := by
    show finHom V (a⁻¹ * b) = 1
    rw [map_mul, map_inv, h1, inv_mul_cancel]
  have h3 := (GlobalTheory.UnitarySplit.real_finite_split D V).2.2.1 _ h2 ((GfC V).mul_mem ((GfC V).inv_mem ha) hb)
  rw [inv_mul_eq_one] at h3
  exact h3

theorem lift_finPt (V : HSp D) {a : GA D V} (ha : a ∈ GfC V) : lift V (finPt V a) = a :=
  eq_of_finPt V (lift_mem V _) ha (finPt_lift V _)

theorem mem_GfC_of_suppAt {Q : Finset (Pl D.host.E)} (hQ : SplitSet Q) {V : HSp D} {g : GA D V}
    (hg : SuppAt (idem Q) V g) : g ∈ GfC V := by
  refine GlobalTheory.WeilProduct.mem_GfC_of_supp (a := idem Q + cA D (idem Q)) ?_ hg
  rw [RingHom.map_add, idem, map_sum (cA D), map_sum (infPart D), map_sum (infPart D), ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun PP hPP => ?_
  have h1 := (hQ.isIdemAt hPP).1
  rw [GlobalTheory.SplitScalar.infPart_splitIdem h1, GlobalTheory.SplitScalar.infPart_splitIdem (GlobalTheory.SplitScalar.isSplitIdem_conj h1), add_zero]

theorem act_of_mem_GfC {S T : HSp D} (B : Base S T) {g : GA D S} (hg : g ∈ GfC S) : B.act g = 1 := by
  have h1 : infHom S g = 1 := hg
  have h2 : realGL B.F.θ S g = 1 := by
    funext τ
    show Formalism.UG.bc (B.F.θ τ) (infHom S g) = 1
    rw [h1, map_one]
  rw [Base.act, MonoidHom.comp_apply, h2, map_one]

noncomputable def kern {S T : HSp D} (B : Base S T) (ω : PairRep S T) (t : Twist D Circle) (x : Bridge.Gf S) :
    PolF D T.rank S.rank →ₗ[ℂ] (GA D T → ℂ) :=
  series B.F ω (B.vecFlat t) (lift S x)

noncomputable abbrev ratAct {S T : HSp D} (B : Base S T) : Representation ℂ (GQ S) (PolF D T.rank S.rank) :=
  B.act.comp (GQ S).subtype

end GlobalTheory.TwTraceCx

namespace GlobalTheory.TwTraceCx

variable {D : D7}

theorem gen_eq_smul {S T : HSp D} {B : Base S T} (hB : B.Good) {t : Twist D Circle} (ht : t.Good) (hQ : B.admitted t.Q)
    {ω₁ ωt : PairRep S T} (h1 : B.IsWeil 1 ω₁) (h2 : B.IsWeil t.chi ωt) (h : GA D S) (P : PolF D T.rank S.rank) :
    B.gen ω₁ t h P = ((detChar S t.chi h : Circle) : ℂ) • series B.F ωt (B.vecFlat t) h P := by
  have hν := ht.isHeckeChar
  have hF := ht.real
  have hω1 : IsWeilDatumO B.F.ψ S T B.mu (B.mu * B.eta⁻¹) ω₁ := by
    have := h1
    unfold Base.IsWeil at this
    simpa only [mul_one] using this
  have hωt : IsWeilDatumO B.F.ψ S T (B.mu * t.chi) (B.mu * B.eta⁻¹ * t.chi) ωt := by
    have := h2
    unfold Base.IsWeil at this
    rwa [mul_right_comm B.mu t.chi] at this
  have key := ((GlobalTheory.SplitChange.change_of_splitting_pair D B.F.ψ S T B.mu (B.mu * B.eta⁻¹) t.chi ω₁ hω1 hν hF).2.1
    _ _ (muVal_detChar S hF) (muVal_detChar T hF)).2 ωt hωt
  have hth := Base.isThetaFunO_fock_vecAt hB hQ (fun PP => flat (t.resC PP.1)) P
  funext g
  have e := key h g _ hth
  have hc : ((detChar S t.chi h : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  change ((detChar T t.chi g : Circle) : ℂ) * (ω₁ (h, g) (B.F.fock (B.vecFlat t) P) 0) =
    ((detChar S t.chi h : Circle) : ℂ) * (ωt (h, g) (B.F.fock (B.vecFlat t) P) 0)
  have e' : ωt (h, g) (B.F.fock (B.vecFlat t) P) 0 = (((detChar T t.chi g : Circle) : ℂ) *
      (((detChar S t.chi h : Circle) : ℂ))⁻¹) * ω₁ (h, g) (B.F.fock (B.vecFlat t) P) 0 := by
    have := congrFun e 0
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact this
  rw [e']
  field_simp

end GlobalTheory.TwTraceCx

namespace GlobalTheory.TwTraceCx

open GlobalTheory.ClassTrace

variable {D : D7}

theorem traceForm_mem_mtLat {S T : HSp D} {B : Base S T} (hB : B.Good) {K : Type} [Field K] [NumberField K]
    {σ : K →+* ℂ} {emb : D.what₂.Tau → D.host.E →+* K} {O : Subring ℂ} (hc : IsCoefRing σ emb O) {t : Twist D Circle}
    (hfin : ∀ x, Finite (Bridge.stab (Bridge.ratF S) (B.levJ t) x))
    (hlam : ∀ x : B.levJ t, ((B.levLam t x : ℂˣ) : ℂ) ∈ O) (h : Bridge.Gf S) {P : PolF D T.rank S.rank}
    (hP : P ∈ B.coefLat σ emb O h) :
    traceForm (Bridge.ratF S) (B.levJ t) (B.levLam t) (ratAct B) h P ∈ B.mtLat σ emb O t := by
  have hV : P ∈ B.valSpace := (Submodule.mem_inf.1 hP).1
  rw [Base.mem_mtLat, Base.mem_formsC]
  refine ⟨⟨fun x => ?_, fun γ x k => ?_⟩, fun x => ?_⟩
  · refine finsum_induction (· ∈ B.valSpace) (zero_mem _) (fun _ _ => add_mem) fun γ => ?_
    exact Submodule.smul_mem _ _ (Base.act_mem_valSpace _ hV)
  · exact traceForm_law _ _ _ _ hfin h P γ x k
  · refine finsum_induction (· ∈ B.coefLat σ emb O x) (zero_mem _) (fun _ _ => add_mem) fun γ => ?_
    by_cases hγ : γ ∈ link (Bridge.ratF S) (B.levJ t) h x
    · obtain ⟨k, rfl⟩ := (mem_link_iff _ _).1 hγ
      have e : h⁻¹ * (Bridge.ratF S γ)⁻¹ * (Bridge.ratF S γ * h * k) = k := by group
      rw [e, lamExt_coe]
      exact (B.coefLat σ emb O _).smul_mem (⟨_, hlam k⟩ : O)
        (Base.act_mem_coefLat hB.frame hc γ h k (Base.mem_St_of_mem_levJ k.2) hP)
    · rw [lamExt_of_not_mem _ _ hγ, zero_smul]
      exact zero_mem _

end GlobalTheory.TwTraceCx

namespace GlobalTheory.TwTraceCx

open GlobalTheory.ClassTrace

variable {D : D7}

set_option maxHeartbeats 3000000 in

theorem dualLaw_kern {S T : HSp D} {B : Base S T} (hB : B.Good) (hS : HSpace.SigOK S) {t : Twist D Circle} (ht : t.Good)
    (hQ : B.admitted t.Q) {ωt : PairRep S T} (h2 : B.IsWeil t.chi ωt) :
    DualLaw (e := RingHom.id ℂ) (Bridge.ratF S) (B.levJ t) (B.levLam t) (ratAct B) (kern B ωt t) := by
  intro γ x k p
  have hW : IsWeilDatumO B.F.ψ S T (B.mu * t.chi) (B.mu * t.chi * B.eta⁻¹) ωt := h2
  obtain ⟨a, ha, γf, hγf, hγ⟩ := (GlobalTheory.UnitarySplit.real_finite_split D S).1 (γ : GA D S)
  have hxl := lift_mem S x
  have hkl := lift_mem S (k : Bridge.Gf S)
  have hfa : finHom S a = 1 := ha
  have e1 : lift S (Bridge.ratF S γ * x * k) = γf * lift S x * lift S (k : Bridge.Gf S) := by
    refine eq_of_finPt S (lift_mem S _) ((GfC S).mul_mem ((GfC S).mul_mem hγf hxl) hkl) ?_
    rw [finPt_lift]
    apply Subtype.ext
    have hx1 : finHom S (lift S x) = x.1 := congrArg Subtype.val (finPt_lift S x)
    have hk1 : finHom S (lift S (k : Bridge.Gf S)) = (k : Bridge.Gf S).1 := congrArg Subtype.val (finPt_lift S _)
    show finHom S (γ : GA D S) * x.1 * (k : Bridge.Gf S).1 = finHom S (γf * lift S x * lift S (k : Bridge.Gf S))
    rw [map_mul, map_mul, hx1, hk1, hγ, map_mul, hfa, one_mul]
  have e2 : ratAct B γ p = B.act a p := by
    show B.act (γ : GA D S) p = _
    rw [hγ, map_mul, act_of_mem_GfC B hγf, mul_one]
  have hcomm : γf * lift S x * lift S (k : Bridge.Gf S) * a = (γ : GA D S) * (lift S x * lift S (k : Bridge.Gf S)) := by
    rw [← (GlobalTheory.UnitarySplit.real_finite_split D S).2.1 a ha _ ((GfC S).mul_mem ((GfC S).mul_mem hγf hxl) hkl), hγ]
    group
  have hJ : finPt S (lift S (k : Bridge.Gf S)) ∈ B.levJ t := by rw [finPt_lift]; exact k.2
  have hT0 : ωt (lift S (k : Bridge.Gf S), 1) (B.F.fock (B.vecFlat t) p) =
      ((B.levLam t k : ℂˣ) : ℂ)⁻¹ • B.F.fock (B.vecFlat t) p := by
    have := ((GlobalTheory.ExportSeries.DualType.thetaSeriesData_have_dualType hB hS ht hQ).1 ωt h2 _ hkl hJ).2 p
    rwa [show (⟨finPt S (lift S (k : Bridge.Gf S)), hJ⟩ : B.levJ t) = k from Subtype.ext (finPt_lift S _)] at this
  have hK2 : ωt (a, 1) (B.F.fock (B.vecFlat t) p) = B.F.fock (B.vecFlat t) (B.act a p) :=
    GlobalTheory.RealFockAction.om_fock_vecAt D S T B t ωt t.Q (fun PP => flat (t.resC PP.1)) hB ht hQ h2 a ha p
  have hth : IsThetaFunO B.F.ψ S T (B.F.fock (B.vecFlat t) p) :=
    Base.isThetaFunO_fock_vecAt hB hQ (fun PP => flat (t.resC PP.1)) p
  funext g
  rw [Pi.smul_apply, RingHom.id_apply, kern, kern, series_apply, series_apply, smul_eq_mul]
  rw [e1, e2, ← hK2]
  have q1 : ((γf * lift S x * lift S (k : Bridge.Gf S), g) : GA D S × GA D T) * (a, 1) =
      (((γ : GA D S), 1) * (lift S x, g)) * (lift S (k : Bridge.Gf S), 1) := by
    simp only [Prod.mk_mul_mk, mul_one, one_mul]
    rw [hcomm, mul_assoc]
  have e5 : ωt (γf * lift S x * lift S (k : Bridge.Gf S), g) (ωt (a, 1) (B.F.fock (B.vecFlat t) p)) =
      ωt ((γ : GA D S), 1) (ωt (lift S x, g) (ωt (lift S (k : Bridge.Gf S), 1) (B.F.fock (B.vecFlat t) p))) := by
    calc ωt (γf * lift S x * lift S (k : Bridge.Gf S), g) (ωt (a, 1) (B.F.fock (B.vecFlat t) p))
        = ωt (((γf * lift S x * lift S (k : Bridge.Gf S), g) : GA D S × GA D T) * (a, 1)) (B.F.fock (B.vecFlat t) p) := by
          rw [map_mul ωt, Module.End.mul_apply]
      _ = ωt ((((γ : GA D S), 1) * (lift S x, g)) * (lift S (k : Bridge.Gf S), 1)) (B.F.fock (B.vecFlat t) p) := by rw [q1]
      _ = _ := by rw [map_mul ωt, map_mul ωt, Module.End.mul_apply, Module.End.mul_apply]
  have hA := hW.om_aut (γ : GA D S) γ.2 1 (one_mem _)
    (ωt (lift S x, g) (ωt (lift S (k : Bridge.Gf S), 1) (B.F.fock (B.vecFlat t) p))) (hW.om_pres _ _ (hW.om_pres _ _ hth))
  simp only [e5, hA]
  simp only [hT0, map_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero ((B.levLam t) k)), one_mul]

theorem classSum_traceForm_eq {S T : HSp D} {B : Base S T} (hB : B.Good) (hS : HSpace.SigOK S) {t : Twist D Circle}
    (ht : t.Good) (hQ : B.admitted t.Q) {ωt : PairRep S T} (h2 : B.IsWeil t.chi ωt) {I : Type} [Fintype I] {rep : I → GA D S}
    (hcl : IsClassSystem S (B.levJ t) rep) {h : GA D S} (hh : h ∈ GfC S) (P : PolF D T.rank S.rank) :
    B.classSum ωt t rep (traceForm (Bridge.ratF S) (B.levJ t) (B.levLam t) (ratAct B) (finPt S h) P) =
      series B.F ωt (B.vecFlat t) h P := by
  have hfin := finite_stab_of_reps _ _ hcl.reps hcl.stab
  have key := classSum_traceForm (e := RingHom.id ℂ) (Bridge.ratF S) (B.levJ t) (B.levLam t) (ratAct B) hfin
    (dualLaw_kern hB hS ht hQ h2) hcl.reps (finPt S h) P
  have e : kern B ωt t (finPt S h) P = series B.F ωt (B.vecFlat t) h P := by rw [kern, lift_finPt S hh]
  rw [← e, ← key, Base.classSum_apply, GlobalTheory.ClassTrace.classSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kern, lift_finPt S (hcl.fin i)]

end GlobalTheory.TwTraceCx

namespace GlobalTheory.TwTraceCx

open GlobalTheory.ClassTrace

theorem trace_cx : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ∀ k Q ψ,
    TwOK i k Q ψ →
    (∀ x : (ρ.B i j b).levJ (ρ.tw i b k Q ψ), (((ρ.B i j b).levLam (ρ.tw i b k Q ψ) x : ℂˣ) : ℂ) ∈ (ρ.eOk i b k).range) →
    ∀ s h P, ρ.IsDatum i j b s h P → ∀ f ∈ ρ.gens i j b k Q ψ h P, ∃ F ∈ ρ.mt i j b k Q ψ, f = ρ.sum i j b k Q ψ F := by
  intro D ρ hρ i j b k Q ψ hok hlam s h P hd f hf
  obtain ⟨ht, hadm, hval⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ i j b k Q ψ hok
  obtain ⟨hQ, hsupp, rfl⟩ := hf
  have hB := hρ.base i j b
  have hS : (Vc D j).SigOK := D.sp.V_sig _
  have hcl := hρ.classes i j b _ ht hadm
  have hfin := finite_stab_of_reps _ _ hcl.reps hcl.stab
  have hh : h * hQ ∈ GfC (Vc D j) := (GfC _).mul_mem hd.fin (mem_GfC_of_suppAt ht.split hsupp)
  have hdisj : Disjoint (ρ.tw i b k Q ψ).Q (D.ntw.S0 i) := hok.2.1.mono_left fun x hx =>
    (mem_half.1 (show x ∈ half (ρ.ch i) Q from hx)).1
  have hP : P ∈ ρ.lat i j b (ρ.eOk i b k).range (h * hQ) :=
    GlobalTheory.T.coefLat_le_translate_splitPlaces_prime_to_l D ρ hρ i j b k _ h hQ P ht.split hdisj hd.fin hsupp hd.mem
  obtain ⟨u, hu⟩ := hval (detRoot (Vc D j) (h * hQ))
  have hc : ((detChar (Vc D j) (ρ.tw i b k Q ψ).chi (h * hQ) : Circle) : ℂ) ∈ (ρ.eOk i b k).range := ⟨u, hu.symm⟩
  refine ⟨(⟨_, hc⟩ : (ρ.eOk i b k).range) • traceForm (Bridge.ratF _) _ _ (ratAct (ρ.B i j b)) (finPt _ (h * hQ)) P,
    Submodule.smul_mem _ _ (traceForm_mem_mtLat hB (hρ.isCoefRing_k i b k) hfin hlam _ hP), ?_⟩
  rw [gen_eq_smul hB ht hadm (hρ.weil_base i j b) (hρ.weil i j b _ ht)]
  change _ = (ρ.B i j b).classSum _ _ _
    (((detChar (Vc D j) (ρ.tw i b k Q ψ).chi (h * hQ) : Circle) : ℂ) •
      traceForm (Bridge.ratF _) _ _ (ratAct (ρ.B i j b)) (finPt _ (h * hQ)) P)
  rw [map_smul, classSum_traceForm_eq hB hS ht hadm (hρ.weil i j b _ ht) hcl hh]

end GlobalTheory.TwTraceCx

end
end

