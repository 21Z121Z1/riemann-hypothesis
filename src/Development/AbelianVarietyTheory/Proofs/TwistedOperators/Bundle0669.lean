import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmegaField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0238
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0661
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0353
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1722
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0527
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0664

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNormalisedTupleDataOverCoefficientField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PinsOverField

open GlobalTheory.CoverHalf GlobalTheory.TwistField GlobalTheory.PinnedData
open scoped nonZeroDivisors

theorem prod_image_congr {α β γ M : Type} [DecidableEq β] [DecidableEq γ] [CommMonoid M] (s : Finset α) (f : α → β) (g : α → γ)
    (P : β → M) (Q : γ → M) (h : ∀ a ∈ s, ∀ b ∈ s, f a = f b ↔ g a = g b) (hv : ∀ a ∈ s, P (f a) = Q (g a)) :
    ∏ b ∈ s.image f, P b = ∏ c ∈ s.image g, Q c := by
  have key : ∀ b ∈ s.image f, ∃ a ∈ s, f a = b := fun b hb => Finset.mem_image.1 hb
  choose u hu1 hu2 using key
  refine Finset.prod_bij (fun b hb => g (u b hb)) (fun b hb => Finset.mem_image_of_mem _ (hu1 b hb)) ?_ ?_ ?_
  · intro b hb b' hb' e
    rw [← hu2 b hb, ← hu2 b' hb']
    exact (h _ (hu1 b hb) _ (hu1 b' hb')).2 e
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hc
    have hb := Finset.mem_image_of_mem f ha
    exact ⟨f a, hb, (h _ (hu1 _ hb) _ ha).1 (hu2 _ hb)⟩
  · intro b hb
    rw [← hv _ (hu1 b hb), hu2]

variable {D : D7}

open Formalism.L2.Pj.LPb in

theorem coverHalf_mul {Q : Finset (Pl D.host.E)} (hQ : Lev.IsTwistPlaces D.host.g Q)
    (h2 : ∀ PP ∈ Q, (2 : 𝓞 D.host.E) ∉ PP.asIdeal)
    (h1 : ∀ PP ∈ Q, ∀ PP' ∈ Q, (∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.E) ∈ PP.asIdeal ∧ (p : 𝓞 D.host.E) ∈ PP'.asIdeal) →
      PP.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = PP'.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) :
    coverHalf D Q * (coverHalf D Q).map (bH D) =
      Ideal.span {((∏ q ∈ Q.image (fun PP => Nat.card (kP PP)), q : ℕ) : 𝓞 D.host.E)} := by
  classical
  have key : ∀ PP ∈ Q, (Nat.card (kP PP)).Prime ∧ ((Nat.card (kP PP) : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∧
      SplitOK D (Nat.card (kP PP)) := fun PP hPP => by
    obtain ⟨⟨q, hq, hc, hu, -⟩, -⟩ := hQ PP hPP
    rw [hc]
    exact ⟨hq, splitOK_of_place PP hq hc hu (h2 PP hPP)⟩
  have hun : ∀ (PP : Pl D.host.E) (q : ℕ), (q : 𝓞 D.host.K) ∈ (PP.under (𝓞 D.host.K)).asIdeal ↔
      (q : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP q => by
    show algebraMap (𝓞 D.host.K) (𝓞 D.host.E) q ∈ PP.asIdeal ↔ _
    rw [map_natCast]
  unfold coverHalf
  rw [← Ideal.mapHom_apply, map_prod, ← Finset.prod_mul_distrib, Nat.cast_prod, ← Ideal.prod_span_singleton]
  convert prod_image_congr Q (fun PP => PP.under (𝓞 D.host.K)) (fun PP => Nat.card (kP PP))
    (fun 𝔭 => 𝔭.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) *
      Ideal.mapHom (bH D) (𝔭.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))))
    (fun q => Ideal.span {(q : 𝓞 D.host.E)}) (fun a ha b hb => ⟨fun e => ?_, fun e => ?_⟩) fun a ha => ?_
  · by_contra hne
    have h3 := (hun b _).1 (e ▸ (hun a _).2 (key a ha).2.1)
    exact not_mem_of_coprime b.isPrime.ne_top ((Nat.coprime_primes (key a ha).1 (key b hb).1).2 hne) h3 (key b hb).2.1
  · exact HeightOneSpectrum.ext (h1 a ha b hb ⟨_, (key a ha).1, (key a ha).2.1, by
      rw [show Nat.card (kP a) = Nat.card (kP b) from e]; exact (key b hb).2.1⟩)
  · obtain ⟨e, he1, he2, he3⟩ := pb_eq_JK D (key a ha).2.2 _ ((hun a _).2 (key a ha).2.1)
    simp only [Ideal.mapHom_apply]
    rw [he3, map_JK, QE_map_bar]
    exact QE_mul D _ _ he1 he2

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_half_tupPrime (T : Core D) (R : RealDat D A Ks) {μ0 : T0} (hT : LawsM T) (hL : R.toLevCh.Is μ0)
    (hO : T.pb = R.C.P.pb) (hG : QGuard R) (t : T0) :
    ∃ l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level T.Q.H, IsCoverLevel T.Q.l (tupPrime R t) (coverHalf D (R.Q t)) l₂ ∧
      HalfIs R t T.Q.l.Mb (coverHalf D (R.Q t)) := by
  obtain ⟨pd, l₂, h1, h2⟩ := exists_half_of_laws T R hT hL hO hG t
  have hb : (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = bH D :=
    RingHom.ext fun a => RingOfIntegers.ext (T.Q.H.bar_eq a)
  have h3 : ∀ PP ∈ R.Q t, (2 : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP h => hG.2 t PP hPP (by
    rw [Nat.cast_mul, Nat.cast_mul, mul_assoc]
    obtain ⟨c, hc⟩ := D.host.two_dvd_QS
    refine Ideal.mul_mem_right _ _ ?_
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (by exact_mod_cast h))
  have h4 := coverHalf_mul (hL.Q_pl t) h3 (hG.1 t)
  have h5 := l₂.prod
  rw [h1.2.2.2.1, Ideal.map_mul, mul_mul_mul_comm, T.Q.l.prod, hb, h4, h1.2.1, Ideal.span_singleton_mul_span_singleton,
    ← Nat.cast_mul] at h5
  have h6 := congrArg Ideal.absNorm h5
  rw [Ideal.absNorm_span_natCast, Ideal.absNorm_span_natCast] at h6
  have h7 := Nat.pow_left_injective Module.finrank_pos.ne' h6
  have h8 : tupPrime R t = pd := Nat.eq_of_mul_eq_mul_left (by have := T.Q.l.three_le; omega) h7
  exact ⟨l₂, h8 ▸ h1, h2⟩

variable (R : RealDat D A Ks) (i : Fin D.R.m)

theorem locK_mem (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam) (t : T0) (PP : Pl D.host.E) (k : D.host.Eˣ) :
    (((R.xiH t).locK PP k : ℂˣ) : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := by
  obtain ⟨_, _, _, hT⟩ := hF.tie
  exact GlobalTheory.TwistValues.xiH_locK_mem R hL hF.pl_onto hF.muVal hT.ok ⟨0, lt_of_lt_of_le two_pos D.R.two_le_m⟩ t PP k

theorem xiR_mem (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam) (t : T0) (P : Pl D.host.E) (hP : P ∈ R.Q t) (u : (kP P)ˣ) :
    ((R.xiR t P u : ℂˣ) : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := P.asIdeal) (u : kP P)
  have hnt : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h
    have h0 : a = 0 := RingOfIntegers.ext h
    rw [h0, map_zero] at ha
    exact u.ne_zero ha.symm
  rw [hL.xiR t P hP a (Units.mk0 _ ha0) u rfl ha.symm]
  exact locK_mem R hL hF t P _

theorem exists_BIs (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam) (M : IntermediateField ℚ ℂ)
    (hM : M = D.what₂.embLL.toRatAlgHom.fieldRange) {b : ℕ} {B₀ : Ideal (𝓞 D.host.E) → M}
    (h₀ : BIs R i M.val.toRingHom A.μ0 b B₀) (t : T0) {bad : ℕ} (hb : b ∣ bad) :
    ∃ B : Ideal (𝓞 D.host.E) → M, BIs R i M.val.toRingHom t bad B := by
  have key : ∀ v : HeightOneSpectrum (𝓞 D.host.E), ((bad : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal →
      (((R.C.mu0 i * R.xiH t * R.C.eta⁻¹).val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal : ℝ) : ℝ) : ℂ) ∈ M := by
    intro v hv
    have hv' : ((b : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := fun h => hv (by
      obtain ⟨c, rfl⟩ := hb
      rw [Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ h)
    have h1 := h₀ v.asIdeal v.ne_bot (by
      by_contra hne
      exact hv' (v.isMaximal.eq_of_le hne le_sup_left ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    rw [GlobalTheory.Mem.BVal.onId_prime, hL.xi_base, mul_one] at h1
    have h2 : (((R.xiH t).val v : ℂˣ) : ℂ) ∈ M := hM ▸ locK_mem R hL hF t v _
    have h4 : M.val.toRingHom (B₀ v.asIdeal) ∈ M := (B₀ v.asIdeal).2
    rw [h1] at h4
    have h3 := mul_mem h2 h4
    convert h3 using 1
    rw [mul_right_comm (R.C.mu0 i), Formalism.L2.Host.HChar.val_mul, Units.val_mul]
    ring
  classical
  refine ⟨fun cc => if h : cc ≠ ⊥ ∧ cc ⊔ Ideal.span {((bad : ℕ) : 𝓞 D.host.E)} = ⊤ then
    ⟨_, GlobalTheory.Mem.BVal.mem_of_primes _ M _ key cc h.1 h.2⟩ else 0, fun cc h0 h1 => ?_⟩
  simp only [dif_pos (And.intro h0 h1)]
  rfl

set_option maxHeartbeats 1000000 in

theorem exists_phi_over {F : Face D A} (hR : R.Char F) (hV : VStd D i) (t : T0) {La : Type} [AddCommGroup La]
    [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (hι : LatEmb (Wc D i) ι)
    (M : IntermediateField ℚ ℂ) (hM : M = D.what₂.embLL.toRatAlgHom.fieldRange)
    (hP : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (J : Ideal (𝓞 D.host.E))
    (hJ : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E)) :
    ∃ φ : (Fin (Vc D i).rank → La ⧸ (J • ⊤ : Submodule (𝓞 D.host.E) La)) → M, PhiIs R i M.val.toRingHom t ι (J • ⊤) φ := by
  have hv : ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
      omegaK R.Pg y * omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) y ∈ M := fun y => by
    refine mul_mem ?_ ?_
    · unfold omegaK
      split_ifs
      exacts [one_mem _, zero_mem _]
    · unfold omegaQ
      split_ifs
      · exact prod_mem fun PP _ => zpow_mem (hM ▸ xiR_mem R hR.lev hR.fam t PP.1 PP.2 _) _
      · exact zero_mem _
  obtain ⟨-, e, he, -⟩ := hR.thP.vP i t
  have hβ := GlobalTheory.T.inverse_selfDual_frame_standard_space_integral D i _ _ hV (hR.lev.βV i)
  have hi : ∀ x a, rowP (Wc D i) (R.βW i) e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun x a =>
    rowP_int _ _ _ (hR.lev.βW i) e _ he (fun PP h => hP PP (by simpa using h)) _
      (hι.2.le (LinearMap.mem_range_self ι x)) a
  refine ⟨fun q => ⟨_, hv fun PP => redM PP
    (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (q b).out)⟩, e, he, fun x =>
    ⟨(redM_uMat (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e (fun b => ι (x b)) fun b a => hi (x b) a).1, ?_⟩⟩
  exact omega_congr _ _ _ _ _ _ _ fun PP hPP => exists_datum (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e ι hi J PP (hJ PP hPP) x _
    fun b => (Submodule.Quotient.eq _).1 (Quotient.out_eq _)

set_option maxHeartbeats 2000000 in

theorem pinsOverL : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), R.Char F → Nonempty (FWTie T R κ v₀) → OMPins T R κ v₀ O i → QGuard R → GlobalTheory.TwistField.CoverField T R → GlobalTheory.TwistField.PinsOverL T R κ v₀ i := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O i hR hfw hO hG hC
  have hpb := GlobalTheory.LevelPrimes.pb_eq_of_tie D G Pl0 T0 A T R F κ v₀ O i hR hfw hO
  obtain ⟨fw⟩ := id hfw
  have hT := fw.laws
  obtain ⟨hc', hP⟩ := hO
  have hV : VStd D i := hP.lift.std
  have hB0 := (hP.tuple ()).B
  have hb0 := hP.bad ()
  have hjL := hP.lift.field
  have hlev := hP.lift.lev
  have hio := hP.io
  have hact := hP.act
  choose l₂ hl₁ hl₂ using exists_half_tupPrime T.toCore R hT.toLawsM hR.lev hpb hG
  obtain ⟨dδ, U₂, dict₂, xi, -, hcov, hhalf, hxi, hcxi, hmod, -⟩ :=
    GlobalTheory.CoverOverField.coversAt D G Pl0 T0 A T R hT hR.lev hR.fam.roots
      (GlobalTheory.TwistValues.xiVal D G Pl0 T0 A _ R hR.lev hR.fam) hC i (Vc D i).rank _ l₂ hl₁ hl₂ (O i).c' (O i).hle hc'
  obtain ⟨c0', hc0, hplace⟩ := GlobalTheory.T.exists_coeffExt_rationalForms_values_field D G Pl0 T0 A T R F κ v₀ hR hfw hpb i (O i).c'.F (O i).jL (inC (O i).c') hjL
  choose Cl fCl h J' bad Lh gam vol La Nc hrep hdv hvol hok hlat using fun t =>
    GlobalTheory.SplitReps.exists_repsR_repsOK R i (hR.lev.βV i) hV (O i).c'.F t (dδ t).l₂ hb0.1
  have hbad : ∀ t, 0 < bad t ∧ BadPin (bad t) (D.host.QS * D.host.q) D.host.d (D.host.g 0 * D.host.g 1) := fun t =>
    ⟨Nat.pos_of_ne_zero (hrep t).1, hb0.2.1.trans (hdv t), hb0.2.2.1.trans (hdv t), hb0.2.2.2.1.trans (hdv t),
      hb0.2.2.2.2.trans (hdv t)⟩
  choose B hBis using fun t => exists_BIs R i hR.lev hR.fam (O i).c'.F hc' hB0 t (hdv t)
  have hodd : Odd ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q) := by
    obtain ⟨e1, e2, -⟩ := hT.pins.2.2.2 _ (inR i)
    have h5 := Formalism.L2.NTheta.odd_r D.R
    have h6 := i.2
    have h7 := D.R.m_add_three_le_k
    rw [e1, e2]
    convert h5 using 1
    simp only [Ranks.sigW, Ranks.r]
    omega
  choose epF hepF using fun t => (GlobalTheory.ClassTieCompare.exists_epIs_iff (n := (Vc D i).rank) (Dw := T.Q.Dw ((i : ℕ) + 1))
    (bad t) (B t)).2 fun L cc g d => GlobalTheory.T.law_of_squares_selfDual_splitLattice _ _ _ _ hodd L cc g.1 g.2.2 d.1 d.2
  choose φ hφis using fun t => exists_phi_over R i hR hV t (iotaW T i) (latEmb_iotaW T hT i) (O i).c'.F hc'
    (hhalf t).2.2 (Mfr (dδ t).l₂) fun PP hPP c hc => by
    have hM : (dδ t).l₂.Mb ≤ PP.asIdeal := by
      rw [(hcov t).1.2.2.2.1]
      rcases hPP with hPP | hPP
      · rw [(hhalf t).1]
        exact Ideal.mul_le_left.trans (Ideal.prod_le_inf.trans (Finset.inf_le hPP))
      · exact Ideal.mul_le_right.trans ((hhalf t).2.1 PP hPP)
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ T.Q.H.bar.surjective).1 hc
    refine ⟨b, hM hb, ?_⟩
    change _ = star ((T.Q.H.bar b : 𝓞 D.host.E) : D.host.E)
    rw [T.Q.H.bar_eq]
    exact (star_star _).symm
  choose thAd hth using fun t => exists_thAd R i hR t c0' (h t) (hrep t).2.2.1 (hrep t).2.2.2.2.2.1 (v₀ i (sg0 D A))
  refine ⟨{ c' := (O i).c', hle := (O i).hle, jL := (O i).jL, hV := (O i).hV, c0' := c0', lev := (O i).lev, dδ := dδ, Cl' := Cl,
            bad := bad, Lh := Lh, La := La, Nc := Nc, gam := gam, vol := vol, ep := fun t k => epF t (Lh t k), B := B,
            epF := epF, io := (O i).io, hw := (O i).hw, φ := φ,
            w := fun t _ q => (dδ t).eF.symm (phiHat (dδ t).c₂ (fun x => (dδ t).eF (φ t x)) q),
            U₂ := U₂, dict₂ := dict₂, xi := xi, thAd := thAd,
            Plc := fun t x => ∃ x₀, Place R i t (h t) c0' (jVx R i t x₀) x }, hc',
    ⟨hjL, hV, fw.hv₀ i _, hc0, hlev⟩,
    fun t => ⟨⟨h t, J' t, hrep t, hplace t _ _, hth t, fun _ => Iff.rfl⟩, hBis t, hxi t, hφis t, hhalf t⟩,
    hact, hbad, fun t => ⟨hok t, hlat t⟩, fun t => ⟨fun _ => rfl, hepF t⟩, hio,
    fun t k q => AlgEquiv.apply_symm_apply _ _, hcov, hcxi, hmod⟩

end GlobalTheory.PinsOverField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterSubgroupTransposeGramRealPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.LineAtPlace

variable {D : D7}

theorem emb_eq_or_conj (e₁ e₂ : D.host.E →+* ℂ)
    (h : ∀ a : D.host.F, e₁ (algebraMap D.host.F D.host.E a) = e₂ (algebraMap D.host.F D.host.E a)) :
    (∀ x, e₂ x = e₁ x) ∨ ∀ x, e₂ x = starRingEnd ℂ (e₁ x) := by
  have hconj : ∀ a : D.host.E, e₁ (star a) = starRingEnd ℂ (e₁ a) := D.sp.cm.cmUnram.2.1 e₁
  have hb := Eqv.star_alphaE D
  have hdec : ∀ y : D.host.E, ∃ p q : D.host.F,
      y = algebraMap D.host.F D.host.E p + algebraMap D.host.F D.host.E q * Eqv.alphaE D := by
    intro y
    refine ⟨(Eqv.basE D).repr y 0, (Eqv.basE D).repr y 1, ?_⟩
    conv_lhs => rw [← (Eqv.basE D).sum_repr y]
    rw [Fin.sum_univ_two, Eqv.basE_zero, Eqv.basE_one, Algebra.smul_def, Algebra.smul_def, mul_one]
  have hb2 : e₂ (Eqv.alphaE D) ^ 2 = e₁ (Eqv.alphaE D) ^ 2 := by
    have h1 : star (Eqv.alphaE D ^ 2) = Eqv.alphaE D ^ 2 := by rw [star_pow, hb]; ring
    obtain ⟨t, ht⟩ := (D.sp.cm.fixed _).1 h1
    rw [← map_pow, ← map_pow, ← ht, h]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hb2 with hc | hc
  · left
    intro y
    obtain ⟨p, q, rfl⟩ := hdec y
    rw [map_add, map_add, map_mul, map_mul, hc, h, h]
  · right
    intro y
    obtain ⟨p, q, rfl⟩ := hdec y
    rw [← hconj, star_add, star_mul, Eqv.star_algebraMapF, Eqv.star_algebraMapF, hb, map_add, map_add, map_mul, map_mul,
      map_neg, hc, h, h]
    ring

theorem exists_piInf (τ : D.what₂.Tau) (p : GlobalTheory.AdelicU.EmbOver D.host.E (Eqv.plW D τ)) :
    ∃ c : ℂ →+* ℂ, Continuous c ∧ (∀ (t : ℝ) z, c (t • z) = t • c z) ∧
      ∀ y : AE D, Eqv.psiT D τ y = c (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf p y) := by
  have key : ∀ c : ℂ →+* ℂ, (∀ t : ℝ, c t = t) → (∀ x, tauE D τ x = c (p.1 x)) →
      ∀ y : AE D, Eqv.psiT D τ y = c (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf p y) := by
    intro c hc hx y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, ha, hb]
    | tmul a x =>
      have l1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf p (a ⊗ₜ[D.host.F] x) = Eqv.gW D (Eqv.plW D τ) (fstA D.host.F a) * p.1 x :=
        GlobalTheory.AdelicU.infEmb_tmul p _ x
      have l2 : Eqv.psiT D τ (a ⊗ₜ[D.host.F] x) = Eqv.gW D (Eqv.plW D τ) (fstA D.host.F a) * tauE D τ x :=
        Eqv.thetaC_tmul D τ _ x
      rw [l1, l2, map_mul, hx, Eqv.gW_real, hc]
  rcases emb_eq_or_conj p.1 (tauE D τ) (fun a => RingHom.congr_fun (p.2.trans (Eqv.plW_embedding D τ)) a) with h | h
  · exact ⟨RingHom.id ℂ, continuous_id, fun _ _ => rfl, key _ (fun _ => rfl) h⟩
  · exact ⟨starRingEnd ℂ, Complex.continuous_conj, fun t z => by simp, key _ Complex.conj_ofReal h⟩

theorem kapX_surj (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (k : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) : ∃ h, kapX X e hJ h = k := by
  subst hJ
  have h1 : (k.1.1)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • reindex e e X.gramᵀ) * (k.1.1).map (cA D) =
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • reindex e e X.gramᵀ) := k.2
  rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at h1
  have hx : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have h2 := congrArg (fun Y => ((incA D D.host.xi0⁻¹ • Y)ᵀ).submatrix e e) h1
  simp only [smul_smul, ← map_mul, inv_mul_cancel₀ hx, map_one, one_smul, transpose_mul,
    transpose_transpose, ← Matrix.mul_assoc] at h2
  rw [← submatrix_mul_equiv _ _ _ e, ← submatrix_mul_equiv _ _ _ e] at h2
  have e1 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (reindex e e X.gramᵀ))ᵀ.submatrix e e = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram := by
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  rw [e1] at h2
  refine ⟨⟨Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom k.1, h2⟩, Subtype.ext (Units.ext ?_)⟩
  show reindex e e (reindex e.symm e.symm k.1.1) = k.1.1
  simp

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem lie_of_exp {n : ℕ} (Y H : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, (NormedSpace.exp (t • Y))ᴴ * H * NormedSpace.exp (t • Y) = H) : Yᴴ * H + H * Y = 0 := by
  have h1 := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) Yᴴ (0 : ℝ)).mul_const H).fun_mul
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ))
  have h2 : (fun t : ℝ => NormedSpace.exp (t • Yᴴ) * H * NormedSpace.exp (t • Y)) = fun _ => H := by
    funext t
    have e : t • Yᴴ = (t • Y)ᴴ := by rw [Matrix.conjTranspose_smul, star_trivial]
    rw [e, Matrix.exp_conjTranspose]
    exact h t
  have h3 := (h1.congr_of_eventuallyEq (f₁ := fun _ => H)
    (Filter.Eventually.of_forall fun t => (congrFun h2 t).symm)).unique (hasDerivAt_const _ _)
  simpa using h3

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem exp_map {n d : ℕ} (e : Fin n ≃ Fin d) (c : ℂ →+* ℂ) (hc : Continuous c) (Z : Matrix (Fin d) (Fin d) ℂ) :
    ((NormedSpace.exp Z).map c).submatrix e e = NormedSpace.exp ((Z.map c).submatrix e e) :=
  NormedSpace.map_exp ((Matrix.reindexAlgEquiv ℂ ℂ e.symm).toRingHom.comp c.mapMatrix)
    ((continuous_id.matrix_map hc).matrix_submatrix e e) Z

end GlobalTheory.LineAtPlace

open GlobalTheory.LineAtPlace in
theorem GlobalTheory.LineAtPlace.exists_oneP : ∀ (D : D7) (θ : InfFam D) (X : HSp D), IsInfFam θ → ∀ {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ)
    (emb : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w) (w : InfinitePlace D.host.F)
    (Z : Matrix (Fin d) (Fin d) ℂ) (γ : Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Wd.J),
    γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd →
    (∀ t : ℝ, (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (emb w)) =
      NormedSpace.exp (t • Z)) →
    (∀ (t : ℝ) (w' : InfinitePlace D.host.F), w' ≠ w →
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (emb w')) = 1) →
    ∃ (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ), Y ∈ lieAt X τ ∧
      ∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hJ (oneP θ X τ Y t) := by
  intro D θ X hθ d e Wd hJ emb w Z γ hγ hw ho
  obtain rfl := Eqv.eq_thetaC D hθ
  obtain ⟨τ, rfl⟩ : ∃ τ, Eqv.plW D τ = w := ⟨_, Eqv.plW_symm D w⟩
  choose h hh using fun t : ℝ => kapX_surj X e hJ (γ (Multiplicative.ofAdd t))
  have hm : ∀ t, Eqv.matA D X (h t) = (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).submatrix e e := by
    intro t
    rw [← hh t]
    show _ = (reindex e e (Eqv.matA D X (h t))).submatrix e e
    simp
  obtain ⟨c, hc, hcs, hp⟩ := exists_piInf τ (emb _)
  have h1 : ∀ t : ℝ, infMat D.sp.cm.sig X.gram (Eqv.thetaC D τ) (h t) =
      NormedSpace.exp (t • (Z.map c).submatrix e e) := by
    intro t
    have e1 : t • (Z.map c).submatrix e e = ((t • Z).map c).submatrix e e := by
      ext i j
      exact (hcs t _).symm
    rw [Eqv.infMat_thetaC, hm, e1, ← exp_map e c hc, ← hw]
    ext i j
    exact hp _
  have hu : ∀ t : ℝ, (NormedSpace.exp (t • (Z.map c).submatrix e e))ᴴ * gramAt D X τ *
      NormedSpace.exp (t • (Z.map c).submatrix e e) = gramAt D X τ := by
    intro t
    rw [← h1]
    exact Eqv.infMat_unitary' D X (h t) τ
  refine ⟨τ, (Z.map c).submatrix e e, lie_of_exp _ _ hu, fun t => ?_⟩
  rw [← hh t, oneP, Eqv.atTau_eq D X τ _ (hu t)]
  congr 1
  apply Eqv.matA_inj D X
  rw [Eqv.matA_atH]
  refine Eqv.matA_of_isAtTau D X ⟨(Eqv.mem_GinfC D X _).2 ?_, h1 t, fun ρ hρ => ?_⟩
  · ext i j
    have k1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t)) (e i) (e j) - (1 : Matrix _ _ (AE D)) (e i) (e j)) :=
      fun u hu => congrFun (congrFun (hγ.2 _ u hu) (e i)) (e j)
    have k2 := GlobalTheory.ConjInfExp.finPart_eq_one
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t)) (e i) (e j) - (1 : Matrix _ _ (AE D)) (e i) (e j) + 1)
      (by rwa [add_sub_cancel_right])
    rw [RingHom.map_add, RingHom.map_one, add_eq_right, RingHom.map_sub, sub_eq_zero] at k2
    rw [Matrix.map_apply, hm, submatrix_apply, k2]
    by_cases k : i = j
    · subst k; simp
    · simp [Matrix.one_apply_ne k, Matrix.one_apply_ne (e.injective.ne k)]
  · obtain ⟨c', -, -, hp'⟩ := exists_piInf ρ (emb _)
    have k1 : Eqv.plW D ρ ≠ Eqv.plW D τ := fun k => hρ (by rw [← Eqv.symm_plW D ρ, k, Eqv.symm_plW])
    rw [Eqv.infMat_thetaC, hm]
    ext i j
    have k2 := congrFun (congrFun (ho t _ k1) (e i)) (e j)
    rw [Matrix.map_apply] at k2
    rw [Matrix.map_apply, submatrix_apply, hp', k2]
    by_cases k : i = j
    · subst k; simp
    · simp [Matrix.one_apply_ne k, Matrix.one_apply_ne (e.injective.ne k)]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedLocalTotalTensorFixedByInnerVertexLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipVertexInv

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.TopLevelInv

theorem flips_isAdmissible {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} {ψ : AddChar k Circle} {ϖ : kˣ}
    {e : ℕ} (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (he : 1 ≤ e) :
    ∀ (l : List (ℕ × ℕ)) (St : Γ.PiLocalization₂), (∀ x ∈ l, CondLE ϖ e (Γ.nu x.1 x.2)) → CanFlip St.path l →
      (∀ X, IsOpen (St.level X : Set (GL (Fin (Γ.rank X)) k)) ∧ St.level X ≤ KO k _) → St.IsAdmissible .one ϖ e →
      (St.flips .one ψ ϖ e l).IsAdmissible .one ϖ e := by
  intro l
  induction l with
  | nil => intro St _ _ _ hT; exact hT
  | cons x l ih =>
    intro St hν hc hJ hT
    obtain _ | ⟨hp, hc'⟩ := hc
    refine ih (St.flip .one ψ ϖ e x) (fun y hy => hν y (List.mem_cons_of_mem _ hy)) hc' (fun X => ?_)
      (GlobalTheory.T.splitThetaGrid_isAdmissible_flipTensor ψ ϖ e hϖ hψ he St x (hν x List.mem_cons_self) hp hJ hT)
    change IsOpen (Γ.flipLevel x.1 x.2 St.level X : Set (GL (Fin (Γ.rank X)) k)) ∧ Γ.flipLevel x.1 x.2 St.level X ≤ _
    by_cases hX : X = (x.1 + 1, x.2 + 1)
    · subst hX; simp only [Grid.flipLevel, Function.update_self]; exact ⟨isOpen_KO, le_rfl⟩
    · simp only [Grid.flipLevel, Function.update_of_ne hX]; exact hJ X

theorem mem_flipOrder {m : ℕ} {x : ℕ × ℕ} (hx : x ∈ flipOrder m) : x.1 < m ∧ x.2 < m := by
  simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, j, hj, rfl⟩ := hx
  exact ⟨hi, hj⟩

theorem mem_inner_opposite {m j : ℕ} (hj : j + 1 < m) : (j + 1, m) ∈ innerVertices (oppositePath m) := by
  obtain ⟨n, hn⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have h : Edge.ex (j + 1) m ∈ (oppositePath m).tail := by
    rw [oppositePath, hn, List.range_succ_eq_map, List.map_cons, List.cons_append, List.tail_cons]
    exact List.mem_append_left _ (List.mem_map.2 ⟨j + 1, List.mem_map.2 ⟨j, List.mem_range.2 (by omega), rfl⟩, rfl⟩)
  exact List.mem_map.2 ⟨_, h, rfl⟩

theorem main : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} (Φ : G.Datum), t ∈ U → ∀ {μ₀ : T}, L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → ∀ (w : Pl D.host.E), w ∈ locPl G t → ∀ (j : ℕ), j + 1 < D.R.m →
    ∀ (κ : GL (Fin ((locGrid G t w).rank (j + 1, D.R.m))) (Kw w)), κ ∈ givenLevel G t w (j + 1, D.R.m) →
    (locGrid G t w).pathAct .one (oppositePath D.R.m) (Pi.mulSingle (j + 1, D.R.m) κ) (Tflip W S.B t Φ w) =
      Tflip W S.B t Φ w := by
  intro D T L sc G W U S t Φ _ μ₀ hL hde hc w hw j hj κ hκ
  have hg := (Good.locGrid_isGood hL G W t hde hc).1 w hw
  have hm : 0 < D.R.m := by omega
  have h00 := hg.square 0 hm 0 hm
  have hν : ∀ x ∈ flipOrder D.R.m, CondLE (unifAt w) (depthAt G w) ((locGrid G t w).nu x.1 x.2) := by
    intro x hx
    obtain ⟨hi, hj⟩ := mem_flipOrder hx
    rw [← Grid.alpha_div_beta]
    exact (hg.square x.1 hi x.2 hj).condν
  have hfl : (flipStage t w S.B W Φ).IsAdmissible .one (unifAt w) (depthAt G w) :=
    flips_isAdmissible h00.unif h00.cond h00.one_le (flipOrder D.R.m) (givenStage t w S.B Φ) hν (canFlip_flipOrder _).1
      (fun X => GivenAdm.givenLevel_open hL hw X) (GivenAdm.givenStage_isAdmissible hL S.B t Φ hw)
  obtain ⟨hp, hl⟩ := flipStage_path_level t w S.B W Φ
  have := hfl.invariant (j + 1, D.R.m) (hp ▸ mem_inner_opposite hj) κ (hl ▸ hκ)
  rw [hp] at this
  exact this

end GlobalTheory.FlipVertexInv
end

