import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Saturated
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.PointRingCommRing
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0005
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0314
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0238
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0267
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsOverLettersOfCrysWith
section
noncomputable section

open GlobalTheory.WachUse GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing

namespace GlobalTheory.WachUse.HeightsProof

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem letφ_letE (i : ZMod n) : letφ W.φ₀ (letE (i - 1) : LetA O n) = letE i := by
  funext j
  change W.φ₀ ((letE (i - 1) : LetA O n) (j - 1)) = (letE i : LetA O n) j
  by_cases hj : j = i
  · subst hj
    simp [letE]
  · have hj' : j - 1 ≠ i - 1 := fun h => hj (sub_left_injective h)
    simp [letE, hj, hj']

theorem φD_letE (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T) :
    W.φD T ((letE (i - 1) : LetA O n) • x) = (letE i : LetA O n) • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O n) W.EE (letE (i - 1))) x
  rwa [algebraMap_smul, W.φE_ext, algebraMap_smul, letφ_letE] at this

theorem Nl_le (T : LocLat G Qp LL O) (i : ZMod n) : W.Nl T i ≤ W.N T := by
  rintro _ ⟨x, hx, rfl⟩
  exact (W.N T).smul_mem _ hx

theorem of_heightBounds (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) (hb : HeightBounds W T M h) (i : ZMod n) :
    (∀ x ∈ W.N T, W.Q ^ M i • (letE i : LetA O n) • W.φD T x ∈ W.N T) ∧
      ∀ y ∈ W.N T, W.Q ^ h i • (letE i : LetA O n) • y ∈ W.φpull T := by
  refine ⟨fun x hx => Nl_le W T i ((hb i).1 _ ?_), fun y hy => ?_⟩
  · rw [← φD_letE]
    exact Submodule.subset_span ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  · exact Submodule.span_mono (Set.image_mono (Nl_le W T (i - 1))) ((hb i).2 _ ⟨y, hy, rfl⟩)

theorem jumpsOverLetters_of_crysWith (T : LocLat G Qp LL O) [FiniteDimensional LL ↥(DdR PD T.ρ)]
    (U : ZMod n → Multiset ℤ) (M h : ZMod n → ℕ) (hU : CrysWith PD W.emb T.ρ U)
    (hb : ∀ i, ∀ u ∈ U i, -(M i : ℤ) ≤ u ∧ u ≤ h i) : JumpsOverLetters W T M h := by
  intro i τ hτ a ha
  have h1 := (GlobalTheory.Per.JumpMult.jump_iff_of_finite PD T.ρ τ a).2.2.1 ha
  rw [hU.2 i τ hτ a] at h1
  exact hb i a (Multiset.count_ne_zero.1 (by exact_mod_cast h1))

end Generic

theorem heights_of_finite {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P}
    {E : LocFon l P AI H} {C : LocCmpT l P AI H E} (hJ : HeightsFromJumps l P AI H E C)
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (hfin : ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), FiniteDimensional ↥LL.1 ↥(DdR (P.PD K) T.ρ)) :
    Heights (H.W K s LL h) := by
  intro T U M hh hU hb
  haveI := hfin T
  exact of_heightBounds _ T M hh
    (hJ K s LL h T hU.1 M hh (jumpsOverLetters_of_crysWith _ T U M hh hU hb)).1

theorem heights_of_caseA : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P) (E : LocFon l P AI H) (C : LocCmpT l P AI H E), Nonempty (LocTied l P AI) → GlobalTheory.IndefiniteRowSideFullHecke.PointRingCommRing.HeightsFromJumps l P AI H E C → ∀ (K LL : FinExt l) (h : CaseA K LL), Heights (H.W K 1 LL h.2.2) := by
  rintro l _ P AI H E C ⟨Ti⟩ hJ K LL h
  exact heights_of_finite hJ K 1 LL h.2.2 fun T => (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI Ti K LL T.V T.ρ).1

end GlobalTheory.WachUse.HeightsProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthsModuloSubmoduleAgree
section
noncomputable section

namespace GlobalTheory.LenModAgree

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem lenMod_eq {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (S H : Submodule O M) :
    BlochKatoDuality.lenMod S H = lenModN S H := by
  unfold BlochKatoDuality.lenMod lenModN
  have h := (LinearMap.quotientInfEquivSupQuotient S H).length_eq
  rw [← h]
  have e : Submodule.comap S.subtype S ⊓ Submodule.comap S.subtype H = Submodule.comap S.subtype H := by simp
  exact (Submodule.quotEquivOfEq _ _ e).length_eq

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem main : (∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (A H : Submodule O M), lenModN A H = BlochKatoDuality.lenMod A H) ∧ ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (e : ℕ), LocBoundP i w hw r Xs M e ↔ LocBound i w hw r Xs M e := by
  refine ⟨fun O M _ _ _ A H => (lenMod_eq A H).symm, ?_⟩
  intro D i w hw r Xs k M e
  unfold LocBoundP LocBound
  rw [lenMod_eq]

end GlobalTheory.LenModAgree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LettersFree
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.LetterFree

theorem letters_free : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), WachLatticeFreeGlobal D HW F := by
  intro D HW F l _ K s LL h T hT
  obtain ⟨hd, -, hb⟩ := letters_loc (HW l) K s LL h T hT
  refine ⟨hd.2.symm, fun i => ?_⟩
  obtain ⟨b, hb1, hb2⟩ := hb i
  exact ⟨_, b, hb1, hb2⟩

end GlobalTheory.NL.LetterFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLeConjugateSplit
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler GlobalTheory.CMVal.Euler.SplitPair

namespace GlobalTheory.LamTie.ConjLevel

variable {E : Type} [Field E] [NumberField E]

theorem exists_cong_one [IsCMField E] {v : HeightOneSpectrum (OF E)} (hs : Splits v) {P : HeightOneSpectrum (𝓞 E)}
    (hP : Over P v) (z : P.adicCompletion E) (hz : Valued.v z ≤ 1) :
    ∃ a : OF E, Valued.v (iota a P - z) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  obtain ⟨-, hef⟩ := GlobalTheory.CMVal.Euler.SplitPlace.split_place E v hs
  obtain ⟨b, hb⟩ := exists_int_cong P z hz
  obtain ⟨a, ha⟩ := (hef P hP).2.2 b
  have h3 := OrderUnits.val_int_le P 1 _ (by simpa using ha)
  refine ⟨a, ?_⟩
  rw [map_sub (algebraMap (𝓞 E) E), map_sub (algebraMap E (Af E)), sub_coord] at h3
  have := Valuation.map_sub_le _ hb h3
  rw [sub_sub_sub_cancel_left] at this
  exact this

theorem exists_cong [IsCMField E] {v : HeightOneSpectrum (OF E)} (hs : Splits v) {P : HeightOneSpectrum (𝓞 E)}
    (hP : Over P v) (m : ℕ) (z : P.adicCompletion E) (hz : Valued.v z ≤ 1) :
    ∃ a : OF E, Valued.v (iota a P - z) ≤ WithZero.exp (-(m : ℤ)) := by
  obtain ⟨-, hef⟩ := GlobalTheory.CMVal.Euler.SplitPlace.split_place E v hs
  induction m with
  | zero => exact ⟨0, by simpa [iota_zero, zero_coord] using hz⟩
  | succ m ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨t, ht, ht'⟩ := Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top m
    have hv : Valued.v (iota t P) = WithZero.exp (-(m : ℤ)) := by
      refine eq_exp_of_le (val_iota_le_of_mem hP m ht) fun h3 => ht' ?_
      rw [← (hef P hP).2.1, ← val_iota_le_iff]
      convert h3 using 2
      push_cast; ring
    have ht0 : iota t P ≠ 0 := fun h => by
      rw [h, map_zero] at hv
      exact WithZero.exp_ne_zero hv.symm
    obtain ⟨c, hc⟩ := exists_cong_one hs hP ((iota a P - z) / iota t P) (by
      rw [map_div₀, hv, div_le_one₀ WithZero.exp_pos]; exact ha)
    refine ⟨a - t * c, ?_⟩
    have : iota (a - t * c) P - z = -(iota t P * (iota c P - (iota a P - z) / iota t P)) := by
      rw [iota_sub, iota_mul, sub_coord, mul_coord]; field_simp; ring
    rw [this, Valuation.map_neg, map_mul, hv]
    refine (mul_le_mul' le_rfl hc).trans_eq ?_
    rw [← WithZero.exp_add]
    congr 1
    push_cast; ring

theorem levelLe_of_split [IsCMField E] {χ : HChar E} (hF : TrivOnF χ) {v : HeightOneSpectrum (OF E)} (hs : Splits v)
    {P P' : HeightOneSpectrum (𝓞 E)} (hP : Over P v) (hP' : Over P' v) {n : ℕ} (hn : LevelLe χ P n) : LevelLe χ P' n := by
  by_cases hne : P = P'
  · exact hne ▸ hn
  obtain ⟨h2, hef⟩ := GlobalTheory.CMVal.Euler.SplitPlace.split_place E v hs
  have hmul := loc_mul_loc hF hP hP' hne (h2 P P' hP hP' hne)
  obtain ⟨m, hm⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ P'
  intro u hu hu'
  have hu1 : Valued.v (u : P'.adicCompletion E) = 1 := hu
  obtain ⟨a, h4⟩ := exists_cong hs hP' (m + n + 1) u hu1.le
  have hlt : WithZero.exp (-((m + n + 1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hlt1 : WithZero.exp (-((1 : ℕ) : ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have h5 : Valued.v (iota a P') = 1 := by
    rw [Valuation.map_eq_of_sub_lt _ (hu1 ▸ h4.trans_lt hlt), hu1]
  have hav : a ∉ v.asIdeal ^ 1 := fun h => (h5 ▸ val_iota_le_of_mem hP' 1 h).not_gt hlt1
  have ha0 : a ≠ 0 := fun h => hav (h ▸ zero_mem _)
  have hunit : Valued.v (iota a P) = 1 := by
    have := eq_exp_of_le (m := 0) (by simpa using val_iota_le_one P a) fun h3 => hav (by
      rw [← (hef P hP).2.1, ← val_iota_le_iff]
      simpa using h3)
    simpa using this
  have hsub : a - 1 ∈ v.asIdeal ^ n := by
    rw [← (hef P' hP').2.1, ← val_iota_le_iff, iota_sub, iota_one, sub_coord, one_coord]
    have := Valuation.map_add_le _ (h4.trans (WithZero.exp_le_exp.2
      (show -((m + n + 1 : ℕ) : ℤ) ≤ -(n : ℤ) by omega))) hu'
    rwa [sub_add_sub_cancel] at this
  have h6 : χ.loc P (locF P a ha0) = 1 := by
    refine hn _ hunit ?_
    have := val_iota_le_of_mem hP n hsub
    rw [iota_sub, iota_one, sub_coord, one_coord] at this
    exact this
  have h7 := hmul a ha0
  rw [h6, one_mul] at h7
  have h8 : χ.loc P' (locF P' a ha0 / u) = 1 := by
    refine hm _ ?_ ?_
    · show Valued.v ((locF P' a ha0 / u : (P'.adicCompletion E)ˣ) : P'.adicCompletion E) = 1
      rw [Units.val_div_eq_div_val, map_div₀, coe_locF, h5, hu1, div_one]
    · rw [Units.val_div_eq_div_val, div_sub_one u.ne_zero, map_div₀, hu1, div_one, coe_locF]
      exact h4.trans (WithZero.exp_le_exp.2 (by omega))
  rw [map_div, div_eq_one, h7] at h8
  exact h8.symm

open Formalism.BasicNotions GlobalTheory.ToricDenom in

theorem levelLe_conj : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (χ : Formalism.L2.Host.HChar H.E), χ.TrivOn H.F →
    ∀ w w' : HeightOneSpectrum (𝓞 H.E), below w = below w' → Splits (below w) → ∀ n : ℕ, χ.LevelLe w n → χ.LevelLe w' n := by
  intro R H χ hF w w' hw hs n hn
  have : IsCMField H.E := H.isCMField_hostE
  exact levelLe_of_split hF hs (over_below w) (hw ▸ over_below w') hn

end GlobalTheory.LamTie.ConjLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLeOfLe
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem levelLe_of_le {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {m m' : ℕ}
    (h : χ.LevelLe w m) (hm : m ≤ m') : χ.LevelLe w m' := by
  intro x hx hv

  refine h x hx (le_trans hv ?_)
  rw [WithZero.exp_le_exp]
  omega

theorem expAt_mul_inv : ∀ (E : Type) [Field E] [NumberField E] (χ χ' : Formalism.L2.Host.HChar E) (w : HeightOneSpectrum (𝓞 E)) (n : ℕ),
    1 ≤ n → ExpAt χ w n → χ'.LevelLe w (n - 1) → ExpAt (χ' * χ⁻¹) w n := by
  intro E _ _ χ χ' w n hn hχ hχ' m
  constructor
  · intro hm

    by_contra hlt
    have h1 : (χ' * χ⁻¹).LevelLe w (n - 1) := levelLe_of_le hm (by omega)
    have h2 : χ.LevelLe w (n - 1) := by
      have h3 := Formalism.L2.Host.HChar.LevelLe.mul (Formalism.L2.Host.HChar.LevelLe.inv h1) hχ'
      have h4 : (χ' * χ⁻¹)⁻¹ * χ' = χ := by group
      rwa [h4] at h3
    have := (hχ (n - 1)).mp h2
    omega
  · intro hm

    have hc : χ.LevelLe w m := (hχ m).mpr hm
    have hc' : χ'.LevelLe w m := levelLe_of_le hχ' (by omega)
    exact Formalism.L2.Host.HChar.LevelLe.mul hc' (Formalism.L2.Host.HChar.LevelLe.inv hc)

end GlobalTheory.LamTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftFMonoLoc
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

noncomputable section

namespace GlobalTheory.StepLiftPf

section Mono

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V'] [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem liftF_mono {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'} (F : LatHom L L') {e e' : ℕ}
    (hF : F.LiftF PD e) (he : e ≤ e') : F.LiftF PD e' := by
  intro c hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add, mul_comm, mul_smul]
  exact (F.ImF PD).smul_mem _ (hF c hc)

end Mono

section MonoLoc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem liftF_mono_loc {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {e e' : ℕ}
    (hF : F.LiftF PD e) (he : e ≤ e') : F.LiftF PD e' :=
  liftF_mono PD F hF he

end MonoLoc

section Core

variable {l : ℕ} [Fact l.Prime]

theorem incl_cont {K K' : FinExt l} (h : K.1 ≤ K'.1) : Continuous (Subgroup.inclusion (GK_le h)) :=
  Continuous.subtype_mk continuous_subtype_val _

theorem sub_props (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal)
    (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c')
    (hFont : TruncatedSeriesCountingIdentities.FontaineAt (P.PD K') ↥LL.1 ↥(OL LL))
    {ι : Type} {k : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1))
    (hc : ∀ x, Continuous (Ms x))
    (Sig : Finset ((pc P h hN hF hS).Iner →* (↥LL.1)ˣ))
    (htr : ∀ a ∈ Sig, ∀ g : (pc P h hN hF hS).Iner, (g : ↥(GK K)) ∈ (pc P h hN hF hS).H → a g = 1)
    (hcop : ∀ a ∈ Sig, Nat.Coprime (orderOf a) (pc P h hN hF hS).PD.p)
    (hpot : ∀ x, (pc P h hN hF hS).IsPotCrys (matRep (Ms x)))
    (hin : ∀ x, (pc P h hN hF hS).InertiaThrough (matRep (Ms x)) Sig)
    (U : Set ℤ) (hJ : ∀ x τ, JumpsInV (P.PD K) (matRep (Ms x)) τ U)
    (W : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hW : IsSubFam Ms W) :
    (pc P h hN hF hS).IsPotCrys W.ρ ∧ (pc P h hN hF hS).InertiaThrough W.ρ Sig ∧
      ∀ τ, JumpsInV (P.PD K) W.ρ τ U := by
  refine ⟨?_, GlobalTheory.inertiaThrough_of_isSubFam l P K K' LL h hN hF hS ι k Ms W hW Sig htr hcop hin,
    fun τ => GlobalTheory.Pass.jumpsInV_of_isSubFam l P K LL ι k Ms W hW τ U fun x => hJ x τ⟩
  let incl := Subgroup.inclusion (GK_le h)
  have hincl : Continuous incl := incl_cont h
  let W' : GRep ↥(GK K') ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := W.V, ρ := W.ρ.comp incl, cont := fun x => (W.cont x).comp hincl }
  let Ms' : ι → (↥(GK K') →* Matrix (Fin k) (Fin k) ↥LL.1) := fun x => (Ms x).comp incl
  have hc' : ∀ x v, Continuous fun g => (Ms' x g).mulVec v :=
    fun x v => ((hc x).comp hincl).matrix_mulVec continuous_const
  have hcr' : ∀ x, IsCrys (P.PD K') (matRep (Ms' x)) := fun x =>
    (GlobalTheory.PcRes.main l P K K' LL h hN hF hS _ (matRep (Ms x))).2.1 (hpot x)
  have hsub : IsSubOfSums W'.ρ (fun x => ⇑(Ms' x)) := by
    obtain ⟨a, x, p, hp, hinj⟩ := hW
    refine ⟨a, x, LinearMap.pi p, ?_, fun g v => funext fun j => hp j (incl g) v⟩
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact hinj v fun j => congrFun hv j
  have hW' : IsCrys (P.PD K') W'.ρ :=
    (subsum_crys (PD := P.PD K') (Ms := Ms') (hc := hc') (hF := hFont) (S := fun _ => Set.univ)
      (hcr := hcr') (hS := fun _ _ _ _ => Set.mem_univ _) (A := W') (hA := hsub)).1
  exact (GlobalTheory.PcRes.main l P K K' LL h hN hF hS W.V W.ρ).2.2 hW'

end Core

section Apply

open Formalism.MainNotions.ElementDenominator

variable {l : ℕ} [Fact l.Prime]

set_option maxHeartbeats 1000000 in

theorem liftFam_core (P : LocPrime l) (K' LL : FinExt l) (h : (qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal)
    (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (qlExt l))) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      (P.PD (qlExt l)).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c')
    (CT : ℕ) (hT : thmT (pc P h hN hF hS) LL CT)
    (hFont : TruncatedSeriesCountingIdentities.FontaineAt (P.PD K') ↥LL.1 ↥(OL LL))
    {ι : Type} {k : ℕ} (Ms : ι → (↥(GK (qlExt l)) →* Matrix (Fin k) (Fin k) ↥LL.1))
    (hc : ∀ x, Continuous (Ms x)) (N η H : ℕ) (hN2 : 2 ≤ N) (hη : 1 ≤ η) (hηH : η < H)
    (hsize : CT * (H * N ^ 2 + N ^ 3) < l)
    (Sig : Finset ((pc P h hN hF hS).Iner →* (↥LL.1)ˣ)) (Fr : ↥(GK (qlExt l)))
    (hFr : (pc P h hN hF hS).IsFrob Fr) (hSt : FrobStable (pc P h hN hF hS).Iner Fr Sig)
    (h1 : 1 ∈ Sig) (hcard : Sig.card ≤ N)
    (htr : ∀ a ∈ Sig, ∀ g : (pc P h hN hF hS).Iner, (g : ↥(GK (qlExt l))) ∈ (pc P h hN hF hS).H → a g = 1)
    (hcop : ∀ a ∈ Sig, Nat.Coprime (orderOf a) (pc P h hN hF hS).PD.p)
    (hpot : ∀ x, (pc P h hN hF hS).IsPotCrys (matRep (Ms x)))
    (hin : ∀ x, (pc P h hN hF hS).InertiaThrough (matRep (Ms x)) Sig)
    (U : Finset ℤ) (hU : ∀ u ∈ U, -(η : ℤ) ≤ u ∧ u ≤ H) (hU0 : (0 : ℤ) ∈ U) (hUc : U.card ≤ N + 1)
    (hJ : ∀ x τ, JumpsInV (P.PD (qlExt l)) (matRep (Ms x)) τ (U : Set ℤ)) :
    LiftFam (O := ↥(OL LL)) (P.PD (qlExt l)) Ms (CT * (N * (N ^ 2 / 4) + η * (N + N ^ 2 / 4))) := by
  intro W₁ W₂ hW₁ hW₂ L₁ L₂ F hFo
  have k₁ := sub_props P (qlExt l) K' LL h hN hF hS hFont Ms hc Sig htr hcop hpot hin _ hJ W₁ hW₁
  have k₂ := sub_props P (qlExt l) K' LL h hN hF hS hFont Ms hc Sig htr hcop hpot hin _ hJ W₂ hW₂
  let T₁ : LocLat ↥(GK (qlExt l)) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := W₁.V, modO := W₁.modO, towO := W₁.towO, ρ := W₁.ρ, cont := W₁.cont, L := L₁ }
  let T₂ : LocLat ↥(GK (qlExt l)) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := W₂.V, modO := W₂.modO, towO := W₂.towO, ρ := W₂.ρ, cont := W₂.cont, L := L₂ }
  obtain ⟨h4, hL⟩ := hT T₁ T₂ F N η H U Sig Fr k₁.1 k₂.1 hFo hFr hSt h1 hcard hN2 k₁.2.1 k₂.2.1 hU hU0
    hUc hη hηH k₁.2.2 k₂.2.2 hsize
  have hr : rPrime (pc P h hN hF hS).Iner Fr Sig ≤ N ^ 2 / 4 :=
    (Nat.le_div_iff_mul_le (by norm_num)).2 (by rw [mul_comm]; exact h4)
  have he : CT * (N * rPrime (pc P h hN hF hS).Iner Fr Sig + η * (N + rPrime (pc P h hN hF hS).Iner Fr Sig)) ≤
      CT * (N * (N ^ 2 / 4) + η * (N + N ^ 2 / 4)) := by
    gcongr
  exact liftF_mono_loc (P.PD (qlExt l)) (T₁ := T₁) (T₂ := T₂) F hL he

end Apply

section Wrap

open Formalism.MainNotions.ElementDenominator

variable {l : ℕ} [Fact l.Prime]

set_option maxHeartbeats 1000000 in

theorem liftFam_of_eq (P : LocPrime l) (K K' LL : FinExt l) (hK : K = qlExt l) (CT : ℕ)
    (hT : ∀ (K' : FinExt l) (h : (qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
      (hS : ∀ (g : ↥(GK (qlExt l))) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
        (P.PD (qlExt l)).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c'),
      thmT (pc P h hN hF hS) LL CT)
    (hFont : ∀ K'' : FinExt l, TruncatedSeriesCountingIdentities.FontaineAt (P.PD K'') ↥LL.1 ↥(OL LL))
    {ι : Type} {k : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1))
    (hc : ∀ x, Continuous (Ms x)) (N η H : ℕ) (hN2 : 2 ≤ N) (hη : 1 ≤ η) (hηH : η < H)
    (hsize : CT * (H * N ^ 2 + N ^ 3) < l)
    (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c')
    (Sig : Finset ((pc P h hN hF hS).Iner →* (↥LL.1)ˣ)) (Fr : ↥(GK K))
    (hFr : (pc P h hN hF hS).IsFrob Fr) (hSt : FrobStable (pc P h hN hF hS).Iner Fr Sig)
    (h1 : 1 ∈ Sig) (hcard : Sig.card ≤ N)
    (hx : ∀ x, (pc P h hN hF hS).IsPotCrys (matRep (Ms x)) ∧
      (pc P h hN hF hS).InertiaThrough (matRep (Ms x)) Sig)
    (U : Finset ℤ) (hU : ∀ u ∈ U, -(η : ℤ) ≤ u ∧ u ≤ H) (hU0 : (0 : ℤ) ∈ U) (hUc : U.card ≤ N + 1)
    (hJ : ∀ x τ, JumpsInV (P.PD K) (matRep (Ms x)) τ (U : Set ℤ)) :
    LiftFam (O := ↥(OL LL)) (P.PD K) Ms (CT * (N * (N ^ 2 / 4) + η * (N + N ^ 2 / 4))) := by
  subst hK
  by_cases hne : Nonempty ι
  · obtain ⟨x0⟩ := hne
    exact liftFam_core P K' LL h hN hF hS CT (hT K' h hN hF hS) (hFont K') Ms hc N η H hN2 hη hηH hsize
      Sig Fr hFr hSt h1 hcard (hx x0).2.1 (hx x0).2.2.1 (fun x => (hx x).1) (fun x => (hx x).2)
      U hU hU0 hUc hJ
  · have hemp : ∀ x : ι, False := fun x => hne ⟨x⟩
    refine liftFam_core P K' LL h hN hF hS CT (hT K' h hN hF hS) (hFont K') Ms hc N η H hN2 hη hηH hsize
      {1} Fr hFr ?_ (Finset.mem_singleton_self _) (by rw [Finset.card_singleton]; omega) ?_ ?_
      (fun x => (hemp x).elim) (fun x => (hemp x).elim) U hU hU0 hUc hJ
    · intro a ha
      rw [Finset.mem_singleton] at ha
      subst ha
      exact ⟨1, Finset.mem_singleton_self _, fun _ _ _ => rfl⟩
    · intro a ha g _
      rw [Finset.mem_singleton] at ha
      subst ha
      rfl
    · intro a ha
      rw [Finset.mem_singleton] at ha
      subst ha
      rw [orderOf_one]
      exact Nat.coprime_one_left _

end Wrap

theorem main : StepLift := by
  intro D CT hT hFont i w hw hdeg ι Ms hc eta H hlt hsize hPot hJump
  obtain ⟨K', h, hN, hF, hS, Sig, Fr, hFr, hSt, h1, hcard, hx⟩ := hPot
  obtain ⟨U, hU, hU0, hUc, hJ⟩ := hJump
  have hK : (D.nbr i w hw).Kw = Formalism.MainNotions.ElementDenominator.qlExt (D.nd.l i) :=
    Subtype.ext (IntermediateField.finrank_eq_one_iff.1 hdeg)
  have hT' : Formalism.MainNotions.ElementDenominator.CorollaryALocal D.loc CT := hT
  have hnV : 2 ≤ D.R.nV + 1 := by
    have h5 := D.R.rank_add_five_le
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega
  have hcl : ∀ x, Continuous (Br.loc D.nbr i w hw (Ms x)) := by
    intro x
    have hfc : Continuous (D.nbr i w hw).toLL := continuous_subtype_val.comp (D.nbr i w hw).eO_cont
    have h1' : Continuous fun g : Br.G D.nbr i w hw => Ms x ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) :=
      (hc x).comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw))
    exact h1'.matrix_map hfc
  exact liftFam_of_eq (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL hK CT
    (fun K' h hN hF hS => hT' (D.nd.l i) K' h hN hF hS (D.nbr i w hw).LL)
    (fun K'' => hFont (D.nd.l i) K'' (D.nbr i w hw).LL)
    (fun x => Br.loc D.nbr i w hw (Ms x)) hcl (D.R.nV + 1) (eta + D.R.t + 1) H hnV (by omega) hlt hsize
    h hN hF hS Sig Fr hFr hSt h1 hcard hx U hU hU0 hUc hJ

end GlobalTheory.StepLiftPf
end
end

