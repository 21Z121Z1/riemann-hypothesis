import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0084
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0031
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0058
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0052
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0085
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RmulMul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0086
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0074
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0057
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0016
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryNormalisesStabil
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0064
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0080
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0049
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.HermitianPerpSubgroup
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.ColumnDimensionRational

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFamilyTraceVolumeConstStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFamily_trace_volume_const : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → ∀ Yy : Submodule L.O S.V, (Yy = (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O ∨ Yy = (perp L S.Hm (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1))).restrictScalars L.O) → (Λ ⊓ Yy).toAddSubgroup.relIndex (Λ' ⊓ Yy).toAddSubgroup = (Λ' ⊓ Yy).toAddSubgroup.relIndex (Λ ⊓ Yy).toAddSubgroup ∧ (Λ ⊓ Yy).toAddSubgroup.relIndex (Λ' ⊓ Yy).toAddSubgroup ≠ 0 ∧ (S.M d Λ ⊓ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O).toAddSubgroup.relIndex (Λ ⊓ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)).restrictScalars L.O).toAddSubgroup = β := by
  first | exact @GlobalTheory.HL.FamilyVol.family_vol | exact GlobalTheory.HL.FamilyVol.family_vol | (intros; apply GlobalTheory.HL.FamilyVol.family_vol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameClassTermsLeOverlatticeMasses
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ClassMass

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ}

theorem M_eq_Mof (S : Frames L r k) {C : Set S.FrP} {p : S.FrP} (hp : p ∈ C) {d : S.Datum}
    {Λ : Submodule L.O S.V} (hC : S.Fr d Λ = C) : S.M d Λ = S.Mof p.1 p.2 := by
  subst hC
  exact ((GlobalTheory.HL.FrameClass.frame_classes L r k S (S.fr d Λ) (S.fr' d Λ)).2.1 p hp).2.symm

theorem class_mass : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ C, S.IsCls C → ∀ p ∈ C, (∀ Q : ℕ → Prop, (S.sumData fun d => S.nT d C fun Λ => Q (S.be d Λ)) ≤ ∑' Mh : {Mh : Submodule L.O S.V // S.Mof p.1 p.2 ≤ Mh ∧ (∀ x ∈ Mh, x ∈ S.ME) ∧ (∀ x ∈ Mh, ∀ y ∈ Mh, S.h x y ∈ L.O) ∧ Q ((S.Mof p.1 p.2).toAddSubgroup.relIndex Mh.toAddSubgroup)}, S.massSig Mh) ∧ (S.sumData fun d => S.nT d C fun Λ => S.BBzero d Λ) = S.massSig (S.Mof p.1 p.2) := by
  intro F _ _ _ _ _ E _ _ _ L r k S C hC p hp
  have hM : ∀ d Λ, S.Fr d Λ = C → S.M d Λ = S.Mof p.1 p.2 := fun d Λ hF => M_eq_Mof S hp hF
  constructor
  · intro Q
    refine (GlobalTheory.T.sum_over_data_term_count_eq_lattice_mass L r k S C (fun d Λ => Q (S.be d Λ)) ?_).trans_le ?_
    · intro h hh d Λ hT hQ
      obtain ⟨-, -, -, hM', hsat', -⟩ := GlobalTheory.HL.ComplAct.main L r k S d Λ hT h hh
      show Q (S.be (h • d) (h • Λ))
      unfold Frames.be
      rw [hM', hsat']
      exact hQ
    · unfold Frames.massSig
      rw [ENNReal.tsum_comm]
      refine ENNReal.tsum_le_tsum fun o => ?_
      split_ifs with hcond
      · obtain ⟨d, hT, hQ, hF⟩ := hcond
        have hbasic := GlobalTheory.HL.TermBasic.term_basic L r k S d o.out hT
        have hSD : IsSD L S.Hm o.out := hbasic.1
        have hle : S.M d o.out ≤ S.sat o.out := hbasic.2.2.1
        rw [hM d o.out hF] at hle
        have hQ' : Q ((S.Mof p.1 p.2).toAddSubgroup.relIndex (S.sat o.out).toAddSubgroup) := by
          have h := hQ
          unfold Frames.be at h
          rw [hM d o.out hF] at h
          exact h
        refine le_trans (le_of_eq ?_) (ENNReal.le_tsum ⟨S.sat o.out, hle,
          fun x hx => (Submodule.mem_inf.mp hx).2,
          fun x hx y hy => (hSD.2 y).mpr (Submodule.mem_inf.mp hy).1 x (Submodule.mem_inf.mp hx).1, hQ'⟩)
        rw [if_pos ⟨hSD, rfl⟩]
      · exact zero_le
  · have hb : ∀ Λ : Submodule L.O S.V, (∃ d, S.IsTerm d Λ ∧ S.BBzero d Λ ∧ S.Fr d Λ = C) ↔
        (IsSD L S.Hm Λ ∧ S.sat Λ = S.Mof p.1 p.2) := by
      intro Λ
      constructor
      · rintro ⟨d, hT, hB, hF⟩
        exact ⟨(GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).1,
          (show S.M d Λ = S.sat Λ from hB).symm.trans (hM d Λ hF)⟩
      · rintro ⟨hSD, hsat⟩
        obtain ⟨d, hT, hF, hB⟩ := GlobalTheory.HL.PrimTerm.term_of_primitive L r k S Λ hSD C hC p hp hsat
        exact ⟨d, hT, hB, hF⟩
    refine (GlobalTheory.T.sum_over_data_term_count_eq_lattice_mass L r k S C (fun d Λ => S.BBzero d Λ) ?_).trans ?_
    · intro h hh d Λ hT hB
      obtain ⟨-, -, -, hM', hsat', -⟩ := GlobalTheory.HL.ComplAct.main L r k S d Λ hT h hh
      show S.M (h • d) (h • Λ) = S.sat (h • Λ)
      rw [hM', hsat']
      exact hB
    · unfold Frames.massSig
      exact tsum_congr fun o => if_congr (hb o.out) rfl rfl

end GlobalTheory.HL.ClassMass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameClassesTotalWeightLe
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TotalWeight

theorem natCast_pow_le_pow_of_exponent_le (q m a e e' : ℕ) (he : e ≤ e') (h1 : (1 : ℝ) ≤ (q : ℝ) ^ (m + a)) :
    (q : ℝ) ^ (e * m) ≤ ((q : ℝ) ^ (m + a)) ^ e' := by
  have h2 : (q : ℝ) ^ m ≤ (q : ℝ) ^ (m + a) := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        simpa using h1
      · simp [hm.ne']
    · exact pow_le_pow_right₀ (by exact_mod_cast hq) (Nat.le_add_right _ _)
  calc (q : ℝ) ^ (e * m) = ((q : ℝ) ^ m) ^ e := by rw [mul_comm, pow_mul]
    _ ≤ ((q : ℝ) ^ (m + a)) ^ e := pow_le_pow_left₀ (by positivity) h2 e
    _ ≤ _ := pow_le_pow_right₀ h1 he

theorem sumCls_one_le {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k)
    (h : ∃ d Λ, S.IsTerm d Λ) :
    (S.sumCls fun _ => 1) ≤ ENNReal.ofReal (S.Hp ^ (3 * (r + 1) ^ 2)) := by
  obtain ⟨d, Λ, hT⟩ := h
  obtain ⟨ha, hD, -, -, h1, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT
  have hth : 0 ≤ S.vth := by
    unfold Frames.vth
    split_ifs <;> norm_num
  have hHp : S.Hp = (S.q : ℝ) ^ ((S.vth + S.vD).toNat + S.a.toNat) := by
    unfold Frames.Hp
    rw [← zpow_natCast]
    congr 1
    push_cast
    rw [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg (add_nonneg hth hD)]
    ring
  refine (GlobalTheory.HL.ClassCount.sumCls_le_encard L r k S).trans
    ((GlobalTheory.IntClsCount.main L r k S hD).trans ?_)
  have he : r * (r + 1) ≤ 3 * (r + 1) ^ 2 := by nlinarith
  rw [hHp] at h1 ⊢
  have key := ENNReal.ofReal_le_ofReal (natCast_pow_le_pow_of_exponent_le S.q _ _ _ _ he h1)
  rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast] at key
  exact key

end GlobalTheory.HL.TotalWeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairAmplitudeMassRepsEqOrbits
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordAmp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
  {H : HermSp M V} {r k : ℕ} {P : LocNG.FPair H r} {S : Frames M.L r k}

open scoped Pointwise ENNReal Classical in
private lemma tsum_transversal_eq_tsum_orbits_lemma {T X G R : Type*} [Group G] [MulAction G X]
    [AddCommMonoid R] [TopologicalSpace R] (St : Subgroup G)
    (rel : T → T → Prop) (A B : Set T) (hB : _root_.Formalism.MainNotions.S.LocNG.IsTransv rel A B) (ℓ : T → X) (term : X → Prop)
    (p : T → Prop) (Q : X → Prop)
    (hterm : ∀ t ∈ A, term (ℓ t)) (hsurj : ∀ Λ, term Λ → ∃ t ∈ A, ℓ t = Λ)
    (hrel : ∀ t t', rel t t' ↔ ∃ g ∈ St, ℓ t' = g • ℓ t)
    (hinv : ∀ Λ, term Λ → ∀ g ∈ St, term (g • Λ))
    (hpQ : ∀ t ∈ A, (p t ↔ Q (ℓ t))) (hQ : ∀ Λ, term Λ → ∀ g ∈ St, Q Λ → Q (g • Λ))
    (f : X → R) (hf : ∀ Λ, term Λ → ∀ g ∈ St, f (g • Λ) = f Λ)
    (val : T → R) (hval : ∀ t ∈ A, val t = f (ℓ t)) :
    ∑' t : {t // t ∈ B ∧ p t}, val t.1
      = ∑' o : MulAction.orbitRel.Quotient St X,
          if term (Quotient.out o) ∧ Q (Quotient.out o) then f (Quotient.out o) else 0 := by
  obtain ⟨hBA, hcover, huniq⟩ := hB
  have key : ∀ Λ : X, ∃ g ∈ St,
      Quotient.out (Quotient.mk (MulAction.orbitRel St X) Λ) = g • Λ := fun Λ => by
    obtain ⟨⟨g, hg⟩, hgx⟩ := Quotient.mk_out (s := MulAction.orbitRel St X) Λ
    exact ⟨g, hg, hgx.symm⟩
  let toFun : {t // t ∈ B ∧ p t} →
      ↥{o : MulAction.orbitRel.Quotient St X | term (Quotient.out o) ∧ Q (Quotient.out o)} :=
    fun t => ⟨Quotient.mk _ (ℓ t.1), by
      obtain ⟨g, hg, he⟩ := key (ℓ t.1)
      have h1 := hterm _ (hBA t.2.1)
      show term (Quotient.out (Quotient.mk (MulAction.orbitRel St X) (ℓ t.1)))
        ∧ Q (Quotient.out (Quotient.mk (MulAction.orbitRel St X) (ℓ t.1)))
      rw [he]
      exact ⟨hinv _ h1 g hg, hQ _ h1 g hg ((hpQ _ (hBA t.2.1)).1 t.2.2)⟩⟩
  have hbij : Function.Bijective toFun := by
    constructor
    · rintro ⟨t, ht⟩ ⟨t', ht'⟩ heq
      have h2 : Quotient.mk (MulAction.orbitRel St X) (ℓ t) = Quotient.mk _ (ℓ t') :=
        congrArg Subtype.val heq
      obtain ⟨⟨g, hg⟩, hgx⟩ := Quotient.exact h2
      have : rel t' t := (hrel t' t).2 ⟨g, hg, hgx.symm⟩
      exact Subtype.ext (huniq _ ht'.1 _ ht.1 this).symm
    · rintro ⟨o, ho⟩
      obtain ⟨t0, ht0A, ht0⟩ := hsurj _ ho.1
      obtain ⟨y, hyB, hy⟩ := hcover t0 ht0A
      obtain ⟨g, hg, hgy⟩ := (hrel y t0).1 hy
      have hyA := hBA hyB
      have hQy : Q (ℓ y) := by
        have := hQ (ℓ t0) (hterm _ ht0A) g⁻¹ (inv_mem hg) (by rw [ht0]; exact ho.2)
        rwa [hgy, inv_smul_smul] at this
      refine ⟨⟨y, hyB, (hpQ y hyA).2 hQy⟩, Subtype.ext ?_⟩
      show Quotient.mk _ (ℓ y) = o
      rw [← Quotient.out_eq o, ← ht0, hgy]
      exact Quotient.sound ⟨⟨g⁻¹, inv_mem hg⟩, inv_smul_smul g _⟩
  let e := Equiv.ofBijective toFun hbij
  have hR : (∑' o : MulAction.orbitRel.Quotient St X,
      if term (Quotient.out o) ∧ Q (Quotient.out o) then f (Quotient.out o) else 0)
      = ∑' o : ↥{o : MulAction.orbitRel.Quotient St X |
          term (Quotient.out o) ∧ Q (Quotient.out o)}, f (Quotient.out o.1) := by
    refine Eq.trans ?_ (tsum_subtype _ (fun o => f (Quotient.out o))).symm
    refine tsum_congr fun o => ?_
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [hR, ← e.tsum_eq]
  refine tsum_congr fun t => ?_
  show val t.1 = f (Quotient.out (Quotient.mk _ (ℓ t.1)))
  obtain ⟨g, hg, he⟩ := key (ℓ t.1)
  rw [he, hf _ (hterm _ (hBA t.2.1)) g hg, hval _ (hBA t.2.1)]

open scoped Pointwise ENNReal Classical in
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k} in

theorem _root_.GlobalTheory.HL.CoordAmp.sums_eq (hM : M.OK) (c : _root_.GlobalTheory.HL.Coord P S)
    (R : _root_.Formalism.MainNotions.S.LocNG.Reps P) (d : _root_.Formalism.MainNotions.S.LocNG.Datum P)
    (p : _root_.Formalism.MainNotions.S.Loc.Term V M r → Prop) (Q : Submodule M.L.O S.V → Prop)
    (hpQ : ∀ t, _root_.Formalism.MainNotions.S.LocNG.IsTermOver P d t → (p t ↔ Q (c.lat t.abelian₂)))
    (hQ : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ h ∈ S.St, Q Λ → Q (h • Λ)) :
    _root_.Formalism.MainNotions.S.LocNG.amp R d p = S.amp (c.dat d) Q ∧
      (∑' t : {t // t ∈ R.RT d ∧ p t}, ENNReal.ofReal (_root_.Formalism.MainNotions.S.LocNG.mu P t.1))
        = S.mass (c.dat d) Q := by
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨-, -, hbij, hlatg, -, hmu⟩ := _root_.GlobalTheory.HL.CoordMass.transport M hM H r k P S c
  obtain ⟨-, -, -, hSt, -⟩ := _root_.GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  obtain ⟨hcorr, hex, -⟩ := _root_.GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c
  have hB := R.hRT d
  have hrel : ∀ t t', _root_.Formalism.MainNotions.S.LocNG.TRel P t t' ↔ ∃ g ∈ S.St,
      c.lat t'.abelian₂ = g • c.lat t.abelian₂ := by
    intro t t'
    unfold _root_.Formalism.MainNotions.S.LocNG.TRel
    constructor
    · rintro ⟨s, hs, he⟩
      exact ⟨c.grp s, (hSt s).1 hs, by rw [he, hlatg]⟩
    · rintro ⟨g, hg, he⟩
      refine ⟨c.grp.symm g, (hSt _).2 (by simpa using hg), hbij.1 ?_⟩
      rw [hlatg, MulEquiv.apply_symm_apply, he]
  have hterm_inv : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ g ∈ S.St, S.IsTerm (c.dat d) (g • Λ) :=
    fun Λ h g hg => (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S _ Λ h g hg).1
  have hom_inv : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ g ∈ S.St,
        S.om (c.dat d) (g • Λ) = S.om (c.dat d) Λ :=
    fun Λ h g hg => (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S _ Λ h g hg).2.1
  have hmu_inv : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ g ∈ S.St,
        S.mu (g • Λ) = S.mu Λ :=
    fun Λ h g hg => ((_root_.GlobalTheory.HL.volSt M.L r k S).1 Λ
      (_root_.GlobalTheory.HL.TermBasic.term_basic M.L r k S _ Λ h).1.1).2.2 g hg
  constructor
  · unfold _root_.Formalism.MainNotions.S.LocNG.amp _root_.GlobalTheory.HL.Frames.amp
    exact tsum_transversal_eq_tsum_orbits_lemma S.St (_root_.Formalism.MainNotions.S.LocNG.TRel P) _ _ hB
      (fun t => c.lat t.abelian₂) (S.IsTerm (c.dat d)) p Q
      (fun t ht => (hcorr d t ht).1) (fun Λ h => hex d Λ h) hrel hterm_inv hpQ hQ
      (fun Λ => (S.mu Λ : ℂ) * S.om (c.dat d) Λ)
      (fun Λ h g hg => by simp only [hmu_inv Λ h g hg, hom_inv Λ h g hg])
      (fun t => (_root_.Formalism.MainNotions.S.LocNG.mu P t : ℂ) * _root_.Formalism.MainNotions.S.LocNG.om P t)
      (fun t ht => by simp only [hmu t, (hcorr d t ht).2.1])
  · unfold _root_.GlobalTheory.HL.Frames.mass
    exact tsum_transversal_eq_tsum_orbits_lemma S.St (_root_.Formalism.MainNotions.S.LocNG.TRel P) _ _ hB
      (fun t => c.lat t.abelian₂) (S.IsTerm (c.dat d)) p Q
      (fun t ht => (hcorr d t ht).1) (fun Λ h => hex d Λ h) hrel hterm_inv hpQ hQ
      (fun Λ => ENNReal.ofReal (S.mu Λ))
      (fun Λ h g hg => by simp only [hmu_inv Λ h g hg])
      (fun t => ENNReal.ofReal (_root_.Formalism.MainNotions.S.LocNG.mu P t))
      (fun t _ => by simp only [hmu t])

open scoped Pointwise ENNReal Classical in
open ValuativeRel in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : _root_.Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
  {H : _root_.Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} {P : _root_.Formalism.MainNotions.S.LocNG.FPair H r} {S : _root_.GlobalTheory.HL.Frames M.L r k} in

theorem _root_.GlobalTheory.HL.CoordAmp.amp_mass_eq : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : _root_.Formalism.MainNotions.S.Loc.Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : _root_.Formalism.MainNotions.S.Loc.HermSp M V) (r k : ℕ)
    (P : _root_.Formalism.MainNotions.S.LocNG.FPair H r), ∀ (S : _root_.GlobalTheory.HL.Frames M.L r k) (c : _root_.GlobalTheory.HL.Coord P S),
    ∀ (R : _root_.Formalism.MainNotions.S.LocNG.Reps P) (d : _root_.Formalism.MainNotions.S.LocNG.Datum P),
    _root_.Formalism.MainNotions.S.LocNG.amp R d (_root_.Formalism.MainNotions.S.LocNG.BBne (H := H)) = S.amp (c.dat d)
        (fun Λ => ¬ S.BBzero (c.dat d) Λ) ∧
      _root_.Formalism.MainNotions.S.LocNG.amp R d (fun t => ¬ _root_.Formalism.MainNotions.S.LocNG.BBne (H := H) t) = S.amp (c.dat d)
        (S.BBzero (c.dat d)) ∧
      _root_.Formalism.MainNotions.S.LocNG.amp R d (fun _ => True) = S.amp (c.dat d) (fun _ => True) ∧
      (∑' t : R.RT d, ENNReal.ofReal (_root_.Formalism.MainNotions.S.LocNG.mu P t.1))
        = S.mass (c.dat d) (fun _ => True) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c R d
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨hcorr, -, -⟩ := _root_.GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c
  have hBB : ∀ Λ, S.IsTerm (c.dat d) Λ →
      ∀ h ∈ S.St,
        (S.BBzero (c.dat d) (h • Λ)
          ↔ S.BBzero (c.dat d) Λ) :=
    fun Λ hΛ h hh => (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S _ Λ hΛ h hh).2.2.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (_root_.GlobalTheory.HL.CoordAmp.sums_eq hM c R d _ _
      (fun t ht => (hcorr d t ht).2.2)
      (fun Λ hΛ h hh hq => by rwa [hBB Λ hΛ h hh])).1
  · exact (_root_.GlobalTheory.HL.CoordAmp.sums_eq hM c R d _ _
      (fun t ht => by rw [(hcorr d t ht).2.2, not_not])
      (fun Λ hΛ h hh hq => (hBB Λ hΛ h hh).2 hq)).1
  · exact (_root_.GlobalTheory.HL.CoordAmp.sums_eq hM c R d (fun _ => True) (fun _ => True)
      (fun _ _ => Iff.rfl) (fun _ _ _ _ _ => trivial)).1
  · rw [← (_root_.GlobalTheory.HL.CoordAmp.sums_eq hM c R d (fun _ => True) (fun _ => True)
      (fun _ _ => Iff.rfl) (fun _ _ _ _ _ => trivial)).2]
    exact ((Equiv.subtypeEquivRight (fun t => by simp)).tsum_eq
      (fun t => ENNReal.ofReal (_root_.Formalism.MainNotions.S.LocNG.mu P t.1))).symm

end GlobalTheory.HL.CoordAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairTsumRepsEqConstMulOrbits
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordSum

theorem tsum_reps_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), ∃ κ : ℝ, 0 ≤ κ ∧ ∀ φ : S.Datum → ℝ≥0∞, (∀ h ∈ S.H0, ∀ δ, φ (h • δ) = φ δ) → (∀ δ, (¬ ∃ Λ, S.IsTerm δ Λ) → φ δ = 0) → (∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * φ (c.dat d.1)) = ENNReal.ofReal κ * S.sumData φ := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c R d0
  have := hM.loc
  have := hM.char0
  obtain ⟨κ, hκ0, hκ⟩ := GlobalTheory.T.exists_wt_eq_mul_nu' M hM H r k P S c d0
  obtain ⟨-, -, hrel, -, -⟩ := GlobalTheory.HL.CoordDatum.transport M hM H r k P S c
  obtain ⟨-, -, hex⟩ := GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver M hM H r k P S c
  refine ⟨κ, hκ0, fun φ hφ hφ0 => ?_⟩

  have hmove : ∀ h ∈ S.H0, ∀ δ : S.Datum, (∃ Λ, S.IsTerm δ Λ) → ∃ Λ, S.IsTerm (h • δ) Λ := by
    rintro h hh δ ⟨Λ, hΛ⟩
    exact ⟨h • Λ, (GlobalTheory.HL.ComplAct.main M.L r k S δ Λ hΛ h hh).1⟩

  have hψ0 : ∀ δ : S.Datum, (¬ ∃ Λ, S.IsTerm δ Λ) → ENNReal.ofReal (S.nu δ) * φ δ = 0 := by
    intro δ hδ
    rw [hφ0 δ hδ, mul_zero]
  have hterm : ∀ d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * φ (c.dat d.1) =
      ENNReal.ofReal κ * (ENNReal.ofReal (S.nu (c.dat d.1)) * φ (c.dat d.1)) := by
    intro d
    by_cases hd : ∃ Λ, S.IsTerm (c.dat d.1) Λ
    · obtain ⟨Λ, hΛ⟩ := hd
      rw [hκ d.1 Λ hΛ, ENNReal.ofReal_mul hκ0, mul_assoc]
    · rw [hφ0 _ hd, mul_zero, mul_zero, mul_zero]
  rw [tsum_congr hterm, ENNReal.tsum_mul_left]
  congr 1

  let A : Set R.RD := {a | ∃ Λ, S.IsTerm (c.dat a.1) Λ}
  have h1 : ∑' a : A, ENNReal.ofReal (S.nu (c.dat a.1.1)) * φ (c.dat a.1.1) =
      ∑' d : R.RD, ENNReal.ofReal (S.nu (c.dat d.1)) * φ (c.dat d.1) := by
    refine tsum_subtype_eq_of_support_subset (f := fun d : R.RD => ENNReal.ofReal (S.nu (c.dat d.1)) * φ (c.dat d.1)) ?_
    intro a ha
    by_contra hn
    exact ha (hψ0 _ hn)
  have hT : ∀ g : S.H0, ∀ x : S.Datum, (∃ Λ, S.IsTerm x Λ) → ∃ Λ, S.IsTerm (g • x) Λ :=
    fun g x hx => hmove g g.2 x hx
  have hι : ∀ a : A, ∃ Λ, S.IsTerm (c.dat a.1.1) Λ := fun a => a.2
  have hsurj : ∀ x : S.Datum, (∃ Λ, S.IsTerm x Λ) → ∃ a : A, ∃ g : S.H0, g • c.dat a.1.1 = x := by
    intro x hx
    obtain ⟨Λ, hΛ⟩ := hx
    obtain ⟨d, rfl⟩ := hex x Λ hΛ
    obtain ⟨y, hyR, hy⟩ := R.hRD.2.1 d (Set.mem_univ d)
    obtain ⟨h, hh, hhy⟩ := (hrel y d).1 hy
    have hTy : ∃ Λ, S.IsTerm (c.dat y) Λ := by
      have h' := hmove h⁻¹ (S.H0.inv_mem hh) _ ⟨Λ, hΛ⟩
      rwa [← hhy, inv_smul_smul] at h'
    exact ⟨⟨⟨y, hyR⟩, hTy⟩, ⟨h, hh⟩, hhy⟩
  have hinj : ∀ a b : A, (∃ g : S.H0, g • c.dat a.1.1 = c.dat b.1.1) → a = b := by
    rintro a b ⟨g, hg⟩
    have hr : LocNG.Datum.Rel a.1.1 b.1.1 := (hrel _ _).2 ⟨g, g.2, hg⟩
    exact Subtype.ext (Subtype.ext (R.hRD.2.2 _ a.1.2 _ b.1.2 hr))
  have hinv : ∀ g : S.H0, ∀ x : S.Datum, (∃ Λ, S.IsTerm x Λ) →
      ENNReal.ofReal (S.nu (g • x)) * φ (g • x) = ENNReal.ofReal (S.nu x) * φ x := by
    rintro g x ⟨Λ, hΛ⟩
    show ENNReal.ofReal (S.nu ((g : S.GLV) • x)) * φ ((g : S.GLV) • x) = _
    rw [(GlobalTheory.HL.Frames.nu_pos_and_smul M.L r k S x Λ hΛ).2 g g.2, hφ g g.2 x]
  have h2 := (GlobalTheory.tsum_transversal_eq_tsum_orbitQuotient (G := S.H0) (X := S.Datum) (A := A)
    (fun a => c.dat a.1.1) (fun x => ∃ Λ, S.IsTerm x Λ) hT hι hsurj hinj).2
    (fun x => ENNReal.ofReal (S.nu x) * φ x) hinv
  rw [← h1, h2]
  show _ = ∑' o : MulAction.orbitRel.Quotient S.H0 S.Datum, ENNReal.ofReal (S.nu o.out) * φ o.out
  refine tsum_congr fun o => ?_
  split_ifs with ho
  · rfl
  · exact (hψ0 _ ho).symm

end GlobalTheory.HL.CoordSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryNormalisesStabilStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFrames_complementUnitary_normalises_stabiliser : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ h ∈ S.H0, (∀ s ∈ S.St, h * s * h⁻¹ ∈ S.St) ∧ ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.IsTerm (h • d) (h • Λ) ∧ S.om (h • d) (h • Λ) = S.om d Λ ∧ S.mu (h • Λ) = S.mu Λ := by
  first | exact @GlobalTheory.HL.FixFrames.unitary_complement_acts | exact GlobalTheory.HL.FixFrames.unitary_complement_acts | (intros; apply GlobalTheory.HL.FixFrames.unitary_complement_acts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMassEqSumFrameClassesStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianMass_eq_sum_frameClasses : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (P : Submodule L.O S.V → Prop), (∀ h ∈ S.St, ∀ Λ, S.IsTerm d Λ → P Λ → P (h • Λ)) → S.mass d P = S.sumCls fun C => S.nT d C P := by
  first | exact @GlobalTheory.HL.mass_eq_sumCls | exact GlobalTheory.HL.mass_eq_sumCls | (intros; apply GlobalTheory.HL.mass_eq_sumCls <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalAmplitudeSummandAtTermOrbitStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localAmplitude_summand_at_term_orbit : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (P : Submodule L.O S.V → Prop), (∀ Λ, ∀ h ∈ S.St, P (h • Λ) ↔ P Λ) → ∀ Λ, S.IsTerm d Λ → IsLat L Λ → ∀ o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V), o = Quotient.mk'' Λ → S.IsTerm d o.out ∧ (∃ h ∈ S.St, o.out = h • Λ) ∧ (if S.IsTerm d o.out ∧ P o.out then (S.mu o.out : ℂ) * S.om d o.out else 0) = (if P Λ then (S.mu Λ : ℂ) * S.om d Λ else 0) ∧ (if S.IsTerm d o.out ∧ P o.out then ENNReal.ofReal (S.mu o.out) else 0) = (if P Λ then ENNReal.ofReal (S.mu Λ) else 0) := by
  first | exact @GlobalTheory.HL.amp_summand_orbit | exact GlobalTheory.HL.amp_summand_orbit | (intros; apply GlobalTheory.HL.amp_summand_orbit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MulVecMemHatSmul
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped TensorProduct ENNReal Pointwise
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.ColCmp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

variable {n r k : ℕ}

def zPerp (σ : E →+* E) {m : ℕ} (Jb : Matrix (Fin m) (Fin m) E) (z : Fin m → E) :
    Submodule (𝓞 E) (Fin m → E) where
  carrier := {x | form σ Jb x z = 0}
  zero_mem' := by simp [form]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, form, Matrix.mulVec_add, dotProduct_add] at *
    rw [ha, hb, add_zero]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq, form] at *
    rw [Matrix.mulVec_smul, dotProduct_smul, ha, smul_zero]

def levelJoin (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (f : Matrix (Fin n) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin n → E)) (g₁ g₂ : ℕ)
    (w : HeightOneSpectrum (𝓞 F) → HeightOneSpectrum (𝓞 E))
    (ε : HeightOneSpectrum (𝓞 F) → Fin k → Fin n → E) : Subgroup (HA (Af F) σ J) :=
  (ParabolicSubgroups.Np (Af F) σ J P ⊓ ParabolicSubgroups.Kmax σ J Λ) ⊔
    (ParabolicSubgroups.Hp (Af F) σ J P f ⊓ ParabolicSubgroups.Kmax σ J Λ ⊓
      ⨅ p ∈ ParabolicSubgroups.Typed F g₁ g₂, ParabolicSubgroups.uniAt σ J Λ (w p).asIdeal (ε p)) ⊔
    FlagUnipotentStabilizers.Kprin σ J Λ (g₁ * g₂)

end GlobalTheory.ColCmp
end
end

