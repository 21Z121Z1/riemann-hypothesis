import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ClassMapInjectiveBijectiveNorms
section
noncomputable section

namespace Formalism.MainNotions.LocalSituation

open Formalism.BasicNotions Formalism.BasicNotions.Loc

def ClassMapInjectiveBijectiveNorms (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    HerrAat (sit D.loc HW l (D.locA l) K s LL h) ∧ HerrAsat (sit D.loc HW l (D.locA l) K s LL h) ∧
      ((HW l).W K s LL h).ClNat

theorem classMapInjectiveBijectiveNorms_of_aux6 {D : Formalism.BasicNotions.D7} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW}
    (h : Conclusion6 D HW F) : ClassMapInjectiveBijectiveNorms D HW F :=
  fun l _ K s LL g => ⟨(h l K s LL g).1, (h l K s LL g).2.1, (h l K s LL g).2.2.1⟩

end Formalism.MainNotions.LocalSituation
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.GammaSemisimpleLocalOfConsequences
section
noncomputable section

namespace Formalism.MainNotions.DeltaInvariantLattices

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable (W : LocWach PD LL O v n)

def WachLatticeFree : Prop := ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → wachFree W T

def WachLatticeDualClosed : Prop :=
  ∀ (T T' : LocLat G Qp LL O) (P : T.V →ₗ[LL] T'.V →ₗ[LL] LL), IsCrys PD T.ρ → IsCrys PD T'.ρ →
    wachDual W T T' P

def WachLatticeTensorClosed : Prop :=
  ∀ (T T' T'' : LocLat G Qp LL O) (b : T.V →ₗ[LL] T'.V →ₗ[LL] T''.V),
    IsCrys PD T.ρ → IsCrys PD T'.ρ → IsCrys PD T''.ρ → wachTensor W T T' T'' b

def WachLatticeMonoidal : Prop := WachLatticeDualClosed W ∧ WachLatticeTensorClosed W

def WachCharacterisationLattice : Prop := ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → p10 W T

def WachTwistLattice : Prop :=
  ∀ (T T' : LocLat G Qp LL O) (j : ℤ), IsCrys PD T.ρ → IsCrys PD T'.ρ → wachTwistIso W T T' j

def GammaSemisimpleQuotient : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ →
    ∀ y : ℕ, 1 ≤ y → SSEig W T (invN W T (W.Q ^ y)) (W.N T)
      {c | ∃ a ∈ Jumps (PD := PD) T, ∃ j : ℕ, 1 ≤ j ∧ j ≤ y ∧ c = (uU W) ^ (-(a + j))}

theorem gamma_semisimple_of_consequences (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (h : ConsW W Pt) : GammaSemisimpleQuotient W :=
  fun T hT => (h T hT).2.1

theorem wach_first_lattice_iff : WachFreeDualTensor W ↔ WachLatticeFree W ∧ WachLatticeMonoidal W := Iff.rfl

theorem wach_tenth_iff : WachTwistCharacterisation W ↔ WachCharacterisationLattice W ∧ WachTwistLattice W := Iff.rfl

theorem P1freeW_of (h : WachFreeDualTensor W) : WachLatticeFree W := h.1

theorem wach_characterisation_lattice_of (h : WachTwistCharacterisation W) : WachCharacterisationLattice W := h.1

end Local

section Theory

def wachLatticeFreeLocal (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    WachLatticeFree ((HW l).W K s LL h)

def wachLatticeMonoidalLocal (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    WachLatticeMonoidal ((HW l).W K s LL h)

def wachCharacterisationLocal (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    WachCharacterisationLattice ((HW l).W K s LL h)

def wachTwistLocal (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    WachTwistLattice ((HW l).W K s LL h)

def gammaSemisimpleLocal (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    GammaSemisimpleQuotient ((HW l).W K s LL h)

end Theory

section Design

def WachLatticeFreeGlobal (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  wachLatticeFreeLocal D.loc HW D.locA F

def WachLatticeMonoidalGlobal (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  wachLatticeMonoidalLocal D.loc HW D.locA F

def WachCharacterisation (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  wachCharacterisationLocal D.loc HW D.locA F

def WachTwistLocalTheory (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  wachTwistLocal D.loc HW D.locA F

def gammaSemisimpleQuotientGlobal (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  gammaSemisimpleLocal D.loc HW D.locA F

theorem gamma_semisimple_local_of_consequences {D : Formalism.BasicNotions.D7} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW}
    (h : cons D HW F) : gammaSemisimpleQuotientGlobal D HW F :=
  fun l _ K s LL g => gamma_semisimple_of_consequences _ _ (h l K s LL g)

theorem wach_first_iff_free_monoidal (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) :
    P1 D HW F ↔ WachLatticeFreeGlobal D HW F ∧ WachLatticeMonoidalGlobal D HW F := by
  constructor
  · intro h
    exact ⟨fun l _ K s LL g => (h l K s LL g).1, fun l _ K s LL g => (h l K s LL g).2⟩
  · rintro ⟨a, b⟩ l _ K s LL g
    exact ⟨a l K s LL g, b l K s LL g⟩

theorem product_first_zeroth_parts_iff_wach_and_twist (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) :
    product_first_zeroth_parts D HW F ↔ WachCharacterisation D HW F ∧ WachTwistLocalTheory D HW F := by
  constructor
  · intro h
    exact ⟨fun l _ K s LL g => (h l K s LL g).1, fun l _ K s LL g => (h l K s LL g).2⟩
  · rintro ⟨a, b⟩ l _ K s LL g
    exact ⟨a l K s LL g, b l K s LL g⟩

theorem wach_free_of_properties {D : Formalism.BasicNotions.D7} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW}
    (h : P1 D HW F) : WachLatticeFreeGlobal D HW F := ((wach_first_iff_free_monoidal D HW F).1 h).1

theorem wach_characterisation_of_tenth {D : Formalism.BasicNotions.D7} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW}
    (h : product_first_zeroth_parts D HW F) : WachCharacterisation D HW F := ((product_first_zeroth_parts_iff_wach_and_twist D HW F).1 h).1

theorem wach_theorem_iff_refined (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (C : CmpOf D.loc D.locA HW F) :
    thm1 D HW F C ↔ (WachLatticeFreeGlobal D HW F ∧ WachLatticeMonoidalGlobal D HW F) ∧ P2 D HW F ∧ P3 D HW F C ∧ P4 D HW F C ∧
      P5 D HW F ∧ P6 D HW F ∧ P7 D HW F ∧ P8 D HW F ∧ P9 D HW F ∧ (WachCharacterisation D HW F ∧ WachTwistLocalTheory D HW F) := by
  rw [wach_theorem_iff_properties, wach_first_iff_free_monoidal, product_first_zeroth_parts_iff_wach_and_twist]

end Design

end Formalism.MainNotions.DeltaInvariantLattices
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.WeaklyAdmissibleFiltrations Module Formalism.MainNotions.N

namespace Formalism.MainNotions.LargeLevelLemmas

open Formalism.BasicNotions Formalism.BasicNotions.Loc

section Lit

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    (LL O : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    [CommRing O] [Algebra O LL]

def bkAAt : Prop :=
  ∀ (A A' : GRep G Qp LL O) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDR PD A.ρ → IsDual1 PD A.ρ A'.ρ P →
    (∀ a ∈ continuousCocycles A.ρ, (a ∈ finiteCocycles PD A.ρ ↔ ∀ b ∈ finiteCocycles PD A'.ρ, CobL PD (cupL A'.ρ P a b))) ∧
    (∀ b ∈ continuousCocycles A'.ρ, (b ∈ finiteCocycles PD A'.ρ ↔ ∀ a ∈ finiteCocycles PD A.ρ, CobL PD (cupL A'.ρ P a b)))

def TateH1FinitenessAt (_PD : PeriodData G Qp K₀ K B BdR) : Prop :=
  ∀ (A : GRep G Qp LL O) (LA : Lattice (O := O) A.ρ), Module.Finite O (LatticeCohomology LA)

theorem bkAAt_of_core [TopologicalSpace Qp] (h : bkACore PD) (hO : GoodO (Qp := Qp) LL O) :
    bkAAt PD LL O :=
  h LL O hO

theorem tate_h1_finite_of_all_coefficients [TopologicalSpace Qp] (h : TateFiniteness PD) (hO : GoodO (Qp := Qp) LL O) :
    TateH1FinitenessAt LL O PD :=
  h LL O hO

end Lit

variable {D : D7}

theorem splits_coef {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    Splits (Qp := ℚ_[D.nd.l i]) (K := Br.Kw D.nbr i w hw) ↥C.LL.1 := by
  refine ⟨C.LL.2, ?_⟩
  have hmem : ∀ (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Om (D.nd.l i)) (x : Br.Kw D.nbr i w hw),
      τ x ∈ C.LL.1 := fun τ x => C.le ((D.nbr i w hw).LL_split τ x)
  let e : (Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) ≃
      (Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Om (D.nd.l i)) :=
    { toFun := fun f => C.LL.1.val.comp f
      invFun := fun τ => τ.codRestrict C.LL.1.toSubalgebra (hmem τ)
      left_inv := fun f => by ext x; rfl
      right_inv := fun τ => by ext x; rfl }
  rw [Fintype.card_congr e]
  exact AlgHom.card _ _ _

section Pt

variable (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i)

def GlobalIndexTheoremPlaces (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ)
    (cB : ℕ) : Prop :=
  Formalism.MainNotions.TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow → Formalism.MainNotions.TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc e' →
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.admTB i r π cB → Formalism.MainNotions.TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB

def Conclusion1 (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ)
    (cB : ℕ) : Prop :=
  0 < dc.col.card → GlobalIndexTheoremPlaces i r ρ π dc lenRow e' cB

def adm51 : Prop := π ∈ D.nd.Z i → ∃ S : IdempotentChoiceData D.nd i, GoodCongruenceObjects D.nd r ρ π S

def CharpolyCoeffsLemmaFamily : Prop := CharpolyCoeffsInSubalgebra D.nd i (D.nd.T i) (rO D.nd i r)

def SpanQuotientLemma : Prop := π ∈ D.nd.Z i → ∀ S : IdempotentChoiceData D.nd i, GoodCongruenceObjects D.nd r ρ π S → VanishingLemma D.nd π S

def HomRelationsLemmaAllChoices : Prop := π ∈ D.nd.Z i → ∀ S : IdempotentChoiceData D.nd i, GoodCongruenceObjects D.nd r ρ π S → QuotientHomNonvanishingBound D.nd r π S

def admG5 : Prop := π ∈ D.nd.Z i → ∀ S : IdempotentChoiceData D.nd i, GoodCongruenceObjects D.nd r ρ π S → TameInertiaCondition D.nd r ρ π S

def BlochKatoAnnihilators : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw), C.IsGood →
    bkAAt (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL)

def tateH1FinitenessAtPlacesOver : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw),
    TateH1FinitenessAt ↥C.LL.1 ↥(OL C.LL) (Br.PD D.loc D.nbr i w hw)

def CyclotomicInertiaHypothesis : Prop := Formalism.MainNotions.TruncatedSeriesCountingIdentities.CyclotomicInertiaImage i

def admitted : Prop :=
  adm51 i r ρ π ∧ CharpolyCoeffsLemmaFamily i r ∧ SpanQuotientLemma i r ρ π ∧ HomRelationsLemmaAllChoices i r ρ π ∧
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG1 i r ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG2 i r ρ π ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG3 i r ρ π ∧
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG4 i r ∧ admG5 i r ρ π ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG5 i r ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.TameGeneratorConditions i ∧
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.admG6 i r ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.admBK i ∧ BlochKatoAnnihilators i ∧
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous i r ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.admSS i r ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π ∧ CyclotomicInertiaHypothesis i ∧
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.CyclotomicCompletionAdmissible i ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.admH2 i ∧
    tateH1FinitenessAtPlacesOver i ∧ Formalism.MainNotions.TruncatedSeriesCountingIdentities.UnramifiedClassFieldBound i

end Pt

theorem sum_padicValNat_range (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), padicValNat p k = padicValNat p n.factorial := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ,
      padicValNat.mul (Nat.succ_ne_zero m) (Nat.factorial_ne_zero m), add_comm]

theorem vdel_le (i : D.nd.Loc) :
    D.nd.vdel i ≤ (D.R.t : ℚ) * (D.nd.s0 i : ℚ) + (padicValNat (D.nd.l i) D.R.t.factorial : ℚ) := by
  have h1 : D.nd.vdel i ≤
      ∑ k ∈ Finset.range D.R.t, ((D.nd.s0 i : ℚ) + (padicValNat (D.nd.l i) k : ℚ)) := by
    unfold NData.vdel
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      exact Finset.mem_range.2 (Finset.mem_Ioo.1 hk).2
    · intro k _ _
      positivity
  have h2 : (∑ k ∈ Finset.range D.R.t, padicValNat (D.nd.l i) k) ≤
      padicValNat (D.nd.l i) D.R.t.factorial := by
    rcases Nat.eq_zero_or_pos D.R.t with h0 | hpos
    · simp [h0]
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      rw [hm, Nat.succ_eq_add_one, sum_padicValNat_range, Nat.factorial_succ,
        padicValNat.mul (Nat.succ_ne_zero m) (Nat.factorial_ne_zero m)]
      exact Nat.le_add_left _ _
  have h3 : (∑ k ∈ Finset.range D.R.t, ((D.nd.s0 i : ℚ) + (padicValNat (D.nd.l i) k : ℚ))) =
      (D.R.t : ℚ) * (D.nd.s0 i : ℚ) + ((∑ k ∈ Finset.range D.R.t, padicValNat (D.nd.l i) k : ℕ) : ℚ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sum]
  have h4 : ((∑ k ∈ Finset.range D.R.t, padicValNat (D.nd.l i) k : ℕ) : ℚ) ≤
      (padicValNat (D.nd.l i) D.R.t.factorial : ℚ) := by exact_mod_cast h2
  linarith

def Conclusion2 (i : D.nd.Loc) : Prop :=
  ∀ (α : Module.End (D.nd.O i) (D.nd.Mt i)) (A : ℤ), A ≠ 0 →
    (∀ f : D.nd.T i, α * D.nd.act i f = D.nd.act i f * α) →
    (∀ x ∈ D.nd.Zgood i, ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
      α.baseChange (KK D.nd i) u = (A : KK D.nd i) • u) →
    (∀ x ∈ D.nd.Z i, x ∉ D.nd.Zgood i → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x,
      α.baseChange (KK D.nd i) u = 0) →
    lenUnit (O := D.nd.O i) (D.nd.l i)
        (↥(MtUp D.nd i (D.nd.Zgood i)) ⧸
          (MtLow D.nd i (D.nd.Zgood i)).comap (MtUp D.nd i (D.nd.Zgood i)).subtype) ≤
      ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℚ) * (D.nd.vcc i π + padicValInt (D.nd.l i) A)

def IntegralityFromMetric (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i)
    (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ),
    GoodR D.nd i r → admitted i r ρ π → Conclusion1 i r ρ π dc lenRow e' cB

def HodgeTateFromSandwich (D : D7) : Prop := ∀ i : D.nd.Loc, Conclusion2 i

def Stmt (D : D7) : Prop := IntegralityFromMetric D ∧ HodgeTateFromSandwich D

theorem hypotheses_of_local_inputs {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i}
    {dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i} {lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ}
    {e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ} {cB : ℕ} (h : admitted i r ρ π)
    (hR : Formalism.MainNotions.TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow) (hL : Formalism.MainNotions.TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc e')
    (hT : Formalism.MainNotions.TruncatedSeriesCountingIdentities.admTB i r π cB) : Formalism.MainNotions.TruncatedSeriesCountingIdentities.admitted i r ρ π dc lenRow e' cB := by
  obtain ⟨-, -, -, -, g1, g2, g3, g4, -, g5, g5x, g6, bk, -, ct, ss, dcm, ep, tie, sh, fo, h2, -, cft⟩ := h
  exact ⟨g1, g2, g3, g4, g5, g5x, g6, bk, hT, hR, hL, ct, ss, dcm, ep, tie, sh, fo, h2, cft⟩

theorem positive_case_of_general (h : Formalism.MainNotions.TruncatedSeriesCountingIdentities.IntegralityFromMetric D) : IntegralityFromMetric D :=
  fun i r ρ π dc lenRow e' cB hG hA _ hR hL hT =>
    h i r ρ π dc lenRow e' cB hG (hypotheses_of_local_inputs hA hR hL hT)

theorem zgoodSubsetZ (i : D.nd.Loc) : D.nd.Zgood i ⊆ D.nd.Z i := by
  intro x hx
  rw [D.Z_tie]
  rw [D.Zgood_tie] at hx
  exact hx.1

theorem endomorphism_bound_at_good_points (h : Formalism.MainNotions.TruncatedSeriesCountingIdentities.HodgeTateFromSandwich D) : HodgeTateFromSandwich D :=
  fun i α A hA hc h1 h0 => h i (D.nd.Zgood i) (zgoodSubsetZ i) α A hA hc h1 h0

theorem global_theorems_of_general (h : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Stmt D) : Stmt D :=
  ⟨positive_case_of_general h.1, endomorphism_bound_at_good_points h.2⟩

end Formalism.MainNotions.LargeLevelLemmas
end
end

