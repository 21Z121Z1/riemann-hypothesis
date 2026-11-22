import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0044
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0083
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0049
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0031
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0239
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0089
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0234
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0229
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0222
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0181
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0184
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0111
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0244
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentAntidiagonalMemSkewLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0240
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0241
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentMiddleRowMemHomLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentRadicalFormsUnitSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Formalism.LocalRingCardinality.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianOrbitUniqueLatticeIntegralFrames
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GoodFrames

theorem Mof_eq_span {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] {L : LocE F E} {r k : ℕ} (S : Frames L r k) (hth : S.th = 1)
    (g g' : Fin (r + 1) → S.V) :
    S.Mof g g' = Submodule.span L.O (Set.range (Sum.elim g g')) := by
  have hth' : algebraMap F E S.th⁻¹ = 1 := by rw [hth, inv_one, map_one]
  apply le_antisymm
  · rw [Frames.Mof]
    apply Submodule.span_le.2
    rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact Submodule.subset_span ⟨Sum.inl j, rfl⟩
    · simp only [hth', one_smul, SetLike.mem_coe]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
        (Submodule.subset_span ⟨Sum.inl j, rfl⟩)
  · apply Submodule.span_le.2
    rintro _ ⟨j | j, rfl⟩
    · exact Submodule.subset_span (Or.inl ⟨j, rfl⟩)
    · have h1 : g' j = algebraMap F E S.th⁻¹ • (g' j - g j) + g j := by rw [hth']; simp
      simp only [Sum.elim_inr, SetLike.mem_coe]
      rw [h1]
      exact Submodule.add_mem _ (Submodule.subset_span (Or.inr ⟨j, rfl⟩))
        (Submodule.subset_span (Or.inl ⟨j, rfl⟩))

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → P.PrimeTo → ∀ (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → A a b = 0 ∧ A' a b = 0) → (∀ a, A a a = 1 ∧ A' a a = 1) → (∀ a b, A a b ∈ M.L.O ∧ A' a b ∈ M.L.O) → ∀ (f f' : Fin (r + 1) → V), (∀ j, f j = ∑ i, A i j • P.A.f i) → (∀ j, f' j = ∑ i, A' i j • P.B.f i) → ∀ d0 : LocNG.Datum P, (∃ t, LocNG.IsTermOver P d0 t) → ∀ d : LocNG.Datum P, (LocNG.Datum.Rel d0 d → ∃! Λ : Submodule M.L.O V, LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) ∧ ((∃ t, LocNG.IsTermOver P d t) → LocNG.Datum.Rel d0 d) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hdim hrel hpt A A' hAt hAd hAi f f' hf hf' d0 hd0 d
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hdim hrel
  have hsplit : M.split = none := hpt.1
  obtain ⟨hgg, hvG, -⟩ := (GlobalTheory.HL.CoordHeight.height_eq M hM H r k P S c).2.2 hpt
  have ha : S.a = 0 := by simp [GlobalTheory.HL.Frames.a, GlobalTheory.HL.Frames.vth, hgg, hvG]
  have hth : S.th = 1 := by simp [GlobalTheory.HL.Frames.th, hgg]
  obtain ⟨-, -, -, -, hD, -⟩ := GlobalTheory.FrameBasic.main M.L r k S
  have hDu : ∀ l, S.D l ≠ 0 → S.D l ∈ M.L.O ∧ ∃ y ∈ M.L.O, S.D l * y = 1 := by
    intro l hl
    by_cases h0 : l = 0
    · have e : S.D l = 1 := by
        subst h0
        unfold GlobalTheory.HL.Frames.D GlobalTheory.HL.lead
        exact Matrix.det_isEmpty (n := Fin 0)
      rw [e]
      exact ⟨M.L.O.one_mem, 1, M.L.O.one_mem, mul_one 1⟩
    · have hmem : (l : ℕ) ∈ P.ends := by
        unfold LocNG.FPair.ends
        simp only [Finset.mem_filter, Finset.mem_range]
        rw [GlobalTheory.HL.CoordHeight.Dm_eq c]
        exact ⟨l.2, Nat.one_le_iff_ne_zero.mpr fun h => h0 (Fin.ext h), hD l hl⟩
      have := hpt.2.2 _ hmem
      rwa [GlobalTheory.HL.CoordHeight.Dm_eq c] at this
  have hTC := GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c
  have hDT := GlobalTheory.HL.CoordDatum.transport M hM H r k P S c
  have hMT := GlobalTheory.HL.CoordMass.transport M hM H r k P S c
  have hNT := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c

  have hfc : ∀ j, c.e (f j) = ∑ i, A i j • S.f i := by
    intro j; rw [hf j, map_sum]; simp [c.f_eq]
  have hfc' : ∀ j, c.e (f' j) = ∑ i, A' i j • S.f' i := by
    intro j; rw [hf' j, map_sum]; simp [c.f'_eq]
  have hfN : ∃ n ∈ P.A.N, f = fun b => n (P.A.f b) := by
    obtain ⟨n, hn, hne⟩ := ((GlobalTheory.HL.FrameOnto.unipotent_onto M.L r k S).2.2 A
      ⟨fun i j h => (hAt i j h).1, fun i => (hAd i).1⟩).1
    refine ⟨c.grp.symm n, (hNT.2.1 _).2 (by simpa using hn), ?_⟩
    funext b
    apply c.e.injective
    change c.e (f b) = c.e (c.e.symm (n (c.e (P.A.f b))))
    rw [LinearEquiv.apply_symm_apply, ← c.f_eq, hne b, hfc b]
  have hf'N : ∃ n ∈ P.B.N, f' = fun b => n (P.B.f b) := by
    obtain ⟨n, hn, hne⟩ := ((GlobalTheory.HL.FrameOnto.unipotent_onto M.L r k S).2.2 A'
      ⟨fun i j h => (hAt i j h).2, fun i => (hAd i).2⟩).2
    refine ⟨c.grp.symm n, (hNT.2.2.1 _).2 (by simpa using hn), ?_⟩
    funext b
    apply c.e.injective
    change c.e (f' b) = c.e (c.e.symm (n (c.e (P.B.f b))))
    rw [LinearEquiv.apply_symm_apply, ← c.f'_eq, hne b, hfc' b]

  set fc : Fin (r + 1) → S.V := fun b => c.e (f b) with hfcdef
  set fc' : Fin (r + 1) → S.V := fun b => c.e (f' b) with hfc'def
  have hAi1 : GlobalTheory.HL.IsIntM M.L A := fun i j => (hAi i j).1
  have hAi2 : GlobalTheory.HL.IsIntM M.L A' := fun i j => (hAi i j).2
  have hcls : (fc, fc') ∈ S.frameCls S.f S.f' :=
    GlobalTheory.HL.GoodClass.mem_cls S hgg S.f S.f' (fc, fc')
      ⟨fun i j h => (hAt i j h).1, fun i => (hAd i).1⟩ ⟨fun i j h => (hAt i j h).2, fun i => (hAd i).2⟩
      hAi1 hAi2 hfc hfc'
  have hMof : S.Mof fc fc' = S.Mof S.f S.f' :=
    ((GlobalTheory.HL.FrameClass.frame_classes M.L r k S S.f S.f').2.1 _ hcls).2
  have hMM : ∀ Λ : Submodule M.L.O V,
      H.MMfam (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) = Sum.elim f f' := by
    intro Λ; simp [HermSp.MMfam, hsplit]
  have hmemlat : ∀ (Λ : Submodule M.L.O V) (v : V), c.e v ∈ c.lat Λ ↔ v ∈ Λ := by
    intro Λ v
    constructor
    · rintro ⟨w, hw, e⟩
      have : w = v := c.e.injective e
      rwa [← this]
    · intro hv; exact ⟨v, hv, rfl⟩
  have hlatspan : c.lat (Submodule.span M.L.O (Set.range (Sum.elim f f'))) =
      Submodule.span M.L.O (Set.range (Sum.elim fc fc')) := by
    rw [Coord.lat, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext x
    cases x <;> rfl
  have hst : ∀ g : Fin (r + 1) → S.V, S.spanTo g (r + 1) = Submodule.span E (Set.range g) := by
    intro g
    have hs : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by ext i; simpa using i.2
    rw [Frames.spanTo, hs, Set.image_univ]
  have hME : ∀ v : V, c.e v ∈ S.ME ↔ v ∈ Submodule.span E (Set.range (Sum.elim f f')) := by
    have e1 : S.ME = Submodule.span E (Set.range (Sum.elim fc fc')) := by
      rw [Frames.ME, hst, hst, ← Submodule.span_union, ← Set.Sum.elim_range,
        ← Submodule.span_span_of_tower M.L.O E (Set.range (Sum.elim S.f S.f')),
        ← Submodule.span_span_of_tower M.L.O E (Set.range (Sum.elim fc fc')),
        ← Mof_eq_span S hth, ← Mof_eq_span S hth, hMof]
    have e2 : Submodule.span E (Set.range (Sum.elim fc fc')) =
        (Submodule.span E (Set.range (Sum.elim f f'))).map (c.e : V →ₗ[E] S.V) := by
      rw [Submodule.map_span, ← Set.range_comp]
      congr 2
      funext x
      cases x <;> rfl
    intro v
    rw [e1, e2, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

  have hKM : ∀ Λ : Submodule M.L.O V,
      ((∀ i, H.MMfam (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) i ∈ Λ) ∧
        ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) ↔
      S.sat (c.lat Λ) = S.Mof fc fc' := by
    intro Λ
    rw [Mof_eq_span S hth, ← hlatspan]
    simp only [LocNG.BBne, hMM, not_exists, not_and, not_not]
    constructor
    · rintro ⟨hin, hbb⟩
      ext x
      obtain ⟨v, rfl⟩ := c.e.surjective x
      rw [Frames.sat, Submodule.mem_inf, Submodule.restrictScalars_mem, hmemlat, hmemlat, hME]
      constructor
      · rintro ⟨h1, h2⟩; exact hbb v h1 h2
      · intro hv
        refine ⟨(Submodule.span_le.2 ?_) hv, ?_⟩
        · rintro _ ⟨i, rfl⟩; exact hin i
        · exact Submodule.span_le_restrictScalars M.L.O E _ hv
    · intro hsat
      have hsub : ∀ v, v ∈ Submodule.span M.L.O (Set.range (Sum.elim f f')) ↔ v ∈ Λ ∧
          v ∈ Submodule.span E (Set.range (Sum.elim f f')) := by
        intro v
        rw [← hmemlat, ← hsat, Frames.sat, Submodule.mem_inf, Submodule.restrictScalars_mem, hmemlat, hME]
      refine ⟨fun i => ((hsub _).1 (Submodule.subset_span ⟨i, rfl⟩)).1, fun v h1 h2 => (hsub v).2 ⟨h1, h2⟩⟩

  have hloc := GlobalTheory.T.generic_local_terms_selfDual_lattices M hM H r k P hdim hrel f f' hfN hf'N
  have hmov := GlobalTheory.T.unitaryComplement_moves_hermitianTerms M hM H r k P hdim hrel f f' hfN hf'N

  have hex0 : ∃ Λ : Submodule M.L.O V,
      LocNG.IsTermOver P d0 (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧
        ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) := by
    obtain ⟨t0, ht0⟩ := hd0
    have hT0 := (hTC.1 d0 t0 ht0).1
    obtain ⟨s, hs, hsFr⟩ := (GlobalTheory.HL.GoodClass.one_class M.L r k S hgg hDu).2.2 _
      ((GlobalTheory.HL.TermBasic.term_basic M.L r k S _ _ hT0).2.2.2.2.2.2.1)
    have hact := GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S (c.dat d0) _ hT0 s⁻¹ (S.St.inv_mem hs)
    have hT1 : S.IsTerm (c.dat d0) (s⁻¹ • c.lat t0.abelian₂) := hact.1
    have hFr1 : S.Fr (c.dat d0) (s⁻¹ • c.lat t0.abelian₂) = S.frameCls S.f S.f' := by
      rw [hact.2.2.2.2.1, hsFr, smul_smul, inv_mul_cancel, one_smul]
    have hBB1 := (GlobalTheory.HL.UnimodTerm.term_unique M.L r k S _ _ hT1 ha).1
    have hM1 : S.M (c.dat d0) (s⁻¹ • c.lat t0.abelian₂) = S.Mof fc fc' := by
      rw [hMof]
      have hmem : (S.fr (c.dat d0) (s⁻¹ • c.lat t0.abelian₂), S.fr' (c.dat d0) (s⁻¹ • c.lat t0.abelian₂)) ∈
          S.frameCls S.f S.f' := by
        rw [← hFr1]; exact GlobalTheory.HL.FrameClass.refl_mem S _ _
      exact ((GlobalTheory.HL.FrameClass.frame_classes M.L r k S S.f S.f').2.1 _ hmem).2
    obtain ⟨⟨Lam1, g1, g1', T1, T1'⟩, ht1, ht1l⟩ := hTC.2.1 d0 _ hT1
    obtain rfl : T1 = P.A.T := ht1.1
    obtain rfl : T1' = P.B.T := ht1.2.1
    have hsat1 : S.sat (c.lat Lam1) = S.Mof fc fc' := by
      rw [ht1l, ← hBB1, hM1]
    obtain ⟨hin, hbb⟩ := (hKM Lam1).2 hsat1
    have hbb1 : ¬ LocNG.BBne (H := H) (⟨Lam1, g1, g1', P.A.T, P.B.T⟩ : Term V M r) := fun h =>
      ((hTC.1 d0 _ ht1).2.2.1 h) (by rw [ht1l]; exact hBB1)
    obtain ⟨n1, hn1, hn1f, -⟩ := ht1.2.2.1
    obtain ⟨n1', hn1', hn1f', -⟩ := ht1.2.2.2.1
    obtain ⟨hSD, hFG, -, -⟩ := (GlobalTheory.T.generic_local_terms_selfDual_lattices M hM H r k P hdim hrel g1 g1' ⟨n1, hn1, hn1f⟩
      ⟨n1', hn1', hn1f'⟩ Lam1).1.2 ⟨d0, ht1, hbb1⟩
    obtain ⟨d1, hd1, hbb1'⟩ := (hloc Lam1).1.1 ⟨hSD, hFG, hin, hbb⟩
    have hd10 : d1 = d0 := by
      have h2 := (hTC.1 d1 _ hd1).1
      simp only at h2
      rw [ht1l] at h2
      exact hDT.1 ((GlobalTheory.HL.TermBasic.term_basic M.L r k S _ _ hT1).2.2.2.2.2.2.2 _ h2)
    subst hd10
    exact ⟨Lam1, hd1, hbb1'⟩

  have huniq : ∀ (d : LocNG.Datum P) (Λ Λ' : Submodule M.L.O V),
      (LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧
        ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) →
      (LocNG.IsTermOver P d (⟨Λ', f, f', P.A.T, P.B.T⟩ : Term V M r) ∧
        ¬ LocNG.BBne (H := H) (⟨Λ', f, f', P.A.T, P.B.T⟩ : Term V M r)) → Λ = Λ' := by
    intro d Λ Λ' h h'
    have key : ∀ Λ : Submodule M.L.O V,
        (LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧
          ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) →
        S.IsTerm (c.dat d) (c.lat Λ) ∧ S.M (c.dat d) (c.lat Λ) = S.Mof fc fc' := by
      intro Λ h
      obtain ⟨-, -, hin, hbb⟩ := (hloc Λ).1.2 ⟨d, h⟩
      have h2 := hTC.1 d _ h.1
      refine ⟨h2.1, ?_⟩
      have hz : S.BBzero (c.dat d) (c.lat Λ) := by
        by_contra hn; exact h.2 (h2.2.2.2 hn)
      rw [hz]; exact (hKM Λ).1 ⟨hin, hbb⟩
    obtain ⟨a1, a2⟩ := key Λ h
    obtain ⟨b1, b2⟩ := key Λ' h'
    apply hMT.2.2.1.1
    exact le_antisymm (GlobalTheory.HL.UnimodTerm.le_of_M_eq S b1 a1 ha (a2.trans b2.symm))
      (GlobalTheory.HL.UnimodTerm.le_of_M_eq S a1 b1 ha (b2.trans a2.symm))
  refine ⟨fun hR => ?_, fun ht => ?_⟩
  · obtain ⟨Λ0, h0⟩ := hex0
    obtain ⟨g, hg, hmv⟩ := hR
    have hset := (hmov g hg d0 d hmv).2
    have hmem : LocNG.img g Λ0 ∈ {Λ : Submodule M.L.O V |
        LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧
          ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} := by
      rw [← hset]; exact ⟨Λ0, h0, rfl⟩
    exact ⟨LocNG.img g Λ0, hmem, fun Λ hΛ => huniq d _ _ hΛ hmem⟩
  · obtain ⟨t, ht⟩ := ht
    obtain ⟨t0, ht0⟩ := hd0
    exact GlobalTheory.T.hermitianData_with_term_single_orbit_primeTo M hM H r k P hdim hrel hpt d0 d t0 t ht0 ht

end GlobalTheory.HL.GoodFrames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableMatrixCoefficientQuotientMeasure
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.QuotInt

theorem opn_continuous {n : ℕ} : Continuous (opn : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  have h : Continuous fun g : Matrix (Fin n) (Fin n) ℂ =>
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) g :=
    LinearMap.continuous_of_finiteDimensional
      ({ toFun := fun g => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n) g
         map_add' := fun a b => map_add _ a b
         map_smul' := fun c a => map_smul _ c a } :
        Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
  exact h.norm

end GlobalTheory.SgInf.QuotInt

namespace GlobalTheory.SgInf

open GlobalTheory.SgInf.QuotInt in

theorem integrable_Afun_quotMeas : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ u ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, Integrable (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) ν := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hν u hu v hv ξ
  have hStd' := hStd
  have hSide' := hSide
  obtain ⟨hk, hrep, -, -, hHaar, -, ha, hdec, -⟩ := hStd'
  obtain ⟨hz, hT, hπ, hHaarS, -⟩ := hSide'
  have hcl := GlobalTheory.SgInf.closedSub_groups k r z hz hT
  have hG : IsClosedSub k r (GG k r) := hcl.1
  have hS : IsClosedSub k r (Sset k r z) := hcl.2.2.2.1
  have hunim : IsUnimod (Sset k r z) μS := (GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μS).1 hHaarS
  have hW := GlobalTheory.T.weil_formula_besselUnitary_integrable k r (Sset k r z) μG μS ν hS hHaar hHaarS hunim hν
  have hνG : ν {x | Matrix.of x ∉ GG k r} = 0 := hW.2.1
  have hstab := (GlobalTheory.SgInfDD.DD_stable_dense k r σ w hrep).1
  have hD1 := GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w : Set H) hstab hdec u hu v hv
  have hPi := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hz hT hπ
  have hmeasG : MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r} :=
    (hG.2.1.preimage (f := fun x : Mt k r => (Matrix.of x : Mat k r)) continuous_id).measurableSet
  have haeG : ∀ᵐ x ∂ν, x ∈ {x : Mt k r | Matrix.of x ∈ GG k r} := by
    rw [ae_iff]; simpa using hνG

  have hcont : ContinuousOn (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x))
      {x | Matrix.of x ∈ GG k r} := by
    have h1 : ContinuousOn (fun x : Mt k r => be (psiGen k r z c) π μS σ (σ (Matrix.of x) u) v)
        {x | Matrix.of x ∈ GG k r} :=
      hD1.2.2.2.comp (f := fun x : Mt k r => (Matrix.of x : Mat k r)) continuous_id.continuousOn
        (fun x hx => hx)
    exact h1.clm_apply continuousOn_const
  have hae : AEStronglyMeasurable (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) ν := by
    have h1 := hcont.aestronglyMeasurable (μ := ν) hmeasG
    rwa [Measure.restrict_eq_self_of_ae_mem haeG] at h1
  refine ⟨hae, ?_⟩

  obtain ⟨C, hC⟩ := hdec u hu v hv
  have hC'0 : 0 ≤ max C 0 := le_max_right _ _
  let f : Mt k r → ENNReal := fun y => ENNReal.ofReal (max C 0 * opn (Matrix.of y : Mat k r) ^ (-a))
  have hopn : Measurable fun y : Mt k r => opn (Matrix.of y : Mat k r) :=
    Continuous.measurable (α := Mt k r) (opn_continuous (n := 2 * r + k + 1))
  have hfm : Measurable f :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (hopn.pow_const (-a)))
  have hcoef : ∀ g ∈ GG k r, ‖coef σ u v g‖ₑ ≤ ENNReal.ofReal (max C 0 * opn g ^ (-a)) := by
    intro g hg
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ((hC g hg).trans ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (opn_nonneg _) _)
  have haeS : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z := by
    rw [ae_iff]; simpa using hHaarS.2.2.1
  have hpt : ∀ x : Mt k r, Matrix.of x ∈ GG k r →
      ‖Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)‖ₑ ≤
        ‖ξ‖ₑ * ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS := by
    intro x hx
    have h1 : ‖Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)‖ₑ ≤
        ‖be (psiGen k r z c) π μS σ (σ (Matrix.of x) u) v‖ₑ * ‖ξ‖ₑ :=
      ContinuousLinearMap.le_opENorm_of_le _ le_rfl
    refine h1.trans ?_
    rw [mul_comm]
    gcongr
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    refine lintegral_mono_ae ?_
    filter_upwards [haeS] with s hs
    have hsG : Matrix.of s ∈ GG k r := hS.1 hs
    have hsi : (Matrix.of s : Mat k r)⁻¹ ∈ Sset k r z := hS.2.2.2.2 _ hs
    have hP : ‖PiS (psiGen k r z c) π (Matrix.of s)⁻¹‖ₑ ≤ 1 := by
      rw [← ofReal_norm, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (hPi.2.2.1 _ hsi).1
    have hc : coef σ (σ (Matrix.of x) u) v (Matrix.of s) = coef σ u v (Matrix.of s * Matrix.of x) := by
      simp only [coef, hrep.1.2 _ hsG _ hx, ContinuousLinearMap.comp_apply]
    rw [enorm_smul]
    calc _ ≤ ‖coef σ (σ (Matrix.of x) u) v (Matrix.of s)‖ₑ * 1 := by gcongr
      _ = ‖coef σ u v (Matrix.of s * Matrix.of x)‖ₑ := by rw [mul_one, hc]
      _ ≤ ENNReal.ofReal (max C 0 * opn (Matrix.of s * Matrix.of x : Mat k r) ^ (-a)) :=
        hcoef _ (hG.2.2.2.1 _ hsG _ hx)
  have hfin : ∫⁻ x, f x ∂μG < ⊤ := by
    have hn : 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < a := by
      have h2 : (1 : ℝ) < ((2 * r + k + 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 1 < 2 * r + k + 1)
      have := pow_lt_pow_right₀ h2 (by norm_num : 2 < 5)
      linarith
    have hN := GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r (GG k r) μG a hG hHaar hn
    have heq : ∫⁻ x, f x ∂μG = ENNReal.ofReal (max C 0) * normInt μG a := by
      rw [normInt, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr fun x => ?_
      exact ENNReal.ofReal_mul hC'0
    rw [heq]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN
  unfold HasFiniteIntegral
  calc _ ≤ ∫⁻ x, ‖ξ‖ₑ * ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ∂ν :=
        lintegral_mono_ae (haeG.mono fun x hx => hpt x hx)
    _ = ‖ξ‖ₑ * ∫⁻ x, f x ∂μG := by rw [lintegral_const_mul' _ _ enorm_ne_top, hν f hfm]
    _ < ⊤ := ENNReal.mul_lt_top enorm_lt_top hfin

end GlobalTheory.SgInf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentAntidiagonalMemSkewLatticeStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnipotent_antidiagonal_mem_skewLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ a : Fin r, (∀ w, (gM A γ w (eI k r a) (esI k r a)).re = 0) → (fun w => (gM A γ w (eI k r a) (esI k r a)).im) ∈ skewLat (σ : E →+* E) (dInv E (2 * (r - a.val))) (s a ^ 2) := by
  first | exact @GlobalTheory.SnMass.VolN.IntG.antidiag_mem_skewLat | exact GlobalTheory.SnMass.VolN.IntG.antidiag_mem_skewLat | (intros; apply GlobalTheory.SnMass.VolN.IntG.antidiag_mem_skewLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentCornerEntryMemIdealLatticeStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnipotent_corner_entry_mem_idealLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ p : UTr r, (fun w => gM A γ w (eI k r p.1.1) (esI k r p.1.2)) ∈ ideLat (dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val)) (s p.1.1 * s p.1.2) := by
  first | exact @GlobalTheory.SnMass.VolN.corner_entry_mem_ideLat | exact GlobalTheory.SnMass.VolN.corner_entry_mem_ideLat | (intros; apply GlobalTheory.SnMass.VolN.corner_entry_mem_ideLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentEntryMemInverseDifferentLatticeStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnipotent_entry_mem_inverseDifferentLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ p : UTr r, (fun w => gM A γ w (eI k r p.1.1) (eI k r p.1.2)) ∈ ideLat (dInv E (r - p.1.1.val) * (dInv E (r - p.1.2.val))⁻¹) (s p.1.1 / s p.1.2) := by
  first | exact @GlobalTheory.SnMass.VolN.gM_entry_mem_ideLat | exact GlobalTheory.SnMass.VolN.gM_entry_mem_ideLat | (intros; apply GlobalTheory.SnMass.VolN.gM_entry_mem_ideLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentMemModelUnipotentAtPlaceStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnipotent_mem_modelUnipotentAtPlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ w, gM A γ w ∈ Nset k r := by
  first | exact @GlobalTheory.SnMass.VolN.gM_mem_Nset | exact GlobalTheory.SnMass.VolN.gM_mem_Nset | (intros; apply GlobalTheory.SnMass.VolN.gM_mem_Nset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentMiddleRowMemHomLatticeStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnipotent_middleRow_mem_homLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ a : Fin r, (fun w (l : Fin (k + 1)) => gM A γ w (eI k r a) (wI k r l)) ∈ homLat (σ : E →+* E) J Λ P f A (dInv E (r - a.val)) (s a) := by
  first | exact @GlobalTheory.SnMass.VolN.row_mem_homLat | exact GlobalTheory.SnMass.VolN.row_mem_homLat | (intros; apply GlobalTheory.SnMass.VolN.row_mem_homLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentRadicalFormsUnitSubgroupStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnipotentRadical_forms_unit_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → (∃ G : Subgroup (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)ˣ, ∀ u : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)ˣ, u ∈ G ↔ (u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) ∈ GN (σ : E →+* E) J Λ P) ∧ ∀ γ ∈ GN (σ : E →+* E) J Λ P, IsUnit γ := by
  first | exact @GlobalTheory.SnMass.VolN.gN_subgroup | exact GlobalTheory.SnMass.VolN.gN_subgroup | (intros; apply GlobalTheory.SnMass.VolN.gN_subgroup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralPiProdMulFintypeProductStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_pi_prod_mul_fintype_product : ∀ (ι : Type) [Fintype ι] (X : ι → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (Y : Type) [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν] (f : ∀ i, X i → ENNReal) (g : Y → ENNReal), (∀ i, Measurable (f i)) → Measurable g → ∫⁻ p, (∏ i, f i (p.1 i)) * g p.2 ∂((Measure.pi μ).prod ν) = (∏ i, ∫⁻ y, f i y ∂(μ i)) * ∫⁻ y, g y ∂ν := by
  first | exact @GlobalTheory.StabUnfold.lintegral_pi_prod_mul | exact GlobalTheory.StabUnfold.lintegral_pi_prod_mul | (intros; apply GlobalTheory.StabUnfold.lintegral_pi_prod_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthTailBoundPrimedOfUnprimed
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TypeAsm

def swapW {k r : ℕ} (W : LocW k r) : LocW k r where
  Wp := W.Wq
  Wq := W.Wp
  π := W.π'
  π' := W.π
  z := W.z'
  z' := W.z
  μG := W.μG
  μW := W.μW'
  μW' := W.μW
  μN := W.μN
  νS := W.νS'
  νS' := W.νS

def swapS {k r : ℕ} {W : LocW k r} (A : LocS W) : LocS (swapW W) where
  H := A.H
  σ := A.σ
  B := A.B'
  B' := A.B
  v0 := A.v0
  cN := A.cN
  deg := A.deg

theorem goodW_swap {D : D7} {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    (h : GoodW D τ w w' θ W) : GoodW D τ w' w θ (swapW W) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h2, h1, h4, h3, h6, h5, h7, h10, h11, h8, h9, h12, h14, h13⟩

theorem goodS_swap {D : D7} {W : LocW D.R.k D.R.rS} {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W}
    (h : GoodS D lam A) : GoodS D lam (swapS A) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h4, h3, h5, h6, h7, h8, h10, h9, h11⟩

theorem tailBd_primed_of_unprimed : ∀ (D : D7) (τ : D.what₂.Tau) (w : D.what₂.Word) (θ : ℝ) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (q : ℕ) (H₁ : ℝ), (∀ (W : LocW D.R.k D.R.rS), GoodW D τ w w θ W → ∀ A : LocS W, GoodS D lam A → TailBd W.z W.νS A.Φ q H₁) → ∀ (W : LocW D.R.k D.R.rS), GoodW D τ w w θ W → ∀ A : LocS W, GoodS D lam A → TailBd W.z' W.νS' A.Φ' q H₁ := by
  intro D τ w θ lam q H₁ h W hW A hA
  exact h (swapW W) (goodW_swap hW) (swapS A) (goodS_swap hA)

end GlobalTheory.TypeAsm
end
end

