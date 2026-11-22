import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0033
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0377
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0340
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0165
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0179
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0376
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.PropsExh
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractionFixed
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RepTensor

theorem extTensor_left {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (k : G) :
    extTensor ρ σ (k, 1) = TensorProduct.map (ρ k) LinearMap.id :=
  TensorProduct.ext' fun a b => by simp [extTensor_tmul]

theorem extTensor_right {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W) (h : H) :
    extTensor ρ σ (1, h) = TensorProduct.map LinearMap.id (σ h) :=
  TensorProduct.ext' fun a b => by simp [extTensor_tmul]

theorem contr_left {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Module.End ℂ V) (l : Module.Dual ℂ W) (v : V ⊗[ℂ] W) :
    A (TensorProduct.rid ℂ V (LinearMap.lTensor V l v)) =
      TensorProduct.rid ℂ V (LinearMap.lTensor V l (TensorProduct.map A LinearMap.id v)) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x w => simp
  | add a b ha hb => simp only [map_add, ha, hb]

theorem contr_right {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (B : Module.End ℂ W) (l : Module.Dual ℂ V) (v : V ⊗[ℂ] W) :
    B (TensorProduct.lid ℂ W (LinearMap.rTensor W l v)) =
      TensorProduct.lid ℂ W (LinearMap.rTensor W l (TensorProduct.map LinearMap.id B v)) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul x w => simp
  | add a b ha hb => simp only [map_add, ha, hb]

theorem mem_fixed_iff' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {K : Subgroup G} {v : V} :
    v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  constructor
  · intro h k hk
    have := h ⟨k, hk⟩
    simpa using this
  · intro h k
    have := h k k.2
    show ρ (k : G) v = ((1 : K →* ℂˣ) k : ℂ) • v
    simpa using this

theorem contrFix : PositivityTheory.Rg.BcB.F.Tail.PExp.ContrFix := by
  intro G H V W _ _ _ _ _ _ ρ σ K L v hv
  have hv' := mem_fixed_iff'.1 hv
  refine ⟨fun l => mem_fixed_iff'.2 fun k hk => ?_, fun l => mem_fixed_iff'.2 fun h hh => ?_⟩
  · have h1 := hv' (k, 1) ⟨hk, L.one_mem⟩
    rw [extTensor_left] at h1
    rw [contr_left, h1]
  · have h1 := hv' (1, h) ⟨K.one_mem, hh⟩
    rw [extTensor_right] at h1
    rw [contr_right, h1]

end GlobalTheory.CompanionTheory.RepTensor
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCountTail
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.IwahoriTraceProof

namespace GlobalTheory.CompanionTheory.IwahoriCount

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem finite_cosets {I : Subgroup G} (ho : IsOpen (I : Set G)) {D : Set G} (hD : IsCompact D) :
    {q : G ⧸ I | q.out ∈ D}.Finite := by
  haveI : DiscreteTopology (G ⧸ I) := QuotientGroup.discreteTopology ho
  have h : IsCompact ((QuotientGroup.mk : G → G ⧸ I) '' D) := hD.image QuotientGroup.continuous_mk
  exact h.finite_of_discrete.subset fun q hq => ⟨q.out, hq, QuotientGroup.out_eq' q⟩

theorem measure_eq_card_mul [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
    {I : Subgroup G} (ho : IsOpen (I : Set G)) {D : Set G} (hD : ∀ g ∈ D, ∀ i ∈ I, g * i ∈ D)
    (S : Finset (G ⧸ I)) (hS : ∀ q, q ∈ S ↔ q.out ∈ D) : μ D = S.card * μ I :=
  _root_.UpperTheory.Reformulated.B.Yla7.main μ ho hD S hS

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem iwahoriCoset_mul {t : Fin n → kˣ} {g i : GL (Fin n) k} (hg : g ∈ iwahoriCoset t)
    (hi : i ∈ iwahori k (Fin n)) : g * i ∈ iwahoriCoset t := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  exact ⟨a, ha, b * i, mul_mem hb hi, by simp only [mul_assoc]⟩

theorem mk_act {t : Fin n → kˣ} (ht : Contracts t) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) {v : V} (hv : v ∈ fixed π (iwahori k (Fin n)))
    {g : GL (Fin n) k} (hg : g ∈ iwahoriCoset t) :
    (Submodule.Quotient.mk (π g v) : Jacquet π (unipB k (Fin n))) = jacBU π t (Submodule.Quotient.mk v) := by
  obtain ⟨u, hu, -, i, hi, rfl⟩ := (mem_iwahoriCoset ht g).1 hg
  rw [jacBU_mk, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, IwahoriInj.mem_fixed.1 hv i hi]
  exact (Submodule.Quotient.eq _).2 (IwahoriInj.sub_mem_twKer hu _)

theorem card_cosets {t : Fin n → kˣ} (ht : Contracts t) (S : Finset (GL (Fin n) k ⧸ iwahori k (Fin n)))
    (hS : ∀ q, q ∈ S ↔ q.out ∈ iwahoriCoset t) : (S.card : ℝ) = (deltaB t)⁻¹ := by
  have ho := IwahoriOnto.isOpen_iwahori k (Fin n)
  have hc := IwahoriOnto.isCompact_iwahori k (Fin n)
  letI : MeasurableSpace (GL (Fin n) k) := _root_.borel _
  haveI : BorelSpace (GL (Fin n) k) := ⟨rfl⟩
  haveI : LocallyCompactSpace (GL (Fin n) k) :=
    hc.locallyCompactSpace_of_mem_nhds_of_group (ho.mem_nhds (one_mem _))
  let μ : Measure (GL (Fin n) k) := Measure.haar
  have h1 := measure_iwahoriCoset μ ht
  have h2 := measure_eq_card_mul μ ho (fun g hg i hi => iwahoriCoset_mul hg hi) S hS
  have h3 : μ.real (iwahoriCoset t) = S.card * μ.real (iwahori k (Fin n) : Set (GL (Fin n) k)) := by
    rw [measureReal_def, measureReal_def, h2, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have h4 : μ.real (iwahori k (Fin n) : Set (GL (Fin n) k)) ≠ 0 := by
    rw [measureReal_def]
    exact (ENNReal.toReal_pos (ho.measure_pos μ ⟨1, one_mem _⟩).ne' hc.measure_lt_top.ne).ne'
  rw [h3, mul_comm] at h1
  exact mul_left_cancel₀ h4 h1

theorem cosetCount : PositivityTheory.Rg.BcB.F.Tail.PExp.CosetCount := by
  intro k _ _ _ _ n t ht
  have hset : {q : GL (Fin n) k ⧸ iwahori k (Fin n) | cosetInd t q.out ≠ 0} =
      {q | q.out ∈ iwahoriCoset t} := by
    ext q
    simp [cosetInd]
  have hfin : {q : GL (Fin n) k ⧸ iwahori k (Fin n) | q.out ∈ iwahoriCoset t}.Finite :=
    finite_cosets (IwahoriOnto.isOpen_iwahori k (Fin n)) (isCompact_iwahoriCoset t)
  refine ⟨hset ▸ hfin, fun V _ _ π v hv => ?_⟩
  have hcard := card_cosets ht hfin.toFinset fun q => hfin.mem_toFinset
  have hsum : PositivityTheory.Rg.BcB.F.Tail.PExp.hkS π (iwahori k (Fin n)) (cosetInd t) v =
      ∑ q ∈ hfin.toFinset, cosetInd t q.out • π q.out v := by
    refine finsum_eq_sum_of_support_subset _ fun q hq => ?_
    rw [Set.Finite.coe_toFinset]
    by_contra h
    apply hq
    have h0 : cosetInd t q.out = 0 := by
      by_contra h'
      exact h (hset ▸ h')
    simp [h0]
  rw [hsum]
  have hterm : ∀ q ∈ hfin.toFinset, (Submodule.Quotient.mk (cosetInd t q.out • π q.out v) :
      Jacquet π (unipB k (Fin n))) = jacBU π t (Submodule.Quotient.mk v) := by
    intro q hq
    have hq' : q.out ∈ iwahoriCoset t := hfin.mem_toFinset.1 hq
    have h1 : cosetInd t q.out = 1 := by simp [cosetInd, hq']
    rw [h1, one_smul]
    exact mk_act ht π hv hq'
  have hmk : (Submodule.Quotient.mk (∑ q ∈ hfin.toFinset, cosetInd t q.out • π q.out v) :
      Jacquet π (unipB k (Fin n))) = ∑ q ∈ hfin.toFinset,
        (Submodule.Quotient.mk (cosetInd t q.out • π q.out v) : Jacquet π (unipB k (Fin n))) :=
    map_sum (Submodule.mkQ _) _ _
  rw [hmk, Finset.sum_congr rfl hterm, Finset.sum_const, ← hcard, Complex.ofReal_natCast,
    Nat.cast_smul_eq_nsmul]

end GlobalTheory.CompanionTheory.IwahoriCount

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosievePairingFamilyCompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue.GlueGen

variable {K : Type} [Field K] {C D : Type 1} [Category.{0} C] [Category.{0} D]

theorem mem_bot (F : C ⥤ ModuleCat.{0} K) (U : ObjectProperty C) (n : ℕ) (z : CH.Cn (U.ι ⋙ F) n) :
    z ∈ relS (U.ι ⋙ F) (fun T => (⊥ : ObjectProperty C) T.obj) n :=
  fun _ hs => False.elim hs

noncomputable def up (F : C ⥤ ModuleCat.{0} K) (U : ObjectProperty C) (n : ℕ) :
    CH.Cn (U.ι ⋙ F) n →ₗ[K] (RC F U (cosieve_bot (C := C))).X n :=
  LinearMap.codRestrict _ LinearMap.id (mem_bot F U n)

def inc (F : C ⥤ ModuleCat.{0} K) (U : ObjectProperty C) :
    Cx.Hom (RC F U (cosieve_bot (C := C))) (CH.cx (U.ι ⋙ F)) (RingHom.id K) :=
  ⟨fun _ => Submodule.subtype _, fun _ _ => rfl⟩

theorem inc_bij (F : C ⥤ ModuleCat.{0} K) (U : ObjectProperty C) (n : ℕ) :
    Function.Bijective ((inc F U).f n) :=
  ⟨Subtype.val_injective, fun z => ⟨⟨z, mem_bot F U n z⟩, rfl⟩⟩

noncomputable def relPr {M : Cx.{1} K} (F : C ⥤ ModuleCat.{0} K) (G : D ⥤ ModuleCat.{0} K) (U : ObjectProperty C)
    (U' : ObjectProperty D) (p : CxPairing M (CH.cx (U.ι ⋙ F)) (CH.cx (U'.ι ⋙ G))) :
    CxPairing M (RC F U (cosieve_bot (C := C))) (RC G U' (cosieve_bot (C := D))) where
  μ {i j n} h := ((p.μ h).compl₂ ((inc F U).f j)).compr₂ (up G U' n)
  leib h x y := Subtype.ext (p.leib h x y.1)

theorem kun_iff (F : ℕ → C ⥤ ModuleCat.{0} K) (E : ℕ → D ⥤ ModuleCat.{0} K) (P : ℕ → Cx.{1} K)
    (U : ObjectProperty C) (U' : ObjectProperty D)
    (p : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (CH.cx (U.ι ⋙ F a')) (CH.cx (U'.ι ⋙ E c))) :
    KunE (P := P) (Q := fun a => RC (F a) U (cosieve_bot (C := C))) (T := fun c => RC (E c) U' (cosieve_bot (C := D)))
        (fun {a a' c} ha => relPr (F a') (E c) U U' (p ha)) ↔
      KunE (P := P) (Q := fun a => CH.cx (U.ι ⋙ F a)) (T := fun c => CH.cx (U'.ι ⋙ E c)) (fun {a a' c} ha => p ha) :=
  GlobalTheory.T.pairing_iso_of_component_isos _ _ (fun a => Cx.Hom.id (P a)) (fun a => inc (F a) U) (fun c => inc (E c) U')
    (fun a n => CrystallineSemistableComparison.P.mapH_bij _ (fun _ => Function.bijective_id) n)
    (fun a n => CrystallineSemistableComparison.P.mapH_bij _ (inc_bij (F a) U) n)
    (fun c n => CrystallineSemistableComparison.P.mapH_bij _ (inc_bij (E c) U') n)
    (fun _ _ _ _ _ _ _ => rfl)

end GlobalTheory.CompanionTheory.KunGlue.GlueGen

open GlobalTheory.CompanionTheory.KunGlue.GlueGen in
theorem GlobalTheory.CompanionTheory.KunGlue.glue_gen : MVBij → CovDesc → ∀ {K : Type} [Field K] {C D : Type 1} [Category.{0} C] [Category.{0} D] (F : ℕ → C ⥤ ModuleCat.{0} K) (E : ℕ → D ⥤ ModuleCat.{0} K) (P : ℕ → Cx.{1} K) (Rel : ObjectProperty C → ObjectProperty D → Prop) (pr : ∀ (U : ObjectProperty C) (U' : ObjectProperty D), Rel U U' → ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (CH.cx (U.ι ⋙ F a')) (CH.cx (U'.ι ⋙ E c))), (∀ {U₁ U₂ : ObjectProperty C} {U₁' U₂' : ObjectProperty D} (r₁ : Rel U₁ U₁') (r₂ : Rel U₂ U₂') (k : U₂ ≤ U₁) (k' : U₂' ≤ U₁') {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n) (x : (P a).X i) (y : CH.Cn (U₁.ι ⋙ F a') j), (resU (E c) k').pullC n ((pr U₁ U₁' r₁ ha).μ hn x y) = (pr U₂ U₂' r₂ ha).μ hn x ((resU (F a') k).pullC j y)) → ∀ {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty C) (W : ι → ObjectProperty D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (hR : ∀ S : Finset ι, Rel (capU V S) (capU W S)), (∀ S : Finset ι, S.Nonempty → KunE (P := P) (Q := fun a => CH.cx ((capU V S).ι ⋙ F a)) (T := fun c => CH.cx ((capU W S).ι ⋙ E c)) (fun {a a' c} ha => pr (capU V S) (capU W S) (hR S) ha)) → KunE (P := P) (Q := fun a => CH.cx ((capU V ∅).ι ⋙ F a)) (T := fun c => CH.cx ((capU W ∅).ι ⋙ E c)) (fun {a a' c} ha => pr (capU V ∅) (capU W ∅) (hR ∅) ha) := by
  intro hmv hcd K _ C D _ _ F E P Rel pr hnat ι _ _ V W cV cW hR hS
  have key := GlobalTheory.T.pairing_restriction_natural hmv (K := K) (ι := ι) P (fun a => covSy (F a) V (cosieve_bot (C := C)))
    (fun c => covSy (E c) W (cosieve_bot (C := D)))
    (fun S {a a' c} ha => relPr (F a') (E c) (capU V S) (capU W S) (pr (capU V S) (capU W S) (hR S) ha))
    (fun {S S'} h {a a' c} ha {i j n} hn x y => Subtype.ext
      (hnat (hR S) (hR S') (fun _ hT => ⟨hT.1, fun α hα => hT.2 α (h hα)⟩)
        (fun _ hT => ⟨hT.1, fun α hα => hT.2 α (h hα)⟩) ha hn x y.1))
    (fun a => hcd K ι C (F a) V ⊥ cosieve_bot cV)
    (fun c => hcd K ι D (E c) W ⊥ cosieve_bot cW)
    (fun S hne => (kun_iff F E P (capU V S) (capU W S) (fun {a a' c} ha => pr (capU V S) (capU W S) (hR S) ha)).2 (hS S hne))
  exact (kun_iff F E P (capU V ∅) (capU W ∅) (fun {a a' c} ha => pr (capU V ∅) (capU W ∅) (hR ∅) ha)).1 key
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleOfContragredientSocle
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.CosocleContra

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}

theorem isIrreducible_quot_of_isCoatom {L : Subrepresentation π} (hL : IsCoatom L) :
    (ProjLine.quot L).IsIrreducible := by
  have h1 : L.toSubmodule ≠ ⊤ := fun e => hL.1 (Subrepresentation.toSubmodule_injective e)
  have := Submodule.Quotient.nontrivial_iff.2 h1
  have : Nontrivial (Subrepresentation (ProjLine.quot L)) := ⟨⊥, ⊤, fun e =>
    bot_ne_top (α := Submodule ℂ (V ⧸ L.toSubmodule)) (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun T => ?_⟩
  let T' : Subrepresentation π :=
    ⟨T.toSubmodule.comap L.toSubmodule.mkQ, fun g v hv => T.apply_mem_toSubmodule g hv⟩
  have hLT : L ≤ T' := fun v hv => by
    have h0 : L.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).2 hv
    show L.toSubmodule.mkQ v ∈ T.toSubmodule
    rw [h0]
    exact zero_mem _
  rcases eq_or_lt_of_le hLT with e | e
  · refine Or.inl (eq_bot_iff.2 fun y hy => ?_)
    obtain ⟨v, rfl⟩ := L.toSubmodule.mkQ_surjective y
    have hv : v ∈ T' := hy
    rw [← e] at hv
    exact (Submodule.Quotient.mk_eq_zero _).2 hv
  · refine Or.inr (eq_top_iff.2 fun y _ => ?_)
    obtain ⟨v, rfl⟩ := L.toSubmodule.mkQ_surjective y
    have hv : v ∈ T' := (hL.2 _ e) ▸ (show v ∈ (⊤ : Subrepresentation π) from trivial)
    exact hv

variable [TopologicalSpace G] [IsTopologicalGroup G]

def pullContra (S : Subrepresentation π) : (contra (ProjLine.quot S)).IntertwiningMap (contra π) where
  toLinearMap :=
    { toFun := fun l => ⟨l.1 ∘ₗ S.toSubmodule.mkQ, mem_smoothPart_of_nhds (Filter.mem_of_superset
        (IsOpen.mem_nhds l.2 (by
          show (ProjLine.quot S).dual 1 l.1 = l.1
          rw [map_one]
          rfl)) fun g hg => LinearMap.ext fun v =>
          LinearMap.congr_fun (show (ProjLine.quot S).dual g l.1 = l.1 from hg) (S.toSubmodule.mkQ v))⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  isIntertwining' _ := rfl

theorem pullContra_injective (S : Subrepresentation π) : Function.Injective (pullContra S) := fun a b h =>
  Subtype.ext (LinearMap.ext fun y => by
    obtain ⟨v, rfl⟩ := S.toSubmodule.mkQ_surjective y
    exact LinearMap.congr_fun (congrArg Subtype.val h) v)

theorem pullContra_apply_eq_zero (S : Subrepresentation π) (l : smoothPart (ProjLine.quot S).dual) {v : V}
    (hv : v ∈ S) : (pullContra S l).1 v = 0 := by
  have h0 : S.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).2 hv
  show l.1 (S.toSubmodule.mkQ v) = 0
  rw [h0, map_zero]

theorem eq_of_isCoatom_of_mem_range {S S' : Subrepresentation π} (hS : IsCoatom S) (hS' : IsCoatom S')
    {w : smoothPart π.dual} (hw : w ≠ 0) (h : w ∈ (pullContra S).range) (h' : w ∈ (pullContra S').range) :
    S = S' := by
  by_contra hne
  have top := hS.sup_eq_top_of_ne hS' hne
  obtain ⟨l, rfl⟩ := h
  obtain ⟨l', hl'⟩ := h'
  refine hw (Subtype.ext (LinearMap.ext fun v => ?_))
  have hv : v ∈ (S ⊔ S').toSubmodule := by
    rw [top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  have h1 := pullContra_apply_eq_zero S l ha
  have h2 := pullContra_apply_eq_zero S' l' hb
  have h3 : (pullContra S l).1 b = 0 := (congrArg (fun y : smoothPart π.dual => y.1 b) hl').symm.trans h2
  show (pullContra S l).1 (a + b) = 0
  rw [map_add, h1, h3, add_zero]

end General

theorem isCosocle_of_isSocle_contra : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → ∀ τ' : IrrRep (GL (Fin N) k), IsSocle τ'.ρ (contra π) → ∃ τ : IrrRep (GL (Fin N) k), IsCosocle τ.ρ π := by
  intro k _ _ _ _ hA N V _ _ π hπ hfl τ' hτ
  obtain ⟨hi, f, hf, hat⟩ := hτ
  have hG := GlobalTheory.SqIntUnit.compactOpen_basis k N
  have hat0 : IsAtom f.range := isAtom_range hi f hf
  have hsm : ∀ S : Subrepresentation π, IsSmooth (ProjLine.quot S) := fun S =>
    (IsSubquotient.of_surjective (ProjLine.quotMk S) S.toSubmodule.mkQ_surjective).isSmooth hπ
  have key : ∀ S : Subrepresentation π, IsCoatom S → (pullContra S).range = f.range := fun S hS => by
    have hirr := isIrreducible_quot_of_isCoatom hS
    exact hat _ (isAtom_range (GlobalTheory.ContraRefl.contra_isIrreducible hG (hA k N _ _ (hsm S) hirr) hirr) _
      (pullContra_injective S))
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push_neg at h
    refine hat0.1 (eq_bot_iff.2 ?_)
    rintro _ ⟨x, rfl⟩
    exact (h x).symm ▸ zero_mem (⊥ : Subrepresentation (contra π)).toSubmodule
  haveI : WellFoundedGT (Subrepresentation π) := ((hasFiniteLength_iff_wellFounded π).1 hfl).1
  have hbt : (⊥ : Subrepresentation π) ≠ ⊤ := fun e => hx (Subtype.ext (LinearMap.ext fun v => by
    have hv : v ∈ (⊥ : Subrepresentation π) := e ▸ (show v ∈ (⊤ : Subrepresentation π) from trivial)
    have hv0 : v = 0 := (Submodule.mem_bot ℂ).1 hv
    rw [hv0, map_zero]
    rfl))
  obtain ⟨L, hL, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subrepresentation π)).resolve_left hbt
  have huniq : ∀ S : Subrepresentation π, IsCoatom S → S = L := fun S hS =>
    eq_of_isCoatom_of_mem_range hS hL hx ((key S hS).symm ▸ ⟨x, rfl⟩) ((key L hL).symm ▸ ⟨x, rfl⟩)
  have hall : ∀ S : Subrepresentation π, S ≤ L ∨ S = ⊤ := fun S => by
    rcases eq_top_or_exists_le_coatom S with h | ⟨M, hM, hSM⟩
    · exact Or.inr h
    · exact Or.inl (huniq M hM ▸ hSM)
  have hc := ProjLine.isCosocle_quot hL.1 hall
  exact ⟨⟨_, ProjLine.quot L, hsm L, hc.1⟩, hc⟩

end GlobalTheory.CompanionTheory.CosocleContra

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistedKernelTop
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMir

section Groups

variable {k : Type} [Field k]

theorem blk_stdBlocks_two {n N : ℕ} (h : ∑ c, ![n, N - n] c = N) (i : Fin N) :
    blk (stdBlocks ![n, N - n] h) i = if (i : ℕ) < n then 0 else 1 := by
  obtain ⟨⟨c, i'⟩, rfl⟩ := (stdBlocks ![n, N - n] h).surjective i
  rw [blk_apply]
  have := stdBlocks_val ![n, N - n] h c i'
  fin_cases c
  · have hi := i'.2
    simp at this hi ⊢
    omega
  · have hi := i'.2
    simp at this hi ⊢
    omega

theorem mem_unipRad_two_iff {n N : ℕ} (h : ∑ c, ![n, N - n] c = N) {g : GL (Fin N) k} :
    g ∈ unipRad k (stdBlocks ![n, N - n] h) ↔
      ∀ i j : Fin N, ¬ ((i : ℕ) < n ∧ n ≤ (j : ℕ)) →
        (g : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  rw [GlobalTheory.RadRev.mem_unipRad_entries]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [blk_stdBlocks_two, blk_stdBlocks_two]
  have : ((if (i : ℕ) < n then (0 : Fin 2) else 1) < if (j : ℕ) < n then 0 else 1) ↔
      ((i : ℕ) < n ∧ n ≤ (j : ℕ)) := by
    by_cases hi : (i : ℕ) < n <;> by_cases hj : (j : ℕ) < n <;> simp [hi, hj] <;> omega
  rw [this]

theorem unipRad_two_le_derUnip {n N : ℕ} (h : ∑ c, ![n, N - n] c = N) :
    unipRad k (stdBlocks ![n, N - n] h) ≤ derUnip k N n := by
  intro g hg
  have hE := (mem_unipRad_two_iff h).1 hg
  refine Subgroup.mem_inf.2 ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩, ?_⟩
  · have := Fin.lt_def.1 hji
    rw [hE i j (by omega), one_apply_ne (ne_of_gt hji)]
  · rw [hE i i (by omega), one_apply_eq]
  · intro i hi
    ext r
    have hc : ((g : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single i 1) r = (g : Matrix (Fin N) (Fin N) k) r i := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hc, hE r i (by omega)]
    by_cases hri : r = i
    · subst hri; simp
    · rw [one_apply_ne hri, Pi.single_apply, if_neg hri]

theorem unipRad_two_ne_bot {n N : ℕ} (h : ∑ c, ![n, N - n] c = N) (h1 : 1 ≤ n) (h2 : n < N) :
    unipRad k (stdBlocks ![n, N - n] h) ≠ ⊥ := by
  set i : Fin N := ⟨0, by omega⟩
  set j : Fin N := ⟨n, h2⟩
  have hne : i ≠ j := by
    intro e
    have := congrArg Fin.val e
    simp [i, j] at this
    omega
  let t : GL (Fin N) k := ⟨transvection i j 1, transvection i j (-1),
    by rw [transvection_mul_transvection_same i j hne]; simp,
    by rw [transvection_mul_transvection_same i j hne]; simp⟩
  have ht : t ∈ unipRad k (stdBlocks ![n, N - n] h) := by
    refine (mem_unipRad_two_iff h).2 fun r s hrs => ?_
    show transvection i j (1 : k) r s = _
    have : ¬ (r = i ∧ s = j) := by
      rintro ⟨rfl, rfl⟩
      exact hrs ⟨by simp [i]; omega, le_refl _⟩
    simp only [transvection, Matrix.add_apply]
    rw [Matrix.single_apply, if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact this ⟨rfl, rfl⟩
  intro hb
  rw [hb, Subgroup.mem_bot] at ht
  have := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i j) ht
  simp [t, transvection, one_apply_ne hne] at this

end Groups

section Chars

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem derChar_eq_one_of_mem_unipRad_two {n N : ℕ} (ψ : AddChar k Circle) (h : ∑ c, ![n, N - n] c = N)
    (u : derUnip k N n) (hu : (u : GL (Fin N) k) ∈ unipRad k (stdBlocks ![n, N - n] h)) :
    derChar k ψ N n u = 1 := by
  have hE := (mem_unipRad_two_iff h).1 hu
  show Circle.toUnits _ = 1
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
  refine (hE p.1 p.2 (by omega)).trans (one_apply_ne fun e => ?_)
  rw [e] at h1
  omega

theorem twKer_unipRad_two_le {n N : ℕ} (ψ : AddChar k Circle) (h : ∑ c, ![n, N - n] c = N)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) :
    twKer π (unipRad k (stdBlocks ![n, N - n] h)) 1 ≤ twKer π (derUnip k N n) (derChar k ψ N n) := by
  refine Submodule.span_mono ?_
  rintro _ ⟨u, v, rfl⟩
  refine ⟨⟨u, unipRad_two_le_derUnip h u.2⟩, v, ?_⟩
  rw [derChar_eq_one_of_mem_unipRad_two ψ h _ u.2]
  simp

end Chars

theorem twKer_derUnip_eq_top_of_isCuspidal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (N n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsCuspidal π → 1 ≤ n → n < N →
      twKer π (derUnip k N n) (derChar k ψ N n) = ⊤ := by
  intro k _ _ _ _ ψ N n V _ _ π hπ h1 h2
  have h : ∑ c, ![n, N - n] c = N := by
    simp [Fin.sum_univ_two]
    omega
  have hs := hπ.2 2 ![n, N - n] (stdBlocks ![n, N - n] h) (unipRad_two_ne_bot h h1 h2)
  have htop : twKer π (unipRad k (stdBlocks ![n, N - n] h)) 1 = ⊤ :=
    Submodule.Quotient.subsingleton_iff.1 hs
  exact eq_top_iff.2 (htop ▸ twKer_unipRad_two_le ψ h π)

end GlobalTheory.CompanionTheory.BZMir
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetLengthOneStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fine_jacquet_length_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (h : Δ.len = 1), FineJac Δ := by
  first | exact @GlobalTheory.CompanionTheory.SegFine.fineJac_one | exact GlobalTheory.CompanionTheory.SegFine.fineJac_one | (intros; apply GlobalTheory.CompanionTheory.SegFine.fineJac_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthExistsCoatomStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_length_exists_coatom : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), HasFiniteLength ρ → Nontrivial V → ∃ S : Subrepresentation ρ, IsCoatom S := by
  first | exact @GlobalTheory.CompanionTheory.FiniteLengthQuot.exists_isCoatom_subrepresentation | exact GlobalTheory.CompanionTheory.FiniteLengthQuot.exists_isCoatom_subrepresentation | (intros; apply GlobalTheory.CompanionTheory.FiniteLengthQuot.exists_isCoatom_subrepresentation <;> assumption)
end

