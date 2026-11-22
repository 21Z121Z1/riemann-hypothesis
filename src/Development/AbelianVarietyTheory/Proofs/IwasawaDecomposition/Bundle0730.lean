import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0849
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0709
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0423
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0179
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0710
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLevelTypeFormsOfUniversalCoeffReading
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0417
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0704
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0461
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitHeckeOperatorsLiftsDoubleCoset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadingInjective
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2 (NExpTied)
open Formalism.AUTREP (GAf)
open GlobalTheory.HeightCounting GlobalTheory.HeightCounting.SideCopy GlobalTheory.TwInputs.Move.Forms

namespace GlobalTheory.HeightCounting.SerCarry

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

def HkAd (X : RealSide D) (Sb : Finset (PlE D.host))
    (hL : ∀ j : ℕ, ℕ → PlE D.host → Module.End D.what₂.LL (Fin (X.R.nW (NX.idxOf D j)) → D.what₂.LL)) : Prop :=
  ∀ j k P α Rr, 1 ≤ j → j ≤ D.R.m → HkDat X.R Sb (NX.idxOf D j) k P α Rr → ∀ x,
    evidence X (NX.idxOf D j) (hL j k P x) =
      hkNorm X.R (NX.idxOf D j) k P • Mult.heckeOn (model X (NX.idxOf D j)) Rr (evidence X (NX.idxOf D j) x)

def HkLaw (D : D7) (S : NX.RatDat D.ntw)
    (eF : ∀ i j b, 1 ≤ j → j ≤ D.R.m → D.nexp.Fm i j b ≃ₗ[FractionRing (D.ntw.O i)] NX.Fm S i j b)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hs : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ k P (x : S.WL j), x ∈ (S.A j).WK → hL j k P x ∈ (S.A j).WK)
    (c : ∀ (i : D.ntw.Tw) (_b : Bool) (_P : PlE D.host), (D.ntw.O i)ˣ) : Prop :=
  ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (k : ℕ) (P : PlE D.host) (x : D.nexp.Fm i j b), P ∉ D.ntw.S0 i →
    IsSplitPl D.host P → k ≤ D.R.r → eF i j b h1 h2 (D.nexp.hkF i j b k P x) =
      algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (c i b P) ^ k • hkF D S i j b (hL j) (hs j h1 h2) k P (eF i j b h1 h2 x)

def LowIn (D : D7) : Prop := ∀ i, ∀ p ∈ lowAll D, placesOver D.host.E p ⊆ ↑(D.ntw.S0 i)

theorem HkAd.at {X : RealSide D} {Sb hL} (H : HkAd X Sb hL) (j : Fin D.R.m)
    (f : (Fin (X.R.nW (NX.idxOf D ((j : ℕ) + 1))) → D.what₂.LL) → Fin (X.R.nW j) → D.what₂.LL) (hf : ∀ x, HEq (f x) x)
    {k P α Rr} (hd : HkDat X.R Sb j k P α Rr) (x) :
    evidence X j (f (hL ((j : ℕ) + 1) k P x)) = hkNorm X.R j k P • Mult.heckeOn (model X j) Rr (evidence X j (f x)) := by
  have key : ∀ (a : Fin D.R.m), a = j → ∀ (u : (Fin (X.R.nW a) → D.what₂.LL) → Fin (X.R.nW a) → D.what₂.LL)
      (f : (Fin (X.R.nW a) → D.what₂.LL) → Fin (X.R.nW j) → D.what₂.LL), (∀ x, HEq (f x) x) →
      (∀ α Rr, HkDat X.R Sb a k P α Rr → ∀ x, evidence X a (u x) = hkNorm X.R a k P • Mult.heckeOn (model X a) Rr (evidence X a x)) →
      ∀ x, evidence X j (f (u x)) = hkNorm X.R j k P • Mult.heckeOn (model X j) Rr (evidence X j (f x)) := by
    intro a haj
    subst haj
    intro u f hf hu x
    rw [eq_of_heq (hf _), eq_of_heq (hf _)]
    exact hu α Rr hd x
  exact key _ (NX.idxOf_succ D j) _ f hf (fun α Rr hd => H _ k P α Rr (Nat.le_add_left _ _) j.2 hd) x

theorem reading_injective (X : RealSide D) (j : Fin D.R.m) : Function.Injective (evidence X j) := by
  refine (X.char.models.HW j _).1.comp ((injective_iff_map_eq_zero _).2 fun x hx => by_contra fun h0 => ?_)
  exact ((X.unif j (sg0 D X.A3.A)).1 1 (fun _ => x) (linearIndependent_unique_iff.2 h0)).ne_zero 0 hx

theorem fiOfEq_heq (X : RealSide D) {a b : Fin D.R.m} (hab : a = b) (x) : HEq ((fiOfEq X hab).e x) x := by
  subst hab; rfl

theorem exists_hkDat (X : RealSide D) (hl : LowIn D) {Sb} (hSb : OverSet D Sb (lowAll D)) {i : D.ntw.Tw} {v : PlE D.host}
    (hv : v ∉ D.ntw.S0 i) (hsp : IsSplitPl D.host v) : v ∉ Sb ∧ ((2 : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal ∧
      ∀ (j : Fin D.R.m) (k : ℕ), k ≤ D.R.r → ∃ α Rr, HkDat X.R Sb j k v α Rr := by
  have hlow : ∀ p ∈ lowAll D, ((p : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := fun p hp hm => hv (hl i p hp hm)
  have hgP : ∀ kk : Fin 2, ((D.host.g kk : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := fun kk =>
    hlow _ (by fin_cases kk <;> simp [lowAll])
  have hso : Bridge.SplitOff v (X.R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := by
    have hAll : X.R.Sb = X.R.Pg := X.char.allPl
    have hPg := X.char.lev.Pg
    refine ⟨(GlobalTheory.HeckeTieCompare.isSplitPl_iff v).1 hsp, fun h => ?_, fun Q hQ h => ?_⟩
    · rw [Finset.mem_coe, hAll] at h
      obtain ⟨kk, hkk⟩ := (hPg v).1 h
      exact hgP kk (GlobalTheory.StepLaw.typePrime_mem_of_div hkk)
    · rw [Finset.mem_coe, hAll] at hQ
      obtain ⟨kk, hkk⟩ := (hPg Q).1 hQ
      have hm := GlobalTheory.StepLaw.typePrime_mem_of_div hkk
      rw [h, Formalism.L2.Col.conjIdeal_asIdeal, Formalism.L2.Col.mem_conjP, map_natCast] at hm
      exact hgP kk hm
  have h1 : v ∉ Sb := fun hh => hv (hSb.subset (hl i) hh)
  have h2 := hlow 2 (by simp [lowAll, Formalism.L2.lowPr])
  refine ⟨h1, h2, fun j k hk => ?_⟩
  obtain ⟨α, Rc, ha, hR⟩ := GlobalTheory.HeckeSupSt.exists_heckeElt X.char.lev X.char.fam j hso hk
  exact ⟨α, Rc, hsp, h1, h2, hk, ha, hR⟩

theorem units_cast {A B : Type} [iA : CommRing A] [iB : CommRing B] (h : A = B) (hi : HEq iA iB) {u : Aˣ} {v : Bˣ} (hu : HEq v u) :
    ringCast h hi (u : A) = v := by
  subst h; cases hi; cases hu; rfl

section Law

variable (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {kKs hk}
  (YS : NX.NExpRealS X.R X.cG (NX.ratDatR X.R X.cG kKs hk)) (hfi : ∀ i x, HEq ((YS.fi i).e x) x)
  (hl : LowIn D) (hl' : LowIn D') {Sb Sb'} (hSb : OverSet D Sb (lowAll D)) (hSb' : OverSet D' Sb' (lowAll D'))
  {hL hL'} (H : HkAd X Sb hL) (H' : HkAd X' Sb' hL')

include hfi hl hl' hSb hSb' H H' in

theorem hk_intertwine {i : D.ntw.Tw} {i' : D'.ntw.Tw} (j : Fin D.R.m) (k : ℕ) {P : PlE D.host} {P' : PlE D'.host} (hP : HEq P P')
    (p0 : P ∉ D.ntw.S0 i) (p1 : P' ∉ D'.ntw.S0 i') (p2 : IsSplitPl D'.host P') (p3 : k ≤ D'.R.r)
    (y : ((NX.ratDatR X.R X.cG kKs hk).A ((j : ℕ) + 1)).WK) (hy) :
    ((ks h m YS j).φ ⟨hL ((j : ℕ) + 1) k P y.1, hy⟩).1 = hL' ((j : ℕ) + 1) k P' ((ks h m YS j).φ y).1 := by
  obtain ⟨q1, q2, q3⟩ := (place_geo h.gal.R h.gal.host).2 P P' hP
  obtain ⟨α', R', hd'⟩ := (exists_hkDat X' hl' hSb' p1 p2).2.2 (h.cm j) k p3
  obtain ⟨r1, r2, -⟩ := exists_hkDat X hl hSb p0 (q1.2 p2)
  obtain ⟨α, R, ha0, hR0, hF⟩ := (hecke_geo h.gal.R h.gal.host h.sp j (h.cm j) rfl).2.2 _ _ (m.βW j (h.cm j) rfl) _ _ m.Pg P P' hP
    k α' R' hd'.elt hd'.reps
  have e0 := H.at j (YS.fi j).e (hfi j) ⟨q1.2 p2, r1, r2, by rw [h.gal.R]; exact p3, ha0, hR0⟩ y.1
  have e0' := H'.at (h.cm j) (fiOfEq X' (NX.idxOf_succ D' (h.cm j))).e (fiOfEq_heq X' _) hd' ((ks h m YS j).φ y).1
  have hnV : D.R.nV = D'.R.nV := by rw [h.gal.R]
  have e1 : hkNorm X.R j k P = hkNorm X'.R (h.cm j) k P' := by
    unfold hkNorm
    rw [q3 _ _ (m.Cmu0 j (h.cm j) rfl), q2, hnV]
  have e2 := hecke_sameMap h m j hF (read_move h m YS j ⟨_, hy⟩) (read_move h m YS j y) (e0.trans (congrArg (· • _) e1))
  exact (fiOfEq X' (NX.idxOf_succ D' (h.cm j))).e.injective (reading_injective X' _ (e2.trans e0'.symm))

include hfi hl hl' hSb hSb' H H' in

theorem hkLaw_move (hsup) {hs c} (hs') {c'} (hc : SameUnits c c') (L : HkLaw D _ YS.eF hL hs c) :
    HkLaw D' (dat h m YS) (tie h m YS hsup).eF hL' hs' c' := by
  intro i' j b h1 h2 k P' x p1 p2 p3
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  have hi := back_heq h i'
  have hP : HEq (cast (place_geo h.gal.R h.gal.host).1.symm P') P' := cast_heq _ _
  generalize cast (place_geo h.gal.R h.gal.host).1.symm P' = P at hP ⊢
  obtain ⟨x, rfl⟩ := (h.fmCast hi _ b).surjective x
  obtain ⟨r1, -, r3⟩ := record_heq h.gal h.set h.frm h.Bsup h.delta hi
  have e1 : D'.nexp.hkF i' (n + 1) b k P' (h.fmCast hi _ b x) = h.fmCast hi _ b (D.nexp.hkF _ (n + 1) b k P x) :=
    eq_of_heq (((r1 _ b _ _ (h.fmCast_heq hi _ b x).symm).2.2 k _ _ hP).symm.trans (h.fmCast_heq hi _ b _).symm)
  have p0 : P ∉ D.ntw.S0 (back h i') := fun hh => p1 ((r3 P P' hP).1.1 hh)
  change eFm h m YS i' (n + 1) b h1 h2 _ = _ • hkF D' (dat h m YS) i' (n + 1) b (hL' (n + 1)) (hs' (n + 1) h1 h2) k P'
    (eFm h m YS i' (n + 1) b h1 h2 _)
  rw [e1, eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2, eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2,
    L _ _ b _ _ k P x p0 (((place_geo h.gal.R h.gal.host).2 P P' hP).1.2 p2) (by rw [h.gal.R]; exact p3), fmOf_smul]
  refine congrArg₂ (· • ·) ?_ (fmOf_restrict (S' := dat h m YS) (h.scal hi b) (ks h m YS ⟨n, lt_m h h2⟩) _ _ _ (hs' (n + 1) h1 h2 k P')
    (fun y => hk_intertwine h m YS hfi hl hl' hSb hSb' H H' ⟨n, lt_m h h2⟩ k hP p0 p1 p2 p3 y _) _)
  rw [map_pow, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  exact congrArg (fun z => algebraMap _ _ z ^ k) (units_cast _ _ (hc _ _ b _ _ hi hP))

end Law

end GlobalTheory.HeightCounting.SerCarry

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingOfIntegersAutCommHostConjugation
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

theorem ringOfIntegers_equiv_bar_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (τ : 𝓞 E ≃+* 𝓞 E) (a : 𝓞 E), τ (H.bar a) = H.bar (τ a) := by
  intro E _ _ _ H τ a
  have hM : (nonZeroDivisors (𝓞 E)).map (τ : 𝓞 E →* 𝓞 E) = nonZeroDivisors (𝓞 E) := by
    exact MulEquivClass.map_nonZeroDivisors τ
  let τE : E ≃+* E := IsLocalization.ringEquivOfRingEquiv E E τ hM
  have hτE : ∀ x : 𝓞 E, τE (x : E) = ((τ x : 𝓞 E) : E) := by
    intro x
    exact IsLocalization.ringEquivOfRingEquiv_eq hM x
  obtain ⟨ψ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply RingOfIntegers.ext
  rw [← hτE, H.bar_eq, H.bar_eq, ← hτE]
  apply ψ.injective
  have h1 := IsCMField.complexEmbedding_complexConj E (ψ.comp (τE : E →+* E)) (a : E)
  have h2 := IsCMField.complexEmbedding_complexConj E ψ (τE (a : E))
  simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom] at h1
  rw [h1, h2]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingOfIntegersEmbeddingFixed
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

namespace GlobalTheory.HeightCounting.Up

theorem rows_O_integers : PrN → AllSt fun _ _ _ _ _ _ x => Function.Injective (Dof x).what₂.OtoLL ∧
    ∃ F : Subfield (Dof x).what₂.LL, ∀ y, y ∈ (Dof x).what₂.OtoLL.range ↔ y ∈ F ∧ IsIntegral ℤ y := by
  intro _
  refine Step.of_all fun K B f T _ _ _ _ w _ P x => ?_
  refine ⟨B.OtoLL_injective, B.Ks.toSubfield, fun y => ?_⟩
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨((show B.O from z) : B.Ks).2, B.O_int z⟩
  · rintro ⟨hy, hi⟩
    exact B.O_full y hy hi

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootToFlag
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.GrassTop

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

noncomputable def rootToFlag (H : Host E) (Dw : Datum H) (x : Root Dw.mult) :
    MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ :=
  if h : x.1 (H.rt : E) = H.rt0 then
    X (⟨x.1, h⟩, ⟨x.2, by have := x.2.isLt; simp only [Datum.mult, h, if_true] at this; omega⟩)
  else
    -X (⟨conjEmb x.1, GlobalTheory.AllWt.conj_mem h⟩,
      ⟨Dw.p + (Dw.q - 1 - x.2), by have := x.2.isLt; simp only [Datum.mult, h, if_false] at this; omega⟩)

noncomputable def rho (H : Host E) (Dw : Datum H) :
    MvPolynomial (Root Dw.mult) ℝ →ₐ[ℝ] MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ :=
  aeval (rootToFlag H Dw)

noncomputable def intGr (H : Host E) (Dw : Datum H) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) : ℝ :=
  Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q)
            (rho H Dw (chernRoots Dw.mult Q * rootDiscr Dw.mult)) /
    ((Dw.p.factorial * Dw.q.factorial : ℝ) ^ Fintype.card (GlobalTheory.AllWt.Psi H))

noncomputable def relIdeal (H : Host E) (Dw : Datum H) : Ideal (MvPolynomial ((E →+* ℂ) × ℕ) ℝ) :=
  Ideal.span ((Set.range fun τ : E →+* ℂ => (X (τ, 0) - 1 : MvPolynomial ((E →+* ℂ) × ℕ) ℝ)) ∪
    {P | ∃ (τ : E →+* ℂ) (k : ℕ), Dw.mult τ < k ∧ P = X (τ, k)} ∪
    {P | ∃ (τ : GlobalTheory.AllWt.Psi H) (k : ℕ), 1 ≤ k ∧
      P = ∑ a ∈ Finset.range (k + 1),
        C ((-1 : ℝ) ^ (k - a)) * X (τ.1, a) * X (conjEmb τ.1, k - a)})

end GlobalTheory.GrassTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowReadingsSameRowsIdentifyDefiniteFormsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowReadings_sameRows_identify_definiteForms : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0'), RowsSame t t' → ∀ (μ : (w.D Z).what₂.Tup) (hμ : Formalism.IndefR.RecTie.Used0 (w.D Z) μ) (hμ' : Formalism.IndefR.RecTie.Used0 (w.D (upL Z S' N h)) μ) (i : Fin (w.D Z).R.m) (x : (w.D Z).what₂.Mt μ ((i : ℕ) + 1)), HEq (t'.r.Y.IL.jMt μ hμ' i x).1 (t.r.Y.IL.jMt μ hμ i x).1 := by
  first | exact @GlobalTheory.Mem.R3.Rw.JmtUp.jMt_rowsSame | exact GlobalTheory.Mem.R3.Rw.JmtUp.jMt_rowsSame | (intros; apply GlobalTheory.Mem.R3.Rw.JmtUp.jMt_rowsSame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SXdAll
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

set_option maxHeartbeats 2000000 in

theorem sXd_all : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, SXd hL := by
  intro hL
  refine StepW.of_all fun K B f T w _ _ _ P x l => ?_
  have hU : x.m.z.R.toRealDat.LUnif := x.m.intersectionNumber_baseChange.prim.unif
  have hW : x.m.z.R.toRealDat.models_HW := x.m.z.pins.char.base.models.HW
  have H := (GlobalTheory.ExportType.type_of_exportTie l.b.ser.ex hU hW).2.2.2
  exact ⟨⟨fun _ j _ => {_d | j ∈ Finset.Icc 1 (Dof x).R.m}, fun i j b a ha u =>
    sub_eq_zero.1 (LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 (H i j ha b a) u))⟩,
    fun i j b h1 h2 => Set.eq_univ_of_forall fun _ => Finset.mem_Icc.2 ⟨h1, h2⟩⟩

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedLowerMapHolds
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.SelRowPin

theorem amb_of_eq {D : D7} {Gp : Type} [Group Gp] [Fintype Gp] {Pl0 T : Type} {m : ℕ} {A : FamIn D.what₂.LL Gp Pl0 T m}
    {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    {X : RowSide D EE} {Fm Fm' : AmbForm D X} {P : Subgroup Gp} {ψ : P →* D.what₂.LLˣ} {tup tup' : T → D.what₂.Tup}
    {jA : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup t)}
    {jA' : ∀ t, (Fin (rDim D A P ψ t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X.Amb (tup' t)}
    (hF : Fm = Fm') (h : tup = tup') (hj : HEq jA jA') :
    (∃ J, AmbTie D A X Fm' P ψ tup' jA' J) → ∃ J, AmbTie D A X Fm P ψ tup jA J := by
  subst hF; subst h; cases hj; exact id

set_option maxHeartbeats 4000000 in

theorem selected_lower_map_third_stage : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (Γ : GeoP) (p : Prm hL), p = prmR N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : Formalism.L2.RecT q.O.ex), RecPinE q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.sat.P → HEq sS q.sat.S → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → Formalism.L2.Rows.RowSideDetermined R.T (divisionPairOfAdelicFormsFaceColumnsData x) := by
  intro _ _ _ _ _ _ _ _ _ hL N Γ p hp _ K q _ _ R hR sP sS _ _ a x hax
  obtain rfl := eq_of_heq hax
  obtain ⟨he, hTw⟩ := hR.s.tw
  have hC : TC.StdC q.w.I q.w.l q.Z R.T.cols := hR.s.cols ▸ q.x.col.std
  apply GlobalTheory.Mem.R3.lower_map_sharp_ambient_tie _ _ _ _ _ _ _ _ q.O.ex a.x R.T
  · exact fun u => GlobalTheory.Mem.Col2.LowerTie.lowerMap_tie q.w.I q.w.ok q.w.pins q.w.l q.Z u _ _ _ (hC u)
  · exact fun u μ hμ _ h1 => GlobalTheory.Mem.Col2.LowerTie.lowerMap_tieTw q.w.I q.w.ok q.w.pins q.w.l q.Z q.w.l0 _ _ _ _ _ _ _ q.O.ex R.T he hC hTw u μ hμ h1
  · cases a with
    | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
    cases x with
    | mk G Pl0 I0 T' A3 core R' F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
    cases pack
    exact amb_of_eq rfl (eq_of_heq htup) hjA q.x.obj.amb.1
  · cases a with
    | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
    cases x with
    | mk G Pl0 I0 T' A3 core R' F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
    cases pack
    exact GlobalTheory.Mem.R3.GamDvd.gamDvd q.w.I q.x.what₂.hX _ _ _ q.w.l q.Z

end GlobalTheory.Mem.R3.SelRowPin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedRealizationGeometric
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

attribute [local instance] GlobalTheory.Mem.R3.TwIn.grp GlobalTheory.Mem.R3.TwIn.fin GlobalTheory.Mem.R3.TwIn.alg

namespace GlobalTheory.Mem.R3.SelRealIn

open Formalism.L2.SG.RowsJoinPinned Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta GlobalTheory.Mem.Top.Bl

section Gen
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 4000000 in

theorem nexp_upd (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (n : NExpRealS R cG S)
    (lam : type_of% R.lam3) (err : type_of% R.err0) :
    ∃ (Sx : RatDat D.ntw) (n' : NExpRealS ((R.updS R.kap lam).withErr err) cG Sx), HEq Sx S ∧ HEq n'.eF n.eF ∧ HEq n'.fi n.fi :=
  ⟨S, ⟨n.fi, n.geq, n.rho, n.chi, n.eF, n.bsup, n.act⟩, HEq.rfl, HEq.rfl, HEq.rfl⟩
end Gen

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx}

theorem psi_pin (q : WPt p.s K) (R : Formalism.L2.RecT q.O.ex) (h : RecPinE q R) (x : TwIn q.O.ex) :
    x.R.ψ = R.T.theta.W.ψ := by
  have h1 := x.pins.keep.std
  have h2 := q.x.th.std
  have e := h.s.theta
  have h3 : Formalism.L2.Theta.IsStdChar (q.w.D q.Z) R.T.theta.W.ψ (-1) :=
    (congrArg (fun z : (Σ a, Formalism.L2.Theta.AllTied (q.w.D q.Z) q.O.ex.th a) => Formalism.L2.Theta.IsStdChar (q.w.D q.Z) z.2.W.ψ (-1)) e).mpr h2
  exact GlobalTheory.StdAdelicChar.isStdChar_unique h1 h3

set_option maxHeartbeats 4000000 in

theorem nexp_move (q : WPt p.s K) (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex) (hx : HEq a.x x) :
    ∃ (Sx : Formalism.IndefR.NX.RatDat (q.w.D q.Z).ntw) (n : Formalism.IndefR.NX.NExpRealS x.R x.cG Sx),
      HEq Sx (Formalism.IndefR.NX.ratDatR (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R q.x.what₂.r.z.cG q.core.row.kKs q.core.row.hk) ∧
      HEq n.eF q.core.row.nexp.eF ∧ HEq n.fi q.core.row.nexp.fi := by
  obtain rfl : a.x = x := eq_of_heq hx
  obtain ⟨Dc, Sp, Zsc, lam, err, _, x, pack, _⟩ := a
  obtain ⟨G, Pl0, I0, T0, A3, core, R, F, cG, _⟩ := x
  dsimp only at pack ⊢
  cases pack
  have h := nexp_upd (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R q.x.what₂.r.z.cG _ q.core.row.nexp lam err
  exact (by with_unfolding_all exact (h :))

set_option maxHeartbeats 4000000 in

theorem realIn_exists : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (Γ : GeoP) (p : Prm hL), p = prmR N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : Formalism.L2.RecT q.O.ex), RecPinE q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.sat.P → HEq sS q.sat.S → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → ∀ (hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH (sS.toSTiesR R).X u (sS.toSTiesR R).Y.hK), HEq (x.F.Sp (zsOf x.R x.F)) (Formalism.IndefR.Cx.spOf (X := (sS.toSTiesR R).X) (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (x.F.Dc (zsOf x.R x.F)) (sS.toSTiesR R).Y.hK (sS.toSTiesR R).G x.wd (fun m => pwOf (sS.toSTiesR R) hin (x.wd m)) x.bR) → ∀ (κ : ℝ) (sEEc : Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) x.R.HE.H →ₗ⋆[ℂ] Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX (sS.toSTiesR R).X)), HEq x.sEE sEEc → 0 < κ → (∀ (v : Tw (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) x.R.HE.H) (hx : x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true))), sEEc v = Tw.mk (twAt (q.w.D q.Z).what₂.embLL x.A3.A.v0) (((1 : ℂ) * (κ : ℂ)) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) (sS.toSTiesR R).X (sS.toSTiesR R).G (Formalism.L2.SG.RowsJoinPinned.iotaX sP.X sP.inst).toMulEquiv q.sat.t q.sat.c) ⟨x.R.HE.e (Tw.out v), hx⟩) ∧ RealDat.nP x.F.lv2 true * ‖sEEc v‖ ^ 2 = ‖v‖ ^ 2) → ∃ y : RealIn x R (sS.toSTiesR R), HEq y.tS q.sat.t ∧ y.cS = q.sat.c ∧ HEq y.Sx (Formalism.IndefR.NX.ratDatR (D := (q.w.st q.Z).toD7) q.x.what₂.r.z.R q.x.what₂.r.z.cG q.core.row.kKs q.core.row.hk) ∧ HEq y.nexp.eF q.core.row.nexp.eF ∧ HEq y.nexp.fi q.core.row.nexp.fi ∧ y.uS = 1 := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 hL N Γ p hp hNE K q hHost hMult R hPin sP sS hsP hsS a x hax hin hsp κ sEEc hsEE hκ hdef
  obtain ⟨hsee, hev, -⟩ := GlobalTheory.Mem.R3.StageMove.spectralStage_point_rowPlacement_transfer K q.B q.f q.T q.w q.Z q.x.Wt _ _ _ _ _ _ _ q.O.ex q.x.what₂ a _ q.sat
  obtain ⟨Sx, nx, hSx, heF, hfi⟩ := nexp_move q a x hax
  have hψ := psi_pin q R hPin x
  have eax : a.x = x := eq_of_heq hax
  rw [eax] at hsee hev
  obtain ⟨hH, -, -, hpos, -, -, hV, hX⟩ := hHost (q.w.st q.Z) q.x.isOver
  have hc : R.T.cols = q.x.col.C := hPin.s.cols
  have hF : (fun u => (R.T.cols.forms u).to0) = fun u => (q.x.col.C.forms u).to0 := by rw [hc]
  have e : (⟨_, sP⟩ : Σ F : ∀ u, Formalism.L2.Forms.Forms0 (q.w.D q.Z) u, GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) F) = ⟨_, q.sat.P⟩ :=
    Sigma.ext hF hsP
  have hm := (congrArg (fun z : (Σ F : ∀ u, Formalism.L2.Forms.Forms0 (q.w.D q.Z) u, GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) F) =>
      SeeAt x.R.toRealDat x.F.lv2 z.2.X z.2.inst q.sat.t ∧
      EvalTieT (MP x.R.toRealDat) x.R.toRealDat.ν0 x.R.toRealDat.fd0 (EP x.R.toRealDat x.F.lv2) z.2.X z.2.G
        (iotaX z.2.X z.2.inst).toMulEquiv q.sat.t q.sat.c) e).mpr ⟨hsee, hev⟩
  refine ⟨{ psiPin := hψ
            hin := hin
            spPin := (by with_unfolding_all exact (hsp :))
            Sx := Sx
            nexp := nx
            stdV := (by with_unfolding_all exact (hV :))
            stdX := (by with_unfolding_all exact (hX :))
            tS := q.sat.t
            cS := q.sat.c
            κS := κ
            ιS := (iotaX sP.X sP.inst).toMulEquiv
            instEq := (by with_unfolding_all exact (sP.inst :))
            ιS_eq := (by with_unfolding_all exact ((GlobalTheory.Mem.JIota.heq_iota_iff (q.w.D q.Z) sP.X sP.inst (iotaX sP.X sP.inst).toMulEquiv).2 rfl :))
            sEEc := sEEc
            sEEj := hsEE
            seeLev := fun _ => (by with_unfolding_all exact (hm.1.conj :))
            seeEval := fun _ => (by with_unfolding_all exact (hm.2 :))
            uS := 1
            uS_norm := norm_one
            seeDef := fun v hx => (by with_unfolding_all exact ((hdef v hx).1 :))
            seeK := ⟨hκ, fun _ v hx => (by with_unfolding_all exact ((hdef v hx).2 :))⟩
            host := (by with_unfolding_all exact (hH :))
            vpos := (by with_unfolding_all exact (hpos :)) }, HEq.rfl, rfl, hSx, heF, hfi, rfl⟩

end GlobalTheory.Mem.R3.SelRealIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitHeckeOperatorsLiftsDoubleCosetStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitHecke_operators_lifts_doubleCoset : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k → ∀ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P →
    Nonempty (Bridge.HeckeTie (Bridge.ratF (Vc X.toD7 i)) P ((famR X I hX U Xg tr).A.heckeL i t)
      (fun x => 1 ≤ x.2 ∧ x.2 ≤ (Vc X.toD7 i).rank) (LiftBrg.envL X I hX U Xg tr L cV i t).isT
      (LiftBrg.envL X I hX U Xg tr L cV i t).isLoc) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.SplitTie.split_tie | exact GlobalTheory.Mem.R3.LiftBrg.SplitTie.split_tie | (intros; apply GlobalTheory.Mem.R3.LiftBrg.SplitTie.split_tie <;> assumption)
end

