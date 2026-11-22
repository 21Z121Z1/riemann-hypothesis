import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0736
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0717
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyPtsOfReading
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0634
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0962
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OfFirstStepLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0423
import Formalism.LocalToGlobal.IndefiniteReal.FWCentral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0744
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0745
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0613
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0667
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0721
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0643
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0747
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0706
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0748
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0730
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0460
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0047
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0602
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGeometricAllStates
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.HeightCounting.HeckeLaw

theorem delAt_unr {D : D7} (C : CharFrame D) (i : D.ntw.Tw) {P : PlE D.host} (hP : P ∉ D.ntw.S0 i) :
    (C.delAt (D.ntw.l i)).UnrAt P := by
  have h : ¬ OverP D.host (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) P := fun hk =>
    hP (D.ntw.primes_subset_exceptional i (by rw [← Finset.mem_coe, D.ntw.pD_eq]; exact hk))
  unfold CharFrame.delAt
  split_ifs at h ⊢
  · exact C.isDel'.unr P h
  · exact C.isDel.unr P h

theorem del_values {B : Base} {δ : Fld.FieldDat B.toPre} {f : Fr B.toPre} (h : B.KsExact δ f) :
    f.del.ValuesIn 0 B.KstoC ∧ f.del'.ValuesIn 0 B.KstoC := by
  have h1 : Fld.charField f ≤ B.KsC := ((Fld.listField_le_iff δ f).1 (le_of_eq (Eq.symm h))).2.2.2.2.1
  rw [Fld.valuesIn_iff, Fld.valuesIn_iff, B.imField_KstoC]
  exact ⟨((le_sup_right.trans le_sup_left).trans le_sup_left).trans h1, (le_sup_right.trans le_sup_left).trans h1⟩

theorem delAt_mem {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) {hX : B.fields.Ok} {Wt : Set B.places.Pl}
    (z : Dat (w.st Z) w.I hX T Wt) (i : (w.st Z).toD7.ntw.Tw) (P : PlE (w.st Z).toD7.host) (hP : P ∉ (w.st Z).toD7.ntw.S0 i) :
    ∃ s : z.core.Q.c.F, (w.st Z).toD7.what₂.embLL (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL s) =
      (((z.R.C.delAt ((w.st Z).toD7.ntw.l i)).val P : ℂˣ) : ℂ) := by
  have hC : z.R.C = Fr.at (w.st Z) f := z.lev.C.trans (congrArg _ w.C_eq)
  have hu := delAt_unr z.R.C i hP
  have hv : (z.R.C.delAt ((w.st Z).toD7.ntw.l i)).ValuesIn 0 B.KstoC := by
    rw [hC]
    unfold CharFrame.delAt
    split_ifs
    · exact (del_values w.exact).2
    · exact (del_values w.exact).1
  obtain ⟨y, hy⟩ := hv P hu
  obtain ⟨s, hs⟩ := z.Ks_le y.1 y.2
  refine ⟨s, ?_⟩
  rw [hs]
  refine Eq.trans (show _ = B.KstoC y from rfl) (hy.trans ?_)
  simp [HChar.valTw]

theorem hecke_geometric_of_lb1 : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ _ _ P x => ∀ (l : SeriesLevel hL x) (i : (Dof x).ntw.Tw) (b : Bool) (j : Fin (Dof x).R.m), GlobalTheory.GeoTie.HeckeGeo l.b.YS x.m.z.geo.fw ((Dof x).nth.iC i) b j := by
  intro hP hS hL
  have ev : ∀ {Q : Ctx → Prop}, Ev Q → StepW Start fun K _ _ _ _ => Q K := fun h =>
    Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)
  refine ((ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev).and (ev GlobalTheory.Mem.StdSize.vstd_size_ev)).trans
    (StepW.of_all fun K B f T w hO _ H => ?_)
  intro P x l i b j
  obtain ⟨hHo, -⟩ := H.1 (w.st x.o.Z) hO
  obtain ⟨hStd, hSize⟩ := H.2 (w.st x.o.Z) hO
  have hfin : Finite (TupU w.I (usedOf w.I T P.Wt)) := by
    have hs : ({τ | τ = (Formalism.L2.DIV.mu0F (X := B.fields) (tuOf w.I (usedOf w.I T P.Wt))).1 ∨ τ ∈ tuOf w.I (usedOf w.I T P.Wt)} :
        Set _).Finite :=
      (Set.finite_singleton _).union (tuOf w.I (usedOf w.I T P.Wt)).finite_toSet
    exact hs.to_subtype
  let X := GlobalTheory.TwInputs.RealSide.ofPins x.m.z.geo x.m.z.pins x.m.intersectionNumber_baseChange x.m.inGeo hfin hHo hStd hSize
  have hC := X.char
  have hSb : ∀ Q ∈ x.m.z.R.Sb, Q ∈ (Dof x).ntw.S0 i := by
    intro Q hQ
    have hA : x.m.z.R.Sb = x.m.z.R.Pg := x.m.z.pins.char.allPl
    obtain ⟨k, hk⟩ := l.b.ser.ex.good.Pg i j b Q (by rw [l.b.ser.ex.pin.Pg]; exact hA ▸ hQ)
    exact (Dof x).ntw.placesOver_subset_exceptional i k hk
  exact GlobalTheory.GeoTie.CuspLev.heckeGeo_of_levels l.b.YS x.m.z.geo.fw ((Dof x).nth.iC i) b j l.b.ser.ex
    (x.m.z.geo.fw.evaluates_of_lUnif x.m.intersectionNumber_baseChange.prim.unif) hC.lev hC.models.HW x.m.intersectionNumber_baseChange.prim.unif
    (l.rat.In.ks _ (Nat.le_add_left _ _) j.2) (fun hV => GlobalTheory.HeckeSupReal.readsCusp_realSide hP.decay hS.hkRead (Dof x) X j hV)
    (fun Q hQs hQ => GlobalTheory.SplitOffS0.main l.b.ser.ex.good i _ hSb Q hQs hQ) hS.hkTr
    (fun Q hQ => delAt_mem w x.o.Z x.m.z i Q hQ)

end GlobalTheory.HeightCounting.HeckeLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeGeneratorsOfLinFormEqZeroStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inRealCone_generators_of_linForm_eq_zero : ∀ {X : Type} [AddCommGroup X] {m p : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (e : Fin p ↪ Fin m) (β : LinearMap.BilinForm ℤ X), (∀ i, 0 ≤ h (δ i)) → (∀ i, h (δ i) = 0 → i ∈ Set.range e) →
    InRCone δ β → h β = 0 → InRCone (fun k => δ (e k)) β := by
  first | exact @GlobalTheory.PolFan.inRCone_of_apply_eq_zero | exact GlobalTheory.PolFan.inRCone_of_apply_eq_zero | (intros; apply GlobalTheory.PolFan.inRCone_of_apply_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvHodgeMetricGramMumfordGoodGrowthBoundaryChartStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_hodgeMetricGram_mumfordGoodGrowth_boundaryChart : ∀ (n a : ℕ) (ha : a ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ ∃ (c : ℝ) (N : ℕ), ∀ v : ReciprocityTheory.L2DbarEstimates.V n, v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B v.ofLp).PosDef ∧ (∀ i k, ContDiffAt ℝ 2 (fun u : ReciprocityTheory.L2DbarEstimates.V n => (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B u.ofLp)⁻¹ i k) v) ∧ GlobalTheory.GoodMetric.GoodBound (Finset.univ.map (Fin.castLEEmb ha)) c N (fun u : ReciprocityTheory.L2DbarEstimates.V n => (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B u.ofLp)⁻¹) v := by
  first | exact @GlobalTheory.HodgeInvGood.inv_hodgeGram_goodBound | exact GlobalTheory.HodgeInvGood.inv_hodgeGram_goodBound | (intros; apply GlobalTheory.HodgeInvGood.inv_hodgeGram_goodBound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockDiagonalWithIdentity
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH IsDedekindDomain NumberField Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameBlockDiagonal

theorem rankV (D : D7) (k : Fin D.R.m) : (Vc D k).rank = D.R.nV := by
  rw [D.sp.V_rank _ (Nat.le_add_left _ _) k.2]

def IsBlockDiagonalWithIdentity {K : Type} [CommRing K] {n r : ℕ} (x : GL (Fin r) K) (y : GL (Fin n) K) : Prop :=
  ∀ a b : Fin n, y.val a b =
    if h : a.val < r ∧ b.val < r then x.val ⟨a.val, h.1⟩ ⟨b.val, h.2⟩ else if a = b then 1 else 0

end GlobalTheory.FrameBlockDiagonal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCoverNormalProjectiveCharts
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagModel

theorem exists_flagModel : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Field K] [Algebra O K] [IsFractionRing O K] (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) [Finite B] (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsCover (algebraMap O K) s V α c D → ∃ (n : ℕ) (I : (PSpace O n).IdealSheafData) (π : I.subscheme ⟶ X) (g : ∀ en : En m, I.subscheme ⟶ PSpace O (plN M en.1)) (κ : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ I.subscheme)), π ≫ s = I.subschemeι ≫ PSpace.str O n ∧ IsFlagModel (algebraMap O K) s V α c π g κ := by
  intro O K _ _ _ _ _ _ _ X s T _ m M B _ V α c D hP hN hC
  obtain ⟨P, p0, p, h, hPlk⟩ := GlobalTheory.T.exists_pluckerFlagEmbedding_of_projective_base O K _ X s T m M B V α c D hP hC
  obtain ⟨F, f, i, hf, hi, hif, hcov⟩ := GlobalTheory.T.flagCells_glue_locallyClosed_pluckerProduct O K _ X s T m M B V α c D P p0 p h hP hN hC hPlk
  have hXn : IsLocallyNoetherian X := by
    obtain ⟨N, ι, _, rfl⟩ := hP
    exact LocallyOfFiniteType.isLocallyNoetherian (ι ≫ PSpace.str O N)
  obtain ⟨hFc, hFn, hFnoe⟩ := GlobalTheory.T.compact_normal_noetherian_of_flagCell_cover X T m B V F i hN hi hcov
  have hbase : ∀ b w, i b w ≫ f ≫ p0 ≫ s = spMap ((MvPolynomial.C : Γ(X, (V b).1) →+* CR m (V b)).comp ((α b).comp (algebraMap O K))) := by
    intro b w
    rw [← Category.assoc, hif, ← Category.assoc, hPlk.base, cbase, Category.assoc, hC.ovr, ← Spec.map_comp]
    rfl
  have hrange : Set.range (f ≫ (p0 ≫ s)) ⊆ Set.range (spMap (algebraMap O K)) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨b, w, y, rfl⟩ := hcov x
    refine ⟨spMap ((MvPolynomial.C : Γ(X, (V b).1) →+* CR m (V b)).comp (α b)) y, ?_⟩
    have e := congrArg (fun φ => φ y) (hbase b w)
    have e2 : spMap ((MvPolynomial.C : Γ(X, (V b).1) →+* CR m (V b)).comp ((α b).comp (algebraMap O K))) =
        spMap ((MvPolynomial.C : Γ(X, (V b).1) →+* CR m (V b)).comp (α b)) ≫ spMap (algebraMap O K) := by rw [← Spec.map_comp]; rfl
    rw [e2] at e
    simp only [Scheme.Hom.comp_apply] at e ⊢
    exact e.symm
  obtain ⟨n, I, ν, j, hν, hIn, hIf, hj, hjν, hdense⟩ :=
    GlobalTheory.NormClosure.exists_normal_closure O K P F (p0 ≫ s) f hPlk.proj hf hFc hFn hrange
  have hsep : IsSeparated (ν ≫ p0) := by
    have : IsProper (PSpace.str O n) := isProper_str O n
    have : IsProper ((ν ≫ p0) ≫ s) := by rw [Category.assoc, hν]; infer_instance
    exact IsSeparated.of_comp (ν ≫ p0) s
  have hcover := GlobalTheory.T.preimage_iUnion_opens_eq_range_flagCells O K _ X s T m M B V α c D P p0 p h hC hPlk F I.subscheme f i j ν hf hi hif
    hcov hj hjν hdense hFnoe hsep
  refine ⟨n, I, ν ≫ p0, fun en => ν ≫ p en, fun b w => i b w ≫ j, by rw [Category.assoc, hν], ?_⟩
  have hflat : Flat ((ν ≫ p0) ≫ s) := by rw [Category.assoc]; exact hIf
  have hdense' : Dense ((ν ≫ p0) ⁻¹' ⋃ b, ((V b).1 : Set X)) := by rw [hcover]; exact hdense
  refine ⟨⟨?_, ?_⟩, hIn, hflat, ?_, ?_, hdense', ?_⟩
  · intro b w
    rw [Category.assoc, ← Category.assoc j, hjν, ← Category.assoc, hif, hPlk.base]
  · intro b w en
    obtain ⟨hu, e⟩ := hPlk.plk b w en
    exact ⟨hu, by rw [Category.assoc, ← Category.assoc j, hjν, ← Category.assoc, hif, e]⟩
  · intro b w
    have := hi b w
    infer_instance
  · rw [hcover]
    ext z
    simp only [Set.mem_iUnion, Set.mem_range, Scheme.Hom.comp_apply]
    constructor
    · rintro ⟨b, w, y, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨b, w, y, rfl⟩ := hcov x
      exact ⟨b, w, y, rfl⟩
  · intro k _ z z' hz e1 e2
    have hr : ∀ y, (ν ≫ p0) (z y) ∈ ⋃ b, ((V b).1 : Set X) := fun y =>
      hz ⟨y, (Scheme.Hom.comp_apply _ _ _)⟩
    have hz1 : Set.range z ⊆ Set.range j := by
      rintro _ ⟨y, rfl⟩
      rw [← hcover]
      exact hr y
    have hz2 : Set.range z' ⊆ Set.range j := by
      rintro _ ⟨y, rfl⟩
      rw [← hcover]
      have e := congrArg (fun φ => φ y) e1
      simp only [Scheme.Hom.comp_apply] at e
      show (ν ≫ p0) (z' y) ∈ ⋃ b, ((V b).1 : Set X)
      simp only [Scheme.Hom.comp_apply] at hr ⊢
      rw [← e]
      exact hr y
    let z₀ := IsOpenImmersion.lift j z hz1
    let z₀' := IsOpenImmersion.lift j z' hz2
    have f₀ : z₀ ≫ j = z := IsOpenImmersion.lift_fac _ _ _
    have f₀' : z₀' ≫ j = z' := IsOpenImmersion.lift_fac _ _ _
    have key : z₀ ≫ f = z₀' ≫ f := by
      refine hPlk.ext _ _ _ ?_ fun en => ?_
      · rw [← hjν, ← Category.assoc, ← Category.assoc, f₀, f₀', Category.assoc, Category.assoc]
        exact e1
      · rw [← hjν, ← Category.assoc, ← Category.assoc, f₀, f₀', Category.assoc, Category.assoc]
        exact e2 en
    have := hf
    rw [← f₀, ← f₀', (cancel_mono f).1 key]

end GlobalTheory.FlagModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHeckeAtZeroOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.RatSide.HeckeAtState

open Formalism.BasicNotions.TH Formalism.IndefR.Mult

theorem isDC_one' {G : Type} [Group G] (J : Subgroup G) : Formalism.IndefR.Bridge.IsDC J 1 {1} := by
  refine ⟨fun a ha => ⟨1, 1, by simpa using ha⟩, ?_⟩
  rintro g ⟨k, k', rfl⟩
  exact ⟨1, ⟨Finset.mem_singleton_self _, by simpa using J.mul_mem k.2 k'.2⟩, fun a ha => Finset.mem_singleton.1 ha.1⟩

theorem isHeckeAt_zero_one' {D : D7} (V : HSp D) {P : PlE D.host} (hP : Formalism.BasicNotions.IsSplitPl D.host P) :
    IsHeckeAt V P 0 1 := by
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P ((GlobalTheory.HeckeTieCompare.isSplitPl_iff P).1 hP)
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
  exact ⟨e, ϖ, he, h1, h2, GlobalTheory.HeckeParts.isHeckeElt_one V he.1 ϖ⟩

section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem heckeScalar_eq (R : RealDat3 D A3 Ks) (i : Fin D.R.m) (P : PlE D.host) (k : ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar R.toRealDat i P k = hkNorm R i k P := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar, hkNorm, zpow_neg, zpow_natCast, inv_pow]
end

theorem heckeOn_one {D : D7} {V : HSp D} {S} (M : DSModel V S) (F : MMap M) : heckeOn M {1} F = F := by
  ext v g
  simp [heckeOn, postOn, heckeLin]

end GlobalTheory.HeightCounting.RatSide.HeckeAtState

namespace GlobalTheory.HeightCounting.RatSide.HeckeAtState

open Formalism.BasicNotions.TH Formalism.IndefR.Mult

section Gen
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

open Classical in

def famOf (R : RealDat3 D A3 Ks) (hq : ∀ i : Fin D.R.m, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R.toRealDat i) (j : ℕ) (k : ℕ)
    (Pl : PlE D.host) : Module.End D.what₂.LL (Fin (R.nW (idxOf D j)) → D.what₂.LL) :=
  if h : k ≠ 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace R.toRealDat Pl ∧ k ≤ D.R.r then
    Classical.choose (hq (idxOf D j) Pl h.2.1 k h.2.2)
  else 1

theorem famOf_zero (R : RealDat3 D A3 Ks) (hq : ∀ i : Fin D.R.m, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R.toRealDat i) (j : ℕ)
    (Pl : PlE D.host) : famOf R hq j 0 Pl = 1 := by
  unfold famOf
  rw [dif_neg (fun h => h.1 rfl)]

theorem exists_heckeRd (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (Sb : Finset (PlE D.host))
    (hq : ∀ i : Fin D.R.m, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R.toRealDat i)
    (hg : ∀ v : PlE D.host, IsSplitPl D.host v → v ∉ Sb → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace R.toRealDat v) :
    ∃ hL' : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL ((ratDatR R cG kKs hk).WL j),
      StabC (ratDatR R cG kKs hk) hL' ∧ (∀ j Pl, hL' j 0 Pl = 1) ∧ HeckeRd R cG kKs hk Sb hL' := by
  refine ⟨famOf R hq, ?_, fun j Pl => famOf_zero R hq j Pl, ?_⟩
  · intro j _ _ k Pl y hy
    change famOf R hq j k Pl y ∈ (R.FW (idxOf D j)).WK
    unfold famOf
    split_ifs with h
    · exact (Classical.choose_spec (hq (idxOf D j) Pl h.2.1 k h.2.2)).2 y hy
    · exact hy
  · intro j k Pl α Rr _ _ hd y
    have hg' : GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace R.toRealDat Pl := hg Pl hd.split hd.offS
    by_cases hk0 : k = 0
    · subst hk0
      have hr := (Classical.choose_spec (hq (idxOf D j) Pl hg' 0 (Nat.zero_le _))).1
      have e1 := (GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.readAs_iff _ _ _ _ _ _).1 (hr Rr ⟨α, hd.elt, hd.reps⟩) y
      have e2 := (GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.readAs_iff _ _ _ _ _ _).1
        (hr {1} ⟨1, isHeckeAt_zero_one' _ hd.split, isDC_one' _⟩) y
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar_zero, one_smul] at e1 e2
      have e4 := (e2.trans (heckeOn_one _ _)).symm.trans e1
      have hn : hkNorm R (idxOf D j) 0 Pl = 1 := by simp [hkNorm]
      rw [famOf_zero, hn, one_smul]
      exact e4
    · have h : k ≠ 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace R.toRealDat Pl ∧ k ≤ D.R.r := ⟨hk0, hg', hd.le⟩
      have e1 := (GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.readAs_iff _ _ _ _ _ _).1
        ((Classical.choose_spec (hq (idxOf D j) Pl h.2.1 k h.2.2)).1 Rr ⟨α, hd.elt, hd.reps⟩) y
      have h1 : famOf R hq j k Pl = Classical.choose (hq (idxOf D j) Pl h.2.1 k h.2.2) := by
        unfold famOf
        rw [dif_pos h]
      rw [h1, ← heckeScalar_eq]
      exact e1
end Gen

end GlobalTheory.HeightCounting.RatSide.HeckeAtState

namespace GlobalTheory.HeightCounting.RatSide.HeckeAtState

theorem heckeAtState : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x → ∃ hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j), StabC (SOf x) hL' ∧ (∀ j Pl, hL' j 0 Pl = 1) ∧ HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' := by
  intro hL hD hT hR
  refine (GlobalTheory.T.rational_hecke_at_levels hL hD hT hR).trans (StepW.of_all fun K B f T w _ _ H P x l => ?_)
  exact exists_heckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) (H P x l) (GlobalTheory.T.isGoodSplitHeckePlace_of_split_not_excluded P x)

end GlobalTheory.HeightCounting.RatSide.HeckeAtState

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHomogeneousOfMulIsHomogeneousOfNeZeroRightStatement
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHomogeneous_of_mul_isHomogeneous_of_ne_zero_right : ∀ {σ : Type} (P Q : MvPolynomial σ ℝ) (a b : ℕ), Q ≠ 0 → Q.IsHomogeneous b → (P * Q).IsHomogeneous (a + b) → P.IsHomogeneous a := by
  first | exact @GlobalTheory.GrassTop.isHomogeneous_of_mul_isHomogeneous_right | exact GlobalTheory.GrassTop.isHomogeneous_of_mul_isHomogeneous_right | (intros; apply GlobalTheory.GrassTop.isHomogeneous_of_mul_isHomogeneous_right <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProductLevelDefiniteFormsRealisationAtTwist
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevProd

open GlobalTheory.MtInProd
open Formalism.L2.NX (locM InLevG InParah inParah_one)
open Classical

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem proj_eA (s : SplitPlace L) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    s.proj (eA L v) = if s.v = v then 1 else 0 := by
  show s.i 1 * (idemF (L := L) v) s.v = _
  rw [map_one, one_mul, idemF_apply]

theorem locM_cut (s : SplitPlace L) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (κ : GAf L n) :
    locM s (cutGA (eA_mul v) (conj_eA v) κ) = if s.v = v then locM s κ else 1 := by
  show ((cutGA (eA_mul v) (conj_eA v) κ).1 : Matrix (Fin n) (Fin n) (AL L)).map s.proj = _
  rw [cutGA_val, map_cutMat, proj_eA]
  split_ifs
  · rw [cutMat_one_left]; rfl
  · rw [cutMat_zero_left]

theorem inLevG_one (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (r : ℕ) :
    InLevG v r (1 : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) := by
  refine ⟨inParah_one v r, fun a b _ _ => ⟨fun hba => ?_, fun hab => ?_⟩⟩
  · have h : a ≠ b := fun e => by subst e; exact lt_irrefl _ hba
    rw [Matrix.one_apply_ne h, map_zero]
    exact WithZero.zero_lt_coe _
  · subst hab
    rw [Matrix.one_apply_eq, sub_self, map_zero]
    exact WithZero.zero_lt_coe _

end Gen

theorem main : ∀ (D : D7) (X : NExpTied D) (i : D.ntw.Tw) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m), NG.IsProdLevel (cell X b hA j).J := by
  intro D X i b k Q ψ hA j κ hκ v
  obtain ⟨hU, hG, hQ, hD⟩ := ((cell X b hA j).J_mem κ).1 hκ
  refine ⟨cutGA (eA_mul v) (conj_eA v) κ, ((cell X b hA j).J_mem _).2 ⟨cutGA_mem_Umax _ _ (eA_mem v) hU, fun kv => ?_,
    fun P hP => ?_, fun P hP => ?_⟩, triv_cut_eA v κ, cut_eA_at v κ⟩
  · rw [locM_cut]; split_ifs
    · exact hG kv
    · exact inLevG_one _ _
  · rw [locM_cut]; split_ifs
    · exact hQ P hP
    · exact inParah_one _ _
  · rw [locM_cut]; split_ifs
    · exact hD P hP
    · exact inParah_one _ _

end GlobalTheory.LevProd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotOverRows
section
namespace GlobalTheory.HeightCounting.Up.IsotAtStates

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

set_option maxHeartbeats 2000000 in

theorem isot_overRows : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → PrN →
    OverRows fun _ _ _ _ w Z _ _ z p0 Y => RationalReadingWithoutCongruence z.R z.F p0 Y → GlobalTheory.CuspMult.MultEq z.R.toRealDat →
      Formalism.BasicNotions.Rows.IsotInternal (w.st Z).toD7.what₂ := by
  intro hW hDS hN
  refine EvG.imp (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev) fun K _ _ _ _ hHost => ?_
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, ?_⟩
  intro B f T hO _ _ _ _ w _ Z Wt hX z p0 Y hHo _ _ hGrp _ hRd hME
  have hH : Formalism.IndefR.Links.HostHyp (w.st Z).toD7 := (hHost (w.st Z) hO).1
  have hGS : Formalism.L2.DIV.GoodStable z.Xg := by
    have hI := GlobalTheory.DimPartsCompare.TameTie.idemTie hN.greenC
      (GlobalTheory.DimPartsCompare.tameTie_of_typesTrue (D := (w.st Z).toD7) hGrp).2.1
    refine GlobalTheory.Mem.R3.GoodDual.goodStable_of_coeff (w.st Z).B.embLL z.Xg z.good.irr fun g => ?_
    apply (w.st Z).B.embLL.injective
    rw [z.good.2, z.good.2, map_inv, GlobalTheory.Mem.R3.GoodDual.goodIdempotent_coeff_inv_eq_coeff hI]
  have hIR : Formalism.BasicNotions.Rows.IsotRank (w.st Z).toD7.what₂ :=
    GlobalTheory.Mem.R3.isotRank_of_multEq hW hDS hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG _ Y z.pins hHo hH hGS
      (GlobalTheory.CuspDec.cuspDecomp hN.hc hN.decay _) hME
  exact (GlobalTheory.NRows.L0.parts_positive_scalars_without_congruence_lengths hW hDS hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y hRd z.pins hHo hH).1 hIR

set_option maxHeartbeats 2000000 in

theorem isot_allSt : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → HypH → PrN →
    AllSt fun _ _ _ _ _ _ x => Formalism.BasicNotions.Rows.IsotInternal (Dof x).what₂ := by
  intro hW hDS hH hN
  have h1 := GlobalTheory.HeightCounting.Up.RowModel.overRows_allSt (isot_overRows hW hDS hN)
  have h0 : StepW Start Pinned := StepW.of_all fun _ _ _ _ _ _ _ s => s.1
  refine (StepW.and h1 (h0.trans hH.multL)).trans (StepW.of_all fun K B f T w _ _ hh P x => ?_)
  obtain ⟨hA, hB⟩ := hh
  exact hA P x x.r.Z (hB x.o.Z P.hX P.Wt x.m.z x.fits.grp x.fits.grpAt x.m.exAt x.m.inGeo)

end GlobalTheory.HeightCounting.Up.IsotAtStates
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeStepAtlasRefinementStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_step_atlas_refinement : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (t : Step Y i₀) (Z : Mdl Y i₀) (g : Z.X ⟶ t.B.X) (D : LCrd (Y Z.i) Z.π), IsMap Z t.B g → IsLat t Z g D → ∀ (A : Atlas (Y Z.i) Z.π Z.ty) (X' : Scheme.{0}) (f : X' ⟶ Z.X) (q : X' ⟶ PSpace (Z.i.c.V W) (plN D.N t.k)) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas (Y Z.i) (f ≫ Z.π) ty'), (∀ (K : Type) [Field K] (w : Sp K ⟶ Z.X) (u : Vecs Dw (Y Z.i).t K), A.FlagAt w u ↔ Z.FlagAt w u) → GRel D A t.σ t.le f q A' → q ≫ PSpace.str _ _ = f ≫ Z.π ≫ (Y Z.i).s → Lifts (Z.π ≫ (Y Z.i).s) f q → ∀ (Z₁ : Mdl Y i₀) (g₀ : Z₁.X ⟶ Z.X), IsMap Z₁ Z g₀ → t.Holds Z₁ → LocMaps Z₁ A' := by
  first | exact @GlobalTheory.GrCl.locMaps_of_grel | exact GlobalTheory.GrCl.locMaps_of_grel | (intros; apply GlobalTheory.GrCl.locMaps_of_grel <;> assumption)
end

