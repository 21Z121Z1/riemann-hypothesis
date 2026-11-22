import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeLeScaleOfPowBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TiedRecordExistsOfActionPin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeafDataOfOnTieOfIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0193
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0145
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenImmersionOfSection
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.Frames

namespace GlobalTheory.FlatLine.DefinitePoint

theorem subsingleton_of_etale {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Sp K) [Etale f] {Z : Set X}
    (hZ : IsIrreducible Z) : Z.Subsingleton := by
  have : LocallyQuasiFinite f := by
    refine ⟨fun {U} hU {V} hV e => ?_⟩
    have h₁ := f.formallyUnramified_appLE hU hV e
    have h₂ := f.finiteType_appLE hU hV e
    algebraize [(f.appLE U V e).hom]
    exact inferInstanceAs (Algebra.QuasiFinite _ _)
  obtain ⟨o⟩ : Nonempty (Sp K) := ⟨IsLocalRing.closedPoint K⟩
  have hd := f.isDiscrete_preimage_singleton o
  have hu : f ⁻¹' {o} = Set.univ :=
    Set.eq_univ_of_forall fun x => Subsingleton.elim (α := PrimeSpectrum K) _ _
  have : DiscreteTopology X := isDiscrete_univ_iff.mp (hu ▸ hd)
  exact hZ.isPreirreducible.subsingleton

theorem isOpenImmersion_of_section {X Y : Scheme.{0}} (f : X ⟶ Y) [Etale f] (s : Y ⟶ X) (hs : s ≫ f = 𝟙 _) :
    IsOpenImmersion s := by
  haveI : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion
      (MorphismProperty.diagonal @IsOpenImmersion) :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.2 le_rfl
  exact MorphismProperty.of_postcomp (W := @IsOpenImmersion)
    (W' := MorphismProperty.diagonal @IsOpenImmersion) s f
    (inferInstanceAs (IsOpenImmersion (Limits.pullback.diagonal f))) (by rw [hs]; infer_instance)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem etale_strK (Xo : Moduli Dw l) (c : Coeff l) (hq : Dw.q = 0) : Etale (strK (Xo := Xo) (c := c)) := by
  have h0 : Dw.dim = 0 := by rw [Datum.dim, hq, mul_zero]
  have hs : SmoothOfRelativeDimension 0 Xo.s := h0 ▸ Xo.smooth
  have he : Etale Xo.s := (Etale.iff_smoothOfRelativeDimension_zero _).2 hs
  infer_instance

theorem genSp_strK (Z : Comp Xo c) : genSp Z ≫ strK = spMap (algebraMap c.F (kap Z)) :=
  (Spec.map_preimage _).symm

theorem isAlgebraic_kap (Z : Comp Xo c) (hZ : (Z : Set (Xo.XF c)).Subsingleton) :
    Algebra.IsAlgebraic c.F (kap Z) := by
  obtain ⟨L, _, _, j, g, hg, hgZ⟩ := exists_numberField_point Z
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField L (Xo.XF c)).symm.surjective g
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hg hgZ
  have hp : p = genPt Z := by
    refine hZ ?_ (CompSplitPfB.cspB_genPt_mem Z)
    obtain ⟨o⟩ : Nonempty (Sp L) := ⟨IsLocalRing.closedPoint L⟩
    have := hgZ o
    rwa [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at this
  subst hp
  have : CharZero (kap Z) := charZero_of_injective_algebraMap (algebraMap c.F (kap Z)).injective
  have ha : Algebra.IsAlgebraic ℚ (kap Z) :=
    Algebra.IsAlgebraic.of_injective (φ.hom.toRatAlgHom) φ.hom.injective
  exact Algebra.IsAlgebraic.tower_top (K := ℚ) c.F

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.q = 0 → FnAlgClosed Xo c → ∀ Z : Comp Xo c, ∃ y₀ : FrPt Xo c c.F, LiesOn Z y₀ ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → y.x = spMap (algebraMap c.F S) ≫ y₀.x := by
  intro E _ _ _ H Dw l Xo c hq hac Z
  have := etale_strK Xo c hq
  have hZ := subsingleton_of_etale (strK (Xo := Xo) (c := c)) (Z.2.1 : IsIrreducible (Z : Set (Xo.XF c)))
  have halg := isAlgebraic_kap Z hZ
  have hsurj : Function.Surjective (algebraMap c.F (kap Z)) := fun a => by
    obtain ⟨b, hb⟩ := hac Z (algebraMap (kap Z) (Om Z) a) ((halg.isAlgebraic a).algebraMap)
    refine ⟨b, (algebraMap (kap Z) (Om Z)).injective ?_⟩
    rw [← hb, ← IsScalarTower.algebraMap_apply]
  let e : c.F ≃+* kap Z := RingEquiv.ofBijective _ ⟨(algebraMap c.F (kap Z)).injective, hsurj⟩
  let g₀ : Sp c.F ⟶ Xo.XF c := spMap e.symm.toRingHom ≫ genSp Z
  have hg₀ : g₀ ≫ strK = spMap (algebraMap c.F c.F) := by
    rw [Category.assoc, genSp_strK, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun x => e.symm_apply_apply x)
  have hid : spMap (algebraMap c.F c.F) = 𝟙 _ := Spec.map_id _
  have hpt : ∀ s, g₀ s = genPt Z := fun s => by
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  have := isOpenImmersion_of_section strK g₀ (hg₀.trans hid)
  obtain ⟨y₀, hy₀⟩ := exists_frPt_local (c := c) GlobalTheory.abelianSchemeLaws_all.2.secTwist _ (prX_over hg₀)
  refine ⟨y₀, fun s => ?_, fun S _ _ y hy => ?_⟩
  · rw [ptF_eq hg₀ hy₀, hpt]
    exact CompSplitPfB.cspB_genPt_mem Z
  · have hr : Set.range (ptF y) ⊆ Set.range g₀ := by
      rintro _ ⟨s, rfl⟩
      exact ⟨IsLocalRing.closedPoint c.F, (hpt _).trans (hZ (CompSplitPfB.cspB_genPt_mem Z) (hy s))⟩
    have h1 := IsOpenImmersion.lift_fac g₀ (ptF y) hr
    have h2 : IsOpenImmersion.lift g₀ (ptF y) hr = spMap (algebraMap c.F S) := by
      have h3 := congrArg (· ≫ strK) h1
      simp only [Category.assoc, hg₀, hid, Category.comp_id] at h3
      rw [h3, ptF, Limits.pullback.lift_snd]
    rw [hy₀, ← Category.assoc, ← h2, h1, ptF, Limits.pullback.lift_fst]

end GlobalTheory.FlatLine.DefinitePoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OnWithOfIsEmpty
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndexAssembly

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.OntoChain GlobalTheory.RunDepth GlobalTheory.TraceLattice GlobalTheory.TraceClassRank
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {L : SizeData₂ D} {Pm : ParameterChoice' D L}

def ownPrime (D : D7) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) : ℕ := if plc v = D.host.pde then D.host.pde' else D.host.pde

abbrev kap (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (i : Fin D.R.m) : WeightFamilies.Wt D ((i : ℕ) + 1) := kaR Tp hK ((i : ℕ) + 1)

abbrev LevelMaps (J : CoreJ D) (G : Type) (i : Fin D.R.m) : Type :=
  G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)

def BoundTie (L : SizeData₂ D) {Bs : DefBase D.what₂.LL} (N : IndefNum Bs) (C : ℝ) : Prop :=
  ∀ j, N.E1 j = C * (L.sc.x ^ L.sc.eps *
    (sizeBudget D.R L.sc.x L.sc.eps + budgetNc D.R L.sc.x L.sc.eps D.host.T2.card))

section Comparison₂

variable {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {c : OnConst}

local instance runAlg (r : RunData J) : Algebra r.full.J.Q.c.F D.what₂.LL := inst

def DepthTie (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (EX : ErrX D) (Tp : ParamsT D L Pm) (hK : DV.KapDef D)
    {P : Type} [Group P] [Finite P] (O : OnObj S P c) (ι : Bs.J → Fin D.R.m) : Prop :=
  letI := Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.barStar J.Q.H
  letI := (Model.hostMap D).toAlgebra
  RunTie J.toCore EX Tp hK O fun i => (ι i : ℕ) + 1

variable (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
  (fw : FWTie J R (kap Tp hK) v₀) (F : Face D A)
  (r : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData J) (hr : ∀ v, LawsFull (r v).full)
  (ι : Bs.J → Fin D.R.m) (ℓ : ∀ i, LevelMaps J G i) (ph : HeightOneSpectrum (𝓞 D.what₂.LL) → Bs.J → ℂ)

def FormsTie (O : OnObj S (Mir R) c) : Prop :=
  ∃ (hc : LawsCore J.toCore)
    (z : ∀ i, (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
      D.what₂.LL ⊗[(recB hc).KO] (recB hc).Cusp ((ι i : ℕ) + 1) (kap Tp hK (ι i)))
    (act : ∀ i, Mir R → (recB hc).Cusp ((ι i : ℕ) + 1) (kap Tp hK (ι i)) → (recB hc).Cusp ((ι i : ℕ) + 1) (kap Tp hK (ι i)))
    (y : ∀ v i, (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (OnTies.srcDim A (ι i) (R.mu v) F.P0 F.ψ0⁻¹) → D.what₂.LL)),
    ∀ v i, OnTie (T := (r v).full) (R := R) (hr v).p fw hinj EX (ownPrime D v) (ι i) (lR Tp hK ((ι i : ℕ) + 1))
      (fR Tp hK ((ι i : ℕ) + 1)) Tp.TO O v i (z i) (act i) (mirIncl R) (ℓ (ι i)) F.P0 F.ψ0⁻¹ (ph v i) (y v i)

def Tied (O : OnObj S (Mir R) c) : Prop :=
  FormsTie Tp hK hinj EX fw F r hr ι ℓ ph O ∧ DepthTie J EX Tp hK O ι ∧ NumTie Tp hK O

variable (R S) in

def RunsPinned : Prop :=
  (∀ v i, OneCover (r v).full.toTop ((ι i : ℕ) + 1) ∧ TwistTrivialOnRational (r v).full ((ι i : ℕ) + 1)) ∧
    (AtPair S fun v => ∀ i, RunPin (T := (r v).full) R (ι i) D.R.nV v (ownPrime D v)) ∧
    ∀ v, HalfPin (T := (r v).full) R ∧ ∀ i, LevelPin (T := (r v).full) R (ι i) (ℓ (ι i))

def GeneratorInputs : Prop :=
  ∀ v i, Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt (recB (hr v).p.toLawsCore) ((ι i : ℕ) + 1) (kap Tp hK (ι i)) ∧
    ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ (hr v).p ((ι i : ℕ) + 1) (inR_succ (ι i))) (kap Tp hK (ι i)) ∧
    WeightAlgebra.H2 (recPJ (hr v).p ((ι i : ℕ) + 1) (inR_succ (ι i)))
      (scalOfP (recB (hr v).p.toLawsCore) hinj EX (ownPrime D v) (kap Tp hK (ι i)) (lR Tp hK ((ι i : ℕ) + 1))
        (fR Tp hK ((ι i : ℕ) + 1)) Tp.TO) (kap Tp hK (ι i)) (lR Tp hK ((ι i : ℕ) + 1)) (fR Tp hK ((ι i : ℕ) + 1))

variable {Tp hK hinj EX fw F r hr ι ℓ ph} {O : OnObj S (Mir R) c}

variable (Tp hK) in

def withNumbers {P : Type} [Group P] [Finite P] (O : OnObj S P c) : OnObj S P c :=
  { O with
    rr := D.R.r
    T2 := D.host.T2.card
    Nc := budgetNc D.R L.sc.x L.sc.eps D.host.T2.card
    DF := topDeg Tp hK
    de2 := L.de2
    pde := D.host.pde }

variable (J Tp hK EX ι) in

def withDepth {P : Type} [Group P] [Finite P] (O : OnObj S P c) : OnObj S P c :=
  letI := Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR.barStar J.Q.H
  letI := (Model.hostMap D).toAlgebra
  withNumbers Tp hK (Model.retie J.toCore EX Tp hK O fun i => (ι i : ℕ) + 1)

end Comparison₂

def depthConst : ℝ := max 1 leafDepth_all_run_unconditional.choose

def absConst : OnConst := ⟨depthConst, 14, 66 * depthConst + 4⟩

section Bound

variable {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df}
  {Tp : ParamsT D L Pm} {hK : DV.KapDef D} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
  {fw : FWTie J R (kap Tp hK) v₀} {F : Face D A}
  {r : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData J} {hr : ∀ v, LawsFull (r v).full}
  {ι : Bs.J → Fin D.R.m} {ℓ : ∀ i, LevelMaps J G i} {ph : HeightOneSpectrum (𝓞 D.what₂.LL) → Bs.J → ℂ}
  {O : OnObj S (Mir R) absConst} {N : IndefNum Bs} {C : ℝ}

end Bound

def IndexBoundInput (Tp : ParamsT D L Pm) (hK : DV.KapDef D) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df}
    {P : Type} [Group P] [Finite P] {c : OnConst} (O : OnObj S P c) : Prop := DomPlus Tp hK → LatticeIndexBoundAtPairs O

def BadShareInput (L : SizeData₂ D) (x₁ : ℝ → ℝ) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df}
    {P : Type} [Group P] [Finite P] {c : OnConst} (O : OnObj S P c) : Prop := x₁ L.sc.eps ≤ L.sc.x → LeafBadShare O

end GlobalTheory.IndexAssembly
end
end

