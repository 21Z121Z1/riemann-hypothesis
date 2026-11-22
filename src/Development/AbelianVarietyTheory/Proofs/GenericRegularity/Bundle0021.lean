import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0020
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0018
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0016
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0010
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0008
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.FrameRingGlRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.AppLEInjective
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Reg.TieUniq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem eq_of_loc {X : Scheme.{0}} {U : X.Opens} (a b : Γ(X, U))
    (h : ∀ p ∈ U, ∃ (W : X.Opens) (hW : W ≤ U), p ∈ W ∧ resG X hW a = resG X hW b) : a = b := by
  apply TopCat.Presheaf.section_ext X.sheaf U
  intro p hp
  obtain ⟨W, hW, hpW, e⟩ := h p hp
  have e1 := X.presheaf.germ_res_apply (homOfLE hW) p hpW a
  have e2 := X.presheaf.germ_res_apply (homOfLE hW) p hpW b
  exact e1.symm.trans ((congrArg _ e).trans e2)

theorem sec_ext {X : Scheme.{0}} {L : LB X} {s t : LB.Sec L} (h : ∀ i, s.f i = t.f i) : s = t := by
  cases s
  cases t
  congr 1
  exact funext h

theorem isoMaps_unique {X : Scheme.{0}} {L M : LB X} (hL : L.IsLB) (w : LB.Iso L M) (σ : LB.Sec L)
    {s s' : LB.Sec M} (h : IsoMaps w σ s) (h' : IsoMaps w σ s') : s = s' := by
  refine sec_ext fun i => eq_of_loc _ _ fun p hp => ?_
  obtain ⟨k, hk⟩ := exists_chart hL p
  exact ⟨M.U i ⊓ L.U k, inf_le_left, ⟨hp, hk⟩, (h i k).trans (h' i k).symm⟩

theorem appLE_injective {X Y : Scheme.{0}} (g : Y ⟶ X) [IsIso g] (U : X.Opens) (V : Y.Opens) (h : V ≤ g ⁻¹ᵁ U)
    (h' : g ⁻¹ᵁ U ≤ V) : Function.Injective (g.appLE U V h).hom := by
  obtain rfl : V = g ⁻¹ᵁ U := le_antisymm h h'
  rw [Scheme.Hom.appLE_eq_app]
  exact (ConcreteCategory.bijective_of_isIso (g.app U)).1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {M : MChart Y} {R : Type} [CommRing R] [Algebra c.F R] {f : Γ(Y.X, M.U) →+* R} {x : Sp R ⟶ Xo.X}

theorem rigIso_unique {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {g : S' ⟶ S} (m : SABMap t' t g)
    (hab : IsAbelianScheme t'.G) {w w' : LB.Iso t'.PP.L (t.PP.L.pull m.φ)} (h : RigIso m w) (h' : RigIso m w') :
    w = w' :=
  GlobalTheory.iso_eq_of_maps_along_section (S := S') (exists_chart t'.PP.isLB)
    (fun y => (exists_chart t.PP.isLB (m.φ y)).elim fun j hj => ⟨fun _ => j, mem_pull.2 hj⟩)
    t'.G.hom (eSec t'.G) (Over.w η[t'.G]) (GlobalTheory.globalFns_holds _ _ hab).2 h.1 h'.1 h.2 h'.2

theorem lift_abelian (Λ : M.Lift f x) : IsAbelianScheme Λ.t'.G := by
  have hp : IsProper Λ.t'.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) Λ.m1.cart.1 Xo.univ.proper
  exact ⟨Λ.t'.semi.comm, Λ.t'.semi.smooth, hp, Λ.t'.semi.geomConnected⟩

theorem lift_mem (Λ : M.Lift f x) (p : Λ.t'.G.left) : Y.t.G.hom (Λ.m2.φ p) ∈ M.U := by
  have e : Λ.m2.φ ≫ Y.t.G.hom = Λ.t'.G.hom ≫ spMap f ≫ M.hU.fromSpec := Λ.m2.cart.1.w
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  have := M.hU.range_fromSpec
  exact this.le ⟨_, rfl⟩

theorem thTie_unique (Λ : M.Lift f x) {s s' : LB.Sec (PPx x)} (h : Λ.ThTie s) (h' : Λ.ThTie s') : s = s' := by
  obtain ⟨w1, w2, σ, s1, r1, r2, i1, a, b⟩ := h
  obtain ⟨w1', w2', σ', s1', r1', r2', i1', a', b'⟩ := h'
  obtain rfl : w1 = w1' := rigIso_unique Λ.m1 (lift_abelian Λ) r1 r1'
  obtain rfl : w2 = w2' := rigIso_unique Λ.m2 (lift_abelian Λ) r2 r2'
  obtain rfl : σ = σ' := by
    refine sec_ext fun k => eq_of_loc _ _ fun p hp => ?_
    obtain ⟨j, hj⟩ := exists_chart Y.t.PP.isLB (Λ.m2.φ p)
    have h₁ : (Y.t.PP.L.pull Λ.m2.φ).U (fun _ => j) ⊓ Λ.t'.PP.L.U k ≤
        Λ.m2.φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U j) := fun q hq => ⟨lift_mem Λ q, mem_pull.1 hq.1⟩
    refine ⟨(Y.t.PP.L.pull Λ.m2.φ).U (fun _ => j) ⊓ Λ.t'.PP.L.U k, inf_le_right, ⟨mem_pull.2 hj, hp⟩, ?_⟩
    have e := (a j k _ h₁ le_rfl).symm.trans (a' j k _ h₁ le_rfl)
    exact (((w2.s (fun _ => j, k)).isUnit.map _).mul_left_cancel e)
  obtain rfl : s1 = s1' := isoMaps_unique Λ.t'.PP.isLB w1 σ i1 i1'
  have hc : IsPullback Λ.t'.G.hom Λ.m1.φ x Xo.univ.t.G.hom := Λ.m1.cart.1.flip
  let g : Λ.t'.G.left ⟶ Gx x := hc.isoPullback.hom
  have hg : IsIso g := inferInstanceAs (IsIso hc.isoPullback.hom)
  have g1 : g ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = Λ.m1.φ := hc.isoPullback_hom_snd
  have g2 : g ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = Λ.t'.G.hom := hc.isoPullback_hom_fst
  refine sec_ext fun i => ?_
  obtain ⟨j, rfl⟩ : ∃ j : Xo.univ.t.PP.L.ι, i = fun _ => j := ⟨i (0 : Fin 1), funext fun k => congrArg i (Subsingleton.elim (α := Fin 1) k 0)⟩
  have hm : ∀ q : Λ.t'.G.left, q ∈ g ⁻¹ᵁ (PPx x).U (fun _ => j) ↔ Λ.m1.φ q ∈ Xo.univ.t.PP.L.U j := by
    intro q
    rw [← g1, Scheme.Hom.comp_apply]
    exact ⟨fun hq => Set.mem_iInter.1 hq (0 : Fin 1), fun hq => Set.mem_iInter.2 fun _ => hq⟩
  have h₁ : (Xo.univ.t.PP.L.pull Λ.m1.φ).U (fun _ => j) ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j) :=
    fun q hq => (hm q).2 (mem_pull.1 hq)
  exact appLE_injective g _ _ h₁ (fun q hq => mem_pull.2 ((hm q).1 hq))
    ((b g g1 g2 (fun _ => j) h₁).symm.trans (b' g g1 g2 (fun _ => j) h₁))

theorem frPt_eq_of_tie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L) (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L) (y z : FrPt Xo c L), M.Comparison₂ f u y → M.Comparison₂ f u z → y.x = z.x → y = z := by
  intro E _ _ _ H Dw l Xo c O _ β Y M L _ _ f u y z hy hz hx
  obtain ⟨x, xo, v, t1, t2, t3, s, t4⟩ := y
  obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := z
  obtain rfl : x = x' := hx
  obtain ⟨Λ, hv, hs⟩ := hy
  obtain ⟨Λ', hv', hs'⟩ := hz
  obtain ⟨k1, k2⟩ := GlobalTheory.T.modelChartLift_coords_generator_indep E H Dw l Xo c O β Y M L f x Λ' Λ
  obtain rfl : v = v' := by
    funext τ i
    exact ((GlobalTheory.T.lieBasis_coordinates_bijective_tangent E H Dw l Xo c O β Y M L f x Λ).1 _).unique (hv τ i) (k1 _ _ (hv' τ i))
  obtain rfl : s = s' := thTie_unique Λ hs (k2 _ hs')
  rfl

end GlobalTheory.Reg.TieUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.DivFinOfTrdeg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

private theorem fg_lemma {F K : Type} [Field F] [Field K] [Algebra F K] (σ : Type) [Finite σ]
    (h : (⊤ : IntermediateField F K).FG) :
    (⊤ : IntermediateField F (FractionRing (MvPolynomial σ K))).FG := by
  rw [IntermediateField.fg_top_iff] at h ⊢
  haveI : Algebra.EssFiniteType K (FractionRing (MvPolynomial σ K)) :=
    Algebra.EssFiniteType.comp K (MvPolynomial σ K) _
  exact Algebra.EssFiniteType.comp F K _

private theorem trdeg_fractionRing_mvPolynomial {F K : Type} [Field F] [Field K] [Algebra F K] (σ : Type) [Finite σ] (n : ℕ)
    (h : Algebra.trdeg F K = n) :
    Algebra.trdeg F (FractionRing (MvPolynomial σ K)) = (n + Nat.card σ : ℕ) := by
  have h1 : Algebra.trdeg (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) = 0 :=
    trdeg_eq_zero_iff.2 (IsLocalization.isAlgebraic _ (nonZeroDivisors _))
  have h2 := trdeg_add_eq (A := FractionRing (MvPolynomial σ K)) K (MvPolynomial σ K)
  rw [h1, add_zero, MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id] at h2
  have h3 := trdeg_add_eq (A := FractionRing (MvPolynomial σ K)) F K
  rw [← h3, h, ← h2, Nat.cast_add, Nat.cast_card]

theorem divFin_of_trdeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ [Fintype (Comp Xo c)] (d : ReciprocityTheory.ChartRestriction.G.T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z)), 1 ≤ d.D → d.D = Dw.dim + Nat.card (FlagVar Dw) → (∀ Z j, d.w j Z ∈ AG Z d.wL) → (∀ Z, d.w (d.jc Z) Z ≠ 0) → (∀ Z, ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD d Z) → DivFin d := by
  intro E _ _ _ H Dw l Xo c _ d hD hdim hw hjc htr Z r hr
  obtain ⟨hfg, htd⟩ := kap_fg_trdeg E H Dw l Xo c
  have hFG : (⊤ : IntermediateField c.F (Om Z)).FG := fg_lemma (FlagVar Dw) (hfg Z)
  have hT : Algebra.trdeg c.F (Om Z) = d.D := by
    rw [hdim]; exact trdeg_fractionRing_mvPolynomial (FlagVar Dw) Dw.dim (htd Z)
  have hrk : ∀ G, Module.finrank (Om Z) (AG Z G) = 1 := fun G =>
    finrank_span_singleton (AddMonoidAlgebra.single_ne_zero.mpr one_ne_zero)
  exact (GlobalTheory.finite_support_and_density_and_aemeasurable.1 c.F (Comp Xo c) (fun Z => Om Z) (WTZ E)
    (fun Z => AC Z) (fun Z G => AG Z G) d Z hD hFG hT hrk (hw Z) (hjc Z) (htr Z)).1 r hr

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCBaseValAtCx
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem GlobalTheory.Reg.exists_cBase_valAtCx :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, ∃ yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)), (∀ Z, CBase h Z (yP Z)) ∧ ValAtCx h yP ∧ GenFromTest Xo c h := by
  intro E _ _ _ H Dw l Xo c hL h
  have hex : ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ), ∃ z : FrPt Xo c (CAt (sgOf P)), FrMap (PAlg P) (genFr h Z) z :=
    fun Z P => hL.bc _ _ (PAlg P) (genFr h Z)
  choose yP hyP using hex
  refine ⟨yP, fun Z P => hyP Z P, fun Z P a n f hf => ?_, fun Z => hL.test _ _⟩
  have e := GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n f hf (Om Z) (CAt (sgOf P)) (PAlg P)
    (genFr h Z) (yP Z P) (hyP Z P)
  rw [e]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralGeneratorChartPointNoInvertStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralGenerator_chartPoint_noInvert : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V), letI := io.toAlgebra; ∀ (x : Sp T.Fr ⟶ Xo.X) (s : LB.Sec (PPx x)) (Λ : M.Lift ((algebraMap T.V T.Fr).comp f₀) x), Λ.ThTie s → ∀ (G : SAB H (Sp T.V)) (m : SABMap G Y.t (spMap f₀ ≫ M.hU.fromSpec)) (m2 : SABMap Λ.t' G (spMap (algebraMap T.V T.Fr))), m2.φ ≫ m.φ = Λ.m2.φ → ∃ θ : LB.Sec G.PP.L, (∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left (le_top : G.PP.L.U i ≤ ⊤) ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧ ∃ (w1 : LB.Iso Λ.t'.PP.L (Xo.univ.t.PP.L.pull Λ.m1.φ)) (w2 : LB.Iso Λ.t'.PP.L (G.PP.L.pull m2.φ)) (σ : LB.Sec Λ.t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull Λ.m1.φ)) (θ2 : LB.Sec (G.PP.L.pull m2.φ)), RigIso Λ.m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m2.φ θ θ2 ∧ ∀ g : Λ.t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = Λ.m1.φ → g ≫ (fst (Over.mk x) Xo.univ.t.G).left = Λ.t'.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull Λ.m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit)) := by
  first | exact @GlobalTheory.Reg.exists_generator_of_thTie_free | exact GlobalTheory.Reg.exists_generator_of_thTie_free | (intros; apply GlobalTheory.Reg.exists_generator_of_thTie_free <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrShFinOfDivFinOfFinset
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem frShFin_of_divFin_of_finset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ [Fintype (Comp Xo c)] (d : ReciprocityTheory.ChartRestriction.G.T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z)) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ), DivFin d → (∀ Z : Comp Xo c, ∃ S : Finset (Om Z), (∀ s ∈ S, s ≠ 0) ∧ ∀ v : AddValuation (Om Z) (WithTop ℤ), ReciprocityTheory.ChartRestriction.G.T0.IsNormDiscrete v → ((∃ la, ReciprocityTheory.ChartRestriction.G.T0.IsOver (K := c.F) v la) ∨ ReciprocityTheory.ChartRestriction.G.T0.IsTrivOn c.F v) → (∀ s ∈ S, v s = 0) → δ Z v = 0) → FrShFin d δ := by
  intro E _ _ _ H Dw l Xo c _ d δ hd hS
  unfold FrShFin
  unfold DivFin at hd
  intro Z
  obtain ⟨S, hS0, hSv⟩ := hS Z
  refine (Set.Finite.biUnion (t := fun s => {v | d.admitted Z v ∧ v s ≠ 0}) S.finite_toSet
    fun s hs => hd Z s (hS0 s hs)).subset ?_
  rintro v ⟨hadm, hδ⟩
  have hnot : ¬ ∀ s ∈ S, v s = 0 := by
    intro hall
    apply hδ
    obtain ⟨hnd, hcase⟩ := hadm
    refine hSv v hnd ?_ hall
    rcases hcase with ⟨la, hla, -⟩ | ⟨ht, -⟩
    · exact Or.inl ⟨la, hla⟩
    · exact Or.inr ht
  push_neg at hnot
  obtain ⟨s, hs, hvs⟩ := hnot
  exact Set.mem_biUnion (Finset.mem_coe.mpr hs) ⟨hadm, hvs⟩

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.Frames

namespace GlobalTheory.Reg.BorelGroupoid

section Tri

variable {S : Type} [CommRing S] {n : ℕ}

theorem lower_mul (A B : Matrix (Fin n) (Fin n) S) (hA : ∀ i j, i < j → A i j = 0)
    (hB : ∀ i j, i < j → B i j = 0) : ∀ i j, i < j → (A * B) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : i < k
  · rw [hA i k hk, zero_mul]
  · rw [hB k j (lt_of_le_of_lt (not_lt.mp hk) hij), mul_zero]

theorem lower_mul_diag (A B : Matrix (Fin n) (Fin n) S) (hA : ∀ i j, i < j → A i j = 0)
    (hB : ∀ i j, i < j → B i j = 0) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hB k i h, mul_zero]
  · rw [hA i k h, zero_mul]

theorem lower_of_mul_eq_one (A B : Matrix (Fin n) (Fin n) S) (hA : ∀ i j, i < j → A i j = 0)
    (hB : B * A = 1) : ∀ i j, i < j → B i j = 0 := by
  have h : A.BlockTriangular OrderDual.toDual := fun i j hij => hA i j hij
  have hd : IsUnit A.det := Matrix.isUnit_det_of_left_inverse hB
  letI := Matrix.invertibleOfIsUnitDet A hd
  have h' := Matrix.blockTriangular_inv_of_blockTriangular h
  rw [Matrix.inv_eq_left_inv hB] at h'
  exact fun i j hij => h' hij

end Tri

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]

theorem chg_refl (y : FrPt Xo c S) : FrChg (fun _ => 1) 1 y y := by
  refine ⟨rfl, fun τ i => ?_, (Model.secBC_id_iff _ _ _ _).2 fun i => ?_⟩
  · have h := Formalism.L2.PjFree.isCombAt_single (y.tan τ) i
    have e : (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) i = Pi.single i 1 := by
      funext j
      rw [Matrix.one_apply, Pi.single_apply]
      simp only [eq_comm]
    rw [← e] at h
    exact h
  · rw [Model.scal_one, _root_.one_mul]

theorem chg_comp {g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S} {a a' : S}
    {y y' y'' : FrPt Xo c S} (h : FrChg g a y y') (h' : FrChg g' a' y' y'') :
    FrChg (fun τ => g' τ * g τ) (a' * a) y y'' := by
  obtain ⟨hx, hc, hs⟩ := h
  obtain ⟨hx', hc', hs'⟩ := h'
  obtain ⟨x', xo', u', t', e', b', s', gen'⟩ := y'
  obtain ⟨x'', xo'', u'', t'', e'', b'', s'', gen''⟩ := y''
  dsimp only at hx hx' hc hc' hs hs'
  subst hx'
  subst hx
  refine ⟨rfl, fun τ i => ?_, (Model.secBC_id_iff _ _ _ _).2 fun i => ?_⟩
  · have h := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S y.x (y.u τ) (y.tan τ) (u' τ) (g τ).transpose
      (g' τ i) (u'' τ i) (fun k => hc τ k) (hc' τ i)
    have e : (g τ).transpose.mulVec (g' τ i) = (g' τ * g τ) i := by
      funext j
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => _root_.mul_comm _ _
    rw [e] at h
    exact h
  · have e1 := (Model.secBC_id_iff _ _ _ _).1 hs i
    have e2 := (Model.secBC_id_iff _ _ _ _).1 hs' i
    dsimp only
    rw [e2, e1, Model.scal_mul, _root_.mul_assoc]

end Geo

theorem frBor_groupoid : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (S : Type) [CommRing S] [Algebra c.F S], (∀ y : FrPt Xo c S, FrBor 1 y y) ∧ (∀ (t t' : Ix Dw → Sˣ) (y y' y'' : FrPt Xo c S), FrBor t y y' → FrBor t' y' y'' → FrBor (t * t') y y'') ∧ (∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → FrBor t⁻¹ y' y) ∧ ∀ (t t' : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → FrBor t' y y' → t = t' := by
  intro E _ _ _ H Dw l Xo c S _ _
  refine ⟨fun y => ?_, fun t t' y y' y'' h h' => ?_, fun t y y' h => ?_, fun t t' y y' h h' => ?_⟩
  · refine (Model.frBor_iff _ _ _).2 ⟨fun _ => 1, fun τ i => ?_, fun τ i j hij => ?_, chg_refl y⟩
    · exact Matrix.one_apply_eq i
    · exact Matrix.one_apply_ne hij.ne
  · obtain ⟨g, hd, hz, hc⟩ := (Model.frBor_iff _ _ _).1 h
    obtain ⟨g', hd', hz', hc'⟩ := (Model.frBor_iff _ _ _).1 h'
    refine (Model.frBor_iff _ _ _).2 ⟨fun τ => g' τ * g τ, fun τ i => ?_,
      fun τ => lower_mul _ _ (hz' τ) (hz τ), ?_⟩
    · show (g' τ * g τ) i i = _
      rw [lower_mul_diag _ _ (hz' τ) (hz τ), hd, hd', Pi.mul_apply, Units.val_mul, _root_.mul_comm]
    · rw [Pi.mul_apply, Units.val_mul, _root_.mul_comm]
      exact chg_comp hc hc'
  · obtain ⟨g, hd, hz, hc⟩ := (Model.frBor_iff _ _ _).1 h
    obtain ⟨g', a', hc'⟩ := Model.exists_frChg y' y hc.1.symm
    obtain ⟨e1, e2⟩ := Model.frChg_unique (chg_comp hc hc') (chg_refl y)
    have hinv : ∀ τ, g' τ * g τ = 1 := fun τ => congrFun e1 τ
    have hz' : ∀ τ i j, i < j → g' τ i j = 0 := fun τ => lower_of_mul_eq_one _ _ (hz τ) (hinv τ)
    refine (Model.frBor_iff _ _ _).2 ⟨g', fun τ i => ?_, hz', ?_⟩
    · have h2 := lower_mul_diag _ _ (hz' τ) (hz τ) i
      rw [hinv, Matrix.one_apply_eq, hd] at h2
      rw [Pi.inv_apply]
      exact Units.eq_inv_of_mul_eq_one_right h2.symm
    · have : a' = ((t⁻¹ none : Sˣ) : S) := by
        rw [Pi.inv_apply]
        exact Units.eq_inv_of_mul_eq_one_right e2
      exact this ▸ hc'
  · obtain ⟨g, hd, -, hc⟩ := (Model.frBor_iff _ _ _).1 h
    obtain ⟨g', hd', -, hc'⟩ := (Model.frBor_iff _ _ _).1 h'
    obtain ⟨e1, e2⟩ := Model.frChg_unique hc hc'
    funext k
    apply Units.ext
    rcases k with _ | ⟨τ, i⟩
    · exact e2
    · rw [← hd, ← hd', e1]

end GlobalTheory.Reg.BorelGroupoid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsCombAtIffCoordinateCombination
section
noncomputable section

namespace GlobalTheory.Reg.VecComb

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {M : MChart Y}
  {R : Type} [CommRing R]

theorem comb_unique {x : Sp R ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)} {a : Fin m → R}
    {w w' : Sp (DualNumber R) ⟶ Xo.univ.t.G.left} (h : IsCombAt x v a w) (h' : IsCombAt x v a w') : w = w' := by
  obtain ⟨u, hu1, hu2⟩ := h
  obtain ⟨u', hu1', hu2'⟩ := h'
  have e : u = u' := funext fun i => Over.OverMorphism.ext ((hu1 i).trans (hu1' i).symm)
  rw [← hu2, ← hu2', e]

theorem comb_exists {x : Sp R ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)}
    (hv : ∀ j, v j ≫ Xo.univ.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) (a : Fin m → R) :
    ∃ w, IsCombAt x v a w := by
  refine ⟨_, fun i => Over.homMk (spMap (epsMul (a i)) ≫ v i) ?_, fun i => rfl, rfl⟩
  show (spMap (epsMul (a i)) ≫ v i) ≫ Xo.univ.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x
  have e : (epsMul (a i)).comp (algebraMap R (DualNumber R)) = algebraMap R (DualNumber R) :=
    RingHom.ext fun r => by simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  rw [Category.assoc, hv i, ← Category.assoc, ← spMap_comp, e]

variable [Algebra c.F R] {f : Γ(Y.X, M.U) →+* R} {x : Sp R ⟶ Xo.X}

theorem exists_frame (Λ : M.Lift f x) : ∃ V : Fin M.n → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left),
    (∀ j, IsTanAt x (V j)) ∧ ∀ cv w, Λ.Vec cv w ↔ IsCombAt x V cv w := by
  obtain ⟨v', hv1, ⟨htan, -⟩, -⟩ := M.lie R f Λ.t' Λ.m2
  have p1 : IsGrpPullback Λ.t'.G Xo.univ.t.G x Λ.m1.φ := Λ.m1.2
  have p2 : IsGrpPullback Λ.t'.G Y.t.G (spMap f ≫ M.hU.fromSpec) Λ.m2.φ := Λ.m2.2
  refine ⟨fun j => (v' j).left ≫ Λ.m1.φ, fun j => ?_, fun cv w => ?_⟩
  · unfold IsTanAt
    constructor
    · rw [Category.assoc, p1.1.w, ← Category.assoc, Over.w (v' j)]
      rfl
    · exact (Chart.tan_push p1 (v' j)).1 (htan j)
  · unfold MChart.Lift.Vec IsCombAt
    constructor
    · rintro ⟨v'', u', hv'', hc, hw⟩
      have e : v'' = v' := funext fun j => Chart.inj_over p2 ((hv'' j).trans (hv1 j).symm)
      rw [e] at hc
      obtain ⟨u, hu1, hu2⟩ := (Chart.comb_push p1 cv v' u').1 hc
      exact ⟨u, fun i => hu1 i, hu2.trans hw⟩
    · rintro ⟨u, hu1, hu2⟩
      have hw : w ≫ Xo.univ.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x := by
        rw [← hu2]
        exact Over.w (List.ofFn u).prod
      let u' : epsR R ⟶ Λ.t'.G :=
        Over.homMk (p1.1.lift w (spMap (algebraMap R (DualNumber R))) hw) (p1.1.lift_snd _ _ _)
      have hl : u'.left ≫ Λ.m1.φ = w := p1.1.lift_fst _ _ _
      exact ⟨v', u', hv1, (Chart.comb_push p1 cv v' u').2 ⟨u, fun i => hu1 i, hu2.trans hl.symm⟩, hl⟩

theorem isCombAt_iff_vec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (x : Sp R ⟶ Xo.X) (Λ : M.Lift f x), ∀ (m : ℕ) (cv : Fin m → Fin M.n → R) (w : Fin m → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)) (a : Fin m → R) (w' : Sp (DualNumber R) ⟶ Xo.univ.t.G.left), (∀ i, Λ.Vec (cv i) (w i)) → (IsCombAt x w a w' ↔ Λ.Vec (∑ i, a i • cv i) w') := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R _ _ f x Λ m cv w a w' hw
  obtain ⟨V, hV, hVec⟩ := exists_frame Λ
  have hwc : ∀ i, IsCombAt x V (cv i) (w i) := fun i => (hVec _ _).1 (hw i)
  have e : (∑ i, a i • cv i) = (Matrix.of fun j i => cv i j).mulVec a := by
    funext j
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have key : ∀ w'', IsCombAt x w a w'' → IsCombAt x V (∑ i, a i • cv i) w'' := by
    intro w'' h
    rw [e]
    exact GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo R x V hV w _ a w'' (fun i => hwc i) h
  have hov : ∀ {k : Fin M.n → R} {w0}, IsCombAt x V k w0 →
      w0 ≫ Xo.univ.t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x := by
    rintro k w0 ⟨u, -, hu⟩
    rw [← hu]
    exact Over.w (List.ofFn u).prod
  rw [hVec]
  constructor
  · exact key w'
  · intro h
    obtain ⟨w'', h''⟩ := comb_exists (fun i => hov (hwc i)) a
    exact comb_unique (key w'' h'') h ▸ h''

end GlobalTheory.Reg.VecComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.TieBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem MChart.tie_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R S : Type) [CommRing R] [Algebra c.F R] [CommRing S] [Algebra c.F S] (f : Γ(Y.X, M.U) →+* R) (ψ : R →ₐ[c.F] S) (u : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) R) (y : FrPt Xo c R) (z : FrPt Xo c S), M.Comparison₂ f u y → FrMap ψ y z → M.Comparison₂ (ψ.toRingHom.comp f) (fun τ => (u τ).map ψ) z := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R S _ _ _ _ f ψ u y z hT hF
  obtain ⟨Λ, hL, hS⟩ := hT
  obtain ⟨hx, hu, pm, h1, h2, h3⟩ := hF
  obtain ⟨Λ', hV, hTh⟩ := GlobalTheory.T.lift_baseChange_alt E H Dw l Xo c O β Y M R f y.x Λ S ψ
  rcases z with ⟨zx⟩
  dsimp only at hx hu h1 h2 h3 ⊢
  subst hx
  refine ⟨Λ', fun τ i => ?_, hTh _ _ pm h1 h2 h3 hS⟩
  have hv := hV _ _ (hL τ i)
  rw [← hu τ i] at hv
  exact hv

end GlobalTheory.Reg
end

