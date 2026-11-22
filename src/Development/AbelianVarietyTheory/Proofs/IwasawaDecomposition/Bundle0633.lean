import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0623
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0423
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0618
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0010
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingHomExtValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpModelFiberEqOneIffMemPeriodLattice
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh.PushKer

theorem unit_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

theorem one_left {S T : Scheme.{0}} (a : T ⟶ S) (G : Over S) [MonObj G] :
    (1 : Over.mk a ⟶ G).left = a ≫ (η[G]).left := by
  rw [Hom.one_def]; simp

theorem one_iff {S T : Scheme.{0}} {a : T ⟶ S} {G : Over S} [MonObj G] (x : Over.mk a ⟶ G) :
    x = 1 ↔ x.left = a ≫ (η[G]).left := by
  rw [← one_left]
  exact ⟨fun h => h ▸ rfl, fun h => Over.OverMorphism.ext h⟩

end GlobalTheory.ShFam.Hor.LogCh.PushKer

namespace GlobalTheory.ShFam.Hor.LogCh

open PushKer

theorem pushEx_eq_one_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → ∀ z, pushEx Z Fu y i P p hu hp z = 1 ↔ z ∈ P.range := by
  intro E _ _ _ H Dw l Xo c O _ β Z g ty σ₀ Fu y i P p hu hp hP z
  rw [← Fu.ex_ker i P hP z, one_iff, one_iff, pushEx_left]
  have u0 := unit_comp Z.m0.toSABMap.cart
  have u1 := unit_comp Z.m.cart
  have hs : (η[Z.oF.t.G]).left ≫ Z.oF.t.G.hom = 𝟙 (Xo.XF c) := Over.w (η[Z.oF.t.G])
  constructor
  · intro h
    have e : liftEx Z Fu y i P hu z = y ≫ (η[Z.oF.t.G]).left := by
      apply Z.m.cart.1.hom_ext
      · rw [h, Category.assoc, u1, ← hp]
        simp only [Model.j, Category.assoc]
      · rw [liftEx_snd, Category.assoc, hs, Category.comp_id]
    rw [← liftEx_fst Z Fu y i P hu z, e, Category.assoc, u0, hu, Category.assoc]
  · intro h
    have e : liftEx Z Fu y i P hu z = y ≫ (η[Z.oF.t.G]).left := by
      apply Z.m0.toSABMap.cart.1.hom_ext
      · rw [liftEx_fst, h, Category.assoc, u0, hu, Category.assoc]
      · rw [liftEx_snd, Category.assoc, hs, Category.comp_id]
    rw [e, Category.assoc, u1, ← hp]
    simp only [Category.assoc]

end GlobalTheory.ShFam.Hor.LogCh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesAgreeOnLieEmbeddingChart
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

noncomputable section

namespace GlobalTheory.FlagEmb

theorem exists_comb_le_iff_sub_mem_span {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (v : Fin n → M) (i : Fin n) (y : M) :
    (∃ cf : Fin n → R, (∀ j, i < j → cf j = 0) ∧ y = ∑ j, cf j • v j) ↔
      ∃ d : R, y - d • v i ∈ Submodule.span R (v '' {j | j < i}) := by
  classical
  have hs : ({j | j < i} : Set (Fin n)) = ↑(Finset.univ.filter (· < i)) := by ext j; simp
  simp_rw [hs, Submodule.mem_span_image_finset_iff_exists_fun', Finset.sum_filter]
  constructor
  · rintro ⟨cf, h0, rfl⟩
    refine ⟨cf i, cf, ?_⟩
    have e : ∀ j, cf j • v j = (if j < i then cf j • v j else 0) + (if j = i then cf i • v i else 0) := by
      intro j
      rcases lt_trichotomy j i with h | h | h
      · simp [h, h.ne]
      · subst h; simp
      · simp [h0 j h, not_lt.2 h.le, h.ne']
    rw [eq_sub_iff_add_eq]
    conv_rhs => rw [Finset.sum_congr rfl fun j _ => e j]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  · rintro ⟨d, g, hg⟩
    refine ⟨fun j => if j < i then g j else if j = i then d else 0, fun j hj => ?_, ?_⟩
    · simp [not_lt.2 hj.le, hj.ne']
    · have e : ∀ j, (if j < i then g j else if j = i then d else 0) • v j =
          (if j < i then g j • v j else 0) + (if j = i then d • v i else 0) := by
        intro j
        rcases lt_trichotomy j i with h | h | h
        · simp [h, h.ne]
        · subst h; simp
        · simp [not_lt.2 h.le, h.ne']
      rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_add_distrib, Finset.sum_ite_eq', hg]
      simp

theorem sameFlag_iff_tri_crd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (L : FinLB X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd t L M), IsLieEmb t L aff crd → ∀ (i : Fin L.n) (R : Type) [CommRing R] (φ : Γ(X, L.U i) →+* R) (x : Sp R ⟶ X) (f f' : c.F →+* R) (u u' : Vecs Dw t R), spMap φ ≫ (aff i).fromSpec = x → IsFrame t f x u → IsFrame t f' x u' → (SameFlag (fun τ => Finset.range (Dw.mult τ + 1)) t x u u' ↔ ∃ d, Tri (fun z : Let Dw.mult => crd i R φ (u z.1 z.2)) (fun z => crd i R φ (u' z.1 z.2)) d) ∧ (∀ τ, LinearIndependent R fun j => crd i R φ (u τ j)) ∧ (f = f' → InBlock (fun z : Let Dw.mult => crd i R φ (u z.1 z.2)) (fun z => crd i R φ (u' z.1 z.2))) := by
  intro E _ _ _ H Dw l c X t L aff M crd hL i R _ φ x f f' u u' hx hu hu'
  subst hx
  have htan : ∀ τ j, IsTanAtG t (spMap φ ≫ (aff i).fromSpec) (u τ j) := fun τ j => (hu.1 τ j).1
  have htan' : ∀ τ j, IsTanAtG t (spMap φ ≫ (aff i).fromSpec) (u' τ j) := fun τ j => (hu'.1 τ j).1
  refine ⟨⟨fun hS => ?_, fun ⟨d, hd⟩ => ?_⟩, fun τ => ?_, fun hff => ?_⟩
  · have h : ∀ z : Let Dw.mult, ∃ d : R, crd i R φ (u' z.1 z.2) - d • crd i R φ (u z.1 z.2) ∈
        Submodule.span R ((fun j : Fin (Dw.mult z.1) => crd i R φ (u z.1 j)) '' {j | j < z.2}) := by
      rintro ⟨τ, j⟩
      obtain ⟨cf, hcf0, hcomb⟩ := hS τ (j + 1) (by simp) j (Nat.lt_succ_self _)
      have e := (hL.comb_iff i φ rfl (htan τ) (htan' τ j) cf).1 hcomb
      exact (exists_comb_le_iff_sub_mem_span (fun k => crd i R φ (u τ k)) j _).1
        ⟨cf, fun k hk => hcf0 k (Nat.succ_le_of_lt hk), e⟩
    choose d hd using h
    exact ⟨d, hd⟩
  · intro τ k _ j hjk
    obtain ⟨cf, hcf0, e⟩ := (exists_comb_le_iff_sub_mem_span (fun k => crd i R φ (u τ k)) j _).2 ⟨d ⟨τ, j⟩, hd ⟨τ, j⟩⟩
    refine ⟨cf, fun k' hk' => hcf0 k' (Fin.lt_def.2 (lt_of_lt_of_le hjk hk')), ?_⟩
    exact (hL.comb_iff i φ rfl (htan τ) (htan' τ j) cf).2 e
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    obtain ⟨w, hwt, hwc⟩ := exists_comb t (htan τ) g
    obtain ⟨w0, hw0t, hw0c⟩ := exists_comb t (htan τ) 0
    have e1 := (hL.comb_iff i φ rfl (htan τ) hwt g).1 hwc
    have e0 := (hL.comb_iff i φ rfl (htan τ) hw0t 0).1 hw0c
    have hww : w = w0 := hL.inj i R φ w w0 hwt hw0t (by rw [e1, e0, hg]; simp)
    subst hww
    have heig : ∀ a : 𝓞 E, w ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ w := fun a =>
      (GlobalTheory.FlagEmb.eig_comb_and_frame_cell E H Dw l c X t R _).1 _ (u τ) g w a _ (fun j => ⟨htan τ j, (hu.1 τ j).2 a⟩) hwc
    have := (hu.2 τ w hwt heig).unique hwc hw0c
    intro j
    simpa using congrFun this j
  · subst hff
    intro z
    obtain ⟨a, ha, _⟩ := hu.2 z.1 (u' z.1 z.2) (hu'.1 z.1 z.2).1 (hu'.1 z.1 z.2).2
    have e := (hL.comb_iff i φ rfl (htan z.1) (htan' z.1 z.2) a).1 ha
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨a, e.symm⟩

end GlobalTheory.FlagEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricHalfCoreFormsOfWeakCharacterisation
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj Formalism.IndefR.FWT
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.RealGeo

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw

theorem geometricHalf_coreForms_of_weakCharacterisation (hP : GlobalTheory.Published.CuspRapidDecay) {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {C : CoreJ D} [Algebra C.Q.c.F D.what₂.LL] (R : RealDat3 D A3 C.Q.c.F)
    (F : Face3 D A3) (hch : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (hn : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) {ph : Fin D.R.m → ℂ}
    (geo : GeoHalf C R.toRealDat ph) : InGeo geo := by
  have hC : PreChar R.toRealDat :=
    ⟨hch.base.lev, hch.base.grp.red_R, hch.base.grp.red_L, hch.base.grp.record, hch.base.fam, hch.base.models,
      RealDat.chain_of_weak hch.base.chain hEx, RealDat.thP_of_weak hch.base.thP hEx⟩
  have hp : C.pb = R.toRealDat.C.P.pb :=
    GlobalTheory.PinsFixHalf.pb_eq_of_pins C R.toRealDat geo.κ geo.v₀ geo.O hC.lev geo.fw.laws geo.pins
  exact (GlobalTheory.RealGeoIn.inGeo_and_lUnif_and_lIntegral hP _ _ _ _ _ C R.toRealDat _ geo hC hch.base.grp.chiW hp hn).1

theorem stepW_rank_large (p : WP) :
    StepW p fun _ _ _ _ w => ∀ Z : w.Lt, 8 * (w.st Z).toD7.R.f * (w.st Z).toD7.R.r + 4 ≤ (w.st Z).toD7.R.nV :=
  Step.of_evG ((evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev).imp fun _ _ _ _ _ H _ _ _ hO _ _ _ w _ Z => (H (w.st Z) hO).2)

set_option maxHeartbeats 1000000 in

theorem inGeo_stepW (hP : GlobalTheory.Published.CuspRapidDecay) (p : WP) :
    StepW p fun _ B' _ _ w' => ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok) (U : Set w'.I.ι) (core' : CoreJ (w'.st Z').toD7)
      (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL), letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
        (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' U Xg tr) core'.Q.c.F)
        (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        Pins R' (face0 (w'.st Z') w'.I hX' U Xg tr) cG' → R'.toRealDat.ExAt →
        ∀ (ph : Fin (w'.st Z').toD7.R.m → ℂ) (geo : GeoHalf core' R'.toRealDat ph), InGeo geo :=
  (stepW_rank_large p).trans (StepW.of_all fun _ _ _ _ _ _ _ H Z' _ _ _ _ _ _ R' _ hPin hEx _ geo =>
    geometricHalf_coreForms_of_weakCharacterisation hP R' _ hPin.char hEx (H Z') geo)

end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricHalfCoreFormsUniformisationIntegralStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricHalf_coreForms_uniformisation_integral : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (ph : Fin D.R.m → ℂ) (B : GeoHalf T R ph), PreChar R → R.grp_chiW → T.pb = R.C.P.pb → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → InGeo B ∧ R.LUnif ∧ R.LIntegral := by
  first | exact @GlobalTheory.RealGeoIn.inGeo_and_lUnif_and_lIntegral | exact GlobalTheory.RealGeoIn.inGeo_and_lUnif_and_lIntegral | (intros; apply GlobalTheory.RealGeoIn.inGeo_and_lUnif_and_lIntegral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannCellSpanPreserved
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GrCl

variable {S : Type} [CommRing S] {m a k b : ℕ}

def gcellOff (x : GVar m a k b → S) (i l : Fin m) : S :=
  if h : a ≤ (l : ℕ) ∧ (l : ℕ) < k ∧ k ≤ (i : ℕ) ∧ (i : ℕ) < b then x ⟨(i, l), h⟩ else 0

theorem gcellOff_ne (x : GVar m a k b → S) {i l : Fin m} (h : gcellOff x i l ≠ 0) :
    a ≤ (l : ℕ) ∧ (l : ℕ) < k ∧ k ≤ (i : ℕ) ∧ (i : ℕ) < b := by
  by_contra h'
  exact h (by simp [gcellOff, h'])

theorem gcellOff_of_ge (x : GVar m a k b → S) (i : Fin m) {l : Fin m} (h : k ≤ (l : ℕ)) : gcellOff x i l = 0 := by
  by_contra h'
  have := gcellOff_ne x h'
  omega

theorem gcellOff_of_lt (x : GVar m a k b → S) {i : Fin m} (l : Fin m) (h : (i : ℕ) < k) : gcellOff x i l = 0 := by
  by_contra h'
  have := gcellOff_ne x h'
  omega

theorem gcell_eq_add (x : GVar m a k b → S) (i l : Fin m) :
    gcell x i l = gcellOff x i l + if i = l then 1 else 0 := by
  by_cases h : a ≤ (l : ℕ) ∧ (l : ℕ) < k ∧ k ≤ (i : ℕ) ∧ (i : ℕ) < b
  · have hne : i ≠ l := fun e => by subst e; omega
    simp [gcell, gcellOff, h, hne]
  · simp [gcell, gcellOff, h]

variable {Q : Type} [AddCommGroup Q] [Module S Q]

theorem gvec_eq_add (c : Fin m → Q) (w : GPm m a b) (x : GVar m a k b → S) (l : Fin m) :
    gvec c w x l = c (w.1 l) + ∑ i, gcellOff x i l • c (w.1 i) := by
  simp only [gvec, gcell_eq_add, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [add_comm]

theorem gvec_of_ge (c : Fin m → Q) (w : GPm m a b) (x : GVar m a k b → S) {l : Fin m} (h : k ≤ (l : ℕ)) :
    gvec c w x l = c (w.1 l) := by
  rw [gvec_eq_add]
  simp [gcellOff_of_ge x _ h]

theorem gvec_inv (c : Fin m → Q) (w : GPm m a b) (x : GVar m a k b → S) (l : Fin m) :
    c (w.1 l) = gvec c w x l - ∑ i, gcellOff x i l • gvec c w x i := by
  have hs : ∑ i, gcellOff x i l • gvec c w x i = ∑ i, gcellOff x i l • c (w.1 i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : gcellOff x i l = 0
    · simp [h]
    · rw [gvec_of_ge c w x (gcellOff_ne x h).2.2.1]
  rw [hs, gvec_eq_add]
  abel

theorem gvec_combo (c : Fin m → Q) (w : GPm m a b) (x : GVar m a k b → S) (g : Fin m → S) :
    ∑ l, g l • gvec c w x l = ∑ i, (g i + ∑ l, gcellOff x i l * g l) • c (w.1 i) := by
  simp only [gvec_eq_add, smul_add, Finset.sum_add_distrib, add_smul, Finset.smul_sum, smul_smul, Finset.sum_smul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by rw [mul_comm]

theorem gpm_lt_iff (w : GPm m a b) {e : ℕ} (he : e ≤ a ∨ b ≤ e) (i : Fin m) :
    (w.1 i : ℕ) < e ↔ (i : ℕ) < e := by
  by_cases hi : (i : ℕ) < a ∨ b ≤ (i : ℕ)
  · rw [w.2 i hi]
  · have hwi : ¬ ((w.1 i : ℕ) < a ∨ b ≤ (w.1 i : ℕ)) := fun h => by
      have := w.1.injective (w.2 _ h)
      rw [this] at h
      exact hi h
    omega

theorem gvec_linearIndependent (c : Fin m → Q) (w : GPm m a b) (x : GVar m a k b → S) (hc : LinearIndependent S c) :
    LinearIndependent S (gvec c w x) := by
  have hd : LinearIndependent S (c ∘ w.1) := hc.comp _ w.1.injective
  rw [Fintype.linearIndependent_iff] at hd ⊢
  intro g hg
  rw [gvec_combo] at hg
  have h1 := hd _ hg
  have hlow : ∀ l : Fin m, (l : ℕ) < k → g l = 0 := fun l hl => by
    have hs : ∑ l', gcellOff x l l' * g l' = 0 :=
      Finset.sum_eq_zero fun l' _ => by rw [gcellOff_of_lt x l' hl, zero_mul]
    have := h1 l
    rwa [hs, add_zero] at this
  intro l
  by_cases hl : (l : ℕ) < k
  · exact hlow l hl
  · have hs : ∑ l', gcellOff x l l' * g l' = 0 := Finset.sum_eq_zero fun l' _ => by
      by_cases h : gcellOff x l l' = 0
      · rw [h, zero_mul]
      · rw [hlow l' (gcellOff_ne x h).2.1, mul_zero]
    have := h1 l
    rwa [hs, add_zero] at this

theorem gvec_span (c : Fin m → Q) (w : GPm m a b) (x : GVar m a k b → S) :
    Submodule.span S (Set.range (gvec c w x)) = Submodule.span S (Set.range c) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    rw [SetLike.mem_coe, gvec_eq_add]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨_, rfl⟩)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨l, rfl⟩ := w.1.surjective j
    rw [SetLike.mem_coe, gvec_inv c w x l]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

theorem gvec_initSpan (c : Fin m → Q) (w : GPm m a b) (x : GVar m a k b → S) {e : ℕ} (he : e ≤ a ∨ b ≤ e) :
    initSpan S (gvec c w x) e = initSpan S c e := by
  unfold GlobalTheory.FlagMod.initSpan
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨j, hj, rfl⟩
    have hj : (j : ℕ) < e := hj
    rw [SetLike.mem_coe, gvec_eq_add]
    refine Submodule.add_mem _ (Submodule.subset_span ⟨w.1 j, (gpm_lt_iff w he j).2 hj, rfl⟩)
      (Submodule.sum_mem _ fun i _ => ?_)
    by_cases h : gcellOff x i j = 0
    · rw [h, zero_smul]
      exact Submodule.zero_mem _
    · have := gcellOff_ne x h
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w.1 i, (gpm_lt_iff w he i).2 (by omega), rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨j, hj, rfl⟩
    have hj : (j : ℕ) < e := hj
    obtain ⟨l, rfl⟩ := w.1.surjective j
    have hl : (l : ℕ) < e := (gpm_lt_iff w he l).1 hj
    rw [SetLike.mem_coe, gvec_inv c w x l]
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨l, hl, rfl⟩) (Submodule.sum_mem _ fun i _ => ?_)
    by_cases h : gcellOff x i l = 0
    · rw [h, zero_smul]
      exact Submodule.zero_mem _
    · have := gcellOff_ne x h
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, (show (i : ℕ) < e by omega), rfl⟩)

theorem gvec_frame : ∀ (S : Type) [CommRing S] (m a k b : ℕ) (Q : Type) [AddCommGroup Q] [Module S Q] (c : Fin m → Q)
    (w : GPm m a b) (x : GVar m a k b → S), a ≤ k → k ≤ b →
    (LinearIndependent S c → LinearIndependent S (gvec c w x)) ∧
      Submodule.span S (Set.range (gvec c w x)) = Submodule.span S (Set.range c) ∧
      ∀ e : ℕ, e ≤ a ∨ b ≤ e → initSpan S (gvec c w x) e = initSpan S c e :=
  fun _ _ _ _ _ _ _ _ _ c w x _ _ =>
    ⟨gvec_linearIndependent c w x, gvec_span c w x, fun _ he => gvec_initSpan c w x he⟩

end GlobalTheory.GrCl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExponentialModelFiberOfUniformisationExp
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_comp_hom isDerivAt0_unique)
open GlobalTheory.TrueCx.TorFrHolo (isDerivAt0_of_cart isHolTo_lift)

section Push

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {g : ℕ}
  {ty : Fin g → (E →+* ℂ)} {σ₀ : KA l →+* ℂ} (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n)
  (P : (Fu.Di i).La →+ (Fin g → ℂ))

theorem isHolTo_ex_fixed (hP : IsPeriod (Fu.Di i) ty P) : IsHolTo Set.univ fun z => (Fu.ex i P z).left := by
  have h1 := (Fu.hol i 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  exact GlobalTheory.LocLift.isHolTo_comp h1 isOpen_univ (β := fun z => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
    fun _ _ => ⟨trivial, trivial⟩

theorem isHolTo_liftEx (hP : IsPeriod (Fu.Di i) ty P)
    (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) :
    IsHolTo Set.univ fun z => liftEx Z Fu y i P hu z ≫ Z.m.φ := by
  have h1 := (Fu.hol i 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  have h2 := isHolTo_lift Z.m0.toSABMap.cart.1 isOpen_univ (fun _ z => (Fu.ex i P z).left) (fun _ => y) h1
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.ThetaHol.isHolTo_const y) (fun _ z => by rw [Over.w (Fu.ex i P z), ← hu]; rfl)
  have h3 := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h2 Z.m.φ
  exact GlobalTheory.LocLift.isHolTo_comp h3 isOpen_univ (β := fun z => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
    fun _ _ => ⟨trivial, trivial⟩

theorem isDerivAt0_liftEx (hP : IsPeriod (Fu.Di i) ty P)
    (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left}
    (hv : v ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y)
    (hd : IsDerivAt0 (fun z => (Fu.ex i P z).left) w (v ≫ Z.m0.toSABMap.φ)) :
    IsDerivAt0 (liftEx Z Fu y i P hu) w v :=
  isDerivAt0_of_cart Z.m0.toSABMap.cart.1 y (fun z => liftEx_snd Z Fu y i P hu z)
    (by simpa only [liftEx_fst] using isHolTo_ex_fixed Fu i P hP) hv
    (by simpa only [liftEx_fst] using hd)

theorem isDerivAt0_ex_of_push (hP : IsPeriod (Fu.Di i) ty P)
    (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left}
    (hv : v ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y)
    (hd : IsDerivAt0 (fun z => liftEx Z Fu y i P hu z ≫ Z.m.φ) w (v ≫ Z.m.φ)) :
    IsDerivAt0 (fun z => (Fu.ex i P z).left) w (v ≫ Z.m0.toSABMap.φ) := by
  have h := isDerivAt0_comp_hom (isDerivAt0_of_cart Z.m.cart.1 y (fun z => liftEx_snd Z Fu y i P hu z)
    (isHolTo_liftEx Z Fu y i P hP hu) hv hd) Z.m0.toSABMap.φ
  simpa only [liftEx_fst] using h

end Push

theorem isExpAt_pushEx : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → IsExpAt Z.t p (pushEx Z Fu y i P p hu hp) := by
  intro E _ _ _ H Dw l Xo c O _ β Z g ty σ₀ Fu y i P p hu hp hP
  subst hp
  obtain ⟨t1, t2, t3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo σ₀ g ty Fu i P hP
  refine ⟨fun a b => ?_, fun w => ?_, fun v hv => ?_⟩
  · let L : (Fin g → ℂ) → (Over.mk y ⟶ Z.oF.t.G) := fun z =>
      Over.homMk (liftEx Z Fu y i P hu z) (liftEx_snd Z Fu y i P hu z)
    have hL : (L (a + b)).left = (L a * L b).left := by
      refine Z.m0.toSABMap.cart.1.hom_ext ?_ ?_
      · have e1 := Z.m0.toSABMap.cart.2 (Over.mk y) (L a) (L b) (pushPt Z.m0.toSABMap.cart.1.w (L a))
          (pushPt Z.m0.toSABMap.cart.1.w (L b)) rfl rfl
        refine Eq.trans ?_ e1
        refine (liftEx_fst Z Fu y i P hu (a + b)).trans ?_
        rw [Fu.ex_add i P hP]
        exact mul_left_congr hu _ _ _ _ (liftEx_fst Z Fu y i P hu a).symm (liftEx_fst Z Fu y i P hu b).symm
      · rw [Over.w, Over.w]
    refine Over.OverMorphism.ext ?_
    have e2 := Z.m.cart.2 (Over.mk y) (L a) (L b) (pushEx Z Fu y i P _ hu rfl a) (pushEx Z Fu y i P _ hu rfl b) rfl rfl
    refine Eq.trans ?_ e2.symm
    exact congrArg (· ≫ Z.m.φ) hL
  · obtain ⟨v, hv, -⟩ := t2 w
    have ht := t1 w v hv
    obtain ⟨v', k1, rfl⟩ := GlobalTheory.ShFam.OpenReg.exists_lift Z.m0.toSABMap (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
      (by rw [ht.1, hu, Category.assoc])
    refine ⟨v' ≫ Z.m.φ, ⟨(GlobalTheory.ShFam.OpenReg.tan_iff Z.m rfl k1).2
      ((GlobalTheory.ShFam.OpenReg.tan_iff Z.m0.toSABMap hu.symm k1).1 ht),
      isDerivAt0_comp_hom (isDerivAt0_liftEx Z Fu y i P hP hu k1 hv) Z.m.φ⟩, fun v₂ hv₂ => ?_⟩
    exact isDerivAt0_unique hv₂.2 (isDerivAt0_comp_hom (isDerivAt0_liftEx Z Fu y i P hP hu k1 hv) Z.m.φ)
  · obtain ⟨v', k1, rfl⟩ := GlobalTheory.ShFam.OpenReg.exists_lift Z.m (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
      (by rw [hv.1, Category.assoc])
    have h1 := (GlobalTheory.ShFam.OpenReg.tan_iff Z.m rfl k1).1 hv
    have h2 := (GlobalTheory.ShFam.OpenReg.tan_iff Z.m0.toSABMap hu.symm k1).2 h1
    obtain ⟨w, hw, hw'⟩ := t3 _ h2
    exact ⟨w, isDerivAt0_comp_hom (isDerivAt0_liftEx Z Fu y i P hP hu k1 hw) Z.m.φ,
      fun w' h' => hw' w' (isDerivAt0_ex_of_push Z Fu y i P hP hu k1 h')⟩

end GlobalTheory.ShFam.Hor.LogCh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemCommonRefinement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

theorem GlobalTheory.ShFam.Pad.exists_dominating_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → (N2 Y ∧ ∀ i, (Y i).SplitFibres ∧ (Y i).N3 ∧ (Y i).N4) → ∀ (n : ℕ) (Z : Fin (n + 1) → Mdl Y i₀), (∀ a, (Z a).i = (Z 0).i ∧ (Z a).ty = (Z 0).ty) → ∃ Z' : Mdl Y i₀, Z'.i = (Z 0).i ∧ Z'.ty = (Z 0).ty ∧ ∀ a, ∃ f : Z'.X ⟶ (Z a).X, IsMap Z' (Z a) f :=
  fun E _ _ _ H Dw Xo p W Y i₀ hp hW hN n Z hZ =>
    GlobalTheory.LocM.MapComp.exists_dominating (fun Z₁ Z₂ h => ⟨_, GlobalTheory.T.correspondence_diagonal E H Dw Xo p W hp hW Y i₀ hN.1 Z₁ Z₂ h⟩) n Z hZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRadicalOfHolomorphicRatioTendstoStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_radical_of_holomorphic_ratio_tendsto : ∀ (F A : Type) [Field F] [CommRing A] [IsDomain A] [Algebra F A], Algebra.Smooth F A → ∀ (σ : F →+* ℂ) (p a : A) (m : ℕ), p ≠ 0 → (∀ (ψ : ℂ → (A →+* ℂ)) (r : ℝ), IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, (ψ u).comp (algebraMap F A) = σ) → ψ 0 p = 0 → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u p ≠ 0) → Tendsto (fun u => ψ u a / ψ u (p ^ m)) (𝓝[≠] 0) (𝓝 0)) → ∃ b : A, a = b * p ^ m ∧ b ∈ (Ideal.span {p}).radical := by
  first | exact @GlobalTheory.ShFam.BdArc.exists_eq_mul_pow_of_tendsto_zero | exact GlobalTheory.ShFam.BdArc.exists_eq_mul_pow_of_tendsto_zero | (intros; apply GlobalTheory.ShFam.BdArc.exists_eq_mul_pow_of_tendsto_zero <;> assumption)
end

