import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0308
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0511
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0514
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Formalism.LocalToGlobal.Columns.ColumnsProofs.HeckeFieldSplit
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFormsIsometryColumnPairingAtState
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.EmtTw
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 2000000

theorem inner_per_e {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} (P : Pre2 K w) (a : w.C.Tup)
    (y y' : Df.MtCx w.I a) : inner ℂ (P.q.per.e a y) (P.q.per.e a y') = Df.cSum w.I P.hX a y y' := by
  let jA := (P.q.t.tA true a).j
  have hF := (P.q.t.tA true a).forms
  let eS : (P.q.p.sA true a).A.T →ₗ[ℂ] Df.MtCx w.I a := (P.q.per.e a).symm.toLinearMap
  let j' := eS.comp jA
  have hspan : Submodule.span ℂ (Set.range j') = ⊤ := by
    have h0 : Submodule.span ℂ (Set.range jA) = ⊤ := by
      rw [← ColTie.span_single_eq]; exact hF.span
    have h1 : Set.range j' = eS '' Set.range jA := by
      rw [← Set.range_comp]; rfl
    rw [h1, Submodule.span_image, h0, Submodule.map_top]
    exact LinearMap.range_eq_top.2 (P.q.per.e a).symm.surjective
  obtain ⟨k, hk⟩ := Df.exists_embLL_im_ne (B := B) P.hX
  refine Df.inner_eq_of_norm_sq _ j' hspan k hk (P.q.per.e a).toLinearMap (Df.cSum w.I P.hX a) (fun m => ?_) y y'
  obtain ⟨x, hx, hjx⟩ := P.q.per.crd a m
  have hj' : j' m = Df.toCx w.I P.hX a x := by
    show (P.q.per.e a).symm (jA m) = _
    rw [show jA m = _ from hjx, LinearEquiv.symm_apply_apply]
  have he : (P.q.per.e a).toLinearMap (j' m) = jA m := by
    show (P.q.per.e a) ((P.q.per.e a).symm (jA m)) = _
    rw [LinearEquiv.apply_symm_apply]
  have hL := GlobalTheory.T.classSum_complexRowForm_columnsLevel_eq (w.st P.Z₀) w.I P.hX P.z.Xg P.z.tr a m x hx
  have hI := hF.inner m m
  rw [he, hj', hL]
  calc ((‖jA m‖ ^ 2 : ℝ) : ℂ) = inner ℂ (jA m) (jA m) := by rw [inner_self_eq_norm_sq_to_K]; norm_cast
    _ = _ := hI

theorem eMtTw_isometry_state : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), ∀ u (a : (w.D x.o.Z).what₂.Tup), a ≠ (w.D x.o.Z).what₂.mu0 → ∀ F G,
      inner ℂ ((w.D x.o.Z).eMtTw u a F) ((w.D x.o.Z).eMtTw u a G) = TC.ipMt w.I w.l u a F G := by
  intro K B f T w _ _ _ P x _ u a _ F G
  change inner ℂ (P.q.e.eT u a F) (P.q.e.eT u a G) = _
  have key : ∀ F : (TC.per w.I w.l u a).Mt, Df.SameForm w.I w.l u a ((P.q.per.e a).symm (P.q.e.eT u a F)) F := fun F => by
    have h := P.q.per.tw u a ((P.q.per.e a).symm (P.q.e.eT u a F))
    rw [LinearEquiv.apply_symm_apply] at h
    exact (congrArg (Df.SameForm w.I w.l u a ((P.q.per.e a).symm (P.q.e.eT u a F))) ((P.q.e.eT u a).symm_apply_apply F)).mp h
  have h1 : ∀ F : (TC.per w.I w.l u a).Mt, P.q.e.eT u a F = P.q.per.e a ((P.q.per.e a).symm (P.q.e.eT u a F)) := fun F =>
    ((P.q.per.e a).apply_symm_apply _).symm
  rw [h1 F, h1 G, inner_per_e P a, GlobalTheory.T.rowFormMetric_eq_classSumMetric w.I w.ok w.pins w.l P.hX x.o.Z u a F G _ _ (key F) (key G)]

end GlobalTheory.Mem.R3.Rw.EmtTw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProvisionalRowsFurtherCompatibilitiesAtState
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Ties

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] {O : Type} [CommRing O] {φ : O →+* ℂ} {σ : K →+* ℂ}

def castEq {m m' : Mat1 K G} (h : m = m') : (Fin m'.n → K) ≃ₗ[K] (Fin m.n → K) := h ▸ LinearEquiv.refl K _

theorem forms_cast {m m' : Mat1 K G} {s : Sp1 O φ G} (h : m = m') (t : Tie1 σ m s) :
    FormsTie σ (t.j.comp (castEq h).toLinearMap) m'.H m'.E s.e := by
  subst h; exact t.forms

theorem lat_cast {m m' : Mat1 K G} {s : Sp1 O φ G} (h : m = m') (t : Tie1 σ m s) :
    OLatTie σ s.lat (t.j.comp (castEq h).toLinearMap) m'.N := by
  subst h; exact t.latT

theorem cen_cast {m m' : Mat1 K G} {s : Sp1 O φ G} (h : m = m') (t : Tie1 σ m s)
    (z : Subalgebra.center ℂ (MonoidAlgebra ℂ G)) (a : MonoidAlgebra K G)
    (ha : ∀ g, σ (a.coeff g) = (z : MonoidAlgebra ℂ G).coeff g) (x) :
    s.act z (t.j (castEq h x)) = t.j (castEq h ((m'.op a).mulVec x)) := by
  subst h; exact t.cen z a ha x

theorem sameOn_tie {τ : Type} (mA : τ → Mat1 K G) (s : τ → Sp1 O φ G) (tA : ∀ μ, Tie1 σ (mA μ) (s μ)) {μ μ' : τ} (hμ : μ = μ')
    {m' : Mat1 K G} (h : mA μ' = m') (j : (Fin m'.n → K) →ₛₗ[σ] (s μ).A.T) (hj : HEq j ((tA μ').cast h).j) :
    SameOn (tA μ).j j := by
  subst hμ; subst h
  obtain rfl : j = (tA μ).j := eq_of_heq hj
  exact ⟨rfl, fun x x' hx => congrArg _ (funext fun a => hx a a rfl)⟩

theorem sameOn_cast {τ : Type} (mL : τ → Mat1 K G) {μ μ' : τ} (hμ : μ = μ') {m' m'' : Mat1 K G} (h : mL μ = m') (h' : mL μ' = m'')
    (j : (Fin m''.n → K) → Fin (mL μ).n → K) (hj : ∀ x, HEq (j x) x) : SameOn (castEq h) j := by
  subst hμ; subst h; subst h'
  exact ⟨rfl, fun x x' hx => (funext fun a => hx a a rfl).trans (eq_of_heq (hj x')).symm⟩

end Gen

theorem stdIso_dat {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : TwDat X.B}
    {Wt : Set X.B.places.Pl} (z : Dat X I hX T Wt) : StdIso X px (z.R.eG.trans z.cG) := by
  obtain ⟨plg, iso, h1, -, -, h4⟩ := z.pins.keep.grp
  have hP : z.R.Pg = (X.B.primes px).vGs := z.lev.Pg
  refine ⟨plg.trans (Equiv.subtypeEquivRight fun x => by rw [hP]; exact Iff.rfl), iso, h1, fun g kv => ?_⟩
  exact (z.idG g (plg kv).1 _ (plg kv).2).symm.trans (h4 g kv)

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

set_option maxHeartbeats 2000000 in

theorem mLU_eq (Z Z' : w.Lt) (hX : B.fields.Ok) {Xg Xg' : Finset (Gc B w.px → B.LL)} {tr tr' : TrI B w.px} (h1 : Xg' = Xg)
    (h2 : tr' = tr) (a : w.I.ι) (i : Fin (w.st Z').toD7.R.m) :
    HEq (mLU (w.st Z) w.I hX Xg tr a ((i : ℕ) + 1))
      (lMat (D := (w.st Z').toD7) (famR (w.st Z') w.I hX Set.univ Xg' tr').A (lev0 w.I) (chr0 w.I) i (tAll w.I a)) := by
  subst h1; subst h2
  have e : mLU (w.st Z') w.I hX Xg' tr' a ((i : ℕ) + 1) =
      lMat (D := (w.st Z').toD7) (famR (w.st Z') w.I hX Set.univ Xg' tr').A (lev0 w.I) (chr0 w.I) i (tAll w.I a) := by
    have hi : 1 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ (w.st Z').toD7.R.m := ⟨by omega, i.2⟩
    unfold mLU
    rw [dif_pos hi]
    exact (by with_unfolding_all exact ((Eq.refl (lMat (D := (w.st Z').toD7) (famR (w.st Z') w.I hX Set.univ Xg' tr').A (lev0 w.I) (chr0 w.I) i (tAll w.I a))) :))
  exact (by with_unfolding_all exact ((heq_of_eq e) :))

set_option maxHeartbeats 2000000 in

theorem crd_eq (Z : w.Lt) (hX : B.fields.Ok) {Xg Xg' : Finset (Gc B w.px → B.LL)} {tr tr' : TrI B w.px} (h1 : Xg' = Xg)
    (h2 : tr' = tr) (a : w.I.ι) (M : Hs) (e : Df.MtCx w.I a ≃ₗ[ℂ] M.T)
    (j : (Fin (mAU (w.st Z) w.I hX Xg tr true a).n → (w.st Z).toD7.what₂.LL) →ₛₗ[(w.st Z).toD7.what₂.embLL] M.T)
    (j' : (Fin (mAU (w.st Z) w.I hX Xg' tr' true a).n → (w.st Z).toD7.what₂.LL) →ₛₗ[(w.st Z).toD7.what₂.embLL] M.T) (hj : HEq j' j)
    (h : ∀ y, IsCrd w.I hX a e
      (rowForm (D := (w.st Z).toD7) (famR (w.st Z) w.I hX Set.univ Xg tr).A (lev1 w.I) (chr1 w.I) (tAll w.I a) y) (j y)) (y) :
    IsCrd w.I hX a e
      (rowForm (D := (w.st Z).toD7) (famR (w.st Z) w.I hX Set.univ Xg' tr').A (lev1 w.I) (chr1 w.I) (tAll w.I a) y) (j' y) := by
  subst h1; subst h2
  obtain rfl : j' = j := eq_of_heq hj
  exact h y

theorem algebra_eq {k L : Type} [Field k] [Field L] (σ : L →+* ℂ) (v : k → ℂ) (i i' : Algebra k L)
    (hi : ∀ y, σ (@algebraMap k L _ _ i y) = v y) (hi' : ∀ y, σ (@algebraMap k L _ _ i' y) = v y) : i = i' :=
  Algebra.algebra_ext _ _ fun y => σ.injective ((hi y).trans (hi' y).symm)

set_option maxHeartbeats 4000000 in

theorem brgStd_copy0 (Z Z' : w.Lt) (hX : B.fields.Ok) (U : Set w.I.ι) (Xg : Finset (Gc B w.px → B.LL)) (tr : TrI B w.px)
    (k : Type) [Field k] [NumberField k] (v : k → ℂ)
    (i : Algebra k (w.st Z).toD7.what₂.LL) (i' : Algebra k (w.st Z').toD7.what₂.LL)
    (hi : ∀ y : k, (w.st Z).toD7.what₂.embLL (algebraMap k (w.st Z).toD7.what₂.LL y) = v y)
    (hi' : ∀ y : k, (w.st Z').toD7.what₂.embLL (algebraMap k (w.st Z').toD7.what₂.LL y) = v y)
    (R : RealDat3 (w.st Z).toD7 (famR (w.st Z) w.I hX U Xg tr) k)
    (R' : RealDat3 (w.st Z').toD7 (famR (w.st Z') w.I hX U Xg tr) k)
    (hR : HEq R' (real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ (iK := i) R))
    (h : BrgStd (w.st Z) w.I hX U Xg tr R.toRealDat) : BrgStd (w.st Z') w.I hX U Xg tr R'.toRealDat := by
  have ei : ((by with_unfolding_all exact (i :))) = i' := algebra_eq (w.st Z').toD7.what₂.embLL v _ i' ((by with_unfolding_all exact (hi :))) hi'
  subst ei
  have eR : ((by with_unfolding_all exact ((real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ (iK := i) R) :))) = R' :=
    eq_of_heq ((by with_unfolding_all exact (hR.symm :)))
  subst eR
  exact (by with_unfolding_all exact (h :))

set_option maxHeartbeats 4000000 in

theorem brgStd_copy (Z Z' : w.Lt) (hX : B.fields.Ok) (U : Set w.I.ι) {Xg Xg' : Finset (Gc B w.px → B.LL)} {tr tr' : TrI B w.px}
    (h1 : Xg' = Xg) (h2 : tr' = tr) (c : Formalism.L2.Pj.CoreJ (w.st Z).toD7) (c' : Formalism.L2.Pj.CoreJ (w.st Z').toD7)
    (i : Algebra c.Q.c.F (w.st Z).toD7.what₂.LL) (i' : Algebra c'.Q.c.F (w.st Z').toD7.what₂.LL)
    (hi : ∀ y : c.Q.c.F, B.embLL (algebraMap c.Q.c.F (w.st Z).toD7.what₂.LL y) = (y : ℂ))
    (hi' : ∀ y : c'.Q.c.F, B.embLL (algebraMap c'.Q.c.F (w.st Z').toD7.what₂.LL y) = (y : ℂ))
    (R : RealDat3 (w.st Z).toD7 (famR (w.st Z) w.I hX U Xg tr) c.Q.c.F)
    (R' : RealDat3 (w.st Z').toD7 (famR (w.st Z') w.I hX U Xg' tr') c'.Q.c.F)
    (hc : HEq c' (coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ c))
    (hR : HEq R' (real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ (iK := i) R))
    (h : BrgStd (w.st Z) w.I hX U Xg tr R.toRealDat) : BrgStd (w.st Z') w.I hX U Xg' tr' R'.toRealDat := by
  subst h1; subst h2
  have ec : ((by with_unfolding_all exact ((coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ c) :))) = c' := (by with_unfolding_all exact ((eq_of_heq hc.symm) :))
  subst ec
  exact (by with_unfolding_all exact ((brgStd_copy0 Z Z' hX U Xg' tr' c.Q.c.F (fun y => (y : ℂ)) i ((i')) ((hi)) ((hi')) R ((R')) ((hR)) h) : _))

variable {Z₀ : w.Lt} {hX : B.fields.Ok} {Wt : Set B.places.Pl} {z₀ : Dat (w.st Z₀) w.I hX T Wt} {q : RowPk w z₀} {o : q.Over}

set_option maxHeartbeats 2000000 in

theorem mL_all (m : Moved o) (i : Fin (w.st o.Z).toD7.R.m) (a : w.I.ι) :
    q.p.mL a ((i : ℕ) + 1) =
      lMat (D := (w.st o.Z).toD7) (famR (w.st o.Z) w.I hX Set.univ m.z.Xg m.z.tr).A (lev0 w.I) (chr0 w.I) i (tAll w.I a) := by
  have h := mLU_eq Z₀ o.Z hX m.Xg m.tr a i
  have h' := q.mL a ((i : ℕ) + 1)
  exact (by with_unfolding_all exact ((eq_of_heq ((heq_of_eq h').trans h)) :))

set_option maxHeartbeats 4000000 in

def allT (h : o.Fits) (m : Moved o) (s : Side0 o) :
    AllT (w.st o.Z).toD7 (famR (w.st o.Z) w.I hX Set.univ m.z.Xg m.z.tr).A (lev0 w.I) (chr0 w.I) (lev1 w.I) (chr1 w.I) s.p0
      (tAll w.I) (m.z.R.eG.trans m.z.cG) where
  jA μ := (by with_unfolding_all exact ((m.t.tA true μ).j :))
  jA0 μ := (by with_unfolding_all exact ((m.t.tA false μ).j :))
  eMt i μ := (by with_unfolding_all exact ((castEq (mL_all m i μ)) :))
  formsA μ := (by with_unfolding_all exact ((m.t.tA true μ).forms :))
  latA μ := (by with_unfolding_all exact ((m.t.tA true μ).latT :))
  formsAtBottomLevel μ := (by with_unfolding_all exact ((m.t.tA false μ).forms :))
  latA0 μ := (by with_unfolding_all exact ((m.t.tA false μ).latT :))
  formsL i μ := (by with_unfolding_all exact ((forms_cast (mL_all m i μ) (q.p.tL μ ((i : ℕ) + 1))) :))
  latL i μ := (by with_unfolding_all exact ((lat_cast (mL_all m i μ) (q.p.tL μ ((i : ℕ) + 1))) :))
  cen μ z a ha := by
    have hs := stdIso_dat m.z
    have hc := h.cen _ hs
    let z' : Subalgebra.center ℂ (MonoidAlgebra ℂ (Gc B w.px)) := Bare.cenPull (m.z.R.eG.trans m.z.cG) z
    have hz := Bare.coeff_cenPull (m.z.R.eG.trans m.z.cG) z
    have ha' : ∀ g, (w.st o.Z).toD7.what₂.embLL (a.coeff g) = (z' : MonoidAlgebra ℂ (Gc B w.px)).coeff g :=
      fun g => (ha g).trans (hz g).symm
    refine ⟨fun x => ?_, fun x => ?_, fun i x => ?_⟩
    · have h1 := hc.amb μ ((by with_unfolding_all exact (z :))) z' ((by with_unfolding_all exact (hz :))) ((m.t.tA true μ).j ((by with_unfolding_all exact (x :))))
      have h2 := (m.t.tA true μ).cen z' a ha' ((by with_unfolding_all exact (x :)))
      exact (by with_unfolding_all exact ((eq_of_heq ((heq_of_eq h1).trans (heq_of_eq h2))) :))
    · have h1 := s.is _ hs μ ((by with_unfolding_all exact (z :))) z' ((by with_unfolding_all exact (hz :))) ((m.t.tA false μ).j ((by with_unfolding_all exact (x :))))
      have h2 := (m.t.tA false μ).cen z' a ha' ((by with_unfolding_all exact (x :)))
      exact (by with_unfolding_all exact ((eq_of_heq ((heq_of_eq h1).trans (heq_of_eq h2))) :))
    · have h1 := hc.mt μ ((i : ℕ) + 1) ((by with_unfolding_all exact (z :))) z' ((by with_unfolding_all exact (hz :))) ((q.p.tL μ ((i : ℕ) + 1)).j (castEq (mL_all m i μ) ((by with_unfolding_all exact (x :)))))
      have h2 := cen_cast (mL_all m i μ) (q.p.tL μ ((i : ℕ) + 1)) z' ((by with_unfolding_all exact (a :))) ((by with_unfolding_all exact (ha' :))) ((by with_unfolding_all exact (x :)))
      exact (by with_unfolding_all exact ((h1.trans h2) :))

set_option maxHeartbeats 2000000 in

theorem jA_same (h : o.Fits) {m : Moved o} {s : Side0 o} (r : ReadPk m s) (t) :
    SameOn ((allT h m s).jA (r.Y.tup t)) (r.Y.jA t) := (by with_unfolding_all exact ((sameOn_tie (mAU (w.st o.Z) w.I hX m.z.Xg m.z.tr true) (q.p.sA true) (m.t.tA true) (congrFun r.tup t) (m.t.hA true t)
    (((r.Y.jA t))) (((r.jA t)))) : _))

set_option maxHeartbeats 2000000 in

theorem rowReading_baseLevel_sameOn_allTuples (h : o.Fits) {m : Moved o} {s : Side0 o} (r : ReadPk m s) (t) :
    SameOn ((allT h m s).jA0 (r.Y.tup t)) (r.Y.jA0 t) := (by with_unfolding_all exact ((sameOn_tie (mAU (w.st o.Z) w.I hX m.z.Xg m.z.tr false) (q.p.sA false) (m.t.tA false) (congrFun r.tup t) (m.t.hA false t)
    (((r.Y.jA0 t))) (((r.jA0 t)))) : _))

set_option maxHeartbeats 2000000 in

theorem eMt_same (h : o.Fits) {m : Moved o} {s : Side0 o} (r : ReadPk m s) (i : Fin (w.st o.Z).toD7.R.m) (t) :
    SameOn ((allT h m s).eMt i (r.Y.tup t)) (r.Y.eMt i t) := (by with_unfolding_all exact ((sameOn_cast (fun a => q.p.mL a ((i : ℕ) + 1)) (congrFun r.tup t) (mL_all m i (r.Y.tup t)) (m.t.hL i t)
    (fun x => (by with_unfolding_all exact ((r.Y.eMt i t ((x))) : _))) ((by with_unfolding_all exact ((r.eMt i t) :)))) :))

set_option maxHeartbeats 2000000 in

theorem crd_moved (h : o.Fits) (m : Moved o) (s : Side0 o) (a : w.C.Tup) (y) :
    IsCrd w.I hX a (q.per.e a)
      (rowForm (D := (w.st o.Z).toD7) (famR (w.st o.Z) w.I hX Set.univ m.z.Xg m.z.tr).A (lev1 w.I) (chr1 w.I) (tAll w.I a) y)
      ((allT h m s).jA a y) := (by with_unfolding_all exact ((crd_eq Z₀ hX m.Xg m.tr a (q.p.sA true a).A (q.per.e a) (q.t.tA true a).j (((m.t.tA true a).j)) (((m.tA true a)))
    (q.per.crd a) ((y))) : _))

set_option maxHeartbeats 2000000 in

theorem io_junk {m : Moved o} {s : Side0 o} (r : ReadPk m s) (μ : (w.D o.Z).what₂.Tup) (h : ¬ Used0 (w.D o.Z) μ) (b : Bool) (j : ℕ) :
    (q.p.ch b).io μ j = 0 := by
  refine (m.t.ch b).junk μ (fun hu => h ?_) j
  rcases hu with hu | ⟨v, hu⟩
  · exact Or.inl hu
  · exact Or.inr ⟨v, hu.trans ((congrFun r.tup _).symm.trans (r.Y.muAt v).symm)⟩

set_option maxHeartbeats 2000000 in

theorem std_moved {m : Moved o} (c : m.Copy) (h : z₀.Std) : m.z.Std :=
  brgStd_copy Z₀ o.Z hX _ m.Xg m.tr z₀.core m.z.core z₀.alg m.z.alg z₀.alg_eq m.z.alg_eq z₀.R m.z.R ((by with_unfolding_all exact (c.core :))) ((by with_unfolding_all exact (c.R :))) h

set_option maxHeartbeats 4000000 in

theorem rxs_of_state : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre → Forced K B T →
    pinAnd HasPk K B f T w → ∀ (P : Pre2 K w) (x : St P) (hη : ∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v), ∀ t : RowsT K w x.o.Z P.Wt x.s.p0, t.r = x.rowsAre hη → Nonempty (RXs t) := by
  intro K B f T w _ _ _ P x hη t ht
  have key : ∀ (r : R3.RowsAre (w.st x.o.Z) w.I P.hX T P.Wt (Equiv.refl _) x.s.p0), x.rowsAre hη = r →
      ∀ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12,
        Nonempty (RXs (⟨P.hX, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ : RowsT K w x.o.Z P.Wt x.s.p0)) := ?_
  · exact key t.r ht.symm t.exAt t.inGeo t.grpAt t.grp t.mu t.exact t.untw t.emt0 t.emt t.etaF t.rowInt t.idx
  intro r hr
  induction hr
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  have hc := x.m.core P.core
  exact ⟨{
    all := (by with_unfolding_all exact ((allT x.fits x.m x.s) :))
    jA_use := (by with_unfolding_all exact ((jA_same x.fits x.r) :))
    movedReadingSameMaps_baseReading_agrees := (by with_unfolding_all exact ((rowReading_baseLevel_sameOn_allTuples x.fits x.r) :))
    eMt_use := (by with_unfolding_all exact ((eMt_same x.fits x.r) :))
    e := P.q.per.e
    eMt0 := P.q.per.ref
    eMtTw := P.q.per.tw
    crd := (by with_unfolding_all exact ((crd_moved x.fits x.m x.s) :))
    io := fun μ j h => ⟨io_junk x.r μ h true j, io_junk x.r μ h false j⟩
    sha := P.q.sha
    laws := (by with_unfolding_all exact (hc.1 :))
    canon := (by with_unfolding_all exact (hc.2.1 :))
    rank := (by with_unfolding_all exact (hc.2.2.1 :))
    pb := (by with_unfolding_all exact (hc.2.2.2 :))
    std := (by with_unfolding_all exact ((std_moved x.copy P.std) :)) }⟩

end GlobalTheory.Mem.R3.Rw.Ties

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleLiftFormsPassToCoeffEnlargement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Tr

theorem exists_iota_comp {K₁ K₂ : Type} [Field K₁] [Field K₂] (c₁ : K₁ →+* ℂ) (c₂ : K₂ →+* ℂ)
    (h : Set.range c₁ ⊆ Set.range c₂) : ∃ ι : K₁ →+* K₂, ∀ x, c₂ (ι x) = c₁ x := by
  have hle : c₁.range ≤ c₂.range := by
    intro y hy
    obtain ⟨x, rfl⟩ := RingHom.mem_range.1 hy
    obtain ⟨z, hz⟩ := h ⟨x, rfl⟩
    exact RingHom.mem_range.2 ⟨z, hz⟩
  let e : K₂ ≃+* c₂.range := RingEquiv.ofBijective c₂.rangeRestrict
    ⟨fun a b hab => c₂.injective (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective c₂⟩
  refine ⟨e.symm.toRingHom.comp ((Subring.inclusion hle).comp c₁.rangeRestrict), fun x => ?_⟩
  have h1 : c₂ (e.symm ⟨c₁ x, hle (RingHom.mem_range_self c₁ x)⟩) = c₁ x := by
    have := congrArg Subtype.val (e.apply_symm_apply ⟨c₁ x, hle (RingHom.mem_range_self c₁ x)⟩)
    exact this
  exact h1

abbrev baseOfColW {B : Base} {f : Fr B.toPre} {T : TwDat B} (_ : ColW B f T) : Base := B

theorem levelFamily_coefficientChange_liftRound (X : Formalism.L2.Col.Fields) {L : Type} [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L)
    (e : X.Tau → X.E →+* L) (he : ∀ τ, ι.comp (X.emb τ) = e τ) {n : ℕ} (lam : X.Tau → DomWeight n)
    {SG : Finset (HeightOneSpectrum (𝓞 X.E))} (Λ₁ : Formalism.L2.Col.LevFam X.E X.K n SG) (Λ₂ : Formalism.L2.Col.LevFam X.E L n SG)
    (hH : ∀ w, (Λ₂ w).H = (Λ₁ w).H)
    (hl : ∀ w (h₁ : ↥(Λ₁ w).H) (h₂ : ↥(Λ₂ w).H), (h₁ : GL (Fin n) (𝓞 X.E ⧸ w.1.asIdeal)) = h₂ →
      ι (((Λ₁ w).lam h₁ : X.Kˣ) : X.K) = (((Λ₂ w).lam h₂ : Lˣ) : L))
    (φ₁ : (Formalism.L2.Col.formGSD (Formalism.L2.Col.roundPk X lam fun d : Formalism.L2.Col.DecoSet X.E n ∅ SG => d.1.N) Λ₁).EqFun) :
    ∃ φ₂ : (Formalism.L2.Col.formGSD (X := ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields))
      (Formalism.L2.Col.roundPk ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields) lam
        fun d : Formalism.L2.Col.DecoSet X.E n ∅ SG => d.1.N) Λ₂).EqFun,
      ∀ d, (φ₂.1 d).1 = MvPolynomial.map ι (φ₁.1 d).1 := by
  refine ⟨⟨fun d => Formalism.L2.Col.hfsJ ι lam (φ₁.1 d), ?_⟩, fun d => rfl⟩
  intro g d
  have hg : g.2.1 ∈ Λ₁.grp := by
    intro w _
    have h' : (g.2.1 w) ∈ (Λ₂ w).H := g.2.2 w (Set.mem_univ _)
    rw [hH w] at h'
    exact h'
  have h1 : φ₁.1 (g • d) = (((Λ₁.chr ⟨g.2.1, hg⟩ : X.Kˣ)) : X.K) •
      Formalism.L2.DIV.rhoVr X.emb lam (Formalism.L2.Col.ufGL X.E n g.1) (φ₁.1 d) := φ₁.2 (g.1, ⟨g.2.1, hg⟩) d
  have he' : e = fun τ => ι.comp (X.emb τ) := funext fun τ => (he τ).symm
  subst he'
  show Formalism.L2.Col.hfsJ ι lam (φ₁.1 (g • d)) = (((Λ₂.chr g.2 : Lˣ)) : L) •
    Formalism.L2.DIV.rhoVr (fun τ => ι.comp (X.emb τ)) lam (Formalism.L2.Col.ufGL X.E n g.1) (Formalism.L2.Col.hfsJ ι lam (φ₁.1 d))
  have h2 := Formalism.L2.Col.hfs_rhoVr ι lam X.emb (Formalism.L2.Col.ufGL X.E n g.1) (φ₁.1 d)
  erw [h2, h1, Formalism.L2.Col.hfsJ_smul]
  congr 1
  rw [Formalism.L2.Col.LevFam.chr_apply, show Λ₂.chr g.2 = _ from Formalism.L2.Col.piChar_apply _ _ g.2, Units.coe_prod, Units.coe_prod, map_prod]
  exact Finset.prod_congr rfl fun w _ => hl w _ _ rfl

theorem liftRound_reidx (X : Formalism.L2.Col.Fields) {L : Type} [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L)
    (e : X.Tau → X.E →+* L) (he : ∀ τ, ι.comp (X.emb τ) = e τ) {n : ℕ} (lam : X.Tau → DomWeight n)
    {SG₁ SG₂ : Finset (HeightOneSpectrum (𝓞 X.E))} (hS : SG₂ = SG₁)
    (Λ₁ : Formalism.L2.Col.LevFam X.E X.K n SG₁) (Λ₂ : Formalism.L2.Col.LevFam X.E L n SG₂)
    (hΛ : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), Λ₂ ⟨w.1, hw⟩ = (Λ₁ w).coefMap ι)
    (c₁ : X.K →+* ℂ) (c₂ : L →+* ℂ) (hc : ∀ x, c₂ (ι x) = c₁ x) :
    Formalism.L2.Col.DecoSet X.E n ∅ SG₂ = Formalism.L2.Col.DecoSet X.E n ∅ SG₁ ∧
    ∀ φ₁ : (Formalism.L2.Col.formGSD (Formalism.L2.Col.roundPk X lam fun d : Formalism.L2.Col.DecoSet X.E n ∅ SG₁ => d.1.N) Λ₁).EqFun,
    ∃ φ₂ : (Formalism.L2.Col.formGSD (X := ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields))
      (Formalism.L2.Col.roundPk ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields) lam
        fun d : Formalism.L2.Col.DecoSet X.E n ∅ SG₂ => d.1.N) Λ₂).EqFun,
      ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map c₂ (φ₂.1 d₂).1) (MvPolynomial.map c₁ (φ₁.1 d₁).1) := by
  subst hS
  have hΛ' : Λ₂ = Λ₁.coefMap ι := funext fun w => hΛ w w.2
  subst hΛ'
  refine ⟨rfl, fun φ₁ => ?_⟩
  obtain ⟨φ₂, h⟩ := levelFamily_coefficientChange_liftRound X ι e he lam Λ₁ (Λ₁.coefMap ι) (fun w => rfl) (fun w h₁ h₂ hh => by
    have : h₁ = h₂ := Subtype.ext hh
    subst this
    rfl) φ₁
  refine ⟨φ₂, fun d₁ d₂ hd => ?_⟩
  cases hd
  rw [h, MvPolynomial.map_map]
  have hc' : c₂.comp ι = c₁ := RingHom.ext hc
  rw [hc']

theorem twistRamifiedPrimes_empty_colTuples {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (W : Set B.places.Pl) :
    Formalism.L2.Col.QE w.I.sel ((mu0F (X := B.fields) (tuOf w.I (usedOf w.I T W))).1 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := by
  have e : Formalism.L2.Col.QE w.I.sel (w.I.tup w.I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty w.I
  rw [w.I.trueColumn_tuple_trivial_eq_one] at e
  exact e

theorem rowLevelPrimes_colTuples_eq_vGs {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (W : Set B.places.Pl) :
    Formalism.L2.Col.rowSG (B.primes w.px) w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T W))).1 = (B.primes w.px).vGs := by
  show Formalism.L2.Col.uSG _ _ = _
  rw [twistRamifiedPrimes_empty_colTuples w W]
  ext x
  simp

theorem glue_inv_coefMap_of_empty {E K L : Type} [Field E] [NumberField E] [Field K] [Field L] (ι : K →+* L) {n : ℕ}
    {SG₁ Q₁ SG₂ Q₂ : Finset (HeightOneSpectrum (𝓞 E))} (hQ₁ : Q₁ = ∅) (hQ₂ : Q₂ = ∅)
    (A₁ : Formalism.L2.Col.LevFam E K n SG₁) (B₁ : Formalism.L2.Col.LevFam E K n Q₁)
    (A₂ : Formalism.L2.Col.LevFam E L n SG₂) (B₂ : Formalism.L2.Col.LevFam E L n Q₂)
    (hA : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), A₂ ⟨w.1, hw⟩ = (A₁ w).coefMap ι) :
    ∀ (w : ↥(Formalism.L2.Col.uSG SG₁ Q₁)) (hw : w.1 ∈ Formalism.L2.Col.uSG SG₂ Q₂),
      (A₂.glue B₂).inv ⟨w.1, hw⟩ = ((A₁.glue B₁).inv w).coefMap ι := by
  intro w hw
  have h1 : w.1 ∈ SG₁ := by
    have := w.2
    simp only [Formalism.L2.Col.uSG, hQ₁, Finset.union_empty] at this
    exact this
  have h2 : w.1 ∈ SG₂ := by
    have := hw
    simp only [Formalism.L2.Col.uSG, hQ₂, Finset.union_empty] at this
    exact this
  show ((A₂.glue B₂) ⟨w.1, hw⟩).inv = (((A₁.glue B₁) w).inv).coefMap ι
  rw [Formalism.L2.Col.LevFam.glue_of_mem _ _ _ h2, Formalism.L2.Col.LevFam.glue_of_mem _ _ _ h1, ← Formalism.L2.Col.Lev.coefMap_inv,
    hA ⟨w.1, h1⟩ h2]

theorem levKV_coefMap_of {E K L : Type} [Field E] [NumberField E] [Field K] [Field L] (ι : K →+* L) {m : ℕ}
    (w : HeightOneSpectrum (𝓞 E)) (χ₁ : Fin m → (𝓞 E ⧸ w.asIdeal)ˣ →* Kˣ) (χ₂ : Fin m → (𝓞 E ⧸ w.asIdeal)ˣ →* Lˣ)
    (h : ∀ s c, ((χ₂ s c : Lˣ) : L) = ι ((χ₁ s c : Kˣ) : K)) (nV r t s : ℕ) :
    (⟨Formalism.L2.Col.HKV (𝓞 E ⧸ w.asIdeal) nV r t, Formalism.L2.Col.lamKV (Formalism.L2.Col.extChi χ₂ s) nV r t⟩ :
        Formalism.L2.Col.Lev (𝓞 E ⧸ w.asIdeal) L nV) =
      Formalism.L2.Col.Lev.coefMap ι ⟨Formalism.L2.Col.HKV (𝓞 E ⧸ w.asIdeal) nV r t, Formalism.L2.Col.lamKV (Formalism.L2.Col.extChi χ₁ s) nV r t⟩ := by
  have hχ : χ₂ = fun s => (Units.map ι.toMonoidHom).comp (χ₁ s) :=
    funext fun s => MonoidHom.ext fun c => Units.ext (h s c)
  subst hχ
  have h' : (fun _ : ℕ => (Formalism.L2.Col.extChi (fun s => (Units.map ι.toMonoidHom).comp (χ₁ s)) s)⁻¹) =
      fun _ : ℕ => (Units.map ι.toMonoidHom).comp (Formalism.L2.Col.extChi χ₁ s)⁻¹ :=
    funext fun _ => (congrArg (·⁻¹) (Formalism.L2.Col.extChi_coefMap ι χ₁ s)).trans (Formalism.L2.Col.coefMap_comp_inv ι _)
  exact congrArg (Formalism.L2.Col.Lev.mk (Formalism.L2.Col.HKV (𝓞 E ⧸ w.asIdeal) nV r t))
    ((congrArg (fun χ => Formalism.L2.Col.lamK χ nV r [t]) h').trans (Formalism.L2.Col.lamK_coefMap ι _ _ _))

theorem lift_refTuple_enl : ∀ {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂} (w₁ : ColW B₁ f₁ T₁) (w₂ : ColW B₂ f₂ T₂) (W₁ : Set B₁.places.Pl) (W₂ : Set B₂.places.Pl), Enl B₁ B₂ → HEq (B₂.primes w₂.px).vGs (B₁.primes w₁.px).vGs → (∀ (j₁ : Fin B₁.R.m) (j₂ : Fin B₂.R.m), (j₁ : ℕ) = j₂ → ∀ (p₁ : {p // p ∈ (B₁.primes w₁.px).vGs}) (p₂ : {p // p ∈ (B₂.primes w₂.px).vGs}), HEq p₂.1 p₁.1 → ∀ (c₁ : (𝓞 B₁.fields.E ⧸ p₁.1.asIdeal)ˣ) (c₂ : (𝓞 B₂.fields.E ⧸ p₂.1.asIdeal)ˣ), HEq c₂ c₁ → B₂.embLL ((w₂.I.Ch.chi j₂ p₂ c₂ : B₂.fields.Kˣ) : B₂.fields.K) = B₁.embLL ((w₁.I.Ch.chi j₁ p₁ c₁ : B₁.fields.Kˣ) : B₁.fields.K)) → ∀ j₁ j₂ : ℕ, j₁ = j₂ → (Formalism.L2.Col.mtKGSD (Pr := B₂.primes w₂.px) B₂.wts w₂.I.Ch w₂.I.sel (mu0F (X := B₂.fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₂).D = (Formalism.L2.Col.mtKGSD (Pr := B₁.primes w₁.px) B₁.wts w₁.I.Ch w₁.I.sel (mu0F (X := B₁.fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).D ∧ ∀ φ₁ : (Formalism.L2.Col.mtKGSD (Pr := B₁.primes w₁.px) B₁.wts w₁.I.Ch w₁.I.sel (mu0F (X := B₁.fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).EqFun, ∃ φ₂ : (Formalism.L2.Col.mtKGSD (Pr := B₂.primes w₂.px) B₂.wts w₂.I.Ch w₂.I.sel (mu0F (X := B₂.fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₂).EqFun, ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map (B₂.embLL : B₂.fields.K →+* ℂ) (φ₂.1 d₂).1) (MvPolynomial.map (B₁.embLL : B₁.fields.K →+* ℂ) (φ₁.1 d₁).1) := by
  intro B₁ B₂ f₁ f₂ T₁ T₂ w₁ w₂ W₁ W₂ hE hv hchi j₁ j₂ hj
  subst hj
  obtain ⟨hpre, -, -, hrange⟩ := hE
  obtain ⟨ι, hι⟩ := exists_iota_comp B₁.embLL B₂.embLL hrange
  cases B₁ with | mk P₁ =>
  cases B₂ with | mk P₂ =>
  dsimp only at hpre
  subst hpre
  refine liftRound_reidx (baseOfColW w₁).fields ι (baseOfColW w₂).tauLL ?_ _ ?_ _ _ ?_ (baseOfColW w₁).embLL
    (baseOfColW w₂).embLL hι
  · intro τ
    ext x
    apply (baseOfColW w₂).embLL.injective
    have h1 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w₁) τ)
    have h2 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w₂) τ)
    simp only [Formalism.L2.Col.Fields.embC, RingHom.comp_apply] at h1 h2
    rw [RingHom.comp_apply, hι]
    exact h1.trans h2.symm
  · exact (rowLevelPrimes_colTuples_eq_vGs w₂ W₂).trans ((eq_of_heq hv).trans (rowLevelPrimes_colTuples_eq_vGs w₁ W₁).symm)
  · refine glue_inv_coefMap_of_empty ι (twistRamifiedPrimes_empty_colTuples w₁ W₁) (twistRamifiedPrimes_empty_colTuples w₂ W₂) _ _ _ _ ?_
    intro w hw
    refine levKV_coefMap_of ι w.1 (fun s => w₁.I.Ch.chi s w) (fun s => w₂.I.Ch.chi s ⟨w.1, hw⟩) ?_ _ _ _ _
    intro s c
    apply (baseOfColW w₂).embLL.injective
    rw [hι]
    exact hchi s s rfl w ⟨w.1, hw⟩ HEq.rfl c c HEq.rfl

end GlobalTheory.Mem.R3.Tr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowPartFormsAndNonzeroVectorsEveryPlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowPart_forms_and_nonzero_vectors_every_place : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v := by
  first | exact @GlobalTheory.RowsLift.rows_lift | exact GlobalTheory.RowsLift.rows_lift | (intros; apply GlobalTheory.RowsLift.rows_lift <;> assumption)
end

