import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0213
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0178
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0217
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0215
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0058
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.EqMulInversePow
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0216
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.WeilBound.CoreStatements.HodgeTatePoints.IsPullbackWhisker

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelFieldPoint
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

open Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace CombVal

section General

variable {S S' : Scheme.{0}} {G : CategoryTheory.Over S} {G' : CategoryTheory.Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left}

theorem push_mul (h : IsGrpPullback G' G f φ) {A : Scheme.{0}} {a : A ⟶ S'} {b : A ⟶ S} (hab : a ≫ f = b)
    (x y : CategoryTheory.Over.mk a ⟶ G') (x₀ y₀ : CategoryTheory.Over.mk b ⟶ G) (hx : x₀.left = x.left ≫ φ) (hy : y₀.left = y.left ≫ φ) :
    (x₀ * y₀).left = (x * y).left ≫ φ := by
  subst hab
  exact h.2 (CategoryTheory.Over.mk a) x y x₀ y₀ hx hy

theorem push_one (h : IsGrpPullback G' G f φ) {A : Scheme.{0}} {a : A ⟶ S'} {b : A ⟶ S} (hab : a ≫ f = b) :
    (1 : CategoryTheory.Over.mk b ⟶ G).left = (1 : CategoryTheory.Over.mk a ⟶ G').left ≫ φ := by
  subst hab
  exact (congrArg (fun z => z.left) (map_one (pushHom h (CategoryTheory.Over.mk a)))).symm

theorem one_left_congr {A : Scheme.{0}} {a b : A ⟶ S} (h : a = b) :
    (1 : CategoryTheory.Over.mk a ⟶ G).left = (1 : CategoryTheory.Over.mk b ⟶ G).left := by
  subst h
  rfl

theorem push_mul₂ {S₂ : Scheme.{0}} {G₂ : CategoryTheory.Over S₂} [GrpObj G₂] {f₂ : S₂ ⟶ S} {φ₂ : G₂.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (h₂ : IsGrpPullback G₂ G f₂ φ₂) {A : Scheme.{0}} {a : A ⟶ S'} {a₂ : A ⟶ S₂}
    (hab : a ≫ f = a₂ ≫ f₂) (x y : CategoryTheory.Over.mk a ⟶ G') (x' y' : CategoryTheory.Over.mk a₂ ⟶ G₂)
    (hx : x.left ≫ φ = x'.left ≫ φ₂) (hy : y.left ≫ φ = y'.left ≫ φ₂) :
    (x * y).left ≫ φ = (x' * y').left ≫ φ₂ := by
  have wx : (x.left ≫ φ) ≫ G.hom = a ≫ f := by
    rw [Category.assoc, h.1.w, ← Category.assoc, CategoryTheory.Over.w x]
    rfl
  have wy : (y.left ≫ φ) ≫ G.hom = a ≫ f := by
    rw [Category.assoc, h.1.w, ← Category.assoc, CategoryTheory.Over.w y]
    rfl
  let W : CategoryTheory.Over.mk (a ≫ f) ⟶ G := CategoryTheory.Over.homMk (x.left ≫ φ) wx
  let W' : CategoryTheory.Over.mk (a ≫ f) ⟶ G := CategoryTheory.Over.homMk (y.left ≫ φ) wy
  exact (push_mul h rfl x y W W' rfl rfl).symm.trans (push_mul h₂ hab.symm x' y' W W' hx hy)

theorem push_one₂ {S₂ : Scheme.{0}} {G₂ : CategoryTheory.Over S₂} [GrpObj G₂] {f₂ : S₂ ⟶ S} {φ₂ : G₂.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (h₂ : IsGrpPullback G₂ G f₂ φ₂) {A : Scheme.{0}} {a : A ⟶ S'} {a₂ : A ⟶ S₂}
    (hab : a ≫ f = a₂ ≫ f₂) :
    (1 : CategoryTheory.Over.mk a ⟶ G').left ≫ φ = (1 : CategoryTheory.Over.mk a₂ ⟶ G₂).left ≫ φ₂ :=
  (push_one h hab).symm.trans (push_one h₂ rfl)

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {F : Type} [Field F] [Algebra c.F F]

abbrev qe (y : FrPt Xo c F) : Spec (CommRingCat.of (DualNumber F)) ⟶ Xo.XF c :=
  spMap (algebraMap F (DualNumber F)) ≫ Small.ptF y

theorem qe_fst (y : FrPt Xo c F) : qe y ≫ pullback.fst _ _ = spMap (algebraMap F (DualNumber F)) ≫ y.x := by
  rw [Category.assoc, Small.ptF_fst]

def liftP (Y : Model Xo c β) (y : FrPt Xo c F) (p : tEps y.x ⟶ Xo.univ.t.G) : CategoryTheory.Over.mk (qe y) ⟶ Y.oF.t.G :=
  CategoryTheory.Over.homMk (Y.m0.cart.1.lift p.left (qe y) ((CategoryTheory.Over.w p).trans (qe_fst y).symm)) (Y.m0.cart.1.lift_snd _ _ _)

theorem pointLift_fst (Y : Model Xo c β) (y : FrPt Xo c F) (p : tEps y.x ⟶ Xo.univ.t.G) :
    (liftP Y y p).left ≫ Y.m0.toSABMap.φ = p.left :=
  Y.m0.cart.1.lift_fst _ _ _

theorem pointLift_eq (Y : Model Xo c β) (y : FrPt Xo c F) (p : tEps y.x ⟶ Xo.univ.t.G) (P : CategoryTheory.Over.mk (qe y) ⟶ Y.oF.t.G)
    (h : P.left ≫ Y.m0.toSABMap.φ = p.left) : (liftP Y y p).left = P.left := by
  apply Y.m0.cart.1.hom_ext
  · exact (pointLift_fst Y y p).trans h.symm
  · exact (CategoryTheory.Over.w (liftP Y y p)).trans (CategoryTheory.Over.w P).symm

variable {Y : Model Xo c β} {X : Scheme.{0}} {tX : SAB H X} {f : X ⟶ Y.X} (m : SABMap tX Y.t f)
  {g : Spec (CommRingCat.of F) ⟶ X} {EC : Type} [AddCommGroup EC] [Module F EC] (MC : LieModel tX.G g EC)
  (y : FrPt Xo c F)

def Rd (p : tEps y.x ⟶ Xo.univ.t.G) (e : EC) : Prop :=
  (MC.pt e).left ≫ m.φ = (liftP Y y p).left ≫ Y.m.φ

variable {y}

theorem base_eq (hY : Small.ptY Y y = g ≫ f) :
    (spMap (algebraMap F (DualNumber F)) ≫ g) ≫ f = qe y ≫ Y.jQ ≫ pullback.fst _ _ := by
  rw [Category.assoc, Category.assoc, ← hY]
  rfl

theorem pt_zero : MC.pt 0 = 1 := by
  have h := MC.add 0 0
  rw [add_zero] at h
  exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)

theorem rd_one (hY : Small.ptY Y y = g ≫ f) : Rd m MC y 1 0 := by
  have h1 : (liftP Y y 1).left = (1 : CategoryTheory.Over.mk (qe y) ⟶ Y.oF.t.G).left := by
    refine pointLift_eq Y y 1 1 ?_
    exact ((push_one Y.m0.cart (qe_fst y)).symm).trans (one_left_congr rfl)
  unfold Rd
  rw [h1, pt_zero]
  exact push_one₂ m.cart Y.m.cart (base_eq hY)

theorem rd_mul (hY : Small.ptY Y y = g ≫ f) {p p' : tEps y.x ⟶ Xo.univ.t.G} {e e' : EC}
    (h : Rd m MC y p e) (h' : Rd m MC y p' e') : Rd m MC y (p * p') (e + e') := by
  have h1 : (liftP Y y (p * p')).left = (liftP Y y p * liftP Y y p').left := by
    refine pointLift_eq Y y _ _ ?_
    exact (push_mul Y.m0.cart (qe_fst y) (liftP Y y p) (liftP Y y p') p p'
      (pointLift_fst Y y p).symm (pointLift_fst Y y p').symm).symm
  unfold Rd
  rw [h1, MC.add]
  exact push_mul₂ m.cart Y.m.cart (base_eq hY) (MC.pt e) (MC.pt e') (liftP Y y p) (liftP Y y p') h h'

theorem scale_base (a : F) : spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ spMap (algebraMap F (DualNumber F)) =
    spMap (algebraMap F (DualNumber F)) := by
  rw [← spMap_comp]
  congr 1
  ext r <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem rd_smul {p p₂ : tEps y.x ⟶ Xo.univ.t.G} {e : EC} (a : F)
    (hp : p₂.left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ p.left) (h : Rd m MC y p e) :
    Rd m MC y p₂ (a • e) := by
  have h1 : (liftP Y y p₂).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ (liftP Y y p).left := by
    apply Y.m0.cart.1.hom_ext
    · rw [pointLift_fst, Category.assoc, pointLift_fst, hp]
    · have e₁ := CategoryTheory.Over.w (liftP Y y p)
      have e₂ := CategoryTheory.Over.w (liftP Y y p₂)
      refine e₂.trans ?_
      rw [Category.assoc, e₁]
      show qe y = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ qe y
      rw [qe, ← Category.assoc, scale_base]
  unfold Rd at h ⊢
  rw [h1, MC.smul, Category.assoc, Category.assoc, h]
  rfl

theorem rd_prod (hY : Small.ptY Y y = g ≫ f) :
    ∀ (n : ℕ) (u : Fin n → (tEps y.x ⟶ Xo.univ.t.G)) (e : Fin n → EC), (∀ i, Rd m MC y (u i) (e i)) →
      Rd m MC y (List.ofFn u).prod (∑ i, e i)
  | 0, u, e, _ => by
    simpa using rd_one m MC hY
  | n + 1, u, e, h => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact rd_mul m MC hY (h 0) (rd_prod hY n _ _ fun i => h i.succ)

end CombVal

theorem comb_val : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (g : Spec (CommRingCat.of F) ⟶ X) (EC : Type) [AddCommGroup EC] [Module F EC] (MC : LieModel tX.G g EC) (y : FrPt Xo c F), Small.ptY Y y = g ≫ f → ∀ (n : ℕ) (v : Fin n → (Spec (CommRingCat.of (DualNumber F)) ⟶ Xo.univ.t.G.left)) (hv : ∀ j, Formalism.L2.Pj.IsTanAt y.x (v j)) (e : Fin n → EC), (∀ j, (MC.pt (e j)).left ≫ m.φ = FinRd.Roots.LieBasis.tanW Y y (v j) (hv j).1) → ∀ (cf : Fin n → F) (w : Spec (CommRingCat.of (DualNumber F)) ⟶ Xo.univ.t.G.left), IsCombAt y.x v cf w → ∃ hw : w ≫ Xo.univ.t.G.hom = spMap (algebraMap F (DualNumber F)) ≫ y.x, (MC.pt (∑ j, cf j • e j)).left ≫ m.φ = FinRd.Roots.LieBasis.tanW Y y w hw := by
  intro E _ _ _ H Dw l Xo c O _ β Y X tX f m F _ _ g EC _ _ MC y hY n v hv e he cf w hc
  obtain ⟨u, hu, rfl⟩ := hc
  refine ⟨CategoryTheory.Over.w ((List.ofFn u).prod), ?_⟩
  have h0 : ∀ j, CombVal.Rd m MC y (CategoryTheory.Over.homMk (v j) (hv j).1 : tEps y.x ⟶ Xo.univ.t.G) (e j) := he
  have h1 : ∀ j, CombVal.Rd m MC y (u j) (cf j • e j) := fun j => CombVal.rd_smul m MC (cf j) (hu j) (h0 j)
  exact CombVal.rd_prod m MC hY n u (fun j => cf j • e j) h1

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartMapsCompatibleRightStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_part_maps_compatible_right : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (L₁ L : Type) [Field L₁] [Field L] [NumberField L] (e₂ : L₁ →+* L) (z₁ : Sp L₁ ⟶ X) (z : Sp (𝓞 L) ⟶ X) (hz : spMap (algebraMap (𝓞 L) L) ≫ z = spMap e₂ ≫ z₁) (P₁ : AbPart t z₁) (P₂ : AbPart t (spMap e₂ ≫ z₁)) (mK2 : SABMap P₂.tK P₁.tK (spMap e₂)) (mB2 : SABMap P₂.tB P₁.tB (spMap e₂)) (c1 : mK2.φ ≫ P₁.m.φ = P₂.m.φ) (c2 : mK2.φ ≫ (P₁.τ.q ≫ P₁.e.hom).left = (P₂.τ.q ≫ P₂.e.hom).left ≫ mB2.φ) (t' : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (m' : SABMap tK t' (spMap (algebraMap (𝓞 L) L))) (mP : SABMap tK P₁.tB (spMap e₂)) (w : P₂.tB.G.left ⟶ tK.G.left) (hw : w ≫ mP.φ = mB2.φ) (hw' : w ≫ tK.G.hom = P₂.tB.G.hom) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M₀ : LieModel t.G ξ Li) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (h : LieMetric M₀ y) (K₀ : ℝ) (hQ : ∀ (zc : Sp ℂ ⟶ X) (P : AbPart t zc) (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (v₀ : epsAt zc ⟶ t.G) (c : ℂ), IsTanAt _ _ v → v.left ≫ P.m.φ = v₀.left → HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (v ≫ P.τ.q ≫ P.e.hom) (v ≫ P.τ.q ≫ P.e.hom) c → c.re ≤ K₀ * (h.ip zc v₀ v₀).re) (B B' : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel t.G z B.carrier) (MB' : LieModel t'.G (𝟙 _) B'.carrier) (hB : IsFibre (fun z v w c => c = h.ip z v w) z B MB) (hB' : IsFibre (HodgeIP t'.G t'.PP.L) (𝟙 _) B' MB') (f : B.carrier →ₗ[𝓞 L] B'.carrier) (hf : ∀ (e : B.carrier) (v : epsAt (𝟙 (Sp L)) ⟶ P₂.tK.G), MB.Lifts (algebraMap (𝓞 L) L) P₂.m.φ e v → MB'.Lifts (algebraMap (𝓞 L) L) (P₂.e.hom.left ≫ w ≫ m'.φ) (f e) (v ≫ P₂.τ.q)) (σ : L →+* ℂ) (x : GroundTheory.Heights₂.Heights.Fibre σ B.carrier), sqAt B' σ (f.lTensor (GroundTheory.Heights₂.Heights.ComplexAt σ) x) ≤ K₀ * sqAt B σ x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SlopeNorm.sqAt_le | exact GlobalTheory.CompanionTheory.Ar.SlopeNorm.sqAt_le | (intros; apply GlobalTheory.CompanionTheory.Ar.SlopeNorm.sqAt_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrCoordRatioValueStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_dvr_coord_ratio_value : ∀ (X : AlgebraicGeometry.Scheme.{0}) (Ω : Type) [Field Ω] (ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (A : Subring Ω) (T : CDVR) (evT : A →+* T.Fr) (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ (hr : ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A), (∀ k i, evT ⟨_, hr k i⟩ ∈ (algebraMap T.V T.Fr).range) → (∀ a : A, ∃ b : A, evT b ≠ 0 ∧ (b : Ω) ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩) ∧ (a : Ω) * b ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩)) → ∃ (zV : AlgebraicGeometry.Spec (CommRingCat.of T.V) ⟶ X) (h : genPt ξ ⤳ centre zV), InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre zV, h⟩ ∧ FinRd.Roots.ReadsPt ξ A T evT zV := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.chart_point | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.chart_point | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.chart_point <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrLieModelLatticeStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_dvr_lie_model_lattice : ∀ (X : AlgebraicGeometry.Scheme.{0}) (G : CategoryTheory.Over X) [CategoryTheory.GrpObj G] [CategoryTheory.IsCommMonObj G] (Ω : Type) [Field Ω] (ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X) (L₀ : Type) [AddCommGroup L₀] [Module Ω L₀] (M : LieModel G ξ L₀) (T : CDVR) (zV : AlgebraicGeometry.Spec (CommRingCat.of T.V) ⟶ X) (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel G (FinRd.Roots.gen T zV) EC) (A : Subring Ω) (evT : A →+* T.Fr), IsCptGen ξ → AlgebraicGeometry.Smooth G.hom → ∀ (h : genPt ξ ⤳ centre zV), genPt ξ ⤳ centre (FinRd.Roots.gen T zV) → FinRd.Roots.ReadsPt ξ A T evT zV → ∀ (L : Lat ξ L₀) (r : ℕ) (b e : Fin r → L₀) (Tm : Matrix (Fin r) (Fin r) Ω) (w : Fin r → EC) (hT : ∀ i j, Tm i j ∈ A), L.IsFrameAt b ⟨centre zV, h⟩ → (∀ i, b i = ∑ j, Tm i j • e j) → (∀ j, M.ValAt (FinRd.Roots.gen T zV) (e j) (MC.pt (w j))) → M.fibAt L zV MC = Submodule.span T.V (Set.range fun i => ∑ j, evT ⟨Tm i j, hT i j⟩ • w j) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.complete_dvr_lie_model_lattice | exact GlobalTheory.CompanionTheory.Relay.complete_dvr_lie_model_lattice | (intros; apply GlobalTheory.CompanionTheory.Relay.complete_dvr_lie_model_lattice <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompleteDvrPullbackSemiabelian
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

open scoped CategoryTheory.Obj

theorem exists_extended_identification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), GlobalTheory.Published.SemiAbelianHomExtension → ∀ (X : Scheme.{0}) (tX : SAB H X) (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) (G : SAB H (Spec (CommRingCat.of T.V))) (t' : SAB H (Spec (CommRingCat.of T.Fr))) (m2 : SABMap t' G (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)))) (b : t'.G.left ⟶ tX.G.left), IsGrpPullback t'.G tX.G (FinRd.Roots.gen T zV) b → (∀ a, (t'.act.act a).left ≫ b = b ≫ (tX.act.act a).left) → ∃ Ψ : G.G.left ⟶ tX.G.left, IsGrpPullback G.G tX.G zV Ψ ∧ m2.φ ≫ Ψ = b ∧ ∀ a, (G.act.act a).left ≫ Ψ = Ψ ≫ (tX.act.act a).left := by
  intro E _ _ _ H hE X tX T zV G t' m2 b hb hact
  have hp : IsGrpPullback ((Over.pullback zV).obj tX.G) tX.G zV (Limits.pullback.fst tX.G.hom zV) :=
    isGrpPullback_pullback tX.G zV
  let ψ : t'.G.left ⟶ ((Over.pullback zV).obj tX.G).left :=
    Limits.pullback.lift b (t'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)))
      (by rw [hb.1.w, Category.assoc])
  have hψf : ψ ≫ Limits.pullback.fst tX.G.hom zV = b := Limits.pullback.lift_fst _ _ _
  have hψs : ψ ≫ ((Over.pullback zV).obj tX.G).hom =
      t'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) := Limits.pullback.lift_snd _ _ _
  have hψ : IsGrpPullback t'.G ((Over.pullback zV).obj tX.G)
      (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) ψ :=
    hp.cancel (hb.congr rfl hψf.symm) hψs
  have hj : GlobalTheory.IsGenericPointHom (Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr))) :=
    GlobalTheory.IsGenericPointHom.fractionField T.V T.Fr
  have hS := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec T.V
  have hH' := IsSemiAbelian.pullback zV tX.G tX.semi
  obtain ⟨e, ⟨hmon, heq⟩, -⟩ := hE.generic_existsUnique_iso_of_extensions hS hj G.semi hH' m2.cart hψ
  obtain ⟨_, _⟩ := hj.quasiCompact_and_dominant
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G.G G.semi
  obtain ⟨-, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ hH'
  refine ⟨e.hom.left ≫ Limits.pullback.fst tX.G.hom zV,
    ((isGrpPullback_of_iso e).comp hp).congr (Category.id_comp _) rfl, ?_, fun a => ?_⟩
  · rw [← Category.assoc, heq, hψf]
  · have hB : ((Over.pullback zV).map (tX.act.act a)).left ≫ Limits.pullback.fst tX.G.hom zV =
        Limits.pullback.fst tX.G.hom zV ≫ (tX.act.act a).left := Limits.pullback.lift_fst _ _ _
    have hψa : (t'.act.act a).left ≫ ψ = ψ ≫ ((Over.pullback zV).map (tX.act.act a)).left := by
      apply Limits.pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hB, hψf, ← Category.assoc ψ, hψf, hact]
      · have h₁ := hψs
        have h₂ := Over.w ((Over.pullback zV).map (tX.act.act a))
        have h₃ := Over.w (t'.act.act a)
        change _ ≫ ((Over.pullback zV).obj tX.G).hom = _ ≫ ((Over.pullback zV).obj tX.G).hom
        rw [Category.assoc, Category.assoc, h₂, h₁, ← Category.assoc, h₃]
    have key : G.act.act a ≫ e.hom = e.hom ≫ (Over.pullback zV).map (tX.act.act a) := by
      refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback m2.cart.1 ?_
      rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← m2.act a, Category.assoc, heq, hψa,
        ← Category.assoc, heq]
    have key' := congrArg (fun f => f.left ≫ Limits.pullback.fst tX.G.hom zV) key
    simp only [Over.comp_left, Category.assoc, hB] at key'
    simpa only [Category.assoc] using key'

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFormalGermOpenAffine
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_formal_germ_open_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0), PowFns t → ∀ z : X0, ∃ (A : Type) (_ : CommRing A) (j : Sp A ⟶ X0) (d : ℕ), IsOpenImmersion j ∧ z ∈ Set.range j ∧ Nonempty (GermAt t j d) := by
  first | exact @PositivityTheory.HtPt.Cd.germ_affine | exact PositivityTheory.HtPt.Cd.germ_affine
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGermSystem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem germSys_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) [IsLocallyNoetherian X], PowFns t → IsCptGen ξ → ∃ (d : ℕ) (M : LieModel t.G ξ (Fin d → Ω)), Nonempty (GermSys t ξ M) :=
  @PositivityTheory.Xgn.germ_system_exists

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteResidueAbsoluteValueStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_residue_absolute_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (e : ℕ), 0 < e → 0 < ramOverZ la → (∀ x y : T.Fr, FinRd.absT p la T e (x * y) = FinRd.absT p la T e x * FinRd.absT p la T e y) ∧ FinRd.absT p la T e 1 = 1 ∧ (∀ x : T.Fr, x ≠ 0 → 0 < FinRd.absT p la T e x) ∧ ∀ x : T.Fr, FinRd.absT p la T e x ≤ 1 ↔ x ∈ (algebraMap T.V T.Fr).range := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT_facts | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT_facts | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.absT_facts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagEqualChangeLowerTriangularStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_equal_change_lower_triangular : ∀ (Ω : Type) [Field Ω] (L : Type) [AddCommGroup L] [Module Ω L] (r : ℕ) (b b₀ : Fin r → L) (Tm : Matrix (Fin r) (Fin r) Ω), LinearIndependent Ω b → (∀ i : ℕ, flagStep Ω b i = flagStep Ω b₀ i) → (∀ i, b i = ∑ j, Tm i j • b₀ j) → LinearIndependent Ω b₀ ∧ ∀ i j, i < j → Tm i j = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FlagTri.independent_and_triangular | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FlagTri.independent_and_triangular | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FlagTri.independent_and_triangular <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatModelTorusRingStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_model_torus_ring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (φ : FrameFn Xo c), τ (H.rt : E) = H.rt0 → IsClopen U → IsLineFn U τ φ → FlatOnModel Z τ φ → ∀ (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (k : Type) [Field k] (ψ₀ : p.R →+* k) (y₀ : Sp k ⟶ Xo.XF c), under y₀ = spMap ψ₀ ≫ z.x → y₀ ≫ pullback.snd _ _ = spMap (ψ₀.comp (algebraMap c.F p.R)) → Set.range y₀ ⊆ U → ∃ g a : p.R, ψ₀ g ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : p.R →+* F) (y : Sp F ⟶ Xo.XF c), under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) → ψ g ≠ 0 → Set.range y ⊆ U ∧ ∀ (v : Vecs y D.p) (w : Vecs y D.q) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q), (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) → (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → ψ a = ψ g * φ F y v w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.exists_regular_near | exact GlobalTheory.CompanionTheory.Ar.LocFn.exists_regular_near | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.exists_regular_near <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.formal_germ_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (S S₂ : Type) [CommRing S] [CommRing S₂] (f : S →+* S₂) (x : Sp S ⟶ X0) (d : ℕ) (g : GermAt t x d), ∃ g₂ : GermAt t (spMap f ≫ x) d, IsMapOf f g.B g₂.B ∧ ∀ l, g₂.tg l = spMap (GlobalTheory.CompanionTheory.Ar.dualMap f) ≫ g.tg l := by
  first | exact @PositivityTheory.HtPt.Ce.germ_bc | exact PositivityTheory.HtPt.Ce.germ_bc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointAbelianMapCompat
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

open CategoryTheory.Limits

theorem genFibre_pullback_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (y : FrPt Xo c F) (t' : SAB H (Spec (CommRingCat.of F))) (m1 : SABMap t' Xo.univ.t y.x) (g : Spec (CommRingCat.of F) ⟶ X), Small.ptY Y y = g ≫ f → ∃ b : t'.G.left ⟶ tX.G.left, IsGrpPullback t'.G tX.G g b ∧ (∀ a, (t'.act.act a).left ≫ b = b ≫ (tX.act.act a).left) ∧ ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (u' : Spec (CommRingCat.of (DualNumber F)) ⟶ t'.G.left), u' ≫ m1.φ = y.u τ i → u' ≫ t'.G.hom = Spec.map (CommRingCat.ofHom (algebraMap F (DualNumber F))) → u' ≫ b ≫ m.φ = Small.tanY Y y τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Y X tX f m F _ _ y t' m1 g hg
  have wa : m1.φ ≫ Xo.univ.t.G.hom = (t'.G.hom ≫ Small.ptF y) ≫ pullback.fst _ _ := by
    rw [m1.cart.1.w, Category.assoc, Small.ptF_fst]
  let a : t'.G.left ⟶ Y.oF.t.G.left := Y.m0.cart.1.lift m1.φ (t'.G.hom ≫ Small.ptF y) wa
  have ha1 : a ≫ Y.m0.toSABMap.φ = m1.φ := IsPullback.lift_fst _ _ _ _
  have ha2 : a ≫ Y.oF.t.G.hom = t'.G.hom ≫ Small.ptF y := IsPullback.lift_snd _ _ _ _
  have gpa : IsGrpPullback t'.G Y.oF.t.G (Small.ptF y) a :=
    IsGrpPullback.cancel Y.m0.cart (m1.cart.congr (Small.ptF_fst y).symm ha1.symm) ha2
  have gpY : IsGrpPullback t'.G Y.t.G (g ≫ f) (a ≫ Y.m.φ) := (gpa.comp Y.m.cart).congr hg rfl
  have wb : (a ≫ Y.m.φ) ≫ Y.t.G.hom = (t'.G.hom ≫ g) ≫ f := by
    rw [gpY.1.w, Category.assoc]
  let b : t'.G.left ⟶ tX.G.left := m.cart.1.lift (a ≫ Y.m.φ) (t'.G.hom ≫ g) wb
  have hb1 : b ≫ m.φ = a ≫ Y.m.φ := IsPullback.lift_fst _ _ _ _
  have hb2 : b ≫ tX.G.hom = t'.G.hom ≫ g := IsPullback.lift_snd _ _ _ _
  have acta : ∀ r, (t'.act.act r).left ≫ a = a ≫ (Y.oF.t.act.act r).left := by
    intro r
    apply Y.m0.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, ha1, Y.m0.act r, ← Category.assoc, ha1, m1.act r]
    · rw [Category.assoc, Category.assoc, ha2, Over.w (Y.oF.t.act.act r), ha2, ← Category.assoc,
        Over.w (t'.act.act r)]
  refine ⟨b, IsGrpPullback.cancel m.cart (gpY.congr rfl hb1.symm) hb2, fun r => ?_, fun τ i u' h1 h2 => ?_⟩
  · apply m.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, hb1, m.act r, ← Category.assoc b, hb1, Category.assoc, ← Y.m.act r,
        ← Category.assoc, acta r, Category.assoc]
    · rw [Category.assoc, Category.assoc, hb2, Over.w (tX.act.act r), hb2, ← Category.assoc,
        Over.w (t'.act.act r)]
  · have e : u' ≫ a = Small.tanF Y y τ i := by
      apply Small.eq_tanF
      · rw [Category.assoc, ha1, h1]
      · rw [Category.assoc, ha2, ← Category.assoc, h2]
    rw [hb1, ← Category.assoc, e]
    rfl

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
end

