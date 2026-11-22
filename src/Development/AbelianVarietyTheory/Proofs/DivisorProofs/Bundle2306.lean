import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0628
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenAmple
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0641
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2260
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialSquareZeroExtensionPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SqZeroPb

def liftHom {K : Type} [Field K] {V W₁ W₂ : Type} [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V]
    [IsCentralScalar K V] [AddCommGroup W₁] [Module K W₁] [Module Kᵐᵒᵖ W₁] [IsCentralScalar K W₁]
    [AddCommGroup W₂] [Module K W₂] [Module Kᵐᵒᵖ W₂] [IsCentralScalar K W₂]
    (e : V ≃ₗ[K] W₁ × W₂) {T : Type} [CommRing T]
    (a : T →+* TrivSqZeroExt K W₁) (b : T →+* TrivSqZeroExt K W₂)
    (h : ∀ t, (a t).fst = (b t).fst) : T →+* TrivSqZeroExt K V where
  toFun t := TrivSqZeroExt.inl (a t).fst + TrivSqZeroExt.inr (e.symm ((a t).snd, (b t).snd))
  map_one' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
  map_mul' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp only [map_mul, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_add,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, add_zero, zero_add, smul_eq_mul, op_smul_eq_smul, smul_zero]
      rw [← map_smul, ← map_smul, ← map_add]
      congr 1
      ext <;> simp [h]
  map_zero' := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp
  map_add' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp only [map_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, zero_add]
      rw [show ((a x).snd + (a y).snd, (b x).snd + (b y).snd)
          = ((a x).snd, (b x).snd) + ((a y).snd, (b y).snd) from rfl, map_add]

end GlobalTheory.SqZeroPb

open GlobalTheory.SqZeroPb in
theorem GlobalTheory.SqZeroPb.isPullback_trivSqZeroExt : ∀ (K : Type) [Field K] (V W₁ W₂ : Type) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V] [AddCommGroup W₁] [Module K W₁] [Module Kᵐᵒᵖ W₁] [IsCentralScalar K W₁] [AddCommGroup W₂] [Module K W₂] [Module Kᵐᵒᵖ W₂] [IsCentralScalar K W₂] (p : V →ₗ[K] W₁) (q : V →ₗ[K] W₂), Function.Bijective (LinearMap.prod p q) → IsPullback (CommRingCat.ofHom (TrivSqZeroExt.map p).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.map q).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₁).toRingHom) (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₂).toRingHom) := by
  intro K _ V W₁ W₂ _ _ _ _ _ _ _ _ _ _ _ _ p q hpq
  let e := LinearEquiv.ofBijective (LinearMap.prod p q) hpq
  have he : ∀ v, e v = (p v, q v) := fun v => rfl
  have hw : CommRingCat.ofHom (TrivSqZeroExt.map p).toRingHom ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₁).toRingHom =
      CommRingCat.ofHom (TrivSqZeroExt.map q).toRingHom ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom K K W₂).toRingHom := by
    ext x; simp
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk hw
    (fun s => CommRingCat.ofHom (liftHom e s.fst.hom s.snd.hom ?_)) ?_ ?_ ?_)
  · intro t
    have := congrArg (fun φ => φ.hom t) s.condition
    simpa using this
  · intro s
    ext t : 2
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [liftHom]
    · simp [liftHom]
      exact congrArg Prod.fst (e.apply_symm_apply _)
  · intro s
    ext t : 2
    have hc := congrArg (fun φ => φ.hom t) s.condition
    simp at hc
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [liftHom, hc]
    · simp [liftHom]
      exact congrArg Prod.snd (e.apply_symm_apply _)
  · intro s m hm1 hm2
    ext t : 2
    have h1 := congrArg (fun φ => φ.hom t) hm1
    have h2 := congrArg (fun φ => φ.hom t) hm2
    simp at h1 h2
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [liftHom, ← h1]
    · simp [liftHom, ← h1, ← h2]
      rw [LinearEquiv.eq_symm_apply]
      rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrvEqSelf
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqvTrans

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X Y : Scheme.{0}} {t : SAB H Y} {p : X ⟶ Y} {G' : Over X} [GrpObj G'] {ψ : G'.left ⟶ t.G.left}

open Classical in

def trv (hψ : IsPullback ψ G'.hom t.G.hom p) (g : G'.left ⟶ G'.left) {R : Type} [CommRing R] (q : Sp R ⟶ X)
    (v : Sp (DualNumber R) ⟶ t.G.left) : Sp (DualNumber R) ⟶ t.G.left :=
  if h : v ≫ t.G.hom = (spMap (algebraMap R (DualNumber R)) ≫ q) ≫ p then hψ.lift v _ h ≫ g ≫ ψ else v

variable (hψ : IsPullback ψ G'.hom t.G.hom p) {R R' : Type} [CommRing R] [CommRing R']

theorem trv_eq (g : G'.left ⟶ G'.left) (q : Sp R ⟶ X) {v : Sp (DualNumber R) ⟶ t.G.left}
    (w : Sp (DualNumber R) ⟶ G'.left) (hw : w ≫ ψ = v) (hw' : w ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ q) :
    trv hψ g q v = w ≫ g ≫ ψ := by
  have h : v ≫ t.G.hom = (spMap (algebraMap R (DualNumber R)) ≫ q) ≫ p := by
    rw [← hw, Category.assoc, hψ.w, ← Category.assoc, hw']
  rw [trv, dif_pos h]
  congr 1
  exact hψ.hom_ext (by rw [hψ.lift_fst, hw]) (by rw [hψ.lift_snd, hw'])

include hψ in

theorem exists_lift (q : Sp R ⟶ X) {v : Sp (DualNumber R) ⟶ t.G.left}
    (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    ∃ w : Sp (DualNumber R) ⟶ G'.left, w ≫ ψ = v ∧ w ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ q :=
  ⟨hψ.lift v _ (by rw [hv, Category.assoc]), hψ.lift_fst _ _ _, hψ.lift_snd _ _ _⟩

theorem trv_over (g : G'.left ⟶ G'.left) {b : X ⟶ X} (hg : g ≫ G'.hom = G'.hom ≫ b) (q : Sp R ⟶ X)
    {v : Sp (DualNumber R) ⟶ t.G.left} (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    trv hψ g q v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ (q ≫ b) ≫ p := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hψ q hv
  rw [trv_eq hψ g q w hw hw', Category.assoc, Category.assoc, hψ.w, reassoc_of% hg, reassoc_of% hw']
  simp only [Category.assoc]

theorem trv_map (g : G'.left ⟶ G'.left) (σ : R →+* R') (q : Sp R ⟶ X) {v : Sp (DualNumber R) ⟶ t.G.left}
    (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    trv hψ g (spMap σ ≫ q) (spMap (dualMap σ) ≫ v) = spMap (dualMap σ) ≫ trv hψ g q v := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hψ q hv
  have e : spMap (dualMap σ) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R' (DualNumber R')) ≫ spMap σ := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
  rw [trv_eq hψ g q w hw hw', trv_eq hψ g (spMap σ ≫ q) (spMap (dualMap σ) ≫ w) (by rw [Category.assoc, hw])
    (by rw [Category.assoc, hw', ← Category.assoc, e, Category.assoc])]
  simp only [Category.assoc]

theorem trv_comp (g₁ g₂ : G'.left ⟶ G'.left) {b₁ : X ⟶ X} (hg₁ : g₁ ≫ G'.hom = G'.hom ≫ b₁) (q : Sp R ⟶ X)
    {v : Sp (DualNumber R) ⟶ t.G.left} (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    trv hψ (g₁ ≫ g₂) q v = trv hψ g₂ (q ≫ b₁) (trv hψ g₁ q v) := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hψ q hv
  rw [trv_eq hψ _ q w hw hw', trv_eq hψ g₁ q w hw hw', trv_eq hψ g₂ (q ≫ b₁) (w ≫ g₁) (Category.assoc _ _ _)
    (by rw [Category.assoc, hg₁, reassoc_of% hw'])]
  simp only [Category.assoc]

theorem trv_eq_self (g : G'.left ⟶ G'.left) (q : Sp R ⟶ X)
    (hg : ∀ w : Sp (DualNumber R) ⟶ G'.left, w ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ q → w ≫ g = w)
    {v : Sp (DualNumber R) ⟶ t.G.left} (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    trv hψ g q v = v := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hψ q hv
  rw [trv_eq hψ g q w hw hw', ← Category.assoc, hg w hw', hw]

end GlobalTheory.EqvTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedLevelPointsOfLattice
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.TraitArc

open GlobalTheory.TauTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {T : CDVR} (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X]
  (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)) {ϖ : T.V} (hϖ : Irreducible ϖ)

def qv : D.toPre.X → ℤ := fun χ => (QForm.exists_QVal hϖ D χ).choose

theorem isQ_qv : QForm.IsQ D.toPre ϖ (qv D hϖ) := fun χ => (QForm.exists_QVal hϖ D χ).choose_spec

def beF : LinearMap.BilinForm ℤ D.toPre.X :=
  LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ D (isQ_qv D hϖ) a b)
    (fun a a' b => by simp [map_add]) (fun n a b => by simp [map_zsmul])
    (fun a b b' => by simp [map_add]) (fun n a b => by simp [map_zsmul])

theorem beF_symm (a b : D.toPre.X) : beF D hϖ a b = beF D hϖ b a := QForm.bOf_comm D a b

theorem beF_self (a : D.toPre.X) : beF D hϖ a a = 2 * qv D hϖ a :=
  (QForm.two_Q_eq hϖ D (isQ_qv D hϖ) a).symm

theorem beF_pos {a : D.toPre.X} (ha : a ≠ 0) : 0 < beF D hϖ a a := by
  have := QForm.Q_pos hϖ D (isQ_qv D hϖ) ha
  rw [beF_self]; omega

include oD in
theorem beF_adj (x : 𝓞 E) (a b : D.toPre.X) : beF D hϖ (x • a) b = beF D hϖ a (H.bar x • b) :=
  letI := H.starRing
  QForm.bOf_balance hϖ D GlobalTheory.abelianSchemeLaws_all.1 oD (isQ_qv D hϖ) x a b

include oD in
theorem beF_w0 (a : D.toPre.X) : beF D hϖ a (H.w0 • a) = qv D hϖ a := by
  have h₁ := beF_adj D oD hϖ H.w0 a a
  have hb : H.bar H.w0 = 1 - H.w0 := by rw [HostModel.cmHost_bar_halfIntegerGenerator]
  rw [hb, sub_smul, one_smul, map_sub, beF_symm D hϖ (H.w0 • a) a] at h₁
  have h₂ := beF_self D hϖ a
  omega

def tF (a b : D.toPre.X) : (FractionRing T.V)ˣ := GlobalTheory.ArcBuild.piK hϖ ^ (-(beF D hϖ a b))

include oD in
theorem isScalarForm_tF : letI := H.starRing; IsScalarForm (𝓞 E) (tF D hϖ) := by
  letI := H.starRing
  refine ⟨fun a b b' => ?_, fun a b => ?_, fun x a b => ?_⟩
  · simp only [tF, map_add, neg_add, zpow_add]
  · rw [tF, tF, beF_symm]
  · rw [tF, tF, beF_adj D oD]; rfl

abbrev D0 : DegPre T.V := letI := H.starRing; GlobalTheory.TauTwist.twist D.toPre H.w0 (tF D hϖ)

def oa0 : letI := H.starRing; (D0 (H := H) D hϖ).OAct (𝓞 E) :=
  letI := H.starRing; twistAct (GlobalTheory.ArcBuild.cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF D oD hϖ) oD

include oD in

theorem gen0 (a : D.toPre.X) : PsiUnitOn (D0 (H := H) D hϖ) a Set.univ :=
  psiUnitOn_rescale_of_qVal T D.toPre ϖ hϖ a (qv D hϖ a) (isQ_qv D hϖ a) _ (by
    show ((GlobalTheory.ArcBuild.piK hϖ ^ (-(beF D hϖ a (H.w0 • a))) : (FractionRing T.V)ˣ) : FractionRing T.V) = _
    rw [beF_w0 D oD, Units.val_zpow_eq_zpow_val]; rfl)

def rF (k : ℕ) (a b : D.toPre.X) : (FractionRing T.V)ˣ := GlobalTheory.ArcBuild.piK hϖ ^ (-(beF D hϖ a b / k))

include oD in
theorem isRootForm_rF {k : ℕ} (hk : ∀ a b, (k : ℤ) ∣ beF D hϖ a b) :
    letI := H.starRing; IsRootForm (𝓞 E) k (tF D hϖ) (rF D hϖ k) := by
  letI := H.starRing
  refine ⟨⟨fun a b b' => ?_, fun a b => ?_, fun x a b => ?_⟩, fun a b => ?_⟩
  · simp only [rF, map_add]
    rw [Int.add_ediv_of_dvd_left (hk a b), neg_add, zpow_add]
  · rw [rF, rF, beF_symm]
  · rw [rF, rF, beF_adj D oD]; rfl
  · rw [rF, tF, ← zpow_natCast, ← zpow_mul, neg_mul, Int.ediv_mul_cancel (hk a b)]
    ext; simp

theorem psiRel0 : letI := H.starRing; PsiRel D.toPre (D0 (H := H) D hϖ).psi fun y => tF D hϖ y (H.w0 • y) :=
  psiRel_rescale _ _

section ThetaShiftProofs

variable {Dm : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] (β : O →+* c.F) (b : O →+* T.V)

theorem dvd_of_dvd {k : ℕ} (hk : k ∣ l.M') (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF D hϖ a a') (a a' : D.toPre.X) :
    (k : ℤ) ∣ beF D hϖ a a' :=
  (Int.natCast_dvd_natCast.2 hk).trans ((dvd_mul_left _ _).trans (hdiv a a'))

def twistedLevelPointsOfLattice (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF D hϖ a a') (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A)
    (v : Dm.La) : QkPt (D0 (H := H) D hϖ) (FractionRing T.V) l.A :=
  letI := H.starRing
  qkScale (GlobalTheory.ArcBuild.cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF D oD hϖ) (psiRel0 D hϖ)
    (isRootForm_rF D oD hϖ (dvd_of_dvd D hϖ (Nat.dvd_lcm_right l.M l.A) hdiv)) _ (pA v)

def eta0 (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF D hϖ a a') (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M)
    (v : Dm.La) : QkPt (D0 (H := H) D hϖ) (FractionRing T.V) l.M :=
  letI := H.starRing
  qkScale (GlobalTheory.ArcBuild.cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF D oD hϖ) (psiRel0 D hϖ)
    (isRootForm_rF D oD hϖ (dvd_of_dvd D hϖ (Nat.dvd_lcm_left l.M l.A) hdiv)) _ (pM v)

open scoped Classical in
variable (Dm) in

def LieCl : Prop :=
  letI := H.starRing
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (r : O), ((β r : c.F) : ℂ) = H.rt0 →
    ∀ τ : 𝓞 E →+* F, ∃ n, LieMult (ofRingAct oD.onB.toRingAct)
      (spMap ((algebraMap (FractionRing T.V) F).comp (algebraMap T.V _))) τ n ∧
      n + Module.finrank (𝓞 E) D.toPre.X =
        if τ H.rt = (algebraMap (FractionRing T.V) F).comp (algebraMap T.V _) (b r) then Dm.p else Dm.q

variable (Dm) in

def TateCl (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF D hϖ a a') (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A)
    (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M) : Prop :=
  letI := H.starRing
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (z : O), ((β z : c.F) : ℂ) = zeta l.A →
    ∃ I : TateIsoQ Dm (D0 (H := H) D hϖ) (oa0 D oD hϖ) F,
      (I.ζ l.A : F) = (algebraMap (FractionRing T.V) F).comp (algebraMap T.V _) (b z) ∧
      (∀ a q, QkExt (algebraMap _ F) (twistedLevelPointsOfLattice D oD hϖ hdiv pA a) q → Out.QkPt.Equiv (D0 (H := H) D hϖ) F q (I.ev l.A a)) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dm.La), ∀ q,
        QkExt (algebraMap _ F) (eta0 D oD hϖ hdiv pM a) q → Out.QkPt.Equiv (D0 (H := H) D hϖ) F q (I.ev l.M a)

def arc (hX : Nontrivial D.toPre.X) (hw : letI := H.starRing; TraceFormTwistIso D.toPre oD H.w0)
    (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF D hϖ a a') (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A)
    (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M) (hLie : LieCl D oD Dm β b)
    (hTate : TateCl D oD hϖ Dm β b hdiv pA pM) : ArcIn Dm l β T.V b :=
  letI := H.starRing
  { D₀ := D0 D hϖ
    oa := oa0 D oD hϖ
    nontriv := hX
    even := psiEven_twist (isScalarForm_tF D oD hϖ) H.w0 D.psi_even
    bimult := tauBimult_twist (GlobalTheory.ArcBuild.cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF D oD hϖ) D.tau_bimult
    gen := gen0 D oD hϖ
    w0 := psi_weight_zero_twist (GlobalTheory.ArcBuild.cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF D oD hϖ) hw
    be := beF D hϖ
    be_symm := beF_symm D hϖ
    be_pos := fun a ha => beF_pos D hϖ ha
    be_adj := beF_adj D oD hϖ
    be_dvd := hdiv
    eta := eta0 D oD hϖ hdiv pM
    etaA := twistedLevelPointsOfLattice D oD hϖ hdiv pA
    geom := fun F _ _ _ r z hr hz f hf => by
      subst hf
      obtain ⟨I, h₁, h₂, h₃⟩ := hTate F z hz
      exact ⟨hLie F r hr, I, h₁, h₂, h₃⟩ }

end ThetaShiftProofs

end GlobalTheory.TraitArc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedPullbackNonvanishingOfPulledSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPullback_nonvanishing_of_pulledSection : ∀ {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}, L.IsLB → ∀ {T : Over S} (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (a b : ℤ) (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (s : LB.Sec (LPow A L b T)) (s' : LB.Sec (LPow A L a T)), IsTwistPull A L ψ m hm a b α s s' → ∀ p : (T ⊗ A).left, ψ.left.base p ∈ nonzeroLocus s → p ∈ nonzeroLocus s' := by
  first | exact @GlobalTheory.TwistNZ.twistPull_nonzero | exact GlobalTheory.TwistNZ.twistPull_nonzero | (intros; apply GlobalTheory.TwistNZ.twistPull_nonzero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

variable {S : Scheme.{0}}

def SiegKerBy {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B} (c : SiegPre h M ζ s) (d : ℕ) : Prop :=
  Out.RelAmple c.A c.diag ∧
    ∀ (T : Over S) (x : T ⟶ c.A),
      (∃ t : (c.P.pull (lift (snd c.A T ≫ x) (fst c.A T)).left).Gen, t.IsGen) → x ^ d = 1

def IsSympLev {A : Over S} [GrpObj A] (P : LB (G2 A).left) (h M : ℕ) {B : Type} [CommRing B] (ζ : B)
    (t₁ : S ⟶ Sp B) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)) : Prop :=
  (∀ a b, lev (a + b) = lev a * lev b) ∧ (∀ a, lev a ^ M = 1) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k) (z : kˣ), x ≫ t₁ = spMap β →
      (z : k) = β ζ →
      (∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = M • b)) ∧
      (∀ g : Over.mk x ⟶ A, g ^ M = 1 → ∃ a, toUnit _ ≫ lev a = g) ∧
      ∀ a b, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) M (toUnit (Over.mk x) ≫ lev a) (toUnit _ ≫ lev b)
        (unitOn (z ^ (2 * omegaStd a b)))

theorem SiegPre.isSympLev {h M : ℕ} {B : Type} [CommRing B] {ζ : B} {s : S ⟶ Sp B} (c : SiegPre h M ζ s) :
    IsSympLev c.P h M ζ s c.lev :=
  ⟨c.lev_add, c.lev_tors, c.geom⟩

def SDRep (h M d : ℕ) : Prop :=
  ∃ (X : Scheme.{0}) (s : X ⟶ Sp (cycAway M)) (u : SiegPre h M (zetaAway M) s),
    SiegKerBy u d ∧ IsUnit ((d : ℕ) : Γ(X, ⊤)) ∧ IsQProjOver s ∧
    ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t),
      IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃! f : S ⟶ X, f ≫ s = t ∧ SiegPB c u f

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def HasLevelStructureOfLevel (b : Base D R) (N h M : ℕ) : Prop :=
  ∃ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
    (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
    IsSympLev u.P h M (zetaAway M) s₁ lev ∧ IsQProjOver s ∧
    ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (t₁ : S ⟶ Sp (cycAway M)) (o : Obj b N t)
      (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ o.A)), IsSympLev o.P h M (zetaAway M) t₁ l →
      ∃! f : S ⟶ X, f ≫ s = t ∧ f ≫ s₁ = t₁ ∧ ∃ m : ObjMap o u f, ∀ a, (l a).left ≫ m.φ = f ≫ (lev a).left

theorem Datum.two_le_finrank_La {p : ℕ} [Fact p.Prime] (D : Datum p) : 2 ≤ Module.finrank ℤ D.La := by
  haveI := D.freeLa
  haveI := D.finLa
  have hF : 0 < Module.finrank ℚ D.F := Module.finrank_pos
  have hpos : 0 < Module.finrank ℤ D.La := by
    rw [D.rankLa]
    exact Nat.mul_pos (Nat.mul_pos D.m_pos D.n_pos) hF
  by_contra hlt
  have h1 : Module.finrank ℤ D.La = 1 := by omega
  let bs := Module.finBasisOfFinrankEq ℤ D.La h1
  have hzero : ∀ x y : D.La, D.EF x y = 0 := by
    intro x y
    have hx : x = bs.repr x 0 • bs 0 := by
      conv_lhs => rw [← bs.sum_repr x]
      simp
    have hy : y = bs.repr y 0 • bs 0 := by
      conv_lhs => rw [← bs.sum_repr y]
      simp
    rw [hx, hy, LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply, D.alt, smul_zero, smul_zero]
  have hsub : ∀ x : D.La, x = 0 := by
    intro x
    apply D.nondeg
    ext y
    simp [hzero]
  have : Module.finrank ℤ D.La = 0 := by
    haveI : Subsingleton D.La := ⟨fun a b => by rw [hsub a, hsub b]⟩
    exact Module.finrank_zero_of_subsingleton
  omega

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedFibreFrameAtOriginEqRigidification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.RigAtOrigin

theorem frame_at_origin : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (x : KeyIn ℂ)
    (φ : x.P.A.left ⟶ D.P.A.left) (he : eSec x.P.A ≫ φ = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A)
    (w : LB.Iso x.P.L (D.P.L.pull φ)), w.IsGen →
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) he D.P.L D.rig) →
    ∀ (g : ℕ) (u : HolUnif x.P.A x.P.L g), u.IsRig x.rig → ∀ (k : x.P.L.ι) (j : D.P.L.ι),
      ⊤ ≤ (u.ex 0).left ⁻¹ᵁ x.P.L.U k → ⊤ ≤ (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) ≫ eSec D.P.A) ⁻¹ᵁ D.P.L.U j →
      valAt' (u.ex 0).left _ (w.s (fun _ => j, k)).val * u.fr k 0 =
        valF (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => j)) (D.rig.s (fun _ => j)).val := by
  intro R _ _ _ D x φ he w _ hM g u hrig k j hk hj
  have hu0 : (u.ex 0).left = eSec x.P.A := by
    rw [(u.ker 0).2 u.Λ.zero_mem]
    change (toUnit _ ≫ η[x.P.A]).left = η[x.P.A].left
    rw [toUnit_unit, Category.id_comp]
  have hj' : ⊤ ≤ (𝟙 (Sp ℂ) ≫ eSec x.P.A ≫ φ) ⁻¹ᵁ D.P.L.U j := by
    rw [Category.id_comp, he]; exact hj
  have hk' : ⊤ ≤ (𝟙 (Sp ℂ) ≫ eSec x.P.A) ⁻¹ᵁ x.P.L.U k := by
    rw [Category.id_comp, ← hu0]; exact hk
  have e := GlobalTheory.ArcThetaFib.maps_val' φ _ he D.P.L D.rig x.P.L w x.rig hM (𝟙 (Sp ℂ)) j k hj' hk'
  have hr := hrig (fun _ => k) (fun q hq => Set.mem_iInter.2 fun _ => hk' hq)
  rw [hu0, hr]
  simp only [Category.id_comp] at e
  exact e.symm

end GlobalTheory.RigAtOrigin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedClassOfCmHostStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_class_of_cm_host : ∀ D : D7, letI : IsCMField D.host.E := D.host.isCMField_hostE; GlobalTheory.UCls.Unr D.host.E := by
  first | exact @GlobalTheory.MassLink.host_unr | exact GlobalTheory.MassLink.host_unr | (intros; apply GlobalTheory.MassLink.host_unr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSubringDedekindOpenImmersionStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_subring_dedekind_open_immersion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (W : ValuationSubring c.F), GlobalTheory.Models.IsDedFrac W.subtype ∧ IsOpenImmersion (spMap W.subtype) := by
  first | exact @GlobalTheory.CoeffValuation.isDedFrac_and_isOpenImmersion | exact GlobalTheory.CoeffValuation.isDedFrac_and_isOpenImmersion | (intros; apply GlobalTheory.CoeffValuation.isDedFrac_and_isOpenImmersion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueStatementHoldsStatement
section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.value_statement_holds : ValueSt := by
  first | exact @GlobalTheory.FlatModel.valueSt | exact GlobalTheory.FlatModel.valueSt | (intros; apply GlobalTheory.FlatModel.valueSt <;> assumption)
end

