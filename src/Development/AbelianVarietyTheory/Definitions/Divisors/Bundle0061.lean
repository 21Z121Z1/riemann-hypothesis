import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1621
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.FrameSignSimple
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.FunObj.SumModel

open GlobalTheory.ChiGrid Formalism.L2.Host Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem frameSign_simple {R : Type} [CommRing R] (n n' : Matrix (Fin 5) (Fin 5) R)
    (hn : ∀ i j, j ≤ i → n i j = if i = j then 1 else 0) (hn' : ∀ i j, j ≤ i → n' i j = if i = j then 1 else 0)
    (h : n'ᵀ * antiDiagonalSignGramMatrix 5 (-1 : R) * n = antiDiagonalSignGramMatrix 5 (-1 : R)) :
    (n 0 1 - n' 0 1) + (n 1 2 - n' 1 2) =
      ∑ p : Fin 4, frameSign R 5 p.castSucc * n p.castSucc p.succ * frameSign R 5 p.succ := by
  have h1 := congrFun (congrFun h 1) 4
  have h2 := congrFun (congrFun h 2) 3
  simp [Matrix.mul_apply, Fin.sum_univ_five, antiDiagonalSignGramMatrix, hn, hn'] at h1 h2
  simp [Fin.sum_univ_four, frameSign]
  linear_combination (-1 : R) * h1 - h2

theorem readOK {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → DomWeight n) : ReadOK σ := by
  obtain ⟨Φ, h, -⟩ := funForm (K := ℂ) σ
  exact readOK_of_equiv σ Φ fun F => (h F _).2 rfl

theorem covOf_funOf {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → DomWeight n) (F : VV ℂ σ) : covOf σ (funOf σ F) = F := by
  obtain ⟨Φ, h, -⟩ := funForm (K := ℂ) σ
  have h1 := (h _ _).1 ((readOK σ).1 F)
  have h2 := (h _ _).1 ((readOK σ).2 (funOf σ F))
  exact Φ.injective (h2.symm.trans h1)

theorem funOf_rhoV {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] {n : ℕ} (emb : ι → E →+* ℂ) (σ : ι → DomWeight n)
    (γ : GL (Fin n) E) (F : VV ℂ σ) :
    funOf σ (rhoK σ (embGL emb γ) F) = rhoK (fun τ => (σ τ).dual) (invTrK (embGL emb γ)) (funOf σ F) := by
  obtain ⟨Φ, h, h', -⟩ := funForm (K := ℂ) σ
  rw [(h _ _).1 ((readOK σ).1 F), (h _ _).1 ((readOK σ).1 _), h']

theorem finEmb_eq {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (y : GfC A) (x : GfC B)
    (h : EmbRel B A d.ι x.1 y.1) : finEmb d y = x :=
  Subtype.ext ((GlobalTheory.AutFunCounterexample.embRel_existsUnique B A d.ι d.isom y.1).unique (finEmb_rel d y) h)

theorem finEmb_mul {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (y y' : GfC A) :
    finEmb d (y * y') = finEmb d y * finEmb d y' := by
  refine finEmb_eq d _ _ ⟨?_, fun v hv => ?_⟩
  · have h1 := (finEmb_rel d y).1
    have h2 := (finEmb_rel d y').1
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul] at *
    rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  · have h1 := (finEmb_rel d y).2 v hv
    have h2 := (finEmb_rel d y').2 v hv
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul] at *
    rw [← Matrix.mulVec_mulVec, h2, h1]

theorem exists_places : ∃ PA : Finset (Pl D.host.E),
    (∀ w ∈ PA, FractionalIdeal.count D.host.E w D.host.AA ≠ 0 ∨ FractionalIdeal.count D.host.E w D.host.AAbar ≠ 0) ∧
    ∀ w, FractionalIdeal.count D.host.E w D.host.AA ≠ 0 → ∃! w', w' ∈ PA ∧ w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := by
  classical
  have hf : {w : Pl D.host.E | FractionalIdeal.count D.host.E w D.host.AA ≠ 0}.Finite :=
    Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors D.host.AA)
  let p : Pl D.host.F → Pl D.host.E → Prop := fun v w => FractionalIdeal.count D.host.E w D.host.AA ≠ 0 ∧ w.under (𝓞 D.host.F) = v
  let f : ∀ w : Pl D.host.E, FractionalIdeal.count D.host.E w D.host.AA ≠ 0 → Pl D.host.E := fun w h =>
    (⟨w, h, rfl⟩ : ∃ w', p (w.under (𝓞 D.host.F)) w').choose
  have hp : ∀ w h, p (w.under (𝓞 D.host.F)) (f w h) := fun w h => Exists.choose_spec _
  have hc : ∀ w h w' h', w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) → f w h = f w' h' := fun w h w' h' e => by
    simp only [f, e]
  refine ⟨hf.toFinset.attach.image fun w => f w.1 (hf.mem_toFinset.1 w.2), fun w hw => ?_, fun w h => ⟨f w h, ⟨?_, (hp w h).2⟩, ?_⟩⟩
  · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hw
    exact Or.inl (hp _ (hf.mem_toFinset.1 a.2)).1
  · exact Finset.mem_image.2 ⟨⟨w, hf.mem_toFinset.2 h⟩, Finset.mem_attach _ _, rfl⟩
  · rintro w' ⟨hw, e⟩
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hw
    exact hc _ (hf.mem_toFinset.1 a.2) _ h ((hp _ (hf.mem_toFinset.1 a.2)).2.symm.trans e)

theorem nonempty_empty {G : GridData L sc} (W : G.Weil) (N : Std G (∅ : Set T)) (Z : Normal W N) : Nonempty (GridChoice W ∅) := by
  obtain ⟨PA, h1, h2⟩ := exists_places (D := D)
  have h : ∀ j, ∃ β : GL (Fin (G.V (.top j)).rank) (Lev.EAf D), j ≤ D.R.m → IsFrame β (G.Λ (.top j)) := fun j => by
    by_cases hj : j ≤ D.R.m
    · have hl := (G.isV (X := .top j) hj fun _ e => by cases e).sd.1
      obtain ⟨β, hβ⟩ := GlobalTheory.AdelicFrame.exists_isFrame D.host.F _ hl.fg hl.span_eq_top
      exact ⟨β, fun _ => hβ⟩
    · exact ⟨1, fun a => absurd a hj⟩
  choose β hβ using h
  exact ⟨⟨Classical.arbitrary _, β, hβ, fun _ h => h.elim, fun _ h => h.elim, N, Z, PA, h1, h2⟩⟩

end GlobalTheory.FunObj.SumModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
section
namespace GlobalTheory.PrimIn

structure Hypotheses2 : Prop where
  q1 : GlobalTheory.Hk3.HoweUnram
  q2 : GlobalTheory.Published.CuspRapidDecay
  q3 : GlobalTheory.Published.HarishChandraFinite
  q4 : GlobalTheory.Published.HarishChandraModules
  q5 : GlobalTheory.Published.DiscreteSeriesCover
  q6 : GlobalTheory.Published.CasselmanWallach
  q7 : GlobalTheory.Published.WeilSiegelFormulaUnitary
  q8 : GlobalTheory.Published.SiegelWeilUnitaryConvergent
  q9 : GlobalTheory.Published.DoublingMethod
  q10 : GlobalTheory.Published.UnramifiedDoublingGL
  q11 : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  q12 : GlobalTheory.Published.GreenCuspidal
  q13 : GlobalTheory.Published.WeilRepresentationUnitaryPair
  q14 : GlobalTheory.Published.SchurOrthogonalitySquareIntegrable

end GlobalTheory.PrimIn
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

def evAt {R : Type} [CommRing R] {X : Scheme.{0}} (ξ : Sp R ⟶ X) {U : X.Opens} (h : ⊤ ≤ ξ ⁻¹ᵁ U) : Γ(X, U) →+* R :=
  (Scheme.ΓSpecIso (.of R)).hom.hom.comp (ξ.appLE U ⊤ h).hom

section Path

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R]

def sqr : G.left ⟶ G.left := (𝟙 G * 𝟙 G : G ⟶ G).left

def triv (b : Sp R ⟶ S) : Sp (PowerSeries R) ⟶ G.left := spMap (PowerSeries.C (R := R)) ≫ b ≫ unitSec G

structure IsPath (c : R) (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left) : Prop where

  base : ξ ≫ G.hom = spMap (PowerSeries.C (R := R)) ≫ b

  zero : spMap (PowerSeries.constantCoeff (R := R)) ≫ ξ = b ≫ unitSec G

  scale : spMap (PowerSeries.rescale c) ≫ ξ = ξ ≫ sqr G

def HasTan {n : ℕ} (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left) {V : S.Opens} (τ : Fin n → Γ(Lie G, V))
    (w : Fin n → R) : Prop :=
  ∀ (U : G.left.Opens) (hU : ⊤ ≤ ξ ⁻¹ᵁ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U)
    (hb : ⊤ ≤ b ⁻¹ᵁ V') (f : Γ(G.left, U)),
    PowerSeries.coeff 1 (evAt ξ hU f) = ∑ i, w i * evAt b hb (dualApp (τ i) hV (dUnit G he f))

structure StalkData (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s))
    (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s)
    (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)) : Prop where

  str : Spec.map (CommRingCat.ofHom π) ≫ S.fromSpecStalk s = G.left.fromSpecStalk _ ≫ G.hom

  unit : Spec.map (CommRingCat.ofHom ε) ≫ G.left.fromSpecStalk _ = S.fromSpecStalk s ≫ unitSec G

  sq : Spec.map (CommRingCat.ofHom m) ≫ G.left.fromSpecStalk _ = G.left.fromSpecStalk _ ≫ sqr G

end Path

def IsRatPath {F : Type} [Field F] {Y : Scheme.{0}} (ξ : Sp (PowerSeries F) ⟶ Y) : Prop :=
  ∃ β : Sp (RatFunc F) ⟶ Y, spMap (algebraMap (RatFunc F) (LaurentSeries F)) ≫ β =
    spMap (algebraMap (PowerSeries F) (LaurentSeries F)) ≫ ξ

def RatRigid {S : Scheme.{0}} (G : Over S) [GrpObj G] {F : Type} [Field F] (b : Sp F ⟶ S) : Prop :=
  ∀ ξ : Sp (PowerSeries F) ⟶ G.left, IsPath G 2 b ξ → IsRatPath ξ → ξ = triv G b

def LocFrame {k K : Type} [Field k] [Field K] [Algebra k K] {C : Scheme.{0}} (x : Sp K ⟶ C) {W : C.Modules} {r : ℕ}
    {V₀ : C.Opens} (s : Fin r → Γ(W, V₀)) (v : Place k K) (g : Matrix (Fin r) (Fin r) K) : Prop :=
  ∃ (b : Sp v.O ⟶ C) (V : C.Opens) (t : Fin r → Γ(W, V)) (V' : C.Opens) (h₀ : V' ≤ V₀) (h₁ : V' ≤ V)
    (hx : ⊤ ≤ x ⁻¹ᵁ V') (M : Matrix (Fin r) (Fin r) Γ(C, V')),
    spMap v.O.subtype ≫ b = x ∧ ⊤ ≤ b ⁻¹ᵁ V ∧ IsFrame t ∧
      (∀ j, resM W h₀ (s j) = ∑ i, M i j • resM W h₁ (t i)) ∧ g = M.map (evAt x hx)

def IsGenOver (k : Type) {K : Type} [Field k] [Field K] [Algebra k K] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]
    (x : Sp K ⟶ C) : Prop :=
  NeronCurve.IsCurve k C ∧ NeronCurve.IsGen x ∧ x ≫ strHom k C = spMap (algebraMap k K)

theorem triv_over {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (b : Sp R ⟶ S) :
    triv G b ≫ G.hom = spMap (PowerSeries.C (R := R)) ≫ b := by
  rw [triv, Category.assoc, Category.assoc, sec_hom, Category.comp_id]

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SecondChernDegreeFubiniStudyLine
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame

namespace GlobalTheory.ChTwoModel

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem quot_eq_map {S : ShortComplex X.Modules} (h : Met p σ S.X₂ (0 + 1)) (hS : S.ShortExact)
    (h₁ : IsVB S.X₁ 0) (h₃ : IsVB S.X₃ 1) [IsIso S.g] :
    h.quot hS h₁ h₃ = h.map (asIso S.g) := Met.ext_of_exists fun y => by
  obtain ⟨a, ha⟩ := Met.exists_adapted hS h₁ h₃ y
  refine ⟨a.quot, ha, ?_⟩
  rw [h.quot_G hS h₁ h₃ a ha]
  ext i j
  refine Eq.trans ?_ (((h.map (asIso S.g)).form_frame a.quot ha i j).symm.trans
    (h.form_map (asIso S.g) (a.t i) (a.t j) ha)).symm
  simp [quotGram, toBlocks₂₂, Met.gram, VBExt.AdaptedChart.frame]

theorem isometric_grLB {E : X.Modules} {h : VMetric p E 1} (H : h.IsCInf) (fl : Vert.Flag E 1) :
    (VMetric.det H).Isometric (VMetric.grLB fl 0 H) := by
  have i₁ : IsIso (fl.ι (Fin.succ 0)) := fl.isIso_last
  have hS := VMetric.stepSeq_shortExact fl 0
  have i₂ : IsIso (VMetric.stepSeq fl 0).g :=
    hS.isIso_g_iff.2 (VB.isVB_zero_iff.1 (fl.isVB (Fin.castSucc 0)))
  have H₁ : (h.stepMet fl 0).IsCInf := H.restrict _ _
  have e₁ := CurveDens.det_isometric_of_isIsometry k X p _ _ 1 (h.stepMet fl 0) h H₁ H
    (asIso (fl.ι (Fin.succ 0))) fun σ V s t y hy => ((h.met σ).form_restrict (fl.isSubbundle _) _ s t hy).symm
  have e₂ := CurveDens.det_isometric_of_isIsometry k X p _ _ 1 (h.stepMet fl 0) (h.grMet fl 0) H₁
    (H.grMet fl 0) (asIso (VMetric.stepSeq fl 0).g) ((VMetric.isIsometry_iff _).2 (VMetric.ext
      (funext fun σ => quot_eq_map ((h.stepMet fl 0).met σ) hS (fl.isVB (Fin.castSucc 0)) _)))
  exact e₁.symm.trans e₂

theorem isCh2Deg_rank_one (HC : Published.ArCalc) [IsIntegral X] (hX : IsRegSurf p) {E : X.Modules}
    {h : VMetric p E 1} (H : h.IsCInf) {a : ℝ} (ha : (VMetric.det H).IsSelfInter a) :
    h.IsCh2Deg (a / 2) := by
  refine ⟨⟨.self hX H (.ofRankOne h.isVB)⟩, fun M => (VMetric.isFlagCh2_rank_one _ _).2 ?_⟩
  have h₁ := (HC.2.2.2.2.1 k X M.Y p (M.ρ ≫ p) 1 hX.toIsArithVar M.reg.toIsArithVar M.ρ rfl
    M.generic M.finite).1 _ a ha
  have h₂ := ((VMetric.isometric_det_pull H M.ρ rfl).symm.trans
    (isometric_grLB M.cInf M.flag)).isSelfInter M.reg.toIsArithVar h₁
  convert h₂ using 1
  rw [RegCover.deg]
  ring

theorem isometric_det_ofLB (L : HermLB p) : L.Isometric (VMetric.det (VMetric.isCInf_ofLB L)) :=
  HermLB.isometric_of_chart (M := VMetric.det (VMetric.isCInf_ofLB L)) (Chart.ofLB L.isLB)
    (fun _ => le_rfl) (fun x i j _ _ => congrArg (gm (𝟙 X) x _) (TautFlag.detUnit_chartSec_eq L.isLB i j).symm)
    fun σ _ _ hy => Met.detWeight_ofWeight (L.φ σ) hy

theorem isCh2Deg_scale (HC : Published.ArCalc) [IsIntegral X] (hX : IsRegSurf p) {E : X.Modules}
    {h : VMetric p E 1} (H : h.IsCInf) {a : ℝ} (ha : (VMetric.det H).IsSelfInter a) (t : ℝ) :
    (h.scale t).IsCh2Deg (a / 2 - t / 2 * h.first_chern_integral) := by
  have h₁ := HC.2.2.1 k X p 1 hX.toIsArithVar _ a (-t / 2) ha
  have e : ((VMetric.det H).shift (fun _ => -t / 2) fun _ => rfl).Isometric (VMetric.det (H.scale t)) :=
    HermLB.isometric_of_chart (M := VMetric.det (H.scale t)) id (fun _ => le_rfl)
      (fun _ _ _ _ _ => rfl) fun σ c y hy => by
        change -Real.log ((Real.exp t : ℂ) • (h.met σ).G c y).det.re = -Real.log _ + 2 * (-t / 2)
        rw [det_smul, Fintype.card_fin, pow_one, Complex.re_ofReal_mul,
          Real.log_mul (by positivity) (det_re_pos ((h.met σ).posDef c y hy)).ne', Real.log_exp]
        ring
  convert isCh2Deg_rank_one HC hX (H.scale t) (e.isSelfInter hX.toIsArithVar h₁) using 1
  rw [VMetric.firstChernIntegral_eq_degree H]
  push_cast
  ring

theorem secondChernDegree_fubiniStudy_line (HC : Published.ArCalc) :
    haveI := ProjSpace.isRegSurf_line.isIntegral
    (HermVB.ofLB (ProjSpace.hermitianTwistingSheaf ℤ 1)).h.IsCh2Deg (1 / 4) ∧
      (HermVB.ofLB (ProjSpace.hermitianTwistingSheaf ℤ 1)).ch2Deg = 1 / 4 := by
  haveI := ProjSpace.isRegSurf_line.isIntegral
  have h := isCh2Deg_rank_one HC ProjSpace.isRegSurf_line (VMetric.isCInf_ofLB (ProjSpace.hermitianTwistingSheaf ℤ 1))
    ((isometric_det_ofLB _).isSelfInter ProjSpace.isRegSurf_line.toIsArithVar (TautFlag.selfInter HC).1)
  rw [show (1 / 2 / 2 : ℝ) = 1 / 4 by norm_num] at h
  exact ⟨h, h.ch2Deg_eq⟩

theorem eq_of_isFlagCh2 [IsIntegral X] (hX : IsRegSurf p) {E : X.Modules} {r : ℕ} {h : VMetric p E r}
    {H : h.IsCInf} {fl : Vert.Flag E r} {a b : ℝ} (ha : h.IsCh2Deg a)
    (hb : VMetric.IsFlagCh2 H fl b) : a = b := by
  let φ := (Scheme.Modules.pullbackId X).app E
  have e₁ := (VMetric.isIsometry_pull_id_comp k X p E r h).1
  have e₂ : h.IsIsometry (h.pull (𝟙 X) (Category.id_comp p)) φ.symm := fun σ V s t y hy => by
    have u (s : Γ(E, V)) : φ.hom.app V (φ.inv.app V s) = s := congr(($(φ.inv_hom_id)).app V s)
    exact (e₁ σ V _ _ y hy).symm.trans (congrArg₂ ((h.met σ).form · · y) (u s) (u t))
  have e₃ := (VMetric.isFlagCh2_ofIso k X p _ _ r h _ φ.symm H
    (H.pull (𝟙 X) (Category.id_comp p)) fl b e₂).1 hb
  have e₄ (q : X ⟶ Sp k) (e : 𝟙 X ≫ p = q) (fl') (H' : VMetric.IsFlagCh2 (H.pull (𝟙 X) e) fl' b) :
      VMetric.IsFlagCh2 (H.pull (𝟙 X) rfl) fl' b := by subst e; exact H'
  have e₅ := ha.eq_div (.self hX H fl) (e₄ _ _ _ e₃)
  rwa [show (VMetric.FlagModel.self hX H fl).deg = 1 from RegCover.deg_self hX, Nat.cast_one,
    div_one] at e₅

theorem eq_zero_of_isCh2Deg_std (HC : Published.ArCalc) {a : ℝ} :
    haveI := ProjSpace.isRegSurf_line.isIntegral
    (HermVB.std (PSpace.str ℤ 1) 2).h.IsCh2Deg a → a = 0 :=
  haveI := ProjSpace.isRegSurf_line.isIntegral
  fun ha => have ⟨_, _, _, hf⟩ := TautFlag.exists_flag HC
    eq_of_isFlagCh2 ProjSpace.isRegSurf_line ha hf

end GlobalTheory.ChTwoModel
end
end

