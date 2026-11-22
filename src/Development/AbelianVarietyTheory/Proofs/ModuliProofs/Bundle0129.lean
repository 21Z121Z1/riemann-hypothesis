import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowerSectionOfChartFunctions
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationFormIntPolynomialBundles
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

noncomputable section

namespace GlobalTheory.FormPoly

open GlobalTheory.CechPic Polynomial

theorem poly_induction {p : ℤ[X] → Prop} (h1 : p 1) (hadd : ∀ F G, p F → p G → p (F + G))
    (hneg : ∀ F, p F → p (-F)) (hX : ∀ F, p F → p (X * F)) (F : ℤ[X]) : p F := by
  have h0 : p 0 := by simpa using hadd 1 (-1) h1 (hneg 1 h1)
  have hC : ∀ a : ℤ, p (Polynomial.C a) := by
    intro a
    induction a using Int.induction_on with
    | zero => simpa using h0
    | succ i ih => simpa using hadd _ _ ih h1
    | pred i ih => simpa [sub_eq_add_neg] using hadd _ _ ih (hneg 1 h1)
  have hmono : ∀ (n : ℕ) (a : ℤ), p (Polynomial.monomial n a) := by
    intro n a
    induction n with
    | zero => simpa using hC a
    | succ n ih => rw [← Polynomial.X_mul_monomial]; exact hX _ ih
  induction F using Polynomial.induction_on' with
  | add F G hF hG => exact hadd _ _ hF hG
  | monomial n a => exact hmono n a

theorem exists_apply {V : Type} [CommGroup V] (c : V → V) (hc : ∀ a b, c (a * b) = c a * c b) (v : V) :
    ∃ ev : ℤ[X] → V, ev 1 = v ∧ (∀ F G, ev (F + G) = ev F * ev G) ∧ ∀ F, ev (X * F) = c (ev F) := by
  let φ : Module.End ℤ (Additive V) :=
    (AddMonoidHom.mk' (fun a => Additive.ofMul (c a.toMul)) (fun a b => by simp [hc])).toIntLinearMap
  refine ⟨fun F => (Polynomial.aeval φ F (Additive.ofMul v)).toMul, by simp, fun F G => by simp, fun F => by simp [φ]⟩

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem exists_ev (s : A ⟶ A) [IsMonHom s] : ∃ ev : ℤ[X] → (A ⟶ A), ev 1 = 𝟙 A ∧
    (∀ F G, ev (F + G) = ev F * ev G) ∧ ∀ F, ev (X * F) = ev F ≫ s := by
  exact exists_apply (fun f => f ≫ s) (fun a b => MonObj.mul_comp a b s) (𝟙 A)

section Ev

variable {s : A ⟶ A} [IsMonHom s] {ev : ℤ[X] → (A ⟶ A)} (h1 : ev 1 = 𝟙 A)
  (hadd : ∀ F G, ev (F + G) = ev F * ev G) (hX : ∀ F, ev (X * F) = ev F ≫ s)

include hadd in
theorem ev_neg (F : ℤ[X]) : ev (-F) = (ev F)⁻¹ := by
  have h0 : ev 0 = 1 := by
    have e := hadd 0 0
    rw [add_zero] at e
    exact mul_left_cancel (e.symm.trans (_root_.mul_one _).symm)
  have e := hadd F (-F)
  rw [add_neg_cancel, h0] at e
  exact eq_inv_of_mul_eq_one_right e.symm

include h1 hadd hX

theorem ev_isMonHom (F : ℤ[X]) : IsMonHom (ev F) := by
  refine poly_induction (p := fun F => IsMonHom (ev F)) ?_ ?_ ?_ ?_ F
  · rw [h1]; infer_instance
  · intro F G hF hG; rw [hadd, Hom.mul_def]; infer_instance
  · intro F hF; rw [ev_neg hadd]; infer_instance
  · intro F hF; rw [hX]; infer_instance

omit [IsMonHom s] in
theorem ev_mul (F G : ℤ[X]) : ev (F * G) = ev F ≫ ev G := by
  refine poly_induction (p := fun G => ev (F * G) = ev F ≫ ev G) ?_ ?_ ?_ ?_ G
  · rw [_root_.mul_one, h1, Category.comp_id]
  · intro G H hG hH; rw [mul_add, hadd, hadd, hG, hH, MonObj.comp_mul]
  · intro G hG; rw [mul_neg, ev_neg hadd, ev_neg hadd, hG, GrpObj.comp_inv]
  · intro G hG; rw [mul_left_comm F X G, hX, hX, hG, Category.assoc]

omit [IsMonHom s] hadd in
theorem ev_X : ev X = s := by
  have e := hX 1
  rwa [_root_.mul_one, h1, Category.id_comp] at e

end Ev

variable {L : LB A.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen)

include hΘ in
theorem lam_inv_left {T : Over S} (x y : T ⟶ A) : lam (cls L hL) x⁻¹ y = -lam (cls L hL) x y := by
  have e := lam_mul_left hL hΘ x x⁻¹ y
  rw [mul_inv_cancel, lam_one_left] at e
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact e.symm

include hΘ in
theorem lam_inv_right {T : Over S} (x y : T ⟶ A) : lam (cls L hL) x y⁻¹ = -lam (cls L hL) x y := by
  rw [lam_comm, lam_inv_left hL hΘ, lam_comm]

include hΘ in

theorem lam_ev_adj {s : A ⟶ A} {ev : ℤ[X] → (A ⟶ A)} (h1 : ev 1 = 𝟙 A)
    (hadd : ∀ F G, ev (F + G) = ev F * ev G) (hX : ∀ F, ev (X * F) = ev F ≫ s) {T : Over S}
    (hs : ∀ x y : T ⟶ A, lam (cls L hL) (x ≫ s) y = lam (cls L hL) x (y ≫ s)) (F : ℤ[X]) :
    ∀ x y : T ⟶ A, lam (cls L hL) (x ≫ ev F) y = lam (cls L hL) x (y ≫ ev F) := by
  have hcomm : ∀ G : ℤ[X], s ≫ ev G = ev G ≫ s := by
    intro G
    have e := ev_mul h1 hadd hX X G
    rw [ev_X h1 hX, hX] at e
    exact e.symm
  refine poly_induction (p := fun F => ∀ x y : T ⟶ A,
    lam (cls L hL) (x ≫ ev F) y = lam (cls L hL) x (y ≫ ev F)) ?_ ?_ ?_ ?_ F
  · intro x y; simp only [h1, Category.comp_id]
  · intro F G hF hG x y
    rw [hadd, MonObj.comp_mul, MonObj.comp_mul, lam_mul_left hL hΘ,
      GlobalTheory.HermTensorLB.lam_mul_right hL hΘ, hF, hG]
  · intro F hF x y
    rw [ev_neg hadd, GrpObj.comp_inv, GrpObj.comp_inv, lam_inv_left hL hΘ, lam_inv_right hL hΘ, hF]
  · intro F hF x y
    rw [hX, ← Category.assoc, hs, hF, Category.assoc, ← hcomm F]

theorem pull_one {K : Type} [Field K] {B T : Over (Sp K)} [GrpObj B] (c : Pic B.left) :
    pull (1 : T ⟶ B).left c = 0 := by
  rw [Hom.one_def, Over.comp_left, pull_comp]
  obtain ⟨N, hN, hc⟩ := cls_surj (pull η[B].left c)
  rw [← hc, (cls_eq_zero_iff hN).2 (ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_isLB_local N hN), map_zero]

private theorem isLB_cube_lemma {S : Scheme.{0}} {A T : Over S} [GrpObj A] {n : ℕ} (x : Fin n → (T ⟶ A))
    {N : LB A.left} (hN : N.IsLB) : (cubeLB A x N).IsLB :=
  ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hN _ _

private theorem lam_id_lemma_2 {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (c : Pic A.left)
    (hadd : ∀ x y z : A ⟶ A, lam c x (y * z) = lam c x y + lam c x z) :
    lam c (𝟙 A) (𝟙 A) = c + pull (GrpObj.inv : A ⟶ A).left c := by
  have e := hadd (𝟙 A) (𝟙 A) (𝟙 A)⁻¹
  rw [_root_.mul_inv_cancel, lam_one_right] at e
  have e2 : lam c (𝟙 A) (𝟙 A)⁻¹ = -c - pull (GrpObj.inv : A ⟶ A).left c := by
    unfold lam
    rw [_root_.mul_inv_cancel, pull_one, ← GrpObj.inv_eq_inv, Over.id_left, pull_id]
    abel
  rw [e2, eq_comm, add_eq_zero_iff_eq_neg] at e
  rw [e]
  abel

private theorem pull_inv_lemma_3 {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (h : Out.Sym A L) : pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL := by
  obtain ⟨U, hU, t, ht⟩ := h (IsLocalRing.closedPoint K)
  have hV : A.hom ⁻¹ᵁ U = ⊤ := by
    rw [ReciprocityTheory.ChartRestriction.G.DVR.eq_top_of_closedPoint_mem U hU]
    simp
  have h0 := (cls_eq_zero_iff (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hL _ _)).2 ⟨t, ht⟩
  rw [cls_linComb hL, Fin.sum_univ_two] at h0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul,
    ← sub_eq_add_neg, sub_eq_zero, pull_comp] at h0
  have hf : (A.left.topIso.inv ≫ (A.left.isoOfEq hV.symm).hom) ≫ (A.hom ⁻¹ᵁ U).ι = 𝟙 A.left := by
    rw [Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.toIso_inv_ι]
  have e := congrArg (pull (A.left.topIso.inv ≫ (A.left.isoOfEq hV.symm).hom)) h0
  rw [← pull_comp _ (A.hom ⁻¹ᵁ U).ι, ← pull_comp _ (A.hom ⁻¹ᵁ U).ι, hf, pull_id, pull_id] at e
  exact e

end GlobalTheory.FormPoly

namespace GlobalTheory

open GlobalTheory.CechPic GlobalTheory.FormPoly

theorem formPoly_bundles : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A), M.IsLB → FormIs P M s → (∃ ev : Polynomial ℤ → (P.A ⟶ P.A), ev 1 = 𝟙 P.A ∧ (∀ F G, ev (F + G) = ev F * ev G) ∧ ∀ F, ev (Polynomial.X * F) = ev F ≫ s) ∧ ∀ (ev : Polynomial ℤ → (P.A ⟶ P.A)), ev 1 = 𝟙 P.A → (∀ F G, ev (F + G) = ev F * ev G) → (∀ F, ev (Polynomial.X * F) = ev F ≫ s) → (∀ F, IsMonHom (ev F)) ∧ (∀ F G, ev (F * G) = ev F ≫ ev G) ∧ (∀ F, FormIs P (cubeLB P.A ![𝟙 P.A, ev (F)] P.L) (ev (2 * F))) ∧ (∀ F G, LBIso (cubeLB P.A ![𝟙 P.A, ev (G ^ 2 * F)] P.L) ((cubeLB P.A ![𝟙 P.A, ev (F)] P.L).pull (ev G).left)) ∧ (∀ F G, LBIso (LB.div (cubeLB P.A ![𝟙 P.A, ev (F + G)] P.L) (cubeLB P.A ![𝟙 P.A, ev (F)] P.L)) (cubeLB P.A ![𝟙 P.A, ev (G)] P.L)) ∧ LBIso (cubeLB P.A ![𝟙 P.A, ev (1)] P.L) (lbPow P.L 2) ∧ (SymB M → LBIso (cubeLB P.A ![𝟙 P.A, ev (Polynomial.X)] P.L) (lbPow M 2)) := by
  intro laws _ K _ _ P M s hM hF
  obtain ⟨hsM, hFi⟩ := hF
  have hΘ : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := by
    obtain ⟨r, hr⟩ := P.rigid
    obtain ⟨cs⟩ := (laws.cube (Sp K) P { L := P.L, rig := r, isLB := P.isLB, rigGen := hr } rfl).1
    exact ⟨cs.t, cs.isGen⟩
  have hc : ∀ {T : Over (Sp K)} (x y : T ⟶ P.A) (N : LB P.A.left) (hN : N.IsLB),
      cls (cubeLB P.A ![x, y] N) (isLB_cube_lemma _ hN) = lam (cls N hN) x y :=
    fun x y N hN => cls_cube_two hN x y _
  have eF : lam (cls M hM) (fst P.A P.A) (snd P.A P.A) =
      lam (cls P.L P.isLB) (fst P.A P.A) (snd P.A P.A ≫ s) := by
    rw [← hc _ _ M hM, ← hc _ _ P.L P.isLB]
    exact (cls_eq_iff (isLB_cube_lemma _ hM) (isLB_cube_lemma _ P.isLB)).2 hFi
  have eF' : ∀ {T : Over (Sp K)} (x y : T ⟶ P.A), lam (cls M hM) x y = lam (cls P.L P.isLB) x (y ≫ s) := by
    intro T x y
    have e := congrArg (pull (lift x y).left) eF
    rwa [pull_lam, pull_lam, lift_fst, lift_snd, lift_snd_assoc] at e
  have hsa : ∀ (T : Over (Sp K)) (x y : T ⟶ P.A),
      lam (cls P.L P.isLB) (x ≫ s) y = lam (cls P.L P.isLB) x (y ≫ s) := by
    intro T x y
    rw [lam_comm (cls P.L P.isLB) (x ≫ s) y, ← eF' y x, lam_comm (cls M hM) y x, eF' x y]
  have hMadd : ∀ x y z : P.A ⟶ P.A,
      lam (cls M hM) x (y * z) = lam (cls M hM) x y + lam (cls M hM) x z := by
    intro x y z
    rw [eF', eF', eF', MonObj.mul_comp, GlobalTheory.HermTensorLB.lam_mul_right P.isLB hΘ]
  have hι := pull_inv_lemma_3 P.isLB P.sym
  refine ⟨exists_ev s, fun ev h1 hadd hX => ?_⟩
  have adj : ∀ (F : Polynomial ℤ) (T : Over (Sp K)) (x y : T ⟶ P.A),
      lam (cls P.L P.isLB) (x ≫ ev F) y = lam (cls P.L P.isLB) x (y ≫ ev F) :=
    fun F T => lam_ev_adj P.isLB hΘ h1 hadd hX (hsa T) F
  refine ⟨ev_isMonHom h1 hadd hX, ev_mul h1 hadd hX, ?_, ?_, ?_, ?_, ?_⟩
  · intro F
    have := ev_isMonHom h1 hadd hX F
    unfold FormIs
    refine ⟨ev_isMonHom h1 hadd hX (2 * F), ?_⟩
    show LBIso (cubeLB P.A ![fst P.A P.A, snd P.A P.A] (cubeLB P.A ![𝟙 P.A, ev F] P.L)) _
    rw [← cls_eq_iff (isLB_cube_lemma _ (isLB_cube_lemma _ P.isLB)) (isLB_cube_lemma _ P.isLB), hc, hc, hc,
      GlobalTheory.HermTensorLB.lam_lam P.isLB hΘ, two_mul, hadd, MonObj.comp_mul,
      GlobalTheory.HermTensorLB.lam_mul_right P.isLB hΘ, Category.comp_id, Category.comp_id,
      lam_comm (cls P.L P.isLB) (snd P.A P.A), adj]
    all_goals first | exact P.isLB | exact isLB_cube_lemma _ P.isLB
  · intro F G
    rw [← cls_eq_iff (isLB_cube_lemma _ P.isLB) (pull_isLB (isLB_cube_lemma _ P.isLB) _),
      cls_pull (isLB_cube_lemma _ P.isLB), hc, hc, pull_lam, Category.comp_id]
    have e := adj G P.A (𝟙 P.A) (ev G ≫ ev F)
    rw [Category.id_comp] at e
    rw [e, show G ^ 2 * F = G * F * G by ring, ev_mul h1 hadd hX, ev_mul h1 hadd hX, Category.assoc]
    all_goals exact P.isLB
  · intro F G
    rw [← cls_eq_iff (LB.isLB_div (isLB_cube_lemma _ P.isLB) (isLB_cube_lemma _ P.isLB)) (isLB_cube_lemma _ P.isLB),
      cls_div (isLB_cube_lemma _ P.isLB) (isLB_cube_lemma _ P.isLB), hc, hc, hc, hadd,
      GlobalTheory.HermTensorLB.lam_mul_right P.isLB hΘ, add_sub_cancel_left]
    all_goals exact P.isLB
  · rw [← cls_eq_iff (isLB_cube_lemma _ P.isLB) (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ P.isLB _ _), hc,
      cls_lbPow P.isLB, h1, lam_id_lemma_2 _ (fun x y z => GlobalTheory.HermTensorLB.lam_mul_right P.isLB hΘ x y z), hι,
      two_nsmul]
    all_goals exact P.isLB
  · intro hsym
    have hιM : pull (GrpObj.inv : P.A ⟶ P.A).left (cls M hM) = cls M hM := by
      rw [← cls_pull hM _ (pull_isLB hM _)]
      exact ((cls_eq_iff hM (pull_isLB hM _)).2 hsym).symm
    have e := eF' (𝟙 P.A) (𝟙 P.A)
    rw [Category.id_comp] at e
    rw [← cls_eq_iff (isLB_cube_lemma _ P.isLB) (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hM _ _), hc, cls_lbPow hM,
      ev_X h1 hX, ← e, lam_id_lemma_2 _ hMadd, hιM, two_nsmul]
    all_goals exact P.isLB

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleIffOfIsReduced
section
noncomputable section

namespace GlobalTheory.ModelCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ModuliCompare GlobalTheory.ObjPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

section Obj

variable {B : Type} [CommRing B] {b : Base l B} {S S' : Scheme.{0}} {s : S ⟶ Sp B} {f : S' ⟶ S}

def objOfSABMap (o : Obj D l b s) {t' : SAB H S'} (m : SABMap t' o.t f) : Obj D l b (f ≫ s) :=
  have hL : LBIso t'.PP.L (o.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hpr := o.proper
  have hp := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally
    S S' o.t.G t'.G f m.cm.F o.t.PP.L t'.PP.L o.t.PP.isLB t'.PP.isLB
    (AbelianSchemeGerms.isAbelianScheme_of_proper o.t.G o.t.semi) m.cart hL
  { t := t'
    proper := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hpr
    ample := hp.2.1 o.ample
    ktriv := hp.2.2 o.ktriv
    eta := fun a => secPull m.cart (o.eta a)
    eta_add := fun a c => by rw [o.eta_add, map_mul]
    eta_ker := fun a ha => by rw [o.eta_ker a ha, map_one]
    etaA := fun a => secPull m.cart (o.etaA a)
    etaA_add := fun a c => by rw [o.etaA_add, map_mul]
    etaA_ker := fun a => by rw [o.etaA_ker a, map_one]
    geom := fun k _ _ x β hx => by
      obtain ⟨hdet, I, hI, hA, hM⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc, hx])
      refine ⟨fun τ => ?_, tateMove (pushEquiv m.cart (Over.mk x)) (fun c g => ?_) (fun n g g' c hc => ?_) I,
        hI, fun a => ?_, fun a ha => ?_⟩
      · rw [GlobalTheory.LiePull.lieMult_pull _ S S' o.t.G t'.G f m.cm.F o.t.act t'.act m.cart m.act k x τ,
          GlobalTheory.LiePull.lieMult_pull _ S S' o.t.G t'.G f m.cm.F o.t.act t'.act m.cart m.act k x τ]
        exact hdet τ
      · apply Over.OverMorphism.ext
        show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
        rw [Category.assoc, m.act, Category.assoc]
      · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' o.t.G t'.G f m.cm.F o.t.PP.L t'.PP.L o.t.PP.isLB t'.PP.isLB
          m.cart hL (Over.mk x) n g g' _ _ _ rfl rfl).2 hc
      · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull m.cart _ _).trans (hA a))
      · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull m.cart _ _).trans (hM a ha)) }

def objMapOfSABMap (o : Obj D l b s) {t' : SAB H S'} (m : SABMap t' o.t f) : ObjMap (objOfSABMap o m) o f :=
  ⟨m, fun _ => secPull_left m.cart _, fun _ => secPull_left m.cart _⟩

theorem sec_eq_secPull {t : SAB H S} {t' : SAB H S'} (m : SABMap t' t f) {e : 𝟙_ (Over S) ⟶ t.G}
    {e' : 𝟙_ (Over S') ⟶ t'.G} (h : e'.left ≫ m.φ = f ≫ e.left) : e' = secPull m.cart e := by
  apply Over.OverMorphism.ext
  apply m.cart.1.hom_ext
  · exact h.trans (secPull_left m.cart _).symm
  · rw [Over.w, Over.w]

end Obj

section Model

variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

abbrev Model₂ (Xo : Moduli D l) (c : Coeff l) {O : Type} [CommRing O] (β : O →+* c.F) : Type 1 :=
  IndefiniteRowSideFullHecke.OpenModelSections.Model (X₀ := Xo.X) (str := Xo.s) Xo.univ (isCoeffField_of_coeff c) β

def toSecond (Y : Model Xo c β) : Model₂ Xo c β where
  X := Y.X
  s := Y.s
  normal := Y.normal
  proj := Y.proj
  flat := Y.flat
  j := Y.jQ
  j_over := Y.jQ_over
  j_open := Y.jQ_open
  j_dense := Y.jQ_dense
  t := Y.t
  t₀ := Y.oF.t
  toUniv := Y.m0.toSABMap
  toModel := Y.m
  ab y := Set.ext_iff.1 Y.ab_gen y

def ofSecond (Y : Model₂ Xo c β) : Model Xo c β where
  X := Y.X
  s := Y.s
  normal := Y.normal
  proj := Y.proj
  flat := Y.flat
  jQ := Y.j
  jQ_over := Y.j_over
  jQ_open := Y.j_open
  jQ_dense := Y.j_dense
  t := Y.t
  oF := objOfSABMap Xo.univ Y.toUniv
  m0 := objMapOfSABMap Xo.univ Y.toUniv
  m := Y.toModel
  ab_gen := Set.ext Y.ab

def modelEquiv (Xo : Moduli D l) (c : Coeff l) {O : Type} [CommRing O] (β : O →+* c.F) :
    Model Xo c β ≃ Model₂ Xo c β where
  toFun := toSecond
  invFun := ofSecond
  left_inv Y := by
    obtain ⟨X, s, _, _, _, jQ, _, _, _, t, ⟨t₀, _, _, _, eta, _, _, etaA, _, _, _⟩, ⟨m0, h₁, h₂⟩, m, _⟩ := Y
    change SABMap t₀ Xo.univ.t (pullback.fst _ _) at m0
    change SABMap t₀ t (jQ ≫ pullback.fst _ _) at m
    obtain rfl : eta = fun a => secPull m0.cart (Xo.univ.eta a) := funext fun a => sec_eq_secPull m0 (h₁ a)
    obtain rfl : etaA = fun a => secPull m0.cart (Xo.univ.etaA a) := funext fun a => sec_eq_secPull m0 (h₂ a)
    rfl
  right_inv _ := rfl

variable (Y : Model Xo c β)

def secEquiv : (𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) ≃
    (Over.mk (IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.baseChangeFst Xo.s (isCoeffField_of_coeff c)) ⟶ Xo.univ.t.G) where
  toFun σ := Over.homMk (σ.left ≫ Y.m0.toSABMap.φ) (by
    have h : σ.left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w σ
    exact (Category.assoc _ _ _).trans ((congrArg (σ.left ≫ ·) Y.m0.cart.1.w).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h).trans (Category.id_comp _)))))
  invFun σ := Over.homMk ((toSecond Y).liftSec σ) (Y.m0.cart.1.lift_snd _ _ _)
  left_inv σ := Over.OverMorphism.ext (Y.m0.cart.1.hom_ext (Y.m0.cart.1.lift_fst _ _ _)
    ((Y.m0.cart.1.lift_snd _ _ _).trans (Over.w σ).symm))
  right_inv σ := Over.OverMorphism.ext (Y.m0.cart.1.lift_fst _ _ _)

theorem secEquiv_left (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) :
    (secEquiv Y σ).left = σ.left ≫ Y.m0.toSABMap.φ := rfl

theorem secMap_secEquiv (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) :
    (toSecond Y).secMap (secEquiv Y σ) = σ.left ≫ Y.m.φ :=
  congrArg (fun x : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G => x.left ≫ Y.m.φ) ((secEquiv Y).left_inv σ)

theorem extends_iff_of_subset (U : Y.X.Opens) (hU : Set.range Y.j ⊆ (U : Set Y.X))
    (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) : Y.Extends U σ ↔ (toSecond Y).Extends (secEquiv Y σ) U := by
  rw [ModelScope.extends_iff_of_subset Y U hU]
  unfold IndefiniteRowSideFullHecke.OpenModelSections.Model.Extends
  rw [secMap_secEquiv]
  show _ ↔ ∃ τ : Over.mk U.ι ⟶ Y.t.G, (Y.j ∣_ U) ≫ τ.left = (Y.j ⁻¹ᵁ U).ι ≫ σ.left ≫ Y.m.φ
  constructor
  · rintro ⟨j', σ', h₀, h₁, h₂⟩
    refine ⟨Over.homMk σ' h₁, ?_⟩
    have e : Y.j ∣_ U = (Y.j ⁻¹ᵁ U).ι ≫ j' := by
      rw [← cancel_mono U.ι, morphismRestrict_ι, Category.assoc, h₀]
    rw [e, Category.assoc, ← h₂]
    rfl
  · rintro ⟨τ, hτ⟩
    have hr : Set.range (𝟙 (Xo.XF c) : _ ⟶ _) ⊆ Set.range (Y.j ⁻¹ᵁ U).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact hU ⟨x, rfl⟩
    have hi := IsOpenImmersion.lift_fac (Y.j ⁻¹ᵁ U).ι (𝟙 _) hr
    refine ⟨IsOpenImmersion.lift (Y.j ⁻¹ᵁ U).ι (𝟙 _) hr ≫ Y.j ∣_ U, τ.left, ?_, Over.w τ, ?_⟩
    · rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hi, Category.id_comp]
    · rw [Category.assoc, hτ, ← Category.assoc, hi, Category.id_comp]

theorem extends_iff (U : Y.X.Opens) (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) :
    Y.Extends U σ ↔ (Set.range Y.j ⊆ (U : Set Y.X) → (toSecond Y).Extends (secEquiv Y σ) U) := by
  by_cases hU : Set.range Y.j ⊆ (U : Set Y.X)
  · rw [extends_iff_of_subset Y U hU]
    exact ⟨fun h _ => h, fun h => h hU⟩
  · exact ⟨fun _ h => (hU h).elim, fun _ => ModelScope.extends_of_not_subset Y U hU σ⟩

end Model

section Push

variable {X : Scheme.{0}} {G : Over X} {L : LB G.left}

end Push

end GlobalTheory.ModelCompare
end
end

