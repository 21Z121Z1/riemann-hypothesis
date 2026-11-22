import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0008
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0279
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0294
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0293
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StabiliserMapHyperplaneEqConjClassMap
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000

namespace GlobalTheory.Mem.Col2.HAt.Stab

theorem co_apply {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {n : ℕ} (h : S.rank = n)
    (g : S.V ≃ₗ[E] S.V) (x : S.V) :
    co S h (g x) = (reGL h E (Formalism.L2.Herm.toGLb S.frame g)).1 *ᵥ co S h x := by
  have e : lin S h (reGL h E (Formalism.L2.Herm.toGLb S.frame g)) = g := by
    subst h
    have e0 : ∀ k : GL (Fin S.rank) E, reGL rfl E k = k := fun k => by
      ext a b
      simp [reGL]
    show (Formalism.L2.Herm.toGLb S.frame).symm (reGL rfl E (reGL rfl E (Formalism.L2.Herm.toGLb S.frame g))) = g
    rw [e0, e0, MulEquiv.symm_apply_apply]
  rw [← co_lin, e]

theorem co_symm_apply {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {n : ℕ} (h : S.rank = n)
    (k : GL (Fin S.rank) E) (x : S.V) :
    co S h ((Formalism.L2.Herm.toGLb S.frame).symm k x) = (reGL h E k).1 *ᵥ co S h x := by
  rw [co_apply, MulEquiv.apply_symm_apply]

theorem eq_of_frMul {E K ι : Type} [Field E] [Field K] [Fintype ι] (τ : ι) (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ}
    (g M : GL (Fin n) E) (y : Col2.Fr emb σ n) (h : frMul emb σ M⁻¹ (frMul emb σ g y) = y) : g = M := by
  have h1 : (M⁻¹ : GL (Fin n) E).1.map (embAt σ emb τ) * (g.1.map (embAt σ emb τ) * y.1 τ) = y.1 τ :=
    congrFun (congrArg Subtype.val h) τ
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul] at h1
  have hy : IsUnit (y.1 τ) := (Matrix.isUnit_iff_isUnit_det _).2 (y.2 τ)
  have h2 : (M⁻¹ * g : GL (Fin n) E).1.map (embAt σ emb τ) = 1 := hy.mul_right_cancel (by rw [h1, Matrix.one_mul])
  have h3 : (M⁻¹ * g : GL (Fin n) E).1 = 1 := by
    apply Matrix.map_injective (embAt σ emb τ).injective
    show _ = (1 : Matrix (Fin n) (Fin n) E).map (embAt σ emb τ)
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact h2
  have h4 : M⁻¹ * g = 1 := Units.ext h3
  exact (inv_mul_eq_one.1 h4).symm

theorem ext_vec {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1) {x y : Fin N → E} (h1 : iniH hN x = iniH hN y)
    (h2 : x (Br.iL hN) = y (Br.iL hN)) : x = y := by
  funext j
  by_cases hj : j.1 < n
  · exact congrFun h1 ⟨j.1, hj⟩
  · have : j = Br.iL hN := Fin.ext (by have := j.2; show j.1 = n; omega)
    rw [this, h2]

theorem ga_eq_gam_mv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u)) → ∀ (u : B.Word) (c : ((I.rec7 l Z).fm u).clsP), ((F u).til.ga c).1.1 = ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))).1 := by
  intro B X I l Z H F hF u c
  classical
  have hemb : Formalism.L2.Forms.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
    funext τ
    ext y
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  let y : Col2.Fr B.fields.emb B.embLL (B.R.N B.R.m) := ⟨fun _ => 1, fun _ => by simp⟩
  let g : GL (Fin (B.R.N B.R.m)) B.fields.E := ((F u).til.ga c).1
  let φ : (I.stp u I.mu0 B.R.m).Cl → Col2.Fr B.fields.emb B.embLL (B.R.N B.R.m) → ℂ := fun _ z => if z = y then 1 else 0
  have hY := (hF u).eY B.R.m le_rfl (Or.inr rfl)
  have h := (F u).evz φ c (frMul B.fields.emb B.embLL g y) y (by
    intro τ
    rw [hemb]
    exact (congrFun (hY _) τ).trans (congrArg (fun k : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) ℂ => (g.1.map (embAt B.embLL B.fields.emb τ) * k : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) ℂ)) (congrFun (hY y) τ)).symm)
  rw [(hF u).eWz] at h
  have h' : B.embLL _ * φ ((I.perIn u I.mu0).tilC c) (frMul B.fields.emb B.embLL ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c)))⁻¹ (frMul B.fields.emb B.embLL g y)) = _ * φ ((I.perIn u I.mu0).tilC c) y := h
  have hy : frMul B.fields.emb B.embLL ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c)))⁻¹ (frMul B.fields.emb B.embLL g y) = y := by
    by_contra hne
    simp only [φ, if_neg hne, if_pos, mul_zero, mul_one] at h'
    exact Units.ne_zero _ h'.symm
  exact congrArg Units.val (eq_of_frMul (show B.fields.Tau from (I.rec7 l Z).eTau.symm 1) _ _ _ _ _ hy)

theorem crdN_stabM : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u)) → CarH H F → ∀ (u : B.Word) (h1 : 1 ≤ (I.rec7 l Z).R.m) (c : ((I.rec7 l Z).mem u).C.cls (I.rec7 l Z).R.m) (s : ((I.rec7 l Z).mem u).C.stab (I.rec7 l Z).R.m c) (y : ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m).V), crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl (Formalism.L2.Herm.stabMLinS (I.rec7 l Z) H u h1 c s y) = ((I.stp u I.mu0 B.R.m).gam c.1 s.1).1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y := by
  intro B X I l Z H F hF hC u h1 c s y
  obtain ⟨k, hk⟩ := (hF u).ends B.R.m le_rfl (Or.inr rfl)
  have e1 := hk.stab c s
  have e2 := (hC.carM u).st_eq c s
  have e3 : ∀ (β β' : H.Ch u (I.rec7 l Z).R.m) (h : H.chOf u (I.rec7 l Z).R.m c = β) (h' : H.chOf u (I.rec7 l Z).R.m c = β'),
      ((H.cls u (I.rec7 l Z).R.m h1 le_rfl β).stabI ⟨c, h⟩ s).1 = ((H.cls u (I.rec7 l Z).R.m h1 le_rfl β').stabI ⟨c, h'⟩ s).1 := by
    intro β β' h h'
    subst h
    subst h'
    rfl
  refine (co_symm_apply ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m) (rankN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl) _ y).trans ?_
  refine congrArg (fun k : GL (Fin (B.R.N B.R.m)) B.fields.E => k.1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y) ?_
  rw [← e1]
  exact (congrArg _ (e3 _ _ rfl (chOf_m H u c))).trans e2.symm

theorem crdP_stabP : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u)) → CarT H F A → ∀ (u : B.Word) (c : ((I.rec7 l Z).fm u).clsP) (s : ((I.rec7 l Z).fm u).stabilizer₂ c) (x : (I.rec7 l Z).sp.X'.V), crdP (I.rec7 l Z) (Formalism.L2.Herm.stabPLinS (I.rec7 l Z) H A u c s x) = ((I.perIn u I.mu0).S'.gam c.1 s.1).1 *ᵥ crdP (I.rec7 l Z) x := by
  intro B X I l Z H F A hF hC u c s x
  have e1 := (hF u).what₂.stab c s
  have e2 := (hC.carP u).st_eq c s
  refine (co_symm_apply (I.rec7 l Z).sp.X' (rankP (I.rec7 l Z)) _ x).trans ?_
  exact congrArg (fun k : GL (Fin (B.R.N B.R.m - 1)) B.fields.E => k.1 *ᵥ crdP (I.rec7 l Z) x) (e2.symm.trans e1)

theorem crdN_tilG : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), CarT H F A → ∀ (u : B.Word) (c : ((I.rec7 l Z).fm u).clsP) (y : ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m).V), crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl (((A u).tilG c).1 y) = ((F u).til.ga c).1.1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y := by
  intro B X I l Z H F A hC u c y
  rw [hC.ga u c]
  exact co_apply ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m) (rankN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl) _ y

theorem gam_ext : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (b : (I.perIn u I.mu0).S'.β) (g : (I.perIn u I.mu0).S'.G b), (∀ y, ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).ext b g)).1 *ᵥ iXc (I.rec7 l Z) y = iXc (I.rec7 l Z) (((I.perIn u I.mu0).S'.gam b g).1 *ᵥ y)) ∧ ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).ext b g)).1 *ᵥ TC.z0 X u = TC.z0 X u := by
  intro B X I hOk hP l Z u b g
  have hi := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hP l Z).2.2.1
  have ini : ∀ y : Fin (B.R.N B.R.m - 1) → B.fields.E, iniH (N_m_succ B.R) (iXc (I.rec7 l Z) y) = y := fun y => by
    funext j
    exact (hi y _).trans (dif_pos j.2)
  have las : ∀ y : Fin (B.R.N B.R.m - 1) → B.fields.E, iXc (I.rec7 l Z) y (Br.iL (N_m_succ B.R)) = 0 := fun y =>
    (hi y _).trans (dif_neg (lt_irrefl _))
  refine ⟨fun y => ext_vec (N_m_succ B.R) ?_ ?_, ext_vec (N_m_succ B.R) ?_ ?_⟩
  · refine ((l.per u I.mu0).gam_ini b g _).trans ?_
    exact (congrArg _ (ini _)).trans (ini _).symm
  · exact ((l.per u I.mu0).gam_last b g _).trans ((las _).trans (las _).symm)
  · refine ((l.per u I.mu0).gam_ini b g _).trans ?_
    have z : iniH (E := B.fields.E) (N_m_succ B.R) (TC.z0 X u) = 0 := by
      funext j
      exact if_neg (by have := j.2; show ¬ (j.1 + 1 = _); omega)
    exact (congrArg _ z).trans ((Matrix.mulVec_zero _).trans z.symm)
  · exact (l.per u I.mu0).gam_last b g _

theorem stabMap_tied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), CarT H F A → Formalism.L2.Herm.SymmetricStabilizerMapCompatibility (I.rec7 l Z) H A := by
  intro B X I hOk hPins l Z H F hStd hCarH A hCarT u h1 c s
  have hF : ∀ u, I.StdF l Z u (F u) := fun u => (hStd u).1
  have hga := ga_eq_gam_mv I l Z H F hF u c
  have conj : ∀ v, ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))).1 *ᵥ
      (((I.stp u I.mu0 B.R.m).gam _ (((I.rec7 l Z).fm u).stabMap c s).1).1 *ᵥ v) =
      ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).ext c.1 s.1)).1 *ᵥ
      (((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))).1 *ᵥ v) := by
    intro v
    show _ *ᵥ (((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 (((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))⁻¹ * (I.perIn u I.mu0).ext c.1 s.1 *
          (I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))).1 *ᵥ v) = _
    rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have key : ∀ y, crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl (((A u).tilG c).1 (Formalism.L2.Herm.stabMLinS (I.rec7 l Z) H u h1 _
      (((I.rec7 l Z).fm u).stabMap c s) (((A u).tilG c).1.symm y))) =
      ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).ext c.1 s.1)).1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y := by
    intro y
    have hw : ((F u).til.ga c).1.1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl (((A u).tilG c).1.symm y) =
        crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y := by
      rw [← crdN_tilG I l Z H F A hCarT u c, LinearEquiv.apply_symm_apply]
    rw [crdN_tilG I l Z H F A hCarT u c, crdN_stabM I l Z H F hF hCarH u h1, ← hw, hga]
    exact conj _
  have hiX : ∀ x, crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl ((I.rec7 l Z).sp.iX' x) = iXc (I.rec7 l Z) (crdP (I.rec7 l Z) x) := by
    intro x
    simp [iXc, crdN, crdP]
  have hext := gam_ext I hOk hPins l Z u c.1 s.1
  refine ⟨fun x => ?_, ?_⟩
  · apply (crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl).injective
    rw [key, hiX, hiX, hext.1, crdP_stabP I l Z H F A hF hCarT u c s x]
    rfl
  · apply (crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl).injective
    rw [key, ← hCarT.z0 u]
    have hz : (F u).til.z0 = TC.z0 X u := funext fun j => (hF u).z0 j
    rw [hz, hext.2]

end GlobalTheory.Mem.Col2.HAt.Stab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevChange
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.DTheta

theorem stepLev_change : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (b : Bool) (t : T) (k : ℕ), k + 1 < D.R.m → ∀ (κ : GA D (Yc D k)), ∀ κ' ∈ levS (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)), ∀ c : ℂ, (∀ φ, R.ωY t k (κ, κ') (R.toRealDat.ptY t k φ) = c • R.toRealDat.ptY t k φ) → ∀ y : R.CC t (k + 1), y.1 ∈ MultT R.θ (R.MY (k + 1)) (levS (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b))) (levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b))) → ∀ φ w g, (R.ioY t k y).1 (R.ItY k φ w) (g * κ) = c * levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) κ' * (R.ioY t k y).1 (R.ItY k φ w) g := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH b t k hk κ κ' hκ' c hc y hy φ w g
  have hch : R.toRealDat.IsChain := RealDat.chain_of_weak hP.char.base.chain hH.aux.ex
  have hio := hch.ioY t k (by omega)
  have e1 := hio.eq y φ w (g * κ)
  have e2 := hio.eq y φ w g
  rw [← e1, ← e2]
  unfold Lift.liftInt

  have hm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 hy)
  set χ1 := levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) with hχ1
  have hlev : ∀ (u : SmT (R.MY (k + 1))) h, y.1 u (h * κ') = χ1 κ' * y.1 u h := by
    intro u h
    induction u using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have := hm.lev v κ' hκ' h
      simp only [PiTensorProduct.lift_symm, LinearMap.compMultilinearMap_apply] at this
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, this]
      ring
    | add a a' ha ha' =>
      simp only [map_add, Pi.add_apply, ha, ha']
      ring
  have hleft : ∀ (u : SmT (R.MY (k + 1))), ∀ γ ∈ GQ (Yc D (k + 1)), ∀ h, y.1 u (γ * h) = y.1 u h := by
    intro u γ hγ h
    induction u using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have := (hm.aut v).left γ hγ h
      simp only [PiTensorProduct.lift_symm, LinearMap.compMultilinearMap_apply] at this
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, this]
    | add a a' ha ha' =>
      simp only [map_add, Pi.add_apply, ha, ha']
  have hω := hch.ωY t k hk
  have hpt := hch.ptY t k hk φ
  have hθ1 : ∀ h, thetaKO (R.ωY t k) (g * κ) h (R.toRealDat.ptY t k φ) =
      c * thetaKO (R.ωY t k) g (h * κ'⁻¹) (R.toRealDat.ptY t k φ) := by
    intro h
    unfold thetaKO
    have e : ((g * κ, h) : GA D (Yc D k) × GA D (Yc D (k + 1))) = (g, h * κ'⁻¹) * (κ, κ') := by
      ext <;> simp [mul_assoc]
    rw [e, map_mul, Module.End.mul_apply, hc φ, map_smul, Pi.smul_apply, smul_eq_mul]
  have hθ2 : ∀ γ ∈ GQ (Yc D (k + 1)), ∀ h, thetaKO (R.ωY t k) g (γ * h) (R.toRealDat.ptY t k φ) =
      thetaKO (R.ωY t k) g h (R.toRealDat.ptY t k φ) := by
    intro γ hγ h
    unfold thetaKO
    have e : ((g, γ * h) : GA D (Yc D k) × GA D (Yc D (k + 1))) = (1, γ) * (g, h) := by
      ext <;> simp
    rw [e, map_mul, Module.End.mul_apply]
    exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ _ hpt)
  have hmod := hP.char.base.models
  have hHF : (R.νY t (k + 1)).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D (k + 1))) (R.fdY t (k + 1)) (R.νY t (k + 1)) := by
    by_cases h2 : k + 1 + 1 < D.R.m
    · have h3 := hmod.νY t (k + 1) h2
      exact ⟨h3.1.1, h3.2⟩
    · have h3 := hmod.νY' t
      have e : D.R.m - 1 = k + 1 := by omega
      rw [e] at h3
      exact ⟨h3.1.1, h3.2⟩
  haveI := Formalism.IndefR.Eqv.measurableMul_GA D (Yc D (k + 1))
  haveI := Formalism.IndefR.Eqv.gQ_countable D (Yc D (k + 1))
  haveI := hHF.1
  haveI : (R.νY t (k + 1)).IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds _ _ hHF.1
  set Ψ : GA D (Yc D (k + 1)) → ℂ := fun h => thetaKO (R.ωY t k) g h (R.toRealDat.ptY t k φ) * y.1 w h with hΨ
  have hRI := Formalism.IndefR.Eqv.rightInv_holds (GA D (Yc D (k + 1))) (GQ (Yc D (k + 1))) (R.νY t (k + 1))
    (R.fdY t (k + 1)) hHF.2 Ψ (fun γ hγ h => by simp only [hΨ, hθ2 γ hγ h, hleft w γ hγ h]) κ'⁻¹
  calc ∫ h in R.fdY t (k + 1), thetaKO (R.ωY t k) (g * κ) h (R.toRealDat.ptY t k φ) * y.1 w h ∂(R.νY t (k + 1))
      = ∫ h in R.fdY t (k + 1), c * χ1 κ' * Ψ (h * κ'⁻¹) ∂(R.νY t (k + 1)) := by
        congr 1
        funext h
        have e := hlev w (h * κ'⁻¹)
        rw [inv_mul_cancel_right] at e
        simp only [hΨ, hθ1 h, e]
        ring
    _ = c * χ1 κ' * ∫ h in R.fdY t (k + 1), Ψ h ∂(R.νY t (k + 1)) := by
        rw [integral_const_mul, hRI.2]

end GlobalTheory.Mem.R3.DTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfForallIsPsEff
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem IsAmpleLB.tens_of_forall_isPsEff : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), IsProjOver f → ∀ A N : LB X, IsAmpleLB A → N.IsLB → (∀ Z : Closeds X, IsIrreducible (Z : Set X) → IsPsEff (N.pull (redι Z))) → IsAmpleLB (tens A N) := by
  intro k _ X f hf A N hA hN hpe
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hf
  have hT : (tens A N).IsLB := isLB_tens hA.isLB hN
  refine isAmpleLB_of_subsingleton_coh_one X (tens A N) hT fun F hF => ?_
  obtain ⟨j₀, hj⟩ := eventually_subsingleton_coh_ample_psEff k X f hf A N hA hN hpe F hF
  refine ⟨max j₀ 1, le_max_right _ _, ?_⟩
  have h1 := hj (max j₀ 1) (max j₀ 1) (le_max_left _ _) le_rfl 1 one_pos
  obtain ⟨i⟩ := nonempty_twist_iso_of_cls_eq F
    (isLB_tens (isLB_lbPow hA.isLB (max j₀ 1)) (isLB_lbPow hN (max j₀ 1)))
    (isLB_lbPow hT (max j₀ 1)) (by
      rw [cls_tens (isLB_lbPow hA.isLB _) (isLB_lbPow hN _), cls_lbPow hA.isLB, cls_lbPow hN,
        cls_lbPow hT, cls_tens hA.isLB hN, smul_add])
  exact (cohOn.mapIso Γ(X, ⊤) ⊤ 1 i).symm.injective.subsingleton

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFockVacuumProperties
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.VecP

open scoped ComplexOrder in

theorem isCartanInv_one_of_onb {k : ℕ} {G B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G 1 B k) : IsCartanInv G 1 := by
  obtain ⟨ε, hε, hB, -⟩ := h
  have hε1 : ∀ a, ε a = 1 := fun a =>
    ((hε a).resolve_right fun h' => absurd h'.2 (not_le.mpr a.2)).1
  have hB1 : Bᴴ * G * B = 1 := by simpa [hε1] using hB
  have hBC : B * (Bᴴ * G) = 1 := mul_eq_one_comm.mp hB1
  have hGB : G * B = (Bᴴ * G)ᴴ := by
    calc G * B = (B * (Bᴴ * G))ᴴ * (G * B) := by rw [hBC, conjTranspose_one, Matrix.one_mul]
      _ = (Bᴴ * G)ᴴ * (Bᴴ * G * B) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (Bᴴ * G)ᴴ := by rw [hB1, Matrix.mul_one]
  have hG : G = (Bᴴ * G)ᴴ * (Bᴴ * G) := by
    calc G = G * (B * (Bᴴ * G)) := by rw [hBC, Matrix.mul_one]
      _ = G * B * (Bᴴ * G) := by rw [Matrix.mul_assoc]
      _ = (Bᴴ * G)ᴴ * (Bᴴ * G) := by rw [hGB]
  have hinj : Function.Injective (Bᴴ * G).mulVec := by
    intro v w hvw
    have h2 := congrArg (fun x => B *ᵥ x) hvw
    simpa only [Matrix.mulVec_mulVec, hBC, Matrix.one_mulVec] using h2
  unfold IsCartanInv
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one, hG]
  exact Matrix.PosDef.conjTranspose_mul_self _ hinj

end GlobalTheory.OneMapRef.VecP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffProdBlockSymbolDetPowStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeFormCoeff_prod_blockSymbol_det_pow : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n) (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q), GlobalTheory.GoodMetric.topCoeff (∏ τ, (GlobalTheory.DomainDens.blockSym h τ).det ^ q) = GlobalTheory.GoodMetric.topCoeff ((GlobalTheory.DomainDens.blockSym h1 ()).det ^ q) ^ Fintype.card ι := by
  first | exact @GlobalTheory.DomainDens.topCoeff_prod_blockSym_det_pow | exact GlobalTheory.DomainDens.topCoeff_prod_blockSym_det_pow | (intros; apply GlobalTheory.DomainDens.topCoeff_prod_blockSym_det_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffRenameCayleyBlockSymbolEmbeddi
section
set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

namespace GlobalTheory.CayleyBlock

namespace TopRename

variable {p q : ℕ} (hc : Fintype.card (Unit × Fin p × Fin q) = p * q)

def idx : Fin p × Fin q ≃ Fin (p * q) :=
  (Equiv.punitProd (Fin p × Fin q)).symm.trans (Fintype.equivFinOfCardEq hc)

theorem blockEmb_eq (x : Fin q × Fin p × Fin p) :
    blockEmb hc x = (idx hc (x.2.1, x.1), idx hc (x.2.2, x.1)) := rfl

theorem blockEmb_injective : Function.Injective (blockEmb hc) := by
  rintro ⟨b, i, j⟩ ⟨b', i', j'⟩ h
  simp only [blockEmb_eq, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨⟨e1, e2⟩, ⟨e3, -⟩⟩ := h
  subst e1 e2 e3
  rfl

def permOf (τ : Fin q → Equiv.Perm (Fin p)) : Equiv.Perm (Fin (p * q)) :=
  (idx hc).permCongr (Equiv.prodCongrLeft fun b => (τ b)⁻¹)

theorem permOf_apply' (τ : Fin q → Equiv.Perm (Fin p)) (j : Fin p) (b : Fin q) :
    permOf hc τ (idx hc (j, b)) = idx hc ((τ b)⁻¹ j, b) := by
  simp [permOf, Equiv.permCongr_apply]

theorem permOf_apply (τ : Fin q → Equiv.Perm (Fin p)) (i : Fin p) (b : Fin q) :
    permOf hc τ (idx hc (τ b i, b)) = idx hc (i, b) := by
  rw [permOf_apply']
  simp

theorem sign_permOf (τ : Fin q → Equiv.Perm (Fin p)) :
    ((Equiv.Perm.sign (permOf hc τ) : ℤˣ) : ℤ) = sgnProd τ := by
  simp [permOf, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_prodCongrLeft, sgnProd]

theorem permOf_injective : Function.Injective (permOf hc) := by
  intro τ τ' e
  funext b
  have h : ∀ j, (τ b)⁻¹ j = (τ' b)⁻¹ j := by
    intro j
    have := congrArg (fun w : Equiv.Perm (Fin (p * q)) => w (idx hc (j, b))) e
    simp only [permOf_apply'] at this
    exact congrArg Prod.fst ((idx hc).injective this)
  exact inv_inj.mp (Equiv.ext h)

theorem graph_apply' {n : ℕ} (g : Fin n → Fin n) (x y : Fin n) :
    (∑ a, Finsupp.single (a, g a) 1 : Fin n × Fin n →₀ ℕ) (x, y) = if g x = y then 1 else 0 := by
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single x (fun c _ hc => by simp [Finsupp.single_apply, hc]) (by simp)]
  simp [Finsupp.single_apply]

theorem graph_permOf (τ : Fin q → Equiv.Perm (Fin p)) :
    (∑ a, Finsupp.single (a, permOf hc τ a) 1 : Fin (p * q) × Fin (p * q) →₀ ℕ) =
      (blockGraph τ).mapDomain (blockEmb hc) := by
  rw [blockGraph, Finsupp.mapDomain_finset_sum]
  simp_rw [Finsupp.mapDomain_finset_sum, Finsupp.mapDomain_single, blockEmb_eq]
  rw [← (idx hc).sum_comp, ← (Equiv.prodCongrLeft fun b => τ b).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => ?_
  simp [permOf_apply]

theorem mem_range_of_graph (w : Equiv.Perm (Fin (p * q))) (u : Fin q × Fin p × Fin p →₀ ℕ)
    (h : u.mapDomain (blockEmb hc) = ∑ a, Finsupp.single (a, w a) 1) : ∃ τ, permOf hc τ = w := by
  have hr : ∀ x : Fin p × Fin q, ((idx hc).symm (w (idx hc x))).2 = x.2 := by
    intro x
    have h0 : (∑ a, Finsupp.single (a, w a) 1 : Fin (p * q) × Fin (p * q) →₀ ℕ) (idx hc x, w (idx hc x)) ≠ 0 := by
      rw [graph_apply' (fun a => w a)]
      simp
    rw [← h] at h0
    by_contra hne
    apply h0
    apply Finsupp.mapDomain_notin_range
    rintro ⟨⟨b, i, j⟩, hy⟩
    rw [blockEmb_eq, Prod.mk.injEq] at hy
    apply hne
    have hx : x = (i, b) := ((idx hc).injective hy.1).symm
    rw [← hy.2, Equiv.symm_apply_apply, hx]
  let f : Fin q → Fin p → Fin p := fun b i => ((idx hc).symm (w (idx hc (i, b)))).1
  have hf : ∀ b, Function.Injective (f b) := by
    intro b i i' e
    have : (idx hc).symm (w (idx hc (i, b))) = (idx hc).symm (w (idx hc (i', b))) :=
      Prod.ext e ((hr (i, b)).trans (hr (i', b)).symm)
    simpa using this
  let σ : Fin q → Equiv.Perm (Fin p) := fun b => Equiv.ofBijective (f b) (Finite.injective_iff_bijective.mp (hf b))
  refine ⟨fun b => (σ b)⁻¹, ?_⟩
  ext1 a
  obtain ⟨⟨i, b⟩, rfl⟩ := (idx hc).surjective a
  rw [permOf_apply', inv_inv, ← (idx hc).apply_symm_apply (w (idx hc (i, b)))]
  congr 1
  exact Prod.ext rfl (hr (i, b)).symm

end TopRename

open TopRename in

theorem topCoeff_rename_blockEmb : ∀ {p q : ℕ} (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q)
    (G : MvPolynomial (Fin q × Fin p × Fin p) ℂ), GlobalTheory.GoodMetric.topCoeff (rename (blockEmb h1) G) =
      ∑ τ : Fin q → Equiv.Perm (Fin p), (sgnProd τ : ℂ) * coeff (blockGraph τ) G := by
  intro p q h1 G
  rw [GlobalTheory.GoodMetric.topCoeff]
  symm
  refine Fintype.sum_of_injective (permOf h1) (permOf_injective h1) _ _ ?_ ?_
  · intro w hw
    rw [coeff_rename_eq_zero, mul_zero]
    intro u hu
    obtain ⟨τ, rfl⟩ := mem_range_of_graph h1 w u hu
    exact absurd ⟨τ, rfl⟩ hw
  · intro τ
    rw [graph_permOf, coeff_rename_mapDomain _ (blockEmb_injective h1), ← sign_permOf h1]

end GlobalTheory.CayleyBlock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPlacesPrimeToLevelAndTypePrimesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlaces_prime_to_levelAndTypePrimes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.Laws → ∀ (u : B.Word) (a : I.ι) (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal ∧ ∀ j, ((B.host.g j : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal := by
  first | exact @GlobalTheory.Mem.Col2.TC.underQ_prime_to_bad | exact GlobalTheory.Mem.Col2.TC.underQ_prime_to_bad | (intros; apply GlobalTheory.Mem.Col2.TC.underQ_prime_to_bad <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldingSchurOrthogonalityDefiniteCoefficientsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_schur_orthogonality_definite_coefficients : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (t : T) (h h' : (R.HX t).H) (a a' : R.cX.W), IntegrableOn (fun g => star ⟪a, R.cX.ext ((R.HX t).e h) g⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') g⟫_ℂ) (R.fdX t) (R.νX t) ∧ (Module.finrank ℂ R.cX.W : ℂ) * ∫ g in R.fdX t, star ⟪a, R.cX.ext ((R.HX t).e h) g⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') g⟫_ℂ ∂(R.νX t) = ⟪a', a⟫_ℂ * ⟪h, h'⟫_ℂ := by
  first | exact @GlobalTheory.Mem.SchurW.schurW | exact GlobalTheory.Mem.SchurW.schurW | (intros; apply GlobalTheory.Mem.SchurW.schurW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCongruenceConjContainsCongruenceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_congruence_conj_contains_congruence : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), principalLevelFrame.CongConj L n := by
  first | exact @GlobalTheory.CongConjugate.congConj | exact GlobalTheory.CongConjugate.congConj | (intros; apply GlobalTheory.CongConjugate.congConj <;> assumption)
end

